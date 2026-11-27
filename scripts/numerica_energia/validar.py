"""Valida energia_rapida contra las definiciones de Lean, aplicadas literalmente.

ζ: σ_Q(k) = 1 + Σ_{d≤Q} μ(d){k/d} − Q m_Q {k/Q} − γ_Q (2{k/2Q} − {k/Q})   (Definiciones.lean)
χ: σ_{Q,χ}(k) = 1 − Σ_{d≤Q} μ(d) χ(d) S_χ(⌊k/d⌋)                        (Testigo.lean)
Uso: python3 validar.py RUTA_BINARIO
"""
import math
import subprocess
import sys
from fractions import Fraction

BIN = sys.argv[1]


def mobius(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    for p in range(2, n + 1):
        if all(p % q for q in range(2, int(p ** 0.5) + 1)):
            for k in range(p, n + 1, p):
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu


def fract(x):
    return x - math.floor(x)


def sigma_zeta(Q, kmax, mu):
    m = sum(Fraction(mu[d], d) for d in range(1, Q + 1))
    t = 1 - sum(mu[d] / d * math.log(Q / d) for d in range(1, Q + 1))
    gam = Q * t / math.log(2)
    out = []
    for k in range(1, kmax + 1):
        phi = 1 + sum(mu[d] * fract(Fraction(k, d)) for d in range(1, Q + 1)) - Q * m * fract(Fraction(k, Q))
        h = 2 * fract(Fraction(k, 2 * Q)) - fract(Fraction(k, Q))
        out.append(float(phi) - gam * float(h))
    return out


CHI = {
    "chi3": (3, {0: 0, 1: 1, 2: -1}),
    "chi4": (4, {0: 0, 1: 1, 2: 0, 3: -1}),
    "chi5": (5, {0: 0, 1: 1, 2: 1j, 4: -1, 3: -1j}),
}


def sigma_chi(nombre, Q, kmax, mu):
    N, chi = CHI[nombre]
    S = lambda y: sum(chi[n % N] for n in range(1, y + 1))
    Sper = [S(y) for y in range(N)]
    out = []
    for k in range(1, kmax + 1):
        T = sum(mu[d] * chi[d % N] * Sper[(k // d) % N] for d in range(1, Q + 1))
        out.append(complex(1 - T))
    return out


def volcar(modo, Q, kmax):
    r = subprocess.run([BIN, "volcar", modo, str(Q), str(kmax)], capture_output=True, text=True, check=True)
    filas = r.stdout.split("\n")[:-1]
    if modo == "zeta":
        return [float(x) for x in filas], r.stderr.strip()
    return [complex(float(a), float(b)) for a, b in (f.split() for f in filas)], r.stderr.strip()


mu = mobius(200)
peor = 0.0
casos = 0
for Q in (2, 3, 5, 7, 10, 30, 64, 97, 150):
    kmax = 6 * Q + 500
    ref = sigma_zeta(Q, kmax, mu)
    got, info = volcar("zeta", Q, kmax)
    err = max(abs(a - b) for a, b in zip(ref, got))
    ceros = all(abs(x) < 1e-9 for x in ref[: Q - 1])
    Eref = sum(x * x / (k * (k + 1)) for k, x in enumerate(ref, 1))
    Egot = float(info.split()[0].split("=")[1])
    print(f"zeta Q={Q:4d}: max|Δσ|={err:.1e}  σ=0 en 1..Q−1: {ceros}  ΔE_K={abs(Eref - Egot):.1e}  [{info}]")
    peor = max(peor, err, abs(Eref - Egot))
    casos += 1
for nombre in CHI:
    for Q in (1, 2, 5, 10, 31, 100):
        kmax = 4 * Q + 300
        ref = sigma_chi(nombre, Q, kmax, mu)
        got, info = volcar(nombre, Q, kmax)
        err = max(abs(a - b) for a, b in zip(ref, got))
        Eref = sum(abs(x) ** 2 / (k * (k + 1)) for k, x in enumerate(ref, 1))
        Egot = float(info.split()[0].split("=")[1])
        print(f"{nombre} Q={Q:4d}: max|Δσ|={err:.1e}  ΔE_K={abs(Eref - Egot):.1e}  [{info}]")
        peor = max(peor, err, abs(Eref - Egot))
        casos += 1
print(f"\n{casos} casos; peor diferencia {peor:.2e}")
sys.exit(0 if peor < 1e-8 else 1)
