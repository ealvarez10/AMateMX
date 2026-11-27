"""Ordenadas de los ceros de ζ(s) y L(s,χ) en la recta crítica, |t| ≤ T, en Python puro.

L(s,χ) = N^{-s} Σ_{a=1}^{N} χ(a) ζ(s, a/N), con la zeta de Hurwitz por Euler–Maclaurin.
Los ceros se localizan como mínimos de |L(1/2+it)| en una malla y se refinan por sección
áurea; se aceptan si |L| < 1e-8 en el mínimo.
"""
import cmath
import math

# B_{2j}/(2j)! para j = 1..12
B2 = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510,
      43867 / 798, -174611 / 330, 854513 / 138, -236364091 / 2730]
COEF = [B2[j] / math.factorial(2 * j + 2) for j in range(12)]


def hurwitz(s, a, M=40):
    tot = 0j
    for n in range(M):
        tot += (n + a) ** (-s)
    x = M + a
    tot += x ** (1 - s) / (s - 1) + 0.5 * x ** (-s)
    prod = s  # s(s+1)...(s+2j-2)
    pot = x ** (-s - 1)
    for j in range(12):
        tot += COEF[j] * prod * pot
        prod *= (s + 2 * j + 1) * (s + 2 * j + 2)
        pot /= x * x
    return tot


def L(s, N, chi):
    if N == 1:
        return hurwitz(s, 1.0)
    return N ** (-s) * sum(chi[a] * hurwitz(s, a / N) for a in range(1, N) if chi[a] != 0)


def ceros(N, chi, T=60.0, paso=0.005, negativos=False):
    f = lambda t: abs(L(complex(0.5, t), N, chi))
    t0 = -T if negativos else 0.2
    ts = [t0 + i * paso for i in range(int((T - t0) / paso) + 1)]
    vs = [f(t) for t in ts]
    out = []
    g = (math.sqrt(5) - 1) / 2
    for i in range(1, len(ts) - 1):
        if vs[i] <= vs[i - 1] and vs[i] < vs[i + 1]:
            a, b = ts[i - 1], ts[i + 1]
            for _ in range(80):
                c, d = b - g * (b - a), a + g * (b - a)
                if f(c) < f(d):
                    b = d
                else:
                    a = c
            t = (a + b) / 2
            if f(t) < 1e-8:
                out.append(t)
    return out


CARACTERES = {
    "zeta": (1, None),
    "chi3": (3, {0: 0, 1: 1, 2: -1}),
    "chi4": (4, {0: 0, 1: 1, 2: 0, 3: -1}),
    "chi5": (5, {0: 0, 1: 1, 2: 1j, 4: -1, 3: -1j}),
}

if __name__ == "__main__":
    import json
    import sys

    T = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    res = {}
    for nombre, (N, chi) in CARACTERES.items():
        neg = nombre == "chi5"  # carácter complejo: los ceros no son simétricos
        zs = ceros(N, chi, T=T, negativos=neg)
        res[nombre] = zs
        print(nombre, " ".join(f"{z:.6f}" for z in zs))
    json.dump(res, open("resultados/ceros.json", "w"), indent=1)
