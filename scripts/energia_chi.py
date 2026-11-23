# Testigo y energía de AMate para un carácter de Dirichlet no principal χ mod q:
#   σ_{Q,χ}(k) = 1 − Σ_{d≤Q} μ(d) χ(d) S_χ(⌊k/d⌋),   S_χ(y) = Σ_{n≤y} χ(n)
#   E_{Q,χ}    = Σ_{k≥1} |σ_{Q,χ}(k)|² / (k(k+1))
# Recurrencia: σ(k) − σ(k−1) = −χ(k) c_Q(k), con c_Q(n) = Σ_{d|n, d≤Q} μ(d).
import cmath, math, sys
from array import array

def mobius(N):
    mu = array('b', [1]) * (N + 1); mu[0] = 0
    es = bytearray([1]) * (N + 1)
    for p in range(2, N + 1):
        if es[p]:
            es[p*p::p] = bytearray(len(es[p*p::p])) if p * p <= N else es[p*p::p]
            for k in range(p, N + 1, p): mu[k] = -mu[k]
            for k in range(p * p, N + 1, p * p): mu[k] = 0
    return mu

def caracteres():
    # χ mod 3 y mod 4 (reales), χ mod 5 de orden 4 (complejo): χ(2) = i
    c3 = {0: 0, 1: 1, 2: -1}
    c4 = {0: 0, 1: 1, 2: 0, 3: -1}
    c5 = {0: 0, 1: 1, 2: 1j, 4: -1, 3: -1j}
    return [('mod 3', 3, c3), ('mod 4', 4, c4), ('mod 5, orden 4', 5, c5)]

def energia(Q, q, chi, K, mu):
    c = [0] * (K + 1)
    for d in range(1, Q + 1):
        if mu[d]:
            for n in range(d, K + 1, d): c[n] += mu[d]
    s = 1 + 0j; E = 0.0; cola = 0.0; maxabs = 0.0; ceros_ok = True
    for k in range(1, K + 1):
        x = chi[k % q]
        if x and c[k]: s -= x * c[k]
        a = abs(s) ** 2
        if k <= Q and abs(s) > 1e-12: ceros_ok = False
        E += a / (k * (k + 1))
        if k > K // 2: cola += a
        if abs(s) > maxabs: maxabs = abs(s)
    media = cola / (K - K // 2)
    return E + media / (K + 1), ceros_ok, maxabs

K = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
mu = mobius(K)
for nombre, q, chi in caracteres():
    print(f'χ {nombre}:')
    for Q in (10, 30, 100, 300, 1000):
        E, ok, mx = energia(Q, q, chi, K, mu)
        print(f'   Q={Q:5d}  E≈{E:.6f}  σ=0 en 1..Q: {ok}  max|σ|={mx:.1f}  E·Q^0 / log Q = {E/math.log(Q):.4f}')
