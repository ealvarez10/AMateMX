"""Análisis de la numérica de energía: tablas, tendencia, periodograma y gráficas SVG.

Uso: python3 -I analizar.py   (lee resultados/*.csv y resultados/ceros.json)
"""
import csv
import json
import math
import os

R = "resultados"
NOMBRES = {"zeta": "ζ(s)", "chi3": "L(s,χ) mod 3", "chi4": "L(s,χ) mod 4", "chi5": "L(s,χ) mod 5, orden 4"}
COLORES = {"zeta": "#1f4e9c", "chi3": "#b8401f", "chi4": "#2e7d32", "chi5": "#7b3fa0"}


def leer(nombre):
    p = os.path.join(R, nombre)
    if not os.path.exists(p):
        return []
    with open(p) as fh:
        filas = [r for r in csv.DictReader(fh) if r.get("E")]
    for r in filas:
        for k in ("Q", "K"):
            r[k] = int(r[k])
        for k in ("E_K", "M", "cola", "E", "err_cola", "max_abs_sigma", "segundos"):
            r[k] = float(r[k])
        r["ceros_ok"] = r["ceros_ok"] == "true"
    return filas


# ---------------------------------------------------------------- estadística
def regresion(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    a = my - b * mx
    res = [y - a - b * x for x, y in zip(xs, ys)]
    s2 = sum(r * r for r in res) / (n - 2)
    return a, b, math.sqrt(s2 / sxx), res


def lomb_scargle(ts, ys, freqs):
    n = len(ts)
    my = sum(ys) / n
    ys = [y - my for y in ys]
    var = sum(y * y for y in ys) / (n - 1)
    out = []
    for w in freqs:
        s2 = sum(math.sin(2 * w * t) for t in ts)
        c2 = sum(math.cos(2 * w * t) for t in ts)
        tau = math.atan2(s2, c2) / (2 * w)
        cc = [math.cos(w * (t - tau)) for t in ts]
        ss = [math.sin(w * (t - tau)) for t in ts]
        yc = sum(y * c for y, c in zip(ys, cc))
        ysn = sum(y * s for y, s in zip(ys, ss))
        p = (yc * yc / sum(c * c for c in cc) + ysn * ysn / sum(s * s for s in ss)) / (2 * var)
        out.append(p)
    return out


def picos(freqs, pot, k=8, sep=0.6):
    idx = sorted(range(1, len(pot) - 1), key=lambda i: -pot[i])
    elegidos = []
    for i in idx:
        if pot[i] < pot[i - 1] or pot[i] < pot[i + 1]:
            continue
        if all(abs(freqs[i] - freqs[j]) > sep for j in elegidos):
            elegidos.append(i)
        if len(elegidos) == k:
            break
    return [(freqs[i], pot[i]) for i in elegidos]


def resolver_ls(filas_x, ys, lam=1e-9):
    """Mínimos cuadrados por ecuaciones normales (con una regularización mínima)."""
    m = len(filas_x[0])
    a = [[0.0] * m for _ in range(m)]
    b = [0.0] * m
    for x, y in zip(filas_x, ys):
        for i in range(m):
            xi = x[i]
            b[i] += xi * y
            fila = a[i]
            for j in range(i, m):
                fila[j] += xi * x[j]
    for i in range(m):
        a[i][i] += lam
        for j in range(i):
            a[i][j] = a[j][i]
    # eliminación gaussiana con pivoteo
    for c in range(m):
        piv = max(range(c, m), key=lambda r: abs(a[r][c]))
        a[c], a[piv] = a[piv], a[c]
        b[c], b[piv] = b[piv], b[c]
        for r in range(c + 1, m):
            f = a[r][c] / a[c][c]
            if f:
                for j in range(c, m):
                    a[r][j] -= f * a[c][j]
                b[r] -= f * b[c]
    sol = [0.0] * m
    for i in range(m - 1, -1, -1):
        sol[i] = (b[i] - sum(a[i][j] * sol[j] for j in range(i + 1, m))) / a[i][i]
    return sol


def r2_senoides(us, ys, frecs):
    filas = [[1.0, u] + [g(f * u) for f in frecs for g in (math.cos, math.sin)] for u in us]
    sol = resolver_ls(filas, ys)
    ajuste = [sum(c * x for c, x in zip(sol, fila)) for fila in filas]
    my = sum(ys) / len(ys)
    sst = sum((y - my) ** 2 for y in ys)
    sse = sum((y - a) ** 2 for y, a in zip(ys, ajuste))
    return 1 - sse / sst, ajuste


def frecuencias_predichas(ceros_lista, gmax, fmin, fmax):
    """{|γ − γ'|} para ceros γ, γ' (con signo) de ordenada |γ| ≤ gmax; ζ y χ reales: ±γ."""
    zs = [g for g in ceros_lista if abs(g) <= gmax]
    fr = set()
    for i, a in enumerate(zs):
        for b in zs[i + 1:]:
            f = abs(a - b)
            if fmin <= f <= fmax:
                fr.add(round(f, 6))
    return sorted(fr)


# ---------------------------------------------------------------- SVG
def svg(series, titulo, xlab, ylab, ancho=900, alto=430, vlineas=(), xr=None, yr=None):
    ml, mr, mt, mb = 78, 24, 44, 56
    xs = [x for s in series for x in s["x"]]
    ys = [y for s in series for y in s["y"]]
    x0, x1 = xr or (min(xs), max(xs))
    y0, y1 = yr or (min(ys), max(ys))
    if y1 == y0:
        y1 = y0 + 1
    pad = (y1 - y0) * 0.06
    y0, y1 = (y0 - pad, y1 + pad) if not yr else (y0, y1)
    X = lambda x: ml + (x - x0) / (x1 - x0) * (ancho - ml - mr)
    Y = lambda y: alto - mb - (y - y0) / (y1 - y0) * (alto - mt - mb)

    def ticks(a, b, n=6):
        paso = 10 ** math.floor(math.log10((b - a) / n))
        for m in (1, 2, 2.5, 5, 10):
            if (b - a) / (paso * m) <= n:
                paso *= m
                break
        t = math.ceil(a / paso) * paso
        out = []
        while t <= b + 1e-12:
            out.append(round(t, 10))
            t += paso
        return out

    extra = 26 if any(s.get("label") for s in series) else 0
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {ancho} {alto + extra}" font-family="Helvetica, Arial, sans-serif" font-size="13">',
         '<rect width="100%" height="100%" fill="#ffffff"/>',
         f'<text x="{ancho/2}" y="24" text-anchor="middle" font-size="15" font-weight="600" fill="#222">{titulo}</text>']
    for t in ticks(y0, y1):
        o.append(f'<line x1="{ml}" x2="{ancho-mr}" y1="{Y(t):.1f}" y2="{Y(t):.1f}" stroke="#e6e6e6"/>')
        o.append(f'<text x="{ml-8}" y="{Y(t)+4:.1f}" text-anchor="end" fill="#555">{t:g}</text>')
    for t in ticks(x0, x1, 10):
        o.append(f'<line x1="{X(t):.1f}" x2="{X(t):.1f}" y1="{alto-mb}" y2="{alto-mb+5}" stroke="#888"/>')
        o.append(f'<text x="{X(t):.1f}" y="{alto-mb+20}" text-anchor="middle" fill="#555">{t:g}</text>')
    for v, etiqueta in vlineas:
        if x0 <= v <= x1:
            o.append(f'<line x1="{X(v):.1f}" x2="{X(v):.1f}" y1="{mt}" y2="{alto-mb}" stroke="#c0392b" stroke-dasharray="4 4" stroke-width="1"/>')
            if etiqueta:
                o.append(f'<text x="{X(v)+3:.1f}" y="{mt+12}" fill="#c0392b" font-size="11">{etiqueta}</text>')
    o.append(f'<rect x="{ml}" y="{mt}" width="{ancho-ml-mr}" height="{alto-mt-mb}" fill="none" stroke="#999"/>')
    for s in series:
        pts = [(X(x), Y(y)) for x, y in zip(s["x"], s["y"]) if x0 <= x <= x1]
        if s.get("puntos"):
            for px, py in pts:
                o.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="{s.get("r",1.3)}" fill="{s["color"]}" fill-opacity="{s.get("op",0.5)}"/>')
        else:
            d = " ".join(f"{px:.1f},{py:.1f}" for px, py in pts)
            o.append(f'<polyline points="{d}" fill="none" stroke="{s["color"]}" stroke-width="{s.get("w",1.6)}" stroke-opacity="{s.get("op",1)}"/>')
    etiquetas = [s for s in series if s.get("label")]
    lx = ml
    for s in etiquetas:
        o.append(f'<rect x="{lx}" y="{alto+6}" width="14" height="4" fill="{s["color"]}"/>')
        o.append(f'<text x="{lx+20}" y="{alto+12}" fill="#333">{s["label"]}</text>')
        lx += 26 + 7.2 * len(s["label"])
    o.append(f'<text x="{(ml+ancho-mr)/2}" y="{alto-14}" text-anchor="middle" fill="#333">{xlab}</text>')
    o.append(f'<text transform="translate(18,{(mt+alto-mb)/2}) rotate(-90)" text-anchor="middle" fill="#333">{ylab}</text>')
    o.append("</svg>")
    return "\n".join(o)


def guardar(nombre, contenido):
    with open(os.path.join(R, nombre), "w") as fh:
        fh.write(contenido)


# ---------------------------------------------------------------- análisis
ceros = json.load(open(os.path.join(R, "ceros.json"))) if os.path.exists(os.path.join(R, "ceros.json")) else {}
informe = []
resumen = {}
for modo in ("zeta", "chi3", "chi4", "chi5"):
    malla = leer(f"{modo}_malla_log.csv")
    todos = leer(f"{modo}_todos_Q_hasta_5000.csv")
    extra = leer("zeta_hasta_1e7.csv") if modo == "zeta" else []
    if not malla:
        continue
    filas = sorted({r["Q"]: r for r in malla + todos + extra}.values(), key=lambda r: r["Q"])
    malos = [r["Q"] for r in filas if not r["ceros_ok"]]
    peor_err = max(r["err_cola"] / r["E"] for r in filas)
    # tabla por décadas
    tabla = []
    for e in range(1, 8):
        q = 10 ** e
        r = next((r for r in filas if r["Q"] == q), None)
        if r is None:
            cerca = min(filas, key=lambda r: abs(math.log(r["Q"]) - math.log(q)))
            if abs(math.log(cerca["Q"]) - math.log(q)) > 0.02:
                continue
            r = cerca
        tabla.append((r["Q"], r["E"], r["err_cola"], r["K"]))
    # tendencia en ln Q, para Q ≥ 100 en la malla
    sel = [r for r in malla + extra if r["Q"] >= 100]
    us = [math.log(r["Q"]) for r in sel]
    es = [r["E"] for r in sel]
    a, b, sb, res = regresion(us, es)
    # extremos por década
    decadas = []
    for e in range(1, 7):
        en = [r["E"] for r in filas if 10 ** e <= r["Q"] < 10 ** (e + 1)]
        if en:
            decadas.append((e, min(en), max(en), sum(en) / len(en), len(en)))
    # periodograma de los residuos en u = ln Q (malla, Q ≥ 30)
    sel2 = [r for r in malla if r["Q"] >= 30]
    u2 = [math.log(r["Q"]) for r in sel2]
    a2, b2, _, res2 = regresion(u2, [r["E"] for r in sel2])
    freqs = [0.5 + 0.02 * i for i in range(int((45 - 0.5) / 0.02))]
    pot = lomb_scargle(u2, res2, freqs)
    pk = picos(freqs, pot)
    gam = [abs(g) for g in ceros.get(modo, [])]
    _zs = ceros.get(modo, [])
    if modo != "chi5":
        _zs = sorted(set(_zs + [-g for g in _zs]))
    _zs = [g for g in _zs if abs(g) <= {"zeta": 33.0, "chi3": 21.0, "chi4": 19.0, "chi5": 15.0}[modo]]
    _pares = [(abs(a - b), a, b) for i, a in enumerate(_zs) for b in _zs[i + 1:]]
    def cercano(f):
        if not _pares:
            return None
        d, a, b = min(_pares, key=lambda x: abs(x[0] - f))
        return (d, f - d, a, b) if abs(f - d) <= 0.2 else None
    # prueba de frecuencias: senoides en |γ ± γ'| frente a conjuntos aleatorios del mismo tamaño
    import random
    zs_signo = ceros.get(modo, [])
    if modo != "chi5":
        zs_signo = sorted(set([g for g in zs_signo] + [-g for g in zs_signo]))
    gmax = {"zeta": 33.0, "chi3": 21.0, "chi4": 19.0, "chi5": 15.0}[modo]
    pred = frecuencias_predichas(zs_signo, gmax, 0.8, 45.0)
    sel3 = [r for r in malla if r["Q"] >= 30]
    u3 = [math.log(r["Q"]) for r in sel3]
    e3 = [r["E"] for r in sel3]
    r2_pred, ajuste_pred = r2_senoides(u3, e3, pred)
    rnd = random.Random(20261126)
    r2_azar = []
    for _ in range(200):
        fr = sorted(rnd.uniform(0.8, 45.0) for _ in pred)
        r2_azar.append(r2_senoides(u3, e3, fr)[0])
    p_valor = (1 + sum(1 for r in r2_azar if r >= r2_pred)) / (1 + len(r2_azar))
    prueba = {"frecuencias": pred, "R2_predichas": r2_pred,
              "R2_azar_mediana": sorted(r2_azar)[len(r2_azar) // 2], "R2_azar_max": max(r2_azar),
              "p_valor": p_valor, "n_puntos": len(u3)}
    guardar(f"{modo}_ajuste_frecuencias.svg", svg(
        [{"x": u3, "y": e3, "color": "#111", "w": 1.1, "label": "E (malla en ln Q)"},
         {"x": u3, "y": ajuste_pred, "color": "#d62728", "w": 1.6, "op": 0.85,
          "label": f"{len(pred)} senoides en |γ ± γ'| (R² = {r2_pred:.2f})"}],
        f"E en ln Q y ajuste con frecuencias de ceros, {NOMBRES[modo]}", "ln Q", "E"))
    resumen[modo] = {
        "prueba_frecuencias": prueba,
        "puntos": len(filas), "Q_max": filas[-1]["Q"], "ceros_ok_todos": not malos,
        "peor_error_relativo_cola": peor_err, "tabla": tabla,
        "pendiente_por_unidad_lnQ": b, "error_pendiente": sb, "decadas": decadas,
        "picos": [(f, p, cercano(f)) for f, p in pk],
    }
    # gráficas
    s_todos = {"x": [math.log(r["Q"]) for r in todos], "y": [r["E"] for r in todos], "color": COLORES[modo],
               "puntos": True, "op": 0.25, "r": 1.0, "label": "todos los Q ≤ 5000"}
    s_malla = {"x": [math.log(r["Q"]) for r in malla + extra], "y": [r["E"] for r in malla + extra],
               "color": "#111", "w": 1.1, "label": "malla en ln Q"}
    # promedio de E en ventanas de ancho 0.1 en ln Q, con todos los Q disponibles
    pares = sorted((math.log(r["Q"]), r["E"]) for r in filas if r["Q"] >= 10)
    suav_x, suav_y = [], []
    u = math.log(10)
    while u <= pares[-1][0]:
        v = [e for x, e in pares if abs(x - u) <= 0.05]
        if len(v) >= 3:
            suav_x.append(u)
            suav_y.append(sum(v) / len(v))
        u += 0.01
    s_suav = {"x": suav_x, "y": suav_y, "color": "#e08e0b", "w": 2.2, "label": "promedio en ventanas de ln Q (±0.05)"}
    ys10 = [r["E"] for r in filas if r["Q"] >= 10]
    guardar(f"{modo}_energia.svg", svg([s_todos, s_malla, s_suav], f"Energía de AMate para {NOMBRES[modo]}, Q ≥ 10",
                                      "ln Q", "E", vlineas=[(math.log(10 ** e), f"10^{e}") for e in range(2, 8)],
                                      xr=(math.log(10), pares[-1][0]), yr=(min(ys10) * 0.97, max(ys10) * 1.03)))
    # periodograma del promedio por intervalos de 0.01 en ln Q con todos los enteros 100 ≤ Q ≤ 5000
    principales = sorted(_pares, key=lambda x: abs(x[1]) + abs(x[2]))[:4]
    def nombre_par(a, b):
        sub = "₀₁₂₃₄₅₆₇₈₉"
        if modo == "chi5":
            return f"{abs(a - b):.1f}"
        pos = sorted({abs(z) for z in _zs})
        i, j = sorted((pos.index(abs(a)) + 1, pos.index(abs(b)) + 1))
        gi, gj = "γ" + sub[i], "γ" + sub[j]
        if a * b < 0:
            return f"2{gi}" if i == j else f"{gi}+{gj}"
        return f"{gj}−{gi}"
    vl = [(d, nombre_par(a, b) if (d, a, b) in principales else "") for d, a, b in _pares if 0.5 <= d <= 45]
    densos = sorted((math.log(r["Q"]), r["E"]) for r in todos if r["Q"] >= 100)
    if densos:
        cajas = {}
        for x, e in densos:
            cajas.setdefault(round(x / 0.01), []).append(e)
        ub = [k * 0.01 for k in sorted(cajas)]
        eb = [sum(cajas[k]) / len(cajas[k]) for k in sorted(cajas)]
        _, _, _, resb = regresion(ub, eb)
        potb = lomb_scargle(ub, resb, freqs)
        resumen.setdefault(modo + "_densos", {})["picos"] = [(f, p, cercano(f)) for f, p in picos(freqs, potb)]
        guardar(f"{modo}_periodograma_densos.svg", svg([{"x": freqs, "y": potb, "color": COLORES[modo], "w": 1.3}],
                f"Periodograma del promedio de E por cajas de ln Q (todos los 100 ≤ Q ≤ 5000), {NOMBRES[modo]}",
                "frecuencia en u = ln Q", "potencia normalizada", vlineas=vl))
    guardar(f"{modo}_periodograma.svg", svg([{"x": freqs, "y": pot, "color": COLORES[modo], "w": 1.3}],
                                           f"Periodograma de E en u = ln Q, {NOMBRES[modo]} (líneas: |γ − γ′| de ceros bajos)",
                                           "frecuencia en u = ln Q", "potencia normalizada", vlineas=vl))

json.dump(resumen, open(os.path.join(R, "resumen.json"), "w"), indent=1, ensure_ascii=False)
for modo, r in resumen.items():
    if modo.endswith("_densos"):
        print(f"\n   [{modo}] picos del periodograma con todos los Q:", ", ".join(f"{f:.2f}" + (f" (|{c[2]:.2f} − ({c[3]:.2f})| = {c[0]:.2f}, Δ{c[1]:+.2f})" if c else " (sin pareja de ceros bajos)") for f, p, c in r["picos"][:6]))
        continue
    print(f"\n=== {NOMBRES[modo]}: {r['puntos']} valores de Q hasta {r['Q_max']}; σ=0 en el tramo inicial: {r['ceros_ok_todos']}; error relativo de cola ≤ {r['peor_error_relativo_cola']:.1e}")
    for q, e, err, k in r["tabla"]:
        print(f"   Q={q:>9}  E={e:.7f}  (±{err:.1e}, K={k:.1e})")
    print(f"   pendiente dE/d(lnQ) para Q≥100: {r['pendiente_por_unidad_lnQ']:+.2e} ± {r['error_pendiente']:.1e}")
    for e, mn, mx, med, n in r["decadas"]:
        print(f"   10^{e}..10^{e+1}: min {mn:.5f}  max {mx:.5f}  media {med:.5f}  ({n} Q)")
    pf = r["prueba_frecuencias"]
    print(f"   ajuste con {len(pf['frecuencias'])} frecuencias |γ±γ'|: R²={pf['R2_predichas']:.3f}; al azar: mediana {pf['R2_azar_mediana']:.3f}, máximo {pf['R2_azar_max']:.3f}; p≈{pf['p_valor']:.3f} ({pf['n_puntos']} puntos)")
    print("   picos del periodograma:", ", ".join(f"{f:.2f}" + (f" (|{c[2]:.2f} − ({c[3]:.2f})| = {c[0]:.2f}, Δ{c[1]:+.2f})" if c else " (sin pareja de ceros bajos)") for f, p, c in r["picos"][:6]))
