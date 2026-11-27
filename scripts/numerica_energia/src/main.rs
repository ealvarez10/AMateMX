//! Energía de AMate, E_Q (ζ) y E_{Q,χ} (caracteres de Dirichlet), con criba O(K log Q).
//!
//! Definiciones (AMateEnergia/Definiciones.lean y AMateDirichlet/Testigo.lean):
//!   c_Q(n) = Σ_{d | n, d ≤ Q} μ(d),   A(k) = Σ_{n ≤ k} c_Q(n) = Σ_{d ≤ Q} μ(d) ⌊k/d⌋.
//!   ζ:  σ_Q(k) = 1 + Σ_{d≤Q} μ(d){k/d} − Q m_Q {k/Q} − γ_Q (2{k/2Q} − {k/Q})
//!             = 1 − (A(k) − Q m_Q ⌊k/Q⌋) − γ_Q (⌊k/Q⌋ mod 2),
//!       m_Q = Σ μ(d)/d,  t_Q = 1 − Σ μ(d) log(Q/d)/d,  γ_Q = Q t_Q / log 2.
//!   χ:  σ_{Q,χ}(k) = 1 − Σ_{n ≤ k} χ(n) c_Q(n)   (exacto en ℤ[i] para χ mod 3, 4, 5).
//!   E = Σ_{k ≥ 1} |σ(k)|² / (k(k+1)).
//!
//! La suma se corta en K. La cola Σ_{k>K} w_k |σ_k|² ≈ M/(K+1), con M la media de |σ|² en
//! (K/2, K]; la diferencia entre las medias de (K/2, 3K/4] y (3K/4, K] da una cota del error.
//!
//! Uso:
//!   energia_rapida <modo> <K> <Q1> [Q2 ...]      modo ∈ {zeta, chi3, chi4, chi5}
//!   energia_rapida volcar <modo> <Q> <kmax>      imprime σ(k) para 1 ≤ k ≤ kmax
//! K puede escribirse como "x<f>" para usar K = f·Q.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Instant;

#[derive(Clone)]
enum Modo {
    Zeta,
    Chi { n: u64, re: Vec<i64>, im: Vec<i64> },
}

fn modo_de(nombre: &str) -> Modo {
    match nombre {
        "zeta" => Modo::Zeta,
        // χ mod 3 y mod 4 reales; χ mod 5 de orden 4 con χ(2) = i.
        "chi3" => Modo::Chi { n: 3, re: vec![0, 1, -1], im: vec![0, 0, 0] },
        "chi4" => Modo::Chi { n: 4, re: vec![0, 1, 0, -1], im: vec![0, 0, 0, 0] },
        "chi5" => Modo::Chi { n: 5, re: vec![0, 1, 0, 0, -1], im: vec![0, 0, 1, -1, 0] },
        _ => panic!("modo desconocido: {nombre}"),
    }
}

fn mobius(n: usize) -> Vec<i8> {
    let mut mu = vec![1i8; n + 1];
    let mut compuesto = vec![false; n + 1];
    let mut primos = Vec::new();
    mu[0] = 0;
    for i in 2..=n {
        if !compuesto[i] {
            primos.push(i);
            mu[i] = -1;
        }
        for &p in &primos {
            let ip = i * p;
            if ip > n {
                break;
            }
            compuesto[ip] = true;
            if i % p == 0 {
                mu[ip] = 0;
                break;
            }
            mu[ip] = -mu[i];
        }
    }
    mu
}

/// Suma compensada (Kahan–Babuška–Neumaier).
#[derive(Clone, Copy, Default)]
struct Suma {
    s: f64,
    c: f64,
}
impl Suma {
    fn add(&mut self, x: f64) {
        let t = self.s + x;
        if self.s.abs() >= x.abs() {
            self.c += (self.s - t) + x;
        } else {
            self.c += (x - t) + self.s;
        }
        self.s = t;
    }
    fn val(&self) -> f64 {
        self.s + self.c
    }
    fn merge(&mut self, o: &Suma) {
        self.add(o.s);
        self.add(o.c);
    }
}

#[derive(Clone, Default)]
struct Parcial {
    e: Suma,
    m1: Suma,
    m2: Suma,
    n1: u64,
    n2: u64,
    maxabs: f64,
    ceros_ok: bool,
    deriva: f64,
}

struct Problema {
    modo: Modo,
    q: u64,
    k: u64,
    divs: Vec<(u64, i32)>, // d ≤ Q libre de cuadrados, μ(d)
    alfa: f64,             // Q m_Q
    gam: f64,              // γ_Q
    sper_re: Vec<i64>,     // S_χ(y) para y mod N
    sper_im: Vec<i64>,
}

impl Problema {
    fn nuevo(modo: Modo, q: u64, k: u64, mu: &[i8]) -> Problema {
        let divs: Vec<(u64, i32)> =
            (1..=q).filter(|&d| mu[d as usize] != 0).map(|d| (d, mu[d as usize] as i32)).collect();
        let mut m = Suma::default();
        let mut t = Suma::default();
        for &(d, s) in &divs {
            let df = d as f64;
            m.add(s as f64 / df);
            t.add(s as f64 / df * ((q as f64) / df).ln());
        }
        let m_q = m.val();
        let t_q = 1.0 - t.val();
        let gam = (q as f64) * t_q / std::f64::consts::LN_2;
        let (mut sper_re, mut sper_im) = (Vec::new(), Vec::new());
        if let Modo::Chi { n, re, im } = &modo {
            // S(y) = Σ_{1≤m≤y} χ(m); periódica de periodo N para χ no principal.
            let (mut a, mut b) = (0i64, 0i64);
            sper_re.push(0);
            sper_im.push(0);
            for y in 1..*n {
                a += re[y as usize];
                b += im[y as usize];
                sper_re.push(a);
                sper_im.push(b);
            }
            // comprobación: S(N) = 0
            let tot: i64 = re.iter().sum::<i64>().abs() + im.iter().sum::<i64>().abs();
            assert_eq!(tot, 0, "el carácter debe ser no principal");
        }
        Problema { modo, q, k, divs, alfa: (q as f64) * m_q, gam, sper_re, sper_im }
    }

    /// D_j = A(jQ) − Q m_Q j = −Σ_{d≤Q} μ(d) {jQ/d}.
    fn d_directo(&self, j: u64) -> f64 {
        let jq = j * self.q;
        let mut s = Suma::default();
        for &(d, m) in &self.divs {
            let r = jq % d;
            if r != 0 {
                s.add(-(m as f64) * (r as f64) / (d as f64));
            }
        }
        s.val()
    }

    /// T(y) = Σ_{d≤Q} μ(d) χ(d) S(⌊y/d⌋), en ℤ[i].
    fn t_directo(&self, y: u64) -> (i64, i64) {
        let (n, re, im) = match &self.modo {
            Modo::Chi { n, re, im } => (*n, re, im),
            _ => unreachable!(),
        };
        let (mut a, mut b) = (0i64, 0i64);
        for &(d, m) in &self.divs {
            let (cr, ci) = (re[(d % n) as usize], im[(d % n) as usize]);
            if cr == 0 && ci == 0 {
                continue;
            }
            let r = ((y / d) % n) as usize;
            let (sr, si) = (self.sper_re[r], self.sper_im[r]);
            let m = m as i64;
            a += m * (cr * sr - ci * si);
            b += m * (cr * si + ci * sr);
        }
        (a, b)
    }

    fn criba(&self, a: u64, b: u64, c: &mut Vec<i32>) {
        c.clear();
        c.resize((b - a) as usize, 0);
        for &(d, m) in &self.divs {
            let mut n = a.div_ceil(d) * d;
            while n < b {
                c[(n - a) as usize] += m;
                n += d;
            }
        }
    }

    /// Procesa k ∈ [a, b); para ζ, a es múltiplo de Q.
    fn bloque(&self, a: u64, b: u64, c: &mut Vec<i32>, p: &mut Parcial, volcar: Option<&mut Vec<f64>>) {
        self.criba(a, b, c);
        let (h1, h2) = (self.k / 2, self.k / 2 + self.k / 4);
        let mut volcado = volcar;
        let registrar = |k: u64, s2: f64, abs: f64, p: &mut Parcial| {
            if k == 0 {
                return;
            }
            let kf = k as f64;
            p.e.add(s2 / (kf * (kf + 1.0)));
            if k > h1 && k <= h2 {
                p.m1.add(s2);
                p.n1 += 1;
            } else if k > h2 {
                p.m2.add(s2);
                p.n2 += 1;
            }
            if abs > p.maxabs {
                p.maxabs = abs;
            }
        };
        match &self.modo {
            Modo::Zeta => {
                let q = self.q;
                let mut j = a / q;
                let mut dj = self.d_directo(j);
                let mut r: i64 = 0; // A(k) − A(jQ)
                for k in a..b {
                    if k % q == 0 && k != a {
                        // D_{j+1} = D_j + (A((j+1)Q) − A(jQ)) − Q m_Q
                        dj += (r + c[(k - a) as usize] as i64) as f64 - self.alfa;
                        j += 1;
                        r = 0;
                    } else if k != a {
                        r += c[(k - a) as usize] as i64;
                    }
                    let paridad = if j % 2 == 1 { self.gam } else { 0.0 };
                    let s = 1.0 - dj - (r as f64) - paridad;
                    if k >= 1 && k < q && s.abs() > 1e-9 {
                        p.ceros_ok = false;
                    }
                    if let Some(v) = volcado.as_deref_mut() {
                        if k >= 1 {
                            v.push(s);
                        }
                    }
                    registrar(k, s * s, s.abs(), p);
                }
                // deriva del recálculo incremental frente al valor directo
                let dd = self.d_directo(j);
                p.deriva = p.deriva.max((dd - dj).abs());
            }
            Modo::Chi { n, re, im } => {
                let (mut ta, mut tb) = if a == 0 { (0, 0) } else { self.t_directo(a - 1) };
                for k in a..b {
                    if k >= 1 {
                        let x = (k % n) as usize;
                        let cc = c[(k - a) as usize] as i64;
                        ta += re[x] * cc;
                        tb += im[x] * cc;
                    }
                    let (sr, si) = (1 - ta, -tb);
                    let s2 = (sr * sr + si * si) as f64;
                    if k >= 1 && k <= self.q && s2 != 0.0 {
                        p.ceros_ok = false;
                    }
                    if let Some(v) = volcado.as_deref_mut() {
                        if k >= 1 {
                            v.push(sr as f64);
                            v.push(si as f64);
                        }
                    }
                    registrar(k, s2, s2.sqrt(), p);
                }
            }
        }
    }
}

fn resolver(pr: &Problema, hilos: usize) -> Parcial {
    let objetivo: u64 = std::env::var("ENERGIA_BLOQUE").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 20);
    let largo = match pr.modo {
        Modo::Zeta => pr.q * (objetivo / pr.q).max(1),
        _ => objetivo,
    };
    let fin = pr.k + 1; // k ∈ [0, K]
    let nbloques = fin.div_ceil(largo) as usize;
    let siguiente = AtomicUsize::new(0);
    let parciales: Vec<Parcial> = thread::scope(|sc| {
        let mut hs = Vec::new();
        for _ in 0..hilos {
            hs.push(sc.spawn(|| {
                let mut p = Parcial { ceros_ok: true, ..Default::default() };
                let mut c = Vec::new();
                loop {
                    let i = siguiente.fetch_add(1, Ordering::Relaxed);
                    if i >= nbloques {
                        break;
                    }
                    let a = i as u64 * largo;
                    let b = (a + largo).min(fin);
                    pr.bloque(a, b, &mut c, &mut p, None);
                }
                p
            }));
        }
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut tot = Parcial { ceros_ok: true, ..Default::default() };
    for p in &parciales {
        tot.e.merge(&p.e);
        tot.m1.merge(&p.m1);
        tot.m2.merge(&p.m2);
        tot.n1 += p.n1;
        tot.n2 += p.n2;
        tot.maxabs = tot.maxabs.max(p.maxabs);
        tot.ceros_ok &= p.ceros_ok;
        tot.deriva = tot.deriva.max(p.deriva);
    }
    tot
}

fn leer_k(s: &str, q: u64) -> u64 {
    if let Some(f) = s.strip_prefix('x') {
        // "x<f>" o "x<f>:<mínimo>": K = max(f·Q, mínimo)
        let (f, minimo) = match f.split_once(':') {
            Some((a, b)) => (a, b.replace('_', "").parse::<f64>().unwrap() as u64),
            None => (f, 0),
        };
        ((f.parse::<f64>().unwrap() * q as f64) as u64).max(minimo)
    } else {
        s.replace('_', "").parse::<f64>().unwrap() as u64
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let hilos = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    if args[1] == "volcar" {
        let modo = modo_de(&args[2]);
        let q: u64 = args[3].parse().unwrap();
        let kmax: u64 = args[4].parse().unwrap();
        let mu = mobius(q as usize);
        let pr = Problema::nuevo(modo.clone(), q, kmax, &mu);
        let mut p = Parcial { ceros_ok: true, ..Default::default() };
        let mut c = Vec::new();
        let mut v = Vec::new();
        pr.bloque(0, kmax + 1, &mut c, &mut p, Some(&mut v));
        match modo {
            Modo::Zeta => v.iter().for_each(|x| println!("{x:.12}")),
            _ => v.chunks(2).for_each(|x| println!("{} {}", x[0], x[1])),
        }
        eprintln!("E_K={:.15} ceros_ok={}", p.e.val(), p.ceros_ok);
        return;
    }
    let modo = modo_de(&args[1]);
    let qs: Vec<u64> = args[3..].iter().map(|s| s.parse().unwrap()).collect();
    let qmax = *qs.iter().max().unwrap();
    let mu = mobius(qmax as usize);
    println!("modo,Q,K,E_K,M,cola,E,err_cola,max_abs_sigma,ceros_ok,deriva,segundos");
    for &q in &qs {
        let k = leer_k(&args[2], q);
        let t0 = Instant::now();
        let pr = Problema::nuevo(modo.clone(), q, k, &mu);
        let p = resolver(&pr, hilos);
        let (m1, m2) = (p.m1.val() / p.n1 as f64, p.m2.val() / p.n2 as f64);
        let m = (p.m1.val() + p.m2.val()) / (p.n1 + p.n2) as f64;
        let cola = m / (k as f64 + 1.0);
        let err = (m1 - m2).abs() / (k as f64 + 1.0);
        let e = p.e.val() + cola;
        println!(
            "{},{},{},{:.12},{:.6},{:.3e},{:.12},{:.3e},{:.3},{},{:.2e},{:.2}",
            args[1], q, k, p.e.val(), m, cola, e, err, p.maxabs, p.ceros_ok, p.deriva,
            t0.elapsed().as_secs_f64()
        );
    }
}
