# Numerical study of the energy / Estudio numérico de la energía

Computes the energy E_Q of the witness for ζ (`AMateEnergia/Definiciones.lean`) and E_{Q,χ} for Dirichlet characters (`AMateDirichlet/Testigo.lean`), as used in Section 7 of the paper.

## Method

Expanding {k/d} = k/d − ⌊k/d⌋, the witness becomes

σ_Q(k) = 1 − A_Q(k) + Q m_Q ⌊k/Q⌋ − γ_Q·(⌊k/Q⌋ mod 2), where A_Q(k) = Σ_{n≤k} c_Q(n) and c_Q(n) = Σ_{d|n, d≤Q} μ(d).

For characters, σ_{Q,χ}(k) = 1 − Σ_{n≤k} χ(n) c_Q(n), which is exact in ℤ[i] for the characters used.

A sieve gives c_Q(n) for n ≤ K in O(K log Q) operations. The sum is truncated at K = max(2000·Q, 10⁷), and the tail is estimated from the mean of |σ|² on (K/2, K].

## Files

| File | Contents |
|---|---|
| `src/main.rs` | parallel computation (Rust, standard library only) |
| `validar.py` | check against the literal Lean definitions |
| `correr.sh` | all runs of the paper |
| `ceros.py` | ordinates of the zeros of ζ and L(s,χ), via the Hurwitz zeta function |
| `analizar.py` | tables, frequency test and SVG plots |
| `resultados/` | CSV data, `analisis.txt`, `resumen.json`, `ceros.json` and plots |

## Reproduce / Reproducir

```bash
cargo build --release --offline
python3 -I validar.py target/release/energia_rapida
./correr.sh target/release/energia_rapida
python3 -I ceros.py 60
python3 -I analizar.py
```

`analizar.py` and `ceros.py` read and write `resultados/` relative to the current directory.

## Resumen

Calcula E_Q para ζ y E_{Q,χ} para los caracteres reales módulo 3 y 4 y el carácter módulo 5 con χ(2) = i.

- `validar.py` compara con las definiciones de Lean: la diferencia es 0 para χ y menor que 5·10⁻¹³ para ζ.
- En 26 núcleos, todas las corridas tardan unos 75 minutos.
