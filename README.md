# AMate: an energy criterion for the Riemann hypothesis, formalized in Lean 4

Author: **Ernesto Álvarez** (independent researcher, Mexico). Versión en español: [LEEME.md](LEEME.md).

This repository contains the Lean 4 formalization accompanying the paper *An energy criterion for the Riemann hypothesis, its calibration, and its formal verification in Lean* ([articulo/](articulo/), in five languages).

**What this is not.** This work does **not** contain an independent proof of the Riemann hypothesis. Its own results are unconditional theorems and equivalences. One optional part (`AMateConAlpoge`) composes them with a Lean library, announced in November 2026, that claims a proof of RH. That library has been machine-checked but, to our knowledge, not yet peer reviewed.

## Main results

Let σ_Q be the explicit witness built from the Möbius function, fractional parts {k/d} and two correction terms, and let E_Q = Σ_k σ_Q(k)² / (k(k+1)) be its energy ([AMateEnergia/Definiciones.lean](AMateEnergia/Definiciones.lean)).

| Result | Lean name |
|---|---|
| **Unconditional calibration:** lim log(2 + E_Q) / log Q = 2Θ − 1, where Θ is the supremum of 1/2 and the real parts of the zeros of ζ | `AMate.tendsto_log_energia_div_log` |
| RH ⇔ E_Q ≪_ε Q^ε (uniform and cofinal versions) | `AMate.rh_iff_energia_subpolinomial`, `AMate.rh_iff_energia_cofinal` |
| No zeros in Re s > θ ⇔ E_Q ≪_ε Q^(2θ−1+ε), for 1/2 ≤ θ < 1 | `AMate.sin_ceros_iff_energia_theta` |
| A zero ρ with Re ρ > 1/2 forces E_Q ≥ c Q^(2 Re ρ − 1) | `AMate.cota_inferior_energia_cero` |
| RH ⇔ arithmetic forms: von Mangoldt windows, a prime deficit, a hyperbolic quadrature sum | `AMate.rh_iff_ventana_vonMangoldt`, `AMate.rh_iff_deficit_primos`, `AMate.rh_iff_S_hiperbolica` |
| Barrier theorem: monotonicity of ϑ together with the classical zero-free regions cannot prove the hyperbolic bound | `AMate.explosion_ventana_ondaPrueba` |
| **Dirichlet L-functions** (χ non-principal): L(s,χ) = s ∫₁^∞ S_χ(⌊x⌋) x^(−s−1) dx for Re s > 0; Mellin transform of the witness; a subpolynomial energy along a sequence implies L(s,χ) ≠ 0 for Re s > 1/2 | `AMate.Dirichlet.LFunction_eq_integral`, `AMate.Dirichlet.integral_sigma_floor`, `AMate.Dirichlet.LFunction_ne_zero_de_energia_cofinal` |
| **Miller test:** for odd composite n, the strong liars lie in a proper subgroup of (ℤ/nℤ)ˣ; the deterministic test is correct given any Bach-type bound | `AMate.Miller.mentirosos_en_subgrupo_propio`, `AMate.Miller.test_miller_correcto` |

All of them use only Mathlib and the axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`.

For Dirichlet L-functions only one direction is formalized: the implication GRH ⇒ subpolynomial energy is not yet done.

AMate’s prime-deficit criterion and Theorem 6.1 of Lee Crossley’s *The Crossley Criteria* both characterise RH by subpolynomial growth of a one-sided sum at fourth powers with weight $m^{-3}$ on arbitrarily late windows. Crossley applies the test to a Möbius remainder. [Theorem 6.1](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/806ba8b6acba5dbef43ad394590585e8d09aa950/paper/crossley-criteria-riemann-hypothesis.md#L273-L293) and [DOI 10.5281/zenodo.24466908](https://doi.org/10.5281/zenodo.24466908).

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.33.1) is pinned in `lean-toolchain`, and Mathlib is pinned at revision `0df444a`.

```bash
lake exe cache get        # download Mathlib's compiled cache
lake build                # AMateEnergia, AMateDirichlet, AMateMiller
lake env lean Axiomas.lean
```

The last command prints the axioms of the main theorems. Every line must list only `propext`, `Classical.choice` and `Quot.sound`.

## Independent kernel check

The proofs of the main theorems, together with everything they use from Mathlib, were exported with `lean4export` and rechecked by the independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib): 67,319 declarations, no errors, and only the three standard axioms in the export. See [verificacion/](verificacion/) and [scripts/verificar_con_nanoda.sh](scripts/verificar_con_nanoda.sh).

## Optional: composition with Alpöge's library

[AMateConAlpoge/](AMateConAlpoge/) contains three files:
- `Composicion.lean` proves `AMate.energia_subpolinomial_alpoge`: E_Q ≤ C_ε Q^ε for all Q ≥ 2, with no hypothesis. It applies `AMate.energia_subpolinomial` to `riemannHypothesis`.
- `Consecuencias.lean` derives, also with no hypothesis, the Littlewood bound for the Mertens function and a smoothed von Mangoldt sum with square-root error.
- `VerificacionConjunta.lean` loads the whole of `AMateEnergia` together with the composition, in one environment, and prints the axioms of twelve key declarations.

These files need the compiled library (175,187 modules, Lean 4.33.1, same Mathlib). Our own build of it took 11 hours on 64 cores and 255 GB of RAM. To compile them, uncomment the corresponding blocks in `lakefile.toml`.

[verificacion/reproduccion_vm/](verificacion/reproduccion_vm/) documents an independent rebuild of that library from source. All 175,187 `.olean` files came out byte-identical to the list published by MIT, including the module that MIT documents as nondeterministic. The script used is included.

## Repository layout

| Path | Contents |
|---|---|
| `AMateEnergia/` | 26 modules: the energy criterion for ζ |
| `AMateDirichlet/` | extension to Dirichlet L-functions |
| `AMateMiller/` | Miller test, algebraic part |
| `AMateConAlpoge/` | optional composition (not built by default) |
| `Axiomas.lean` | axiom check of the main theorems |
| `scripts/` | nanoda recheck; numerical experiment for Dirichlet characters |
| `verificacion/` | evidence: rebuild of Alpöge's library, nanoda output |
| `articulo/` | the paper in English, Spanish, French, Chinese and Hindi (LaTeX and PDF) |

## License

- **Code:** Apache License 2.0 ([LICENSE](LICENSE)), the same as Mathlib.
- **Paper** in `articulo/`: Creative Commons Attribution 4.0 (CC BY 4.0).

## How to cite

See [CITATION.cff](CITATION.cff).

## Use of AI

The formal proofs, the numerical checks and the translations of the paper were developed with the assistance of language models (Claude and Codex). All proofs are checked by the Lean kernel, and the main theorems were also checked by an independent kernel. The novelty and correctness of the mathematics still require review by specialists.
