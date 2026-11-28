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
| **Dirichlet L-functions** (χ non-principal): GRH for χ ⇔ E_{Q,χ} ≪_ε Q^ε; no zeros in Re s > θ ⇔ E_{Q,χ} ≪_ε Q^(2θ−1+ε); unconditional calibration lim log(2 + E_{Q,χ}) / log Q = 2Θ_χ − 1; on the way, \|L(1/2 + ix, χ)\| ≪ (1 + \|x\|)^(1/3) | `AMate.Dirichlet.grh_iff_energia_subpolinomial`, `AMate.Dirichlet.sin_ceros_iff_energia_theta_L`, `AMate.Dirichlet.tendsto_log_energia_div_log_L`, `AMate.Dirichlet.L_recta_critica` |
| **Miller test:** for odd composite n, the strong liars lie in a proper subgroup of (ℤ/nℤ)ˣ; every proper subgroup lies in the kernel of a non-principal Dirichlet character; the executable test `esPrimoMiller B` (fast modular exponentiation) decides primality for every Bach-type bound B, unconditionally with B(n) = n; from GRH, the truncated explicit formula and the zero count in windows, B(n) = ⌊K(1 + log n)^4⌋ and B(n) = ⌊K(1 + log n)^2⌋ work for some K | `AMate.Miller.mentirosos_en_subgrupo_propio`, `AMate.Miller.cotaSubgruposPropios_of_cotaCaracteres`, `AMate.Miller.esPrimoMiller_correcto`, `AMate.Miller.esPrimoMiller_id_correcto`, `AMate.Miller.esPrimoMiller_de_grh`, `AMate.Miller.esPrimoMiller_de_grh_cuad` |
| **Bach's bound with explicit constant:** from GRH and analytic statements of Alpöge's library taken as hypotheses, every non-principal character mod n takes a value ≠ 1 at some a ≤ 2(log n)² coprime to n, for log n ≥ 64; hence `esPrimoMiller basesExplicitas`, with (⌊log₂ n⌋ + 1)² bases for n ≥ 2^93, is a certified executable primality test | `AMate.Miller.Explicito.cota_bach_explicita`, `AMate.Miller.esPrimoMiller_explicito` |

All of them use only Mathlib and the axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`.


## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.33.1) is pinned in `lean-toolchain`, and Mathlib is pinned at revision `0df444a`.

```bash
lake exe cache get        # download Mathlib's compiled cache
lake build                # AMateEnergia, AMateDirichlet, AMateMiller
lake env lean Axiomas.lean
```

The last command prints the axioms of the main theorems. Every line must list only `propext`, `Classical.choice` and `Quot.sound`.

## Independent kernel check

The proofs of the main theorems, together with everything they use from Mathlib, were exported with `lean4export` and rechecked by the independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib): 76,387 declarations, no errors, and only the three standard axioms in the export. See [verificacion/](verificacion/) and [scripts/verificar_con_nanoda.sh](scripts/verificar_con_nanoda.sh).

## Optional: composition with Alpöge's library

[AMateConAlpoge/](AMateConAlpoge/) contains six files:
- `Composicion.lean` proves `AMate.energia_subpolinomial_alpoge`: E_Q ≤ C_ε Q^ε for all Q ≥ 2, with no hypothesis. It applies `AMate.energia_subpolinomial` to `riemannHypothesis`.
- `Consecuencias.lean` derives, also with no hypothesis, the Littlewood bound for the Mertens function and a smoothed von Mangoldt sum with square-root error.
- `VerificacionConjunta.lean` loads the whole of `AMateEnergia` together with the composition, in one environment, and prints the axioms of twelve key declarations.
- `ComposicionDirichlet.lean` proves, with no hypothesis, E_{Q,χ} ≤ C_ε Q^ε and Θ_χ = 1/2 for every non-principal Dirichlet character, from `LFunction_ne_zero_of_half_lt_re`.
- `HipotesisAlpoge.lean` instantiates the analytic hypotheses of the explicit Bach bound (`HipHadamard`, `SerieDigamma`) with theorems of that library: Cauchy's formula on rectangles, the location and finiteness of the zeros, the regular part of L'/L, the functional equation of L'/L, bounds for the digamma function, good heights, and the digamma series. It leaves only GRH as a hypothesis (`AMate.Miller.esPrimoMiller_explicito_de_grh`).
- `MillerAlpoge.lean` proves, with no hypothesis, that Miller's test with ⌊K(1 + log n)^4⌋ or ⌊K(1 + log n)^2⌋ bases decides primality for some K, from `explicitFormula_closed`, `zerosWindow_closed` and `LFunction_eq_zero_re_of_isPrimitive`; that constant K is not explicit. With `HipotesisAlpoge.lean` it also proves, with no hypothesis, Bach's bound a ≤ 2(log n)² for log n ≥ 64 (`AMate.Miller.cota_bach_explicita_alpoge`) and the certified executable test `AMate.Miller.esPrimoMiller_explicito_alpoge`.

All of them compile with that library, and their theorems depend only on the three standard axioms. `HipotesisAlpoge.lean` does not import `Main`, so it was also compiled locally against the compiled library. `ComposicionDirichlet.lean` and `MillerAlpoge.lean` were compiled on 28 November 2026 on a virtual machine that rebuilt the library from source, with [verificacion/reproduccion_vm/amate_composiciones_vm.sh](verificacion/reproduccion_vm/amate_composiciones_vm.sh); the result, with the axioms of ten declarations and the hashes of the compiled sources, is in [verificacion/reproduccion_vm/composiciones_resultado.txt](verificacion/reproduccion_vm/composiciones_resultado.txt).

These files need the compiled library (175,187 modules, Lean 4.33.1, same Mathlib). Our own build of it took 11 hours on 64 cores and 255 GB of RAM. To compile them, uncomment the corresponding blocks in `lakefile.toml`.

[verificacion/reproduccion_vm/](verificacion/reproduccion_vm/) documents two independent rebuilds of that library from source, on two different virtual machines (23 and 28 November 2026). Both times, all 175,187 `.olean` files came out byte-identical to the list published by MIT, including the module that MIT documents as nondeterministic. The script used is included.

## Repository layout

| Path | Contents |
|---|---|
| `AMateEnergia/` | 26 modules: the energy criterion for ζ |
| `AMateDirichlet/` | the criterion and its calibration for Dirichlet L-functions (8 modules) |
| `AMateMiller/` | Miller test: algebraic part, bridge to Dirichlet characters, executable test, Bach-type bounds from GRH, and Bach's bound 2(log n)² with explicit constant (26 modules) |
| `AMateConAlpoge/` | optional composition (not built by default) |
| `Axiomas.lean` | axiom check of the main theorems |
| `scripts/` | nanoda recheck; numerical study of $E_Q$ and $E_{Q,\chi}$ (`scripts/numerica_energia`, Section 7 of the paper); executable Miller examples (`scripts/miller_ejemplos.lean`) |
| `verificacion/` | evidence: rebuild of Alpöge's library, nanoda output |
| `articulo/` | the paper in English, Spanish, French, Chinese and Hindi (LaTeX and PDF) |

## License

- **Code:** Apache License 2.0 ([LICENSE](LICENSE)), the same as Mathlib.
- **Paper** in `articulo/`: Creative Commons Attribution 4.0 (CC BY 4.0).

## How to cite

See [CITATION.cff](CITATION.cff).

## Use of AI

The formal proofs, the numerical checks and the translations of the paper were developed with the assistance of language models. All proofs are checked by the Lean kernel, and the main theorems were also checked by an independent kernel. The novelty and correctness of the mathematics still require review by specialists.
