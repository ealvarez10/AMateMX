import AMateEnergia.Definiciones
import AMateEnergia.ZetaBanda
import AMateEnergia.EnergiaFourier
import AMateEnergia.InversaZeta
import AMateEnergia.PerronContorno
import AMateEnergia.PolinomioCritica

/-!
# Entradas analíticas

Las cuatro piezas analíticas del estado 45, todas demostradas: `E_eq_integral` (en
`EnergiaFourier`), `zeta_recta_critica` (en `ZetaBanda`), `balazard_saias` (en `InversaZeta` y
`PerronContorno`) y `P_recta_critica` (en `PolinomioCritica`). Solo las dos últimas usan la
hipótesis de Riemann.
-/

open Complex MeasureTheory

namespace AMate

/-- Estado 45, (2.4)–(2.5): identidad de Mellin del testigo y Plancherel de Mellin.
Demostrada en `EnergiaFourier`: `σ_Q(⌊x⌋)` tiene transformada `(1 − ζ(s) P_Q(s))/s` en
`Re s > 0` (sin prolongación analítica) y Plancherel en `Re s = 1/2` da la identidad. -/
theorem E_eq_integral {Q : ℕ} (hQ : 2 ≤ Q) :
    E Q = (1 / (2 * Real.pi)) *
      ∫ x : ℝ, ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
        / (1 / 4 + x ^ 2) :=
  E_eq_integral_de (by omega)

/-- Estado 45, (6.1), con exponente `1/3` en lugar de `1/4`:
`|ζ(1/2 + ix)| ≤ C (1 + |x|)^{1/3}`, sin hipótesis. Cualquier exponente `a < 1/2` sirve para
el teorema principal si `η < 1/2 − a`; con `a = 1/3` vale `η = 1/8`. Demostrada en
`ZetaBanda` por las tres rectas de Hadamard. -/
theorem zeta_recta_critica :
    ∃ C : ℝ, ∀ x : ℝ, ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ≤ C * (1 + |x|) ^ (1 / 3 : ℝ) :=
  zeta_critica_un_tercio

/-- Estado 45, §3: lema de Balazard–Saias con `θ = 1/2`, que la hipótesis de Riemann permite.
Demostrado: `inv_zeta_bound` (`‖1/ζ(s)‖ ≪ |t|^η` bajo RH, en `InversaZeta`) y la fórmula de
Perron suavizada (`balazard_saias_de`, en `PerronContorno`): peso lineal en `[n, n + √n]`,
inversión de Mellin en `Re w = 2` y desplazamiento a `Re (s + w) = 1/2 + δ/2` sobre rectángulos.
Se excluye `s = 1`: Mathlib da a `ζ` un valor convencional en el polo y el lema usa allí
`1/ζ(1) = 0` por continuación. -/
theorem balazard_saias (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 1 → s ≠ 1 →
      ‖∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - 1 / riemannZeta s‖
        ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η :=
  balazard_saias_de hRH hδ hδ' hη

/-- Estado 45, (5.4) con `b = 1/2 + δ`: cota del polinomio en la recta crítica bajo RH.
Demostrada en `PolinomioCritica`: sumación de Abel desde la recta `Re s = b` y las cotas
`m_Q, t_Q = O(Q^{−1/2 + 2δ/3})` de (5.2)–(5.3). -/
theorem P_recta_critica (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → ∀ x : ℝ,
      ‖P Q (1 / 2 + (x : ℂ) * I)‖ ≤ C * (Q : ℝ) ^ δ * (1 + |x|) ^ η :=
  P_recta_critica_de hRH hδ hδ' hη

end AMate
