import AMateMiller.FormulaExplicita

/-!
# Enunciados analíticos de la biblioteca de Alpöge (copias literales)

Para la cota de Bach con constante explícita hacen falta, además de GRH, varios hechos sobre
`L(s, χ)` que la biblioteca de Lean anunciada por Alpöge (2026) demuestra con constantes no
explícitas. Aquí solo se copian sus enunciados, con los mismos cuerpos, para usarlos como hipótesis
(como `FormulaExplicita.lean`); una composición los instancia con los teoremas de Alpöge porque
las definiciones coinciden.

Las constantes no explícitas solo se usan para que ciertos bordes de los rectángulos tiendan a
`0`; los términos que quedan en la cota final son explícitos.

De `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeightExists.lean`:

* `rect`, `rectInt`: el rectángulo `[x₀, x₁] × [y₀, y₁]` y la integral sobre su borde.
* `RectCauchy`: fórmula de Cauchy en rectángulos (`PI.EF.rectCauchy`).
* `ZeroLocus`, `ZerosFinite`: dónde están los ceros con `Re s ≥ −3/2` (`PI.EF.zeroLocus`,
  `PI.EF.zerosFinite`).
* `IsRegPart`, `RegularPart`: `L'/L = H + ∑ m_ρ/(s − ρ) + ε₀/s − δ₁/(s − 1)` con `H` holomorfa
  en el rectángulo (`PI.EF.regularPart`).
* `GoodHeight`, `GoodHeightExists`, `LogDerivHoriz`: alturas buenas y `|L'/L| ≪ log²` en ellas.

De `Development/AutomorphicSpectrum/Proofs/GlobalProofs`:

* `DigammaDerecha`, `DigammaIzquierda`: `|ψ(z)| ≤ C log(|z| + 2)` en las regiones indicadas.
* `ReflexionLogDeriv`: la ecuación funcional de `L'/L` para caracteres primitivos de módulo `> 1`.
* `SerieDigamma`: `ψ(z) = lim (log n − ∑_{k ≤ n} 1/(z + k))` para `Re z > 0`.
-/

noncomputable section

namespace AMate.Miller.PI.EF

open Complex

section defs

variable {N : ℕ} [NeZero N]

abbrev mult (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

open Classical in

def eps0 (χ : DirichletCharacter ℂ N) : ℂ := if χ.Even ∧ χ ≠ 1 then 1 else 0

open Classical in

def del1 (χ : DirichletCharacter ℂ N) : ℂ := if χ = 1 then 1 else 0

def NoOrdinate (χ : DirichletCharacter ℂ N) (T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≠ T'

def GoodHeight (χ : DirichletCharacter ℂ N) (κ T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
    1 / (κ * Real.log (N * T')) ≤ |(|ρ.im|) - T'|

end defs

def rectInt (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f (x + y₀ * I)) - (∫ x : ℝ in x₀..x₁, f (x + y₁ * I)) +
    I • (∫ y : ℝ in y₀..y₁, f (x₁ + y * I)) - I • ∫ y : ℝ in y₀..y₁, f (x₀ + y * I)

def rect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := Set.Icc x₀ x₁ ×ℂ Set.Icc y₀ y₁

def GoodHeightExists (κ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ GoodHeight χ κ T'

def ZerosFinite : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, (ZerosBelow χ T).Finite

def RectCauchy : Prop :=
  ∀ (x₀ x₁ y₀ y₁ : ℝ) (h : ℂ → ℂ) (w : ℂ), x₀ < w.re → w.re < x₁ → y₀ < w.im → w.im < y₁ →
    DifferentiableOn ℂ h (rect x₀ x₁ y₀ y₁) →
    rectInt (fun s => h s / (s - w)) x₀ x₁ y₀ y₁ = 2 * Real.pi * I * h w

def ZeroLocus : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -3 / 2 ≤ s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s = 0 →
      (0 < s.re ∧ s.re < 1) ∨ (s = 0 ∧ χ.Even ∧ χ ≠ 1) ∨ (s = -1 ∧ χ.Odd)

def IsRegPart {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x₁ T' : ℝ) (H : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ H (rect (-1 / 2) x₁ (-T') T') ∧
  ∀ s ∈ rect (-1 / 2) x₁ (-T') T', DirichletCharacter.LFunction χ s ≠ 0 → s ≠ 1 →
    logDeriv (DirichletCharacter.LFunction χ) s =
      H s + (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / (s - ρ)) + eps0 χ / s - del1 χ / (s - 1)

def RegularPart : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ x₁ T' : ℝ, 1 < x₁ → 0 < T' →
    NoOrdinate χ T' → ∃ H : ℂ → ℂ, IsRegPart χ x₁ T' H

def LogDerivHoriz (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T' : ℝ, 2 ≤ T' →
    GoodHeight χ κ T' → ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T' * I)‖ ≤ C * Real.log (N * T') ^ 2 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (-T' : ℝ) * I)‖ ≤ C * Real.log (N * T') ^ 2

end AMate.Miller.PI.EF

namespace AMate.Miller.PI.Digamma

/-- `GlobalTheory.T.digamma_log_bound_right_half_plane`. -/
def DigammaDerecha : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2)

/-- `GlobalTheory.T.digamma_log_bound_left_region`. -/
def DigammaIzquierda : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
    ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2)

/-- `GlobalTheory.T.dirichlet_logDeriv_reflection_formula`. -/
def ReflexionLogDeriv : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive → ∀ a : ℂ,
    (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ, (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) →
    (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) → DirichletCharacter.LFunction χ s ≠ 0 →
    DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 →
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 -
        Complex.digamma ((s + a) / 2) / 2 -
        deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) / DirichletCharacter.LFunction χ⁻¹ (1 - s)

/-- `GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma`. -/
def SerieDigamma : Prop :=
  ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z))

end AMate.Miller.PI.Digamma
