import Mathlib

/-!
# Fórmula explícita y ceros en ventanas (enunciados)

Copias literales de las definiciones, solo con Mathlib, que usa la biblioteca de Lean anunciada por
Alpöge (2026) en `Formalism/PeriodIntegrals/ExplicitFormula.lean` y
`Formalism/PeriodIntegrals/ZerosWindow.lean`. Aquí son solo enunciados: `CotaBach` los usa como
hipótesis, y una composición puede instanciarlos con `PI.explicitFormula_closed` y
`PI.zerosWindow_closed`, porque los cuerpos coinciden y las definiciones se despliegan igual.

* `psi0 χ u = ∑_{n ≤ u} Λ(n) χ(n) − [χ = 1] u`.
* `ZerosBelow χ T`: ceros de `L(s,χ)` con `0 < Re ρ < 1` y `|Im ρ| < T`.
* `ExplicitFormulaWith C`: fórmula explícita truncada para caracteres primitivos.
* `ZerosNear χ t`, `ZerosWindowWith C`: a lo sumo `C log(N(|t| + 2))` ceros, con multiplicidad, en
  `|Im ρ − t| ≤ 1`.
-/

noncomputable section

namespace AMate.Miller.PI

open Classical in

def psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
    (if χ = 1 then (u : ℂ) else 0)

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ExplicitFormulaWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)

def ExplicitFormula : Prop := ∃ C : ℝ, 0 < C ∧ ExplicitFormulaWith C

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosWindowWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def ZerosWindow : Prop := ∃ C : ℝ, 0 < C ∧ ZerosWindowWith C

end AMate.Miller.PI
