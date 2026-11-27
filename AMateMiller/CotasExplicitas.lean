import AMateMiller.FormulaLimite
import AMateMiller.DigammaExplicito

/-!
# Cotas explícitas para la suma sobre ceros

* `VM_le`: con RH, `VM(σ) = −ζ'/ζ(σ) ≤ 1/σ + 1/(σ − 1) + ½ log(σ/2) − ½ log π` para
  `1 < σ < 3/2` (la suma sobre los ceros de `ζ` en la cota de Hadamard es `≥ 0`).
* `hadamard_chi_le`: para `χ` primitivo no trivial,
  `∑ m_ρ · 2(σ − ½)/((σ − ½)² + γ²) ≤ log(N/π) + max(log(σ/2), log((σ+1)/2)) + 2 VM(σ)`.
* `hadamard_zeta_le`: para `ζ`, `∑ … ≤ 2(1/σ + 1/(σ − 1) − ½ log π + ½ log(σ/2))`.
* `suma_K_le`: con GRH, `∑ m_ρ |K(ρ)| ≤ √x · ½ (Σ_{1+α}/(1 + 2α) + Σ_{1+β}/(1 + 2β))`.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Hadamard AMate.Miller.Ponderada AMate.Miller.DigammaExp

set_option linter.unusedSectionVars false

/-- La paridad del carácter trivial es `0`. -/
theorem par_one {N : ℕ} [NeZero N] : par (1 : DirichletCharacter ℂ N) = 0 := by
  rcases par_spec (1 : DirichletCharacter ℂ N) with ⟨-, h⟩ | ⟨ho, -⟩
  · exact h
  · exfalso
    unfold DirichletCharacter.Odd at ho
    rw [MulChar.one_apply isUnit_one.neg] at ho
    norm_num at ho

/-- `L(Λ, σ) = VM(σ)` para `σ > 1`. -/
theorem LSeries_vonMangoldt_eq_VM {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) = ((VM σ : ℝ) : ℂ) := by
  unfold VM LSeries
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero (by omega)]
    have e : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ (σ : ℂ) =
        ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
      push_cast; rfl
    rw [e, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))]

/-- `ζ'/ζ(σ) = −VM(σ)` para `σ > 1`. -/
theorem logDeriv_zeta_real {σ : ℝ} (hσ : 1 < σ) :
    logDeriv riemannZeta (σ : ℂ) = -((VM σ : ℝ) : ℂ) := by
  rw [← LSeries_vonMangoldt_eq_VM hσ,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ),
    logDeriv_apply]
  ring

/-- `ZerosBelow χ 0 = ∅`. -/
theorem zerosBelow_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ZerosBelow χ 0 = ∅ := by
  ext ρ
  simp only [ZerosBelow, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro _ _ h
  exact absurd h (not_lt.mpr (abs_nonneg _))

/-- **Cota de `VM` a partir de RH.** -/
theorem VM_le (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {σ : ℝ} (hσ1 : 1 < σ)
    (hσ2 : σ < 3 / 2) :
    VM σ ≤ 1 / σ + 1 / (σ - 1) + Real.log (σ / 2) / 2 - Real.log Real.pi / 2 := by
  set χ : DirichletCharacter ℂ 1 := 1
  have hp : χ.IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have hfin : (ZerosBelow χ 0).Finite := by rw [zerosBelow_zero]; exact finite_empty
  have hH := cota_hadamard h hG hp hσ1 hσ2 hfin
  have hempty : hfin.toFinset = ∅ := by
    rw [Set.Finite.toFinset_eq_empty]; exact zerosBelow_zero χ
  rw [hempty, Finset.sum_empty] at hH
  have hinv : χ⁻¹ = χ := inv_one
  have hdel : del1 χ = 1 := by classical simp [del1, χ]
  rw [hinv, hdel] at hH
  have hΛ : Λd χ σ = ((Real.log (1 / Real.pi) / 2 : ℝ) : ℂ) + Complex.digamma ((σ : ℂ) / 2) / 2 -
      ((VM σ : ℝ) : ℂ) := by
    unfold Λd
    rw [par_one, add_zero, DirichletCharacter.LFunction_modOne_eq, logDeriv_zeta_real hσ1,
      Nat.cast_one]
    ring
  have hsum : Λd χ σ + Λd χ σ + 1 * ((2 : ℂ) / σ + 2 / ((σ : ℂ) - 1)) =
      ((Real.log (1 / Real.pi) - 2 * VM σ + (2 / σ + 2 / (σ - 1)) : ℝ) : ℂ) +
        Complex.digamma ((σ / 2 : ℝ) : ℂ) := by
    rw [hΛ]; push_cast; ring
  rw [hsum, Complex.add_re, Complex.ofReal_re] at hH
  have hψ := digamma_real_le hS (show (0 : ℝ) < σ / 2 by linarith)
  rw [Real.log_div one_ne_zero Real.pi_pos.ne', Real.log_one] at hH
  have : 1 / σ + 1 / (σ - 1) = (2 / σ + 2 / (σ - 1)) / 2 := by ring
  linarith

/-- **Hadamard para `χ` primitivo no trivial.** -/
theorem hadamard_chi_le (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) {T : ℝ} (hfin : (ZerosBelow χ T).Finite) :
    ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) ≤
      Real.log (N / Real.pi) + max (Real.log (σ / 2)) (Real.log ((σ + 1) / 2)) + 2 * VM σ := by
  have hH := cota_hadamard h hG hp hσ1 hσ2 hfin
  have hdel : del1 χ = 0 := by classical simp [del1, hχ]
  rw [hdel, zero_mul, add_zero] at hH
  refine hH.trans ?_
  have hpar := par_re_nonneg χ
  have hpinv : par χ⁻¹ = par χ := par_inv χ
  have hre : ∀ (ψc : DirichletCharacter ℂ N), par ψc = par χ →
      (Λd ψc σ).re ≤ Real.log (N / Real.pi) / 2 +
        max (Real.log (σ / 2)) (Real.log ((σ + 1) / 2)) / 2 + VM σ := by
    intro ψc hψc
    unfold Λd
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re]
    have hL := norm_logDeriv_le_VM ψc (show 1 < ((σ : ℂ)).re by simpa using hσ1)
    simp only [Complex.ofReal_re] at hL
    have hLre := (Complex.re_le_norm _).trans hL
    have hψ : (Complex.digamma (((σ : ℂ) + par ψc) / 2)).re ≤
        max (Real.log (σ / 2)) (Real.log ((σ + 1) / 2)) := by
      rcases par_spec χ with ⟨-, h0⟩ | ⟨-, h1⟩
      · rw [hψc, h0, add_zero]
        have := digamma_real_le hS (show (0 : ℝ) < σ / 2 by linarith)
        push_cast at this
        exact this.trans (le_max_left _ _)
      · rw [hψc, h1]
        have := digamma_real_le hS (show (0 : ℝ) < (σ + 1) / 2 by linarith)
        push_cast at this
        exact this.trans (le_max_right _ _)
    linarith
  have h1 := hre χ rfl
  have h2 := hre χ⁻¹ hpinv
  rw [Complex.add_re]
  linarith

/-- **Hadamard para `ζ`.** -/
theorem hadamard_zeta_le (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) {T : ℝ}
    (hfin : (ZerosBelow (1 : DirichletCharacter ℂ 1) T).Finite) :
    ∑ ρ ∈ hfin.toFinset, (mult (1 : DirichletCharacter ℂ 1) ρ : ℝ) *
        (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) ≤
      2 * (1 / σ + 1 / (σ - 1) - Real.log Real.pi / 2 + Real.log (σ / 2) / 2) := by
  set χ : DirichletCharacter ℂ 1 := 1
  have hp : χ.IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have hH := cota_hadamard h hG hp hσ1 hσ2 hfin
  have hinv : χ⁻¹ = χ := inv_one
  have hdel : del1 χ = 1 := by classical simp [del1, χ]
  rw [hinv, hdel] at hH
  refine hH.trans ?_
  have hΛ : Λd χ σ = ((Real.log (1 / Real.pi) / 2 : ℝ) : ℂ) + Complex.digamma ((σ : ℂ) / 2) / 2 -
      ((VM σ : ℝ) : ℂ) := by
    unfold Λd
    rw [par_one, add_zero, DirichletCharacter.LFunction_modOne_eq, logDeriv_zeta_real hσ1,
      Nat.cast_one]
    ring
  have hsum : Λd χ σ + Λd χ σ + 1 * ((2 : ℂ) / σ + 2 / ((σ : ℂ) - 1)) =
      ((Real.log (1 / Real.pi) - 2 * VM σ + (2 / σ + 2 / (σ - 1)) : ℝ) : ℂ) +
        Complex.digamma ((σ / 2 : ℝ) : ℂ) := by
    rw [hΛ]; push_cast; ring
  rw [hsum, Complex.add_re, Complex.ofReal_re]
  have hψ := digamma_real_le hS (show (0 : ℝ) < σ / 2 by linarith)
  have hVM := VM_nonneg σ
  rw [Real.log_div one_ne_zero Real.pi_pos.ne', Real.log_one]
  have : 1 / σ + 1 / (σ - 1) = (2 / σ + 2 / (σ - 1)) / 2 := by ring
  linarith

/-- `1/(ab) ≤ (1/a² + 1/b²)/2`. -/
theorem inv_mul_le_half {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b) ≤ (1 / a ^ 2 + 1 / b ^ 2) / 2 := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [sq_nonneg (a - b), mul_pos ha hb]

/-- `1/|ρ + γ|² = G_{1+γ}(ρ)/(1 + 2γ)` si `Re ρ = 1/2`. -/
theorem inv_norm_sq_eq {ρ : ℂ} (hre : ρ.re = 1 / 2) {γ : ℝ} (hγ : 0 < γ) :
    1 / ‖ρ + γ‖ ^ 2 = (2 * ((1 + γ) - 1 / 2) / (((1 + γ) - 1 / 2) ^ 2 + ρ.im ^ 2)) / (1 + 2 * γ) := by
  have hn : ‖ρ + γ‖ ^ 2 = (1 / 2 + γ) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero, hre]
    ring
  rw [hn, show (1 + γ) - 1 / 2 = 1 / 2 + γ by ring]
  have h1 : 0 < (1 / 2 + γ) ^ 2 + ρ.im ^ 2 := by nlinarith [sq_nonneg ρ.im]
  have h2 : (0 : ℝ) < 1 + 2 * γ := by linarith
  field_simp

/-- **Suma de `|K(ρ)|` sobre los ceros.** -/
theorem suma_K_le (hG : GRHPrimitivo) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {x α β : ℝ} (hx : 0 < x) (hα : 0 < α) (hβ : 0 < β) {T : ℝ}
    (hfin : (ZerosBelow χ T).Finite) :
    ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) * ‖K x α β ρ‖ ≤
      Real.sqrt x / 2 * ((∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) *
          (2 * ((1 + α) - 1 / 2) / (((1 + α) - 1 / 2) ^ 2 + ρ.im ^ 2))) / (1 + 2 * α) +
        (∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) *
          (2 * ((1 + β) - 1 / 2) / (((1 + β) - 1 / 2) ^ 2 + ρ.im ^ 2))) / (1 + 2 * β)) := by
  have hterm : ∀ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) * ‖K x α β ρ‖ ≤
      Real.sqrt x / 2 * ((mult χ ρ : ℝ) *
          (2 * ((1 + α) - 1 / 2) / (((1 + α) - 1 / 2) ^ 2 + ρ.im ^ 2)) / (1 + 2 * α) +
        (mult χ ρ : ℝ) * (2 * ((1 + β) - 1 / 2) / (((1 + β) - 1 / 2) ^ 2 + ρ.im ^ 2)) /
          (1 + 2 * β)) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hre := re_eq_half_de_mem hG hp hρ
    have hm := (Nat.cast_nonneg (mult χ ρ) : (0 : ℝ) ≤ mult χ ρ)
    have hpa : 0 < ‖ρ + α‖ := by
      rw [norm_pos_iff]; intro e; have := congrArg Complex.re e; simp [hre] at this; linarith
    have hpb : 0 < ‖ρ + β‖ := by
      rw [norm_pos_iff]; intro e; have := congrArg Complex.re e; simp [hre] at this; linarith
    have hK : ‖K x α β ρ‖ = Real.sqrt x * (1 / (‖ρ + α‖ * ‖ρ + β‖)) := by
      unfold K
      rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.sqrt_eq_rpow]
      ring
    have hab := inv_mul_le_half hpa hpb
    rw [inv_norm_sq_eq hre hα, inv_norm_sq_eq hre hβ] at hab
    rw [hK]
    have hsx := Real.sqrt_nonneg x
    calc (mult χ ρ : ℝ) * (Real.sqrt x * (1 / (‖ρ + α‖ * ‖ρ + β‖)))
        ≤ (mult χ ρ : ℝ) * (Real.sqrt x * (((2 * ((1 + α) - 1 / 2) /
            (((1 + α) - 1 / 2) ^ 2 + ρ.im ^ 2)) / (1 + 2 * α) + (2 * ((1 + β) - 1 / 2) /
            (((1 + β) - 1 / 2) ^ 2 + ρ.im ^ 2)) / (1 + 2 * β)) / 2)) := by
          gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]

end AMate.Miller.Explicito
