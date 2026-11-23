import AMateEnergia.ZetaCotas

/-!
# Cota de `ζ` en la recta `Re s = 0`

* `norm_sq_Gamma_one_sub`: `|Γ(1 − it)|² = π t / sinh(π t)`, por la fórmula de reflexión y la
  simetría `Γ(conj s) = conj Γ(s)`.
* `norm_sq_riemannZeta_mul_I_le`: por la ecuación funcional,
  `|ζ(it)|² ≤ |t|/(2π) · |ζ(1 − it)|²`.
* `norm_riemannZeta₁_mul_I_le`: `‖(s − 1) ζ(s)‖ ≤ C (1 + |t|)^{3/2} (2 + log(2 + |t|))` en
  `Re s = 0`.

Es la tercera pieza de la cota en la recta crítica por las tres rectas de Hadamard.
-/

open Complex

namespace AMate

theorem riemannZeta₁_eq (s : ℂ) (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- `|Γ(1 − it)|² = π t / sinh(π t)` para `t ≠ 0`. -/
theorem norm_sq_Gamma_one_sub (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 - t * I)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  have htI : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hsh : Real.sinh (Real.pi * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero ht
  have hconj : Gamma (1 + t * I) = (starRingEnd ℂ) (Gamma (1 - t * I)) := by
    rw [← Gamma_conj]
    congr 1
    simp [map_sub, conj_ofReal]
  have hadd : Gamma (1 + t * I) = (t * I) * Gamma (t * I) := by
    rw [add_comm, Gamma_add_one _ htI]
  have hrefl := Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hsin : Complex.sin (Real.pi * (t * I)) = Real.sinh (Real.pi * t) * I := by
    rw [show (Real.pi : ℂ) * (t * I) = ((Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
      sin_mul_I, ofReal_sinh]
  have key : ((Complex.normSq (Gamma (1 - t * I)) : ℝ) : ℂ)
      = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← mul_conj, ← hconj, hadd,
      show Gamma (1 - t * I) * (t * I * Gamma (t * I))
        = t * I * (Gamma (t * I) * Gamma (1 - t * I)) by ring,
      hrefl, hsin]
    have hshC : ((Real.sinh (Real.pi * t) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsh
    have hI : I ≠ 0 := I_ne_zero
    push_cast at hshC ⊢
    field_simp
  rw [Complex.sq_norm]
  exact_mod_cast key

/-- `|cos(π(1 − it)/2)| = |sinh(πt/2)|`. -/
theorem norm_cos_pi_one_sub_div_two (t : ℝ) :
    ‖Complex.cos (Real.pi * (1 - t * I) / 2)‖ = |Real.sinh (Real.pi * t / 2)| := by
  have h : (Real.pi : ℂ) * (1 - t * I) / 2 = (Real.pi : ℂ) / 2 - ((Real.pi * t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, cos_pi_div_two_sub, sin_mul_I, norm_mul, norm_I, mul_one, ← ofReal_sinh,
    Complex.norm_real, Real.norm_eq_abs]

theorem sinh_identity (t : ℝ) (ht : t ≠ 0) :
    Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2
      = Real.pi * t * Real.sinh (Real.pi * t / 2) / (2 * Real.cosh (Real.pi * t / 2)) := by
  have h2 : Real.sinh (Real.pi * t)
      = 2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    rw [← Real.sinh_two_mul]
    congr 1
    ring
  have hs : Real.sinh (Real.pi * t / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ht) two_ne_zero
  have hc : Real.cosh (Real.pi * t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [h2]
  field_simp

/-- Ecuación funcional en `Re s = 0`: `|ζ(it)|² ≤ |t|/(2π) · |ζ(1 − it)|²`. -/
theorem norm_sq_riemannZeta_mul_I_le (t : ℝ) (ht : t ≠ 0) :
    ‖riemannZeta (t * I)‖ ^ 2 ≤ |t| / (2 * Real.pi) * ‖riemannZeta (1 - t * I)‖ ^ 2 := by
  have hsn : ∀ n : ℕ, (1 : ℂ) - t * I ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs1 : (1 : ℂ) - t * I ≠ 1 := by
    intro h
    apply ht
    have := congrArg Complex.im h
    simpa using this
  have hfe := riemannZeta_one_sub hsn hs1
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  have h2pi : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - t * I))‖ = (2 * Real.pi)⁻¹ := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Real.rpow_neg_one]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, mul_pow, h2pi,
    norm_sq_Gamma_one_sub t ht, norm_cos_pi_one_sub_div_two t, sq_abs]
  have hpi := Real.pi_pos
  have hc := Real.cosh_pos (Real.pi * t / 2)
  have hsc : t * Real.sinh (Real.pi * t / 2) ≤ |t| * Real.cosh (Real.pi * t / 2) := by
    have h1 : |Real.sinh (Real.pi * t / 2)| ≤ Real.cosh (Real.pi * t / 2) := by
      have := Real.cosh_sq (Real.pi * t / 2)
      nlinarith [abs_nonneg (Real.sinh (Real.pi * t / 2)), sq_abs (Real.sinh (Real.pi * t / 2))]
    calc t * Real.sinh (Real.pi * t / 2) ≤ |t * Real.sinh (Real.pi * t / 2)| := le_abs_self _
      _ = |t| * |Real.sinh (Real.pi * t / 2)| := abs_mul _ _
      _ ≤ |t| * Real.cosh (Real.pi * t / 2) := by gcongr
  have hfac : ‖(2 : ℂ)‖ ^ 2 * ((2 * Real.pi)⁻¹) ^ 2
      * (Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2)
      ≤ |t| / (2 * Real.pi) := by
    rw [sinh_identity t ht, Complex.norm_two]
    rw [show (2 : ℝ) ^ 2 * ((2 * Real.pi)⁻¹) ^ 2
        * (Real.pi * t * Real.sinh (Real.pi * t / 2) / (2 * Real.cosh (Real.pi * t / 2)))
        = t * Real.sinh (Real.pi * t / 2) / (2 * Real.pi * Real.cosh (Real.pi * t / 2)) by
      field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hz := sq_nonneg ‖riemannZeta (1 - t * I)‖
  calc ‖(2 : ℂ)‖ ^ 2 * ((2 * Real.pi)⁻¹) ^ 2 * (Real.pi * t / Real.sinh (Real.pi * t))
        * Real.sinh (Real.pi * t / 2) ^ 2 * ‖riemannZeta (1 - t * I)‖ ^ 2
      = (‖(2 : ℂ)‖ ^ 2 * ((2 * Real.pi)⁻¹) ^ 2
        * (Real.pi * t / Real.sinh (Real.pi * t) * Real.sinh (Real.pi * t / 2) ^ 2))
        * ‖riemannZeta (1 - t * I)‖ ^ 2 := by ring
    _ ≤ |t| / (2 * Real.pi) * ‖riemannZeta (1 - t * I)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfac hz

/-- Cota en la recta `Re s = 0`: `‖(s − 1) ζ(s)‖ ≤ C (1 + |t|)^{3/2} (2 + log(2 + |t|))`. -/
theorem norm_riemannZeta₁_mul_I_le :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖riemannZeta₁ (t * I)‖ ≤ C * (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t : ℝ => riemannZeta₁ (t * I))
    ((differentiable_riemannZeta₁.continuous.comp
      (continuous_ofReal.mul continuous_const)).continuousOn)
  refine ⟨max B 1, fun t => ?_⟩
  have hL : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have h1t : (1 : ℝ) ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  have hM : (1 : ℝ) ≤ max B 1 := le_max_right _ _
  have hX : (1 : ℝ) ≤ (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by nlinarith
  by_cases ht : |t| ≤ 1
  · have hb := hB t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    calc ‖riemannZeta₁ (t * I)‖ ≤ B := hb
      _ ≤ max B 1 := le_max_left _ _
      _ = max B 1 * 1 := (mul_one _).symm
      _ ≤ max B 1 * ((1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|))) :=
          mul_le_mul_of_nonneg_left hX (by linarith)
      _ = max B 1 * (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by ring
  · push Not at ht
    have ht0 : t ≠ 0 := by
      intro h
      rw [h, abs_zero] at ht
      linarith
    have htpos : (0 : ℝ) < |t| := abs_pos.mpr ht0
    have hne : (t : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have hne2 : (1 : ℂ) - t * I ≠ 1 := by
      intro h
      apply ht0
      have := congrArg Complex.im h
      simpa using this
    have hR := norm_riemannZeta₁_one_add_le (-t)
    rw [abs_neg, show (1 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - t * I by push_cast; ring,
      riemannZeta₁_eq _ hne2, norm_mul, show (1 : ℂ) - t * I - 1 = -(t * I) by ring, norm_neg,
      norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hR
    have hζ1 : ‖riemannZeta (1 - t * I)‖ ≤ 2 * (2 + Real.log (2 + |t|)) := by
      have h2 : (1 + |t|) * (2 + Real.log (2 + |t|)) ≤ |t| * (2 * (2 + Real.log (2 + |t|))) := by
        nlinarith
      exact le_of_mul_le_mul_left (le_trans hR h2) htpos
    have hsq := norm_sq_riemannZeta_mul_I_le t ht0
    have h4 : ‖riemannZeta (t * I)‖ ^ 2
        ≤ (Real.sqrt (1 + |t|) * (2 + Real.log (2 + |t|))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have hfac : |t| / (2 * Real.pi) * 4 ≤ 1 + |t| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg t]
      calc ‖riemannZeta (t * I)‖ ^ 2 ≤ |t| / (2 * Real.pi) * ‖riemannZeta (1 - t * I)‖ ^ 2 := hsq
        _ ≤ |t| / (2 * Real.pi) * (2 * (2 + Real.log (2 + |t|))) ^ 2 := by gcongr
        _ = (|t| / (2 * Real.pi) * 4) * (2 + Real.log (2 + |t|)) ^ 2 := by ring
        _ ≤ (1 + |t|) * (2 + Real.log (2 + |t|)) ^ 2 := by gcongr
    have hζ0 : ‖riemannZeta (t * I)‖ ≤ Real.sqrt (1 + |t|) * (2 + Real.log (2 + |t|)) := by
      have h5 := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h5
    have hnorm : ‖(t : ℂ) * I - 1‖ ≤ 1 + |t| := by
      calc ‖(t : ℂ) * I - 1‖ ≤ ‖(t : ℂ) * I‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + |t| := by
            rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_one]
            ring
    have hrpow : (1 + |t|) ^ (3 / 2 : ℝ) = (1 + |t|) * Real.sqrt (1 + |t|) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    have hp : 0 ≤ (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by positivity
    calc ‖riemannZeta₁ (t * I)‖ = ‖(t : ℂ) * I - 1‖ * ‖riemannZeta (t * I)‖ := by
          rw [riemannZeta₁_eq _ hne, norm_mul]
      _ ≤ (1 + |t|) * (Real.sqrt (1 + |t|) * (2 + Real.log (2 + |t|))) := by gcongr
      _ = (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by rw [hrpow]; ring
      _ ≤ max B 1 * (1 + |t|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by nlinarith

end AMate
