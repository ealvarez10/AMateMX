import AMateEnergia.PerronPeso
import AMateEnergia.InversaZeta
import AMateEnergia.ZetaRectaCero

/-!
# `1/ζ` holomorfa y el lado de Dirichlet de Perron

* `Zinv z = (z − 1)/ζ₁(z)`: vale `1/ζ(z)` si `z ≠ 1` (`Zinv_eq`) y, bajo RH, es holomorfa en
  `Re z > 1/2` (`differentiableOn_Zinv`), con `‖Zinv z‖ ≤ C (1 + |Im z|)^η` en `Re z ≥ 1/2 + δ`
  (`Zinv_bound`, a partir de `inv_zeta_bound`).
* `dirichlet_side`: en la recta `Re w = 2`,
  `(1/2π) ∫ Zinv(s + w) pesoMellin(w) dy = ∑_{d ≤ N+h} μ(d) d^{−s} peso(d)`, intercambiando la serie
  de `1/ζ` con la integral e invirtiendo Mellin término a término.
-/

open Complex MeasureTheory Set Filter Metric

namespace AMate

/-! ### `Z = 1/ζ` como función holomorfa -/

/-- `Z(z) = (z − 1)/ζ₁(z)`: vale `1/ζ(z)` fuera de `z = 1` y es holomorfa donde `ζ₁ ≠ 0`. -/
noncomputable def Zinv (z : ℂ) : ℂ := (z - 1) / riemannZeta₁ z

theorem Zinv_eq {z : ℂ} (hz : z ≠ 1) : Zinv z = (riemannZeta z)⁻¹ := by
  unfold Zinv
  rw [riemannZeta₁_eq z hz, ← div_div, div_self (sub_ne_zero.mpr hz), one_div]

theorem riemannZeta₁_ne_zero_of_RH (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) :
    riemannZeta₁ z ≠ 0 := by
  by_cases h1 : z = 1
  · rw [h1, riemannZeta₁_one]
    exact one_ne_zero
  rw [riemannZeta₁_eq z h1]
  refine mul_ne_zero (sub_ne_zero.mpr h1) ?_
  intro h0
  have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have h2 := congrArg Complex.re hn
    simp at h2
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have := hRH z h0 htriv h1
  linarith

theorem differentiableOn_Zinv (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ Zinv {z | 1 / 2 < z.re} := by
  intro z hz
  exact ((differentiableAt_id.sub_const 1).div differentiable_riemannZeta₁.differentiableAt
    (riemannZeta₁_ne_zero_of_RH hRH hz)).differentiableWithinAt

theorem Zinv_eq_LSeries {z : ℂ} (hz : 1 < z.re) :
    Zinv z = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  rw [Zinv_eq hz1, ← LSeries_one_eq_riemannZeta hz]
  exact inv_eq_of_mul_eq_one_right (LSeries_one_mul_Lseries_moebius hz)

/-- Bajo RH, `‖Z(z)‖ ≤ C (1 + |Im z|)^η` en `Re z ≥ 1/2 + δ`. -/
theorem Zinv_bound (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 + δ ≤ z.re → ‖Zinv z‖ ≤ C * (1 + |z.im|) ^ η := by
  obtain ⟨C₁, hC₁⟩ := inv_zeta_bound hRH hδ hδ' hη
  obtain ⟨S, hS⟩ := zeta_bounds_of_one_lt (show (1 : ℝ) < 3 / 2 by norm_num)
  set Kset : Set ℂ := {z | 1 / 2 + δ ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ 3} with hKset
  have hKc : IsCompact Kset := by
    apply (isCompact_closedBall (0 : ℂ) 5).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_re).inter
        ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp continuous_im) continuous_const))
    · intro z hz
      rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im z
      have h1 : |z.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
      linarith [hz.2.2]
  have hcont : ContinuousOn Zinv Kset :=
    (differentiableOn_Zinv hRH).continuousOn.mono (fun z hz => by
      show 1 / 2 < z.re
      linarith [hz.1])
  obtain ⟨K₀, hK₀⟩ := hKc.bddAbove_image hcont.norm
  refine ⟨max C₁ 0 + max S 0 + max K₀ 0, by positivity, fun z hz => ?_⟩
  have hpow : 1 ≤ (1 + |z.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg z.im]) hη.le
  have hm1 := le_max_right C₁ 0
  have hm2 := le_max_right S 0
  have hm3 := le_max_right K₀ 0
  rcases le_or_gt 3 |z.im| with him | him
  · have hz1 : z ≠ 1 := by
      intro h
      rw [h] at him
      simp at him
      linarith
    rw [Zinv_eq hz1]
    calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * |z.im| ^ η := hC₁ z hz him
      _ ≤ max C₁ 0 * (1 + |z.im|) ^ η :=
          mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hη.le)
            (by positivity) hm1
      _ ≤ (max C₁ 0 + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr; linarith
  · rcases le_or_gt (3 / 2) z.re with hre | hre
    · have hz1 : z ≠ 1 := by
        intro h
        rw [h] at hre
        norm_num at hre
      rw [Zinv_eq hz1]
      calc ‖(riemannZeta z)⁻¹‖ ≤ max S 0 := le_trans (hS z hre).2 (le_max_left _ _)
        _ ≤ (max C₁ 0 + max S 0 + max K₀ 0) * 1 := by linarith
        _ ≤ (max C₁ 0 + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr
    · have hzK : z ∈ Kset := ⟨hz, hre.le, him.le⟩
      calc ‖Zinv z‖ ≤ max K₀ 0 := le_trans (hK₀ ⟨z, hzK, rfl⟩) (le_max_left _ _)
        _ ≤ (max C₁ 0 + max S 0 + max K₀ 0) * 1 := by linarith
        _ ≤ (max C₁ 0 + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr

/-! ### Lado de Dirichlet -/

theorem term_moebius_add {s w : ℂ} (d : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + w) d
      = (if d = 0 then 0 else (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) ^ s)
        * (d : ℂ) ^ (-w) := by
  rcases eq_or_ne d 0 with hd | hd
  · simp [hd]
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [LSeries.term_of_ne_zero hd, if_neg hd, cpow_add _ _ hd', cpow_neg]
  have h1 : (d : ℂ) ^ s ≠ 0 := by
    rw [cpow_def_of_ne_zero hd']
    exact Complex.exp_ne_zero _
  have h2 : (d : ℂ) ^ w ≠ 0 := by
    rw [cpow_def_of_ne_zero hd']
    exact Complex.exp_ne_zero _
  field_simp

/-- **Lado de Dirichlet**: en `Re w = 2`,
`(1/2π) ∫ Z(s+w) pesoMellin(w) dy = ∑_{d ≤ N+h} μ(d) d^{−s} φ(d)`. -/
theorem dirichlet_side {N h : ℝ} (hN : 0 < N) (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ)
        * ∫ y : ℝ, Zinv (s + (((2 : ℝ) : ℂ) + y * I)) * pesoMellin N h (((2 : ℝ) : ℂ) + y * I)
      = ∑ d ∈ Finset.Icc 1 ⌊N + h⌋₊,
          (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso N h d : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun y => pesoMellin N h (((2 : ℝ) : ℂ) + y * I) with hFdef
  have hF : Integrable F := integrable_pesoMellin_line hN hh (by norm_num) (by norm_num)
  set c : ℕ → ℂ := fun d =>
    if d = 0 then 0 else (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) ^ s with hc
  set f : ℕ → ℝ → ℂ := fun d y => c d * ((d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) with hf
  have hw0 : ∀ y : ℝ, -(((2 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y h0
    have := congrArg Complex.re h0
    simp at this
  have hc1 : ∀ d, ‖c d‖ ≤ 1 := by
    intro d
    rcases eq_or_ne d 0 with hd | hd
    · simp [hc, hd]
    simp only [hc, if_neg hd]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hd), Complex.norm_intCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    rw [div_le_one (Real.rpow_pos_of_pos (by linarith) _)]
    have : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    linarith [Real.one_le_rpow hd1 hs.le]
  have hpow : ∀ (d : ℕ) (y : ℝ), ‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ ≤ (d : ℝ) ^ (-(2 : ℝ)) := by
    intro d y
    rcases eq_or_ne d 0 with hd | hd
    · subst hd
      rw [Nat.cast_zero, zero_cpow (hw0 y), norm_zero, Nat.cast_zero,
        Real.zero_rpow (by norm_num)]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hd)]
    simp
  have hfint : ∀ d, Integrable (f d) := by
    intro d
    have hmeas : AEStronglyMeasurable (fun y : ℝ => (d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) :=
      ((Continuous.const_cpow (by fun_prop) (Or.inr (hw0 ·))).aestronglyMeasurable).mul
        hF.aestronglyMeasurable
    have hint : Integrable (fun y : ℝ => (d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) := by
      refine Integrable.mono' (hF.norm.const_mul ((d : ℝ) ^ (-(2 : ℝ)))) hmeas
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hpow d y) (norm_nonneg _)
    exact hint.const_mul (c d)
  have hsum : Summable (fun d => ∫ y, ‖f d y‖) := by
    have hg : Summable (fun d : ℕ => (d : ℝ) ^ (-(2 : ℝ)) * ∫ y, ‖F y‖) :=
      (Real.summable_nat_rpow.mpr (by norm_num)).mul_right _
    refine Summable.of_nonneg_of_le (fun d => integral_nonneg fun y => norm_nonneg _)
      (fun d => ?_) hg
    rw [← integral_const_mul]
    refine integral_mono (hfint d).norm (hF.norm.const_mul _) (fun y => ?_)
    simp only [hf, norm_mul]
    have h1 := hc1 d
    have h2 := hpow d y
    have h3 := norm_nonneg (F y)
    have h4 : 0 ≤ ‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ := norm_nonneg _
    calc ‖c d‖ * (‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ * ‖F y‖)
        ≤ 1 * ((d : ℝ) ^ (-(2 : ℝ)) * ‖F y‖) := by gcongr
      _ = (d : ℝ) ^ (-(2 : ℝ)) * ‖F y‖ := one_mul _
  have hpt : ∀ y : ℝ, Zinv (s + (((2 : ℝ) : ℂ) + y * I)) * F y = ∑' d, f d y := by
    intro y
    have hre : 1 < (s + (((2 : ℝ) : ℂ) + y * I)).re := by simp; linarith
    rw [Zinv_eq_LSeries hre, LSeries, ← tsum_mul_right]
    refine tsum_congr fun d => ?_
    rw [term_moebius_add]
    simp only [hf, hc]
    ring
  have hval : ∀ d, ∫ y, f d y = c d * (2 * Real.pi * ((peso N h d : ℝ) : ℂ)) := by
    intro d
    rcases eq_or_ne d 0 with hd | hd
    · simp [hf, hc, hd]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hmi := mellinInv_pesoMellin hN hh (σ := 2) two_pos hd0
    unfold mellinInv at hmi
    simp only [hf, integral_const_mul]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have e : (2 * (Real.pi : ℂ)) * (((1 / (2 * Real.pi)) : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    rw [← hmi, Complex.real_smul, ← mul_assoc, e, one_mul]
    simp only [ofReal_natCast, smul_eq_mul, hFdef]
  have hI : ∫ y : ℝ, Zinv (s + (((2 : ℝ) : ℂ) + y * I)) * F y = ∑' d, ∫ y, f d y := by
    rw [integral_tsum_of_summable_integral_norm hfint hsum]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hI, tsum_congr hval, tsum_eq_sum (s := Finset.Icc 1 ⌊N + h⌋₊)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    simp only [hc, if_neg hd1]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    rw [cpow_neg]
    push_cast
    field_simp
  · intro d hd
    rcases eq_or_ne d 0 with hd0 | hd0
    · simp [hc, hd0]
    have hgt : N + h < d := by
      have : ¬ (d ≤ ⌊N + h⌋₊) := fun h' => hd (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, h'⟩)
      have h2 : ⌊N + h⌋₊ < d := not_le.mp this
      exact (Nat.floor_lt (by linarith)).mp h2
    simp [peso_of_ge hh hgt.le]

end AMate
