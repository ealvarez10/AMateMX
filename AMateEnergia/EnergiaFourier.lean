import AMateEnergia.Plancherel
import AMateEnergia.MellinTestigo

/-!
# La energía como integral en la recta crítica

Estado 45, (2.4)–(2.5). En variable logarítmica, `G_Q(u) = e^{u/2} σ_Q(⌊e^{−u}⌋)` para `u < 0`:

* `integral_norm_sq_G_eq`, `integral_sigma_sq_eq_E`: `∫ |G_Q|² = ∫_1^∞ σ_Q(⌊x⌋)² x^{−2} dx = E_Q`,
  sumando por tramos `[k, k+1)`;
* `fourier_G`: `𝓕 G_Q(−y/2π) = (1 − ζ(s) P_Q(s))/s` con `s = 1/2 + iy`, por `mellin_eq_fourier` e
  `integral_sigma_floor`;
* `E_eq_integral_de`: Plancherel (`plancherel`) y el cambio `ξ = −y/2π`.
-/

open MeasureTheory Set Complex FourierTransform

namespace AMate

/-- `σ_Q(⌊x⌋)` en `(1, ∞)`, cero fuera. -/
noncomputable def sigmaTail (Q : ℕ) (x : ℝ) : ℂ :=
  indicator (Ioi 1) (fun x : ℝ => ((sigma Q ⌊x⌋₊ : ℝ) : ℂ)) x

/-- `σ_Q(⌊x⌋)²` en `(1, ∞)`, cero fuera. -/
noncomputable def tail2 (Q : ℕ) (x : ℝ) : ℝ :=
  indicator (Ioi 1) (fun x : ℝ => sigma Q ⌊x⌋₊ ^ 2) x

/-- El testigo en variable logarítmica: `G_Q(u) = e^{u/2} σ_Q(⌊e^{−u}⌋)` si `u < 0`, y cero si no. -/
noncomputable def G (Q : ℕ) (u : ℝ) : ℂ := Real.exp (u / 2) • sigmaTail Q (Real.exp (-u))

theorem measurable_sigmaTail (Q : ℕ) : Measurable (sigmaTail Q) := by
  unfold sigmaTail
  exact (Complex.measurable_ofReal.comp
    ((measurable_from_nat (f := sigma Q)).comp Nat.measurable_floor)).indicator
    (measurableSet_Ioi (a := (1 : ℝ)))

theorem measurable_G (Q : ℕ) : Measurable (G Q) :=
  (Real.measurable_exp.comp (measurable_id.div_const 2)).smul
    ((measurable_sigmaTail Q).comp (Real.measurable_exp.comp measurable_neg))

/-! ### Lado de Fourier: la transformada de Mellin -/

theorem mellin_sigmaTail (Q : ℕ) (s : ℂ) :
    mellin (sigmaTail Q) (-s)
      = ∫ x in Ioi (1 : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  unfold mellin sigmaTail
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1)
      • indicator (Ioi (1 : ℝ)) (fun x : ℝ => ((sigma Q ⌊x⌋₊ : ℝ) : ℂ)) t)
      = indicator (Ioi (1 : ℝ)) (fun t : ℝ => ((sigma Q ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [indicator_of_mem ht, mul_comm]
    · simp [indicator_of_notMem ht]
  rw [hfun, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `𝓕 G_Q (−y/2π) = σ̂_Q(1/2 + iy) = (1 − ζ(s) P_Q(s))/s` con `s = 1/2 + iy`. -/
theorem fourier_G {Q : ℕ} (hQ : 1 ≤ Q) (y : ℝ) :
    𝓕 (G Q) (-y / (2 * Real.pi))
      = (1 - riemannZeta (1 / 2 + y * I) * P Q (1 / 2 + y * I)) / (1 / 2 + y * I) := by
  have hre : (1 / 2 + (y : ℂ) * I).re = 1 / 2 := by simp
  have him : (1 / 2 + (y : ℂ) * I).im = y := by simp
  have hs0 : 0 < (1 / 2 + (y : ℂ) * I).re := by rw [hre]; norm_num
  have hs1 : (1 / 2 + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    norm_num at this
  rw [← integral_sigma_floor hQ hs0 hs1, ← mellin_sigmaTail, mellin_eq_fourier]
  have hfun : (fun u : ℝ => Real.exp (-(-(1 / 2 + (y : ℂ) * I)).re * u)
      • sigmaTail Q (Real.exp (-u))) = G Q := by
    funext u
    unfold G
    rw [neg_re, hre]
    congr 2
    ring
  rw [hfun, neg_im, him]

/-! ### Lado de la energía -/

theorem norm_sq_G (Q : ℕ) (u : ℝ) : ‖G Q u‖ ^ 2 = Real.exp u * tail2 Q (Real.exp (-u)) := by
  have he : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold G sigmaTail tail2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  by_cases h : Real.exp (-u) ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp only [indicator_of_notMem h, norm_zero]
    ring

theorem integral_norm_sq_G_eq (Q : ℕ) :
    ∫ u, ‖G Q u‖ ^ 2 = ∫ x in Ioi (1 : ℝ), sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) := by
  have hM := mellin_eq_fourier (fun x : ℝ => ((tail2 Q x : ℝ) : ℂ)) (s := -1)
  have hL : mellin (fun x : ℝ => ((tail2 Q x : ℝ) : ℂ)) (-1)
      = ((∫ x in Ioi (1 : ℝ), sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) : ℝ) : ℂ) := by
    unfold mellin
    have hfun : (fun t : ℝ => (t : ℂ) ^ ((-1 : ℂ) - 1) • ((tail2 Q t : ℝ) : ℂ))
        = indicator (Ioi (1 : ℝ))
          (fun t : ℝ => ((sigma Q ⌊t⌋₊ ^ 2 * t ^ (-2 : ℝ) : ℝ) : ℂ)) := by
      funext t
      unfold tail2
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
        simp only [indicator_of_mem ht]
        rw [ofReal_mul, ofReal_cpow ht0, smul_eq_mul]
        push_cast
        ring_nf
      · simp [indicator_of_notMem ht]
    rw [hfun, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one,
      integral_complex_ofReal]
  have hR : 𝓕 (fun u : ℝ => Real.exp (-(-1 : ℂ).re * u) • ((tail2 Q (Real.exp (-u)) : ℝ) : ℂ))
      ((-1 : ℂ).im / (2 * Real.pi)) = ((∫ u, ‖G Q u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [norm_sq_G, Complex.real_smul]
  exact_mod_cast hR.symm.trans (hM.symm.trans hL)

theorem integral_sigma_sq_eq_E (Q : ℕ) :
    ∫ x in Ioi (1 : ℝ), sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) = E Q := by
  set f : ℝ → ℝ := fun x => sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) with hf
  set S : ℕ → Set ℝ := fun k => Ico ((k : ℝ) + 1) ((k : ℝ) + 2) with hS
  have hU : (⋃ k, S k) = Ici 1 := by
    ext t
    simp only [S, mem_iUnion, mem_Ico, mem_Ici]
    constructor
    · rintro ⟨k, hk, -⟩
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · intro ht
      have ht0 : 0 ≤ t := by linarith
      have hf1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
      refine ⟨⌊t⌋₊ - 1, ?_, ?_⟩
      · rw [Nat.cast_sub hf1]
        push_cast
        linarith [Nat.floor_le ht0]
      · rw [Nat.cast_sub hf1]
        push_cast
        linarith [Nat.lt_floor_add_one t]
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    simp only [Function.onFun, S]
    rw [Set.Ico_disjoint_Ico]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      exact le_trans (min_le_left _ _) (le_trans (by linarith) (le_max_right _ _))
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      exact le_trans (min_le_right _ _) (le_trans (by linarith) (le_max_left _ _))
  obtain ⟨C, hC⟩ := sigma_acotado Q
  have hint : IntegrableOn f (Ioi 1) := by
    have hg : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
    refine hg.mono' ?_ ?_
    · exact Measurable.aestronglyMeasurable
        ((((measurable_from_nat (f := sigma Q)).comp Nat.measurable_floor).pow_const 2).mul
          (measurable_id.pow_const (-2 : ℝ)))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      have hp := Real.rpow_nonneg hx0.le (-2 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
      have hsq : sigma Q ⌊x⌋₊ ^ 2 ≤ C ^ 2 := by
        have h1 := hC ⌊x⌋₊
        nlinarith [abs_nonneg (sigma Q ⌊x⌋₊), sq_abs (sigma Q ⌊x⌋₊)]
      exact mul_le_mul_of_nonneg_right hsq hp
  have hint' : IntegrableOn f (⋃ k, S k) := by
    rw [hU]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hint
  have hsum := hasSum_integral_iUnion (fun k => measurableSet_Ico) hd hint'
  rw [hU, integral_Ici_eq_integral_Ioi] at hsum
  have hblock : ∀ k : ℕ, ∫ x in Ico ((k : ℝ) + 1) ((k : ℝ) + 2), f x
      = sigma Q (k + 1) ^ 2 * w (k + 1) := by
    intro k
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hcongr : ∀ x ∈ Ioo ((k : ℝ) + 1) ((k : ℝ) + 2),
        f x = sigma Q (k + 1) ^ 2 * x ^ (-2 : ℝ) := by
      intro x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hfl : ⌊x⌋₊ = k + 1 := by
        rw [Nat.floor_eq_iff hx0]
        push_cast
        constructor <;> linarith [hx.1, hx.2]
      simp only [f, hfl]
    rw [integral_Ico_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hcongr,
      integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      integral_rpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt hk0 (by positivity)⟩), w_succ,
      show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
    ring
  simp only [hblock] at hsum
  unfold E
  exact hsum.tsum_eq.symm

/-! ### Integrabilidad -/

theorem sigmaTail_exp_eq_zero (Q : ℕ) {u : ℝ} (hu : 0 ≤ u) : sigmaTail Q (Real.exp (-u)) = 0 := by
  unfold sigmaTail
  apply indicator_of_notMem
  simp only [mem_Ioi, not_lt]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_sigmaTail_le (Q : ℕ) {C : ℝ} (hC : ∀ k, |sigma Q k| ≤ C) (x : ℝ) :
    ‖sigmaTail Q x‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  unfold sigmaTail
  by_cases h : x ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs]
    exact hC _
  · simp only [indicator_of_notMem h, norm_zero]
    exact hC0

theorem integrable_G (Q : ℕ) : Integrable (G Q) ∧ MemLp (G Q) 2 := by
  obtain ⟨C, hC⟩ := sigma_acotado Q
  have hmeas := (measurable_G Q).aestronglyMeasurable (μ := volume)
  have hbound : ∀ u, ‖G Q u‖ ≤ indicator (Iic 0) (fun u => C * Real.exp ((1 / 2) * u)) u := by
    intro u
    by_cases hu : u ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hu]
      unfold G
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        show (1 / 2) * u = u / 2 by ring, mul_comm C]
      exact mul_le_mul_of_nonneg_left (norm_sigmaTail_le Q hC _) (Real.exp_pos _).le
    · rw [indicator_of_notMem hu]
      have : 0 ≤ u := le_of_lt (not_le.mp hu)
      unfold G
      rw [sigmaTail_exp_eq_zero Q this, smul_zero, norm_zero]
  have h1 : Integrable (G Q) := by
    refine Integrable.mono' ?_ hmeas (Filter.Eventually.of_forall hbound)
    exact (integrable_indicator_iff measurableSet_Iic).mpr
      (Integrable.const_mul (integrableOn_exp_mul_Iic (by norm_num) 0) C)
  refine ⟨h1, (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_⟩
  have hbound2 : ∀ u, ‖‖G Q u‖ ^ 2‖ ≤ indicator (Iic 0) (fun u => C ^ 2 * Real.exp (1 * u)) u := by
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := hbound u
    by_cases hu : u ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hu] at hb ⊢
      have hsq : (C * Real.exp ((1 / 2) * u)) ^ 2 = C ^ 2 * Real.exp (1 * u) := by
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
        congr 2
        ring
      rw [← hsq]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    · rw [indicator_of_notMem hu] at hb ⊢
      have h0 : ‖G Q u‖ = 0 := le_antisymm hb (norm_nonneg _)
      rw [h0]
      norm_num
  refine Integrable.mono' ?_ (hmeas.norm.pow 2) (Filter.Eventually.of_forall hbound2)
  exact (integrable_indicator_iff measurableSet_Iic).mpr
    (Integrable.const_mul (integrableOn_exp_mul_Iic (by norm_num) 0) _)

/-! ### La identidad -/

/-- **Estado 45, (2.4)–(2.5)**: `E_Q = (1/2π) ∫ |1 − ζ(1/2+ix) P_Q(1/2+ix)|²/(1/4 + x²) dx`. -/
theorem E_eq_integral_de {Q : ℕ} (hQ : 1 ≤ Q) :
    E Q = (1 / (2 * Real.pi)) *
      ∫ x : ℝ, ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
        / (1 / 4 + x ^ 2) := by
  obtain ⟨h1, h2⟩ := integrable_G Q
  obtain ⟨-, hpl⟩ := plancherel h1 h2
  have hpt : ∀ x : ℝ,
      ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2)
        = ‖𝓕 (G Q) ((-1 / (2 * Real.pi)) * x)‖ ^ 2 := by
    intro x
    rw [show (-1 / (2 * Real.pi)) * x = -x / (2 * Real.pi) by ring, fourier_G hQ x, norm_div,
      div_pow]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hcv := Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (G Q) ξ‖ ^ 2) (-1 / (2 * Real.pi))
  have habs : |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [abs_inv, abs_div, abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      one_div, inv_inv]
  have hE : E Q = ∫ ξ, ‖𝓕 (G Q) ξ‖ ^ 2 := by
    rw [hpl, integral_norm_sq_G_eq, integral_sigma_sq_eq_E]
  rw [hE, integral_congr_ae (Filter.Eventually.of_forall hpt), hcv, habs, smul_eq_mul]
  field_simp

end AMate
