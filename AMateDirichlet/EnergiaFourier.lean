import AMateEnergia.Plancherel
import AMateDirichlet.Testigo

/-!
# La energía de un carácter como integral en la recta crítica

Análogo para `χ ≠ 1` de `AMateEnergia.EnergiaFourier`. En variable logarítmica,
`G_{Q,χ}(u) = e^{u/2} σ_{Q,χ}(⌊e^{−u}⌋)` para `u < 0`:

* `integral_norm_sq_G_eq`: `∫ |G_{Q,χ}|² = ∫_1^∞ |σ_{Q,χ}(⌊x⌋)|² x^{−2} dx`, que vale `E_{Q,χ}`
  por `integral_sigma_sq_eq_E`;
* `fourier_G`: `𝓕 G_{Q,χ}(−y/2π) = (1 − L(s,χ) P_{Q,χ}(s))/s` con `s = 1/2 + iy`, por
  `mellin_eq_fourier` e `integral_sigma_floor`;
* `E_eq_integral`: Plancherel (`plancherel`) y el cambio `ξ = −y/2π`:
  `E_{Q,χ} = (1/2π) ∫ |1 − L(1/2+ix,χ) P_{Q,χ}(1/2+ix)|² / (1/4 + x²) dx`.
-/

open MeasureTheory Set Complex FourierTransform

namespace AMate.Dirichlet

variable {N : ℕ}

/-- `σ_{Q,χ}(⌊x⌋)` en `(1, ∞)`, cero fuera. -/
noncomputable def sigmaTail (χ : DirichletCharacter ℂ N) (Q : ℕ) (x : ℝ) : ℂ :=
  indicator (Ioi 1) (fun x : ℝ => sigma χ Q ⌊x⌋₊) x

/-- `|σ_{Q,χ}(⌊x⌋)|²` en `(1, ∞)`, cero fuera. -/
noncomputable def tail2 (χ : DirichletCharacter ℂ N) (Q : ℕ) (x : ℝ) : ℝ :=
  indicator (Ioi 1) (fun x : ℝ => ‖sigma χ Q ⌊x⌋₊‖ ^ 2) x

/-- El testigo en variable logarítmica: `G(u) = e^{u/2} σ_{Q,χ}(⌊e^{−u}⌋)` si `u < 0`. -/
noncomputable def G (χ : DirichletCharacter ℂ N) (Q : ℕ) (u : ℝ) : ℂ :=
  Real.exp (u / 2) • sigmaTail χ Q (Real.exp (-u))

theorem measurable_sigmaTail (χ : DirichletCharacter ℂ N) (Q : ℕ) :
    Measurable (sigmaTail χ Q) := by
  unfold sigmaTail
  exact ((measurable_from_nat (f := sigma χ Q)).comp Nat.measurable_floor).indicator
    (measurableSet_Ioi (a := (1 : ℝ)))

theorem measurable_G (χ : DirichletCharacter ℂ N) (Q : ℕ) : Measurable (G χ Q) :=
  (Real.measurable_exp.comp (measurable_id.div_const 2)).smul
    ((measurable_sigmaTail χ Q).comp (Real.measurable_exp.comp measurable_neg))

/-! ### Lado de Fourier -/

theorem mellin_sigmaTail (χ : DirichletCharacter ℂ N) (Q : ℕ) (s : ℂ) :
    mellin (sigmaTail χ Q) (-s)
      = ∫ x in Ioi (1 : ℝ), sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) := by
  unfold mellin sigmaTail
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1)
      • indicator (Ioi (1 : ℝ)) (fun x : ℝ => sigma χ Q ⌊x⌋₊) t)
      = indicator (Ioi (1 : ℝ)) (fun t : ℝ => sigma χ Q ⌊t⌋₊ * (t : ℂ) ^ (-s - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [indicator_of_mem ht, mul_comm]
    · simp [indicator_of_notMem ht]
  rw [hfun, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

variable [NeZero N]

/-- `𝓕 G(−y/2π) = (1 − L(s,χ) P_{Q,χ}(s))/s` con `s = 1/2 + iy`. -/
theorem fourier_G {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) (y : ℝ) :
    𝓕 (G χ Q) (-y / (2 * Real.pi))
      = (1 - DirichletCharacter.LFunction χ (1 / 2 + y * I) * P χ Q (1 / 2 + y * I))
          / (1 / 2 + y * I) := by
  have hre : (1 / 2 + (y : ℂ) * I).re = 1 / 2 := by simp
  have him : (1 / 2 + (y : ℂ) * I).im = y := by simp
  have hs0 : 0 < (1 / 2 + (y : ℂ) * I).re := by rw [hre]; norm_num
  rw [← integral_sigma_floor hχ Q hs0, ← mellin_sigmaTail, mellin_eq_fourier]
  have hfun : (fun u : ℝ => Real.exp (-(-(1 / 2 + (y : ℂ) * I)).re * u)
      • sigmaTail χ Q (Real.exp (-u))) = G χ Q := by
    funext u
    unfold G
    rw [neg_re, hre]
    congr 2
    ring
  rw [hfun, neg_im, him]

/-! ### Lado de la energía -/

omit [NeZero N] in
theorem norm_sq_G (χ : DirichletCharacter ℂ N) (Q : ℕ) (u : ℝ) :
    ‖G χ Q u‖ ^ 2 = Real.exp u * tail2 χ Q (Real.exp (-u)) := by
  have he : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold G sigmaTail tail2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  by_cases h : Real.exp (-u) ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, norm_zero]
    ring

omit [NeZero N] in
theorem integral_norm_sq_G_eq (χ : DirichletCharacter ℂ N) (Q : ℕ) :
    ∫ u, ‖G χ Q u‖ ^ 2 = ∫ x in Ioi (1 : ℝ), ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) := by
  have hM := mellin_eq_fourier (fun x : ℝ => ((tail2 χ Q x : ℝ) : ℂ)) (s := -1)
  have hL : mellin (fun x : ℝ => ((tail2 χ Q x : ℝ) : ℂ)) (-1)
      = ((∫ x in Ioi (1 : ℝ), ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) : ℝ) : ℂ) := by
    unfold mellin
    have hfun : (fun t : ℝ => (t : ℂ) ^ ((-1 : ℂ) - 1) • ((tail2 χ Q t : ℝ) : ℂ))
        = indicator (Ioi (1 : ℝ))
          (fun t : ℝ => ((‖sigma χ Q ⌊t⌋₊‖ ^ 2 * t ^ (-2 : ℝ) : ℝ) : ℂ)) := by
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
  have hR : 𝓕 (fun u : ℝ => Real.exp (-(-1 : ℂ).re * u) • ((tail2 χ Q (Real.exp (-u)) : ℝ) : ℂ))
      ((-1 : ℂ).im / (2 * Real.pi)) = ((∫ u, ‖G χ Q u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [norm_sq_G, Complex.real_smul]
  exact_mod_cast hR.symm.trans (hM.symm.trans hL)

/-! ### Integrabilidad -/

omit [NeZero N] in
theorem sigmaTail_exp_eq_zero (χ : DirichletCharacter ℂ N) (Q : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    sigmaTail χ Q (Real.exp (-u)) = 0 := by
  unfold sigmaTail
  apply indicator_of_notMem
  simp only [mem_Ioi, not_lt]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_sigmaTail_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) (x : ℝ) :
    ‖sigmaTail χ Q x‖ ≤ 1 + Q * N := by
  unfold sigmaTail
  by_cases h : x ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h]
    exact norm_sigma_le hχ Q _
  · simp only [indicator_of_notMem h, norm_zero]
    positivity

theorem integrable_G {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) :
    Integrable (G χ Q) ∧ MemLp (G χ Q) 2 := by
  set C : ℝ := 1 + Q * N
  have hmeas := (measurable_G χ Q).aestronglyMeasurable (μ := volume)
  have hbound : ∀ u, ‖G χ Q u‖ ≤ indicator (Iic 0) (fun u => C * Real.exp ((1 / 2) * u)) u := by
    intro u
    by_cases hu : u ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hu]
      unfold G
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        show (1 / 2) * u = u / 2 by ring, mul_comm C]
      exact mul_le_mul_of_nonneg_left (norm_sigmaTail_le hχ Q _) (Real.exp_pos _).le
    · rw [indicator_of_notMem hu]
      have : 0 ≤ u := le_of_lt (not_le.mp hu)
      unfold G
      rw [sigmaTail_exp_eq_zero χ Q this, smul_zero, norm_zero]
  have h1 : Integrable (G χ Q) := by
    refine Integrable.mono' ?_ hmeas (Filter.Eventually.of_forall hbound)
    exact (integrable_indicator_iff measurableSet_Iic).mpr
      (Integrable.const_mul (integrableOn_exp_mul_Iic (by norm_num) 0) C)
  refine ⟨h1, (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_⟩
  have hbound2 : ∀ u, ‖‖G χ Q u‖ ^ 2‖
      ≤ indicator (Iic 0) (fun u => C ^ 2 * Real.exp (1 * u)) u := by
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
      have h0 : ‖G χ Q u‖ = 0 := le_antisymm hb (norm_nonneg _)
      rw [h0]
      norm_num
  refine Integrable.mono' ?_ (hmeas.norm.pow 2) (Filter.Eventually.of_forall hbound2)
  exact (integrable_indicator_iff measurableSet_Iic).mpr
    (Integrable.const_mul (integrableOn_exp_mul_Iic (by norm_num) 0) _)

/-! ### La identidad -/

/-- `E_{Q,χ} = (1/2π) ∫ |1 − L(1/2+ix,χ) P_{Q,χ}(1/2+ix)|² / (1/4 + x²) dx`. -/
theorem E_eq_integral {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) :
    E χ Q = (1 / (2 * Real.pi)) *
      ∫ x : ℝ, ‖1 - DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I)
          * P χ Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2) := by
  obtain ⟨h1, h2⟩ := integrable_G hχ Q
  obtain ⟨-, hpl⟩ := plancherel h1 h2
  have hpt : ∀ x : ℝ,
      ‖1 - DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I) * P χ Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
          / (1 / 4 + x ^ 2)
        = ‖𝓕 (G χ Q) ((-1 / (2 * Real.pi)) * x)‖ ^ 2 := by
    intro x
    rw [show (-1 / (2 * Real.pi)) * x = -x / (2 * Real.pi) by ring, fourier_G hχ Q x, norm_div,
      div_pow]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hcv := Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (G χ Q) ξ‖ ^ 2) (-1 / (2 * Real.pi))
  have habs : |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [abs_inv, abs_div, abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      one_div, inv_inv]
  have hE : E χ Q = ∫ ξ, ‖𝓕 (G χ Q) ξ‖ ^ 2 := by
    rw [hpl, integral_norm_sq_G_eq, integral_sigma_sq_eq_E hχ]
  rw [hE, integral_congr_ae (Filter.Eventually.of_forall hpt), hcv, habs, smul_eq_mul]
  field_simp

end AMate.Dirichlet
