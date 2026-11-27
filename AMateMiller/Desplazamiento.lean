import Mathlib

/-!
# Desplazamiento de rectas verticales hacia la derecha

`integral_vertical_eq_zero`: si `f` es holomorfa en `Re s > c₀` y `‖f s‖ ≤ B ‖s − s₀‖^{-3/2}` en
`Re s ≥ c` (con `c₀ < c` y `Re s₀ < c`), entonces `∫ f(c + it) dt = 0`.

Se mueve la recta hacia la derecha con el teorema de Cauchy en rectángulos `[c, R] × [−n, n]`
(los lados horizontales tienden a `0`) y luego `R → ∞` por convergencia dominada.
-/

open Complex MeasureTheory Filter Topology Set

namespace AMate.Miller.Contorno

/-- `t ↦ max(δ, |t − y₀|)^{-3/2}` es integrable. -/
theorem integrable_dom {δ : ℝ} (hδ : 0 < δ) (y₀ : ℝ) :
    Integrable (fun t : ℝ => (max δ |t - y₀|) ^ (-(3 / 2 : ℝ))) := by
  set m : ℝ := min δ 1 / 2 with hm
  have hm0 : 0 < m := by positivity
  have h1 : Integrable (fun t : ℝ => m ^ (-(3 / 2 : ℝ)) * (1 + ‖t - y₀‖) ^ (-(3 / 2 : ℝ))) := by
    have : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
      integrable_one_add_norm (by simp; norm_num)
    exact (this.comp_sub_right y₀).const_mul _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (max δ |t - y₀|) ^ (-(3 / 2 : ℝ))) volume :=
    ((measurable_const.max (measurable_id.sub_const y₀).abs).pow_const _).aestronglyMeasurable
  refine h1.mono' hmeas (Eventually.of_forall fun t => ?_)
  have hpos : 0 < max δ |t - y₀| := lt_max_of_lt_left hδ
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le _), Real.norm_eq_abs]
  have hle : m * (1 + |t - y₀|) ≤ max δ |t - y₀| := by
    rcases le_or_gt 1 |t - y₀| with h | h
    · have : m ≤ 1 / 2 := by rw [hm]; linarith [min_le_right δ 1]
      have : m * (1 + |t - y₀|) ≤ (1 / 2) * (1 + |t - y₀|) := by gcongr
      linarith [le_max_right δ |t - y₀|]
    · have : m * (1 + |t - y₀|) ≤ m * 2 := by gcongr; linarith
      have : m * 2 = min δ 1 := by rw [hm]; ring
      linarith [min_le_left δ 1, le_max_left δ |t - y₀|]
  calc (max δ |t - y₀|) ^ (-(3 / 2 : ℝ)) ≤ (m * (1 + |t - y₀|)) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
    _ = m ^ (-(3 / 2 : ℝ)) * (1 + |t - y₀|) ^ (-(3 / 2 : ℝ)) :=
        Real.mul_rpow hm0.le (by positivity)

/-- Cota de `‖σ + it − s₀‖^{-3/2}` por la función dominante. -/
theorem rpow_dist_le {s₀ : ℂ} {σ t δ : ℝ} (hδ : 0 < δ) (hσ : δ ≤ σ - s₀.re) :
    ‖((σ : ℂ) + t * I) - s₀‖ ^ (-(3 / 2 : ℝ)) ≤ (max δ |t - s₀.im|) ^ (-(3 / 2 : ℝ)) := by
  apply Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_left hδ) _ (by norm_num)
  apply max_le
  · refine hσ.trans ?_
    have := Complex.abs_re_le_norm (((σ : ℂ) + t * I) - s₀)
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero] at this
    exact (le_abs_self _).trans this
  · have := Complex.abs_im_le_norm (((σ : ℂ) + t * I) - s₀)
    simpa using this

/-- **Desplazamiento a la derecha.** -/
theorem integral_vertical_eq_zero {f : ℂ → ℂ} {c c₀ B : ℝ} {s₀ : ℂ}
    (hc₀ : c₀ < c) (hs₀ : s₀.re < c)
    (hf : DifferentiableOn ℂ f {s : ℂ | c₀ < s.re})
    (hB : ∀ s : ℂ, c ≤ s.re → ‖f s‖ ≤ B * ‖s - s₀‖ ^ (-(3 / 2 : ℝ))) :
    ∫ t : ℝ, f (c + t * I) = 0 := by
  set δ : ℝ := c - s₀.re with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set y₀ := s₀.im with hy₀
  have hB0 : 0 ≤ B := by
    have h := hB c (by simp)
    have hp : 0 < ‖(c : ℂ) - s₀‖ ^ (-(3 / 2 : ℝ)) := by
      apply Real.rpow_pos_of_pos
      rw [norm_pos_iff, sub_ne_zero]
      intro e
      have := congrArg Complex.re e
      simp at this
      linarith
    by_contra hneg
    push Not at hneg
    have : B * ‖(c : ℂ) - s₀‖ ^ (-(3 / 2 : ℝ)) < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (f c)]
  set D : ℝ → ℝ := fun t => B * (max δ |t - y₀|) ^ (-(3 / 2 : ℝ)) with hD
  have hDi : Integrable D := (integrable_dom hδ y₀).const_mul B
  -- cotas en rectas verticales
  have hdom : ∀ σ : ℝ, c ≤ σ → ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ D t := by
    intro σ hσ t
    have h1 := hB (σ + t * I) (by simpa using hσ)
    refine h1.trans (mul_le_mul_of_nonneg_left (rpow_dist_le hδ (by rw [hδdef]; linarith)) hB0)
  have hcont : ∀ σ : ℝ, c ≤ σ → Continuous fun t : ℝ => f (σ + t * I) := by
    intro σ hσ
    have hco : ContinuousOn f {s : ℂ | c₀ < s.re} := hf.continuousOn
    refine hco.comp_continuous (by fun_prop) fun t => ?_
    show c₀ < ((σ : ℂ) + t * I).re
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      add_zero]
    linarith
  have hint : ∀ σ : ℝ, c ≤ σ → Integrable fun t : ℝ => f (σ + t * I) := fun σ hσ =>
    hDi.mono' (hcont σ hσ).aestronglyMeasurable (Eventually.of_forall (hdom σ hσ))
  -- paso 1: la integral no depende de `R ≥ c`
  have hstep : ∀ R : ℝ, c ≤ R → ∫ t : ℝ, f (c + t * I) = ∫ t : ℝ, f (R + t * I) := by
    intro R hR
    have hrect : ∀ n : ℕ,
        (∫ x : ℝ in c..R, f (x + ((-(n : ℝ) : ℝ) : ℂ) * I)) - (∫ x : ℝ in c..R, f (x + ((n : ℝ) : ℂ) * I)) +
          I • (∫ y : ℝ in (-(n : ℝ))..(n : ℝ), f (R + y * I)) -
            I • (∫ y : ℝ in (-(n : ℝ))..(n : ℝ), f (c + y * I)) = 0 := by
      intro n
      have h := integral_boundary_rect_eq_zero_of_differentiableOn f
        ⟨c, -(n : ℝ)⟩ ⟨R, (n : ℝ)⟩ ?_
      · exact h
      · refine hf.mono fun s hs => ?_
        rw [Complex.mem_reProdIm] at hs
        have := hs.1
        rw [Set.mem_uIcc] at this
        show c₀ < s.re
        rcases this with h | h <;> linarith [h.1, h.2]
    -- los lados horizontales tienden a 0
    have hhor : ∀ y : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) ≤ |y n|) →
        Tendsto (fun n : ℕ => ∫ x : ℝ in c..R, f (x + ((y n : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      intro y hy
      have hbd : ∀ᶠ n : ℕ in atTop, ‖∫ x : ℝ in c..R, f (x + ((y n : ℝ) : ℂ) * I)‖ ≤
          B * ((n : ℝ) - |y₀|) ^ (-(3 / 2 : ℝ)) * |R - c| := by
        filter_upwards [eventually_gt_atTop (⌈|y₀|⌉₊ + 1)] with n hn
        have hn' : |y₀| + 1 < (n : ℝ) := by
          have := Nat.le_ceil |y₀|
          have : ((⌈|y₀|⌉₊ + 1 : ℕ) : ℝ) < n := by exact_mod_cast hn
          push_cast at this
          linarith
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le hR] at hx
        have h1 := hB (x + ((y n : ℝ) : ℂ) * I) (by simp; linarith [hx.1])
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hB0)
        apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
        have him := Complex.abs_im_le_norm ((x : ℂ) + ((y n : ℝ) : ℂ) * I - s₀)
        have e : ((x : ℂ) + ((y n : ℝ) : ℂ) * I - s₀).im = y n - y₀ := by simp [hy₀]
        rw [e] at him
        have := abs_sub_abs_le_abs_sub (y n) y₀
        linarith [hy n]
      have hlim : Tendsto (fun n : ℕ => B * ((n : ℝ) - |y₀|) ^ (-(3 / 2 : ℝ)) * |R - c|) atTop
          (𝓝 0) := by
        have h0 : Tendsto (fun n : ℕ => ((n : ℝ) - |y₀|) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by norm_num)).comp
            (tendsto_atTop_add_const_right _ (-|y₀|) tendsto_natCast_atTop_atTop)
        have := (h0.const_mul B).mul_const |R - c|
        simpa using this
      exact squeeze_zero_norm' hbd hlim
    have hv : ∀ σ : ℝ, c ≤ σ → Tendsto (fun n : ℕ => ∫ y : ℝ in (-(n : ℝ))..(n : ℝ), f (σ + y * I))
        atTop (𝓝 (∫ t : ℝ, f (σ + t * I))) := fun σ hσ =>
      intervalIntegral_tendsto_integral (hint σ hσ)
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
    have h1 := hhor (fun n => -(n : ℝ)) (fun n => by rw [abs_neg, Nat.abs_cast])
    have h2 := hhor (fun n => (n : ℝ)) (fun n => by rw [Nat.abs_cast])
    have hT := ((h1.sub h2).add ((hv R hR).const_smul I)).sub ((hv c le_rfl).const_smul I)
    have hz := tendsto_nhds_unique tendsto_const_nhds
      (hT.congr' (Eventually.of_forall fun n => hrect n))
    simp only [sub_zero, zero_add, smul_eq_mul] at hz
    have : I * ((∫ t : ℝ, f (R + t * I)) - ∫ t : ℝ, f (c + t * I)) = 0 := by
      rw [mul_sub]; exact hz.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h I_ne_zero
    · exact (sub_eq_zero.mp h).symm
  -- paso 2: la integral en `Re s = c + n` tiende a 0
  have hlim : Tendsto (fun n : ℕ => ∫ t : ℝ, f ((c + n : ℝ) + t * I)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (F := fun (n : ℕ) (t : ℝ) =>
      f ((c + n : ℝ) + t * I)) (f := fun _ => (0 : ℂ)) D
      (fun n => (hcont (c + n) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])).aestronglyMeasurable)
      hDi (fun n => Eventually.of_forall (hdom (c + n) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])))
      (Eventually.of_forall fun t => ?_)
    · rwa [integral_zero] at h
    · -- ‖f((c+n) + it)‖ ≤ B (δ + n)^{-3/2} → 0
      have hb : ∀ n : ℕ, ‖f ((c + n : ℝ) + t * I)‖ ≤ B * (δ + n) ^ (-(3 / 2 : ℝ)) := by
        intro n
        have h1 := hB ((c + n : ℝ) + t * I) (by simp)
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hB0)
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
        have := Complex.abs_re_le_norm (((c + n : ℝ) : ℂ) + t * I - s₀)
        simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
          sub_zero, add_zero] at this
        have e : c + (n : ℝ) - s₀.re = δ + n := by rw [hδdef]; ring
        rw [e] at this
        exact (le_abs_self _).trans this
      have h0 : Tendsto (fun n : ℕ => B * (δ + n) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 2 by norm_num)).comp
          (tendsto_atTop_add_const_left _ δ tendsto_natCast_atTop_atTop)
        simpa using this.const_mul B
      exact squeeze_zero_norm hb h0
  have heq : ∀ n : ℕ, ∫ t : ℝ, f (c + t * I) = ∫ t : ℝ, f ((c + n : ℝ) + t * I) := fun n =>
    hstep (c + n) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact tendsto_nhds_unique (tendsto_const_nhds.congr heq) hlim

end AMate.Miller.Contorno
