import AMateMiller.FormulaRect
import AMateMiller.HadamardLimite

/-!
# Fórmula explícita ponderada: paso al límite

Para `χ` primitivo, `x ≥ 1` y `0 < α < β < 1/2`, si las sumas `∑ m_ρ K(ρ)` sobre los ceros con
`|Im ρ| < T'` están acotadas por `Zb` para todo `T'`, entonces

  `|S(x) + Res + ε₀/(αβ) − δ₁ K(1)| ≤ Zb + (1/2π) ∫ |L'/L(−1/2 + iy) K(−1/2 + iy)| dy`

(`cota_S`). Se usa `rect_K` en alturas buenas `T'_k → ∞`: los lados horizontales tienden a `0`,
el derecho tiende a `−2π S(x)` (`perron_L`) y el izquierdo se acota por la integral completa.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF

noncomputable section

namespace AMate.Miller.Ponderada

open AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- `|K(σ + iy)| ≤ x^{3/2}/y²` para `x ≥ 1`, `σ ≤ 3/2` y `y ≠ 0`. -/
theorem norm_K_le {x α β σ y : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ 3 / 2) (hy : 0 < |y|) :
    ‖K x α β ((σ : ℂ) + y * I)‖ ≤ x ^ (3 / 2 : ℝ) / |y| ^ 2 := by
  unfold K
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
  have ha : |y| ≤ ‖(σ : ℂ) + y * I + α‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + y * I + α); simpa using this
  have hb : |y| ≤ ‖(σ : ℂ) + y * I + β‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + y * I + β); simpa using this
  have hxσ : x ^ σ ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ
  calc x ^ σ / (‖(σ : ℂ) + y * I + α‖ * ‖(σ : ℂ) + y * I + β‖) ≤ x ^ (3 / 2 : ℝ) / (|y| * |y|) := by
        apply div_le_div₀ (by positivity) hxσ (by positivity) (mul_le_mul ha hb hy.le (by linarith))
    _ = x ^ (3 / 2 : ℝ) / |y| ^ 2 := by rw [sq]

/-- `y ↦ L'/L(3/2 + iy) K(3/2 + iy)` es integrable. -/
theorem integrable_derecha (χ : DirichletCharacter ℂ N) {x α β : ℝ} (hx : 0 < x) (hα : 0 < α)
    (hαβ : α < β) :
    Integrable fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ) (((3 / 2 : ℝ) : ℂ) + y * I) *
      K x α β (((3 / 2 : ℝ) : ℂ) + y * I) := by
  have hre : ∀ y : ℝ, 1 < (((3 / 2 : ℝ) : ℂ) + y * I).re := fun y => by simp; norm_num
  have hne1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hL : ∀ y : ℝ, DirichletCharacter.LFunction χ (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (hne1 y)) (hre y).le
  have hKi := integrable_kernel (c := 3 / 2) (α := α) (β := β) hx (by linarith) (by linarith)
  have hcont : Continuous fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      (((3 / 2 : ℝ) : ℂ) + y * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_logDeriv_L χ (hne1 y) (hL y)).comp
      (f := fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + y * I) (by fun_prop)
  refine (hKi.norm.const_mul (VM (3 / 2))).mono' (hcont.aestronglyMeasurable.mul hKi.1)
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  have h1 := norm_logDeriv_le_VM χ (hre y)
  have e : (((3 / 2 : ℝ) : ℂ) + y * I).re = 3 / 2 := by simp
  rw [e] at h1
  unfold K
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Cota de la fórmula explícita ponderada.** -/
theorem cota_S (h : HipHadamard) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {x α β : ℝ}
    (hx : 1 ≤ x) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2)
    (hLE : Integrable fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      (((-1 / 2 : ℝ) : ℂ) + y * I) * K x α β (((-1 / 2 : ℝ) : ℂ) + y * I))
    {Zb : ℝ} (hZ : ∀ (T' : ℝ) (hfin : (ZerosBelow χ T').Finite),
      ‖∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * K x α β ρ‖ ≤ Zb) :
    ‖S χ x α β + Res χ x α β + eps0 χ / (α * β) - del1 χ * K x α β 1‖ ≤
      Zb + (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + y * I) * K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)‖ := by
  obtain ⟨κ, Ch, hκ, hGHE, hLDH⟩ := h.alt
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hgood : ∀ k : ℕ, ∃ T' : ℝ, (k : ℝ) + 2 ≤ T' ∧ T' ≤ (k : ℝ) + 2 + 1 ∧ GoodHeight χ κ T' :=
    fun k => hGHE N χ hp ((k : ℝ) + 2) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  choose Tk hTk1 hTk2 hTkg using hgood
  have hTk2' : ∀ k, 2 ≤ Tk k := fun k => by linarith [hTk1 k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hTk0 : ∀ k, 0 < Tk k := fun k => by linarith [hTk2' k]
  have hno : ∀ k, NoOrdinate χ (Tk k) := fun k => noOrdinate_of_good hκ (hTk2' k) (hTkg k)
  have hreg : ∀ k, ∃ H₀ : ℂ → ℂ, IsRegPart χ (3 / 2) (Tk k) H₀ := fun k =>
    h.rp N χ hp (3 / 2) (Tk k) (by norm_num) (hTk0 k) (hno k)
  choose H₀ hH₀ using hreg
  have hfk : ∀ k, (ZerosBelow χ (Tk k)).Finite := fun k => h.zf N χ hp (Tk k)
  have hTk_top : Tendsto Tk atTop atTop :=
    tendsto_atTop_mono (fun k => hTk1 k)
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set F : ℂ → ℂ := fun s => logDeriv (DirichletCharacter.LFunction χ) s * K x α β s with hF
  set X : ℂ := S χ x α β + Res χ x α β + eps0 χ / (α * β) - del1 χ * K x α β 1 with hX
  set LEint : ℝ := ∫ y : ℝ, ‖F (((-1 / 2 : ℝ) : ℂ) + y * I)‖ with hLEint
  -- los cuatro lados
  set bot : ℕ → ℂ := fun k => ∫ σ : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), F (σ + ((-Tk k : ℝ) : ℂ) * I)
  set top : ℕ → ℂ := fun k => ∫ σ : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), F (σ + (Tk k : ℂ) * I)
  set rgt : ℕ → ℂ := fun k => ∫ y : ℝ in (-Tk k)..(Tk k), F (((3 / 2 : ℝ) : ℂ) + y * I)
  set lft : ℕ → ℂ := fun k => ∫ y : ℝ in (-Tk k)..(Tk k), F (((-1 / 2 : ℝ) : ℂ) + y * I)
  have h2π : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdesc : ∀ k, X = -(∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * K x α β ρ) +
      (bot k - top k) / (2 * Real.pi * I) + (rgt k / (2 * Real.pi) + S χ x α β) -
        lft k / (2 * Real.pi) := by
    intro k
    have hid := rect_K h.rc h.zl hp (hTk0 k) (hno k) (hH₀ k) (hfk k) hx0 hα hαβ hβ
    have hri : rectInt F (-1 / 2) (3 / 2) (-Tk k) (Tk k) =
        (bot k - top k) + I * rgt k - I * lft k := by
      simp only [rectInt, smul_eq_mul, bot, top, rgt, lft]
    rw [hri] at hid
    have : (bot k - top k + I * rgt k - I * lft k) / (2 * Real.pi * I) =
        (bot k - top k) / (2 * Real.pi * I) + rgt k / (2 * Real.pi) - lft k / (2 * Real.pi) := by
      have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    rw [this] at hid
    rw [hX]
    linear_combination -hid
  -- cotas
  have hlft : ∀ k, ‖lft k‖ ≤ LEint := by
    intro k
    calc ‖lft k‖ ≤ ∫ y : ℝ in (-Tk k)..(Tk k), ‖F (((-1 / 2 : ℝ) : ℂ) + y * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hTk0 k])
      _ ≤ LEint := by
          rw [intervalIntegral.integral_of_le (by linarith [hTk0 k])]
          exact setIntegral_le_integral hLE.norm (Eventually.of_forall fun y => norm_nonneg _)
  set M : ℝ := 4 * N * |Ch| * x ^ (3 / 2 : ℝ) * 2 with hM
  have hhor : ∀ k : ℕ, ∀ y : ℝ, (y = Tk k ∨ y = -Tk k) →
      ‖∫ σ : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), F (σ + y * I)‖ ≤ M / Tk k := by
    intro k y hy
    have hT := hTk2' k
    have hT0 := hTk0 k
    have hyabs : |y| = Tk k := by
      rcases hy with rfl | rfl
      · exact abs_of_pos hT0
      · rw [abs_neg]; exact abs_of_pos hT0
    have hb : ∀ σ ∈ Set.uIoc (-1 / 2 : ℝ) (3 / 2), ‖F (σ + y * I)‖ ≤
        |Ch| * (4 * (N * Tk k)) * (x ^ (3 / 2 : ℝ) / Tk k ^ 2) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      have hL := hLDH N χ hp (Tk k) hT (hTkg k) σ hσ.1.le (by linarith [hσ.2])
      have hL' : ‖logDeriv (DirichletCharacter.LFunction χ) (σ + y * I)‖ ≤
          Ch * Real.log (N * Tk k) ^ 2 := by
        rcases hy with rfl | rfl
        · exact hL.1
        · exact hL.2
      have hlog := log_sq_le (show 1 ≤ (N : ℝ) * Tk k by nlinarith)
      have hK := norm_K_le (α := α) (β := β) hx hσ.2 (y := y) (by rw [hyabs]; exact hT0)
      rw [hyabs] at hK
      simp only [hF]
      rw [norm_mul]
      refine mul_le_mul ?_ hK (norm_nonneg _) (by positivity)
      calc ‖logDeriv (DirichletCharacter.LFunction χ) (σ + y * I)‖ ≤ Ch * Real.log (N * Tk k) ^ 2 := hL'
        _ ≤ |Ch| * Real.log (N * Tk k) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ |Ch| * (4 * (N * Tk k)) := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
    rw [show |(3 / 2 : ℝ) - -1 / 2| = 2 by norm_num, hM]
    field_simp
  have hdec : Tendsto (fun k => M / Tk k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hTk_top
  have hbot : Tendsto bot atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hhor k (-Tk k) (Or.inr rfl)) hdec
  have htop : Tendsto top atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hhor k (Tk k) (Or.inl rfl)) hdec
  have hrgt : Tendsto (fun k => rgt k / (2 * Real.pi) + S χ x α β) atTop (𝓝 0) := by
    have hi := integrable_derecha χ hx0 hα hαβ
    have h1 := intervalIntegral_tendsto_integral hi (tendsto_neg_atTop_atBot.comp hTk_top) hTk_top
    have hP := perron_L χ hx0 hα hαβ
    simp_rw [neg_mul] at hP
    rw [integral_neg] at hP
    have hval : (∫ y : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((3 / 2 : ℝ) : ℂ) + y * I) *
        K x α β (((3 / 2 : ℝ) : ℂ) + y * I)) / (2 * Real.pi) + S χ x α β = 0 := by
      rw [← hP]
      ring
    rw [← hval]
    exact (h1.div_const _).add_const _
  -- el error total tiende a `0`
  set e : ℕ → ℝ := fun k => ‖(bot k - top k) / (2 * Real.pi * I)‖ +
    ‖rgt k / (2 * Real.pi) + S χ x α β‖ with he
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h := (((hbot.sub htop).div_const (2 * Real.pi * I)).norm).add hrgt.norm
    simp only [sub_zero, zero_div, norm_zero, add_zero] at h
    exact h
  have hbound : ∀ k, ‖X‖ ≤ Zb + (1 / (2 * Real.pi)) * LEint + e k := by
    intro k
    rw [hdesc k]
    have h1 := hZ (Tk k) (hfk k)
    have h2 : ‖lft k / (2 * Real.pi)‖ ≤ (1 / (2 * Real.pi)) * LEint := by
      rw [norm_div, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
        rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hpi]]
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (hlft k) (by positivity)
    calc ‖-(∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * K x α β ρ) +
          (bot k - top k) / (2 * Real.pi * I) + (rgt k / (2 * Real.pi) + S χ x α β) -
            lft k / (2 * Real.pi)‖
        ≤ ‖∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * K x α β ρ‖ +
          ‖(bot k - top k) / (2 * Real.pi * I)‖ + ‖rgt k / (2 * Real.pi) + S χ x α β‖ +
            ‖lft k / (2 * Real.pi)‖ := by
          have := norm_sub_le (-(∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * K x α β ρ) +
            (bot k - top k) / (2 * Real.pi * I) + (rgt k / (2 * Real.pi) + S χ x α β))
            (lft k / (2 * Real.pi))
          have := norm_add₃_le (a := -(∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * K x α β ρ))
            (b := (bot k - top k) / (2 * Real.pi * I)) (c := rgt k / (2 * Real.pi) + S χ x α β)
          rw [norm_neg] at this
          linarith
      _ ≤ Zb + (1 / (2 * Real.pi)) * LEint + e k := by
          simp only [he]
          linarith
  have hlim : Tendsto (fun k => Zb + (1 / (2 * Real.pi)) * LEint + e k) atTop
      (𝓝 (Zb + (1 / (2 * Real.pi)) * LEint)) := by
    simpa using he0.const_add (Zb + (1 / (2 * Real.pi)) * LEint)
  exact ge_of_tendsto' hlim hbound

end AMate.Miller.Ponderada
