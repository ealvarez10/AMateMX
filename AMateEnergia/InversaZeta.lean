import AMateEnergia.ZetaIntegral

/-!
# Cota de `1/ζ` bajo la hipótesis de Riemann

Primera mitad del lema de Balazard–Saias (estado 45, §3), según Titchmarsh, §14.2.

* `exists_log_ball`: logaritmo holomorfo de una función sin ceros en un disco (primitiva de
  `g'/g`, `DifferentiableOn.isExactOn_ball`).
* `three_circles`: tres círculos de Hadamard, de las tres rectas de Mathlib aplicadas a
  `w ↦ f(c + e^w)`.
* `zeta_bounds_of_one_lt`, `logDeriv_zeta_bound`: `ζ`, `1/ζ` y `ζ'/ζ` acotadas en `Re s ≥ σ₀ > 1`.
* `inv_zeta_bound`: bajo RH, `‖1/ζ(s)‖ ≤ C |t|^η` en `Re s ≥ 1/2 + δ`, `|t| ≥ 3`. En el disco de
  centro `2 + it`, `log ζ` existe por RH; Borel–Carathéodory (Mathlib) da `|log ζ| ≪ log |t|` en el
  radio `3/2 − δ/2`, la serie de `ζ'/ζ` da `|log ζ| ≪ 1` en el radio `1/2`, y los tres círculos
  interpolan con exponente `θ₀ < 1`, de modo que `|log ζ| ≤ η log |t| + C`.
-/

open Complex Metric Set

namespace AMate

/-! ### Logaritmo holomorfo en un disco -/

/-- Una función holomorfa sin ceros en un disco tiene un logaritmo holomorfo, con derivada
`g'/g` y valor `log (g c)` en el centro. -/
theorem exists_log_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (h0 : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ L : ℂ → ℂ, L c = Complex.log (g c) ∧
      (∀ z ∈ ball c r, HasDerivAt L (deriv g z / g z) z) ∧
      (∀ z ∈ ball c r, Complex.exp (L z) = g z) := by
  have hopen : IsOpen (ball c r) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) :=
    (hg.deriv hopen).div hg h0
  obtain ⟨F, hFc, hF⟩ := hd.isExactOn_ball.with_val_at c (Complex.log (g c))
  refine ⟨F, hFc, hF, ?_⟩
  have hderiv : ∀ z ∈ ball c r, HasDerivAt (fun z => g z * Complex.exp (-F z)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have h1 := hgz.mul (hF z hz).neg.cexp
    have hgz0 := h0 z hz
    have hq : g z * (deriv g z / g z) = deriv g z := by field_simp
    have e : deriv g z * Complex.exp (-F z)
        + g z * (Complex.exp (-F z) * -(deriv g z / g z)) = 0 := by
      linear_combination (-(Complex.exp (-F z))) * hq
    exact h1.congr_deriv e
  have hdiff : DifferentiableOn ℂ (fun z => g z * Complex.exp (-F z)) (ball c r) :=
    fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  have hc : c ∈ ball c r := mem_ball_self hr
  intro z hz
  have hk := hopen.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hdiff
    (fun w hw => (hderiv w hw).deriv) hz hc
  have hgc : g c * Complex.exp (-F c) = 1 := by
    rw [hFc, Complex.exp_neg, Complex.exp_log (h0 c hc)]
    exact mul_inv_cancel₀ (h0 c hc)
  rw [hgc, Complex.exp_neg] at hk
  have hne : Complex.exp (F z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hk
  exact hk.symm

/-! ### Tres círculos de Hadamard -/

/-- **Tres círculos de Hadamard**, a partir de las tres rectas aplicadas a `w ↦ f(c + e^w)`. -/
theorem three_circles {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ R : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂)
    (h2R : r₂ < R) (hf : DifferentiableOn ℂ f (ball c R)) {a b : ℝ}
    (ha : ∀ z, ‖z - c‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z, ‖z - c‖ = r₂ → ‖f z‖ ≤ b)
    {z : ℂ} (hz1 : r₁ ≤ ‖z - c‖) (hz2 : ‖z - c‖ ≤ r₂) :
    ‖f z‖ ≤ a ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₂ - Real.log r₁))
      * b ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₂ - Real.log r₁)) := by
  set F : ℂ → ℂ := fun w => f (c + Complex.exp w) with hFdef
  have hlu : Real.log r₁ < Real.log r₂ := Real.log_lt_log h1 h12
  have hR0 : 0 < R := by linarith
  have hdiffF : DifferentiableOn ℂ F {w | w.re < Real.log R} := by
    intro w hw
    have hmem : c + Complex.exp w ∈ ball c R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
      calc Real.exp w.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hw
        _ = R := Real.exp_log hR0
    have hfa : DifferentiableAt ℂ f (c + Complex.exp w) :=
      hf.differentiableAt (isOpen_ball.mem_nhds hmem)
    exact (hfa.comp w ((differentiableAt_const c).add Complex.differentiableAt_exp)).differentiableWithinAt
  have hstrip : HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₂)
      ⊆ {w | w.re < Real.log R} := fun w hw =>
    lt_of_le_of_lt hw.2 (Real.log_lt_log (by linarith) h2R)
  have hcl : closure (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₂))
      ⊆ HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₂) :=
    closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) (isClosed_Icc.preimage continuous_re)
  have hd : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₂)) :=
    (hdiffF.mono (hcl.trans hstrip)).diffContOnCl
  have hB : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₂)) := by
    have hcont : ContinuousOn (fun z => ‖f z‖) (closedBall c r₂) :=
      (hf.continuousOn.mono (closedBall_subset_ball h2R)).norm
    obtain ⟨K, hK⟩ := (isCompact_closedBall c r₂).bddAbove_image hcont
    refine ⟨K, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    apply hK
    refine ⟨c + Complex.exp w, ?_, rfl⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp (Real.log r₂) := Real.exp_le_exp.mpr hw.2
      _ = r₂ := Real.exp_log (by linarith)
  have haF : ∀ w ∈ re ⁻¹' {Real.log r₁}, ‖F w‖ ≤ a := by
    intro w hw
    have hw' : w.re = Real.log r₁ := hw
    apply ha
    rw [add_sub_cancel_left, Complex.norm_exp, hw', Real.exp_log h1]
  have hbF : ∀ w ∈ re ⁻¹' {Real.log r₂}, ‖F w‖ ≤ b := by
    intro w hw
    have hw' : w.re = Real.log r₂ := hw
    apply hb
    rw [add_sub_cancel_left, Complex.norm_exp, hw', Real.exp_log (by linarith)]
  have hzc : z - c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    linarith
  have hw : (Complex.log (z - c)).re = Real.log ‖z - c‖ := Complex.log_re _
  have hmem : Complex.log (z - c)
      ∈ HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₂) := by
    show (Complex.log (z - c)).re ∈ Icc _ _
    rw [hw]
    exact ⟨Real.log_le_log h1 hz1, Real.log_le_log (by linarith) hz2⟩
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hmem hd hB haF hbF
  have hFz : F (Complex.log (z - c)) = f z := by
    show f (c + Complex.exp (Complex.log (z - c))) = f z
    rw [Complex.exp_log hzc]
    congr 1
    ring
  rw [hFz, hw] at h3
  exact h3

/-! ### Cotas en `Re s > 1` -/

theorem norm_LSeries_le_of_re {f : ℕ → ℂ} {σ₀ : ℝ}
    (hsum : Summable (fun n => ‖LSeries.term f σ₀ n‖)) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f σ₀ n‖ := by
  have hle : ∀ n, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f σ₀ n‖ :=
    fun n => LSeries.norm_term_le_of_re_le_re f (by simpa using hs) n
  have hs' : Summable (fun n => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum
  calc ‖LSeries f s‖ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' n, ‖LSeries.term f σ₀ n‖ := Summable.tsum_le_tsum hle hs' hsum

/-- Para `Re s ≥ σ₀ > 1`, `‖ζ(s)‖` y `‖1/ζ(s)‖` están acotados. -/
theorem zeta_bounds_of_one_lt {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ S : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → ‖riemannZeta s‖ ≤ S ∧ ‖(riemannZeta s)⁻¹‖ ≤ S := by
  have hre : 1 < (σ₀ : ℂ).re := by simpa using hσ₀
  have h1 : Summable (fun n => ‖LSeries.term (1 : ℕ → ℂ) σ₀ n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr hre)
  have hμ : Summable (fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) σ₀ n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hre)
  have hn1 : 0 ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) σ₀ n‖ := tsum_nonneg fun n => norm_nonneg _
  have hnμ : 0 ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) σ₀ n‖ :=
    tsum_nonneg fun n => norm_nonneg _
  refine ⟨∑' n, ‖LSeries.term (1 : ℕ → ℂ) σ₀ n‖
      + ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) σ₀ n‖,
    fun s hs => ⟨?_, ?_⟩⟩
  · have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
    rw [← LSeries_one_eq_riemannZeta hs1]
    linarith [norm_LSeries_le_of_re h1 hs]
  · have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
    have hinv : (riemannZeta s)⁻¹ = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
      rw [← LSeries_one_eq_riemannZeta hs1]
      exact inv_eq_of_mul_eq_one_right (LSeries_one_mul_Lseries_moebius hs1)
    rw [hinv]
    linarith [norm_LSeries_le_of_re hμ hs]

/-- Para `Re s ≥ σ₀ > 1`, `‖ζ'(s)/ζ(s)‖` está acotado. -/
theorem logDeriv_zeta_bound {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ B : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ B := by
  have hre : 1 < (σ₀ : ℂ).re := by simpa using hσ₀
  have hsum : Summable (fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ₀ n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ₀ n‖,
    fun s hs => ?_⟩
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have h' : deriv riemannZeta s / riemannZeta s
      = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [h, neg_div, neg_neg]
  rw [h', norm_neg]
  exact norm_LSeries_le_of_re hsum hs

/-! ### Una desigualdad sublineal -/

theorem rpow_le_lin {A θ l : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y → A * y ^ θ ≤ l * y + C := by
  rcases hA.eq_or_lt with hA0 | hApos
  · refine ⟨0, le_rfl, fun y hy => ?_⟩
    rw [← hA0, zero_mul, add_zero]
    positivity
  have h1θ : 1 - θ ≠ 0 := by linarith
  set Y : ℝ := (A / l) ^ (1 / (1 - θ)) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos (div_pos hApos hl) _
  have hC : 0 ≤ A * Y ^ θ := by positivity
  refine ⟨A * Y ^ θ, hC, fun y hy => ?_⟩
  rcases le_or_gt y Y with hyY | hyY
  · have h : y ^ θ ≤ Y ^ θ := Real.rpow_le_rpow hy hyY hθ0
    have := mul_le_mul_of_nonneg_left h hA
    nlinarith [mul_nonneg hl.le hy]
  · have hy0 : 0 < y := lt_trans hY0 hyY
    have h1 : y ^ (θ - 1) ≤ Y ^ (θ - 1) := Real.rpow_le_rpow_of_nonpos hY0 hyY.le (by linarith)
    have h2 : Y ^ (θ - 1) = l / A := by
      rw [hY, ← Real.rpow_mul (div_pos hApos hl).le,
        show 1 / (1 - θ) * (θ - 1) = -1 by field_simp; ring, Real.rpow_neg_one, inv_div]
    have h3 : y ^ θ = y ^ (θ - 1) * y := by
      rw [Real.rpow_sub_one hy0.ne', div_mul_cancel₀ _ hy0.ne']
    calc A * y ^ θ = A * y ^ (θ - 1) * y := by rw [h3]; ring
      _ ≤ A * Y ^ (θ - 1) * y := by gcongr
      _ = l * y := by rw [h2]; field_simp
      _ ≤ l * y + A * Y ^ θ := le_add_of_nonneg_right hC

/-! ### Cota de `1/ζ` bajo la hipótesis de Riemann -/

theorem norm_log_le {w : ℂ} (hw : w ≠ 0) {S : ℝ} (hS1 : ‖w‖ ≤ S) (hS2 : ‖w⁻¹‖ ≤ S) :
    ‖Complex.log w‖ ≤ Real.log S + Real.pi := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hl1 : Real.log ‖w‖ ≤ Real.log S := Real.log_le_log hpos hS1
  have hl2 : -Real.log S ≤ Real.log ‖w‖ := by
    have h := Real.log_le_log (by rw [norm_inv]; positivity) hS2
    rw [norm_inv, Real.log_inv] at h
    linarith
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ Real.log S + Real.pi := add_le_add (abs_le.mpr ⟨hl2, hl1⟩) (Complex.abs_arg_le_pi w)

set_option maxHeartbeats 1600000 in
/-- **Bajo RH, `|1/ζ(s)| ≪ |t|^η` en `Re s ≥ 1/2 + δ`, `|t| ≥ 3`** (Titchmarsh, §14.2):
logaritmo holomorfo de `ζ` en el disco de centro `2 + it`, Borel–Carathéodory y tres círculos. -/
theorem inv_zeta_bound (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → 3 ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ η := by
  obtain ⟨S, hS⟩ := zeta_bounds_of_one_lt (show (1 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨B, hB⟩ := logDeriv_zeta_bound (show (1 : ℝ) < 3 / 2 by norm_num)
  have hS1 : 1 ≤ S := by
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    obtain ⟨ha, hb⟩ := hS 2 (by norm_num)
    have hne := riemannZeta_ne_zero_of_one_lt_re h2
    have hprod : ‖riemannZeta 2‖ * ‖(riemannZeta 2)⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hne, norm_one]
    nlinarith [norm_nonneg (riemannZeta 2), norm_nonneg (riemannZeta 2)⁻¹]
  set K : ℝ := Real.log S + Real.pi with hKdef
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg hS1
    have := Real.pi_pos
    linarith
  set B' : ℝ := max B 0 with hB'
  set r₂ : ℝ := 3 / 2 - δ / 2 with hr₂
  set R : ℝ := 3 / 2 - δ / 4 with hR
  set A₀ : ℝ := K + B' / 2 + 1 with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    have : 0 ≤ B' := le_max_right _ _
    linarith
  set θ₀ : ℝ := (Real.log (3 / 2 - δ) - Real.log (1 / 2)) / (Real.log r₂ - Real.log (1 / 2))
    with hθ₀
  have hden : 0 < Real.log r₂ - Real.log (1 / 2) := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) (show (1 : ℝ) / 2 < r₂ by linarith)
    linarith
  have hθ₀0 : 0 ≤ θ₀ := by
    apply div_nonneg _ hden.le
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (show (1 : ℝ) / 2 ≤ 3 / 2 - δ by linarith)
    linarith
  have hθ₀1 : θ₀ < 1 := by
    rw [div_lt_one hden]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < 3 / 2 - δ) (show 3 / 2 - δ < r₂ by linarith)
    linarith
  obtain ⟨C₀, hC₀0, hC₀⟩ := rpow_le_lin (by linarith : (0 : ℝ) ≤ A₀) hθ₀0 hθ₀1
    (show 0 < η * δ / 16 by positivity)
  set c₃ : ℝ := η * Real.log 9 + η * (12 * K) / 16 + η * δ / 16 + C₀ with hc₃
  refine ⟨S + Real.exp c₃, fun s hsre hsim => ?_⟩
  set t := s.im with ht
  have ht0 : 0 < |t| := by linarith
  have htη : 1 ≤ |t| ^ η := Real.one_le_rpow (by linarith) hη.le
  have hS0 : 0 ≤ S := by linarith
  rcases le_or_gt (3 / 2) s.re with hbig | hsmall
  · -- región `Re s ≥ 3/2`
    calc ‖(riemannZeta s)⁻¹‖ ≤ S := (hS s hbig).2
      _ ≤ (S + Real.exp c₃) * 1 := by have := Real.exp_pos c₃; linarith
      _ ≤ (S + Real.exp c₃) * |t| ^ η := by gcongr
  -- disco de centro `s₀ = 2 + it`
  set s₀ : ℂ := 2 + (t : ℂ) * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball s₀ R, 1 / 2 + δ / 4 < z.re ∧ 3 / 2 < |z.im| ∧ z.re < 4 ∧ |z.im| < |t| + 2 := by
    intro z hz
    have hn : ‖z - s₀‖ < R := by rw [← dist_eq_norm]; exact hz
    have hre := Complex.abs_re_le_norm (z - s₀)
    have him := Complex.abs_im_le_norm (z - s₀)
    rw [sub_re, hs₀re] at hre
    rw [sub_im, hs₀im] at him
    have h1 := abs_lt.mp (lt_of_le_of_lt hre hn)
    have h2 : |z.im - t| < R := lt_of_le_of_lt him hn
    refine ⟨by linarith [h1.1], ?_, by linarith [h1.2], ?_⟩
    · linarith [abs_sub_comm z.im t, abs_sub_abs_le_abs_sub t z.im]
    · linarith [abs_sub_abs_le_abs_sub z.im t]
  have hne1 : ∀ z ∈ ball s₀ R, z ≠ 1 := by
    intro z hz h1
    have := (hball z hz).2.1
    rw [h1] at this
    norm_num at this
  have hζne : ∀ z ∈ ball s₀ R, riemannZeta z ≠ 0 := by
    intro z hz h0
    obtain ⟨hre, him, -, -⟩ := hball z hz
    have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have : z.im = 0 := by rw [hn]; simp
      rw [this, abs_zero] at him
      linarith
    have := hRH z h0 htriv (hne1 z hz)
    linarith
  have hζdiff : DifferentiableOn ℂ riemannZeta (ball s₀ R) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  obtain ⟨L, hLc, hLd, hLe⟩ := exists_log_ball hRpos hζdiff hζne
  have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun z hz =>
    (hLd z hz).differentiableAt.differentiableWithinAt
  -- cota de `log ζ(s₀)`
  have hLs₀ : ‖L s₀‖ ≤ K := by
    rw [hLc]
    have h := hS s₀ (by rw [hs₀re]; norm_num)
    exact norm_log_le (riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)) h.1 h.2
  -- `Re L ≤ M` en el disco grande
  set M : ℝ := Real.log (9 * |t|) with hM
  have hMpos : 0 < M := Real.log_pos (by linarith)
  have hLre : ∀ z ∈ ball s₀ R, (L z).re ≤ M := by
    intro z hz
    obtain ⟨hre, him, hre4, him2⟩ := hball z hz
    have hz0 : 0 < z.re := by linarith
    have hnz : ‖z‖ ≤ |t| + 6 := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz0] at this
      linarith
    have hz1 : 3 / 2 ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1)
      rw [sub_im, one_im, sub_zero] at this
      linarith
    have hζ := norm_riemannZeta_le hz0 (hne1 z hz)
    have hq1 : ‖z / (z - 1)‖ ≤ ‖z‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) (by linarith)
    have hq2 : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      rw [div_le_iff₀ hz0]
      nlinarith [norm_nonneg z]
    have hζb : ‖riemannZeta z‖ ≤ 9 * |t| := by linarith
    have hpos : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr (hζne z hz)
    have hreL : (L z).re = Real.log ‖riemannZeta z‖ := by
      rw [← hLe z hz, Complex.norm_exp, Real.log_exp]
    rw [hreL]
    exact Real.log_le_log hpos hζb
  -- Borel–Carathéodory: `‖L‖ ≤ b` en la circunferencia de radio `r₂`
  set b : ℝ := (16 * M + 12 * K) / δ + 1 with hb
  have hb1 : 1 ≤ b := by
    have : 0 ≤ (16 * M + 12 * K) / δ := by positivity
    linarith
  have hbound2 : ∀ z, ‖z - s₀‖ = r₂ → ‖L z‖ ≤ b := by
    intro z hz
    set f : ℂ → ℂ := fun w => L (s₀ + w) with hf
    have hfd : DifferentiableOn ℂ f (ball 0 R) := by
      intro w hw
      have hw' : s₀ + w ∈ ball s₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]
        exact hw
      exact ((hLd _ hw').differentiableAt.comp w
        ((differentiableAt_const s₀).add differentiableAt_id)).differentiableWithinAt
    have hfM : Set.MapsTo f (ball 0 R) {z | z.re ≤ M} := by
      intro w hw
      have hw' : s₀ + w ∈ ball s₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]
        exact hw
      exact hLre _ hw'
    have hwR : z - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, hz]
      linarith
    have hBC := Complex.borelCaratheodory hMpos hfd hfM hRpos hwR
    have hfz : f (z - s₀) = L z := by simp only [hf, add_sub_cancel]
    have hf0 : f 0 = L s₀ := by simp only [hf, add_zero]
    rw [hfz, hf0, hz, show R - r₂ = δ / 4 by rw [hR, hr₂]; ring] at hBC
    have hr₂2 : r₂ ≤ 2 := by linarith
    have hRr : R + r₂ ≤ 3 := by linarith
    have hnum : 2 * M * r₂ + ‖L s₀‖ * (R + r₂) ≤ 4 * M + 3 * K := by
      have e1 : M * r₂ ≤ M * 2 := mul_le_mul_of_nonneg_left hr₂2 hMpos.le
      have e2 : ‖L s₀‖ * (R + r₂) ≤ K * 3 :=
        mul_le_mul hLs₀ hRr (by linarith) hK0
      linarith
    have hkey : 2 * M * r₂ / (δ / 4) + ‖L s₀‖ * (R + r₂) / (δ / 4) ≤ (16 * M + 12 * K) / δ := by
      rw [← add_div, div_le_div_iff₀ (by positivity) hδ]
      nlinarith [mul_le_mul_of_nonneg_right hnum hδ.le]
    linarith
  -- cota en la circunferencia interior de radio `1/2`
  have hbound1 : ∀ z, ‖z - s₀‖ = 1 / 2 → ‖L z‖ ≤ A₀ := by
    intro z hz
    have hsub : closedBall s₀ (1 / 2) ⊆ ball s₀ R := closedBall_subset_ball (by linarith)
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := L) (f' := fun x => deriv riemannZeta x / riemannZeta x) (C := B')
      (fun x hx => (hLd x (hsub hx)).hasDerivWithinAt)
      (fun x hx => by
        refine le_trans (hB x ?_) (le_max_left _ _)
        have h1 : ‖x - s₀‖ ≤ 1 / 2 := by rw [← dist_eq_norm]; exact hx
        have h2 := Complex.abs_re_le_norm (x - s₀)
        rw [sub_re, hs₀re] at h2
        have := (abs_le.mp (le_trans h2 h1)).1
        linarith)
      (convex_closedBall s₀ (1 / 2)) (mem_closedBall_self (by norm_num))
      (show z ∈ closedBall s₀ (1 / 2) by rw [mem_closedBall, dist_eq_norm, hz])
    rw [hz] at hmv
    have := norm_sub_norm_le (L z) (L s₀)
    linarith
  -- tres círculos en `s`
  have hss₀ : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hs₀, ht]
  have hdist : ‖s - s₀‖ = 2 - s.re := by
    rw [hss₀, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hz1 : 1 / 2 ≤ ‖s - s₀‖ := by rw [hdist]; linarith
  have hz2 : ‖s - s₀‖ ≤ r₂ := by rw [hdist]; linarith
  have h3 := three_circles (by norm_num : (0 : ℝ) < 1 / 2) (show (1 : ℝ) / 2 < r₂ by linarith)
    (show r₂ < R by linarith) hLdiff hbound1 hbound2 hz1 hz2
  set θ : ℝ := (Real.log ‖s - s₀‖ - Real.log (1 / 2)) / (Real.log r₂ - Real.log (1 / 2)) with hθ
  have hθ0 : 0 ≤ θ := by
    apply div_nonneg _ hden.le
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hz1
    linarith
  have hθθ₀ : θ ≤ θ₀ := by
    apply div_le_div_of_nonneg_right _ hden.le
    have := Real.log_le_log (by linarith : (0 : ℝ) < ‖s - s₀‖)
      (show ‖s - s₀‖ ≤ 3 / 2 - δ by rw [hdist]; linarith)
    linarith
  have hLs : ‖L s‖ ≤ A₀ * b ^ θ₀ := by
    calc ‖L s‖ ≤ A₀ ^ (1 - θ) * b ^ θ := h3
      _ ≤ A₀ ^ (1 : ℝ) * b ^ θ₀ := by
          gcongr
          linarith
      _ = A₀ * b ^ θ₀ := by rw [Real.rpow_one]
  have hlin := hC₀ b (by linarith)
  have hbexp : η * δ / 16 * b
      = η * Real.log |t| + (η * Real.log 9 + η * (12 * K) / 16 + η * δ / 16) := by
    rw [hb, hM, Real.log_mul (by norm_num) ht0.ne']
    field_simp
    ring
  have hζs : riemannZeta s = Complex.exp (L s) := (hLe s (by
    rw [mem_ball, dist_eq_norm]; linarith)).symm
  have hinv : ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (‖L s‖) := by
    rw [hζs, ← Complex.exp_neg, Complex.norm_exp, neg_re]
    exact Real.exp_le_exp.mpr (by linarith [neg_le_abs (L s).re, Complex.abs_re_le_norm (L s)])
  have htpow : |t| ^ η = Real.exp (η * Real.log |t|) := by
    rw [Real.rpow_def_of_pos ht0, mul_comm]
  calc ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (‖L s‖) := hinv
    _ ≤ Real.exp (η * Real.log |t| + c₃) := by
        apply Real.exp_le_exp.mpr
        rw [hc₃]
        linarith
    _ = Real.exp c₃ * |t| ^ η := by rw [htpow, ← Real.exp_add]; ring_nf
    _ ≤ (S + Real.exp c₃) * |t| ^ η := by
        have := Real.rpow_nonneg ht0.le η
        nlinarith

end AMate
