import AMateEnergia.ZetaRectaCero

/-!
# Cota de `ζ` en la recta crítica

Tres rectas de Hadamard aplicadas a `f(s) = (s − 1) ζ(s) e^{(s − s₀)²}` en la banda
`0 ≤ Re s ≤ 1`, con `s₀ = 1/2 + i t₀`.

* `riemannZeta₁_strip_bound`: cota cruda `‖(s − 1) ζ(s)‖ ≤ P (1 + |t|)² e^{2|t|}` en la banda;
  da la acotación de `f` que pide el teorema de las tres rectas.
* `gauss_sup`, `crude_gauss`: el factor gaussiano absorbe el crecimiento en los bordes.
* `norm_sq_riemannZeta₁_critica`: `‖(s₀ − 1) ζ(s₀)‖² ≤ K (1 + |t₀|)^{5/2} (2 + log(2 + |t₀|))²`,
  con las cotas de `ZetaCotas` en `Re s = 1` y de `ZetaRectaCero` en `Re s = 0`.
* `zeta_critica_un_tercio`: `|ζ(1/2 + ix)| ≤ C (1 + |x|)^{1/3}`.

La convexidad da el exponente `1/4` más un logaritmo; el `1/3` sale de absorber el
logaritmo con `log y ≤ 12 y^{1/12}`, y basta para el teorema principal.
-/

open Complex MeasureTheory Set

namespace AMate

/-- `‖Γ(s)‖ ≤ Γ(Re s)` para `Re s > 0`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

/-- `Γ` real está acotada en `[1/2, 1]`. -/
theorem Gamma_bdd_half_one : ∃ G : ℝ, ∀ x ∈ Icc (1 / 2 : ℝ) 1, Real.Gamma x ≤ G := by
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    apply (Real.differentiableAt_Gamma _).continuousAt.continuousWithinAt
    intro m hm
    have h1 : (0 : ℝ) < x := by linarith [hx.1]
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨G, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hG x hx)⟩

/-- `‖cos w‖ ≤ exp |Im w|`. -/
theorem norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have hn : ‖(2 : ℂ) * Complex.cos w‖ ≤ 2 * Real.exp |w.im| := by
    rw [Complex.two_cos]
    calc ‖cexp (w * I) + cexp (-w * I)‖ ≤ ‖cexp (w * I)‖ + ‖cexp (-w * I)‖ := norm_add_le _ _
      _ = Real.exp (w * I).re + Real.exp (-w * I).re := by rw [Complex.norm_exp, Complex.norm_exp]
      _ ≤ Real.exp |w.im| + Real.exp |w.im| := by
          gcongr
          · simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
            linarith [neg_abs_le w.im]
          · simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one, sub_neg_eq_add,
              zero_add]
            exact le_abs_self _
      _ = 2 * Real.exp |w.im| := by ring
  rw [norm_mul, Complex.norm_two] at hn
  linarith

/-- Cota cruda en la banda: `‖(s − 1) ζ(s)‖ ≤ P (1 + |t|)² e^{2|t|}` para `0 ≤ Re s ≤ 1`. -/
theorem riemannZeta₁_strip_bound : ∃ P : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
    ‖riemannZeta₁ z‖ ≤ P * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  obtain ⟨G, hG⟩ := Gamma_bdd_half_one
  refine ⟨|B| + 3 + 6 * |G|, fun z h0 h1 => ?_⟩
  set t := z.im with htdef
  have hat := abs_nonneg t
  have hE : 1 ≤ (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by
    have e1 : (1 : ℝ) ≤ (1 + |t|) ^ 2 := by nlinarith
    have e2 : (1 : ℝ) ≤ Real.exp (2 * |t|) := Real.one_le_exp (by positivity)
    nlinarith
  have hP : 0 ≤ |B| + 3 + 6 * |G| := by positivity
  have hzn : ‖z‖ ≤ 1 + |t| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |t| := by rw [abs_of_nonneg h0]; linarith
  have hz1n : ‖z - 1‖ ≤ 1 + |t| := by
    calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |t| := by
          simp only [sub_re, one_re, sub_im, one_im, sub_zero]
          rw [abs_of_nonpos (by linarith)]
          linarith
  by_cases ht1 : |t| ≤ 1
  · have hzb : z ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    calc ‖riemannZeta₁ z‖ ≤ B := hB z hzb
      _ ≤ |B| + 3 + 6 * |G| := by linarith [le_abs_self B, abs_nonneg G]
      _ = (|B| + 3 + 6 * |G|) * 1 := (mul_one _).symm
      _ ≤ (|B| + 3 + 6 * |G|) * ((1 + |t|) ^ 2 * Real.exp (2 * |t|)) :=
          mul_le_mul_of_nonneg_left hE hP
      _ = (|B| + 3 + 6 * |G|) * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by ring
  push Not at ht1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at htdef
    simp at htdef
    rw [htdef, abs_zero] at ht1
    linarith
  have hzpos : 1 < ‖z‖ := by
    calc (1 : ℝ) < |t| := ht1
      _ = |z.im| := rfl
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hsq : (1 + |t|) ≤ (1 + |t|) ^ 2 := by nlinarith
  have hexp1 : (1 : ℝ) ≤ Real.exp (2 * |t|) := Real.one_le_exp (by positivity)
  by_cases hre : 1 / 2 ≤ z.re
  · -- directo: ‖(z − 1) ζ(z)‖ ≤ ‖z‖ + 2 ‖z − 1‖ ‖z‖
    have hzre : 0 < z.re := by linarith
    have hζ := norm_riemannZeta_le hzre hz1
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hz1pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1'
    have hinv : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      rw [div_le_iff₀ hzre]
      nlinarith [norm_nonneg z]
    have hmain : ‖riemannZeta₁ z‖ ≤ ‖z‖ + 2 * ‖z - 1‖ * ‖z‖ := by
      rw [riemannZeta₁_eq z hz1, norm_mul]
      calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ ‖z - 1‖ * (‖z / (z - 1)‖ + ‖z‖ / z.re) := by gcongr
        _ = ‖z‖ + ‖z - 1‖ * (‖z‖ / z.re) := by
            rw [norm_div, mul_add, mul_div_cancel₀ _ hz1pos.ne']
        _ ≤ ‖z‖ + ‖z - 1‖ * (2 * ‖z‖) := by gcongr
        _ = ‖z‖ + 2 * ‖z - 1‖ * ‖z‖ := by ring
    calc ‖riemannZeta₁ z‖ ≤ ‖z‖ + 2 * ‖z - 1‖ * ‖z‖ := hmain
      _ ≤ (1 + |t|) + 2 * (1 + |t|) * (1 + |t|) := by gcongr
      _ ≤ 3 * (1 + |t|) ^ 2 := by nlinarith
      _ ≤ (|B| + 3 + 6 * |G|) * (1 + |t|) ^ 2 := by
          gcongr
          linarith [abs_nonneg B, abs_nonneg G]
      _ ≤ (|B| + 3 + 6 * |G|) * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by
          have : 0 ≤ (|B| + 3 + 6 * |G|) * (1 + |t|) ^ 2 := by positivity
          nlinarith
  · -- ecuación funcional con `s' = 1 − z`
    push Not at hre
    set s' : ℂ := 1 - z with hs'def
    have hs're : s'.re = 1 - z.re := by simp [hs'def]
    have hs'im : s'.im = -t := by simp [hs'def, htdef]
    have hs'pos : 0 < s'.re := by rw [hs're]; linarith
    have hs'n : ∀ n : ℕ, s' ≠ -n := by
      intro n h
      have := congrArg Complex.re h
      rw [hs're] at this
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hs'1 : s' ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      rw [hs'im] at this
      simp at this
      rw [this, abs_zero] at ht1
      linarith
    have hfe := riemannZeta_one_sub hs'n hs'1
    rw [show (1 : ℂ) - s' = z by simp [hs'def]] at hfe
    -- cotas de cada factor
    have h2pi : ‖(2 * (Real.pi : ℂ)) ^ (-s')‖ ≤ 1 := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · linarith [Real.pi_gt_three]
      · simp only [neg_re]
        linarith
    have hGam : ‖Gamma s'‖ ≤ |G| := by
      refine (norm_Gamma_le_Gamma_re hs'pos).trans ((hG _ ⟨?_, ?_⟩).trans (le_abs_self _))
      · rw [hs're]; linarith
      · rw [hs're]; linarith
    have hcos : ‖Complex.cos (Real.pi * s' / 2)‖ ≤ Real.exp (2 * |t|) := by
      refine (norm_cos_le_exp _).trans (Real.exp_le_exp.mpr ?_)
      have him : (Real.pi * s' / 2 : ℂ).im = Real.pi * s'.im / 2 := by
        simp [mul_im]
      rw [him, hs'im, abs_div, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_two]
      have := Real.pi_lt_four
      nlinarith
    have hs'n1 : ‖s' - 1‖ = ‖z‖ := by
      rw [show s' - 1 = -z by simp [hs'def], norm_neg]
    have hs'norm : ‖s'‖ ≤ 1 + |t| := by
      calc ‖s'‖ ≤ |s'.re| + |s'.im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1 + |t| := by
            rw [hs're, hs'im, abs_neg, abs_of_nonneg (by linarith)]
            linarith
    have hζ' : ‖riemannZeta s'‖ ≤ 3 * (1 + |t|) := by
      have h := norm_riemannZeta_le hs'pos hs'1
      have hinv : ‖s'‖ / s'.re ≤ 2 * ‖s'‖ := by
        rw [div_le_iff₀ hs'pos]
        rw [hs're]
        nlinarith [norm_nonneg s']
      have hq : ‖s' / (s' - 1)‖ ≤ ‖s'‖ := by
        rw [norm_div, hs'n1, div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg s']
      linarith
    have hzeta : ‖riemannZeta z‖ ≤ 2 * |G| * Real.exp (2 * |t|) * (3 * (1 + |t|)) := by
      rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_two]
      calc 2 * ‖(2 * (Real.pi : ℂ)) ^ (-s')‖ * ‖Gamma s'‖ * ‖Complex.cos (Real.pi * s' / 2)‖
            * ‖riemannZeta s'‖
          ≤ 2 * 1 * |G| * Real.exp (2 * |t|) * (3 * (1 + |t|)) := by gcongr
        _ = 2 * |G| * Real.exp (2 * |t|) * (3 * (1 + |t|)) := by ring
    calc ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by rw [riemannZeta₁_eq z hz1, norm_mul]
      _ ≤ (1 + |t|) * (2 * |G| * Real.exp (2 * |t|) * (3 * (1 + |t|))) := by gcongr
      _ = 6 * |G| * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by ring
      _ ≤ (|B| + 3 + 6 * |G|) * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by
          gcongr
          linarith [abs_nonneg B]

/-! ### Supremos con peso gaussiano -/

theorem one_add_abs_cube_le (u : ℝ) : (1 + |u|) ^ 3 ≤ 16 * Real.exp (u ^ 2) := by
  have he := Real.quadratic_le_exp_of_nonneg (sq_nonneg u)
  have ha := abs_nonneg u
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rw [hu2] at he ⊢
  nlinarith [sq_nonneg (|u| - 1), sq_nonneg (|u| ^ 2 - |u|), sq_nonneg |u|]

theorem abs_le_add_abs_sub (t t₀ : ℝ) : |t| ≤ |t₀| + |t - t₀| := by
  calc |t| = |t₀ + (t - t₀)| := by ring_nf
    _ ≤ |t₀| + |t - t₀| := abs_add_le _ _

/-- `(1+|t|)^a (2 + log(2+|t|)) e^{−(t−t₀)²} ≤ 16 (1+|t₀|)^a (2 + log(2+|t₀|))` para `0 ≤ a ≤ 2`. -/
theorem gauss_sup (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (t t₀ : ℝ) :
    (1 + |t|) ^ a * (2 + Real.log (2 + |t|)) * Real.exp (-(t - t₀) ^ 2)
      ≤ 16 * ((1 + |t₀|) ^ a * (2 + Real.log (2 + |t₀|))) := by
  have hau := abs_nonneg (t - t₀)
  have hat0 := abs_nonneg t₀
  have htri := abs_le_add_abs_sub t t₀
  have hb1 : 1 + |t| ≤ (1 + |t₀|) * (1 + |t - t₀|) := by nlinarith
  have hL0 : 0 ≤ Real.log (2 + |t₀|) := Real.log_nonneg (by linarith)
  have hb2 : 2 + Real.log (2 + |t|) ≤ (2 + Real.log (2 + |t₀|)) * (1 + |t - t₀|) := by
    have h1 : 2 + |t| ≤ (2 + |t₀|) * (1 + |t - t₀|) := by nlinarith
    have h2 : Real.log (2 + |t|) ≤ Real.log (2 + |t₀|) + Real.log (1 + |t - t₀|) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) h1
    have h3 : Real.log (1 + |t - t₀|) ≤ |t - t₀| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + |t - t₀| by positivity)
      linarith
    nlinarith
  have hp1 : (1 + |t|) ^ a ≤ (1 + |t₀|) ^ a * (1 + |t - t₀|) ^ a := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hb1 ha0
  have hp2 : (1 + |t - t₀|) ^ a * (1 + |t - t₀|) ≤ (1 + |t - t₀|) ^ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + |t - t₀| by linarith) ha2
    rw [Real.rpow_two] at h
    have hnn : (0 : ℝ) ≤ 1 + |t - t₀| := by positivity
    calc (1 + |t - t₀|) ^ a * (1 + |t - t₀|) ≤ (1 + |t - t₀|) ^ 2 * (1 + |t - t₀|) :=
          mul_le_mul_of_nonneg_right h hnn
      _ = (1 + |t - t₀|) ^ 3 := by ring
  have hcube := one_add_abs_cube_le (t - t₀)
  have hexp : Real.exp ((t - t₀) ^ 2) * Real.exp (-(t - t₀) ^ 2) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE := Real.exp_pos (-(t - t₀) ^ 2)
  have hLt : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hLt' : 0 ≤ 2 + Real.log (2 + |t|) := by linarith
  calc (1 + |t|) ^ a * (2 + Real.log (2 + |t|)) * Real.exp (-(t - t₀) ^ 2)
      ≤ ((1 + |t₀|) ^ a * (1 + |t - t₀|) ^ a) * ((2 + Real.log (2 + |t₀|)) * (1 + |t - t₀|))
        * Real.exp (-(t - t₀) ^ 2) := by gcongr
    _ = ((1 + |t₀|) ^ a * (2 + Real.log (2 + |t₀|)))
        * (((1 + |t - t₀|) ^ a * (1 + |t - t₀|)) * Real.exp (-(t - t₀) ^ 2)) := by ring
    _ ≤ ((1 + |t₀|) ^ a * (2 + Real.log (2 + |t₀|)))
        * ((1 + |t - t₀|) ^ 3 * Real.exp (-(t - t₀) ^ 2)) := by gcongr
    _ ≤ ((1 + |t₀|) ^ a * (2 + Real.log (2 + |t₀|)))
        * (16 * Real.exp ((t - t₀) ^ 2) * Real.exp (-(t - t₀) ^ 2)) := by gcongr
    _ = 16 * ((1 + |t₀|) ^ a * (2 + Real.log (2 + |t₀|))) := by
        rw [mul_assoc 16, hexp]
        ring

/-- Versión cruda para la acotación en la banda. -/
theorem crude_gauss (t t₀ : ℝ) :
    (1 + |t|) ^ 2 * Real.exp (2 * |t|) * Real.exp (-(t - t₀) ^ 2)
      ≤ (1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4 := by
  have hau := abs_nonneg (t - t₀)
  have hat0 := abs_nonneg t₀
  have htri := abs_le_add_abs_sub t t₀
  have h1 : 1 + |t| ≤ (1 + |t₀|) * Real.exp |t - t₀| := by
    have := Real.add_one_le_exp |t - t₀|
    nlinarith
  have h1sq : (1 + |t|) ^ 2 ≤ (1 + |t₀|) ^ 2 * Real.exp (2 * |t - t₀|) := by
    have hnn : 0 ≤ 1 + |t| := by positivity
    calc (1 + |t|) ^ 2 ≤ ((1 + |t₀|) * Real.exp |t - t₀|) ^ 2 := by gcongr
      _ = (1 + |t₀|) ^ 2 * Real.exp (2 * |t - t₀|) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
  have h2 : Real.exp (2 * |t|) ≤ Real.exp (2 * |t₀|) * Real.exp (2 * |t - t₀|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (2 * |t - t₀|) * Real.exp (2 * |t - t₀|) * Real.exp (-(t - t₀) ^ 2)
      ≤ Real.exp 4 := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (t - t₀) ^ 2 = |t - t₀| ^ 2 := (sq_abs _).symm
    nlinarith [sq_nonneg (|t - t₀| - 2)]
  calc (1 + |t|) ^ 2 * Real.exp (2 * |t|) * Real.exp (-(t - t₀) ^ 2)
      ≤ ((1 + |t₀|) ^ 2 * Real.exp (2 * |t - t₀|))
        * (Real.exp (2 * |t₀|) * Real.exp (2 * |t - t₀|)) * Real.exp (-(t - t₀) ^ 2) := by
        gcongr
    _ = ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|))
        * (Real.exp (2 * |t - t₀|) * Real.exp (2 * |t - t₀|) * Real.exp (-(t - t₀) ^ 2)) := by
        ring
    _ ≤ ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|)) * Real.exp 4 := by gcongr
    _ = (1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4 := by ring

theorem norm_exp_sq (z : ℂ) (t₀ : ℝ) :
    ‖cexp ((z - (1 / 2 + t₀ * I)) ^ 2)‖ = Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re]

/-! ### Tres rectas de Hadamard -/

/-- `‖(s₀ − 1) ζ(s₀)‖² ≤ K (1 + |t₀|)^{5/2} (2 + log(2 + |t₀|))²` en `s₀ = 1/2 + i t₀`. -/
theorem norm_sq_riemannZeta₁_critica : ∃ K : ℝ, 0 ≤ K ∧ ∀ t₀ : ℝ,
    ‖riemannZeta₁ (1 / 2 + t₀ * I)‖ ^ 2
      ≤ K * (1 + |t₀|) ^ (5 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := norm_riemannZeta₁_mul_I_le
  obtain ⟨P, hP⟩ := riemannZeta₁_strip_bound
  refine ⟨Real.exp (1 / 2) * 256 * max C₀ 0,
    mul_nonneg (by positivity) (le_max_right _ _), fun t₀ => ?_⟩
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have hL0 : 0 ≤ Real.log (2 + |t₀|) := Real.log_nonneg (by linarith [abs_nonneg t₀])
  have hpos0 : (0 : ℝ) < 1 + |t₀| := by positivity
  have hf : Differentiable ℂ (fun z => riemannZeta₁ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2)) :=
    differentiable_riemannZeta₁.mul
      (((differentiable_id.sub_const (1 / 2 + t₀ * I)).pow 2).cexp)
  have hnf : ∀ z, ‖riemannZeta₁ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2)‖
      = ‖riemannZeta₁ z‖ * Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2) := by
    intro z
    rw [norm_mul, norm_exp_sq]
  have ha : ∀ z ∈ re ⁻¹' {(0 : ℝ)},
      ‖riemannZeta₁ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2)‖
        ≤ Real.exp (1 / 4) * max C₀ 0
          * (16 * ((1 + |t₀|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have hzI : z = (z.im : ℂ) * I := Complex.ext (by simp [hz0]) (by simp)
    have hζ := hC₀ z.im
    rw [← hzI] at hζ
    rw [hnf, hz0, show ((0 : ℝ) - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 = 1 / 4 + (-(z.im - t₀) ^ 2) by ring,
      Real.exp_add]
    have hg := gauss_sup (3 / 2) (by norm_num) (by norm_num) z.im t₀
    have hLz : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    have hX : 0 ≤ (1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|)) := by positivity
    have hζ' : ‖riemannZeta₁ z‖
        ≤ max C₀ 0 * ((1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|))) := by
      calc ‖riemannZeta₁ z‖ ≤ C₀ * (1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|)) := hζ
        _ = C₀ * ((1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|))) := by ring
        _ ≤ max C₀ 0 * ((1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    calc ‖riemannZeta₁ z‖ * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2))
        ≤ max C₀ 0 * ((1 + |z.im|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |z.im|)))
          * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) :=
          mul_le_mul_of_nonneg_right hζ' (by positivity)
      _ = Real.exp (1 / 4) * max C₀ 0 * ((1 + |z.im|) ^ (3 / 2 : ℝ)
          * (2 + Real.log (2 + |z.im|)) * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ Real.exp (1 / 4) * max C₀ 0
          * (16 * ((1 + |t₀|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) :=
          mul_le_mul_of_nonneg_left hg (mul_nonneg (Real.exp_pos _).le hC0)
  have hb : ∀ z ∈ re ⁻¹' {(1 : ℝ)},
      ‖riemannZeta₁ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2)‖
        ≤ Real.exp (1 / 4) * (16 * ((1 + |t₀|) ^ (1 : ℝ) * (2 + Real.log (2 + |t₀|)))) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have hz1I : z = 1 + (z.im : ℂ) * I := Complex.ext (by simp [hz1]) (by simp)
    have hζ := norm_riemannZeta₁_one_add_le z.im
    rw [← hz1I] at hζ
    rw [hnf, hz1, show ((1 : ℝ) - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 = 1 / 4 + (-(z.im - t₀) ^ 2) by ring,
      Real.exp_add]
    have hg := gauss_sup 1 (by norm_num) (by norm_num) z.im t₀
    rw [Real.rpow_one, Real.rpow_one] at hg
    rw [Real.rpow_one]
    calc ‖riemannZeta₁ z‖ * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2))
        ≤ (1 + |z.im|) * (2 + Real.log (2 + |z.im|))
          * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) :=
          mul_le_mul_of_nonneg_right hζ (by positivity)
      _ = Real.exp (1 / 4) * ((1 + |z.im|) * (2 + Real.log (2 + |z.im|))
          * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ Real.exp (1 / 4) * (16 * ((1 + |t₀|) * (2 + Real.log (2 + |t₀|)))) :=
          mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
  have hBdd : BddAbove ((norm ∘ fun z => riemannZeta₁ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2))
      '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨|P| * Real.exp (1 / 4) * ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4), ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
    have hPz := hP z hz'.1 hz'.2
    simp only [Function.comp]
    rw [hnf]
    have hsig : (z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 ≤ 1 / 4 + (-(z.im - t₀) ^ 2) := by
      nlinarith [hz'.1, hz'.2]
    have hexp_le : Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2)
        ≤ Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hsig
    have hcg := crude_gauss z.im t₀
    have hPabs : ‖riemannZeta₁ z‖ ≤ |P| * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|) := by
      have : P * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|)
          ≤ |P| * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|) := by
        gcongr
        exact le_abs_self P
      linarith
    calc ‖riemannZeta₁ z‖ * Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2)
        ≤ (|P| * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|))
          * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) := by gcongr
      _ = |P| * Real.exp (1 / 4) * ((1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|)
          * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ |P| * Real.exp (1 / 4) * ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4) := by
          gcongr
  have hre : (1 / 2 + (t₀ : ℂ) * I).re = 1 / 2 := by simp
  have hmem : (1 / 2 + (t₀ : ℂ) * I) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    show (1 / 2 + (t₀ : ℂ) * I).re ∈ Icc (0 : ℝ) 1
    rw [hre]
    constructor <;> norm_num
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' zero_lt_one hmem
    hf.diffContOnCl hBdd ha hb
  rw [hre, show ((1 : ℝ) / 2 - 0) / (1 - 0) = 1 / 2 by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h3
  have hfs : riemannZeta₁ (1 / 2 + t₀ * I) * cexp ((1 / 2 + t₀ * I - (1 / 2 + t₀ * I)) ^ 2)
      = riemannZeta₁ (1 / 2 + t₀ * I) := by simp
  rw [hfs] at h3
  set a := Real.exp (1 / 4) * max C₀ 0
    * (16 * ((1 + |t₀|) ^ (3 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) with hadef
  set b := Real.exp (1 / 4) * (16 * ((1 + |t₀|) ^ (1 : ℝ) * (2 + Real.log (2 + |t₀|)))) with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hsq : (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ 2 = a * b := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ha0, Real.sq_sqrt hb0]
  have hab : a * b = Real.exp (1 / 2) * 256 * max C₀ 0 * (1 + |t₀|) ^ (5 / 2 : ℝ)
      * (2 + Real.log (2 + |t₀|)) ^ 2 := by
    rw [hadef, hbdef, Real.rpow_one, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
      Real.rpow_add hpos0, Real.rpow_one,
      show Real.exp (1 / 2) = Real.exp (1 / 4) * Real.exp (1 / 4) by
        rw [← Real.exp_add]; norm_num]
    ring
  calc ‖riemannZeta₁ (1 / 2 + t₀ * I)‖ ^ 2 ≤ (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = a * b := hsq
    _ = _ := hab

/-! ### Cota en la recta crítica con exponente `1/3` -/

theorem two_add_log_le (x : ℝ) (hx : 0 ≤ x) :
    2 + Real.log (2 + x) ≤ 26 * (1 + x) ^ (1 / 12 : ℝ) := by
  have h1 : Real.log (2 + x) ≤ (2 + x) ^ (1 / 12 : ℝ) / (1 / 12) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2 : (2 + x) ^ (1 / 12 : ℝ) ≤ (2 * (1 + x)) ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h3 : (2 * (1 + x)) ^ (1 / 12 : ℝ) = 2 ^ (1 / 12 : ℝ) * (1 + x) ^ (1 / 12 : ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h4 : (2 : ℝ) ^ (1 / 12 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 12 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h5 : (1 : ℝ) ≤ (1 + x) ^ (1 / 12 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hy := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + x by linarith) (1 / 12)
  have hlog : Real.log (2 + x) ≤ 24 * (1 + x) ^ (1 / 12 : ℝ) := by
    calc Real.log (2 + x) ≤ (2 + x) ^ (1 / 12 : ℝ) / (1 / 12) := h1
      _ = 12 * (2 + x) ^ (1 / 12 : ℝ) := by ring
      _ ≤ 12 * (2 ^ (1 / 12 : ℝ) * (1 + x) ^ (1 / 12 : ℝ)) := by rw [← h3]; gcongr
      _ ≤ 12 * (2 * (1 + x) ^ (1 / 12 : ℝ)) := by gcongr
      _ = 24 * (1 + x) ^ (1 / 12 : ℝ) := by ring
  linarith

/-- **Cota de `ζ` en la recta crítica**: `|ζ(1/2 + ix)| ≤ C (1 + |x|)^{1/3}`. -/
theorem zeta_critica_un_tercio : ∃ C : ℝ, ∀ x : ℝ,
    ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ≤ C * (1 + |x|) ^ (1 / 3 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := norm_sq_riemannZeta₁_critica
  refine ⟨Real.sqrt (9 * K * 676), fun x => ?_⟩
  have hax := abs_nonneg x
  have hpos : (0 : ℝ) < 1 + |x| := by positivity
  have hs₀1 : (1 / 2 + (x : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h1 := hK x
  rw [riemannZeta₁_eq _ hs₀1, norm_mul, mul_pow] at h1
  have hn : ‖(1 / 2 + (x : ℂ) * I) - 1‖ ^ 2 = 1 / 4 + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hlow : (1 + |x|) ^ 2 / 9 ≤ ‖(1 / 2 + (x : ℂ) * I) - 1‖ ^ 2 := by
    rw [hn, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
    nlinarith [sq_nonneg (|x| - 1 / 8)]
  have hrp : (1 + |x|) ^ (5 / 2 : ℝ) = (1 + |x|) ^ 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_two]
  have hζsq : ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2
      ≤ 9 * K * (1 + |x|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2 := by
    have hA : (1 + |x|) ^ 2 / 9 * ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2
        ≤ (1 + |x|) ^ 2 / 9
          * (9 * K * (1 + |x|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2) := by
      calc (1 + |x|) ^ 2 / 9 * ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2
          ≤ ‖(1 / 2 + (x : ℂ) * I) - 1‖ ^ 2 * ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hlow (sq_nonneg _)
        _ ≤ K * (1 + |x|) ^ (5 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2 := h1
        _ = (1 + |x|) ^ 2 / 9
            * (9 * K * (1 + |x|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2) := by
            rw [hrp]
            ring
    exact le_of_mul_le_mul_left hA (by positivity)
  have hL := two_add_log_le |x| hax
  have hLnn : 0 ≤ 2 + Real.log (2 + |x|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |x| by linarith)
    linarith
  have hy12 : ((1 + |x|) ^ (1 / 12 : ℝ)) ^ 2 = (1 + |x|) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hy3 : ((1 + |x|) ^ (1 / 3 : ℝ)) ^ 2 = (1 + |x|) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hy26 : (1 + |x|) ^ (1 / 2 : ℝ) * (1 + |x|) ^ (1 / 6 : ℝ) = (1 + |x|) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hL2 : (2 + Real.log (2 + |x|)) ^ 2 ≤ 676 * (1 + |x|) ^ (1 / 6 : ℝ) := by
    calc (2 + Real.log (2 + |x|)) ^ 2 ≤ (26 * (1 + |x|) ^ (1 / 12 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hLnn hL 2
      _ = 676 * (1 + |x|) ^ (1 / 6 : ℝ) := by rw [mul_pow, hy12]; norm_num
  have hfin : ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2
      ≤ (Real.sqrt (9 * K * 676) * (1 + |x|) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hy3]
    calc ‖riemannZeta (1 / 2 + (x : ℂ) * I)‖ ^ 2
        ≤ 9 * K * (1 + |x|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2 := hζsq
      _ ≤ 9 * K * (1 + |x|) ^ (1 / 2 : ℝ) * (676 * (1 + |x|) ^ (1 / 6 : ℝ)) := by gcongr
      _ = 9 * K * 676 * ((1 + |x|) ^ (1 / 2 : ℝ) * (1 + |x|) ^ (1 / 6 : ℝ)) := by ring
      _ = 9 * K * 676 * (1 + |x|) ^ (2 / 3 : ℝ) := by rw [hy26]
  have h5 := Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h5

end AMate
