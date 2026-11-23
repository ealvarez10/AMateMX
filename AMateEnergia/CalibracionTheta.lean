import AMateEnergia.PolinomioCritica
import AMateEnergia.Teorema

/-!
# Calibración general en `θ ∈ [1/2, 1)` y exponente límite exacto de la energía

Formalización completa de los resultados cuantitativos del Estado 45 para cualquier semiplano libre
de ceros `Re s > θ` (`1/2 ≤ θ < 1`) y de la fórmula límite incondicional `(1.1)`:

* `SinCerosDerecha θ`: ausencia de ceros de `ζ` en `Re s > θ`.
* `inv_and_logDeriv_zeta_bound_theta`, `Zinv_bound_theta`: cotas `O(|t|^η)` para `1/ζ(s)`,
  `ζ'(s)/ζ(s)` y `Zinv(s)` en `Re s ≥ θ + δ`.
* `balazard_saias_theta` (Estado 45, `(3.1)`): aproximación uniforme de `∑_{d≤n} μ(d) d^{−s}` por
  `Zinv(s)` en `Re s ≥ θ + δ`.
* `m_bound_theta`, `t_bound_theta`, `P_recta_critica_theta` (Estado 45, `(5.2)–(5.4)`):
  `‖P_Q(1/2 + ix)‖ ≤ C Q^{θ − 1/2 + δ} (1 + |x|)^η`.
* `energia_cota_theta`, `sin_ceros_iff_energia_theta` y `sin_ceros_iff_energia_cofinal_theta`
  (Estado 45, `(6.4)`): equivalencia exacta entre `SinCerosDerecha θ` y
  `E_Q ≤ C_ε Q^{2θ − 1 + ε}` (uniforme o cofinal).
* `Theta_zeta`, `Theta_zeta_eq_sSup_of_nonempty`, `Theta_zeta_eq_half_iff_rh` y
  `tendsto_log_energia_div_log` (Estado 45, `(1.1)`): incondicionalmente (sin asumir RH ni insumos
  externos),
  `lim_{Q → ∞} log(2 + E_Q) / log Q = 2 Θ_ζ − 1`.
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate

/-! ### Semiplano libre de ceros `Re s > θ` y `Zinv` holomorfa -/

/-- Ausencia de ceros de `ζ` en el semiplano abierto `Re s > θ`. -/
def SinCerosDerecha (θ : ℝ) : Prop :=
  ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0

theorem sinCerosDerecha_one : SinCerosDerecha 1 :=
  fun _ hρ => riemannZeta_ne_zero_of_one_le_re hρ.le

theorem sinCerosDerecha_half_iff_rh : SinCerosDerecha (1 / 2) ↔ RiemannHypothesis :=
  ⟨rh_of_no_zero_gt_half, fun hRH ρ hρ => by
    by_cases h1 : ρ = 1
    · subst h1; exact riemannZeta_one_ne_zero
    · intro h0
      have htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        have hre := congrArg Complex.re hn
        simp at hre
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have := hRH ρ h0 htriv h1
      linarith⟩

theorem riemannZeta₁_ne_zero_of_theta {θ : ℝ} (hZ : SinCerosDerecha θ) {z : ℂ} (hz : θ < z.re) :
    riemannZeta₁ z ≠ 0 := by
  by_cases h1 : z = 1
  · rw [h1, riemannZeta₁_one]; exact one_ne_zero
  · rw [riemannZeta₁_eq z h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (hZ z hz)

theorem differentiableOn_Zinv_theta {θ : ℝ} (hZ : SinCerosDerecha θ) :
    DifferentiableOn ℂ Zinv {z | θ < z.re} := by
  intro z hz
  exact ((differentiableAt_id.sub_const 1).div differentiable_riemannZeta₁.differentiableAt
    (riemannZeta₁_ne_zero_of_theta hZ hz)).differentiableWithinAt

/-! ### Cotas de `1/ζ` y `ζ'/ζ` en `Re s ≥ θ + δ` -/

set_option maxHeartbeats 1600000 in
/-- Bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`), en `Re s ≥ θ + δ` y `|Im s| ≥ 4` tanto `1/ζ(s)` como
`ζ'(s)/ζ(s)` quedan acotados por `C |Im s|^η`. -/
theorem inv_and_logDeriv_zeta_bound_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ)
    (hθδ : θ + δ < 1) (hη : 0 < η) (hZ : SinCerosDerecha θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, θ + δ ≤ s.re → 4 ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ η ∧
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * |s.im| ^ η := by
  obtain ⟨S, hS⟩ := zeta_bounds_of_one_lt (show (1 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨B, hB⟩ := logDeriv_zeta_bound (show (1 : ℝ) < 3 / 2 by norm_num)
  have hS1 : 1 ≤ S := by
    obtain ⟨ha, hb⟩ := hS 2 (by norm_num)
    have hne := riemannZeta_ne_zero_of_one_lt_re (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    have hprod : ‖riemannZeta 2‖ * ‖(riemannZeta 2)⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hne, norm_one]
    nlinarith [norm_nonneg (riemannZeta 2), norm_nonneg (riemannZeta 2)⁻¹]
  set K : ℝ := Real.log S + Real.pi with hKdef
  have hK0 : 0 ≤ K := by linarith [Real.log_nonneg hS1, Real.pi_pos]
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set δ₁ : ℝ := δ / 2 with hδ₁
  have hδ₁0 : 0 < δ₁ := half_pos hδ
  set r_int : ℝ := 2 - θ - δ₁ with hr_int
  set r₂ : ℝ := 2 - θ - δ₁ / 2 with hr₂
  set R : ℝ := 2 - θ - δ₁ / 4 with hR
  have hr_int_gt : 1 / 2 < r_int := by simp only [r_int, δ₁]; linarith
  have hr₂_gt : r_int < r₂ := by simp only [r_int, r₂]; linarith
  have hR_gt : r₂ < R := by simp only [r₂, R]; linarith
  have hR_lt32 : R < 3 / 2 := by simp only [R]; linarith
  set A₀ : ℝ := K + B' / 2 + 1 with hA₀
  have hA₀1 : 1 ≤ A₀ := by simp only [A₀]; linarith
  set θ₀ : ℝ := (Real.log r_int - Real.log (1 / 2)) / (Real.log r₂ - Real.log (1 / 2)) with hθ₀
  have hden : 0 < Real.log r₂ - Real.log (1 / 2) :=
    sub_pos.mpr (Real.log_lt_log (by norm_num) (lt_trans hr_int_gt hr₂_gt))
  have hθ₀0 : 0 ≤ θ₀ :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log (by norm_num) hr_int_gt.le)) hden.le
  have hθ₀1 : θ₀ < 1 := by
    rw [div_lt_one hden]
    exact sub_lt_sub_right (Real.log_lt_log (by linarith) hr₂_gt) _
  obtain ⟨C₀, hC₀0, hC₀⟩ := rpow_le_lin (by linarith : (0 : ℝ) ≤ A₀) hθ₀0 hθ₀1
    (show 0 < η * δ₁ / 16 by positivity)
  set c₃ : ℝ := η * Real.log 9 + η * (12 * K) / 16 + η * δ₁ / 16 + C₀ + A₀ with hc₃
  have hc₃0 : 0 ≤ c₃ := by
    have : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    simp only [c₃]; positivity
  set C_tot : ℝ := S + B' + Real.exp c₃ + (2 / δ) * (1 + c₃) with hC_tot
  refine ⟨C_tot, by positivity, fun s hsre hsim => ?_⟩
  set t := s.im with ht
  have ht0 : 0 < |t| := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have htη : 1 ≤ |t| ^ η := Real.one_le_rpow ht1 hη.le
  rcases le_or_gt (3 / 2) s.re with hbig | hsmall
  · refine ⟨?_, ?_⟩
    · calc ‖(riemannZeta s)⁻¹‖ ≤ S := (hS s hbig).2
        _ ≤ C_tot * 1 := by
            simp only [C_tot]
            have : 0 ≤ B' + Real.exp c₃ + (2 / δ) * (1 + c₃) := by positivity
            linarith
        _ ≤ C_tot * |t| ^ η := by gcongr
    · calc ‖deriv riemannZeta s / riemannZeta s‖ ≤ B' := (hB s hbig).trans (le_max_left _ _)
        _ ≤ C_tot * 1 := by
            simp only [C_tot]
            have : 0 ≤ S + Real.exp c₃ + (2 / δ) * (1 + c₃) := by positivity
            linarith
        _ ≤ C_tot * |t| ^ η := by gcongr
  · set s₀ : ℂ := 2 + (t : ℂ) * I with hs₀
    have hs₀re : s₀.re = 2 := by simp [hs₀]
    have hs₀im : s₀.im = t := by simp [hs₀]
    have hRpos : 0 < R := by linarith
    have hball : ∀ z ∈ ball s₀ R,
        θ + δ₁ / 4 < z.re ∧ 5 / 2 < |z.im| ∧ z.re < 4 ∧ |z.im| < |t| + 2 := by
      intro z hz
      have hn : ‖z - s₀‖ < R := by rw [← dist_eq_norm]; exact hz
      have hre := Complex.abs_re_le_norm (z - s₀)
      have him := Complex.abs_im_le_norm (z - s₀)
      rw [sub_re, hs₀re] at hre
      rw [sub_im, hs₀im] at him
      have h1 := abs_lt.mp (lt_of_le_of_lt hre hn)
      have h2 : |z.im - t| < R := lt_of_le_of_lt him hn
      refine ⟨by simp only [R] at h1; linarith [h1.1], ?_, by linarith [h1.2], ?_⟩
      · linarith [abs_sub_comm z.im t, abs_sub_abs_le_abs_sub t z.im]
      · linarith [abs_sub_abs_le_abs_sub z.im t]
    have hne1 : ∀ z ∈ ball s₀ R, z ≠ 1 := by
      intro z hz h1
      have := (hball z hz).2.1
      rw [h1] at this; norm_num at this
    have hζne : ∀ z ∈ ball s₀ R, riemannZeta z ≠ 0 :=
      fun z hz => hZ z (by linarith [(hball z hz).1])
    have hζdiff : DifferentiableOn ℂ riemannZeta (ball s₀ R) := fun z hz =>
      (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
    obtain ⟨L, hLc, hLd, hLe⟩ := exists_log_ball hRpos hζdiff hζne
    have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun z hz =>
      (hLd z hz).differentiableAt.differentiableWithinAt
    have hLs₀ : ‖L s₀‖ ≤ K := by
      rw [hLc]
      have h := hS s₀ (by rw [hs₀re]; norm_num)
      exact norm_log_le (riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)) h.1 h.2
    set M : ℝ := Real.log (9 * |t|) with hM
    have hMpos : 0 < M := Real.log_pos (by linarith)
    have hLre : ∀ z ∈ ball s₀ R, (L z).re ≤ M := by
      intro z hz
      obtain ⟨hre, him, hre4, him2⟩ := hball z hz
      have hz0 : 1 / 2 < z.re := by linarith
      have hnz : ‖z‖ ≤ |t| + 6 := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos (by linarith)] at this; linarith
      have hz1 : 3 / 2 ≤ ‖z - 1‖ := by
        have := Complex.abs_im_le_norm (z - 1)
        rw [sub_im, one_im, sub_zero] at this; linarith
      have hζ := norm_riemannZeta_le (by linarith) (hne1 z hz)
      have hq1 : ‖z / (z - 1)‖ ≤ ‖z‖ := by
        rw [norm_div]; exact div_le_self (norm_nonneg _) (by linarith)
      have hq2 : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg z]
      have hζb : ‖riemannZeta z‖ ≤ 9 * |t| := by linarith
      have hpos : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr (hζne z hz)
      have hreL : (L z).re = Real.log ‖riemannZeta z‖ := by
        rw [← hLe z hz, Complex.norm_exp, Real.log_exp]
      rw [hreL]; exact Real.log_le_log hpos hζb
    set b : ℝ := (16 * M + 12 * K) / δ₁ + 1 with hb
    have hb1 : 1 ≤ b := by
      have : 0 ≤ (16 * M + 12 * K) / δ₁ := by positivity
      linarith
    have hbound2 : ∀ z, ‖z - s₀‖ = r₂ → ‖L z‖ ≤ b := by
      intro z hz
      set f : ℂ → ℂ := fun w => L (s₀ + w) with hf
      have hfd : DifferentiableOn ℂ f (ball 0 R) := by
        intro w hw
        have hw' : s₀ + w ∈ ball s₀ R := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]; exact hw
        exact ((hLd _ hw').differentiableAt.comp w
          ((differentiableAt_const s₀).add differentiableAt_id)).differentiableWithinAt
      have hfM : Set.MapsTo f (ball 0 R) {z | z.re ≤ M} := by
        intro w hw
        have hw' : s₀ + w ∈ ball s₀ R := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]; exact hw
        exact hLre _ hw'
      have hwR : z - s₀ ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right, hz]; linarith
      have hBC := Complex.borelCaratheodory hMpos hfd hfM hRpos hwR
      have hfz : f (z - s₀) = L z := by simp only [hf, add_sub_cancel]
      have hf0 : f 0 = L s₀ := by simp only [hf, add_zero]
      rw [hfz, hf0, hz, show R - r₂ = δ₁ / 4 by rw [hR, hr₂]; ring] at hBC
      have hr₂2 : r₂ ≤ 2 := by linarith
      have hRr : R + r₂ ≤ 3 := by linarith
      have hnum : 2 * M * r₂ + ‖L s₀‖ * (R + r₂) ≤ 4 * M + 3 * K := by
        have e1 : M * r₂ ≤ M * 2 := mul_le_mul_of_nonneg_left hr₂2 hMpos.le
        have e2 : ‖L s₀‖ * (R + r₂) ≤ K * 3 := mul_le_mul hLs₀ hRr (by linarith) hK0
        linarith
      have hkey : 2 * M * r₂ / (δ₁ / 4) + ‖L s₀‖ * (R + r₂) / (δ₁ / 4) ≤ (16 * M + 12 * K) / δ₁ := by
        rw [← add_div, div_le_div_iff₀ (by positivity) hδ₁0]
        nlinarith [mul_le_mul_of_nonneg_right hnum hδ₁0.le]
      linarith
    have hbound_small : ∀ z, ‖z - s₀‖ ≤ 1 / 2 → ‖L z‖ ≤ A₀ := by
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
        (show z ∈ closedBall s₀ (1 / 2) by rw [mem_closedBall, dist_eq_norm]; exact hz)
      have := norm_sub_norm_le (L z) (L s₀)
      have hmul_le : B' * ‖z - s₀‖ ≤ B' * (1 / 2) := mul_le_mul_of_nonneg_left hz hB'0
      linarith
    have hL_rint : ∀ w, ‖w - s₀‖ ≤ r_int → ‖L w‖ ≤ η * Real.log |t| + c₃ := by
      intro w hw_le
      have hbexp : η * δ₁ / 16 * b
          = η * Real.log |t| + (η * Real.log 9 + η * (12 * K) / 16 + η * δ₁ / 16) := by
        rw [hb, hM, Real.log_mul (by norm_num) ht0.ne']
        field_simp
        ring
      rcases le_or_gt ‖w - s₀‖ (1 / 2) with hle12 | hgt12
      · have h1 := hbound_small w hle12
        have hlog_nn : 0 ≤ η * Real.log |t| := mul_nonneg hη.le (Real.log_nonneg ht1)
        have : A₀ ≤ c₃ := by
          have : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
          have : 0 ≤ η * Real.log 9 + η * (12 * K) / 16 + η * δ₁ / 16 + C₀ := by positivity
          simp only [c₃]; linarith
        linarith
      · have h3 := three_circles (by norm_num : (0 : ℝ) < 1 / 2) (lt_trans hr_int_gt hr₂_gt)
          hR_gt hLdiff (fun z hz => hbound_small z hz.le) hbound2 hgt12.le (hw_le.trans hr₂_gt.le)
        set θw : ℝ := (Real.log ‖w - s₀‖ - Real.log (1 / 2)) / (Real.log r₂ - Real.log (1 / 2))
        have hθw0 : 0 ≤ θw :=
          div_nonneg (sub_nonneg.mpr (Real.log_le_log (by norm_num) hgt12.le)) hden.le
        have hθw_le : θw ≤ θ₀ := by
          apply div_le_div_of_nonneg_right _ hden.le
          exact sub_le_sub_right (Real.log_le_log (by linarith) hw_le) _
        have hLw : ‖L w‖ ≤ A₀ * b ^ θ₀ := by
          calc ‖L w‖ ≤ A₀ ^ (1 - θw) * b ^ θw := h3
            _ ≤ A₀ ^ (1 : ℝ) * b ^ θ₀ := by gcongr; linarith
            _ = A₀ * b ^ θ₀ := by rw [Real.rpow_one]
        have hlin := hC₀ b (by linarith)
        simp only [c₃]
        linarith
    have hss₀ : ‖s - s₀‖ = 2 - s.re := by
      have heq : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs₀, ht]
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hs_rint : ‖s - s₀‖ ≤ r_int := by
      rw [hss₀]; simp only [r_int, δ₁]; linarith
    have hs_in_R : s ∈ ball s₀ R := by
      rw [mem_ball, dist_eq_norm]; linarith
    refine ⟨?_, ?_⟩
    · have hζs : riemannZeta s = Complex.exp (L s) := (hLe s hs_in_R).symm
      have hinv : ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (‖L s‖) := by
        rw [hζs, ← Complex.exp_neg, Complex.norm_exp, neg_re]
        exact Real.exp_le_exp.mpr (by linarith [neg_le_abs (L s).re, Complex.abs_re_le_norm (L s)])
      have htpow : |t| ^ η = Real.exp (η * Real.log |t|) := by
        rw [Real.rpow_def_of_pos ht0, mul_comm]
      have hLs_bd := hL_rint s hs_rint
      calc ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (‖L s‖) := hinv
        _ ≤ Real.exp (η * Real.log |t| + c₃) := Real.exp_le_exp.mpr hLs_bd
        _ = Real.exp c₃ * |t| ^ η := by rw [htpow, ← Real.exp_add]; ring_nf
        _ ≤ C_tot * |t| ^ η := by
            gcongr
            simp only [C_tot]
            have : 0 ≤ S + B' + (2 / δ) * (1 + c₃) := by positivity
            linarith
    · have hsub_ball : closedBall s δ₁ ⊆ ball s₀ R := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        rw [mem_ball, dist_eq_norm]
        have htri := norm_add_le (w - s) (s - s₀)
        rw [sub_add_sub_cancel] at htri
        have : ‖w - s₀‖ ≤ r_int := by
          have : 2 - s.re + δ₁ ≤ r_int := by simp only [r_int, δ₁]; linarith
          linarith [hss₀]
        linarith
      have hcl_L : DiffContOnCl ℂ L (ball s δ₁) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ hδ₁0.ne']
        exact hLdiff.mono hsub_ball
      have hsph_L : ∀ w ∈ sphere s δ₁, ‖L w‖ ≤ (1 + c₃) * |t| ^ η := by
        intro w hw
        rw [mem_sphere, dist_eq_norm] at hw
        have htri := norm_add_le (w - s) (s - s₀)
        rw [sub_add_sub_cancel, hw, hss₀] at htri
        have hw_rint : ‖w - s₀‖ ≤ r_int := by
          simp only [r_int, δ₁] at htri ⊢; linarith
        have hLw := hL_rint w hw_rint
        have hlog_le : Real.log |t| ≤ |t| ^ η / η := Real.log_le_rpow_div ht0.le hη
        have hmul_log : η * Real.log |t| ≤ |t| ^ η := by
          have := mul_le_mul_of_nonneg_left hlog_le hη.le
          rwa [mul_div_cancel₀ _ hη.ne'] at this
        nlinarith
      have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hδ₁0 hcl_L hsph_L
      rw [(hLd s hs_in_R).deriv] at hcauchy
      have hdiv_eq : (1 + c₃) * |t| ^ η / δ₁ = (2 / δ) * (1 + c₃) * |t| ^ η := by
        simp only [δ₁]; field_simp
      rw [hdiv_eq] at hcauchy
      calc ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (2 / δ) * (1 + c₃) * |t| ^ η := hcauchy
        _ ≤ C_tot * |t| ^ η := by
            gcongr
            simp only [C_tot]
            have : 0 ≤ S + B' + Real.exp c₃ := by positivity
            linarith

/-- Bajo `SinCerosDerecha θ`, `‖Zinv z‖ ≤ C (1 + |Im z|)^η` en `Re z ≥ θ + δ`. -/
theorem Zinv_bound_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hη : 0 < η) (hZ : SinCerosDerecha θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, θ + δ ≤ z.re → ‖Zinv z‖ ≤ C * (1 + |z.im|) ^ η := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := inv_and_logDeriv_zeta_bound_theta hθ hδ hθδ hη hZ
  obtain ⟨S, hS⟩ := zeta_bounds_of_one_lt (show (1 : ℝ) < 3 / 2 by norm_num)
  set Kset : Set ℂ := {z | θ + δ ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ 4}
  have hKc : IsCompact Kset := by
    apply (isCompact_closedBall (0 : ℂ) 6).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_re).inter
        ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp continuous_im) continuous_const))
    · intro z hz
      rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im z
      have h1 : |z.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
      linarith [hz.2.2]
  have hcont : ContinuousOn Zinv Kset :=
    (differentiableOn_Zinv_theta hZ).continuousOn.mono fun z hz => by
      show θ < z.re; linarith [hz.1]
  obtain ⟨K₀, hK₀⟩ := hKc.bddAbove_image hcont.norm
  refine ⟨C₁ + max S 0 + max K₀ 0, by positivity, fun z hz => ?_⟩
  have hpow : 1 ≤ (1 + |z.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg z.im]) hη.le
  rcases le_or_gt 4 |z.im| with him | him
  · have hz1 : z ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
    rw [Zinv_eq hz1]
    calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * |z.im| ^ η := (hC₁ z hz him).1
      _ ≤ C₁ * (1 + |z.im|) ^ η :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hη.le) hC₁0
      _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by
          gcongr; linarith [le_max_right S 0, le_max_right K₀ 0]
  · rcases le_or_gt (3 / 2) z.re with hre | hre
    · have hz1 : z ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
      rw [Zinv_eq hz1]
      calc ‖(riemannZeta z)⁻¹‖ ≤ max S 0 := le_trans (hS z hre).2 (le_max_left _ _)
        _ ≤ (C₁ + max S 0 + max K₀ 0) * 1 := by linarith [le_max_right K₀ 0]
        _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr
    · have hzK : z ∈ Kset := ⟨hz, hre.le, him.le⟩
      calc ‖Zinv z‖ ≤ max K₀ 0 := le_trans (hK₀ ⟨z, hzK, rfl⟩) (le_max_left _ _)
        _ ≤ (C₁ + max S 0 + max K₀ 0) * 1 := by linarith [le_max_right S 0]
        _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr

/-! ### Lema de Balazard–Saias general en `θ ∈ [1/2, 1)` (Estado 45, `(3.1)`) -/

theorem differentiableOn_contornoK_theta {θ : ℝ} (hZ : SinCerosDerecha θ) {N h : ℝ} (hN : 0 < N)
    (hh : 0 < h) {s : ℂ} (hs : θ < s.re) :
    DifferentiableOn ℂ (contornoK N h s) {w | θ < (s + w).re ∧ -1 < w.re} := by
  set U : Set ℂ := {w | θ < (s + w).re ∧ -1 < w.re}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_re.comp (continuous_const.add continuous_id))).inter
      (isOpen_lt continuous_const continuous_re)
  have h0 : (0 : ℂ) ∈ U := ⟨by simpa using hs, by simp⟩
  have hZd : DifferentiableOn ℂ (fun w => Zinv (s + w)) U := by
    intro w hw
    have hd := (differentiableOn_Zinv_theta hZ).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show θ < (s + w).re from hw.1))
    exact (hd.comp w ((differentiableAt_const s).add differentiableAt_id)).differentiableWithinAt
  have hdsl : DifferentiableOn ℂ (dslope (fun w => Zinv (s + w)) 0) U :=
    (differentiableOn_dslope (hUo.mem_nhds h0)).mpr hZd
  have hG : DifferentiableOn ℂ (pesoG N h) U := by
    intro w hw
    have hw1 : (h : ℂ) * (w + 1) ≠ 0 := by
      refine mul_ne_zero (ofReal_ne_zero.mpr hh.ne') ?_
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [hw.2]
    unfold pesoG
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.div ?_ ?_ hw1)
    · exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr (by linarith)))).sub
        (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hN.ne')))
    · fun_prop
  exact hdsl.mul hG

theorem integrable_Zinv_mul_line_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hη : 0 < η) (hη1 : η < 1) (hZ : SinCerosDerecha θ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h)
    {s : ℂ} {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ -1) (hsσ : θ + δ ≤ s.re + σ) :
    Integrable (fun y : ℝ => Zinv (s + ((σ : ℂ) + y * I)) * pesoMellin N h ((σ : ℂ) + y * I)) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound_theta hθ hδ hθδ hη hZ
  obtain ⟨K, hK0, hK⟩ := norm_pesoMellin_line_le hN hh hσ0 hσ1
  have hcont : Continuous (fun y : ℝ => Zinv (s + ((σ : ℂ) + y * I))) := by
    refine (differentiableOn_Zinv_theta hZ).continuousOn.comp_continuous (by fun_prop) fun y => ?_
    show θ < (s + ((σ : ℂ) + y * I)).re; simp; linarith
  have hF := integrable_pesoMellin_line hN hh hσ0 hσ1
  refine Integrable.mono' ((integrable_one_add_norm (r := 2 - η) (by norm_num; linarith)).const_mul
    (CZ * (1 + |s.im|) ^ η * K)) (hcont.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have him : (s + ((σ : ℂ) + y * I)).im = s.im + y := by simp
  have hre : θ + δ ≤ (s + ((σ : ℂ) + y * I)).re := by simp; linarith
  have hy : 0 < 1 + |y| := by positivity
  rw [norm_mul, Real.norm_eq_abs y]
  calc ‖Zinv (s + ((σ : ℂ) + y * I))‖ * ‖pesoMellin N h ((σ : ℂ) + y * I)‖
      ≤ (CZ * (1 + |s.im + y|) ^ η) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        rw [← him]; exact mul_le_mul (hCZ _ hre) (hK y) (norm_nonneg _) (by positivity)
    _ ≤ (CZ * ((1 + |s.im|) ^ η * (1 + |y|) ^ η)) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        gcongr; exact one_add_abs_add_rpow_le _ _ hη.le
    _ = CZ * (1 + |s.im|) ^ η * K * ((1 + |y|) ^ η * (1 + |y|) ^ (-(2 : ℝ))) := by ring
    _ = CZ * (1 + |s.im|) ^ η * K * (1 + |y|) ^ (-(2 - η)) := by
        rw [← Real.rpow_add hy]; congr 2; ring

theorem horizontal_K_theta {θ δ₂ η' : ℝ} (hθ : 1 / 2 ≤ θ) (hδ₂ : 0 < δ₂) (hθδ₂ : θ + δ₂ < 1)
    (hη' : 0 < η') (hη'1 : η' ≤ 1) (hZ : SinCerosDerecha θ) {N h : ℝ} (hN : 1 ≤ N) (hh : 0 < h)
    {s : ℂ} {α β : ℝ} (hβ : β ≤ 2) (hreg : θ + δ₂ ≤ s.re + α) :
    ∃ D : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, α ≤ x → x ≤ β →
      ‖contornoK N h s (x + T * I)‖ ≤ D / T ∧
        ‖contornoK N h s (x + ((-T : ℝ) : ℂ) * I)‖ ≤ D / T := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound_theta hθ hδ₂ hθδ₂ hη' hZ
  set CZ' : ℝ := CZ * (1 + |s.im|) ^ η'
  have hCZ'0 : 0 ≤ CZ' := by positivity
  set E_c : ℝ := 2 * (N + h) ^ (3 : ℝ) / h
  refine ⟨(2 * CZ' + ‖Zinv s‖) * E_c, fun T hT x hx1 hx2 => ?_⟩
  have hT0 : 0 < T := by linarith
  have main : ∀ w : ℂ, w.re = x → |w.im| = T →
      ‖contornoK N h s w‖ ≤ (2 * CZ' + ‖Zinv s‖) * E_c / T := by
    intro w hwre hwim
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwim; simp at hwim; linarith
    rw [contornoK_eq hw0]
    have hnw : T ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
    have hnw1 : T ≤ ‖w + 1‖ := by
      have := Complex.abs_im_le_norm (w + 1)
      rwa [add_im, one_im, add_zero, hwim] at this
    have hZw : ‖Zinv (s + w)‖ ≤ 2 * CZ' * T := by
      have hre : θ + δ₂ ≤ (s + w).re := by rw [add_re, hwre]; linarith
      have h1 := hCZ (s + w) hre
      rw [add_im] at h1
      have h2 := one_add_abs_add_rpow_le s.im w.im hη'.le
      have h3 : (1 + |w.im|) ^ η' ≤ 1 + |w.im| := by
        calc (1 + |w.im|) ^ η' ≤ (1 + |w.im|) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) hη'1
          _ = 1 + |w.im| := Real.rpow_one _
      calc ‖Zinv (s + w)‖ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |w.im|) ^ η') :=
            le_trans h1 (mul_le_mul_of_nonneg_left h2 hCZ0)
        _ = CZ' * (1 + |w.im|) ^ η' := by simp only [CZ']; ring
        _ ≤ CZ' * (1 + T) := by rw [← hwim]; exact mul_le_mul_of_nonneg_left h3 hCZ'0
        _ ≤ 2 * CZ' * T := by nlinarith
    have hF : ‖pesoMellin N h w‖ * T ^ 2 ≤ E_c := by
      have h1 := norm_pesoMellin_le (N := N) (by linarith) hh w
      rw [hwre] at h1
      have hNh1 : 1 ≤ N + h := by linarith
      have hnum : (N + h) ^ (x + 1) + N ^ (x + 1) ≤ 2 * (N + h) ^ (3 : ℝ) := by
        have e1 : (N + h) ^ (x + 1) ≤ (N + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNh1 (by linarith)
        have e2 : N ^ (x + 1) ≤ N ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        have e3 : N ^ (3 : ℝ) ≤ (N + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        linarith
      have hden : h * T * T ≤ h * ‖w‖ * ‖w + 1‖ := by gcongr
      have h2 : ‖pesoMellin N h w‖ ≤ 2 * (N + h) ^ (3 : ℝ) / (h * T * T) :=
        h1.trans (by gcongr)
      have hpos : 0 < h * T * T := by positivity
      rw [le_div_iff₀ hpos] at h2
      simp only [E_c]
      rw [le_div_iff₀ hh]
      nlinarith [norm_nonneg (pesoMellin N h w)]
    rw [le_div_iff₀ hT0]
    have hsplit : ‖Zinv (s + w) * pesoMellin N h w - Zinv s * pesoMellin N h w‖
        ≤ (‖Zinv (s + w)‖ + ‖Zinv s‖) * ‖pesoMellin N h w‖ := by
      rw [← sub_mul, norm_mul]; gcongr; exact norm_sub_le _ _
    have hZs : ‖Zinv (s + w)‖ + ‖Zinv s‖ ≤ (2 * CZ' + ‖Zinv s‖) * T := by
      nlinarith [norm_nonneg (Zinv s)]
    calc ‖Zinv (s + w) * pesoMellin N h w - Zinv s * pesoMellin N h w‖ * T
        ≤ (‖Zinv (s + w)‖ + ‖Zinv s‖) * ‖pesoMellin N h w‖ * T := by gcongr
      _ ≤ (2 * CZ' + ‖Zinv s‖) * T * ‖pesoMellin N h w‖ * T := by gcongr
      _ = (2 * CZ' + ‖Zinv s‖) * (‖pesoMellin N h w‖ * T ^ 2) := by ring
      _ ≤ (2 * CZ' + ‖Zinv s‖) * E_c := by gcongr
  exact ⟨main _ (by simp) (by simp [abs_of_pos hT0]),
    main _ (by simp) (by simp [abs_of_pos hT0])⟩

set_option maxHeartbeats 4000000 in
/-- **Lema de Balazard–Saias general (Estado 45, `(3.1)`):** bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`),
para `n ≥ 1` y `Re s ≥ θ + δ` (incluido `s = 1`),
`‖∑_{d≤n} μ(d) d^{−s} − Zinv s‖ ≤ C n^{−δ/3} (1 + |Im s|)^η`. -/
theorem balazard_saias_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hη : 0 < η) (hZ : SinCerosDerecha θ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s : ℂ, θ + δ ≤ s.re →
      ‖∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - Zinv s‖
        ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  set η' : ℝ := min η (δ / 6)
  have hη'0 : 0 < η' := lt_min hη (by positivity)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'δ : η' ≤ δ / 6 := min_le_right _ _
  have hη'1 : η' < 1 := by linarith
  have hδ2 : 0 < δ / 2 := by positivity
  have hθδ2 : θ + δ / 2 < 1 := by linarith
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound_theta hθ hδ2 hθδ2 hη'0 hZ
  have hJint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(1 + η'))) :=
    integrable_one_add_norm (by norm_num; linarith)
  set J : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(1 + η'))
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  set Cm : ℝ := CZ * (3 * (4 / δ) ^ (1 + 2 * η')) * J / (2 * Real.pi)
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨1 + Cm, fun n hn s hsre => ?_⟩
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hh0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN0
  set a : ℝ := min (s.re - θ - δ / 2) (1 / 2)
  have ha1 : δ / 2 ≤ a := le_min (by linarith) (by linarith)
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  have ha3 : a ≤ s.re - θ - δ / 2 := min_le_left _ _
  have ha0 : 0 < a := by linarith
  have hsθ : θ < s.re := by linarith
  have hD := dirichlet_side hN0 hh0 (s := s) (by linarith)
  have hU : {w : ℂ | -a ≤ w.re ∧ w.re ≤ 2} ⊆ {w | θ < (s + w).re ∧ -1 < w.re} :=
    fun w hw => ⟨by simp; linarith [hw.1], by linarith [hw.1]⟩
  have hdiff := (differentiableOn_contornoK_theta hZ hN0 hh0 hsθ).mono hU
  have hlineK : ∀ σ : ℝ, σ ≠ 0 → σ ≠ -1 → θ + δ / 2 ≤ s.re + σ →
      Integrable (fun y : ℝ => contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I)) ∧
      ∫ y : ℝ, contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I)
        = (∫ y : ℝ, Zinv (s + (σ + y * I)) * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I))
          - Zinv s * ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
    intro σ hσ0 hσ1 hσs
    have hZF := integrable_Zinv_mul_line_theta hθ hδ2 hθδ2 hη'0 hη'1 hZ hN0 hh0 hσ0 hσ1 hσs
    have hF := integrable_pesoMellin_line hN0 hh0 hσ0 hσ1
    have hfun : (fun y : ℝ => contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I))
        = fun y : ℝ => Zinv (s + (σ + y * I)) * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I)
          - Zinv s * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
      funext y
      apply contornoK_eq
      intro h0; have := congrArg Complex.re h0; simp at this; exact hσ0 this
    rw [hfun]
    exact ⟨hZF.sub (hF.const_mul _), by rw [integral_sub hZF (hF.const_mul _), integral_const_mul]⟩
  obtain ⟨hKa, hIa⟩ := hlineK (-a) (by linarith) (by linarith) (by linarith)
  obtain ⟨hK2, hI2⟩ := hlineK 2 (by norm_num) (by norm_num) (by linarith)
  obtain ⟨Dh, hDh⟩ := horizontal_K_theta hθ hδ2 hθδ2 hη'0 hη'1.le hZ hN1 hh0
    (s := s) (α := -a) (β := 2) le_rfl (by linarith)
  have hshift := integral_vertical_eq (by linarith) hdiff hKa hK2 hDh
  have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have hint2 : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I)
      = 2 * Real.pi := by
    have h1 := mellinInv_pesoMellin hN0 hh0 (σ := 2) two_pos one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1] at h1
    simp only [ofReal_one, one_cpow, one_smul] at h1
    rw [Complex.real_smul] at h1
    have e : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by push_cast; field_simp
    exact mul_left_cancel₀ hc (h1.trans e.symm)
  have hinta : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) = 0 := by
    have h1 := mellinInv_pesoMellin_neg hN0 hh0 (σ := -a) (by linarith) (by linarith) one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1, sub_self] at h1
    simp only [ofReal_one, one_cpow, one_smul, ofReal_zero] at h1
    rw [Complex.real_smul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  have hrel : (∫ y : ℝ, Zinv (s + (((2 : ℝ) : ℂ) + y * I))
        * pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I))
      = 2 * Real.pi * Zinv s + ∫ y : ℝ, Zinv (s + (((-a : ℝ) : ℂ) + y * I))
        * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) := by
    rw [hIa, hI2, hinta, hint2] at hshift
    linear_combination -hshift
  set A_int : ℂ := ∫ y : ℝ, Zinv (s + (((-a : ℝ) : ℂ) + y * I))
    * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I)
  set Q_c : ℝ := CZ * (1 + |s.im|) ^ η' * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η'))
  have hAbound : ‖A_int‖ ≤ Q_c * J := by
    rw [show J = ∫ y : ℝ, (1 + ‖y‖) ^ (-(1 + η')) from rfl, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hJint.const_mul Q_c) (Eventually.of_forall fun y => ?_)
    have hre : θ + δ / 2 ≤ (s + (((-a : ℝ) : ℂ) + y * I)).re := by simp; linarith
    have him : (s + (((-a : ℝ) : ℂ) + y * I)).im = s.im + y := by simp
    have hZ1 := hCZ _ hre
    rw [him] at hZ1
    have hZ2 : ‖Zinv (s + (((-a : ℝ) : ℂ) + y * I))‖
        ≤ CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by
      calc _ ≤ CZ * (1 + |s.im + y|) ^ η' := hZ1
        _ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |y|) ^ η') :=
            mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le _ _ hη'0.le) hCZ0
        _ = CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by ring
    have hF := norm_pesoMellin_left hN1 ha0 ha2 (κ := 2 * η') (by positivity) (by linarith) y
    have h2a : (2 / a) ^ (1 + 2 * η') ≤ (4 / δ) ^ (1 + 2 * η') := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [div_le_div_iff₀ ha0 hδ]; linarith
    have hy : 0 < 1 + |y| := by positivity
    have hpow : (1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η')) = (1 + ‖y‖) ^ (-(1 + η')) := by
      rw [← Real.rpow_add hy, Real.norm_eq_abs]; congr 1; ring
    have hNe : (n : ℝ) ^ (2 * η' / 2) = (n : ℝ) ^ η' := by congr 1; ring
    rw [norm_mul]
    calc ‖Zinv (s + (((-a : ℝ) : ℂ) + y * I))‖
          * ‖pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I)‖
        ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ (2 * η' / 2) * (2 / a) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := mul_le_mul hZ2 hF (norm_nonneg _) (by positivity)
      _ ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := by rw [hNe]; gcongr
      _ = Q_c * ((1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η'))) := by simp only [Q_c]; ring
      _ = Q_c * (1 + ‖y‖) ^ (-(1 + η')) := by rw [hpow]
  have hSφ : ∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      = Zinv s + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int := by
    rw [← hD, hrel]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast; field_simp
  have hsm := smoothing_error hn (s := s) (by linarith)
  have hdiff_eq : ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - Zinv s
      = -(∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s))
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int := by
    linear_combination hSφ
  have h1_exp : (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
    have he1 : (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have he2 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
    calc (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) * 1 := by linarith
      _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by gcongr
  have h2_exp : (n : ℝ) ^ (-a) * (n : ℝ) ^ η' ≤ (n : ℝ) ^ (-δ / 3) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3_im : (1 + |s.im|) ^ η' ≤ (1 + |s.im|) ^ η :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hη'η
  have hA_term : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖
      ≤ Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
    have hpi_pos : 0 < 2 * Real.pi := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpi_pos)]
    calc (1 / (2 * Real.pi)) * ‖A_int‖
        ≤ (1 / (2 * Real.pi)) * (Q_c * J) := mul_le_mul_of_nonneg_left hAbound (by positivity)
      _ = CZ * (3 * (4 / δ) ^ (1 + 2 * η')) * J / (2 * Real.pi)
            * ((n : ℝ) ^ (-a) * (n : ℝ) ^ η') * (1 + |s.im|) ^ η' := by simp only [Q_c]; ring
      _ ≤ Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
          simp only [Cm]
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2_exp hCm0) h3_im
            (by positivity) (by positivity)
  rw [hdiff_eq]
  calc ‖-(∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s))
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖
      ≤ ‖∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)‖
        + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η + Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η :=
        add_le_add (hsm.trans h1_exp) hA_term
    _ = (1 + Cm) * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by ring

/-! ### Cotas de `m_Q`, `t_Q`, `P_Q` y `E_Q` bajo `SinCerosDerecha θ` (Estado 45, `(5.2)–(6.4)`) -/

theorem m_bound_theta {θ δ : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hZ : SinCerosDerecha θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |m n| ≤ K * (n : ℝ) ^ (-(1 - θ - 2 * δ / 3)) := by
  obtain ⟨C, hC⟩ := balazard_saias_theta hθ hδ hθδ (η := 1) one_pos hZ
  set b : ℝ := θ + δ with hb
  have hR : ∀ d : ℕ, 1 ≤ d → ‖Dsum d b - Zinv b‖ ≤ C * (d : ℝ) ^ (-δ / 3) := by
    intro d hd
    have := hC d hd (b : ℂ) (by simp [hb])
    simpa [Dsum] using this
  have hC0 : 0 ≤ C := by
    have h1 := hR 1 le_rfl; simp at h1; exact le_trans (norm_nonneg _) h1
  have hm0 : ∀ n : ℕ, 1 ≤ n → |m n| ≤ C * (n : ℝ) ^ (-δ / 3) := by
    intro n hn
    have := hC n hn 1 (by simp; linarith)
    rw [show ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 : ℂ)) = Dsum n 1 from rfl,
      Dsum_one, Zinv_one, sub_zero, Complex.norm_real, Real.norm_eq_abs] at this
    simpa using this
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ (b - 1) with hg
  set R_seq : ℕ → ℂ := fun d => Dsum d b - Zinv b with hRdef
  have hgdec : ∀ d : ℕ, 1 ≤ d → g (d + 1) ≤ g d := fun d hd =>
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hd) (by push_cast; linarith) (by linarith)
  have hg0 : ∀ d, 0 ≤ g d := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hformula : ∀ n : ℕ, ((m n : ℝ) : ℂ)
      = Zinv b + R_seq n * g (n + 1)
        + ∑ d ∈ Finset.Icc 1 n, R_seq d * ((g d : ℂ) - g (d + 1)) := by
    intro n
    have hterm : ∀ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 : ℂ))
        = (((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(b : ℂ))) * (g d : ℂ) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      simp only [hg]
      rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc, ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
      congr 2; push_cast; ring
    rw [← Dsum_one, Dsum, Finset.sum_congr rfl hterm, abel_Icc]
    have hA : ∀ d, ∑ e ∈ Finset.Icc 1 d, ((mu e : ℝ) : ℂ) * (e : ℂ) ^ (-(b : ℂ)) = Dsum d b :=
      fun _ => rfl
    simp only [hA, hRdef]
    have htel : ∑ d ∈ Finset.Icc 1 n, ((g d : ℂ) - g (d + 1)) = (g 1 : ℂ) - g (n + 1) := by
      have := telescopio_Ioc g (n := 0) n
      rw [zero_add, zero_add] at this
      rw [show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_add_one_left_eq_Ioc 0 n]
      exact_mod_cast this
    have hg1 : g 1 = 1 := by simp [hg]
    have hsplit : ∑ d ∈ Finset.Icc 1 n, Dsum d b * ((g d : ℂ) - g (d + 1))
        = Zinv b * ∑ d ∈ Finset.Icc 1 n, ((g d : ℂ) - g (d + 1))
          + ∑ d ∈ Finset.Icc 1 n, (Dsum d b - Zinv b) * ((g d : ℂ) - g (d + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hsplit, htel, hg1]; push_cast; ring
  set β : ℝ := 1 - θ - 2 * δ / 3 with hβ
  have hexp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (-δ / 3) * g (n + 1) ≤ (n : ℝ) ^ (-β) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ) ^ (-δ / 3) * g (n + 1)
        ≤ (n : ℝ) ^ (-δ / 3) * g n :=
          mul_le_mul_of_nonneg_left (hgdec n hn) (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-β) := by
          simp only [hg]
          rw [← Real.rpow_add hn0]; congr 1; simp only [b, β]; ring
  have hdiff_g : ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ^ (-δ / 3) * (g d - g (d + 1))
        ≤ (d : ℝ) ^ (-β) - ((d + 1 : ℕ) : ℝ) ^ (-β) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hd1 : (d : ℝ) ^ (-δ / 3) * g d = (d : ℝ) ^ (-β) := by
      simp only [hg]; rw [← Real.rpow_add hd0]; congr 1; simp only [b, β]; ring
    have hd2 : ((d + 1 : ℕ) : ℝ) ^ (-δ / 3) ≤ (d : ℝ) ^ (-δ / 3) :=
      Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith) (by linarith)
    have hd3 : ((d + 1 : ℕ) : ℝ) ^ (-δ / 3) * g (d + 1) = ((d + 1 : ℕ) : ℝ) ^ (-β) := by
      simp only [hg]; rw [← Real.rpow_add (by positivity)]; congr 1; simp only [b, β]; ring
    have := mul_le_mul_of_nonneg_right hd2 (hg0 (d + 1))
    nlinarith [hgdec d hd]
  refine ⟨3 * C, by positivity, fun n hn => ?_⟩
  have hdiff : ∀ j : ℕ, ‖((m (n + j) : ℝ) : ℂ) - ((m n : ℝ) : ℂ)‖ ≤ 3 * C * (n : ℝ) ^ (-β) := by
    intro j
    have hsub : ((m (n + j) : ℝ) : ℂ) - ((m n : ℝ) : ℂ)
        = R_seq (n + j) * g (n + j + 1) - R_seq n * g (n + 1)
          + ∑ d ∈ Finset.Ioc n (n + j), R_seq d * ((g d : ℂ) - g (d + 1)) := by
      rw [hformula (n + j), hformula n]
      have hsplit_sum : ∑ d ∈ Finset.Icc 1 (n + j), R_seq d * ((g d : ℂ) - g (d + 1))
          = (∑ d ∈ Finset.Icc 1 n, R_seq d * ((g d : ℂ) - g (d + 1)))
            + ∑ d ∈ Finset.Ioc n (n + j), R_seq d * ((g d : ℂ) - g (d + 1)) := by
        rw [show Finset.Icc 1 (n + j) = Finset.Ioc 0 (n + j) from Finset.Icc_add_one_left_eq_Ioc 0 (n + j),
          show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_add_one_left_eq_Ioc 0 n]
        exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le n) (Nat.le_add_right n j)).symm
      rw [hsplit_sum]; ring
    rw [hsub]
    have hnj_bd : ‖R_seq (n + j) * (g (n + j + 1) : ℂ)‖ ≤ C * ((n + j : ℕ) : ℝ) ^ (-β) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact (mul_le_mul_of_nonneg_right (hR (n + j) (by omega)) (hg0 _)).trans
        (by have := hexp (n + j) (by omega); nlinarith)
    have hn_bd : ‖R_seq n * (g (n + 1) : ℂ)‖ ≤ C * (n : ℝ) ^ (-β) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact (mul_le_mul_of_nonneg_right (hR n hn) (hg0 _)).trans
        (by have := hexp n hn; nlinarith)
    have hsum_bd : ‖∑ d ∈ Finset.Ioc n (n + j), R_seq d * ((g d : ℂ) - g (d + 1))‖
        ≤ C * (((n + 1 : ℕ) : ℝ) ^ (-β) - ((n + j + 1 : ℕ) : ℝ) ^ (-β)) := by
      calc ‖∑ d ∈ Finset.Ioc n (n + j), R_seq d * ((g d : ℂ) - g (d + 1))‖
          ≤ ∑ d ∈ Finset.Ioc n (n + j), ‖R_seq d * ((g d : ℂ) - g (d + 1))‖ := norm_sum_le _ _
        _ ≤ ∑ d ∈ Finset.Ioc n (n + j), C * ((d : ℝ) ^ (-β) - ((d + 1 : ℕ) : ℝ) ^ (-β)) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd1 : 1 ≤ d := by have := (Finset.mem_Ioc.mp hd).1; omega
            have hgd : 0 ≤ g d - g (d + 1) := sub_nonneg.mpr (hgdec d hd1)
            rw [norm_mul, show ((g d : ℂ) - g (d + 1)) = ((g d - g (d + 1) : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgd]
            calc ‖R_seq d‖ * (g d - g (d + 1))
                ≤ (C * (d : ℝ) ^ (-δ / 3)) * (g d - g (d + 1)) :=
                  mul_le_mul_of_nonneg_right (hR d hd1) hgd
              _ = C * ((d : ℝ) ^ (-δ / 3) * (g d - g (d + 1))) := by ring
              _ ≤ C * ((d : ℝ) ^ (-β) - ((d + 1 : ℕ) : ℝ) ^ (-β)) :=
                  mul_le_mul_of_nonneg_left (hdiff_g d hd1) hC0
        _ = C * (((n + 1 : ℕ) : ℝ) ^ (-β) - ((n + j + 1 : ℕ) : ℝ) ^ (-β)) := by
            rw [← Finset.mul_sum, telescopio_Ioc (fun k => (k : ℝ) ^ (-β)) j]
    have hβ_pos : 0 < β := by simp only [β]; linarith
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmon1 : ((n + j : ℕ) : ℝ) ^ (-β) ≤ (n : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hn_pos (by exact_mod_cast Nat.le_add_right n j) (by linarith)
    have hmon2 : ((n + 1 : ℕ) : ℝ) ^ (-β) ≤ (n : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hn_pos (by exact_mod_cast Nat.le_succ n) (by linarith)
    have hnn_end : 0 ≤ ((n + j + 1 : ℕ) : ℝ) ^ (-β) := by positivity
    have htri1 := norm_add_le (R_seq (n + j) * g (n + j + 1) - R_seq n * g (n + 1))
      (∑ d ∈ Finset.Ioc n (n + j), R_seq d * ((g d : ℂ) - g (d + 1)))
    have htri2 := norm_sub_le (R_seq (n + j) * g (n + j + 1)) (R_seq n * g (n + 1))
    nlinarith
  have h0 : Tendsto (fun j : ℕ => ((n + j : ℕ) : ℝ) ^ (-δ / 3)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < δ / 3 by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
    refine this.congr fun j => ?_
    show ((j + n : ℕ) : ℝ) ^ (-(δ / 3)) = ((n + j : ℕ) : ℝ) ^ (-δ / 3)
    rw [add_comm j n, neg_div]
  have hlim : Tendsto (fun j : ℕ => C * ((n + j : ℕ) : ℝ) ^ (-δ / 3) + 3 * C * (n : ℝ) ^ (-β))
      atTop (𝓝 (3 * C * (n : ℝ) ^ (-β))) := by
    simpa using (h0.const_mul C).add (tendsto_const_nhds (x := 3 * C * (n : ℝ) ^ (-β)))
  refine ge_of_tendsto' hlim fun j => ?_
  have hj := hdiff j
  have hmj := hm0 (n + j) (by omega)
  have e : ‖((m (n + j) : ℝ) : ℂ) - ((m n : ℝ) : ℂ)‖ = |m (n + j) - m n| := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e] at hj
  have h1 := abs_sub_abs_le_abs_sub (m n) (m (n + j))
  rw [abs_sub_comm] at h1
  linarith

theorem t_cauchy_theta {θ δ : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hZ : SinCerosDerecha θ) :
    ∃ C c : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |t n| ≤ C * (n : ℝ) ^ (-δ / 3) * (Real.log n + c) := by
  obtain ⟨C, hC⟩ := balazard_saias_theta hθ hδ hθδ (η := 1) one_pos hZ
  set r : ℝ := 1 - θ - δ with hr
  have hr0 : 0 < r := by linarith
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    simp at h1; exact le_trans (norm_nonneg _) (by linarith)
  refine ⟨C, (1 + r) / r, hC0, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set E_fn : ℂ → ℂ := fun s => Dsum n s - Zinv s with hE
  have hE1 : E_fn 1 = ((m n : ℝ) : ℂ) := by simp [hE, Dsum_one, Zinv_one]
  set D' : ℂ := ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * ((d : ℂ) ^ (-(1 : ℂ)) * Complex.log d * (-1))
    with hD'
  have hEd : HasDerivAt E_fn (D' - 1) 1 := (hasDerivAt_Dsum n).sub hasDerivAt_Zinv_one
  have hD'val : D' = -∑ d ∈ Finset.Icc 1 n, ((mu d / (d : ℝ) * Real.log d : ℝ) : ℂ) := by
    rw [hD', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [cpow_neg_one, ← Complex.natCast_log]; push_cast; ring
  have ht : ((t n : ℝ) : ℂ) = -(Real.log n : ℂ) * E_fn 1 - (D' - 1) := by
    have hsum : ∑ d ∈ Finset.Icc 1 n, mu d / (d : ℝ) * Real.log ((n : ℝ) / (d : ℝ))
        = Real.log n * m n - ∑ d ∈ Finset.Icc 1 n, mu d / (d : ℝ) * Real.log d := by
      unfold m
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [Real.log_div hn0.ne' hd0.ne']; ring
    rw [hE1, hD'val]; unfold t; rw [hsum]; push_cast; ring
  have hb1 : ‖E_fn 1‖ ≤ C * (n : ℝ) ^ (-δ / 3) := by
    have := hC n hn 1 (by simp; linarith)
    simpa [hE, Dsum] using this
  have hdiff : DifferentiableOn ℂ E_fn (closedBall 1 r) := by
    intro z hz
    have hz' : θ < z.re := by
      have h1 : ‖z - 1‖ ≤ r := by rw [← dist_eq_norm]; exact hz
      have h2 := Complex.abs_re_le_norm (z - 1)
      rw [sub_re, one_re] at h2
      have := (abs_le.mp (le_trans h2 h1)).1
      linarith
    have hD : DifferentiableAt ℂ (Dsum n) z := by
      unfold Dsum
      refine DifferentiableAt.fun_sum fun d hd => ?_
      have hd0 : (d : ℂ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hd).1
        exact_mod_cast (show d ≠ 0 by omega)
      exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hd0) |>.const_mul _
    have hZd : DifferentiableAt ℂ Zinv z :=
      (differentiableOn_Zinv_theta hZ).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hz')
    exact (hD.sub hZd).differentiableWithinAt
  have hcl : DiffContOnCl ℂ E_fn (ball 1 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr0.ne']; exact hdiff
  have hsph : ∀ z ∈ sphere (1 : ℂ) r, ‖E_fn z‖ ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + r) := by
    intro z hz
    have h1 : ‖z - 1‖ = r := by rw [← dist_eq_norm]; exact hz
    have hre : θ + δ ≤ z.re := by
      have h2 := Complex.abs_re_le_norm (z - 1)
      rw [sub_re, one_re, h1] at h2
      have := (abs_le.mp h2).1; linarith
    have him : |z.im| ≤ r := by
      have h2 := Complex.abs_im_le_norm (z - 1)
      rwa [sub_im, one_im, sub_zero, h1] at h2
    have := hC n hn z hre
    rw [Real.rpow_one] at this
    exact this.trans (by gcongr)
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hcl hsph
  rw [hEd.deriv] at hcauchy
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc |t n| = ‖((t n : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖-(Real.log n : ℂ) * E_fn 1 - (D' - 1)‖ := by rw [ht]
    _ ≤ Real.log n * ‖E_fn 1‖ + ‖D' - 1‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ Real.log n * (C * (n : ℝ) ^ (-δ / 3)) + C * (n : ℝ) ^ (-δ / 3) * (1 + r) / r := by gcongr
    _ = C * (n : ℝ) ^ (-δ / 3) * (Real.log n + (1 + r) / r) := by ring

theorem t_bound_theta {θ δ : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hZ : SinCerosDerecha θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |t n| ≤ K * (n : ℝ) ^ (-(1 - θ - 2 * δ / 3)) := by
  obtain ⟨Km, hKm0, hKm⟩ := m_bound_theta hθ hδ hθδ hZ
  obtain ⟨Ct, ct, hCt0, hCt⟩ := t_cauchy_theta hθ hδ hθδ hZ
  set β : ℝ := 1 - θ - 2 * δ / 3 with hβ
  have hβ0 : 0 < β := by simp only [β]; linarith
  set K : ℝ := Km * ((2 : ℝ) ^ (β + 1) / β) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun n hn => ?_⟩
  have h22 : (2 : ℝ) ^ (β + 1) * (2 : ℝ) ^ (-β - 1) = 1 := by
    rw [← Real.rpow_add (by norm_num), show β + 1 + (-β - 1) = 0 by ring, Real.rpow_zero]
  have hdiff : ∀ j : ℕ, |t n - t (n + j)| ≤ K * (n : ℝ) ^ (-β) := by
    intro j
    rw [t_diff hn j]
    have hterm : ∀ i ∈ Finset.range j,
        |m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))|
          ≤ K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) := by
      intro i _
      have hk1 : (1 : ℝ) ≤ ((n + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + i by omega)
      have hk0 : (0 : ℝ) < ((n + i : ℕ) : ℝ) := by linarith
      have hq : ((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ) = 1 + 1 / ((n + i : ℕ) : ℝ) := by
        push_cast; field_simp
      have hlog0 : 0 ≤ Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ)) := by
        rw [hq]; exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
      have hlog1 : Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ)) ≤ 1 / ((n + i : ℕ) : ℝ) := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / ((n + i : ℕ) : ℝ) by positivity)
        rw [hq]; linarith
      have hm := hKm (n + i) (by omega)
      have hmvt := rpow_neg_sub_ge hβ0 hk1
      have hpow : ((n + i : ℕ) : ℝ) ^ (-β) * (1 / ((n + i : ℕ) : ℝ))
          = ((n + i : ℕ) : ℝ) ^ (-β - 1) := by
        rw [Real.rpow_sub_one hk0.ne']; ring
      rw [abs_mul, abs_of_nonneg hlog0]
      calc |m (n + i)| * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))
          ≤ (Km * ((n + i : ℕ) : ℝ) ^ (-β)) * (1 / ((n + i : ℕ) : ℝ)) :=
            mul_le_mul hm hlog1 hlog0 (by positivity)
        _ = Km * ((n + i : ℕ) : ℝ) ^ (-β - 1) := by rw [mul_assoc, hpow]
        _ = Km * ((2 : ℝ) ^ (β + 1) / β) * (β * (2 : ℝ) ^ (-β - 1) * ((n + i : ℕ) : ℝ) ^ (-β - 1)) := by
            field_simp; rw [mul_assoc, h22, mul_one]
        _ ≤ K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) := by
            rw [hK]; gcongr
    calc |∑ i ∈ Finset.range j, m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))|
        ≤ ∑ i ∈ Finset.range j,
            |m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) :=
          Finset.sum_le_sum hterm
      _ = K * ((n : ℝ) ^ (-β) - ((n + j : ℕ) : ℝ) ^ (-β)) := by
          rw [← Finset.mul_sum]; congr 1
          have := Finset.sum_range_sub' (fun i => ((n + i : ℕ) : ℝ) ^ (-β)) j
          simp only [Nat.cast_add, Nat.cast_one, add_zero] at this ⊢
          rw [← this]; exact Finset.sum_congr rfl fun i _ => by ring_nf
      _ ≤ K * (n : ℝ) ^ (-β) := by
          have : 0 ≤ ((n + j : ℕ) : ℝ) ^ (-β) := by positivity
          nlinarith
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ (δ / 3)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (show 0 < δ / 3 by positivity)).tendsto_div_nhds_zero
  have hpowt : Tendsto (fun x : ℝ => x ^ (-(δ / 3))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (show 0 < δ / 3 by positivity)
  have hcomb : Tendsto (fun x : ℝ => Ct * (Real.log x / x ^ (δ / 3)) + Ct * ct * x ^ (-(δ / 3)))
      atTop (𝓝 0) := by
    simpa using (hlog.const_mul Ct).add (hpowt.const_mul (Ct * ct))
  have hseq := hcomb.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
  have hlim : Tendsto (fun j : ℕ => (Ct * (Real.log ((j + n : ℕ) : ℝ) / ((j + n : ℕ) : ℝ) ^ (δ / 3))
      + Ct * ct * ((j + n : ℕ) : ℝ) ^ (-(δ / 3))) + K * (n : ℝ) ^ (-β)) atTop
      (𝓝 (K * (n : ℝ) ^ (-β))) := by
    simpa using hseq.add (tendsto_const_nhds (x := K * (n : ℝ) ^ (-β)))
  refine ge_of_tendsto' hlim fun j => ?_
  have hj0 : (0 : ℝ) < ((j + n : ℕ) : ℝ) := by exact_mod_cast (show 0 < j + n by omega)
  have htj := hCt (n + j) (by omega)
  rw [add_comm n j] at htj
  have e : Ct * ((j + n : ℕ) : ℝ) ^ (-δ / 3) * (Real.log ((j + n : ℕ) : ℝ) + ct)
      = Ct * (Real.log ((j + n : ℕ) : ℝ) / ((j + n : ℕ) : ℝ) ^ (δ / 3))
        + Ct * ct * ((j + n : ℕ) : ℝ) ^ (-(δ / 3)) := by
    rw [neg_div, Real.rpow_neg hj0.le]; field_simp
  rw [e] at htj
  have hd := hdiff j
  rw [add_comm n j] at hd
  have := abs_sub_abs_le_abs_sub (t n) (t (j + n))
  linarith

theorem Dsum_critica_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hη : 0 < η) (hZ : SinCerosDerecha θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ x : ℝ,
      ‖Dsum Q (1 / 2 + (x : ℂ) * I)‖ ≤ K * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by
  obtain ⟨C, hC⟩ := balazard_saias_theta hθ hδ hθδ hη hZ
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound_theta hθ hδ hθδ hη hZ
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    simp at h1; exact le_trans (norm_nonneg _) (by linarith)
  refine ⟨4 * (CZ + C), by positivity, fun Q hQ x => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set v : ℝ := θ - 1 / 2 + δ with hv
  have hv0 : 0 < v := by simp only [v]; linarith
  have hv1 : v ≤ 1 := by simp only [v]; linarith
  set s₀ : ℂ := ((θ + δ : ℝ) : ℂ) + (x : ℂ) * I with hs₀
  have hs₀re : s₀.re = θ + δ := by simp [hs₀]
  have hs₀im : s₀.im = x := by simp [hs₀]
  set M : ℝ := (CZ + C) * (1 + |x|) ^ η with hM
  have hM0 : 0 ≤ M := by positivity
  have hA : ∀ d : ℕ, ‖Dsum d s₀‖ ≤ M := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp [Dsum, hM0]
    have h1 := hC d hd s₀ (by rw [hs₀re])
    rw [hs₀im] at h1
    have h2 := hCZ s₀ (by rw [hs₀re])
    rw [hs₀im] at h2
    have h3 : (d : ℝ) ^ (-δ / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    calc ‖Dsum d s₀‖ ≤ ‖Dsum d s₀ - Zinv s₀‖ + ‖Zinv s₀‖ := norm_le_norm_sub_add _ _
      _ ≤ C * (d : ℝ) ^ (-δ / 3) * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := add_le_add h1 h2
      _ ≤ C * 1 * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := by gcongr
      _ = M := by rw [hM]; ring
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ v with hg
  have hginc : ∀ d : ℕ, g d ≤ g (d + 1) := fun d =>
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by push_cast; linarith) hv0.le
  have hterm : ∀ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 / 2 + (x : ℂ) * I))
      = (((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s₀)) * (g d : ℂ) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    simp only [hg]
    rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc, ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
    congr 2; rw [hs₀]; simp only [v]; push_cast; ring
  have hab : Dsum Q (1 / 2 + (x : ℂ) * I)
      = Dsum Q s₀ * (g (Q + 1) : ℂ) + ∑ d ∈ Finset.Icc 1 Q, Dsum d s₀ * ((g d : ℂ) - g (d + 1)) := by
    unfold Dsum; rw [Finset.sum_congr rfl hterm, abel_Icc]
  have htel : ∑ d ∈ Finset.Icc 1 Q, (g (d + 1) - g d) = g (Q + 1) - 1 := by
    have := telescopio_Ioc (fun d => -g d) (n := 0) Q
    rw [show Finset.Icc 1 Q = Finset.Ioc 0 Q from Finset.Icc_add_one_left_eq_Ioc 0 Q]
    simp only [zero_add] at this
    have hg1 : g 1 = 1 := by simp [hg]
    rw [hg1] at this
    linarith [this, show ∑ d ∈ Finset.Ioc 0 Q, (g (d + 1) - g d)
      = ∑ d ∈ Finset.Ioc 0 Q, (-g d - -g (d + 1)) from Finset.sum_congr rfl fun d _ => by ring]
  have hgQ : g (Q + 1) ≤ 2 * (Q : ℝ) ^ v := by
    simp only [hg]
    calc ((Q + 1 : ℕ) : ℝ) ^ v ≤ (2 * (Q : ℝ)) ^ v :=
          Real.rpow_le_rpow (by positivity) (by push_cast; linarith [show (1 : ℝ) ≤ Q by exact_mod_cast hQ]) hv0.le
      _ = 2 ^ v * (Q : ℝ) ^ v := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ 2 * (Q : ℝ) ^ v := by
          gcongr
          calc (2 : ℝ) ^ v ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hv1
            _ = 2 := Real.rpow_one 2
  have hg0 : ∀ d, 0 ≤ g d := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  rw [hab]
  calc ‖Dsum Q s₀ * (g (Q + 1) : ℂ) + ∑ d ∈ Finset.Icc 1 Q, Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖
      ≤ ‖Dsum Q s₀ * (g (Q + 1) : ℂ)‖
        + ∑ d ∈ Finset.Icc 1 Q, ‖Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖ :=
        le_trans (norm_add_le _ _) (by gcongr; exact norm_sum_le _ _)
    _ ≤ M * g (Q + 1) + ∑ d ∈ Finset.Icc 1 Q, M * (g (d + 1) - g d) := by
        gcongr with d _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
          exact mul_le_mul_of_nonneg_right (hA Q) (hg0 _)
        · rw [norm_mul, show ((g d : ℂ) - g (d + 1)) = ((g d - g (d + 1) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hginc d])]
          have := hA d; nlinarith [hginc d]
    _ = M * (2 * g (Q + 1) - 1) := by rw [← Finset.mul_sum, htel]; ring
    _ ≤ M * (4 * (Q : ℝ) ^ v) := by gcongr; linarith
    _ = 4 * (CZ + C) * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by rw [hM, hv]; ring

theorem P_recta_critica_theta {θ δ η : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hη : 0 < η) (hZ : SinCerosDerecha θ) :
    ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → ∀ x : ℝ,
      ‖P Q (1 / 2 + (x : ℂ) * I)‖ ≤ C * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by
  obtain ⟨KD, hKD0, hKD⟩ := Dsum_critica_theta hθ hδ hθδ hη hZ
  obtain ⟨Km, hKm0, hKm⟩ := m_bound_theta hθ hδ hθδ hZ
  obtain ⟨Kt, hKt0, hKt⟩ := t_bound_theta hθ hδ hθδ hZ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨KD + Km + 3 * Kt / Real.log 2, fun Q hQ x => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ0 : (0 : ℝ) < Q := by linarith
  set v : ℝ := θ - 1 / 2 + δ with hv
  have hv0 : 0 < v := by simp only [v]; linarith
  set s : ℂ := 1 / 2 + (x : ℂ) * I with hs
  have hsre : (-s).re = -(1 / 2) := by simp [hs]
  have hQs : ‖(Q : ℂ) ^ (-s)‖ = (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hsre]
  have h2Qs : ‖((2 * Q : ℕ) : ℂ) ^ (-s)‖ ≤ (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hsre]
    exact Real.rpow_le_rpow_of_nonpos hQ0 (by push_cast; linarith) (by norm_num)
  set β : ℝ := 1 - θ - 2 * δ / 3 with hβ
  have hexp : (Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Q : ℝ) ^ v := by
    have e : (Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ))
        = (Q : ℝ) ^ (θ - 1 / 2 + 2 * δ / 3) := by
      rw [mul_assoc, ← Real.rpow_add hQ0, ← Real.rpow_one_add' hQ0.le (by rw [hβ]; intro h; linarith)]
      congr 1; rw [hβ]; ring
    rw [e]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by simp only [v]; linarith)
  have hpow1 : 1 ≤ (1 + |x|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg x]) hη.le
  have hD := hKD Q (by omega) x
  have hm := hKm Q (by omega)
  have ht := hKt Q (by omega)
  have hP : P Q s = Dsum Q s - (Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)
      - ((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)) := rfl
  have hT2 : ‖(Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)‖ ≤ Km * (Q : ℝ) ^ v := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, hQs]
    calc (Q : ℝ) * |m Q| * (Q : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ (Q : ℝ) * (Km * (Q : ℝ) ^ (-β)) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = Km * ((Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ Km * (Q : ℝ) ^ v := by gcongr
  have hT3 : ‖((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖
      ≤ 3 * Kt / Real.log 2 * (Q : ℝ) ^ v := by
    have hg : |gam Q| ≤ (Q : ℝ) * (Kt * (Q : ℝ) ^ (-β)) / Real.log 2 := by
      unfold gam; rw [abs_div, abs_mul, abs_of_pos hQ0, abs_of_pos hl2]; gcongr
    have hinner : ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)‖ ≤ 3 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s)‖ + ‖(Q : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ ≤ 2 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) + (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [norm_mul, hQs]; gcongr; simp
        _ = 3 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |gam Q| * ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)‖
        ≤ ((Q : ℝ) * (Kt * (Q : ℝ) ^ (-β)) / Real.log 2) * (3 * (Q : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hg hinner (norm_nonneg _) (by positivity)
      _ = 3 * Kt / Real.log 2 * ((Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 3 * Kt / Real.log 2 * (Q : ℝ) ^ v := by gcongr
  rw [hP]
  calc ‖Dsum Q s - (Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)
        - ((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖
      ≤ ‖Dsum Q s‖ + ‖(Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)‖
        + ‖((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖ :=
        le_trans (norm_sub_le _ _) (by gcongr; exact norm_sub_le _ _)
    _ ≤ KD * (Q : ℝ) ^ v * (1 + |x|) ^ η + Km * (Q : ℝ) ^ v * (1 + |x|) ^ η
        + 3 * Kt / Real.log 2 * (Q : ℝ) ^ v * (1 + |x|) ^ η := by
        gcongr
        all_goals first
          | exact hD
          | exact le_trans hT2 (le_mul_of_one_le_right (by positivity) hpow1)
          | exact le_trans hT3 (le_mul_of_one_le_right (by positivity) hpow1)
    _ = (KD + Km + 3 * Kt / Real.log 2) * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by
        rw [hv]; ring

/-- **Estado 45, `(6.4)`:** si `1/2 ≤ θ < 1` y `ζ` no tiene ceros en `Re s > θ`, entonces para todo
`ε > 0` existe `C` tal que `E_Q ≤ C Q^{2θ − 1 + ε}` para todo `Q ≥ 2`. -/
theorem energia_cota_theta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hZ : SinCerosDerecha θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  intro ε hε
  set δ : ℝ := min (ε / 2) ((1 - θ) / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by linarith)
  have hθδ : θ + δ < 1 := by
    have : δ ≤ (1 - θ) / 2 := min_le_right _ _
    linarith
  set v : ℝ := θ - 1 / 2 + δ
  have hv0 : 0 < v := by simp only [v]; linarith
  have h2v_le : 2 * v ≤ 2 * θ - 1 + ε := by
    have : δ ≤ ε / 2 := min_le_left _ _
    simp only [v]; linarith
  obtain ⟨Cζ, hCζ⟩ := zeta_recta_critica
  obtain ⟨CP, hCP⟩ := P_recta_critica_theta hθ hδ hθδ (show (0 : ℝ) < 1 / 8 by norm_num) hZ
  set K : ℝ := Cζ ^ 2 * CP ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hint1 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hint2 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(13 / 12 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set I₁ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))
  set I₂ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(13 / 12 : ℝ))
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun x => by positivity
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun x => by positivity
  refine ⟨(16 * I₁ + 16 * K * I₂) / (2 * Real.pi), fun Q hQ => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ2v : (Q : ℝ) ^ (2 * v) ≤ (Q : ℝ) ^ (2 * θ - 1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h2v_le
  have hQ2v1 : 1 ≤ (Q : ℝ) ^ (2 * v) := Real.one_le_rpow hQ1 (by positivity)
  rw [E_eq_integral hQ]
  set g : ℝ → ℝ := fun x => 16 * (1 + ‖x‖) ^ (-(2 : ℝ))
    + 16 * K * (Q : ℝ) ^ (2 * v) * (1 + ‖x‖) ^ (-(13 / 12 : ℝ))
  have hgint : Integrable g := (hint1.const_mul 16).add (hint2.const_mul _)
  have hpt : ∀ x : ℝ,
      ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2)
        ≤ g x := by
    intro x
    set y : ℝ := 1 + |x|
    have hy0 : 0 < y := by positivity
    set z := riemannZeta (1 / 2 + (x : ℂ) * I)
    set p := P Q (1 / 2 + (x : ℂ) * I)
    have hζ2 : ‖z‖ ^ 2 ≤ Cζ ^ 2 * y ^ (2 / 3 : ℝ) := by
      have e : (y ^ (1 / 3 : ℝ)) ^ 2 = y ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
      calc ‖z‖ ^ 2 ≤ (Cζ * y ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCζ x) 2
        _ = Cζ ^ 2 * y ^ (2 / 3 : ℝ) := by rw [mul_pow, e]
    have hP2 : ‖p‖ ^ 2 ≤ CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ) := by
      have e1 : ((Q : ℝ) ^ v) ^ 2 = (Q : ℝ) ^ (2 * v) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
      have e2 : (y ^ (1 / 8 : ℝ)) ^ 2 = y ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
      calc ‖p‖ ^ 2 ≤ (CP * (Q : ℝ) ^ v * y ^ (1 / 8 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hCP Q hQ x) 2
        _ = CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ) := by rw [mul_pow, mul_pow, e1, e2]
    have hprod : ‖z‖ ^ 2 * ‖p‖ ^ 2 ≤ K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ) := by
      have e : y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ) = y ^ (11 / 12 : ℝ) := by
        rw [← Real.rpow_add hy0]; norm_num
      calc ‖z‖ ^ 2 * ‖p‖ ^ 2
          ≤ (Cζ ^ 2 * y ^ (2 / 3 : ℝ)) * (CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ)) :=
            mul_le_mul hζ2 hP2 (by positivity) (by positivity)
        _ = K * (Q : ℝ) ^ (2 * v) * (y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ)) := by simp only [K]; ring
        _ = K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ) := by rw [e]
    have hnum : ‖1 - z * p‖ ^ 2 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ)) := by
      have h1 : ‖1 - z * p‖ ≤ 1 + ‖z‖ * ‖p‖ := by
        calc ‖1 - z * p‖ ≤ ‖(1 : ℂ)‖ + ‖z * p‖ := norm_sub_le _ _
          _ = 1 + ‖z‖ * ‖p‖ := by rw [norm_one, norm_mul]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (1 + ‖z‖ * ‖p‖) ^ 2 ≤ 2 + 2 * (‖z‖ ^ 2 * ‖p‖ ^ 2) := by
        nlinarith [sq_nonneg (‖z‖ * ‖p‖ - 1)]
      linarith
    have hden : y ^ 2 / 8 ≤ 1 / 4 + x ^ 2 := by
      simp only [y]; nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
    have hy2 : 0 < y ^ 2 / 8 := by positivity
    have hB0 : 0 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ)) := by positivity
    have hnx : (1 + ‖x‖) = y := by rw [Real.norm_eq_abs]
    calc ‖1 - z * p‖ ^ 2 / (1 / 4 + x ^ 2)
        ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ))) / (1 / 4 + x ^ 2) := by gcongr
      _ ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ))) / (y ^ 2 / 8) :=
          div_le_div_of_nonneg_left hB0 hy2 hden
      _ = 16 * (y ^ 2)⁻¹ + 16 * K * (Q : ℝ) ^ (2 * v) * (y ^ (11 / 12 : ℝ) / y ^ 2) := by
          field_simp; ring
      _ = g x := by
          simp only [g, hnx]
          rw [Real.rpow_neg hy0.le, Real.rpow_two, ← Real.rpow_two y,
            show -(13 / 12 : ℝ) = 11 / 12 - 2 by norm_num, Real.rpow_sub hy0]
  have hf0 : ∀ x : ℝ, 0 ≤
      ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2) :=
    fun _ => by positivity
  have hmono := integral_mono_of_nonneg (Eventually.of_forall hf0) hgint (Eventually.of_forall hpt)
  have hgval : ∫ x : ℝ, g x = 16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂ := by
    simp only [g]
    rw [integral_add (hint1.const_mul 16) (hint2.const_mul _), integral_const_mul, integral_const_mul]
  rw [hgval] at hmono
  calc 1 / (2 * Real.pi) * ∫ x : ℝ,
        ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2)
      ≤ 1 / (2 * Real.pi) * (16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂) := by gcongr
    _ ≤ 1 / (2 * Real.pi) * ((16 * I₁ + 16 * K * I₂) * (Q : ℝ) ^ (2 * θ - 1 + ε)) := by
        gcongr
        have : (16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂)
            ≤ (16 * I₁ + 16 * K * I₂) * (Q : ℝ) ^ (2 * v) := by
          nlinarith [mul_nonneg hK0 hI₂0]
        exact this.trans (mul_le_mul_of_nonneg_left hQ2v (by positivity))
    _ = (16 * I₁ + 16 * K * I₂) / (2 * Real.pi) * (Q : ℝ) ^ (2 * θ - 1 + ε) := by ring

/-- Equivalencia bilateral general en `θ ∈ [1/2, 1)` (Estado 45, §1 y `(6.4)`):
`SinCerosDerecha θ ↔ ∀ ε > 0, ∃ C, ∀ Q ≥ 2, E_Q ≤ C Q^{2θ − 1 + ε}`. -/
theorem sin_ceros_iff_energia_theta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SinCerosDerecha θ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  refine ⟨energia_cota_theta hθ hθ1, fun h => sin_ceros_de_energia_cofinal hθ fun ε hε => ?_⟩
  obtain ⟨C, hC⟩ := h ε hε
  exact ⟨C, fun Q₀ => ⟨max Q₀ 2, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩

theorem sin_ceros_iff_energia_cofinal_theta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SinCerosDerecha θ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧ E Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  refine ⟨fun hZ ε hε => ?_, sin_ceros_de_energia_cofinal hθ⟩
  obtain ⟨C, hC⟩ := energia_cota_theta hθ hθ1 hZ ε hε
  exact ⟨C, fun Q₀ => ⟨max Q₀ 2, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩

/-! ### Abscisa suprema `Theta_zeta` y teorema límite incondicional `(1.1)` del Estado 45 -/

/-- Conjunto de partes reales de los ceros no triviales de `ζ` en `0 < Re ρ < 1`. -/
def CerosRealesZeta : Set ℝ :=
  {x : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = x}

/-- Abscisa crítica `Θ_ζ = sup ({1/2} ∪ {Re ρ : ζ(ρ) = 0, 0 < Re ρ < 1})`. -/
noncomputable def Theta_zeta : ℝ := sSup (insert (1 / 2 : ℝ) CerosRealesZeta)

theorem bddAbove_insert_cerosRealesZeta : BddAbove (insert (1 / 2 : ℝ) CerosRealesZeta) := by
  refine ⟨1, fun x hx => ?_⟩
  rcases hx with rfl | ⟨ρ, -, -, h1, rfl⟩
  · norm_num
  · exact h1.le

theorem Theta_zeta_mem_Icc : 1 / 2 ≤ Theta_zeta ∧ Theta_zeta ≤ 1 := by
  refine ⟨le_csSup bddAbove_insert_cerosRealesZeta (mem_insert _ _),
    csSup_le (insert_nonempty _ _) fun x hx => ?_⟩
  rcases hx with rfl | ⟨ρ, -, -, h1, rfl⟩
  · norm_num
  · exact h1.le

/-- Por la simetría funcional `ρ ↦ 1 − ρ`, en cuanto `CerosRealesZeta` es no vacío, `Theta_zeta`
coincide exactamente con `sSup CerosRealesZeta`. -/
theorem Theta_zeta_eq_sSup_of_nonempty (hne : CerosRealesZeta.Nonempty) :
    Theta_zeta = sSup CerosRealesZeta := by
  have hbdd : BddAbove CerosRealesZeta :=
    bddAbove_insert_cerosRealesZeta.mono (subset_insert _ _)
  unfold Theta_zeta
  apply le_antisymm
  · refine csSup_le (insert_nonempty _ _) fun x hx => ?_
    rcases hx with rfl | hxC
    · obtain ⟨y, ρ, hζ0, h0, h1, rfl⟩ := hne
      rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
      · exact hge.trans (le_csSup hbdd ⟨ρ, hζ0, h0, h1, rfl⟩)
      · -- `1 - ρ` es cero no trivial con `Re(1 - ρ) > 1/2`.
        have hs0 : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
        have hs1 : ρ ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
        have hnot_neg : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
          intro n h; rw [h] at h0; simp at h0; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
        have hfe := riemannZeta_one_sub hnot_neg hs1
        rw [hζ0, mul_zero] at hfe
        have hmem : 1 - ρ.re ∈ CerosRealesZeta :=
          ⟨1 - ρ, hfe, by simp; linarith, by simp; linarith, by simp⟩
        exact (by linarith : (1 / 2 : ℝ) ≤ 1 - ρ.re).trans (le_csSup hbdd hmem)
    · exact le_csSup hbdd hxC
  · exact csSup_le_csSup bddAbove_insert_cerosRealesZeta hne (subset_insert _ _)

theorem sinCerosDerecha_of_gt_Theta_zeta {θ : ℝ} (hgt : Theta_zeta < θ) :
    SinCerosDerecha θ := by
  intro ρ hρ hζ0
  have h12 : 1 / 2 < ρ.re := lt_of_le_of_lt Theta_zeta_mem_Icc.1 (lt_trans hgt hρ)
  rcases le_or_gt 1 ρ.re with hge1 | hlt1
  · exact riemannZeta_ne_zero_of_one_le_re hge1 hζ0
  · have hmem : ρ.re ∈ insert (1 / 2 : ℝ) CerosRealesZeta :=
      Or.inr ⟨ρ, hζ0, by linarith, hlt1, rfl⟩
    have hle : ρ.re ≤ Theta_zeta := le_csSup bddAbove_insert_cerosRealesZeta hmem
    linarith

theorem Theta_zeta_eq_half_iff_rh : Theta_zeta = 1 / 2 ↔ RiemannHypothesis := by
  rw [← sinCerosDerecha_half_iff_rh]
  constructor
  · intro heq ρ hρ
    exact sinCerosDerecha_of_gt_Theta_zeta (θ := (1 / 2 + ρ.re) / 2)
      (by rw [heq]; linarith) ρ (by linarith)
  · intro hZ
    apply le_antisymm _ Theta_zeta_mem_Icc.1
    refine csSup_le (insert_nonempty _ _) fun x hx => ?_
    rcases hx with rfl | ⟨ρ, hζ0, -, -, rfl⟩
    · exact le_rfl
    · by_contra! hgt
      exact hZ ρ hgt hζ0

theorem E_nonneg (Q : ℕ) : 0 ≤ E Q :=
  tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (by unfold w; positivity)

/-- **Teorema límite incondicional del Estado 45, `(1.1)`:**
sin asumir `RiemannHypothesis` ni resultados externos,
`lim_{Q → ∞} log(2 + E_Q) / log Q = 2 Θ_ζ − 1`. -/
theorem tendsto_log_energia_div_log :
    Tendsto (fun Q : ℕ => Real.log (2 + E Q) / Real.log (Q : ℝ))
      atTop (𝓝 (2 * Theta_zeta - 1)) := by
  rw [tendsto_order]
  have hΘ_lo := Theta_zeta_mem_Icc.1
  have hΘ_hi := Theta_zeta_mem_Icc.2
  constructor
  · -- Cota inferior asintótica: para todo `a < 2 Θ_ζ − 1`, eventualmente `a < log(2 + E_Q)/log Q`.
    intro a ha
    set ε : ℝ := (2 * Theta_zeta - 1) - a
    have hε : 0 < ε := sub_pos.mpr ha
    rcases le_or_gt Theta_zeta (1 / 2 + ε / 4) with hsmall | hbig
    · filter_upwards [eventually_ge_atTop 2] with Q hQ
      have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
      have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
      have h2E : 1 ≤ 2 + E Q := by linarith [E_nonneg Q]
      have hnn : 0 ≤ Real.log (2 + E Q) / Real.log (Q : ℝ) :=
        div_nonneg (Real.log_nonneg h2E) hlogQ_pos.le
      have ha_neg : a < 0 := by simp only [ε] at hsmall; linarith
      exact lt_of_lt_of_le ha_neg hnn
    · have hlt_sup : max (1 / 2) (Theta_zeta - ε / 4) < Theta_zeta :=
        max_lt (by linarith) (by linarith)
      obtain ⟨x, hx_mem, hx_gt⟩ :=
        (lt_csSup_iff bddAbove_insert_cerosRealesZeta (insert_nonempty _ _)).mp hlt_sup
      have hx_ne : x ≠ 1 / 2 := by
        have := (max_lt_iff.mp hx_gt).1; linarith
      rcases hx_mem with rfl | ⟨ρ, hζ0, -, -, rfl⟩
      · exact absurd rfl hx_ne
      · have hβ_gt12 : 1 / 2 < ρ.re := (max_lt_iff.mp hx_gt).1
        have hβ_gtΘ : Theta_zeta - ε / 4 < ρ.re := (max_lt_iff.mp hx_gt).2
        have hρ_ne0 : ρ ≠ 0 := by intro h; rw [h] at hβ_gt12; simp at hβ_gt12; linarith
        set c₀ : ℝ := (2 * ρ.re - 1) / ‖ρ‖ ^ 2
        have hc₀_pos : 0 < c₀ := div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hρ_ne0))
        have hdiv0 : Tendsto (fun Q : ℕ => Real.log c₀ / Real.log (Q : ℝ)) atTop (𝓝 0) := by
          have hlog_top : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          simpa using tendsto_const_nhds.div_atTop hlog_top
        have hev_c := (tendsto_order.mp hdiv0).1 (-(ε / 2)) (by linarith)
        filter_upwards [eventually_ge_atTop 2, hev_c] with Q hQ hlog_c
        have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
        have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
        have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
        have hlow := cota_inferior_energia_cero hζ0 hβ_gt12 hQ
        have hmul := mul_le_mul_of_nonneg_right hlow
          (Real.rpow_nonneg hQ_pos.le (2 * ρ.re - 1))
        have hrp : (Q : ℝ) ^ (1 - 2 * ρ.re) * (Q : ℝ) ^ (2 * ρ.re - 1) = 1 := by
          rw [← Real.rpow_add hQ_pos, show (1 - 2 * ρ.re) + (2 * ρ.re - 1) = 0 by ring,
            Real.rpow_zero]
        rw [mul_assoc, hrp, mul_one] at hmul
        have h2E_gt : c₀ * (Q : ℝ) ^ (2 * ρ.re - 1) < 2 + E Q := by
          change c₀ * (Q : ℝ) ^ (2 * ρ.re - 1) ≤ E Q at hmul
          linarith
        have hlog_le := Real.log_le_log (by positivity) h2E_gt.le
        rw [Real.log_mul hc₀_pos.ne' (Real.rpow_pos_of_pos hQ_pos _).ne',
          Real.log_rpow hQ_pos] at hlog_le
        have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
        rw [add_div, mul_div_cancel_right₀ _ hlogQ_pos.ne'] at hdiv_le
        simp only [ε] at hβ_gtΘ hlog_c
        linarith
  · -- Cota superior asintótica: para todo `b > 2 Θ_ζ − 1`, eventualmente `log(2 + E_Q)/log Q < b`.
    intro b hb
    set ε : ℝ := b - (2 * Theta_zeta - 1)
    have hε : 0 < ε := sub_pos.mpr hb
    have hlog_top : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    rcases eq_or_lt_of_le hΘ_hi with hΘ_eq1 | hΘ_lt1
    · -- Caso `Θ_ζ = 1`: `E_Q ≤ C_lin Q` por `E_le_lineal`.
      set C_lin : ℝ := 2 + 8 * (1 + 1 / Real.log 2)
      have hClin_pos : 0 < C_lin := by
        have : 0 < Real.log 2 := Real.log_pos (by norm_num)
        simp only [C_lin]; positivity
      have hdiv0 : Tendsto (fun Q : ℕ => Real.log C_lin / Real.log (Q : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop hlog_top
      have hev := (tendsto_order.mp hdiv0).2 (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop 2, hev] with Q hQ hlog_c
      have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      have hlogQ_pos : 0 < Real.log (Q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
      have hE := E_le_lineal hQ
      have h2E : 2 + E Q ≤ C_lin * (Q : ℝ) := by simp only [C_lin]; nlinarith
      have hlog_le := Real.log_le_log (by linarith [E_nonneg Q]) h2E
      rw [Real.log_mul hClin_pos.ne' hQ_pos.ne'] at hlog_le
      have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
      rw [add_div, div_self hlogQ_pos.ne'] at hdiv_le
      simp only [ε] at hlog_c
      linarith
    · -- Caso `Θ_ζ < 1`: aplicamos `energia_cota_theta` en `θ' ∈ (Θ_ζ, 1)`.
      set θ' : ℝ := min (Theta_zeta + ε / 4) ((Theta_zeta + 1) / 2)
      have hθ'_gt : Theta_zeta < θ' := lt_min (by linarith) (by linarith)
      have hθ'_lt1 : θ' < 1 := (min_le_right _ _).trans_lt (by linarith)
      have hθ'_ge12 : 1 / 2 ≤ θ' := hΘ_lo.trans hθ'_gt.le
      have hθ'_le : θ' ≤ Theta_zeta + ε / 4 := min_le_left _ _
      obtain ⟨C, hC⟩ := energia_cota_theta hθ'_ge12 hθ'_lt1
        (sinCerosDerecha_of_gt_Theta_zeta hθ'_gt) (ε / 4) (by positivity)
      set C_up : ℝ := 2 + max C 0
      have hCup_pos : 0 < C_up := by simp only [C_up]; positivity
      have hdiv0 : Tendsto (fun Q : ℕ => Real.log C_up / Real.log (Q : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop hlog_top
      have hev := (tendsto_order.mp hdiv0).2 (ε / 8) (by positivity)
      filter_upwards [eventually_ge_atTop 2, hev] with Q hQ hlog_c
      have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      have hlogQ_pos : 0 < Real.log (Q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
      set p_exp : ℝ := 2 * θ' - 1 + ε / 4
      have hp_nn : 0 ≤ p_exp := by simp only [p_exp]; linarith
      have hp_le : p_exp ≤ 2 * Theta_zeta - 1 + 3 * ε / 4 := by simp only [p_exp]; linarith
      have hQp_ge1 : 1 ≤ (Q : ℝ) ^ p_exp := Real.one_le_rpow hQ1 hp_nn
      have hEQ := hC Q hQ
      have h2E : 2 + E Q ≤ C_up * (Q : ℝ) ^ p_exp := by
        have hC_max : C * (Q : ℝ) ^ p_exp ≤ max C 0 * (Q : ℝ) ^ p_exp :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hQ_pos.le _)
        simp only [C_up]; nlinarith
      have hlog_le := Real.log_le_log (by linarith [E_nonneg Q]) h2E
      rw [Real.log_mul hCup_pos.ne' (Real.rpow_pos_of_pos hQ_pos _).ne',
        Real.log_rpow hQ_pos] at hlog_le
      have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
      rw [add_div, mul_div_cancel_right₀ _ hlogQ_pos.ne'] at hdiv_le
      simp only [ε] at hp_le hlog_c
      linarith

end AMate
