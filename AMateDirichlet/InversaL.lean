import AMateEnergia.InversaZeta
import AMateDirichlet.Testigo

/-!
# Cota de `1/L(s,χ)` en un semiplano sin ceros

Análogo para `χ ≠ 1` de la primera mitad del lema de Balazard–Saias (`AMateEnergia.InversaZeta` y
`inv_and_logDeriv_zeta_bound_theta`). Como `L(s,χ)` es entera, no hay polo en `s = 1`.

* `SinCerosDerechaL χ θ`: `L(s,χ)` no se anula en `Re s > θ`.
* `L_bounds_of_one_lt`, `logDeriv_L_bound`: `L`, `1/L` y `L'/L` acotadas en `Re s ≥ σ₀ > 1`
  (series de `χ`, de `μ χ` y de `Λ χ`).
* `norm_LFunction_le`: `‖L(s,χ)‖ ≤ N ‖s‖ / Re s` para `Re s > 0`, de
  `L(s,χ) = s ∫_1^∞ S_χ(⌊x⌋) x^{−s−1} dx` y `‖S_χ‖ ≤ N`.
* `inv_L_bound_theta`: bajo `SinCerosDerechaL χ θ` (`1/2 ≤ θ`), `‖1/L(s,χ)‖ ≤ C |Im s|^η` en
  `Re s ≥ θ + δ`, `|Im s| ≥ 4`: logaritmo holomorfo en el disco de centro `2 + it`,
  Borel–Carathéodory y tres círculos.
* `Linv_bound_theta`: `‖1/L(s,χ)‖ ≤ C (1 + |Im s|)^η` en todo `Re s ≥ θ + δ`.
-/

open Complex Metric Set MeasureTheory

namespace AMate.Dirichlet

variable {N : ℕ} [NeZero N]

/-- Ausencia de ceros de `L(s,χ)` en el semiplano abierto `Re s > θ`. -/
def SinCerosDerechaL (χ : DirichletCharacter ℂ N) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0

theorem sinCerosDerechaL_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    SinCerosDerechaL χ 1 :=
  fun _ hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le

/-! ### Cotas en `Re s > 1` -/

/-- Para `Re s ≥ σ₀ > 1`, `‖L(s,χ)‖` y `‖1/L(s,χ)‖` están acotados. -/
theorem L_bounds_of_one_lt (χ : DirichletCharacter ℂ N) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ S : ℝ, ∀ s : ℂ, σ₀ ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ S ∧ ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ S := by
  have hre : 1 < (σ₀ : ℂ).re := by simpa using hσ₀
  have hχs := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hre
  have hμs := DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hre)
  have h1 := summable_norm_iff.mpr hχs
  have hμ := summable_norm_iff.mpr hμs
  have hn1 : 0 ≤ ∑' n, ‖LSeries.term (fun n : ℕ => χ n) σ₀ n‖ :=
    tsum_nonneg fun n => norm_nonneg _
  have hnμ : 0 ≤ ∑' n, ‖LSeries.term
      ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.moebius n : ℂ)) σ₀ n‖ :=
    tsum_nonneg fun n => norm_nonneg _
  refine ⟨(∑' n, ‖LSeries.term (fun n : ℕ => χ n) σ₀ n‖) + ∑' n, ‖LSeries.term
      ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.moebius n : ℂ)) σ₀ n‖,
    fun s hs => ⟨?_, ?_⟩⟩
  · have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
    exact (norm_LSeries_le_of_re h1 hs).trans (le_add_of_nonneg_right hnμ)
  · have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1,
      inv_eq_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hs1)]
    exact (norm_LSeries_le_of_re hμ hs).trans (le_add_of_nonneg_left hn1)

/-- Para `Re s ≥ σ₀ > 1`, `‖L'(s,χ)/L(s,χ)‖` está acotado. -/
theorem logDeriv_L_bound (χ : DirichletCharacter ℂ N) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ∃ B : ℝ, ∀ s : ℂ, σ₀ ≤ s.re →
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ B := by
  have hre : 1 < (σ₀ : ℂ).re := by simpa using hσ₀
  have hsum := summable_norm_iff.mpr (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hre)
  refine ⟨∑' n, ‖LSeries.term
      ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ₀ n‖,
    fun s hs => ?_⟩
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ₀ hs
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs1
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1,
    DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have h' : deriv (LSeries fun n : ℕ => χ n) s / LSeries (fun n : ℕ => χ n) s
      = -LSeries ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [h, neg_div, neg_neg]
  rw [h', norm_neg]
  exact norm_LSeries_le_of_re hsum hs

/-! ### Cota elemental en `Re s > 0` -/

/-- `‖L(s,χ)‖ ≤ N ‖s‖ / Re s` para `Re s > 0` y `χ ≠ 1`. -/
theorem norm_LFunction_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z : ℂ} (hz : 0 < z.re) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ N * ‖z‖ / z.re := by
  rw [LFunction_eq_integral hχ hz, norm_mul]
  have hint : IntegrableOn (fun x : ℝ => (N : ℝ) * x ^ (-z.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hle : ‖∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-z - 1)‖
      ≤ ∫ x in Ioi (1 : ℝ), (N : ℝ) * x ^ (-z.re - 1) := by
    refine norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-z - 1).re = -z.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (norm_S_le hχ _) (Real.rpow_nonneg hx0.le _)
  have hval : ∫ x in Ioi (1 : ℝ), (N : ℝ) * x ^ (-z.re - 1) = N / z.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos]
    rw [show -z.re - 1 + 1 = -z.re by ring, Real.one_rpow]
    field_simp
  rw [hval] at hle
  calc ‖z‖ * ‖∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-z - 1)‖ ≤ ‖z‖ * (N / z.re) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = N * ‖z‖ / z.re := by ring

/-! ### Cota de `1/L` en `Re s ≥ θ + δ` -/

set_option maxHeartbeats 1600000 in
/-- Bajo `SinCerosDerechaL χ θ` (`1/2 ≤ θ < 1`), en `Re s ≥ θ + δ` y `|Im s| ≥ 4`,
`‖1/L(s,χ)‖ ≤ C |Im s|^η`. -/
theorem inv_L_bound_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ η : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1) (hη : 0 < η) (hZ : SinCerosDerechaL χ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, θ + δ ≤ s.re → 4 ≤ |s.im| →
      ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ C * |s.im| ^ η := by
  set Lf := DirichletCharacter.LFunction χ with hLf
  obtain ⟨S, hS⟩ := L_bounds_of_one_lt χ (show (1 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨B, hB⟩ := logDeriv_L_bound χ (show (1 : ℝ) < 3 / 2 by norm_num)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hne2 : Lf 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hS1 : 1 ≤ S := by
    obtain ⟨ha, hb⟩ := hS 2 (by norm_num)
    have hprod : ‖Lf 2‖ * ‖(Lf 2)⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hne2, norm_one]
    nlinarith [norm_nonneg (Lf 2), norm_nonneg (Lf 2)⁻¹]
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
  have hl5N : 0 ≤ Real.log (5 * N) := Real.log_nonneg (by linarith)
  set c₃ : ℝ := η * Real.log (5 * N) + η * (12 * K) / 16 + η * δ₁ / 16 + C₀ + A₀ with hc₃
  have hc₃0 : 0 ≤ c₃ := by simp only [c₃]; positivity
  set C_tot : ℝ := S + Real.exp c₃ with hC_tot
  refine ⟨C_tot, by positivity, fun s hsre hsim => ?_⟩
  set t := s.im with ht
  have ht0 : 0 < |t| := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have htη : 1 ≤ |t| ^ η := Real.one_le_rpow ht1 hη.le
  rcases le_or_gt (3 / 2) s.re with hbig | hsmall
  · calc ‖(Lf s)⁻¹‖ ≤ S := (hS s hbig).2
      _ ≤ C_tot * 1 := by simp only [C_tot]; have := Real.exp_pos c₃; linarith
      _ ≤ C_tot * |t| ^ η := by gcongr
  set s₀ : ℂ := 2 + (t : ℂ) * I with hs₀
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
  have hLne : ∀ z ∈ ball s₀ R, Lf z ≠ 0 :=
    fun z hz => hZ z (by linarith [(hball z hz).1])
  have hLdiff0 : DifferentiableOn ℂ Lf (ball s₀ R) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  obtain ⟨Lg, hLc, hLd, hLe⟩ := exists_log_ball hRpos hLdiff0 hLne
  have hLdiff : DifferentiableOn ℂ Lg (ball s₀ R) := fun z hz =>
    (hLd z hz).differentiableAt.differentiableWithinAt
  have hLs₀ : ‖Lg s₀‖ ≤ K := by
    rw [hLc]
    have h := hS s₀ (by rw [hs₀re]; norm_num)
    exact norm_log_le (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hs₀re]; norm_num)) h.1 h.2
  set M : ℝ := Real.log (5 * N * |t|) with hM
  have hMpos : 0 < M := Real.log_pos (by nlinarith)
  have hLre : ∀ z ∈ ball s₀ R, (Lg z).re ≤ M := by
    intro z hz
    obtain ⟨hre, him, hre4, him2⟩ := hball z hz
    have hz0 : 1 / 2 < z.re := by linarith
    have hnz : ‖z‖ ≤ |t| + 6 := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith)] at this; linarith
    have hL := norm_LFunction_le hχ (show 0 < z.re by linarith)
    have hq : (N : ℝ) * ‖z‖ / z.re ≤ 2 * N * ‖z‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg z, mul_nonneg (by linarith : (0 : ℝ) ≤ N) (norm_nonneg z)]
    have hLb : ‖Lf z‖ ≤ 5 * N * |t| := by
      have : 2 * (N : ℝ) * ‖z‖ ≤ 5 * N * |t| := by
        have h6 : ‖z‖ ≤ 5 / 2 * |t| := by linarith
        nlinarith
      linarith
    have hpos : 0 < ‖Lf z‖ := norm_pos_iff.mpr (hLne z hz)
    have hreL : (Lg z).re = Real.log ‖Lf z‖ := by
      rw [← hLe z hz, Complex.norm_exp, Real.log_exp]
    rw [hreL]; exact Real.log_le_log hpos hLb
  set b : ℝ := (16 * M + 12 * K) / δ₁ + 1 with hb
  have hb1 : 1 ≤ b := by
    have : 0 ≤ (16 * M + 12 * K) / δ₁ := by positivity
    linarith
  have hbound2 : ∀ z, ‖z - s₀‖ = r₂ → ‖Lg z‖ ≤ b := by
    intro z hz
    set f : ℂ → ℂ := fun w => Lg (s₀ + w) with hf
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
    have hfz : f (z - s₀) = Lg z := by simp only [hf, add_sub_cancel]
    have hf0 : f 0 = Lg s₀ := by simp only [hf, add_zero]
    rw [hfz, hf0, hz, show R - r₂ = δ₁ / 4 by rw [hR, hr₂]; ring] at hBC
    have hr₂2 : r₂ ≤ 2 := by linarith
    have hRr : R + r₂ ≤ 3 := by linarith
    have hnum : 2 * M * r₂ + ‖Lg s₀‖ * (R + r₂) ≤ 4 * M + 3 * K := by
      have e1 : M * r₂ ≤ M * 2 := mul_le_mul_of_nonneg_left hr₂2 hMpos.le
      have e2 : ‖Lg s₀‖ * (R + r₂) ≤ K * 3 := mul_le_mul hLs₀ hRr (by linarith) hK0
      linarith
    have hkey : 2 * M * r₂ / (δ₁ / 4) + ‖Lg s₀‖ * (R + r₂) / (δ₁ / 4)
        ≤ (16 * M + 12 * K) / δ₁ := by
      rw [← add_div, div_le_div_iff₀ (by positivity) hδ₁0]
      nlinarith [mul_le_mul_of_nonneg_right hnum hδ₁0.le]
    linarith
  have hbound_small : ∀ z, ‖z - s₀‖ ≤ 1 / 2 → ‖Lg z‖ ≤ A₀ := by
    intro z hz
    have hsub : closedBall s₀ (1 / 2) ⊆ ball s₀ R := closedBall_subset_ball (by linarith)
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Lg) (f' := fun x => deriv Lf x / Lf x) (C := B')
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
    have := norm_sub_norm_le (Lg z) (Lg s₀)
    have hmul_le : B' * ‖z - s₀‖ ≤ B' * (1 / 2) := mul_le_mul_of_nonneg_left hz hB'0
    linarith
  have hL_rint : ∀ w, ‖w - s₀‖ ≤ r_int → ‖Lg w‖ ≤ η * Real.log |t| + c₃ := by
    intro w hw_le
    have hbexp : η * δ₁ / 16 * b
        = η * Real.log |t| + (η * Real.log (5 * N) + η * (12 * K) / 16 + η * δ₁ / 16) := by
      rw [hb, hM, Real.log_mul (by positivity) ht0.ne']
      field_simp
      ring
    rcases le_or_gt ‖w - s₀‖ (1 / 2) with hle12 | hgt12
    · have h1 := hbound_small w hle12
      have hlog_nn : 0 ≤ η * Real.log |t| := mul_nonneg hη.le (Real.log_nonneg ht1)
      have : A₀ ≤ c₃ := by
        have : 0 ≤ η * Real.log (5 * N) + η * (12 * K) / 16 + η * δ₁ / 16 + C₀ := by positivity
        simp only [c₃]; linarith
      linarith
    · have h3 := three_circles (by norm_num : (0 : ℝ) < 1 / 2) (lt_trans hr_int_gt hr₂_gt)
        hR_gt hLdiff (fun z hz => hbound_small z hz.le) hbound2 hgt12.le
        (hw_le.trans hr₂_gt.le)
      set θw : ℝ := (Real.log ‖w - s₀‖ - Real.log (1 / 2)) / (Real.log r₂ - Real.log (1 / 2))
      have hθw0 : 0 ≤ θw :=
        div_nonneg (sub_nonneg.mpr (Real.log_le_log (by norm_num) hgt12.le)) hden.le
      have hθw_le : θw ≤ θ₀ := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact sub_le_sub_right (Real.log_le_log (by linarith) hw_le) _
      have hLw : ‖Lg w‖ ≤ A₀ * b ^ θ₀ := by
        calc ‖Lg w‖ ≤ A₀ ^ (1 - θw) * b ^ θw := h3
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
  have hLs : Lf s = Complex.exp (Lg s) := (hLe s hs_in_R).symm
  have hinv : ‖(Lf s)⁻¹‖ ≤ Real.exp (‖Lg s‖) := by
    rw [hLs, ← Complex.exp_neg, Complex.norm_exp, neg_re]
    exact Real.exp_le_exp.mpr (by linarith [neg_le_abs (Lg s).re, Complex.abs_re_le_norm (Lg s)])
  have htpow : |t| ^ η = Real.exp (η * Real.log |t|) := by
    rw [Real.rpow_def_of_pos ht0, mul_comm]
  have hLs_bd := hL_rint s hs_rint
  calc ‖(Lf s)⁻¹‖ ≤ Real.exp (‖Lg s‖) := hinv
    _ ≤ Real.exp (η * Real.log |t| + c₃) := Real.exp_le_exp.mpr hLs_bd
    _ = Real.exp c₃ * |t| ^ η := by rw [htpow, ← Real.exp_add]; ring_nf
    _ ≤ C_tot * |t| ^ η := by
        gcongr
        simp only [C_tot]
        linarith

theorem continuousOn_Linv_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hZ : SinCerosDerechaL χ θ) :
    ContinuousOn (fun z => (DirichletCharacter.LFunction χ z)⁻¹) {z | θ < z.re} :=
  ((DirichletCharacter.differentiable_LFunction hχ).continuous.continuousOn).inv₀
    fun z hz => hZ z hz

theorem differentiableOn_Linv_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hZ : SinCerosDerechaL χ θ) :
    DifferentiableOn ℂ (fun z => (DirichletCharacter.LFunction χ z)⁻¹) {z | θ < z.re} :=
  ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn).inv fun z hz => hZ z hz

/-- Bajo `SinCerosDerechaL χ θ`, `‖1/L(z,χ)‖ ≤ C (1 + |Im z|)^η` en `Re z ≥ θ + δ`. -/
theorem Linv_bound_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ η : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1) (hη : 0 < η) (hZ : SinCerosDerechaL χ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      ‖(DirichletCharacter.LFunction χ z)⁻¹‖ ≤ C * (1 + |z.im|) ^ η := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := inv_L_bound_theta hχ hθ hδ hθδ hη hZ
  obtain ⟨S, hS⟩ := L_bounds_of_one_lt χ (show (1 : ℝ) < 3 / 2 by norm_num)
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
  have hcont : ContinuousOn (fun z => (DirichletCharacter.LFunction χ z)⁻¹) Kset :=
    (continuousOn_Linv_theta hχ hZ).mono fun z hz => by
      show θ < z.re; linarith [hz.1]
  obtain ⟨K₀, hK₀⟩ := hKc.bddAbove_image hcont.norm
  refine ⟨C₁ + max S 0 + max K₀ 0, by positivity, fun z hz => ?_⟩
  have hpow : 1 ≤ (1 + |z.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg z.im]) hη.le
  rcases le_or_gt 4 |z.im| with him | him
  · calc ‖(DirichletCharacter.LFunction χ z)⁻¹‖ ≤ C₁ * |z.im| ^ η := hC₁ z hz him
      _ ≤ C₁ * (1 + |z.im|) ^ η :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hη.le) hC₁0
      _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by
          gcongr; linarith [le_max_right S 0, le_max_right K₀ 0]
  · rcases le_or_gt (3 / 2) z.re with hre | hre
    · calc ‖(DirichletCharacter.LFunction χ z)⁻¹‖ ≤ max S 0 :=
            le_trans (hS z hre).2 (le_max_left _ _)
        _ ≤ (C₁ + max S 0 + max K₀ 0) * 1 := by linarith [le_max_right K₀ 0]
        _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr
    · have hzK : z ∈ Kset := ⟨hz, hre.le, him.le⟩
      calc ‖(DirichletCharacter.LFunction χ z)⁻¹‖ ≤ max K₀ 0 :=
            le_trans (hK₀ ⟨z, hzK, rfl⟩) (le_max_left _ _)
        _ ≤ (C₁ + max S 0 + max K₀ 0) * 1 := by linarith [le_max_right S 0]
        _ ≤ (C₁ + max S 0 + max K₀ 0) * (1 + |z.im|) ^ η := by gcongr

end AMate.Dirichlet
