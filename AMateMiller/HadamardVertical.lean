import AMateMiller.HadamardRect

/-!
# La recta `Re s = 3/2` en la identidad de Hadamard

* `VM σ = ∑ Λ(n) n^{-σ}` y `norm_logDeriv_le_VM`: `|L'/L(s, χ)| ≤ VM(Re s)` para `Re s > 1`.
* `integral_Λd_G_eq_zero`: `∫ Λd(3/2 + iy, χ) G(3/2 + iy) dy = 0`, desplazando la recta a la
  derecha (`Contorno.integral_vertical_eq_zero`).
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- `VM σ = ∑ Λ(n)/n^σ`. -/
def VM (σ : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖

theorem summable_VM {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖ :=
  summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ))

theorem VM_nonneg (σ : ℝ) : 0 ≤ VM σ := tsum_nonneg fun _ => norm_nonneg _

theorem VM_anti {σ σ' : ℝ} (hσ : 1 < σ) (h : σ ≤ σ') : VM σ' ≤ VM σ :=
  Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using h) n)
    (summable_VM (hσ.trans_le h)) (summable_VM hσ)

variable {N : ℕ} [NeZero N]

/-- `L'/L(s, χ) = −L(χΛ, s)` para `Re s > 1`. -/
theorem logDeriv_eq_neg_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      -LSeries (fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have e : (fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (fun n : ℕ => (χ (n : ZMod N) : ℂ)) * fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) :=
    rfl
  rw [e, h]
  ring

/-- `|L'/L(s, χ)| ≤ VM(Re s)` para `Re s > 1`. -/
theorem norm_logDeriv_le_VM (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ VM s.re := by
  rw [logDeriv_eq_neg_LSeries χ hs, norm_neg]
  set f : ℕ → ℂ := fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hle : ∀ n, ‖LSeries.term f s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s.re : ℂ) n‖ := by
    intro n
    refine (LSeries.norm_term_le s ?_).trans (LSeries.norm_term_le_of_re_le_re _ (by simp) n)
    · show ‖χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum : Summable fun n => ‖LSeries.term f s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle (summable_VM hs)
  calc ‖LSeries f s‖ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ VM s.re := Summable.tsum_le_tsum hle hsum (summable_VM hs)

theorem ne_one_of_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h; rw [h] at hs; simp at hs

theorem L_sigma_ne' (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (ne_one_of_re hs)) hs.le

/-- `log y ≤ 2 √y`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Real.sqrt_eq_rpow]
  linarith

/-- Cota de `G` en `Re s ≥ 3/2`: `|G(s)| ≤ 8 (2σ − 1)/((3/2 − σ) |s − 1|²)`. -/
theorem norm_G_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖G σ s‖ ≤ 4 * (2 * σ - 1) / (3 / 2 - σ) * ‖s - 1‖⁻¹ ^ 2 := by
  have hd : 0 < 3 / 2 - σ := by linarith
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [le_abs_self (s.re - 1)]
  have hn1 : 0 < ‖s - 1‖ := by linarith
  have ha : ‖s - 1‖ ≤ 2 * ‖s - ((1 - σ : ℝ) : ℂ)‖ := by
    have h1 : ‖s - 1‖ ≤ ‖s - ((1 - σ : ℝ) : ℂ)‖ + σ := by
      have e2 : ‖((1 - σ : ℝ) : ℂ) - 1‖ = σ := by
        rw [show ((1 - σ : ℝ) : ℂ) - 1 = ((-σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
      have := norm_add_le (s - ((1 - σ : ℝ) : ℂ)) (((1 - σ : ℝ) : ℂ) - 1)
      rw [show s - ((1 - σ : ℝ) : ℂ) + (((1 - σ : ℝ) : ℂ) - 1) = s - 1 by ring, e2] at this
      exact this
    have h2 : σ ≤ ‖s - ((1 - σ : ℝ) : ℂ)‖ := by
      have := Complex.abs_re_le_norm (s - ((1 - σ : ℝ) : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith [le_abs_self (s.re - (1 - σ))]
    linarith
  have hb : ‖s - 1‖ ≤ (1 + (σ - 1) / (3 / 2 - σ)) * ‖s - (σ : ℂ)‖ := by
    have h1 : ‖s - 1‖ ≤ ‖s - (σ : ℂ)‖ + (σ - 1) := by
      have := norm_add_le (s - (σ : ℂ)) ((σ : ℂ) - 1)
      rw [show s - (σ : ℂ) + ((σ : ℂ) - 1) = s - 1 by ring,
        show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      exact this
    have h2 : 3 / 2 - σ ≤ ‖s - (σ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (s - (σ : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith [le_abs_self (s.re - σ)]
    have h3 : σ - 1 ≤ (σ - 1) / (3 / 2 - σ) * ‖s - (σ : ℂ)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      nlinarith
    nlinarith
  have hpa : 0 < ‖s - ((1 - σ : ℝ) : ℂ)‖ := by linarith
  have hpb : 0 < ‖s - (σ : ℂ)‖ := by
    have := Complex.abs_re_le_norm (s - (σ : ℂ)); rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [le_abs_self (s.re - σ)]
  have hG : G σ s = (((1 - σ : ℝ) : ℂ) - σ) / ((s - ((1 - σ : ℝ) : ℂ)) * (s - σ)) := by
    unfold G
    have a : s - ((1 - σ : ℝ) : ℂ) ≠ 0 := norm_pos_iff.mp hpa
    have b : s - (σ : ℂ) ≠ 0 := norm_pos_iff.mp hpb
    field_simp
    ring
  rw [hG, norm_div, norm_mul]
  have hnum : ‖((1 - σ : ℝ) : ℂ) - σ‖ = 2 * σ - 1 := by
    rw [show ((1 - σ : ℝ) : ℂ) - σ = ((1 - 2 * σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  rw [hnum]
  set K : ℝ := 1 + (σ - 1) / (3 / 2 - σ) with hK
  have hK1 : 1 ≤ K := by rw [hK]; have : 0 ≤ (σ - 1) / (3 / 2 - σ) := div_nonneg (by linarith) hd.le; linarith
  have hprod : ‖s - 1‖ ^ 2 ≤ 2 * K * (‖s - ((1 - σ : ℝ) : ℂ)‖ * ‖s - (σ : ℂ)‖) := by
    have := mul_le_mul ha hb (norm_nonneg _) (by positivity)
    nlinarith
  have hK2 : 2 * K ≤ 2 / (3 / 2 - σ) := by
    rw [hK, le_div_iff₀ hd]
    have : (σ - 1) / (3 / 2 - σ) * (3 / 2 - σ) = σ - 1 := div_mul_cancel₀ _ hd.ne'
    nlinarith
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2σ : 0 < 2 * σ - 1 := by linarith
  calc (2 * σ - 1) * ‖s - 1‖ ^ 2 ≤ (2 * σ - 1) * (2 * K * (‖s - ((1 - σ : ℝ) : ℂ)‖ * ‖s - (σ : ℂ)‖)) :=
        mul_le_mul_of_nonneg_left hprod h2σ.le
    _ ≤ (2 * σ - 1) * (2 / (3 / 2 - σ) * (‖s - ((1 - σ : ℝ) : ℂ)‖ * ‖s - (σ : ℂ)‖)) := by
        gcongr
    _ ≤ 4 * (2 * σ - 1) / (3 / 2 - σ) * (‖s - ((1 - σ : ℝ) : ℂ)‖ * ‖s - (σ : ℂ)‖) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc', le_div_iff₀ hd,
          div_mul_cancel₀ _ hd.ne']
        nlinarith [mul_pos hpa hpb]

/-- `|Λd(s)| ≤ |log(N/π)|/2 + (C/2) log(|s| + 3) + VM(3/2)` en `Re s ≥ 3/2`. -/
theorem norm_Λd_le_derecha {C : ℝ} (hC0 : 0 < C)
    (hD : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖Λd χ s‖ ≤ |Real.log (N / Real.pi)| / 2 + C / 2 * Real.log (‖s‖ + 3) + VM (3 / 2) := by
  have hpar := par_re_nonneg χ
  have hw : 1 / 2 ≤ ((s + par χ) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re]; linarith
  have hnw : ‖(s + par χ) / 2‖ ≤ ‖s‖ + 1 := by
    have hp1 : ‖par χ‖ ≤ 1 := by
      rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le s (par χ)
    linarith [norm_nonneg s]
  have h1 := hD _ hw
  have h2 : Real.log (‖(s + par χ) / 2‖ + 2) ≤ Real.log (‖s‖ + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have h3 := norm_logDeriv_le_VM χ (show 1 < s.re by linarith)
  have h4 := VM_anti (show (1 : ℝ) < 3 / 2 by norm_num) hs
  unfold Λd
  calc ‖((Real.log (N / Real.pi) / 2 : ℝ) : ℂ) + Complex.digamma ((s + par χ) / 2) / 2 +
        logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ ‖((Real.log (N / Real.pi) / 2 : ℝ) : ℂ)‖ + ‖Complex.digamma ((s + par χ) / 2) / 2‖ +
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := norm_add₃_le
    _ ≤ |Real.log (N / Real.pi)| / 2 + C / 2 * Real.log (‖s‖ + 3) + VM (3 / 2) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two, norm_div, Complex.norm_ofNat]
        have : C * Real.log (‖(s + par χ) / 2‖ + 2) ≤ C * Real.log (‖s‖ + 3) :=
          mul_le_mul_of_nonneg_left h2 hC0.le
        linarith

/-- Para `r ≥ 1/2`: `A₀ + A₁ log(r + 4) ≤ (2A₀ + 8A₁) √r`. -/
theorem cota_log_sqrt {A₀ A₁ r : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hr : 1 / 2 ≤ r) :
    A₀ + A₁ * Real.log (r + 4) ≤ (2 * A₀ + 8 * A₁) * Real.sqrt r := by
  have hsr : 2 / 3 ≤ Real.sqrt r := by
    rw [show (2 / 3 : ℝ) = Real.sqrt (4 / 9) by
      rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hl : Real.log (r + 4) ≤ 2 * Real.sqrt r + 4 := by
    have h := log_le_two_sqrt (show (0 : ℝ) ≤ r + 4 by linarith)
    have : Real.sqrt (r + 4) ≤ Real.sqrt r + 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith), Real.sqrt_nonneg r]
    linarith
  have : A₁ * Real.log (r + 4) ≤ A₁ * (8 * Real.sqrt r) :=
    mul_le_mul_of_nonneg_left (by linarith) hA₁
  nlinarith

/-- `√r · r⁻² = r^{-3/2}`. -/
theorem sqrt_mul_inv_sq {r : ℝ} (hr : 0 < r) : Real.sqrt r * r⁻¹ ^ 2 = r ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
  norm_num

/-- Cota de `Λd·G` en `Re s ≥ 3/2`. -/
theorem cota_Λd_G (hD : DigammaDerecha) (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ1 : 1 < σ)
    (hσ2 : σ < 3 / 2) :
    ∃ B : ℝ, ∀ s : ℂ, 3 / 2 ≤ s.re → ‖Λd χ s * G σ s‖ ≤ B * ‖s - 1‖ ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := hD
  set A₀ : ℝ := |Real.log (N / Real.pi)| / 2 + VM (3 / 2) with hA₀
  set A₁ : ℝ := C / 2 with hA₁
  set K₀ : ℝ := 4 * (2 * σ - 1) / (3 / 2 - σ) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; apply div_nonneg <;> linarith
  refine ⟨K₀ * (2 * A₀ + 8 * A₁), fun s hs => ?_⟩
  have hr : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [le_abs_self (s.re - 1)]
  have hr0 : 0 < ‖s - 1‖ := by linarith
  have h1 := norm_Λd_le_derecha hC0 hC χ hs
  have h2 := norm_G_le hσ1 hσ2 hs
  have h3 : Real.log (‖s‖ + 3) ≤ Real.log (‖s - 1‖ + 4) := by
    apply Real.log_le_log (by positivity)
    have := norm_sub_norm_le s 1
    simp at this
    linarith
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; exact add_nonneg (by positivity) (VM_nonneg _)
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have h4 := cota_log_sqrt hA₀0 hA₁0 hr
  have hΛle : ‖Λd χ s‖ ≤ (2 * A₀ + 8 * A₁) * Real.sqrt ‖s - 1‖ := by
    have h5 : A₁ * Real.log (‖s‖ + 3) ≤ A₁ * Real.log (‖s - 1‖ + 4) :=
      mul_le_mul_of_nonneg_left h3 hA₁0
    have e : |Real.log (N / Real.pi)| / 2 + C / 2 * Real.log (‖s‖ + 3) + VM (3 / 2) =
        A₀ + A₁ * Real.log (‖s‖ + 3) := by rw [hA₀, hA₁]; ring
    linarith
  rw [norm_mul]
  calc ‖Λd χ s‖ * ‖G σ s‖ ≤ ((2 * A₀ + 8 * A₁) * Real.sqrt ‖s - 1‖) * (K₀ * ‖s - 1‖⁻¹ ^ 2) :=
        mul_le_mul hΛle h2 (norm_nonneg _) (by positivity)
    _ = K₀ * (2 * A₀ + 8 * A₁) * (Real.sqrt ‖s - 1‖ * ‖s - 1‖⁻¹ ^ 2) := by ring
    _ = K₀ * (2 * A₀ + 8 * A₁) * ‖s - 1‖ ^ (-(3 / 2 : ℝ)) := by rw [sqrt_mul_inv_sq hr0]

/-- `Λd·G` es holomorfa en `Re s > (σ + 3/2)/2`. -/
theorem differentiableAt_Λd_G {χ : DirichletCharacter ℂ N} {σ : ℝ}
    (hσ1 : 1 < σ) {s : ℂ} (hs : σ < s.re) :
    DifferentiableAt ℂ (fun s => Λd χ s * G σ s) s := by
  have hs1 : 1 < s.re := by linarith
  have hΛ : DifferentiableAt ℂ (Λd χ) s := by
    unfold Λd
    have hpar := par_re_nonneg χ
    have hw : 0 < ((s + par χ) / 2).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re]; linarith
    have hd : DifferentiableAt ℂ (fun z => Complex.digamma ((z + par χ) / 2)) s :=
      DifferentiableAt.comp (f := fun z : ℂ => (z + par χ) / 2) (g := Complex.digamma) s
        (differentiableAt_digamma hw) (by fun_prop)
    exact ((differentiableAt_const _).add (hd.div_const 2)).add
      (differentiableAt_logDeriv_L' χ (ne_one_of_re hs1) (L_sigma_ne' χ hs1))
  have hG : DifferentiableAt ℂ (G σ) s := by
    unfold G
    have a : s - ((1 - σ : ℝ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have b : s - (σ : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have g1 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - ((1 - σ : ℝ) : ℂ))) s :=
      (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const _) a
    have g2 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - (σ : ℂ))) s :=
      (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const _) b
    exact g1.sub g2
  exact hΛ.mul hG

/-- **Desplazamiento a la derecha para `Λd·G`**: `∫ Λd(3/2 + iy) G(3/2 + iy) dy = 0`. -/
theorem integral_Λd_G_eq_zero (hD : DigammaDerecha) {χ : DirichletCharacter ℂ N}
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) :
    ∫ y : ℝ, Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) = 0 := by
  obtain ⟨B, hB⟩ := cota_Λd_G hD χ hσ1 hσ2
  refine Contorno.integral_vertical_eq_zero (f := fun s => Λd χ s * G σ s) (c := 3 / 2)
    (c₀ := (σ + 3 / 2) / 2) (s₀ := 1) (B := B) (by linarith) (by norm_num) ?_ hB
  intro s hs
  have hs' : σ < s.re := by
    have : (σ + 3 / 2) / 2 < s.re := hs
    linarith
  exact (differentiableAt_Λd_G hσ1 hs').differentiableWithinAt

/-- `y ↦ Λd(3/2 + iy) G(3/2 + iy)` es integrable. -/
theorem integrable_Λd_G (hD : DigammaDerecha) {χ : DirichletCharacter ℂ N}
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) :
    Integrable fun y : ℝ => Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) := by
  obtain ⟨B, hB⟩ := cota_Λd_G hD χ hσ1 hσ2
  have hB0 : 0 ≤ B := by
    have h := hB (3 / 2) (by norm_num)
    have hp : 0 < ‖(3 / 2 : ℂ) - 1‖ ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    push Not at hneg
    have : B * ‖(3 / 2 : ℂ) - 1‖ ^ (-(3 / 2 : ℝ)) < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (Λd χ (3 / 2) * G σ (3 / 2))]
  have hcont : Continuous fun y : ℝ => Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : σ < ((3 / 2 : ℝ) + y * I : ℂ).re := by simp; linarith
    exact (differentiableAt_Λd_G hσ1 hre).continuousAt.comp (f := fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + y * I)
      (by fun_prop)
  refine ((Contorno.integrable_dom (δ := 1 / 2) (by norm_num) 0).const_mul B).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have h1 := hB ((3 / 2 : ℝ) + y * I) (by simp)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hB0)
  have := Contorno.rpow_dist_le (s₀ := 1) (σ := 3 / 2) (t := y) (δ := 1 / 2) (by norm_num)
    (by norm_num)
  simpa using this

end AMate.Miller.Hadamard
