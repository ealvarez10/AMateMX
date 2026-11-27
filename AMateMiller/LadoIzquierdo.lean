import AMateMiller.CotasExplicitas

/-!
# El lado izquierdo `Re s = −1/2` de la fórmula explícita ponderada

Para `χ` primitivo módulo `N`, `x ≥ 1` y `0 < α < β < 1/2`, con `b = 1/2 − β`:

  `(1/2π) ∫ |L'/L(−1/2 + iy) K(−1/2 + iy)| dy ≤ x^{−1/2} ((A + 12)/(2b) + 8/π)`,
  `A = |log(N/π)| + 15 + VM(3/2)`   (`cota_LE`).

Se usa la reflexión `L'/L(s) = −log(N/π) − ½ψ((s+a)/2) − ½ψ((1−s+a)/2) − L'/L(1 − s, χ⁻¹)`,
las cotas de `ψ` en rectas verticales y `∫ dy/(b² + y²) = π/b`.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Hadamard AMate.Miller.Ponderada AMate.Miller.DigammaExp

set_option linter.unusedSectionVars false

/-! ### Integrales elementales -/

theorem integrable_inv_sq_add {b : ℝ} (hb : 0 < b) :
    Integrable fun y : ℝ => 1 / (b ^ 2 + y ^ 2) := by
  have h := (integrable_inv_one_add_sq.comp_div hb.ne').const_mul (1 / b ^ 2)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  field_simp

theorem integral_inv_sq_add {b : ℝ} (hb : 0 < b) :
    ∫ y : ℝ, 1 / (b ^ 2 + y ^ 2) = Real.pi / b := by
  have e : (fun y : ℝ => 1 / (b ^ 2 + y ^ 2)) = fun y => (1 / b ^ 2) * (1 + (y / b) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [e, integral_const_mul, Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) b,
    integral_univ_inv_one_add_sq, abs_of_pos hb, smul_eq_mul]
  field_simp

/-- La cola `h(y) = [|y| ≥ 1] |y|^{-3/2}`. -/
def cola (y : ℝ) : ℝ := if 1 ≤ |y| then |y| ^ (-(3 / 2 : ℝ)) else 0

theorem cola_nonneg (y : ℝ) : 0 ≤ cola y := by
  unfold cola; split_ifs <;> [exact Real.rpow_nonneg (abs_nonneg _) _; exact le_rfl]

theorem integrable_cola : Integrable cola := by
  have hdom : Integrable (fun y : ℝ => 2 ^ (3 / 2 : ℝ) * (1 + ‖y‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  have hmeas : AEStronglyMeasurable cola volume := by
    refine Measurable.aestronglyMeasurable ?_
    unfold cola
    exact Measurable.ite (measurableSet_le measurable_const measurable_id.abs)
      (measurable_id.abs.pow_const _) measurable_const
  refine hdom.mono' hmeas (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (cola_nonneg y)]
  unfold cola
  split_ifs with h
  · have hpos : 0 < |y| := by linarith
    have h1 : (1 + ‖y‖) / 2 ≤ |y| := by rw [Real.norm_eq_abs]; linarith
    calc |y| ^ (-(3 / 2 : ℝ)) ≤ ((1 + ‖y‖) / 2) ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      _ = 2 ^ (3 / 2 : ℝ) * (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_eq_mul_inv, inv_inv, mul_comm]
  · positivity

theorem integral_cola : ∫ y : ℝ, cola y = 4 := by
  have e : cola = fun y => (fun t : ℝ => if 1 ≤ t then t ^ (-(3 / 2 : ℝ)) else 0) |y| := rfl
  rw [e, integral_comp_abs]
  have h1 : ∫ t in Ioi (0 : ℝ), (if 1 ≤ t then t ^ (-(3 / 2 : ℝ)) else 0) =
      ∫ t in Ioi (1 : ℝ), t ^ (-(3 / 2 : ℝ)) := by
    have hf : (fun t : ℝ => if 1 ≤ t then t ^ (-(3 / 2 : ℝ)) else 0) =
        (Ici (1 : ℝ)).indicator (fun t => t ^ (-(3 / 2 : ℝ))) := by
      funext t; simp [Set.indicator, mem_Ici]
    rw [hf, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 by
        ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
        · exact fun h => h.2
        · exact fun h => ⟨by linarith, h⟩,
      integral_Ici_eq_integral_Ioi]
  rw [h1, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  norm_num

/-! ### Cotas puntuales -/

variable {N : ℕ} [NeZero N]

/-- `‖ψ(w)‖ ≤ 17 + 2 log(3 + |y|)` en los dos puntos que da la reflexión. -/
theorem norm_digamma_izq (hS : SerieDigamma) {w : ℂ} (h1 : -1 / 4 ≤ w.re) (h2 : w.re ≤ 5 / 4)
    (h3 : w.re ≠ 0) {y : ℝ} (hw : ‖w‖ ≤ 2 + |y|)
    (hre : w.re = -1 / 4 ∨ 1 / 4 ≤ w.re) :
    ‖Complex.digamma w‖ ≤ 17 + 2 * Real.log (3 + |y|) := by
  have hl : ∀ v : ℂ, ‖v‖ ≤ 2 + |y| → Real.log (1 + ‖v‖) ≤ Real.log (3 + |y|) := fun v hv =>
    Real.log_le_log (by positivity) (by linarith)
  rcases hre with he | hge
  · -- `Re w = −1/4`: `ψ(w) = ψ(w + 1) − 1/w`
    have hw0 : w ≠ 0 := by intro e; rw [e] at he; norm_num at he
    have hw1 : 1 / 4 ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w; rw [he] at this; norm_num at this; linarith
    have e := digamma_add_inv (w := w) (by rw [he]; norm_num) hw0
    have hr : 0 < (w + 1).re := by simp [he]; norm_num
    have hd := norm_digamma_le hS hr (by simp [he]; norm_num)
    have hw1' : 3 / 4 ≤ ‖w + 1‖ := by
      have := Complex.abs_re_le_norm (w + 1); simp [he] at this; norm_num at this; linarith
    have hn1 : ‖w + 1‖ ≤ 2 + |y| + 1 := by
      have := norm_add_le w 1; simp at this; linarith
    have hl1 : Real.log (1 + ‖w + 1‖) ≤ Real.log (3 + |y|) + 1 := by
      have : Real.log (1 + ‖w + 1‖) ≤ Real.log (4 + |y|) := Real.log_le_log (by positivity) (by linarith)
      have h4 : Real.log (4 + |y|) ≤ Real.log (3 + |y|) + 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < (4 + |y|) / (3 + |y|) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at this
        have h5 : (4 + |y|) / (3 + |y|) - 1 ≤ 1 := by
          rw [div_sub_one (by positivity), div_le_one (by positivity)]; linarith [abs_nonneg y]
        linarith
      linarith
    have hinv1 : 1 / ‖w + 1‖ ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hinv : ‖1 / w‖ ≤ 4 := by
      rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
    have : Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by rw [← e]; ring
    rw [this]
    calc ‖Complex.digamma (w + 1) - 1 / w‖ ≤ ‖Complex.digamma (w + 1)‖ + ‖1 / w‖ := norm_sub_le _ _
      _ ≤ (9 + 4 / 3 + 2 * (Real.log (3 + |y|) + 1)) + 4 := by linarith
      _ ≤ 17 + 2 * Real.log (3 + |y|) := by nlinarith
  · have hd := norm_digamma_le hS (by linarith) (by linarith)
    have hw1 : 1 / 4 ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w; linarith [le_abs_self w.re]
    have hinv : 1 / ‖w‖ ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have := hl w hw
    linarith

/-- **Cota de `L'/L` en `Re s = −1/2`.** -/
theorem norm_logDeriv_izq (hR : ReflexionLogDeriv) (hS : SerieDigamma) (hZL : ZeroLocus)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (y : ℝ) :
    ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      |Real.log (N / Real.pi)| + 17 + VM (3 / 2) + 2 * Real.log (3 + |y|) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
  have hpar := par_re_nonneg χ
  have e1 : 1 - s = ((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hsre : s.re = -1 / 2 := by simp [hs]
  have c1 : ∀ n : ℕ, (s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.add_re, hsre, Complex.neg_re,
      Complex.natCast_re] at hre
    rcases par_spec χ with ⟨-, h0⟩ | ⟨-, h1⟩
    · rw [h0] at hre; simp at hre
      rcases n with _ | n
      · norm_num at hre
      · push_cast at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rw [h1] at hre; simp at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have c2 : ∀ n : ℕ, (1 - s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.sub_re, Complex.one_re, hsre,
      Complex.neg_re, Complex.natCast_re] at hre
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hpar.1]
  have c3 : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro hL
    have hne1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
    rcases hZL N χ hp s (by rw [hsre]; norm_num) hne1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hsre] at h; linarith [h.1]
    · have := congrArg Complex.re h; rw [hsre] at this; simp at this
    · have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hre1 : 1 < (1 - s).re := by rw [e1]; simp; norm_num
  have c4 : DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 := L_sigma_ne' χ⁻¹ hre1
  have href := reflexion_gen hR hp c1 c2 c3 c4
  have hL' : logDeriv (DirichletCharacter.LFunction χ) s =
      -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((s + par χ) / 2) / 2 -
        Complex.digamma ((1 - s + par χ) / 2) / 2 -
        logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) := by
    unfold Λd at href
    rw [par_inv] at href
    have e : (1 - s + par χ) / 2 = ((1 - s) + par χ) / 2 := by ring
    rw [e]
    push_cast at href ⊢
    linear_combination href
  rw [hL']
  have hVM : ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ ≤ VM (3 / 2) := by
    have := norm_logDeriv_le_VM χ⁻¹ hre1
    rwa [show (1 - s).re = 3 / 2 by rw [e1]; simp] at this
  -- las dos digammas
  have hnw : ∀ w : ℂ, w = (s + par χ) / 2 ∨ w = (1 - s + par χ) / 2 → ‖w‖ ≤ 2 + |y| := by
    intro w hw
    have hp1 : ‖par χ‖ ≤ 1 := by
      rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
    have hsn : ‖s‖ ≤ 1 / 2 + |y| := by
      have h1 := norm_add_le (((-1 / 2 : ℝ) : ℂ)) ((y : ℂ) * I)
      have h2 : ‖(((-1 / 2 : ℝ) : ℂ))‖ = 1 / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
      have h3 : ‖(y : ℂ) * I‖ = |y| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [hs]; linarith
    rcases hw with rfl | rfl
    · rw [norm_div, Complex.norm_ofNat]
      have := norm_add_le s (par χ); linarith [abs_nonneg y]
    · rw [norm_div, Complex.norm_ofNat]
      have h1 := norm_add_le (1 - s) (par χ)
      have h2 := norm_sub_le 1 s
      rw [norm_one] at h2; linarith [abs_nonneg y]
  have hd1 : ‖Complex.digamma ((s + par χ) / 2)‖ ≤ 17 + 2 * Real.log (3 + |y|) := by
    have hr : ((s + par χ) / 2).re = (-1 / 2 + (par χ).re) / 2 := by simp [hsre]
    refine norm_digamma_izq hS (by rw [hr]; linarith [hpar.1]) (by rw [hr]; linarith [hpar.2.1])
      (by rw [hr]; rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num) (hnw _ (Or.inl rfl)) ?_
    rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hr, h]
    · left; norm_num
    · right; norm_num
  have hd2 : ‖Complex.digamma ((1 - s + par χ) / 2)‖ ≤ 17 + 2 * Real.log (3 + |y|) := by
    have hr : ((1 - s + par χ) / 2).re = (3 / 2 + (par χ).re) / 2 := by simp [hsre]; ring
    refine norm_digamma_izq hS (by rw [hr]; linarith [hpar.1]) (by rw [hr]; linarith [hpar.2.1])
      (by rw [hr]; linarith [hpar.1]) (hnw _ (Or.inr rfl)) (Or.inr (by rw [hr]; linarith [hpar.1]))
  calc ‖-((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((s + par χ) / 2) / 2 -
        Complex.digamma ((1 - s + par χ) / 2) / 2 -
        logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖
      ≤ ‖((Real.log (N / Real.pi) : ℝ) : ℂ)‖ + ‖Complex.digamma ((s + par χ) / 2)‖ / 2 +
        ‖Complex.digamma ((1 - s + par χ) / 2)‖ / 2 +
        ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ := by
        have := norm_sub_le (-((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((s + par χ) / 2) / 2 -
          Complex.digamma ((1 - s + par χ) / 2) / 2) (logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s))
        have := norm_sub_le (-((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((s + par χ) / 2) / 2)
          (Complex.digamma ((1 - s + par χ) / 2) / 2)
        have := norm_sub_le (-((Real.log (N / Real.pi) : ℝ) : ℂ)) (Complex.digamma ((s + par χ) / 2) / 2)
        simp only [norm_neg, norm_div, Complex.norm_ofNat] at *
        linarith
    _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith

/-- `L(−1/2 + iy) ≠ 0`. -/
theorem L_izq_ne (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (y : ℝ) :
    DirichletCharacter.LFunction χ (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = -1 / 2 := by simp [hs]
  intro hL
  have hne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  rcases hZL N χ hp s (by rw [hsre]; norm_num) hne1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
  · rw [hsre] at h; linarith [h.1]
  · have := congrArg Complex.re h; rw [hsre] at this; simp at this
  · have := congrArg Complex.re h; rw [hsre] at this; norm_num at this

/-- `|K(−1/2 + iy)| ≤ x^{−1/2}/(b² + y²)` con `b = 1/2 − β`. -/
theorem norm_K_izq {x α β : ℝ} (hx : 0 < x) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2)
    (y : ℝ) :
    ‖K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-(1 / 2 : ℝ)) / ((1 / 2 - β) ^ 2 + y ^ 2) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
  have hb : 0 < 1 / 2 - β := by linarith
  have hfac : ∀ γ : ℝ, 0 < γ → γ ≤ β → Real.sqrt ((1 / 2 - β) ^ 2 + y ^ 2) ≤ ‖s + γ‖ := by
    intro γ hγ hγβ
    rw [show ‖s + γ‖ = Real.sqrt ((γ - 1 / 2) ^ 2 + y ^ 2) by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp [hs]; ring]
    apply Real.sqrt_le_sqrt
    nlinarith
  unfold K
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : s.re = -1 / 2 := by simp [hs]
  rw [hre, show (-1 / 2 : ℝ) = -(1 / 2) by ring]
  have h1 := hfac α hα hαβ.le
  have h2 := hfac β (by linarith) le_rfl
  have hsq : (1 / 2 - β) ^ 2 + y ^ 2 ≤ ‖s + α‖ * ‖s + β‖ := by
    have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (norm_nonneg _)
    rwa [Real.mul_self_sqrt (by positivity)] at this
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

/-- `2 log(3 + t) ≤ 8 + 4√t`. -/
theorem log_tres_le {t : ℝ} (ht : 0 ≤ t) : 2 * Real.log (3 + t) ≤ 8 + 4 * Real.sqrt t := by
  have h := log_le_two_sqrt (show (0 : ℝ) ≤ 3 + t by linarith)
  have h2 : Real.sqrt (3 + t) ≤ 2 + Real.sqrt t := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  linarith

/-- `√|y|/(b² + y²) ≤ 1/(b² + y²) + cola y`. -/
theorem sqrt_div_le (b y : ℝ) (hb : 0 < b) :
    Real.sqrt |y| / (b ^ 2 + y ^ 2) ≤ 1 / (b ^ 2 + y ^ 2) + cola y := by
  have hd : 0 < b ^ 2 + y ^ 2 := by positivity
  unfold cola
  split_ifs with h
  · have hy : 0 < |y| := by linarith
    have hsq : Real.sqrt |y| / (b ^ 2 + y ^ 2) ≤ |y| ^ (-(3 / 2 : ℝ)) := by
      rw [div_le_iff₀ hd]
      have e : |y| ^ (-(3 / 2 : ℝ)) * |y| ^ 2 = Real.sqrt |y| := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hy]; norm_num
      have : |y| ^ 2 = y ^ 2 := sq_abs y
      have h0 : 0 ≤ |y| ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hy.le _
      nlinarith
    have : 0 ≤ 1 / (b ^ 2 + y ^ 2) := by positivity
    linarith
  · push Not at h
    have : Real.sqrt |y| ≤ 1 := by
      rw [Real.sqrt_le_one]; exact h.le
    rw [add_zero]
    exact div_le_div_of_nonneg_right this hd.le

/-- **Cota del lado izquierdo.** -/
theorem cota_LE (hR : ReflexionLogDeriv) (hS : SerieDigamma) (hZL : ZeroLocus)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {x α β : ℝ} (hx : 0 < x) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) :
    Integrable (fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + y * I) * K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)) ∧
      (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + y * I) * K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      x ^ (-(1 / 2 : ℝ)) * ((|Real.log (N / Real.pi)| + 17 + VM (3 / 2) + 12) / (2 * (1 / 2 - β)) +
        8 / Real.pi) := by
  set b : ℝ := 1 / 2 - β with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set A : ℝ := |Real.log (N / Real.pi)| + 17 + VM (3 / 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; have := VM_nonneg (3 / 2); positivity
  set F : ℝ → ℂ := fun y => logDeriv (DirichletCharacter.LFunction χ)
    (((-1 / 2 : ℝ) : ℂ) + y * I) * K x α β (((-1 / 2 : ℝ) : ℂ) + y * I) with hF
  set D : ℝ → ℝ := fun y => x ^ (-(1 / 2 : ℝ)) * ((A + 12) * (1 / (b ^ 2 + y ^ 2)) + 4 * cola y)
    with hD
  have hDi : Integrable D :=
    (((integrable_inv_sq_add hb0).const_mul (A + 12)).add (integrable_cola.const_mul 4)).const_mul _
  have hbound : ∀ y, ‖F y‖ ≤ D y := by
    intro y
    have h1 := norm_logDeriv_izq hR hS hZL hp y
    have h2 := norm_K_izq hx hα hαβ hβ y
    have h3 := log_tres_le (abs_nonneg y)
    have h4 := sqrt_div_le b y hb0
    have hd : 0 < b ^ 2 + y ^ 2 := by positivity
    have hxp : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
    rw [hF, norm_mul]
    calc ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + y * I)‖ *
          ‖K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ (A + 2 * Real.log (3 + |y|)) * (x ^ (-(1 / 2 : ℝ)) / (b ^ 2 + y ^ 2)) :=
          mul_le_mul (by rw [hA]; linarith) h2 (norm_nonneg _) (by
            have := Real.log_nonneg (show (1 : ℝ) ≤ 3 + |y| by linarith [abs_nonneg y])
            linarith)
      _ ≤ x ^ (-(1 / 2 : ℝ)) * ((A + 8) / (b ^ 2 + y ^ 2) + 4 * (Real.sqrt |y| / (b ^ 2 + y ^ 2))) := by
          rw [mul_div_assoc', div_le_iff₀ hd]
          have e : x ^ (-(1 / 2 : ℝ)) * ((A + 8) / (b ^ 2 + y ^ 2) +
              4 * (Real.sqrt |y| / (b ^ 2 + y ^ 2))) * (b ^ 2 + y ^ 2) =
              x ^ (-(1 / 2 : ℝ)) * (A + 8 + 4 * Real.sqrt |y|) := by field_simp
          rw [e]
          nlinarith
      _ ≤ D y := by
          rw [hD]
          apply mul_le_mul_of_nonneg_left _ hxp.le
          have : (A + 8) / (b ^ 2 + y ^ 2) = (A + 8) * (1 / (b ^ 2 + y ^ 2)) := by ring
          nlinarith [h4]
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro y
    have hne1 : ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; norm_num at this
    have hc : Continuous fun y : ℝ => ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by fun_prop
    have hL := (continuousAt_logDeriv_L χ hne1 (L_izq_ne hZL hp y)).comp
      (f := fun y : ℝ => ((-1 / 2 : ℝ) : ℂ) + y * I) hc.continuousAt
    have hK : ContinuousAt (fun y : ℝ => K x α β (((-1 / 2 : ℝ) : ℂ) + y * I)) y := by
      unfold K
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have ha : ((-1 / 2 : ℝ) : ℂ) + y * I + α ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hb' : ((-1 / 2 : ℝ) : ℂ) + y * I + β ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      refine ContinuousAt.div ?_ (by fun_prop) (mul_ne_zero ha hb')
      exact ContinuousAt.const_cpow (f := fun y : ℝ => ((-1 / 2 : ℝ) : ℂ) + y * I)
        hc.continuousAt (Or.inl hx0)
    exact hL.mul hK
  have hFi : Integrable F := hDi.mono' hcont.aestronglyMeasurable (Eventually.of_forall hbound)
  refine ⟨hFi, ?_⟩
  have hint : ∫ y, ‖F y‖ ≤ ∫ y, D y :=
    integral_mono hFi.norm hDi fun y => hbound y
  have hDval : ∫ y, D y = x ^ (-(1 / 2 : ℝ)) * ((A + 12) * (Real.pi / b) + 4 * 4) := by
    rw [hD, integral_const_mul, integral_add ((integrable_inv_sq_add hb0).const_mul _)
      (integrable_cola.const_mul _), integral_const_mul, integral_const_mul, integral_inv_sq_add hb0,
      integral_cola]
  rw [hDval] at hint
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (1 / (2 * Real.pi)) * ∫ y, ‖F y‖ ≤ (1 / (2 * Real.pi)) *
        (x ^ (-(1 / 2 : ℝ)) * ((A + 12) * (Real.pi / b) + 4 * 4)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = x ^ (-(1 / 2 : ℝ)) * ((A + 12) / (2 * b) + 8 / Real.pi) := by
        field_simp
        ring

end AMate.Miller.Explicito
