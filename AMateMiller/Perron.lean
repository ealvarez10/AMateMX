import Mathlib

/-!
# Núcleo de Perron con dos polos simples

Para `0 < a, b` distintos, la función `g(u) = (e^{−au} − e^{−bu})/(b − a)` (`u > 0`), `g(u) = 0`
(`u ≤ 0`) es continua e integrable, y su transformada de Fourier es
`1/((a + 2πiξ)(b + 2πiξ))`. Por la fórmula de inversión,

  `(1/2π) ∫ e^{itu}/((a + it)(b + it)) dt = g(u)`   (`nucleo`),

y de ahí, para `y > 0` y `c + α, c + β > 0`,

  `(1/2π) ∫ y^{c+it}/((c + it + α)(c + it + β)) dt = [y > 1] (y^{−α} − y^{−β})/(β − α)`
  (`perron`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform

noncomputable section

namespace AMate.Miller.Perron

/-- `g(u) = (e^{−a u⁺} − e^{−b u⁺})/(b − a)` con `u⁺ = max u 0`. -/
def gK (a b : ℝ) (u : ℝ) : ℂ :=
  ((Real.exp (-a * max u 0) - Real.exp (-b * max u 0)) / (b - a) : ℝ)

theorem gK_of_pos {a b u : ℝ} (hu : 0 < u) :
    gK a b u = ((Real.exp (-a * u) - Real.exp (-b * u)) / (b - a) : ℝ) := by
  rw [gK, max_eq_left hu.le]

theorem gK_of_nonpos {a b u : ℝ} (hu : u ≤ 0) : gK a b u = 0 := by
  rw [gK, max_eq_right hu]; simp

theorem continuous_gK (a b : ℝ) : Continuous (gK a b) := by
  unfold gK
  fun_prop

theorem integrableOn_exp_neg {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (-a * u)) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 ha
  simpa [neg_mul] using this

theorem integrable_gK {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Integrable (gK a b) := by
  have h1 : IntegrableOn (gK a b) (Ioi 0) := by
    have : IntegrableOn (fun u : ℝ => (((Real.exp (-a * u) - Real.exp (-b * u)) / (b - a) : ℝ) : ℂ))
        (Ioi 0) :=
      (((integrableOn_exp_neg ha).sub (integrableOn_exp_neg hb)).div_const (b - a)).ofReal
    refine this.congr_fun (fun u hu => (gK_of_pos hu).symm) measurableSet_Ioi
  have h2 : IntegrableOn (gK a b) (Iic 0) :=
    (integrableOn_zero).congr_fun (fun u hu => (gK_of_nonpos hu).symm) measurableSet_Iic
  have := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- `∫_{u > 0} e^{−(a + iξ')u} du = 1/(a + iξ')`. -/
theorem integral_exp_Ioi {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫ u : ℝ in Ioi 0, Complex.exp ((-(a : ℂ) - t * I) * u) = 1 / ((a : ℂ) + t * I) := by
  have hre : ((-(a : ℂ) - t * I)).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi hre 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    show (-(a : ℂ) - t * I) = -((a : ℂ) + t * I) by ring, neg_div_neg_eq]

theorem integrableOn_cexp {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntegrableOn (fun u : ℝ => Complex.exp ((-(a : ℂ) - t * I) * u)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0

/-- Transformada de Fourier de `g`. -/
theorem fourier_gK {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (ξ : ℝ) :
    𝓕 (gK a b) ξ = 1 / (((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * ((b : ℂ) + (2 * Real.pi * ξ : ℝ) * I)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set t : ℝ := 2 * Real.pi * ξ with ht
  have hzero : ∀ v : ℝ, v ∉ Ioi (0 : ℝ) →
      Complex.exp (↑(-2 * Real.pi * v * ξ) * I) • gK a b v = 0 := by
    intro v hv
    rw [Set.mem_Ioi, not_lt] at hv
    rw [gK_of_nonpos hv, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcong : ∀ v ∈ Ioi (0 : ℝ), Complex.exp (↑(-2 * Real.pi * v * ξ) * I) • gK a b v =
      (1 / ((b : ℂ) - a)) * (Complex.exp ((-(a : ℂ) - t * I) * v) -
        Complex.exp ((-(b : ℂ) - t * I) * v)) := by
    intro v hv
    rw [gK_of_pos hv, smul_eq_mul]
    have hba : (b : ℂ) - a ≠ 0 := by
      intro h; apply hab; exact_mod_cast (sub_eq_zero.mp h).symm
    push_cast
    have e1 : Complex.exp ((-(a : ℂ) - t * I) * v) =
        Complex.exp (-(a : ℂ) * v) * Complex.exp (-2 * Real.pi * v * ξ * I) := by
      rw [← Complex.exp_add]; congr 1; rw [ht]; push_cast; ring
    have e2 : Complex.exp ((-(b : ℂ) - t * I) * v) =
        Complex.exp (-(b : ℂ) * v) * Complex.exp (-2 * Real.pi * v * ξ * I) := by
      rw [← Complex.exp_add]; congr 1; rw [ht]; push_cast; ring
    rw [e1, e2]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcong, integral_const_mul,
    integral_sub (integrableOn_cexp ha t) (integrableOn_cexp hb t), integral_exp_Ioi ha t,
    integral_exp_Ioi hb t]
  have h1 : (a : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (b : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hba : (b : ℂ) - a ≠ 0 := by
    intro h; apply hab; exact_mod_cast (sub_eq_zero.mp h).symm
  field_simp
  ring

/-- `|a + it| ≥ min(a, 1)(1 + |t|)/2`. -/
theorem norm_add_mul_I_ge {a : ℝ} (ha : 0 < a) (t : ℝ) :
    min a 1 * (1 + |t|) / 2 ≤ ‖(a : ℂ) + t * I‖ := by
  have h1 : a ≤ ‖(a : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((a : ℂ) + t * I); simp at this
    linarith [le_abs_self a, abs_of_pos ha]
  have h2 : |t| ≤ ‖(a : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((a : ℂ) + t * I); simpa using this
  have hm : min a 1 ≤ 1 := min_le_right a 1
  have hm' : min a 1 ≤ a := min_le_left a 1
  rcases le_total |t| 1 with h | h
  · have : min a 1 * (1 + |t|) ≤ min a 1 * 2 := by
      gcongr; linarith
    linarith
  · have : min a 1 * (1 + |t|) ≤ 1 * (|t| + |t|) := by
      apply mul_le_mul hm (by linarith) (by positivity) (by norm_num)
    linarith

theorem integrable_fourier_gK {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Integrable (𝓕 (gK a b)) := by
  have he : 𝓕 (gK a b) = fun ξ : ℝ => 1 / (((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) *
      ((b : ℂ) + (2 * Real.pi * ξ : ℝ) * I)) := funext (fourier_gK ha hb hab)
  rw [he]
  set m : ℝ := min a 1 * min b 1 / 4 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hdom : Integrable (fun ξ : ℝ => m⁻¹ * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  have hne : ∀ (c : ℝ), 0 < c → ∀ ξ : ℝ, (c : ℂ) + (2 * Real.pi * ξ : ℝ) * I ≠ 0 := by
    intro c hc ξ h; have := congrArg Complex.re h; simp at this; linarith
  refine hdom.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · refine (Continuous.aestronglyMeasurable ?_)
    refine continuous_const.div (by fun_prop) fun ξ => mul_ne_zero (hne a ha ξ) (hne b hb ξ)
  · have h1 := norm_add_mul_I_ge ha (2 * Real.pi * ξ)
    have h2 := norm_add_mul_I_ge hb (2 * Real.pi * ξ)
    have hxi : 1 + |ξ| ≤ 1 + |2 * Real.pi * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have : |ξ| ≤ 2 * Real.pi * |ξ| := by
        have := Real.pi_gt_three; nlinarith [abs_nonneg ξ]
      linarith
    have hpos : 0 < 1 + |ξ| := by positivity
    rw [norm_div, norm_one, norm_mul, Real.norm_eq_abs]
    have hprod : m * (1 + |ξ|) ^ 2 ≤ ‖(a : ℂ) + (2 * Real.pi * ξ : ℝ) * I‖ *
        ‖(b : ℂ) + (2 * Real.pi * ξ : ℝ) * I‖ := by
      have k1 : min a 1 * (1 + |ξ|) / 2 ≤ ‖(a : ℂ) + (2 * Real.pi * ξ : ℝ) * I‖ :=
        le_trans (by gcongr) h1
      have k2 : min b 1 * (1 + |ξ|) / 2 ≤ ‖(b : ℂ) + (2 * Real.pi * ξ : ℝ) * I‖ :=
        le_trans (by gcongr) h2
      have := mul_le_mul k1 k2 (by positivity) (norm_nonneg _)
      rw [hm]
      nlinarith
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hprod)]
    have e : m⁻¹ * (1 + |ξ|) ^ (-(2 : ℝ)) * (m * (1 + |ξ|) ^ 2) = 1 := by
      rw [Real.rpow_neg hpos.le, Real.rpow_two]
      field_simp
    calc (1 : ℝ) = m⁻¹ * (1 + |ξ|) ^ (-(2 : ℝ)) * (m * (1 + |ξ|) ^ 2) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- **Núcleo**: `(1/2π) ∫ e^{itu}/((a + it)(b + it)) dt = g(u)`. -/
theorem nucleo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (u : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Complex.exp (t * u * I) / (((a : ℂ) + t * I) * ((b : ℂ) + t * I)) =
      gK a b u := by
  have hinv := (continuous_gK a b).fourierInv_fourier_eq (integrable_gK ha hb)
    (integrable_fourier_gK ha hb hab)
  have h := congrFun hinv u
  rw [Real.fourierInv_eq'] at h
  simp_rw [fourier_gK ha hb hab, smul_eq_mul] at h
  set F : ℝ → ℂ := fun t => Complex.exp (t * u * I) / (((a : ℂ) + t * I) * ((b : ℂ) + t * I))
    with hF
  have hcomp : ∫ ξ : ℝ, Complex.exp (↑(2 * Real.pi * (inner ℝ ξ u)) * I) *
      (1 / (((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * ((b : ℂ) + (2 * Real.pi * ξ : ℝ) * I))) =
      ∫ ξ : ℝ, F (2 * Real.pi * ξ) := by
    congr 1
    funext ξ
    simp only [hF, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    push_cast
    ring_nf
  rw [hcomp, Measure.integral_comp_mul_left F (2 * Real.pi), Complex.real_smul] at h
  rw [← h]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr hpi)]
  push_cast
  ring

/-- **Perron**: para `y > 0` y `c + α, c + β > 0` distintos,
`(1/2π) ∫ y^{c+it}/((c + it + α)(c + it + β)) dt = [y > 1](y^{−α} − y^{−β})/(β − α)`. -/
theorem perron {c α β y : ℝ} (ha : 0 < c + α) (hb : 0 < c + β) (hab : α ≠ β) (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I + α) * ((c : ℂ) + t * I + β)) =
      if 1 < y then (((y ^ (-α) - y ^ (-β)) / (β - α) : ℝ) : ℂ) else 0 := by
  have hab' : c + α ≠ c + β := by intro h; apply hab; linarith
  have hfun : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I + α) *
      ((c : ℂ) + t * I + β))) = fun t : ℝ => ((y ^ c : ℝ) : ℂ) *
      (Complex.exp (t * Real.log y * I) / ((((c + α : ℝ)) : ℂ) + t * I) /
        ((((c + β : ℝ)) : ℂ) + t * I)) := by
    funext t
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Complex.cpow_def_of_ne_zero hy0, ← Complex.ofReal_log hy.le,
      Real.rpow_def_of_pos hy, Complex.ofReal_exp]
    rw [show ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + t * Real.log y * I by push_cast; ring, Complex.exp_add]
    push_cast
    rw [← div_div]
    ring
  rw [hfun, integral_const_mul]
  have hn := nucleo ha hb hab' (Real.log y)
  simp only [div_div] at hn ⊢
  rw [mul_left_comm, hn]
  split_ifs with h1
  · rw [gK_of_pos (Real.log_pos h1)]
    have r1 : y ^ c * Real.exp (-(c + α) * Real.log y) = y ^ (-α) := by
      rw [show Real.exp (-(c + α) * Real.log y) = y ^ (-(c + α)) by
        rw [Real.rpow_def_of_pos hy]; ring_nf, ← Real.rpow_add hy]
      ring_nf
    have r2 : y ^ c * Real.exp (-(c + β) * Real.log y) = y ^ (-β) := by
      rw [show Real.exp (-(c + β) * Real.log y) = y ^ (-(c + β)) by
        rw [Real.rpow_def_of_pos hy]; ring_nf, ← Real.rpow_add hy]
      ring_nf
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_div_assoc', mul_sub, r1, r2]
    ring
  · rw [gK_of_nonpos (Real.log_nonpos hy.le (not_lt.mp h1)), mul_zero]

end AMate.Miller.Perron
