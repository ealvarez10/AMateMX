import AMateDirichlet.LRectaCritica

/-!
# Cota de `L(s,χ)` en `Re s = 0`

Para `χ ≠ 1` módulo `N`:

* `norm_sq_Gamma_half_add`, `norm_sq_Gamma_mul_I`: `|Γ(1/2 + iy)|² = π/cosh(πy)` y
  `|Γ(iy)|² = π/(y sinh(πy))`, por la fórmula de reflexión.
* `norm_sq_Gammaℝ_cociente_par`, `norm_sq_Gammaℝ_cociente_impar`: `|γ(1 − it)|² ≤ (1 + |t|) |γ(it)|²`
  para el factor arquimediano `γ` de un carácter par o impar.
* `norm_rootNumber_le`: `|ε(χ)| ≤ √N`.
* `norm_LFunction_mul_I_le_primitivo`: si `χ` es primitivo,
  `|L(it,χ)| ≤ N √(1 + |t|) |L(1 − it, χ⁻¹)|` (ecuación funcional).
* `norm_LFunction_mul_I_le`: para todo `χ ≠ 1`, `|L(it,χ)| ≤ C (1 + |t|)^{1/2} (2 + log(2 + |t|))`,
  pasando al carácter primitivo con `LFunction_changeLevel`.
-/

open Complex Set

namespace AMate.Dirichlet

/-! ### `Γ` en rectas especiales -/

/-- `|Γ(1/2 + iy)|² = π / cosh(π y)`. -/
theorem norm_sq_Gamma_half_add (y : ℝ) :
    ‖Gamma (1 / 2 + y * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * y) := by
  have hconj : Gamma (1 - (1 / 2 + y * I)) = (starRingEnd ℂ) (Gamma (1 / 2 + y * I)) := by
    rw [← Gamma_conj]
    congr 1
    apply Complex.ext <;> norm_num
  have hrefl := Gamma_mul_Gamma_one_sub (1 / 2 + (y : ℂ) * I)
  have hsin : Complex.sin (Real.pi * (1 / 2 + y * I)) = ((Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (1 / 2 + y * I) = ((Real.pi * y : ℝ) : ℂ) * I + Real.pi / 2 by
        push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  have key : ((Complex.normSq (Gamma (1 / 2 + y * I)) : ℝ) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
    rw [← mul_conj, ← hconj, hrefl, hsin, ofReal_div]
  rw [Complex.sq_norm]
  exact_mod_cast key

/-- `|Γ(iy)|² = π / (y sinh(π y))` para `y ≠ 0`. -/
theorem norm_sq_Gamma_mul_I (y : ℝ) (hy : y ≠ 0) :
    ‖Gamma (y * I)‖ ^ 2 = Real.pi / (y * Real.sinh (Real.pi * y)) := by
  have h1 := AMate.norm_sq_Gamma_one_sub y hy
  have hyI : (y : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hy) I_ne_zero
  have hadd : Gamma (1 - y * I) = (-(y * I)) * Gamma (-(y * I)) := by
    rw [show (1 : ℂ) - y * I = -(y * I) + 1 by ring, Gamma_add_one _ (neg_ne_zero.mpr hyI)]
  have hconj : Gamma (-((y : ℂ) * I)) = (starRingEnd ℂ) (Gamma (y * I)) := by
    rw [← Gamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hn : ‖Gamma (-((y : ℂ) * I))‖ = ‖Gamma (y * I)‖ := by
    rw [hconj, RCLike.norm_conj]
  have hnorm : ‖-((y : ℂ) * I)‖ = |y| := by simp
  rw [hadd, norm_mul, mul_pow, hn, hnorm, sq_abs] at h1
  have hsh : Real.sinh (Real.pi * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hy
  rw [eq_div_iff (mul_ne_zero hy hsh)]
  have h2 : y ^ 2 * ‖Gamma (y * I)‖ ^ 2 * Real.sinh (Real.pi * y) = Real.pi * y := by
    rw [h1]
    field_simp
  have h3 : y * (‖Gamma (y * I)‖ ^ 2 * (y * Real.sinh (Real.pi * y)) - Real.pi) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hy
  · linarith

/-- `‖Γℝ(s)‖ = π^{−Re s/2} ‖Γ(s/2)‖`. -/
theorem norm_Gammaℝ (s : ℂ) : ‖Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp [neg_div]

/-! ### Desigualdades hiperbólicas -/

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h1 := Real.cosh_sub_sinh x
  have h2 := Real.cosh_add_sinh x
  have e1 := Real.exp_pos (-x)
  have e2 := Real.exp_pos x
  rw [abs_le]
  constructor <;> linarith

theorem mul_sinh_pos {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : t ≠ 0) : 0 < t * Real.sinh (c * t) := by
  rcases lt_or_gt_of_ne ht with h | h
  · have : Real.sinh (c * t) < 0 := Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hc h)
    nlinarith
  · have : 0 < Real.sinh (c * t) := Real.sinh_pos_iff.mpr (mul_pos hc h)
    nlinarith

/-- `a cosh a ≤ (1 + a) sinh a` para `a > 0`. -/
theorem mul_cosh_le_sinh {a : ℝ} (_ha : 0 < a) :
    a * Real.cosh a ≤ (1 + a) * Real.sinh a := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have hp := Real.exp_pos a
  have hm := Real.exp_pos (-a)
  have hpm : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 2 * a + 1 ≤ Real.exp a ^ 2 := by
    rw [sq, ← Real.exp_add, show a + a = 2 * a by ring]
    have := Real.add_one_le_exp (2 * a)
    linarith
  have h3 : (2 * a + 1) * Real.exp (-a) ≤ Real.exp a := by
    calc (2 * a + 1) * Real.exp (-a) ≤ Real.exp a ^ 2 * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right h2 hm.le
      _ = Real.exp a * (Real.exp a * Real.exp (-a)) := by ring
      _ = Real.exp a := by rw [hpm, mul_one]
  nlinarith

/-- `|a| / |sinh a| ≤ (1 + |a|)/cosh a`, en la forma `|a| cosh a ≤ (1 + |a|) |sinh a|`. -/
theorem abs_mul_cosh_le (a : ℝ) : |a| * Real.cosh a ≤ (1 + |a|) * |Real.sinh a| := by
  rcases lt_trichotomy a 0 with h | h | h
  · have := mul_cosh_le_sinh (neg_pos.mpr h)
    rw [Real.cosh_neg, Real.sinh_neg] at this
    rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr h)]
    linarith
  · subst h
    simp
  · have := mul_cosh_le_sinh h
    rw [abs_of_pos h, abs_of_pos (Real.sinh_pos_iff.mpr h)]
    exact this

/-! ### Cociente de los factores arquimedianos -/

/-- Carácter par: `|Γℝ(1 − it)|² ≤ (1 + |t|) |Γℝ(it)|²`. -/
theorem norm_sq_Gammaℝ_cociente_par (t : ℝ) (ht : t ≠ 0) :
    ‖Gammaℝ (1 - t * I)‖ ^ 2 ≤ (1 + |t|) * ‖Gammaℝ (t * I)‖ ^ 2 := by
  have ht2 : t / 2 ≠ 0 := div_ne_zero ht two_ne_zero
  have h1 : (1 - (t : ℂ) * I) / 2 = 1 / 2 + ((-(t / 2) : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : ((t : ℂ) * I) / 2 = ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hre1 : (1 - (t : ℂ) * I).re = 1 := by simp
  have hre2 : ((t : ℂ) * I).re = 0 := by simp
  rw [norm_Gammaℝ, norm_Gammaℝ, h1, h2, hre1, hre2, mul_pow, mul_pow, norm_sq_Gamma_half_add,
    norm_sq_Gamma_mul_I _ ht2, show Real.pi * -(t / 2) = -(Real.pi * (t / 2)) by ring,
    Real.cosh_neg]
  have hpi := Real.pi_pos
  have hpi2 : (Real.pi ^ (-1 / 2 : ℝ)) ^ 2 = Real.pi⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpi.le]
    norm_num
    exact Real.rpow_neg_one Real.pi
  have hpi0 : (Real.pi ^ (-0 / 2 : ℝ)) ^ 2 = 1 := by norm_num
  rw [hpi2, hpi0, one_mul]
  set a := Real.pi * (t / 2) with hadef
  have hch := Real.cosh_pos a
  have hu : 0 < t / 2 * Real.sinh a := by
    have := mul_sinh_pos hpi ht
    rw [hadef, show Real.pi * (t / 2) = (Real.pi / 2) * t by ring]
    have h' := mul_sinh_pos (show 0 < Real.pi / 2 by positivity) ht
    nlinarith
  have hsh := abs_sinh_le_cosh a
  have hkey : t / 2 * Real.sinh a ≤ (1 + |t|) * Real.pi * Real.cosh a := by
    have e1 : t / 2 * Real.sinh a ≤ |t / 2| * |Real.sinh a| := by
      rw [← abs_mul]
      exact le_abs_self _
    have e2 : |t / 2| * |Real.sinh a| ≤ |t / 2| * Real.cosh a :=
      mul_le_mul_of_nonneg_left hsh (abs_nonneg _)
    have e3 : |t / 2| ≤ (1 + |t|) * Real.pi := by
      rw [abs_div, abs_two]
      nlinarith [abs_nonneg t, Real.pi_gt_three]
    nlinarith [abs_nonneg (t / 2)]
  rw [show Real.pi⁻¹ * (Real.pi / Real.cosh a) = 1 / Real.cosh a by field_simp,
    div_le_iff₀ hch]
  rw [show (1 + |t|) * (Real.pi / (t / 2 * Real.sinh a)) * Real.cosh a
      = (1 + |t|) * Real.pi * Real.cosh a / (t / 2 * Real.sinh a) by ring,
    le_div_iff₀ hu]
  linarith

/-- Carácter impar: `|Γℝ(2 − it)|² ≤ (1 + |t|) |Γℝ(1 + it)|²`. -/
theorem norm_sq_Gammaℝ_cociente_impar (t : ℝ) (ht : t ≠ 0) :
    ‖Gammaℝ (1 - t * I + 1)‖ ^ 2 ≤ (1 + |t|) * ‖Gammaℝ (t * I + 1)‖ ^ 2 := by
  have ht2 : t / 2 ≠ 0 := div_ne_zero ht two_ne_zero
  have h1 : (1 - (t : ℂ) * I + 1) / 2 = 1 - ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : ((t : ℂ) * I + 1) / 2 = 1 / 2 + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hre1 : (1 - (t : ℂ) * I + 1).re = 2 := by simp; norm_num
  have hre2 : ((t : ℂ) * I + 1).re = 1 := by simp
  rw [norm_Gammaℝ, norm_Gammaℝ, h1, h2, hre1, hre2, mul_pow, mul_pow,
    AMate.norm_sq_Gamma_one_sub _ ht2, norm_sq_Gamma_half_add]
  have hpi := Real.pi_pos
  have hpi1 : (Real.pi ^ (-2 / 2 : ℝ)) ^ 2 = (Real.pi ^ 2)⁻¹ := by
    rw [show (-2 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one, inv_pow]
  have hpi2 : (Real.pi ^ (-1 / 2 : ℝ)) ^ 2 = Real.pi⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpi.le]
    norm_num
    exact Real.rpow_neg_one Real.pi
  rw [hpi1, hpi2]
  set a := Real.pi * (t / 2) with hadef
  have hch := Real.cosh_pos a
  have hsa : Real.sinh a ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero ht2
  have hS : 0 < |Real.sinh a| := abs_pos.mpr hsa
  have hprod : 0 < t / 2 * Real.sinh a := by
    have h' := mul_sinh_pos (show 0 < Real.pi / 2 by positivity) ht
    rw [hadef, show Real.pi * (t / 2) = Real.pi / 2 * t by ring]
    nlinarith
  have hLHS : (Real.pi ^ 2)⁻¹ * (Real.pi * (t / 2) / Real.sinh a)
      = |t / 2| / (Real.pi * |Real.sinh a|) := by
    have hpos : 0 < (t / 2) / (Real.pi * Real.sinh a) := by
      rw [show (t / 2) / (Real.pi * Real.sinh a)
          = (t / 2 * Real.sinh a) / (Real.pi * Real.sinh a ^ 2) by field_simp]
      have : 0 < Real.sinh a ^ 2 := by positivity
      positivity
    calc (Real.pi ^ 2)⁻¹ * (Real.pi * (t / 2) / Real.sinh a)
        = (t / 2) / (Real.pi * Real.sinh a) := by field_simp
      _ = |(t / 2) / (Real.pi * Real.sinh a)| := (abs_of_pos hpos).symm
      _ = |t / 2| / (Real.pi * |Real.sinh a|) := by
          rw [abs_div, abs_mul, abs_of_pos hpi]
  rw [hLHS, show Real.pi⁻¹ * (Real.pi / Real.cosh a) = 1 / Real.cosh a by field_simp,
    mul_one_div, div_le_div_iff₀ (by positivity) hch]
  set u := |t / 2| with hudef
  have hu : 0 ≤ u := abs_nonneg _
  have hat : |t| = 2 * u := by rw [hudef, abs_div, abs_two]; ring
  have haa : |a| = Real.pi * u := by rw [hadef, abs_mul, abs_of_pos hpi]
  have hcoth := abs_mul_cosh_le a
  rw [haa] at hcoth
  have hk : (1 + Real.pi * u) * |Real.sinh a| ≤ Real.pi * ((1 + 2 * u) * (Real.pi * |Real.sinh a|)) := by
    have h3 := Real.pi_gt_three
    have hpp : 9 < Real.pi * Real.pi := by nlinarith
    have h2p : 0 ≤ 2 * Real.pi * Real.pi - Real.pi := by nlinarith
    have hc : 1 + Real.pi * u ≤ Real.pi * ((1 + 2 * u) * Real.pi) := by
      nlinarith [mul_nonneg hu h2p]
    calc (1 + Real.pi * u) * |Real.sinh a| ≤ Real.pi * ((1 + 2 * u) * Real.pi) * |Real.sinh a| :=
          mul_le_mul_of_nonneg_right hc hS.le
      _ = Real.pi * ((1 + 2 * u) * (Real.pi * |Real.sinh a|)) := by ring
  rw [hat]
  have hfin : Real.pi * (u * Real.cosh a) ≤ Real.pi * ((1 + 2 * u) * (Real.pi * |Real.sinh a|)) := by
    calc Real.pi * (u * Real.cosh a) = Real.pi * u * Real.cosh a := by ring
      _ ≤ (1 + Real.pi * u) * |Real.sinh a| := hcoth
      _ ≤ _ := hk
  exact le_of_mul_le_mul_left hfin hpi

/-! ### Ecuación funcional en `Re s = 0` -/

variable {N : ℕ}

theorem even_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [MulChar.inv_apply_eq_inv']
  constructor
  · intro h
    rwa [inv_eq_one] at h
  · intro h
    rw [h, inv_one]

theorem gammaFactor_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ s = DirichletCharacter.gammaFactor χ s := by
  unfold DirichletCharacter.gammaFactor
  by_cases h : χ.Even
  · rw [if_pos ((even_inv_iff χ).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((even_inv_iff χ).mp h')), if_neg h]

variable [NeZero N]

theorem norm_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ N := by
  unfold gaussSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖χ a * ZMod.stdAddChar a‖ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = N := by simp [ZMod.card]

/-- `|ε(χ)| ≤ √N`. -/
theorem norm_rootNumber_le (χ : DirichletCharacter ℂ N) :
    ‖DirichletCharacter.rootNumber χ‖ ≤ Real.sqrt N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold DirichletCharacter.rootNumber
  rw [norm_div, norm_div, norm_pow, norm_I, one_pow, div_one,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [hre, ← Real.sqrt_eq_rpow, div_le_iff₀ (Real.sqrt_pos.mpr hN), Real.mul_self_sqrt hN.le]
  exact norm_gaussSum_le χ

omit [NeZero N] in
theorem gammaFactor_ne_zero_re_pos (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

omit [NeZero N] in
theorem gammaFactor_mul_I_ne_zero (χ : DirichletCharacter ℂ N) {t : ℝ} (ht : t ≠ 0) :
    DirichletCharacter.gammaFactor χ (t * I) ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
        intro h
        apply ht
        have := congrArg Complex.im h
        simpa using this)).mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
    · refine Gamma_ne_zero fun m h => ht ?_
      have := congrArg Complex.im h
      simpa using this
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp)

/-- **Ecuación funcional en `Re s = 0`** para `χ` primitivo:
`|L(it,χ)| ≤ N √(1 + |t|) |L(1 − it, χ⁻¹)|`. -/
theorem norm_LFunction_mul_I_le_primitivo {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hp : χ.IsPrimitive) (t : ℝ) (ht : t ≠ 0) :
    ‖DirichletCharacter.LFunction χ (t * I)‖
      ≤ N * Real.sqrt (1 + |t|) * ‖DirichletCharacter.LFunction χ⁻¹ (1 - t * I)‖ := by
  have hN1 : N ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set γ := DirichletCharacter.gammaFactor χ with hγdef
  have hγinv : DirichletCharacter.gammaFactor χ⁻¹ = γ := funext (gammaFactor_inv χ)
  have hγ1 : γ (1 - t * I) ≠ 0 := gammaFactor_ne_zero_re_pos χ (by simp)
  have hγ0 : γ (t * I) ≠ 0 := gammaFactor_mul_I_ne_zero χ ht
  have hratio : ‖γ (1 - t * I)‖ ≤ Real.sqrt (1 + |t|) * ‖γ (t * I)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (γ (1 - t * I))), ← Real.sqrt_sq (norm_nonneg (γ (t * I))),
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rcases χ.even_or_odd with he | ho
    · simp only [hγdef, he.gammaFactor_def]
      exact norm_sq_Gammaℝ_cociente_par t ht
    · simp only [hγdef, ho.gammaFactor_def]
      exact norm_sq_Gammaℝ_cociente_impar t ht
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (t * I) (Or.inr hN1)
  have hL' := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - t * I)
    (Or.inr hN1)
  have hFE := hp.completedLFunction_one_sub (1 - t * I)
  rw [show (1 : ℂ) - (1 - t * I) = t * I by ring] at hFE
  rw [hγinv] at hL'
  have hΛ' : DirichletCharacter.completedLFunction χ⁻¹ (1 - t * I)
      = DirichletCharacter.LFunction χ⁻¹ (1 - t * I) * γ (1 - t * I) := by
    rw [hL', div_mul_cancel₀ _ hγ1]
  have hmain : DirichletCharacter.LFunction χ (t * I) * γ (t * I)
      = (N : ℂ) ^ ((1 - t * I) - 1 / 2) * DirichletCharacter.rootNumber χ
        * (DirichletCharacter.LFunction χ⁻¹ (1 - t * I) * γ (1 - t * I)) := by
    rw [hL, div_mul_cancel₀ _ hγ0, hFE, hΛ']
  have hnorm := congrArg norm hmain
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N)] at hnorm
  have hre : ((1 : ℂ) - t * I - 1 / 2).re = 1 / 2 := by simp; norm_num
  rw [hre, ← Real.sqrt_eq_rpow] at hnorm
  have hpos : 0 < ‖γ (t * I)‖ := norm_pos_iff.mpr hγ0
  have hroot := norm_rootNumber_le χ
  have key : ‖DirichletCharacter.LFunction χ (t * I)‖ * ‖γ (t * I)‖
      ≤ (N * Real.sqrt (1 + |t|) * ‖DirichletCharacter.LFunction χ⁻¹ (1 - t * I)‖)
        * ‖γ (t * I)‖ := by
    rw [hnorm]
    calc Real.sqrt N * ‖DirichletCharacter.rootNumber χ‖
          * (‖DirichletCharacter.LFunction χ⁻¹ (1 - t * I)‖ * ‖γ (1 - t * I)‖)
        ≤ Real.sqrt N * Real.sqrt N
          * (‖DirichletCharacter.LFunction χ⁻¹ (1 - t * I)‖
            * (Real.sqrt (1 + |t|) * ‖γ (t * I)‖)) := by gcongr
      _ = (N * Real.sqrt (1 + |t|) * ‖DirichletCharacter.LFunction χ⁻¹ (1 - t * I)‖)
          * ‖γ (t * I)‖ := by
          rw [Real.mul_self_sqrt hN0.le]
          ring
  exact le_of_mul_le_mul_right key hpos

/-- **Cota en `Re s = 0`**: para `χ ≠ 1`,
`|L(it,χ)| ≤ C (1 + |t|)^{1/2} (2 + log(2 + |t|))`. -/
theorem norm_LFunction_mul_I_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (t * I)‖
      ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |t|)) := by
  set q := χ.conductor with hqdef
  have : NeZero q := ⟨χ.conductor_ne_zero⟩
  set χ' := χ.primitiveCharacter with hχ'def
  have hrec : DirichletCharacter.changeLevel χ.conductor_dvd_level χ' = χ :=
    χ.changeLevel_primitiveCharacter
  have hχ' : χ' ≠ 1 := by
    intro h
    apply hχ
    rw [← hrec, h, map_one]
  have hp : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχ'i : χ'⁻¹ ≠ 1 := inv_ne_one.mpr hχ'
  set k := N.primeFactors.card with hkdef
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine ⟨(2 : ℝ) ^ k * q * (1 + 3 * q) + ‖DirichletCharacter.LFunction χ 0‖, by positivity,
    fun t => ?_⟩
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hA : (0 : ℝ) ≤ (2 : ℝ) ^ k * q * (1 + 3 * q) := by positivity
  by_cases ht : t = 0
  · subst ht
    simp only [ofReal_zero, zero_mul, abs_zero, add_zero, Real.one_rpow, mul_one]
    have h2 : (1 : ℝ) ≤ 2 + Real.log 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      linarith
    nlinarith [norm_nonneg (DirichletCharacter.LFunction χ 0)]
  have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ' (s := t * I)
    (Or.inl hχ')
  rw [hrec] at hcl
  have hprod : ‖∏ p ∈ N.primeFactors, (1 - χ' p * (p : ℂ) ^ (-((t : ℂ) * I)))‖ ≤ 2 ^ k := by
    rw [norm_prod]
    calc ∏ p ∈ N.primeFactors, ‖1 - χ' p * (p : ℂ) ^ (-((t : ℂ) * I))‖
        ≤ ∏ _p ∈ N.primeFactors, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
          have : (-((t : ℂ) * I)).re = 0 := by simp
          rw [this, Real.rpow_zero, mul_one]
          linarith [DirichletCharacter.norm_le_one χ' (p : ZMod q)]
      _ = 2 ^ k := by rw [Finset.prod_const]
  have hprim := norm_LFunction_mul_I_le_primitivo hχ' hp t ht
  have hone := norm_LFunction_one_add_le hχ'i (-t)
  rw [show (1 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - t * I by push_cast; ring, abs_neg] at hone
  rw [hcl, norm_mul, ← Real.sqrt_eq_rpow]
  have hs : 0 ≤ Real.sqrt (1 + |t|) := Real.sqrt_nonneg _
  calc ‖DirichletCharacter.LFunction χ' (t * I)‖
        * ‖∏ p ∈ N.primeFactors, (1 - χ' p * (p : ℂ) ^ (-((t : ℂ) * I)))‖
      ≤ (q * Real.sqrt (1 + |t|) * ((1 + 3 * q) * (2 + Real.log (2 + |t|)))) * 2 ^ k := by
        gcongr
        exact hprim.trans (by gcongr)
    _ = ((2 : ℝ) ^ k * q * (1 + 3 * q)) * Real.sqrt (1 + |t|) * (2 + Real.log (2 + |t|)) := by
        ring
    _ ≤ ((2 : ℝ) ^ k * q * (1 + 3 * q) + ‖DirichletCharacter.LFunction χ 0‖)
          * Real.sqrt (1 + |t|) * (2 + Real.log (2 + |t|)) := by
        gcongr
        exact le_add_of_nonneg_right (norm_nonneg _)

end AMate.Dirichlet
