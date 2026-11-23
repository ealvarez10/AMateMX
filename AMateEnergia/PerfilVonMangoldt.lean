import AMateEnergia.ZetaIntegral

/-!
# Perfil de von Mangoldt de conductor 1 y su transformada meromorfa

Pieza 1 del puente de conductor 1 hacia `RiemannHypothesis` y `E_Q`:

* `zeta_real_neg_of_mem_Ioo`, `zeta_ofReal_ne_zero`: `ζ(x) < 0` en `(0, 1)` y `ζ(x) ≠ 0` en todo el
  semieje real positivo `(0, ∞)` (ausencia total de ceros reales / de Siegel para conductor 1).
* `G_vonMangoldt`: el perfil `G(y) = ∑_{1 ≤ n ≤ y} Λ(n)(y/n − 1) − y log y + (1 + γ_E) y`, su
  medibilidad y la cota cuadrática elemental `|G(y)| ≤ (4 + |γ_E|) y²` para `y ≥ 1`.
* `mellin_G_vonMangoldt`: identidad exacta de Mellin en `Re s > 2`.
* `Phi_zeta`: prolongación meromorfa explícita a `{Re s > 0}` mediante `dslope` en `s = 1`,
  igual a la transformada de Laplace `∫_0^∞ G(e^u) e^{−su} du` en `Re s > 2`, holomorfa fuera de los
  ceros de `ζ` y con polo simple de residuo no nulo en cada cero `ρ` de `ζ` con `Re ρ > 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ArithmeticFunction.vonMangoldt

namespace AMate

/-! ### Ausencia de ceros reales de `ζ` en `(0, ∞)` -/

/-- En `(0, 1)`, `ζ(x)` es real y estrictamente negativo: `x/(x − 1) < 0` y la integral de `{t}`
es no negativa. -/
theorem zeta_real_neg_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hx_re : 0 < (x : ℂ).re := by simpa using hx0
  have hx_ne1 : (x : ℂ) ≠ 1 := by
    intro h
    have : x = 1 := by exact_mod_cast h
    linarith
  have hζ := zeta_eq_integral_fract hx_re hx_ne1
  have hfract_re : 0 ≤ (fractIntegral (x : ℂ)).re := by
    unfold fractIntegral
    have hcongr : ∀ t ∈ Ioi (1 : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(x : ℂ) - 1)
          = ((Int.fract t * t ^ (-x - 1) : ℝ) : ℂ) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      rw [show -(x : ℂ) - 1 = ((-x - 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow ht0.le, ← ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal, ofReal_re]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (lt_trans one_pos ht).le _)
  have hdiv_re : ((x : ℂ) / ((x : ℂ) - 1)).re = x / (x - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  have hmul_re : ((x : ℂ) * fractIntegral (x : ℂ)).re = x * (fractIntegral (x : ℂ)).re := by
    simp [mul_re]
  have hre := congrArg Complex.re hζ
  rw [sub_re, hdiv_re, hmul_re] at hre
  have hneg : x / (x - 1) < 0 := div_neg_of_pos_of_neg hx0 (by linarith)
  have hnonneg : 0 ≤ x * (fractIntegral (x : ℂ)).re := mul_nonneg hx0.le hfract_re
  linarith

/-- Para conductor 1, `ζ` no tiene ningún cero en el semieje real `(0, ∞)`. -/
theorem zeta_ofReal_ne_zero {x : ℝ} (hx : 0 < x) : riemannZeta (x : ℂ) ≠ 0 := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · intro h0
    have := zeta_real_neg_of_mem_Ioo hx hx1
    rw [h0, zero_re] at this
    exact lt_irrefl 0 this
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hx1)

/-! ### El perfil de von Mangoldt `G_vonMangoldt` -/

/-- Rampa de von Mangoldt `∑_{1 ≤ n ≤ y} Λ(n) (y/n − 1)`. -/
noncomputable def rampaVonMangoldt (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1)

/-- Perfil centrado de von Mangoldt para `ζ(s)` (conductor 1):
`G(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y/n − 1) − y log y + (1 + γ_E) y`. -/
noncomputable def G_vonMangoldt (y : ℝ) : ℝ :=
  rampaVonMangoldt y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

theorem rampaVonMangoldt_eq_range_of_gt (y : ℝ) {N : ℕ} (hN : ⌊y⌋₊ < N) :
    rampaVonMangoldt y = ∑ n ∈ Finset.range N, Λ n * max (y / (n : ℝ) - 1) 0 := by
  unfold rampaVonMangoldt
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range N := fun n hn => by
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hy0 : 0 ≤ y := by
      by_contra! hneg
      have hfl : ⌊y⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
      omega
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hn_le : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hy0)
    have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, one_le_div hn_pos]
      exact hn_le
    rw [max_eq_left hnonneg]
  · intro n hn hn'
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hgt : ⌊y⌋₊ < n := by
        by_contra hle
        exact hn' (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hy_lt : y < (n : ℝ) := by
        rcases lt_or_ge y 0 with hneg | hy0
        · linarith
        · exact (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast hgt)
      have hle0 : y / (n : ℝ) - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hn_pos]
        exact hy_lt.le
      rw [max_eq_right hle0, mul_zero]

theorem rampaVonMangoldt_eq_tsum (y : ℝ) :
    rampaVonMangoldt y = ∑' n : ℕ, Λ n * max (y / (n : ℝ) - 1) 0 := by
  rw [rampaVonMangoldt_eq_range_of_gt y (Nat.lt_succ_self ⌊y⌋₊)]
  symm
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  by_cases hn0 : n = 0
  · subst hn0; simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hy_lt : y < (n : ℝ) := by
      rcases lt_or_ge y 0 with hneg | hy0
      · linarith
      · exact (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast hn)
    have hle0 : y / (n : ℝ) - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn_pos]
      exact hy_lt.le
    rw [max_eq_right hle0, mul_zero]

theorem measurable_rampaVonMangoldt : Measurable rampaVonMangoldt := by
  refine measurable_of_tendsto_metrizable
    (f := fun N (y : ℝ) => ∑ n ∈ Finset.range N, Λ n * max (y / (n : ℝ) - 1) 0)
    (fun N => by fun_prop) (tendsto_pi_nhds.mpr fun y => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop ⌊y⌋₊] with N hN
  exact rampaVonMangoldt_eq_range_of_gt y hN

theorem measurable_G_vonMangoldt : Measurable G_vonMangoldt := by
  unfold G_vonMangoldt
  exact (measurable_rampaVonMangoldt.sub (measurable_id.mul Real.measurable_log)).add
    (measurable_const.mul measurable_id)

theorem rampaVonMangoldt_nonneg (y : ℝ) : 0 ≤ rampaVonMangoldt y := by
  rw [rampaVonMangoldt_eq_range_of_gt y (Nat.lt_succ_self ⌊y⌋₊)]
  exact Finset.sum_nonneg fun n _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

theorem rampaVonMangoldt_le_sq {y : ℝ} (hy : 1 ≤ y) : rampaVonMangoldt y ≤ y ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  unfold rampaVonMangoldt
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1)
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, y := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
        have hn_le : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hy0.le)
        have hsub_nn : 0 ≤ y / (n : ℝ) - 1 := by
          rw [sub_nonneg, one_le_div hn_pos]; exact hn_le
        have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) :=
          (Real.log_le_sub_one_of_pos hn_pos).trans (by linarith)
        calc Λ n * (y / (n : ℝ) - 1)
            ≤ Real.log (n : ℝ) * (y / (n : ℝ)) :=
              mul_le_mul ArithmeticFunction.vonMangoldt_le_log (by linarith) hsub_nn
                (Real.log_nonneg (by exact_mod_cast hn.1))
          _ ≤ (n : ℝ) * (y / (n : ℝ)) :=
              mul_le_mul_of_nonneg_right hlog_le (by positivity)
          _ = y := mul_div_cancel₀ y hn_pos.ne'
    _ = (⌊y⌋₊ : ℝ) * y := by simp
    _ ≤ y * y := mul_le_mul_of_nonneg_right (Nat.floor_le hy0.le) hy0.le
    _ = y ^ 2 := (sq y).symm

/-- Cota cuadrática elemental: `|G(y)| ≤ (4 + |γ_E|) y²` para todo `y ≥ 1`. -/
theorem abs_G_vonMangoldt_le {y : ℝ} (hy : 1 ≤ y) :
    |G_vonMangoldt y| ≤ (4 + |Real.eulerMascheroniConstant|) * y ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hy_sq : y ≤ y ^ 2 := by nlinarith
  have hramp_nonneg := rampaVonMangoldt_nonneg y
  have hramp_le := rampaVonMangoldt_le_sq hy
  have hlog_nn : 0 ≤ y * Real.log y := mul_nonneg hy0.le (Real.log_nonneg hy)
  have hlog_le : y * Real.log y ≤ y ^ 2 := by
    have : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    nlinarith
  have hlin_le : |(1 + Real.eulerMascheroniConstant) * y|
      ≤ (1 + |Real.eulerMascheroniConstant|) * y ^ 2 := by
    rw [abs_mul, abs_of_pos hy0]
    have h1 : |1 + Real.eulerMascheroniConstant| ≤ 1 + |Real.eulerMascheroniConstant| := by
      simpa using abs_add_le (1 : ℝ) Real.eulerMascheroniConstant
    calc |1 + Real.eulerMascheroniConstant| * y
        ≤ (1 + |Real.eulerMascheroniConstant|) * y := mul_le_mul_of_nonneg_right h1 hy0.le
      _ ≤ (1 + |Real.eulerMascheroniConstant|) * y ^ 2 :=
          mul_le_mul_of_nonneg_left hy_sq (by positivity)
  unfold G_vonMangoldt
  calc |rampaVonMangoldt y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y|
      ≤ |rampaVonMangoldt y - y * Real.log y| + |(1 + Real.eulerMascheroniConstant) * y| :=
        abs_add_le _ _
    _ ≤ (|rampaVonMangoldt y| + |y * Real.log y|) + |(1 + Real.eulerMascheroniConstant) * y| := by
        gcongr
        exact abs_sub _ _
    _ ≤ (y ^ 2 + y ^ 2) + (1 + |Real.eulerMascheroniConstant|) * y ^ 2 := by
        rw [abs_of_nonneg hramp_nonneg, abs_of_nonneg hlog_nn]
        linarith
    _ ≤ (4 + |Real.eulerMascheroniConstant|) * y ^ 2 := by
        nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-! ### Transformada de Mellin de `G_vonMangoldt` en `Re s > 2` -/

theorem integrableOn_rampa_unitaria (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hg : IntegrableOn (fun y : ℝ => y ^ (-s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hg.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Complex.measurable_ofReal.comp (by fun_prop)).mul (by measurability)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    have hmax_le : max (y / (n : ℝ) - 1) 0 ≤ y := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hy0.le]
      · have hdiv : y / (n : ℝ) ≤ y := div_le_self hy0.le (by exact_mod_cast hn)
        exact max_le (by linarith) hy0.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc max (y / (n : ℝ) - 1) 0 * y ^ (-s.re - 1)
        ≤ y * y ^ (-s.re - 1) := mul_le_mul_of_nonneg_right hmax_le (Real.rpow_nonneg hy0.le _)
      _ = y ^ (1 : ℝ) * y ^ (-s.re - 1) := by rw [Real.rpow_one]
      _ = y ^ (-s.re) := by rw [← Real.rpow_add hy0]; congr 1; ring

theorem mellin_rampa_unitaria {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; rw [h] at hs; norm_num at hs)
  have hint := integrableOn_rampa_unitaria n hs
  rw [← Ioc_union_Ioi_eq_Ioi hn1,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hn1))]
  have hzero : ∫ y in Ioc 1 (n : ℝ), ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hle : y / (n : ℝ) - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]
      exact hy.2
    simp [max_eq_right hle]
  rw [hzero, zero_add]
  have hcongr : ∀ y ∈ Ioi (n : ℝ),
      ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
        = (1 / (n : ℂ)) * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-s - 1) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hn0 hy
    have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
    have hge : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, one_le_div hn0]
      exact hy.le
    rw [max_eq_left hge]
    push_cast
    rw [sub_mul, div_mul_eq_mul_div, show (y : ℂ) * (y : ℂ) ^ (-s - 1) / (n : ℂ)
        = (1 / (n : ℂ)) * ((y : ℂ) * (y : ℂ) ^ (-s - 1)) by ring,
      show -s = (-s - 1) + 1 by ring, cpow_add _ _ hyC, cpow_one]
    ring
  have hi1 : IntegrableOn (fun y : ℝ => (1 / (n : ℂ)) * (y : ℂ) ^ (-s)) (Ioi (n : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hn0).const_mul _
  have hi2 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hn0
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub hi1 hi2, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) hn0,
    integral_Ioi_cpow_of_lt (by simp; linarith) hn0]
  have he : ((n : ℝ) : ℂ) ^ (-s + 1) = (n : ℂ) * (n : ℂ) ^ (-s) := by
    rw [ofReal_natCast, cpow_add _ _ hnC, cpow_one]
    ring
  rw [he, ofReal_natCast, show -s - 1 + 1 = -s by ring]
  have h1s : -s + 1 ≠ 0 := by intro h; apply hs1; linear_combination -h
  field_simp
  ring

theorem mellin_log_pow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) ∧
      ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  set e : ℝ := (s.re - 1) / 2
  have he0 : 0 < e := by simp [e]; linarith
  have hmaj : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := by
    intro c y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc Real.log y * y ^ c.re ≤ (y ^ e / e) * y ^ c.re :=
          mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hy0.le he0) (Real.rpow_nonneg hy0.le _)
      _ = y ^ e * y ^ c.re / e := by ring
  have hint : IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) := by
    have hc : e + (-s).re < -1 := by simp [e]; linarith
    refine ((integrableOn_Ioi_rpow_of_lt hc one_pos).div_const e).mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp Real.measurable_log).mul
        (by measurability)).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => hmaj (-s) y hy)
  refine ⟨hint, ?_⟩
  have htend : Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
    have hc : 0 < -(e + (-s + 1).re) := by simp [e]; linarith
    have h0 := (tendsto_rpow_neg_atTop hc).div_const e
    rw [neg_neg, zero_div] at h0
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 1] with y hy using hmaj (-s + 1) y hy
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd : ∀ y ∈ Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
        ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (lt_of_lt_of_le one_pos hy).ne'
    have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have hi_cpow : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd ((hint.const_mul _).add hi_cpow) htend
  rw [integral_add (hint.const_mul _) hi_cpow, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos] at hftc
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at hftc
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; rw [h] at hs; norm_num at hs)
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at hftc ⊢
  linear_combination hftc

/-- Identidad exacta de Mellin del perfil `G_vonMangoldt` en `Re s > 2`. -/
theorem mellin_G_vonMangoldt {s : ℂ} (hs2 : 2 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((G_vonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1
          - (1 + (Real.eulerMascheroniConstant : ℂ)) * s) / (s * (s - 1)) := by
  have hs : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; rw [h] at hs; norm_num at hs)
  -- Serie de las rampas intercambiada con la integral.
  let T : ℕ → ℝ → ℂ := fun n y =>
    ((Λ n : ℝ) : ℂ) * (((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  have hT_int : ∀ n, IntegrableOn (T n) (Ioi 1) := fun n =>
    (integrableOn_rampa_unitaria n hs).const_mul _
  have hT_val : ∀ n, ∫ y in Ioi (1 : ℝ), T n y
      = LSeries.term (fun k => ((Λ k : ℝ) : ℂ)) s n / (s * (s - 1)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [T]
    · simp only [T]
      rw [integral_const_mul, mellin_rampa_unitaria hn hs, LSeries.term_of_ne_zero hn.ne', cpow_neg]
      ring
  have hT_norm_sum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖T n y‖ := by
    have hLS := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (s.re : ℂ)) (by simp [hs])
    refine Summable.of_nonneg_of_le (fun n => setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)
      (fun n => ?_) (hLS.norm.div_const (s.re * (s.re - 1)))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [T]
    · have hcongr : ∀ y ∈ Ioi (1 : ℝ),
          ‖T n y‖ = Λ n * (max (y / (n : ℝ) - 1) 0 * y ^ (-s.re - 1)) := by
        intro y hy
        have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
        simp only [T, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.norm_of_nonneg (le_max_right _ _), Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
      have hreal_int : ((∫ y in Ioi (1 : ℝ), max (y / (n : ℝ) - 1) 0 * y ^ (-s.re - 1) : ℝ) : ℂ)
          = (n : ℂ) ^ (-(s.re : ℂ)) / ((s.re : ℂ) * ((s.re : ℂ) - 1)) := by
        rw [← integral_complex_ofReal]
        have hc : ∀ y ∈ Ioi (1 : ℝ),
            ((max (y / (n : ℝ) - 1) 0 * y ^ (-s.re - 1) : ℝ) : ℂ)
              = ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-(s.re : ℂ) - 1) := by
          intro y hy
          have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
          rw [ofReal_mul, show -(s.re : ℂ) - 1 = ((-s.re - 1 : ℝ) : ℂ) by push_cast; ring,
            ofReal_cpow hy0.le]
        rw [setIntegral_congr_fun measurableSet_Ioi hc]
        exact mellin_rampa_unitaria hn (by simpa using hs)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hrhs_re : ((n : ℂ) ^ (-(s.re : ℂ)) / ((s.re : ℂ) * ((s.re : ℂ) - 1))).re
          = (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
          show -(s.re : ℂ) = ((-s.re : ℝ) : ℂ) by push_cast; ring,
          ← ofReal_cpow hn_pos.le, ← ofReal_one, ← ofReal_sub, ← ofReal_mul, ← ofReal_div, ofReal_re]
      have hint_eq : ∫ y in Ioi (1 : ℝ), max (y / (n : ℝ) - 1) 0 * y ^ (-s.re - 1)
          = (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
        have := congrArg Complex.re hreal_int
        simpa [hrhs_re] using this
      rw [hint_eq, LSeries.term_of_ne_zero hn.ne']
      have hnorm_term : ‖((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (s.re : ℂ)‖ = Λ n * (n : ℝ) ^ (-s.re) := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
          ofReal_re, Real.rpow_neg hn_pos.le, div_eq_mul_inv]
      rw [hnorm_term]
      exact le_of_eq (by ring)
  have h_ramp_hasSum := hasSum_integral_of_summable_integral_norm hT_int hT_norm_sum
  have h_ramp_pt : ∀ y ∈ Ioi (1 : ℝ),
      ((rampaVonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) = ∑' n, T n y := by
    intro y _
    rw [rampaVonMangoldt_eq_tsum y]
    have hfin : ∀ n ∉ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / (n : ℝ) - 1) 0 = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      by_cases hn0 : n = 0
      · subst hn0; simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hy_lt : y < (n : ℝ) := by
          rcases lt_or_ge y 0 with hneg | hy0
          · linarith
          · exact (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast hn)
        rw [max_eq_right ((sub_nonpos.mpr ((div_le_one hn_pos).mpr hy_lt.le))), mul_zero]
    rw [tsum_eq_sum hfin]
    symm
    rw [tsum_eq_sum (s := Finset.range (⌊y⌋₊ + 1)) fun n hn => by
      have h0 := hfin n hn
      simp only [T, ← mul_assoc, ← ofReal_mul, h0, ofReal_zero, zero_mul]]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by simp only [T]; ring
  have hI_ramp_eq : ∫ y in Ioi (1 : ℝ), ((rampaVonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = -deriv riemannZeta s / riemannZeta s / (s * (s - 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi h_ramp_pt, ← h_ramp_hasSum.tsum_eq]
    simp_rw [hT_val, tsum_div_const]
    have hLS_eq := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    rw [LSeries] at hLS_eq
    rw [hLS_eq]
  have hi_ramp : IntegrableOn
      (fun y : ℝ => ((rampaVonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
    have hg : IntegrableOn (fun y : ℝ => y ^ (1 - s.re)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hg.mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp measurable_rampaVonMangoldt).mul
        (by measurability)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
      have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rampaVonMangoldt_nonneg y),
        Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      calc rampaVonMangoldt y * y ^ (-s.re - 1)
          ≤ y ^ 2 * y ^ (-s.re - 1) :=
            mul_le_mul_of_nonneg_right (rampaVonMangoldt_le_sq hy.le) (Real.rpow_nonneg hy0.le _)
        _ = y ^ (2 : ℝ) * y ^ (-s.re - 1) := by rw [Real.rpow_two]
        _ = y ^ (1 - s.re) := by rw [← Real.rpow_add hy0]; congr 1; ring
  obtain ⟨hi_log, hval_log⟩ := mellin_log_pow hs
  have hi_lin : IntegrableOn
      (fun y : ℝ => ((1 + (Real.eulerMascheroniConstant : ℂ)) * (y : ℂ) ^ (-s))) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos).const_mul _
  have hpt_G : ∀ y ∈ Ioi (1 : ℝ),
      ((G_vonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
        = ((rampaVonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
          - ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)
          + (1 + (Real.eulerMascheroniConstant : ℂ)) * (y : ℂ) ^ (-s) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
    have hy_pow : (y : ℂ) * (y : ℂ) ^ (-s - 1) = (y : ℂ) ^ (-s) := by
      rw [show -s = (-s - 1) + 1 by ring, cpow_add _ _ hyC, cpow_one]
      ring
    unfold G_vonMangoldt
    push_cast
    calc (((rampaVonMangoldt y : ℂ) - (y : ℂ) * (Real.log y : ℂ)
            + (1 + (Real.eulerMascheroniConstant : ℂ)) * (y : ℂ)) * (y : ℂ) ^ (-s - 1))
        = (rampaVonMangoldt y : ℂ) * (y : ℂ) ^ (-s - 1)
          - (Real.log y : ℂ) * ((y : ℂ) * (y : ℂ) ^ (-s - 1))
          + (1 + (Real.eulerMascheroniConstant : ℂ)) * ((y : ℂ) * (y : ℂ) ^ (-s - 1)) := by ring
      _ = _ := by rw [hy_pow]
  have hi_sub : IntegrableOn
      (fun y : ℝ => ((rampaVonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
        - ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) :=
    Integrable.sub hi_ramp hi_log
  rw [setIntegral_congr_fun measurableSet_Ioi hpt_G,
    integral_add hi_sub hi_lin, integral_sub hi_ramp hi_log,
    hI_ramp_eq, hval_log, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  simp only [ofReal_one, one_cpow]
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have e_s1 : -s + 1 = -(s - 1) := by ring
  rw [e_s1]
  field_simp
  ring

/-! ### Prolongación meromorfa `Phi_zeta` y sus polos simples -/

/-- `(s − 1) ζ(s)` completada con el valor `1` en `s = 1`. -/
noncomputable def zetaEntera : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem zetaEntera_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaEntera s = (s - 1) * riemannZeta s := by
  simp [zetaEntera, hs]

@[simp] theorem zetaEntera_one : zetaEntera 1 = 1 := by
  simp [zetaEntera]

theorem differentiable_zetaEntera : Differentiable ℂ zetaEntera := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := (1 : ℂ)) Filter.univ_mem]
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz1 : z ≠ 1 := by simpa using hz
    apply DifferentiableAt.differentiableWithinAt
    have hev : zetaEntera =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
      exact zetaEntera_of_ne_one hw
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq hev
  · simpa only [zetaEntera, continuousAt_update_same] using riemannZeta_residue_one

theorem deriv_zetaEntera_one : deriv zetaEntera 1 = Real.eulerMascheroniConstant := by
  have hd : HasDerivAt zetaEntera (deriv zetaEntera 1) 1 := (differentiable_zetaEntera 1).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [slope_def_field, zetaEntera_of_ne_one hs1, zetaEntera_one]
  field_simp

theorem deriv_zetaEntera_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv zetaEntera s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : zetaEntera =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact zetaEntera_of_ne_one hw
  rw [hev.deriv_eq]
  have h : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]
  ring

theorem zetaEntera_ne_zero_iff {w : ℂ} : zetaEntera w ≠ 0 ↔ riemannZeta w ≠ 0 := by
  by_cases hw : w = 1
  · subst hw
    rw [zetaEntera_one]
    exact ⟨fun _ => riemannZeta_one_ne_zero, fun _ => one_ne_zero⟩
  · rw [zetaEntera_of_ne_one hw]
    exact ⟨fun h hz => h (by rw [hz, mul_zero]), mul_ne_zero (sub_ne_zero.mpr hw)⟩

/-- Numerador regularizado en `s = 1`: `ζ₁'/ζ₁ − γ_E s + (1 − s)`. -/
noncomputable def N_zeta (s : ℂ) : ℂ :=
  deriv zetaEntera s / zetaEntera s - (Real.eulerMascheroniConstant : ℂ) * s + (1 - s)

theorem N_zeta_one : N_zeta 1 = 0 := by
  unfold N_zeta
  rw [deriv_zetaEntera_one, zetaEntera_one]
  ring

/-- Transformada de Laplace meromorfa `Φ_ζ(s) = −dslope N_ζ 1 (s) / s`. -/
noncomputable def Phi_zeta (s : ℂ) : ℂ := -(dslope N_zeta 1 s) / s

theorem Phi_zeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    Phi_zeta s = -(deriv zetaEntera s / zetaEntera s
      - (Real.eulerMascheroniConstant : ℂ) * s + (1 - s)) / (s * (s - 1)) := by
  unfold Phi_zeta
  rw [dslope_of_ne _ hs, slope_def_field, N_zeta_one, N_zeta]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- En `Re s > 2`, `Φ_ζ(s)` coincide con la integral de Laplace `∫_0^∞ G(e^u) e^{−su} du`. -/
theorem Phi_zeta_eq_laplace {s : ℂ} (hs : 2 < s.re) :
    Phi_zeta s = ∫ u in Ioi (0 : ℝ), ((G_vonMangoldt (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  -- Cambio de variable `y = e^u` entre `(0, ∞)` y `(1, ∞)`.
  have himg : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.one_lt_exp_iff.mpr hu
    · intro hy
      exact ⟨Real.log y, Real.log_pos hy, Real.exp_log (lt_trans one_pos hy)⟩
  have hchange : ∫ u in Ioi (0 : ℝ), ((G_vonMangoldt (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)
      = ∫ y in Ioi (1 : ℝ), ((G_vonMangoldt y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) := by
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [abs_of_pos (Real.exp_pos u), Complex.real_smul,
      Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
      mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  rw [hchange, mellin_G_vonMangoldt hs, Phi_zeta_of_ne_one hs1,
    deriv_zetaEntera_of_ne_one hs1, zetaEntera_of_ne_one hs1]
  congr 1
  field_simp
  ring

theorem zetaEntera_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, zetaEntera w = 0 := by
  intro hz
  have hon : AnalyticOnNhd ℂ zetaEntera Set.univ :=
    fun w _ => differentiable_zetaEntera.analyticAt w
  have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hz
  have h1 := hzero (Set.mem_univ 1)
  rw [zetaEntera_one] at h1
  exact one_ne_zero h1

/-- Los ceros de `ζ` son aislados en todo `ℂ`. -/
theorem ceros_aislados_zeta (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  rcases (differentiable_zetaEntera.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (zetaEntera_not_eventually_zero z)
  · filter_upwards [h] with w hw
    exact zetaEntera_ne_zero_iff.mp hw

/-- `Φ_ζ` es analítica en todo punto `ρ ≠ 0` donde `ζ(ρ) ≠ 0` (incluido `ρ = 1`). -/
theorem analyticAt_Phi_zeta {ρ : ℂ} (hρ0 : ρ ≠ 0) (hζ : riemannZeta ρ ≠ 0) :
    AnalyticAt ℂ Phi_zeta ρ := by
  have hgρ : zetaEntera ρ ≠ 0 := zetaEntera_ne_zero_iff.mpr hζ
  have hUo : IsOpen {s : ℂ | zetaEntera s ≠ 0} :=
    isOpen_ne_fun differentiable_zetaEntera.continuous continuous_const
  have hNd : DifferentiableOn ℂ N_zeta {s : ℂ | zetaEntera s ≠ 0} := by
    intro s hs
    have hA := differentiable_zetaEntera.analyticAt s
    exact ((((hA.deriv.differentiableAt.div hA.differentiableAt hs).sub
      ((differentiableAt_const _).mul differentiableAt_id)).add
      ((differentiableAt_const 1).sub differentiableAt_id))).differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope N_zeta 1) {s : ℂ | zetaEntera s ≠ 0} :=
    (differentiableOn_dslope (hUo.mem_nhds (by show zetaEntera 1 ≠ 0; rw [zetaEntera_one]; exact one_ne_zero))).mpr hNd
  exact (hDd.analyticAt (hUo.mem_nhds hgρ)).neg.div analyticAt_id hρ0

/-- En cada cero `ρ` de `ζ` con `Re ρ > 0`, `Φ_ζ` tiene un polo simple `c / (s − ρ) + h(s)` con
`c ≠ 0` y `h` analítica en `ρ`. -/
theorem polo_simple_Phi_zeta {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ_re : 0 < ρ.re) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, Phi_zeta s = c / (s - ρ) + h s := by
  have hρ0 : ρ ≠ 0 := by intro h; rw [h, zero_re] at hρ_re; exact lt_irrefl 0 hρ_re
  have hρ1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hζ)
  have hg0 : zetaEntera ρ = 0 := by rw [zetaEntera_of_ne_one hρ1, hζ, mul_zero]
  have hA : AnalyticAt ℂ zetaEntera ρ := differentiable_zetaEntera.analyticAt ρ
  have htop : analyticOrderAt zetaEntera ρ ≠ ⊤ :=
    fun h => zetaEntera_not_eventually_zero ρ (analyticOrderAt_eq_top.mp h)
  obtain ⟨q, hq_an, hq_ne, hfg⟩ := hA.analyticOrderAt_ne_top.mp htop
  set m : ℕ := analyticOrderNatAt zetaEntera ρ with hm_def
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by omega
    have h_ord0 : analyticOrderAt zetaEntera ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, ← hm_def, hm_zero, Nat.cast_zero]
    exact (hA.analyticOrderAt_eq_zero.mp h_ord0) hg0
  have hlogDeriv : ∀ᶠ s in 𝓝[≠] ρ,
      deriv zetaEntera s / zetaEntera s = (m : ℂ) / (s - ρ) + deriv q s / q s := by
    have hev : ∀ᶠ s in 𝓝 ρ,
        (∀ᶠ z in 𝓝 s, zetaEntera z = (z - ρ) ^ m • q z) ∧ q s ≠ 0 ∧ AnalyticAt ℂ q s :=
      (Eventually.eventually_nhds hfg).and
        ((hq_an.continuousAt.eventually_ne hq_ne).and hq_an.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s ⟨hs1, hs2, hs3⟩ hsne
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hd : HasDerivAt (fun z => (z - ρ) ^ m * q z)
        ((m : ℂ) * (s - ρ) ^ (m - 1) * 1 * q s + (s - ρ) ^ m * deriv q s) s :=
      (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
    have e1 : deriv zetaEntera s = deriv (fun z => (z - ρ) ^ m * q z) s := by
      apply EventuallyEq.deriv_eq
      filter_upwards [hs1] with z hz
      rw [hz, smul_eq_mul]
    have e2 : zetaEntera s = (s - ρ) ^ m * q s := by
      simpa only [smul_eq_mul] using hs1.self_of_nhds
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [e1, hd.deriv, e2, hk, Nat.add_sub_cancel, pow_succ]
    field_simp
  have hr_an : AnalyticAt ℂ (fun s : ℂ => 1 / (s * (s - 1))) ρ :=
    analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
  have hdslope_an : AnalyticAt ℂ (dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ) ρ := by
    obtain ⟨p, hp⟩ := hr_an
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  set c : ℂ := -(m : ℂ) / (ρ * (ρ - 1))
  have hc_ne : c ≠ 0 := by
    simp only [c]
    exact div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm_pos.ne'))
      (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
  refine ⟨c, hc_ne, fun s => -((m : ℂ) * dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ s)
      - (deriv q s / q s - (Real.eulerMascheroniConstant : ℂ) * s + (1 - s))
        * (1 / (s * (s - 1))), ?_, ?_⟩
  · exact ((analyticAt_const.mul hdslope_an).neg).sub
      (((((hq_an.deriv.div hq_an hq_ne).sub (analyticAt_const.mul analyticAt_id)).add
        (analyticAt_const.sub analyticAt_id))).mul hr_an)
  · have hne0 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 0 := nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ0)
    have hne1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 1 := nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ1)
    filter_upwards [hlogDeriv, hne0, hne1, self_mem_nhdsWithin] with s hs hs0 hs1 hsρ
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
    rw [Phi_zeta_of_ne_one hs1, hs, dslope_of_ne _ hsρ, slope_def_field]
    simp only [c]
    field_simp
    ring

end AMate
