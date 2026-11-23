import Mathlib

/-!
# Representación integral de `ζ` en `Re s > 0`

Para `Re s > 0`, `s ≠ 1`:

`ζ(s) = s/(s − 1) − s ∫_1^∞ {x} x^{−s−1} dx`.

Se demuestra primero en `Re s > 1`, integrando por tramos `[n, n+1]` y usando la serie de
Dirichlet, y se prolonga a `Re s > 0` con el teorema de identidad: la integral es una
transformada de Mellin holomorfa y `(s − 1) ζ(s)` es entera (`riemannZeta₁`). Como corolario,
`‖ζ(s)‖ ≤ ‖s/(s − 1)‖ + ‖s‖/Re s`, cota a priori para Phragmén–Lindelöf.

Es la base común de `zeta_recta_critica` y de `E_eq_integral` (estado 45, (2.4) y (6.1)).
-/

open MeasureTheory Set Filter Topology Complex

namespace AMate

/-- Integral exacta en un tramo: `s ∫_n^{n+1} (x − n) x^{−s−1} dx`. -/
theorem block_integral {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    s * ∫ x in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) - n) * (x : ℂ) ^ (-s - 1)
      = (((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) - ((n : ℂ) + 1) ^ (-s) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : ∀ x ∈ uIcc (n : ℝ) ((n : ℝ) + 1), (0 : ℝ) < x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    linarith [hx.1]
  have h0 : (0 : ℝ) ∉ uIcc (n : ℝ) ((n : ℝ) + 1) := fun h => lt_irrefl _ (hpos 0 h)
  have hsplit : EqOn (fun x : ℝ => ((x : ℂ) - n) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ (-s) - (n : ℂ) * (x : ℂ) ^ (-s - 1)) (uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx).ne'
    simp only
    rw [sub_mul]
    congr 1
    rw [show -s = (-s - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one]
    ring_nf
  have hi1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume (n : ℝ) ((n : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  have hi2 : IntervalIntegrable (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (-s - 1)) volume
      (n : ℝ) ((n : ℝ) + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul]
  have hne1 : -s ≠ -1 := fun h => hs1 (by linear_combination -h)
  have hne2 : -s - 1 ≠ -1 := fun h => hs0 (by linear_combination -h)
  rw [integral_cpow (Or.inr ⟨hne1, h0⟩), integral_cpow (Or.inr ⟨hne2, h0⟩)]
  push_cast
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1C : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show ((n : ℝ) + 1) ≠ 0 by positivity)
  have e1 : ((n : ℂ) + 1) ^ (-s + 1) = ((n : ℂ) + 1) * ((n : ℂ) + 1) ^ (-s) := by
    rw [cpow_add _ _ hn1C, cpow_one]
    ring
  have e2 : (n : ℂ) ^ (-s + 1) = (n : ℂ) * (n : ℂ) ^ (-s) := by
    rw [cpow_add _ _ hnC, cpow_one]
    ring
  have e3 : ((n : ℂ) + 1) ^ (1 - s) = ((n : ℂ) + 1) * ((n : ℂ) + 1) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, e1]
  have e4 : (n : ℂ) ^ (1 - s) = (n : ℂ) * (n : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, e2]
  rw [show -s - 1 + 1 = -s by ring, e1, e2, e3, e4]
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : -s + 1 ≠ 0 := by rw [show -s + 1 = 1 - s by ring]; exact hs1'
  have hs0' : -s ≠ 0 := neg_ne_zero.mpr hs0
  generalize ((n : ℂ) + 1) ^ (-s) = A
  generalize (n : ℂ) ^ (-s) = B
  field_simp
  ring_nf

/-- En `(k+1, k+2)` la parte fraccionaria es `x − (k+1)`. -/
theorem block_fract (s : ℂ) (k : ℕ) :
    ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 1 + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 1 + 1), ((x : ℂ) - ((k : ℕ) + 1 : ℕ)) * (x : ℂ) ^ (-s - 1) := by
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hfl : ⌊x⌋ = (k : ℤ) + 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  simp only
  rw [← Int.self_sub_floor, hfl]
  push_cast
  ring

/-- Integrabilidad de `{x} x^{−s−1}` en `(1, ∞)` para `Re s > 0`. -/
theorem integrableOn_fract_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hg.mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (Complex.measurable_ofReal.comp measurable_fract).mul
      (by measurability)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hf : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      exact (Int.fract_lt_one x).le
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc ‖((Int.fract x : ℝ) : ℂ)‖ * x ^ (-s.re - 1) ≤ 1 * x ^ (-s.re - 1) := by
          gcongr
      _ = x ^ (-s.re - 1) := one_mul _

/-- Sumas parciales: `s ∫_1^{N+1} {x} x^{−s−1} dx = ((N+1)^{1−s} − 1)/(1−s) − ∑_{k<N} (k+2)^{−s}`. -/
theorem partial_fract_integral {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    s * ∫ x in (1 : ℝ)..((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
        - ∑ k ∈ Finset.range N, ((k : ℂ) + 1 + 1) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hint : ∀ k < N, IntervalIntegrable
      (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) volume
      ((fun k : ℕ => (k : ℝ) + 1) k) ((fun k : ℕ => (k : ℝ) + 1) (k + 1)) := by
    intro k _
    simp only
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
    refine (integrableOn_fract_cpow hs).mono_set (fun x hx => ?_)
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hx ⊢
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hx.1]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
    (a := fun k : ℕ => (k : ℝ) + 1) hint
  simp only [Nat.cast_zero, zero_add] at hadj
  rw [← hadj, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range N,
      s * ∫ x in ((k : ℝ) + 1)..(((k + 1 : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        = ((((k : ℂ) + 1) + 1) ^ (1 - s) - ((k : ℂ) + 1) ^ (1 - s)) / (1 - s)
          - (((k : ℂ) + 1) + 1) ^ (-s) := by
    intro k _
    have hb := block_fract s k
    have hc := block_integral hs0 hs1 (n := k + 1) (by omega)
    push_cast at hb hc ⊢
    rw [hb]
    exact hc
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div]
  have htel := Finset.sum_range_sub (fun k : ℕ => ((k : ℂ) + 1) ^ (1 - s)) N
  push_cast at htel
  simp only [zero_add, one_cpow] at htel
  rw [htel]

/-- Representación integral de `ζ` para `Re s > 1`. -/
theorem zeta_eq_integral_fract_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = s / (s - 1) - s * ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hs0' : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun N : ℕ => s * ∫ x in (1 : ℝ)..((N : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_fract_cpow hs0') hN).const_mul s
  have hpow : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (-(s.re - 1)) := by
      intro N
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hc : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      congr 1
      simp
    simp_rw [hnorm]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp hN
  have hsm : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa using h
  have hhs := hsm.hasSum
  rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hhs
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ((k : ℂ) + 1 + 1) ^ (-s)) atTop
      (𝓝 (riemannZeta s - 1)) := by
    refine ((hhs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const 1).congr (fun N => ?_)
    simp only [Function.comp, Finset.sum_range_succ', Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      zero_add, one_cpow, div_one, add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k _
    rw [cpow_neg, one_div]
  have hR := ((hpow.sub_const 1).div_const (1 - s)).sub hsum
  have hL' := hL.congr (fun N => partial_fract_integral hs0' hs1 N)
  have hlim := tendsto_nhds_unique hL' hR
  rw [hlim]
  field_simp
  ring

/-! ### Prolongación a `Re s > 0` -/

/-- `∫_1^∞ {x} x^{−z−1} dx`. -/
noncomputable def fractIntegral (z : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1)

/-- La parte fraccionaria truncada a `(1, ∞)`. -/
noncomputable def fractTail (t : ℝ) : ℂ := Set.indicator (Ioi (1 : ℝ)) (fun t => ((Int.fract t : ℝ) : ℂ)) t

theorem fractIntegral_eq_mellin (z : ℂ) : fractIntegral z = mellin fractTail (-z) := by
  unfold fractIntegral mellin fractTail
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-z - 1) • Set.indicator (Ioi (1 : ℝ))
      (fun t => ((Int.fract t : ℝ) : ℂ)) t)
      = Set.indicator (Ioi (1 : ℝ)) (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [Set.indicator_of_mem ht, mul_comm]
    · simp [Set.indicator_of_notMem ht]
  rw [hfun, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_right zero_le_one]

theorem measurable_fractTail : Measurable fractTail :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

theorem norm_fractTail_le (t : ℝ) : ‖fractTail t‖ ≤ 1 := by
  unfold fractTail
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact zero_le_one

/-- La integral es holomorfa en `Re z > 0`. -/
theorem differentiableAt_fractIntegral {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ fractIntegral z := by
  have hm : DifferentiableAt ℂ (mellin fractTail) (-z) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -z.re - 1)
    · refine ((locallyIntegrable_const (1 : ℂ)).mono measurable_fractTail.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)).locallyIntegrableOn _
      simpa using norm_fractTail_le t
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simpa using norm_fractTail_le t
    · simp only [neg_re]
      linarith
    · have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
      refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [hlt] with t ht
      have : t ∉ Ioi (1 : ℝ) := fun h => lt_asymm ht h
      simp [fractTail, Set.indicator_of_notMem this]
    · simp only [neg_re]
      linarith
  have hfun : fractIntegral = fun w => mellin fractTail (-w) := funext fractIntegral_eq_mellin
  rw [hfun]
  exact hm.comp z differentiableAt_id.neg

/-- Representación integral de `ζ` en `Re s > 0`, `s ≠ 1`. -/
theorem zeta_eq_integral_fract {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractIntegral s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ (fun z => z - z * (z - 1) * fractIntegral z) U := by
    intro z hz
    exact (differentiableAt_id.sub ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (differentiableAt_fractIntegral hz))).differentiableWithinAt
  have hEq : EqOn riemannZeta₁ (fun z => z - z * (z - 1) * fractIntegral z) U := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU) (hG.analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U])
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp at hz
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have h3 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hz1', one_mul]
    rw [h3, zeta_eq_integral_fract_of_one_lt hz]
    unfold fractIntegral
    field_simp
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [riemannZeta_eq_inv_sub_mul hs1, hEq hs]
  field_simp

/-! ### Primera cota de crecimiento -/

theorem norm_fractIntegral_le {s : ℂ} (hs : 0 < s.re) : ‖fractIntegral s‖ ≤ 1 / s.re := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hval : ∫ x in Ioi (1 : ℝ), x ^ (-s.re - 1) = 1 / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]
  unfold fractIntegral
  rw [← hval]
  refine norm_integral_le_of_norm_le hg ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hf : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  have hre : (-s - 1).re = -s.re - 1 := by simp
  rw [hre]
  calc ‖((Int.fract x : ℝ) : ℂ)‖ * x ^ (-s.re - 1) ≤ 1 * x ^ (-s.re - 1) := by gcongr
    _ = x ^ (-s.re - 1) := one_mul _

/-- Cota polinomial de `ζ` en `Re s > 0`: `‖ζ(s)‖ ≤ ‖s/(s−1)‖ + ‖s‖/Re s`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s / (s - 1)‖ + ‖s‖ / s.re := by
  rw [zeta_eq_integral_fract hs hs1]
  calc ‖s / (s - 1) - s * fractIntegral s‖ ≤ ‖s / (s - 1)‖ + ‖s * fractIntegral s‖ :=
        norm_sub_le _ _
    _ = ‖s / (s - 1)‖ + ‖s‖ * ‖fractIntegral s‖ := by rw [norm_mul]
    _ ≤ ‖s / (s - 1)‖ + ‖s‖ * (1 / s.re) := by
        gcongr
        exact norm_fractIntegral_le hs
    _ = ‖s / (s - 1)‖ + ‖s‖ / s.re := by ring

end AMate
