import AMateEnergia.ZetaBanda
import AMateDirichlet.Testigo

/-!
# Cota de `L(s,χ)` en la recta crítica

Para `χ ≠ 1` módulo `N`:

* `LFunction_trunc`: para `Re s > 0` y `X ≥ 1` entero,
  `L(s,χ) = ∑_{n ≤ X} χ(n) n^{−s} − S_χ(X) X^{−s} + s ∫_X^∞ S_χ(⌊x⌋) x^{−s−1} dx`.
* `norm_LFunction_one_add_le`: en `Re s = 1`, `‖L(1 + it, χ)‖ ≤ (1 + 3N)(2 + log(2 + |t|))`.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace AMate.Dirichlet

variable {N : ℕ} [NeZero N]

/-! ### Fórmula truncada -/

omit [NeZero N] in
/-- En un tramo `[k, k+1]`: `s ∫_k^{k+1} S_χ(⌊x⌋) x^{−s−1} dx = S_χ(k) (k^{−s} − (k+1)^{−s})`. -/
theorem integral_tramo (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    s * ∫ x in (k : ℝ)..((k : ℝ) + 1), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)
      = S χ k * ((k : ℂ) ^ (-s) - ((k : ℂ) + 1) ^ (-s)) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (k : ℝ) + 1 := by
    filter_upwards [(Set.countable_singleton ((k : ℝ) + 1)).ae_notMem volume] with x hx
    simpa using hx
  have hcongr : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (k : ℝ) ((k : ℝ) + 1) →
      S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) = S χ k * (x : ℂ) ^ (-s - 1) := by
    filter_upwards [hne] with x hx hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hfl : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff (by linarith [hmem.1])]
      exact ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩
    rw [hfl]
  have hr : -s - 1 ≠ -1 := by
    intro h
    apply hs
    linear_combination -h
  have h0 : (0 : ℝ) ∉ [[(k : ℝ), (k : ℝ) + 1]] := by
    rw [Set.uIcc_of_le (by linarith)]
    simp only [mem_Icc, not_and, not_le]
    intro h
    linarith
  rw [intervalIntegral.integral_congr_ae hcongr, intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨hr, h0⟩), show -s - 1 + 1 = -s by ring]
  push_cast
  field_simp
  ring

theorem intervalIntegrable_S_floor_cpow {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_S_floor_cpow hχ hs).mono_set fun x hx => lt_of_le_of_lt ha hx.1

/-- `s ∫_1^X S_χ(⌊x⌋) x^{−s−1} dx = ∑_{n ≤ X} χ(n) n^{−s} − S_χ(X) X^{−s}`. -/
theorem integral_uno_X {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (X : ℕ) (hX : 1 ≤ X) :
    s * ∫ x in (1 : ℝ)..(X : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)
      = (∑ n ∈ Finset.Icc 1 X, χ n * (n : ℂ) ^ (-s)) - S χ X * (X : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  induction X, hX using Nat.le_induction with
  | base => simp [S]
  | succ X hX ih =>
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_S_floor_cpow hχ hs le_rfl hX1)
      (intervalIntegrable_S_floor_cpow hχ hs hX1 (by linarith)), mul_add, ih,
      integral_tramo χ hs0 hX, Finset.sum_Icc_succ_top (by omega), S_succ]
    push_cast
    ring

/-- Cola: `‖∫_X^∞ S_χ(⌊x⌋) x^{−s−1} dx‖ ≤ N X^{−σ}/σ`. -/
theorem norm_cola_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) {X : ℝ}
    (hX : 1 ≤ X) :
    ‖∫ x in Ioi X, S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)‖ ≤ (N : ℝ) * X ^ (-s.re) / s.re := by
  have hX0 : 0 < X := by linarith
  have hb : IntegrableOn (fun x : ℝ => (N : ℝ) * x ^ (-s.re - 1)) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hX0).const_mul _
  have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi X)),
      ‖S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)‖ ≤ (N : ℝ) * x ^ (-s.re - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans hX0 hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (norm_S_le hχ _) (Real.rpow_nonneg hx0.le _)
  calc ‖∫ x in Ioi X, S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)‖
      ≤ ∫ x in Ioi X, (N : ℝ) * x ^ (-s.re - 1) := norm_integral_le_of_norm_le hb hae
    _ = (N : ℝ) * X ^ (-s.re) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hX0,
        show -s.re - 1 + 1 = -s.re by ring]
      field_simp

/-- **Fórmula truncada**: para `Re s > 0` y `X ≥ 1`,
`L(s,χ) = ∑_{n ≤ X} χ(n) n^{−s} − S_χ(X) X^{−s} + s ∫_X^∞ S_χ(⌊x⌋) x^{−s−1} dx`. -/
theorem LFunction_trunc {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    {X : ℕ} (hX : 1 ≤ X) :
    DirichletCharacter.LFunction χ s
      = (∑ n ∈ Finset.Icc 1 X, χ n * (n : ℂ) ^ (-s)) - S χ X * (X : ℂ) ^ (-s)
        + s * ∫ x in Ioi (X : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) := by
  have hint := integrableOn_S_floor_cpow hχ hs
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [LFunction_eq_integral hχ hs, ← intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hX1)), mul_add, integral_uno_X hχ hs X hX]

/-- `‖L(s,χ)‖ ≤ ∑_{n ≤ X} n^{−σ} + N X^{−σ} + ‖s‖ N X^{−σ}/σ` para `σ = Re s > 0`, `X ≥ 1`. -/
theorem norm_LFunction_le_trunc {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-s.re)) + N * (X : ℝ) ^ (-s.re)
        + ‖s‖ * (N * (X : ℝ) ^ (-s.re) / s.re) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  rw [LFunction_trunc hχ hs hX]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast this
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn0), neg_re]
    calc ‖χ n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _)
            (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-s.re) := one_mul _
  · rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hX0), neg_re]
    exact mul_le_mul_of_nonneg_right (norm_S_le hχ _) (Real.rpow_nonneg hX0.le _)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cola_le hχ hs (by exact_mod_cast hX)) (norm_nonneg _)

/-- **Cota en `Re s = 1`**: `‖L(1 + it, χ)‖ ≤ (1 + 3N)(2 + log(2 + |t|))`. -/
theorem norm_LFunction_one_add_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ (1 + (t : ℂ) * I)‖
      ≤ (1 + 3 * N) * (2 + Real.log (2 + |t|)) := by
  set X : ℕ := ⌊|t|⌋₊ + 1 with hXdef
  have hX : 1 ≤ X := by omega
  have hat := abs_nonneg t
  have hXr : (X : ℝ) = ⌊|t|⌋₊ + 1 := by rw [hXdef]; push_cast; ring
  have hXgt : |t| < X := by rw [hXr]; exact Nat.lt_floor_add_one _
  have hXle : (X : ℝ) ≤ |t| + 1 := by rw [hXr]; linarith [Nat.floor_le hat]
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hre : (1 + (t : ℂ) * I).re = 1 := by simp
  have h := norm_LFunction_le_trunc hχ (s := 1 + (t : ℂ) * I) (by rw [hre]; norm_num) hX
  rw [hre] at h
  have hsum : (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-(1 : ℝ))) ≤ 1 + Real.log (2 + |t|) := by
    have hh := harmonic_le_one_add_log X
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    have hlog : Real.log X ≤ Real.log (2 + |t|) := Real.log_le_log (by linarith) (by linarith)
    calc (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-(1 : ℝ)))
        = ∑ n ∈ Finset.Icc 1 X, ((n : ℝ))⁻¹ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Real.rpow_neg_one]
      _ ≤ 1 + Real.log X := hh
      _ ≤ 1 + Real.log (2 + |t|) := by linarith
  have hXinv : (X : ℝ) ^ (-(1 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ hX1
  have hsn : ‖1 + (t : ℂ) * I‖ ≤ 1 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hratio : ‖1 + (t : ℂ) * I‖ * (X : ℝ) ^ (-(1 : ℝ)) ≤ 2 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith)
  calc ‖DirichletCharacter.LFunction χ (1 + (t : ℂ) * I)‖
      ≤ (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-(1 : ℝ))) + N * (X : ℝ) ^ (-(1 : ℝ))
        + ‖1 + (t : ℂ) * I‖ * (N * (X : ℝ) ^ (-(1 : ℝ)) / 1) := h
    _ = (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-(1 : ℝ))) + N * (X : ℝ) ^ (-(1 : ℝ))
        + N * (‖1 + (t : ℂ) * I‖ * (X : ℝ) ^ (-(1 : ℝ))) := by ring
    _ ≤ (1 + Real.log (2 + |t|)) + N * 1 + N * 2 := by gcongr
    _ ≤ (1 + 3 * N) * (2 + Real.log (2 + |t|)) := by nlinarith

end AMate.Dirichlet
