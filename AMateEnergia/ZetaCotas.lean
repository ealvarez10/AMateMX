import AMateEnergia.ZetaIntegral

/-!
# Cotas de `ζ` hacia la recta crítica

* `zeta_eq_trunc`: para `Re s > 0`, `s ≠ 1`,
  `ζ(s) = ∑_{k ≤ N} k^{−s} + (N+1)^{1−s}/(s − 1) − s ∫_{N+1}^∞ {x} x^{−s−1} dx`.
* `norm_riemannZeta₁_one_add_le`: en la recta `Re s = 1`,
  `‖(s − 1) ζ(s)‖ ≤ (1 + |t|)(2 + log(2 + |t|))`.

Son las dos primeras piezas de la cota de `ζ` en la recta crítica por las tres rectas de
Hadamard aplicadas a `(s − 1) ζ(s) e^{(s − s₀)²}` en `0 ≤ Re s ≤ 1`. Faltan la cota en
`Re s = 0` (ecuación funcional y `|Γ(1 + it)|` exacto), la acotación en la banda y la
aplicación de las tres rectas.
-/

open MeasureTheory Set Filter Topology Complex

namespace AMate

/-- Cota de la cola `∫_c^∞ {x} x^{−s−1} dx` para `c ≥ 1`. -/
theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 1 ≤ c) :
    ‖∫ x in Ioi c, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ c ^ (-s.re) / s.re := by
  have hc0 : 0 < c := by linarith
  have hg : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc0
  have hval : ∫ x in Ioi c, x ^ (-s.re - 1) = c ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hc0, show -s.re - 1 + 1 = -s.re by ring,
      neg_div_neg_eq]
  rw [← hval]
  refine norm_integral_le_of_norm_le hg ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := lt_trans hc0 hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hf : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  have hre : (-s - 1).re = -s.re - 1 := by simp
  rw [hre]
  calc ‖((Int.fract x : ℝ) : ℂ)‖ * x ^ (-s.re - 1) ≤ 1 * x ^ (-s.re - 1) := by gcongr
    _ = x ^ (-s.re - 1) := one_mul _

/-- Fórmula truncada en `N`, para `Re s > 0`, `s ≠ 1`. -/
theorem zeta_eq_trunc {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    riemannZeta s = ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s)
      + ((N : ℂ) + 1) ^ (1 - s) / (s - 1)
      - s * ∫ x in Ioi ((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hint := integrableOn_fract_cpow hs
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hsplit : fractIntegral s
      = (∫ x in (1 : ℝ)..((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + ∫ x in Ioi ((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    unfold fractIntegral
    rw [← Set.Ioc_union_Ioi_eq_Ioi hN,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN)),
      intervalIntegral.integral_of_le hN]
  have hpart := partial_fract_integral hs hs1 N
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [zeta_eq_integral_fract hs hs1, hsplit, mul_add, hpart, Finset.sum_range_succ']
  push_cast
  simp only [zero_add, one_cpow]
  field_simp
  ring

/-- Cota en la recta `Re s = 1`: `‖(s − 1) ζ(s)‖ ≤ (1 + |t|)(2 + log(2 + |t|))`. -/
theorem norm_riemannZeta₁_one_add_le (t : ℝ) :
    ‖riemannZeta₁ (1 + t * I)‖ ≤ (1 + |t|) * (2 + Real.log (2 + |t|)) := by
  have hlog2 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases ht : t = 0
  · subst ht
    simp only [ofReal_zero, zero_mul, add_zero, riemannZeta₁_one, norm_one, abs_zero]
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  set s : ℂ := 1 + t * I with hsdef
  have hsre : s.re = 1 := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    apply ht
    have := congrArg Complex.im h
    simpa [hsdef] using this
  have hs0 : 0 < s.re := by rw [hsre]; exact one_pos
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  set N := ⌈|t|⌉₊ with hNdef
  have hN1 : |t| ≤ (N : ℝ) := Nat.le_ceil _
  have hN2 : (N : ℝ) < |t| + 1 := Nat.ceil_lt_add_one (abs_nonneg t)
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ hs1', one_mul]
  rw [h1, zeta_eq_trunc hs0 hs1 N]
  set S := ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s) with hS
  set A := ((N : ℂ) + 1) ^ (1 - s) with hA
  set T := ∫ x in Ioi ((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) with hT
  have hcancel : (s - 1) * (A / (s - 1)) = A := by field_simp
  have hexp : (s - 1) * (S + A / (s - 1) - s * T) = (s - 1) * S + A - (s - 1) * s * T := by
    linear_combination hcancel
  rw [hexp]
  have hns1 : ‖s - 1‖ = |t| := by simp [hsdef]
  have hns : ‖s‖ ≤ 1 + |t| := by
    calc ‖s‖ = ‖(1 : ℂ) + (t : ℂ) * I‖ := rfl
      _ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |t| := by simp
  have hnS : ‖S‖ ≤ 1 + Real.log (2 + |t|) := by
    calc ‖S‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖((k : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k _
          have hk : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hk, Complex.norm_natCast_cpow_of_pos (by omega)]
          simp [hsre, Real.rpow_neg_one]
      _ = (harmonic (N + 1) : ℝ) := by
          unfold harmonic
          push_cast
          rfl
      _ ≤ 1 + Real.log ((N + 1 : ℕ) : ℝ) := harmonic_le_one_add_log _
      _ ≤ 1 + Real.log (2 + |t|) := by
          gcongr
          push_cast
          linarith
  have hnA : ‖A‖ = 1 := by
    have hA' : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hA, hA', Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [hsre]
  have hnT : ‖T‖ ≤ ((N : ℝ) + 1)⁻¹ := by
    have h := norm_tail_le hs0 (c := (N : ℝ) + 1) (by linarith)
    rw [hsre] at h
    simpa [Real.rpow_neg_one] using h
  have hfrac : (1 + |t|) * ((N : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hNpos]
    linarith
  calc ‖(s - 1) * S + A - (s - 1) * s * T‖
      ≤ ‖(s - 1) * S + A‖ + ‖(s - 1) * s * T‖ := norm_sub_le _ _
    _ ≤ ‖(s - 1) * S‖ + ‖A‖ + ‖(s - 1) * s * T‖ := by gcongr; exact norm_add_le _ _
    _ = |t| * ‖S‖ + 1 + |t| * ‖s‖ * ‖T‖ := by rw [norm_mul, norm_mul, norm_mul, hns1, hnA]
    _ ≤ |t| * (1 + Real.log (2 + |t|)) + 1 + |t| * (1 + |t|) * ((N : ℝ) + 1)⁻¹ := by gcongr
    _ ≤ |t| * (1 + Real.log (2 + |t|)) + 1 + |t| := by
        have := mul_le_mul_of_nonneg_left hfrac (abs_nonneg t)
        nlinarith [abs_nonneg t]
    _ ≤ (1 + |t|) * (2 + Real.log (2 + |t|)) := by nlinarith [abs_nonneg t]

end AMate
