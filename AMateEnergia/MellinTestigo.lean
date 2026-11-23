import AMateEnergia.Elementales
import AMateEnergia.ZetaIntegral

/-!
# Transformada de Mellin del testigo

* `sigma_floor_eq`: `σ_Q(⌊x⌋) = 1 + ∑ μ(d) {x/d} − Q m_Q {x/Q} − γ_Q (2 {x/2Q} − {x/Q})`, porque
  `P_Q(1) = 0` cancela los términos en `{x}`.
* `integral_fracPow`: `∫_1^∞ {x/a} x^{−s−1} dx = a^{−1}/(s − 1) − a^{−s} ζ(s)/s`.
* `integral_sigma_floor`: `∫_1^∞ σ_Q(⌊x⌋) x^{−s−1} dx = (1 − ζ(s) P_Q(s))/s` en `Re s > 0`,
  `s ≠ 1` (estado 45, (2.4)).

No hace falta prolongación analítica: `zeta_eq_integral_fract` ya vale en `Re s > 0`.
-/

open MeasureTheory Set Complex

namespace AMate

/-! ### El testigo en variable continua -/

theorem fract_eq_sub_floor {y : ℝ} (hy : 0 ≤ y) : Int.fract y = y - (⌊y⌋₊ : ℝ) := by
  unfold Int.fract
  rw [← Int.natCast_floor_eq_floor hy]
  push_cast
  ring

theorem fract_div_eq {x : ℝ} (hx : 0 ≤ x) {a : ℕ} (ha : 1 ≤ a) :
    Int.fract (x / a) = u a ⌊x⌋₊ + Int.fract x / a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [fract_eq_sub_floor (div_nonneg hx ha0.le), fract_eq_sub_floor hx, u_eq a _ ha,
    Nat.floor_div_natCast]
  ring

/-- `σ_Q(⌊x⌋) = 1 + ∑ μ(d) {x/d} − Q m_Q {x/Q} − γ_Q (2 {x/2Q} − {x/Q})`: como `P_Q(1) = 0`, los
términos en `{x}` se cancelan. -/
theorem sigma_floor_eq {Q : ℕ} (hQ : 1 ≤ Q) {x : ℝ} (hx : 0 ≤ x) :
    sigma Q ⌊x⌋₊ = 1 + ∑ d ∈ Finset.Icc 1 Q, mu d * Int.fract (x / d)
      - Q * m Q * Int.fract (x / Q)
      - gam Q * (2 * Int.fract (x / ((2 * Q : ℕ) : ℝ)) - Int.fract (x / Q)) := by
  have hsum : ∑ d ∈ Finset.Icc 1 Q, mu d * Int.fract (x / d)
      = ∑ d ∈ Finset.Icc 1 Q, mu d * u d ⌊x⌋₊ + Int.fract x * m Q := by
    rw [m, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [fract_div_eq hx (Finset.mem_Icc.mp hd).1]
    ring
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [hsum, fract_div_eq hx hQ, fract_div_eq hx (show 1 ≤ 2 * Q by omega)]
  simp only [sigma, phi, h]
  push_cast
  field_simp
  ring

/-! ### Transformadas de Mellin de `{x/a}` -/

/-- `{x/a} x^{−s−1}`. -/
noncomputable def fracPow (s : ℂ) (a : ℕ) (x : ℝ) : ℂ :=
  ((Int.fract (x / a) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

theorem mul_cpow_neg_sub_one {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) * (y : ℂ) ^ (-s - 1) = (y : ℂ) ^ (-s) := by
  have hne : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have h1 : (y : ℂ) ^ (-s) = (y : ℂ) ^ ((-s - 1) + 1) := by ring_nf
  rw [h1, cpow_add _ _ hne, cpow_one]
  ring

theorem integrableOn_bdd_cpow {s : ℂ} (hs : 0 < s.re) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) :
    IntegrableOn (fun x : ℝ => ((g x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hint.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      ((Complex.measurable_ofReal.comp hg).mul (by measurability))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc |g x| * x ^ (-s.re - 1) ≤ 1 * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hb x) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-s.re - 1) := one_mul _

theorem integrableOn_fracPow {s : ℂ} (hs : 0 < s.re) (a : ℕ) :
    IntegrableOn (fracPow s a) (Ioi 1) :=
  integrableOn_bdd_cpow hs (measurable_fract.comp (measurable_id.div_const _)) fun x => by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le

/-- `∫_1^∞ {x/a} x^{−s−1} dx = a^{−1}/(s − 1) − a^{−s} ζ(s)/s` para `Re s > 0`, `s ≠ 1`. -/
theorem integral_fracPow {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {a : ℕ} (ha : 1 ≤ a) :
    ∫ x in Ioi (1 : ℝ), fracPow s a x
      = (1 / (a : ℂ)) / (s - 1) - (a : ℂ) ^ (-s) * riemannZeta s / s := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hA1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hAne : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  -- cambio de variable `x = a y`
  have hsub := integral_comp_mul_left_Ioi (fracPow s a) (1 / (a : ℝ)) hA
  rw [show (a : ℝ) * (1 / a) = 1 by field_simp] at hsub
  have hcongr : ∫ y in Ioi (1 / (a : ℝ)), fracPow s a (a * y)
      = (a : ℂ) ^ (-s - 1) *
        ∫ y in Ioi (1 / (a : ℝ)), ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := lt_trans (by positivity) hy
    have hay : (a : ℝ) * y / a = y := by field_simp
    show ((Int.fract ((a : ℝ) * y / a) : ℝ) : ℂ) * (((a : ℝ) * y : ℝ) : ℂ) ^ (-s - 1)
      = (a : ℂ) ^ (-s - 1) * (((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
    rw [hay, ofReal_mul, mul_cpow_ofReal_nonneg hA.le hy0.le, ofReal_natCast]
    ring
  have hmul : (a : ℂ) * (a : ℂ) ^ (-s - 1) = (a : ℂ) ^ (-s) := by
    have := mul_cpow_neg_sub_one hA s
    rwa [ofReal_natCast] at this
  have hmain : ∫ x in Ioi (1 : ℝ), fracPow s a x = (a : ℂ) ^ (-s) *
      ∫ y in Ioi (1 / (a : ℝ)), ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) := by
    have h2 : ∫ x in Ioi (1 : ℝ), fracPow s a x
        = (a : ℂ) * ∫ y in Ioi (1 / (a : ℝ)), fracPow s a (a * y) := by
      rw [hsub, Complex.real_smul, ← mul_assoc, ofReal_inv, ofReal_natCast,
        mul_inv_cancel₀ hAne, one_mul]
    rw [h2, hcongr, ← mul_assoc, hmul]
  -- separar `(1/a, 1]` y `(1, ∞)`
  have h1a : 1 / (a : ℝ) ≤ 1 := by rw [div_le_one hA]; exact hA1
  have h0a : 0 < 1 / (a : ℝ) := by positivity
  have hIoo : ∀ y ∈ Ioo (1 / (a : ℝ)) 1,
      ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) = (y : ℂ) ^ (-s) := by
    intro y hy
    have hy0 : 0 < y := lt_trans h0a hy.1
    rw [Int.fract_eq_self.mpr ⟨hy0.le, hy.2⟩, mul_cpow_neg_sub_one hy0]
  have hcp : IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (-s)) volume (1 / (a : ℝ)) 1 :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr (Set.notMem_uIcc_of_lt h0a one_pos))
  have hIocInt : IntegrableOn (fun y : ℝ => ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
      (Ioc (1 / (a : ℝ)) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have := (hcp.1 : IntegrableOn _ (Ioc (1 / (a : ℝ)) 1)).mono_set Ioo_subset_Ioc_self
    exact this.congr_fun (fun y hy => (hIoo y hy).symm) measurableSet_Ioo
  have hval : ∫ y in Ioc (1 / (a : ℝ)) 1, ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (1 - ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hIoo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h1a,
      integral_cpow (Or.inr ⟨by intro h; apply hs1; linear_combination -h,
        Set.notMem_uIcc_of_lt h0a one_pos⟩),
      ofReal_one, one_cpow, show -s + 1 = 1 - s by ring]
  have hJ : ∫ y in Ioi (1 / (a : ℝ)), ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (1 - ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s) + fractIntegral s := by
    rw [← Ioc_union_Ioi_eq_Ioi h1a, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hIocInt (integrableOn_fract_cpow hs), hval, fractIntegral]
  -- álgebra final
  have hF : fractIntegral s = 1 / (s - 1) - riemannZeta s / s := by
    rw [zeta_eq_integral_fract hs hs1]
    field_simp
    ring
  have hw : ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s) = ((a : ℂ) * (a : ℂ) ^ (-s))⁻¹ := by
    have e1 : ((1 / (a : ℝ) : ℝ) : ℂ) = (a : ℂ)⁻¹ := by push_cast; ring
    rw [e1, inv_cpow _ _ (by rw [natCast_arg]; exact Real.pi_ne_zero.symm), sub_eq_add_neg,
      cpow_add _ _ hAne, cpow_one]
  have hz0 : (a : ℂ) ^ (-s) ≠ 0 := by
    rw [cpow_def_of_ne_zero hAne]
    exact Complex.exp_ne_zero _
  have hzw : (a : ℂ) ^ (-s) * ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s) = 1 / a := by
    rw [hw]
    field_simp
  rw [hmain, hJ, hF]
  calc (a : ℂ) ^ (-s) * ((1 - ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + (1 / (s - 1) - riemannZeta s / s))
      = ((a : ℂ) ^ (-s) - (a : ℂ) ^ (-s) * ((1 / (a : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + (a : ℂ) ^ (-s) / (s - 1) - (a : ℂ) ^ (-s) * riemannZeta s / s := by ring
    _ = ((a : ℂ) ^ (-s) - 1 / a) / (1 - s)
        + (a : ℂ) ^ (-s) / (s - 1) - (a : ℂ) ^ (-s) * riemannZeta s / s := by rw [hzw]
    _ = (1 / (a : ℂ)) / (s - 1) - (a : ℂ) ^ (-s) * riemannZeta s / s := by
        field_simp
        ring

/-! ### Transformada de Mellin del testigo -/

/-- Estado 45, (2.4): `∫_1^∞ σ_Q(⌊x⌋) x^{−s−1} dx = (1 − ζ(s) P_Q(s))/s` en `Re s > 0`, `s ≠ 1`. -/
theorem integral_sigma_floor {Q : ℕ} (hQ : 1 ≤ Q) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∫ x in Ioi (1 : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = (1 - riemannZeta s * P Q s) / s := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hcint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hpt : ∀ x ∈ Ioi (1 : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = (x : ℂ) ^ (-s - 1) + ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x
        - ((Q : ℂ) * ((m Q : ℝ) : ℂ)) * fracPow s Q x
        - ((gam Q : ℝ) : ℂ) * (2 * fracPow s (2 * Q) x - fracPow s Q x) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans one_pos hx)
    have hs' : ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x
        = (∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * ((Int.fract (x / d) : ℝ) : ℂ))
          * (x : ℂ) ^ (-s - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ => by unfold fracPow; ring
    rw [hs', sigma_floor_eq hQ hx0]
    unfold fracPow
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hsumint : IntegrableOn
      (fun x => ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x) (Ioi 1) :=
    integrable_finsetSum _ fun d _ => Integrable.const_mul (integrableOn_fracPow hs d) _
  have hCint : IntegrableOn (fun x => ((Q : ℂ) * ((m Q : ℝ) : ℂ)) * fracPow s Q x) (Ioi 1) :=
    Integrable.const_mul (integrableOn_fracPow hs Q) _
  have hDint : IntegrableOn
      (fun x => ((gam Q : ℝ) : ℂ) * (2 * fracPow s (2 * Q) x - fracPow s Q x)) (Ioi 1) :=
    Integrable.const_mul ((Integrable.const_mul (integrableOn_fracPow hs (2 * Q)) 2).sub
      (integrableOn_fracPow hs Q)) _
  have I1 : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) = 1 / s := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos, ofReal_one, one_cpow,
      show -s - 1 + 1 = -s by ring, neg_div_neg_eq]
  have I2 : ∫ x in Ioi (1 : ℝ), ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x
      = ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ)
          * ((1 / (d : ℂ)) / (s - 1) - (d : ℂ) ^ (-s) * riemannZeta s / s) := by
    rw [integral_finsetSum _ fun d _ => Integrable.const_mul (integrableOn_fracPow hs d) _]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [integral_const_mul, integral_fracPow hs hs1 (Finset.mem_Icc.mp hd).1]
  have I3 : ∫ x in Ioi (1 : ℝ), ((Q : ℂ) * ((m Q : ℝ) : ℂ)) * fracPow s Q x
      = ((Q : ℂ) * ((m Q : ℝ) : ℂ))
          * ((1 / (Q : ℂ)) / (s - 1) - (Q : ℂ) ^ (-s) * riemannZeta s / s) := by
    rw [integral_const_mul, integral_fracPow hs hs1 hQ]
  have I4 : ∫ x in Ioi (1 : ℝ), ((gam Q : ℝ) : ℂ) * (2 * fracPow s (2 * Q) x - fracPow s Q x)
      = ((gam Q : ℝ) : ℂ) * (2 * ((1 / ((2 * Q : ℕ) : ℂ)) / (s - 1)
          - ((2 * Q : ℕ) : ℂ) ^ (-s) * riemannZeta s / s)
          - ((1 / (Q : ℂ)) / (s - 1) - (Q : ℂ) ^ (-s) * riemannZeta s / s)) := by
    rw [integral_const_mul, integral_sub (Integrable.const_mul (integrableOn_fracPow hs (2 * Q)) 2)
      (integrableOn_fracPow hs Q), integral_const_mul,
      integral_fracPow hs hs1 (show 1 ≤ 2 * Q by omega), integral_fracPow hs hs1 hQ]
  have hB : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)
      + ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x) (Ioi 1) := hcint.add hsumint
  have hA : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)
      + ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * fracPow s d x
      - ((Q : ℂ) * ((m Q : ℝ) : ℂ)) * fracPow s Q x) (Ioi 1) := hB.sub hCint
  rw [integral_sub hA hDint, integral_sub hB hCint, integral_add hcint hsumint, I1, I2, I3, I4]
  have hm : ((m Q : ℝ) : ℂ) = ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * (1 / (d : ℂ)) := by
    unfold m
    push_cast
    exact Finset.sum_congr rfl fun d _ => by ring
  have hsplit : ∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ)
        * ((1 / (d : ℂ)) / (s - 1) - (d : ℂ) ^ (-s) * riemannZeta s / s)
      = ((m Q : ℝ) : ℂ) / (s - 1)
        - (∑ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)) * riemannZeta s / s := by
    rw [hm, Finset.sum_div, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit]
  unfold P
  push_cast
  field_simp
  ring

end AMate
