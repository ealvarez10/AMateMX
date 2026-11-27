import AMateEnergia.PolinomioCritica
import AMateDirichlet.InversaL

/-!
# Fórmula de Perron con `1/L(s,χ)` y cota de `P_{Q,χ}` en la recta crítica

Análogo para `χ ≠ 1` de `AMateEnergia.PerronZ`, `AMateEnergia.PerronContorno` y de la parte de
Balazard–Saias de `AMateEnergia.CalibracionTheta`. Como `L(s,χ)` es entera y `L(1,χ) ≠ 0`, el
papel de `Zinv` lo hace directamente `1/L(s,χ)`, sin correctores.

* `dirichlet_sideL`: en `Re w = 2`,
  `(1/2π) ∫ L(s+w,χ)^{−1} pesoMellin(w) dy = ∑_{d ≤ X+h} μ(d) χ(d) d^{−s} peso(d)`.
* `smoothing_errorL`: el peso cambia `P_{n,χ}(s)` en a lo sumo `n^{1/2 − Re s}`.
* `contornoKL`: `(L(s+w,χ)^{−1} − L(s,χ)^{−1}) pesoMellin(w)`, holomorfa en `w = 0` por `dslope`.
* `balazard_saias_L`: bajo `SinCerosDerechaL χ θ`, para `n ≥ 1` y `Re s ≥ θ + δ`,
  `‖P_{n,χ}(s) − 1/L(s,χ)‖ ≤ C n^{−δ/3} (1 + |Im s|)^η`.
* `P_recta_critica_L`: sumación de Abel desde `Re s = θ + δ`:
  `‖P_{Q,χ}(1/2 + ix)‖ ≤ C Q^{θ − 1/2 + δ} (1 + |x|)^η`.
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate.Dirichlet

variable {N : ℕ} [NeZero N]

local notation "Lχ" => DirichletCharacter.LFunction

/-! ### Serie de `1/L` y lado de Dirichlet -/

theorem Linv_eq_LSeries (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 < z.re) :
    (Lχ χ z)⁻¹
      = LSeries ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.moebius n : ℂ)) z := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact inv_eq_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hz)

omit [NeZero N] in
theorem term_chi_moebius_add (χ : DirichletCharacter ℂ N) {s w : ℂ} (d : ℕ) :
    LSeries.term ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.moebius n : ℂ)) (s + w) d
      = (if d = 0 then 0 else ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d / (d : ℂ) ^ s)
        * (d : ℂ) ^ (-w) := by
  rcases eq_or_ne d 0 with hd | hd
  · simp [hd]
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [LSeries.term_of_ne_zero hd, if_neg hd, cpow_add _ _ hd', cpow_neg, Pi.mul_apply]
  have h1 : (d : ℂ) ^ s ≠ 0 := by
    rw [cpow_def_of_ne_zero hd']
    exact Complex.exp_ne_zero _
  have h2 : (d : ℂ) ^ w ≠ 0 := by
    rw [cpow_def_of_ne_zero hd']
    exact Complex.exp_ne_zero _
  field_simp

/-- **Lado de Dirichlet**: en `Re w = 2`,
`(1/2π) ∫ L(s+w,χ)^{−1} pesoMellin(w) dy = ∑_{d ≤ X+h} μ(d) χ(d) d^{−s} φ(d)`. -/
theorem dirichlet_sideL (χ : DirichletCharacter ℂ N) {X h : ℝ} (hX : 0 < X) (hh : 0 < h)
    {s : ℂ} (hs : 0 < s.re) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ)
        * ∫ y : ℝ, (Lχ χ (s + (((2 : ℝ) : ℂ) + y * I)))⁻¹
            * pesoMellin X h (((2 : ℝ) : ℂ) + y * I)
      = ∑ d ∈ Finset.Icc 1 ⌊X + h⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
            * ((peso X h d : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun y => pesoMellin X h (((2 : ℝ) : ℂ) + y * I) with hFdef
  have hF : Integrable F := integrable_pesoMellin_line hX hh (by norm_num) (by norm_num)
  set c : ℕ → ℂ := fun d =>
    if d = 0 then 0 else ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d / (d : ℂ) ^ s with hc
  set f : ℕ → ℝ → ℂ := fun d y => c d * ((d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) with hf
  have hw0 : ∀ y : ℝ, -(((2 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y h0
    have := congrArg Complex.re h0
    simp at this
  have hc1 : ∀ d, ‖c d‖ ≤ 1 := by
    intro d
    rcases eq_or_ne d 0 with hd | hd
    · simp [hc, hd]
    simp only [hc, if_neg hd]
    rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hd),
      Complex.norm_intCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    rw [div_le_one (Real.rpow_pos_of_pos (by linarith) _)]
    have hμ1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ1 : ‖χ d‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have := mul_le_mul hμ1 hχ1 (norm_nonneg _) zero_le_one
    linarith [Real.one_le_rpow hd1 hs.le]
  have hpow : ∀ (d : ℕ) (y : ℝ),
      ‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ ≤ (d : ℝ) ^ (-(2 : ℝ)) := by
    intro d y
    rcases eq_or_ne d 0 with hd | hd
    · subst hd
      rw [Nat.cast_zero, zero_cpow (hw0 y), norm_zero, Nat.cast_zero,
        Real.zero_rpow (by norm_num)]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hd)]
    simp
  have hfint : ∀ d, Integrable (f d) := by
    intro d
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ => (d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) :=
      ((Continuous.const_cpow (by fun_prop) (Or.inr (hw0 ·))).aestronglyMeasurable).mul
        hF.aestronglyMeasurable
    have hint : Integrable (fun y : ℝ => (d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * F y) := by
      refine Integrable.mono' (hF.norm.const_mul ((d : ℝ) ^ (-(2 : ℝ)))) hmeas
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hpow d y) (norm_nonneg _)
    exact hint.const_mul (c d)
  have hsum : Summable (fun d => ∫ y, ‖f d y‖) := by
    have hg : Summable (fun d : ℕ => (d : ℝ) ^ (-(2 : ℝ)) * ∫ y, ‖F y‖) :=
      (Real.summable_nat_rpow.mpr (by norm_num)).mul_right _
    refine Summable.of_nonneg_of_le (fun d => integral_nonneg fun y => norm_nonneg _)
      (fun d => ?_) hg
    rw [← integral_const_mul]
    refine integral_mono (hfint d).norm (hF.norm.const_mul _) (fun y => ?_)
    simp only [hf, norm_mul]
    have h1 := hc1 d
    have h2 := hpow d y
    have h3 := norm_nonneg (F y)
    have h4 : 0 ≤ ‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ := norm_nonneg _
    calc ‖c d‖ * (‖(d : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I))‖ * ‖F y‖)
        ≤ 1 * ((d : ℝ) ^ (-(2 : ℝ)) * ‖F y‖) := by gcongr
      _ = (d : ℝ) ^ (-(2 : ℝ)) * ‖F y‖ := one_mul _
  have hpt : ∀ y : ℝ, (Lχ χ (s + (((2 : ℝ) : ℂ) + y * I)))⁻¹ * F y = ∑' d, f d y := by
    intro y
    have hre : 1 < (s + (((2 : ℝ) : ℂ) + y * I)).re := by simp; linarith
    rw [Linv_eq_LSeries χ hre, LSeries, ← tsum_mul_right]
    refine tsum_congr fun d => ?_
    rw [term_chi_moebius_add]
    simp only [hf, hc]
    ring
  have hval : ∀ d, ∫ y, f d y = c d * (2 * Real.pi * ((peso X h d : ℝ) : ℂ)) := by
    intro d
    rcases eq_or_ne d 0 with hd | hd
    · simp [hf, hc, hd]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hmi := mellinInv_pesoMellin hX hh (σ := 2) two_pos hd0
    unfold mellinInv at hmi
    simp only [hf, integral_const_mul]
    congr 1
    have e : (2 * (Real.pi : ℂ)) * (((1 / (2 * Real.pi)) : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    rw [← hmi, Complex.real_smul, ← mul_assoc, e, one_mul]
    simp only [ofReal_natCast, smul_eq_mul, hFdef]
  have hI : ∫ y : ℝ, (Lχ χ (s + (((2 : ℝ) : ℂ) + y * I)))⁻¹ * F y = ∑' d, ∫ y, f d y := by
    rw [integral_tsum_of_summable_integral_norm hfint hsum]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hI, tsum_congr hval, tsum_eq_sum (s := Finset.Icc 1 ⌊X + h⌋₊)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    simp only [hc, if_neg hd1]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    rw [cpow_neg]
    push_cast
    field_simp
  · intro d hd
    rcases eq_or_ne d 0 with hd0 | hd0
    · simp [hc, hd0]
    have hgt : X + h < d := by
      have : ¬ (d ≤ ⌊X + h⌋₊) :=
        fun h' => hd (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, h'⟩)
      have h2 : ⌊X + h⌋₊ < d := not_le.mp this
      exact (Nat.floor_lt (by linarith)).mp h2
    simp [peso_of_ge hh hgt.le]

/-! ### Error del suavizado -/

omit [NeZero N] in
theorem smoothing_errorL (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (hs : 0 < s.re) :
    ‖∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      - P χ n s‖ ≤ (n : ℝ) ^ (1 / 2 - s.re) := by
  set M := ⌊(n : ℝ) + Real.sqrt n⌋₊ with hM
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hnM : n ≤ M := Nat.le_floor (by linarith)
  have hMle : (M : ℝ) ≤ n + Real.sqrt n := Nat.floor_le (by positivity)
  have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := Finset.Icc_add_one_left_eq_Ioc 0 M
  have e2 : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
  rw [e1, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hnM, ← e2]
  have hfirst : ∑ d ∈ Finset.Icc 1 n,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ) = P χ n s := by
    unfold P
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn : (d : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    rw [peso_of_le hsqpos hdn, ofReal_one, mul_one]
  rw [hfirst, add_sub_cancel_left]
  calc ‖∑ d ∈ Finset.Ioc n M, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)‖
      ≤ ∑ d ∈ Finset.Ioc n M, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc n M, (n : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdn : n < d := (Finset.mem_Ioc.mp hd).1
        have hd0 : 0 < d := by omega
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hd0,
          Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (peso_nonneg _)]
        have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hχ1 : ‖χ d‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h2 : (d : ℝ) ^ (-s).re ≤ (n : ℝ) ^ (-s.re) := by
          rw [neg_re]
          exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hdn.le) (by linarith)
        have h3 := peso_le_one (N := (n : ℝ)) (h := Real.sqrt n) (d : ℝ)
        have h4 : 0 ≤ (d : ℝ) ^ (-s).re := by positivity
        calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * ‖χ d‖ * (d : ℝ) ^ (-s).re
              * peso (n : ℝ) (Real.sqrt n) d
            ≤ 1 * 1 * (n : ℝ) ^ (-s.re) * 1 :=
              mul_le_mul (mul_le_mul (mul_le_mul h1 hχ1 (norm_nonneg _) zero_le_one) h2 h4
                (by norm_num)) h3 (peso_nonneg _) (by positivity)
          _ = (n : ℝ) ^ (-s.re) := by ring
    _ = ((M - n : ℕ) : ℝ) * (n : ℝ) ^ (-s.re) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ Real.sqrt n * (n : ℝ) ^ (-s.re) := by
        gcongr
        rw [Nat.cast_sub hnM]
        linarith
    _ = (n : ℝ) ^ (1 / 2 - s.re) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        ring_nf

/-! ### El integrando del contorno -/

/-- `(L(s+w,χ)^{−1} − L(s,χ)^{−1}) pesoMellin(w)`, escrito con `dslope` para que sea holomorfo en
`w = 0`. -/
noncomputable def contornoKL (χ : DirichletCharacter ℂ N) (X h : ℝ) (s : ℂ) (w : ℂ) : ℂ :=
  dslope (fun w => (Lχ χ (s + w))⁻¹) 0 w * pesoG X h w

theorem contornoKL_eq (χ : DirichletCharacter ℂ N) {X h : ℝ} {s w : ℂ} (hw : w ≠ 0) :
    contornoKL χ X h s w
      = (Lχ χ (s + w))⁻¹ * pesoMellin X h w - (Lχ χ s)⁻¹ * pesoMellin X h w := by
  unfold contornoKL
  rw [dslope_of_ne _ hw, slope_def_field, pesoMellin_eq_div, add_zero, sub_zero]
  field_simp

theorem differentiableOn_contornoKL_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hZ : SinCerosDerechaL χ θ) {X h : ℝ} (hX : 0 < X) (hh : 0 < h) {s : ℂ} (hs : θ < s.re) :
    DifferentiableOn ℂ (contornoKL χ X h s) {w | θ < (s + w).re ∧ -1 < w.re} := by
  set U : Set ℂ := {w | θ < (s + w).re ∧ -1 < w.re}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_re.comp (continuous_const.add continuous_id))).inter
      (isOpen_lt continuous_const continuous_re)
  have h0 : (0 : ℂ) ∈ U := ⟨by simpa using hs, by simp⟩
  have hZd : DifferentiableOn ℂ (fun w => (Lχ χ (s + w))⁻¹) U := by
    intro w hw
    have hd := (differentiableOn_Linv_theta hχ hZ).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show θ < (s + w).re from hw.1))
    exact (hd.comp w ((differentiableAt_const s).add differentiableAt_id)).differentiableWithinAt
  have hdsl : DifferentiableOn ℂ (dslope (fun w => (Lχ χ (s + w))⁻¹) 0) U :=
    (differentiableOn_dslope (hUo.mem_nhds h0)).mpr hZd
  have hG : DifferentiableOn ℂ (pesoG X h) U := by
    intro w hw
    have hw1 : (h : ℂ) * (w + 1) ≠ 0 := by
      refine mul_ne_zero (ofReal_ne_zero.mpr hh.ne') ?_
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [hw.2]
    unfold pesoG
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.div ?_ ?_ hw1)
    · exact (DifferentiableAt.const_cpow (by fun_prop)
          (Or.inl (ofReal_ne_zero.mpr (by linarith)))).sub
        (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hX.ne')))
    · fun_prop
  exact hdsl.mul hG

theorem integrable_Linv_mul_line_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ η : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1) (hη : 0 < η) (hη1 : η < 1)
    (hZ : SinCerosDerechaL χ θ) {X h : ℝ} (hX : 0 < X) (hh : 0 < h)
    {s : ℂ} {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ -1) (hsσ : θ + δ ≤ s.re + σ) :
    Integrable (fun y : ℝ =>
      (Lχ χ (s + ((σ : ℂ) + y * I)))⁻¹ * pesoMellin X h ((σ : ℂ) + y * I)) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Linv_bound_theta hχ hθ hδ hθδ hη hZ
  obtain ⟨K, hK0, hK⟩ := norm_pesoMellin_line_le hX hh hσ0 hσ1
  have hcont : Continuous (fun y : ℝ => (Lχ χ (s + ((σ : ℂ) + y * I)))⁻¹) := by
    refine (continuousOn_Linv_theta hχ hZ).comp_continuous (by fun_prop) fun y => ?_
    show θ < (s + ((σ : ℂ) + y * I)).re; simp; linarith
  have hF := integrable_pesoMellin_line hX hh hσ0 hσ1
  refine Integrable.mono'
    ((integrable_one_add_norm (r := 2 - η) (by norm_num; linarith)).const_mul
      (CZ * (1 + |s.im|) ^ η * K)) (hcont.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have him : (s + ((σ : ℂ) + y * I)).im = s.im + y := by simp
  have hre : θ + δ ≤ (s + ((σ : ℂ) + y * I)).re := by simp; linarith
  have hy : 0 < 1 + |y| := by positivity
  rw [norm_mul, Real.norm_eq_abs y]
  calc ‖(Lχ χ (s + ((σ : ℂ) + y * I)))⁻¹‖ * ‖pesoMellin X h ((σ : ℂ) + y * I)‖
      ≤ (CZ * (1 + |s.im + y|) ^ η) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        rw [← him]; exact mul_le_mul (hCZ _ hre) (hK y) (norm_nonneg _) (by positivity)
    _ ≤ (CZ * ((1 + |s.im|) ^ η * (1 + |y|) ^ η)) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        gcongr; exact one_add_abs_add_rpow_le _ _ hη.le
    _ = CZ * (1 + |s.im|) ^ η * K * ((1 + |y|) ^ η * (1 + |y|) ^ (-(2 : ℝ))) := by ring
    _ = CZ * (1 + |s.im|) ^ η * K * (1 + |y|) ^ (-(2 - η)) := by
        rw [← Real.rpow_add hy]; congr 2; ring

theorem horizontal_KL_theta {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ₂ η' : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ₂ : 0 < δ₂) (hθδ₂ : θ + δ₂ < 1) (hη' : 0 < η') (hη'1 : η' ≤ 1)
    (hZ : SinCerosDerechaL χ θ) {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    {s : ℂ} {α β : ℝ} (hβ : β ≤ 2) (hreg : θ + δ₂ ≤ s.re + α) :
    ∃ D : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, α ≤ x → x ≤ β →
      ‖contornoKL χ X h s (x + T * I)‖ ≤ D / T ∧
        ‖contornoKL χ X h s (x + ((-T : ℝ) : ℂ) * I)‖ ≤ D / T := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Linv_bound_theta hχ hθ hδ₂ hθδ₂ hη' hZ
  set CZ' : ℝ := CZ * (1 + |s.im|) ^ η'
  have hCZ'0 : 0 ≤ CZ' := by positivity
  set E_c : ℝ := 2 * (X + h) ^ (3 : ℝ) / h
  refine ⟨(2 * CZ' + ‖(Lχ χ s)⁻¹‖) * E_c, fun T hT x hx1 hx2 => ?_⟩
  have hT0 : 0 < T := by linarith
  have main : ∀ w : ℂ, w.re = x → |w.im| = T →
      ‖contornoKL χ X h s w‖ ≤ (2 * CZ' + ‖(Lχ χ s)⁻¹‖) * E_c / T := by
    intro w hwre hwim
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwim; simp at hwim; linarith
    rw [contornoKL_eq χ hw0]
    have hnw : T ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
    have hnw1 : T ≤ ‖w + 1‖ := by
      have := Complex.abs_im_le_norm (w + 1)
      rwa [add_im, one_im, add_zero, hwim] at this
    have hZw : ‖(Lχ χ (s + w))⁻¹‖ ≤ 2 * CZ' * T := by
      have hre : θ + δ₂ ≤ (s + w).re := by rw [add_re, hwre]; linarith
      have h1 := hCZ (s + w) hre
      rw [add_im] at h1
      have h2 := one_add_abs_add_rpow_le s.im w.im hη'.le
      have h3 : (1 + |w.im|) ^ η' ≤ 1 + |w.im| := by
        calc (1 + |w.im|) ^ η' ≤ (1 + |w.im|) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) hη'1
          _ = 1 + |w.im| := Real.rpow_one _
      calc ‖(Lχ χ (s + w))⁻¹‖ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |w.im|) ^ η') :=
            le_trans h1 (mul_le_mul_of_nonneg_left h2 hCZ0)
        _ = CZ' * (1 + |w.im|) ^ η' := by simp only [CZ']; ring
        _ ≤ CZ' * (1 + T) := by rw [← hwim]; exact mul_le_mul_of_nonneg_left h3 hCZ'0
        _ ≤ 2 * CZ' * T := by nlinarith
    have hF : ‖pesoMellin X h w‖ * T ^ 2 ≤ E_c := by
      have h1 := norm_pesoMellin_le (N := X) (by linarith) hh w
      rw [hwre] at h1
      have hXh1 : 1 ≤ X + h := by linarith
      have hnum : (X + h) ^ (x + 1) + X ^ (x + 1) ≤ 2 * (X + h) ^ (3 : ℝ) := by
        have e1 : (X + h) ^ (x + 1) ≤ (X + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hXh1 (by linarith)
        have e2 : X ^ (x + 1) ≤ X ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
        have e3 : X ^ (3 : ℝ) ≤ (X + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        linarith
      have hden : h * T * T ≤ h * ‖w‖ * ‖w + 1‖ := by gcongr
      have h2 : ‖pesoMellin X h w‖ ≤ 2 * (X + h) ^ (3 : ℝ) / (h * T * T) :=
        h1.trans (by gcongr)
      have hpos : 0 < h * T * T := by positivity
      rw [le_div_iff₀ hpos] at h2
      simp only [E_c]
      rw [le_div_iff₀ hh]
      nlinarith [norm_nonneg (pesoMellin X h w)]
    rw [le_div_iff₀ hT0]
    have hsplit : ‖(Lχ χ (s + w))⁻¹ * pesoMellin X h w - (Lχ χ s)⁻¹ * pesoMellin X h w‖
        ≤ (‖(Lχ χ (s + w))⁻¹‖ + ‖(Lχ χ s)⁻¹‖) * ‖pesoMellin X h w‖ := by
      rw [← sub_mul, norm_mul]; gcongr; exact norm_sub_le _ _
    have hZs : ‖(Lχ χ (s + w))⁻¹‖ + ‖(Lχ χ s)⁻¹‖ ≤ (2 * CZ' + ‖(Lχ χ s)⁻¹‖) * T := by
      nlinarith [norm_nonneg (Lχ χ s)⁻¹]
    calc ‖(Lχ χ (s + w))⁻¹ * pesoMellin X h w - (Lχ χ s)⁻¹ * pesoMellin X h w‖ * T
        ≤ (‖(Lχ χ (s + w))⁻¹‖ + ‖(Lχ χ s)⁻¹‖) * ‖pesoMellin X h w‖ * T := by gcongr
      _ ≤ (2 * CZ' + ‖(Lχ χ s)⁻¹‖) * T * ‖pesoMellin X h w‖ * T := by gcongr
      _ = (2 * CZ' + ‖(Lχ χ s)⁻¹‖) * (‖pesoMellin X h w‖ * T ^ 2) := by ring
      _ ≤ (2 * CZ' + ‖(Lχ χ s)⁻¹‖) * E_c := by gcongr
  exact ⟨main _ (by simp) (by simp [abs_of_pos hT0]),
    main _ (by simp) (by simp [abs_of_pos hT0])⟩

/-! ### Lema de Balazard–Saias para `χ` -/

set_option maxHeartbeats 4000000 in
/-- **Balazard–Saias para `χ`**: bajo `SinCerosDerechaL χ θ` (`1/2 ≤ θ < 1`), para `n ≥ 1` y
`Re s ≥ θ + δ`, `‖P_{n,χ}(s) − 1/L(s,χ)‖ ≤ C n^{−δ/3} (1 + |Im s|)^η`. -/
theorem balazard_saias_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ η : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1) (hη : 0 < η) (hZ : SinCerosDerechaL χ θ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s : ℂ, θ + δ ≤ s.re →
      ‖P χ n s - (Lχ χ s)⁻¹‖ ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  set η' : ℝ := min η (δ / 6)
  have hη'0 : 0 < η' := lt_min hη (by positivity)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'δ : η' ≤ δ / 6 := min_le_right _ _
  have hη'1 : η' < 1 := by linarith
  have hδ2 : 0 < δ / 2 := by positivity
  have hθδ2 : θ + δ / 2 < 1 := by linarith
  obtain ⟨CZ, hCZ0, hCZ⟩ := Linv_bound_theta hχ hθ hδ2 hθδ2 hη'0 hZ
  have hJint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(1 + η'))) :=
    integrable_one_add_norm (by norm_num; linarith)
  set J : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(1 + η'))
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  set Cm : ℝ := CZ * (3 * (4 / δ) ^ (1 + 2 * η')) * J / (2 * Real.pi)
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨1 + Cm, fun n hn s hsre => ?_⟩
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hh0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN0
  set a : ℝ := min (s.re - θ - δ / 2) (1 / 2)
  have ha1 : δ / 2 ≤ a := le_min (by linarith) (by linarith)
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  have ha3 : a ≤ s.re - θ - δ / 2 := min_le_left _ _
  have ha0 : 0 < a := by linarith
  have hsθ : θ < s.re := by linarith
  have hD := dirichlet_sideL χ hN0 hh0 (s := s) (by linarith)
  have hU : {w : ℂ | -a ≤ w.re ∧ w.re ≤ 2} ⊆ {w | θ < (s + w).re ∧ -1 < w.re} :=
    fun w hw => ⟨by simp; linarith [hw.1], by linarith [hw.1]⟩
  have hdiff := (differentiableOn_contornoKL_theta hχ hZ hN0 hh0 hsθ).mono hU
  have hlineK : ∀ σ : ℝ, σ ≠ 0 → σ ≠ -1 → θ + δ / 2 ≤ s.re + σ →
      Integrable (fun y : ℝ => contornoKL χ (n : ℝ) (Real.sqrt n) s (σ + y * I)) ∧
      ∫ y : ℝ, contornoKL χ (n : ℝ) (Real.sqrt n) s (σ + y * I)
        = (∫ y : ℝ, (Lχ χ (s + (σ + y * I)))⁻¹ * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I))
          - (Lχ χ s)⁻¹ * ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
    intro σ hσ0 hσ1 hσs
    have hZF := integrable_Linv_mul_line_theta hχ hθ hδ2 hθδ2 hη'0 hη'1 hZ hN0 hh0 hσ0 hσ1 hσs
    have hF := integrable_pesoMellin_line hN0 hh0 hσ0 hσ1
    have hfun : (fun y : ℝ => contornoKL χ (n : ℝ) (Real.sqrt n) s (σ + y * I))
        = fun y : ℝ => (Lχ χ (s + (σ + y * I)))⁻¹ * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I)
          - (Lχ χ s)⁻¹ * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
      funext y
      apply contornoKL_eq
      intro h0; have := congrArg Complex.re h0; simp at this; exact hσ0 this
    rw [hfun]
    exact ⟨hZF.sub (hF.const_mul _),
      by rw [integral_sub hZF (hF.const_mul _), integral_const_mul]⟩
  obtain ⟨hKa, hIa⟩ := hlineK (-a) (by linarith) (by linarith) (by linarith)
  obtain ⟨hK2, hI2⟩ := hlineK 2 (by norm_num) (by norm_num) (by linarith)
  obtain ⟨Dh, hDh⟩ := horizontal_KL_theta hχ hθ hδ2 hθδ2 hη'0 hη'1.le hZ hN1 hh0
    (s := s) (α := -a) (β := 2) le_rfl (by linarith)
  have hshift := integral_vertical_eq (by linarith) hdiff hKa hK2 hDh
  have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have hint2 : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I)
      = 2 * Real.pi := by
    have h1 := mellinInv_pesoMellin hN0 hh0 (σ := 2) two_pos one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1] at h1
    simp only [ofReal_one, one_cpow, one_smul] at h1
    rw [Complex.real_smul] at h1
    have e : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by push_cast; field_simp
    exact mul_left_cancel₀ hc (h1.trans e.symm)
  have hinta : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) = 0 := by
    have h1 := mellinInv_pesoMellin_neg hN0 hh0 (σ := -a) (by linarith) (by linarith) one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1, sub_self] at h1
    simp only [ofReal_one, one_cpow, one_smul, ofReal_zero] at h1
    rw [Complex.real_smul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  have hrel : (∫ y : ℝ, (Lχ χ (s + (((2 : ℝ) : ℂ) + y * I)))⁻¹
        * pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I))
      = 2 * Real.pi * (Lχ χ s)⁻¹ + ∫ y : ℝ, (Lχ χ (s + (((-a : ℝ) : ℂ) + y * I)))⁻¹
        * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) := by
    rw [hIa, hI2, hinta, hint2] at hshift
    linear_combination -hshift
  set A_int : ℂ := ∫ y : ℝ, (Lχ χ (s + (((-a : ℝ) : ℂ) + y * I)))⁻¹
    * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I)
  set Q_c : ℝ := CZ * (1 + |s.im|) ^ η'
    * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η'))
  have hAbound : ‖A_int‖ ≤ Q_c * J := by
    rw [show J = ∫ y : ℝ, (1 + ‖y‖) ^ (-(1 + η')) from rfl, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hJint.const_mul Q_c) (Eventually.of_forall fun y => ?_)
    have hre : θ + δ / 2 ≤ (s + (((-a : ℝ) : ℂ) + y * I)).re := by simp; linarith
    have him : (s + (((-a : ℝ) : ℂ) + y * I)).im = s.im + y := by simp
    have hZ1 := hCZ _ hre
    rw [him] at hZ1
    have hZ2 : ‖(Lχ χ (s + (((-a : ℝ) : ℂ) + y * I)))⁻¹‖
        ≤ CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by
      calc _ ≤ CZ * (1 + |s.im + y|) ^ η' := hZ1
        _ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |y|) ^ η') :=
            mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le _ _ hη'0.le) hCZ0
        _ = CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by ring
    have hF := norm_pesoMellin_left hN1 ha0 ha2 (κ := 2 * η') (by positivity) (by linarith) y
    have h2a : (2 / a) ^ (1 + 2 * η') ≤ (4 / δ) ^ (1 + 2 * η') := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [div_le_div_iff₀ ha0 hδ]; linarith
    have hy : 0 < 1 + |y| := by positivity
    have hpow : (1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η')) = (1 + ‖y‖) ^ (-(1 + η')) := by
      rw [← Real.rpow_add hy, Real.norm_eq_abs]; congr 1; ring
    have hNe : (n : ℝ) ^ (2 * η' / 2) = (n : ℝ) ^ η' := by congr 1; ring
    rw [norm_mul]
    calc ‖(Lχ χ (s + (((-a : ℝ) : ℂ) + y * I)))⁻¹‖
          * ‖pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I)‖
        ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ (2 * η' / 2) * (2 / a) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := mul_le_mul hZ2 hF (norm_nonneg _) (by positivity)
      _ ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := by rw [hNe]; gcongr
      _ = Q_c * ((1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η'))) := by simp only [Q_c]; ring
      _ = Q_c * (1 + ‖y‖) ^ (-(1 + η')) := by rw [hpow]
  have hSφ : ∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      = (Lχ χ s)⁻¹ + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int := by
    rw [← hD, hrel]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast; field_simp
  have hsm := smoothing_errorL χ hn (s := s) (by linarith)
  have hdiff_eq : P χ n s - (Lχ χ s)⁻¹
      = -(∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
              * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - P χ n s)
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int := by
    linear_combination hSφ
  have h1_exp : (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
    have he1 : (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have he2 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
    calc (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) * 1 := by linarith
      _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by gcongr
  have h2_exp : (n : ℝ) ^ (-a) * (n : ℝ) ^ η' ≤ (n : ℝ) ^ (-δ / 3) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3_im : (1 + |s.im|) ^ η' ≤ (1 + |s.im|) ^ η :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hη'η
  have hA_term : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖
      ≤ Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
    have hpi_pos : 0 < 2 * Real.pi := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpi_pos)]
    calc (1 / (2 * Real.pi)) * ‖A_int‖
        ≤ (1 / (2 * Real.pi)) * (Q_c * J) := mul_le_mul_of_nonneg_left hAbound (by positivity)
      _ = CZ * (3 * (4 / δ) ^ (1 + 2 * η')) * J / (2 * Real.pi)
            * ((n : ℝ) ^ (-a) * (n : ℝ) ^ η') * (1 + |s.im|) ^ η' := by simp only [Q_c]; ring
      _ ≤ Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
          simp only [Cm]
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2_exp hCm0) h3_im
            (by positivity) (by positivity)
  rw [hdiff_eq]
  calc ‖-(∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
              * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - P χ n s)
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖
      ≤ ‖∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)
              * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
          - P χ n s‖
        + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A_int‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η + Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η :=
        add_le_add (hsm.trans h1_exp) hA_term
    _ = (1 + Cm) * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by ring

/-! ### Cota de `P_{Q,χ}` en la recta crítica -/

/-- Bajo `SinCerosDerechaL χ θ` (`1/2 ≤ θ < 1`):
`‖P_{Q,χ}(1/2 + ix)‖ ≤ C Q^{θ − 1/2 + δ} (1 + |x|)^η` para todo `Q ≥ 1` y todo `x`. -/
theorem P_recta_critica_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ δ η : ℝ}
    (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1) (hη : 0 < η) (hZ : SinCerosDerechaL χ θ) :
    ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → ∀ x : ℝ,
      ‖P χ Q (1 / 2 + (x : ℂ) * I)‖ ≤ C * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by
  obtain ⟨C, hC⟩ := balazard_saias_L hχ hθ hδ hθδ hη hZ
  obtain ⟨CZ, hCZ0, hCZ⟩ := Linv_bound_theta hχ hθ hδ hθδ hη hZ
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    have hp : (1 : ℝ) ≤ (1 + |(2 : ℂ).im|) ^ η := Real.one_le_rpow (by simp) hη.le
    have h1' : ‖P χ 1 2 - (Lχ χ 2)⁻¹‖ ≤ C * (1 + |(2 : ℂ).im|) ^ η := by simpa using h1
    have : 0 ≤ C * (1 + |(2 : ℂ).im|) ^ η := le_trans (norm_nonneg _) h1'
    by_contra hneg
    push Not at hneg
    have : C * (1 + |(2 : ℂ).im|) ^ η < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
    linarith
  refine ⟨4 * (CZ + C), fun Q hQ x => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set v : ℝ := θ - 1 / 2 + δ with hv
  have hv0 : 0 < v := by simp only [v]; linarith
  have hv1 : v ≤ 1 := by simp only [v]; linarith
  set s₀ : ℂ := ((θ + δ : ℝ) : ℂ) + (x : ℂ) * I with hs₀
  have hs₀re : s₀.re = θ + δ := by simp [hs₀]
  have hs₀im : s₀.im = x := by simp [hs₀]
  set M : ℝ := (CZ + C) * (1 + |x|) ^ η with hM
  have hM0 : 0 ≤ M := by positivity
  have hA : ∀ d : ℕ, ‖P χ d s₀‖ ≤ M := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp [P, hM0]
    have h1 := hC d hd s₀ (by rw [hs₀re])
    rw [hs₀im] at h1
    have h2 := hCZ s₀ (by rw [hs₀re])
    rw [hs₀im] at h2
    have h3 : (d : ℝ) ^ (-δ / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    calc ‖P χ d s₀‖ ≤ ‖P χ d s₀ - (Lχ χ s₀)⁻¹‖ + ‖(Lχ χ s₀)⁻¹‖ := norm_le_norm_sub_add _ _
      _ ≤ C * (d : ℝ) ^ (-δ / 3) * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := add_le_add h1 h2
      _ ≤ C * 1 * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := by gcongr
      _ = M := by rw [hM]; ring
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ v with hg
  have hginc : ∀ d : ℕ, g d ≤ g (d + 1) := fun d =>
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by push_cast; linarith) hv0.le
  have hterm : ∀ d ∈ Finset.Icc 1 Q,
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-(1 / 2 + (x : ℂ) * I))
        = (((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s₀)) * (g d : ℂ) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    simp only [hg]
    rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc _ ((d : ℂ) ^ (-s₀)),
      ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
    congr 2; rw [hs₀]; simp only [v]; push_cast; ring
  have hab : P χ Q (1 / 2 + (x : ℂ) * I)
      = P χ Q s₀ * (g (Q + 1) : ℂ)
        + ∑ d ∈ Finset.Icc 1 Q, P χ d s₀ * ((g d : ℂ) - g (d + 1)) := by
    unfold P; rw [Finset.sum_congr rfl hterm, abel_Icc]
  have htel : ∑ d ∈ Finset.Icc 1 Q, (g (d + 1) - g d) = g (Q + 1) - 1 := by
    have := telescopio_Ioc (fun d => -g d) (n := 0) Q
    rw [show Finset.Icc 1 Q = Finset.Ioc 0 Q from Finset.Icc_add_one_left_eq_Ioc 0 Q]
    simp only [zero_add] at this
    have hg1 : g 1 = 1 := by simp [hg]
    rw [hg1] at this
    linarith [this, show ∑ d ∈ Finset.Ioc 0 Q, (g (d + 1) - g d)
      = ∑ d ∈ Finset.Ioc 0 Q, (-g d - -g (d + 1)) from Finset.sum_congr rfl fun d _ => by ring]
  have hgQ : g (Q + 1) ≤ 2 * (Q : ℝ) ^ v := by
    simp only [hg]
    calc ((Q + 1 : ℕ) : ℝ) ^ v ≤ (2 * (Q : ℝ)) ^ v :=
          Real.rpow_le_rpow (by positivity)
            (by push_cast; linarith [show (1 : ℝ) ≤ Q by exact_mod_cast hQ]) hv0.le
      _ = 2 ^ v * (Q : ℝ) ^ v := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ 2 * (Q : ℝ) ^ v := by
          gcongr
          calc (2 : ℝ) ^ v ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hv1
            _ = 2 := Real.rpow_one 2
  have hg0 : ∀ d, 0 ≤ g d := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  rw [hab]
  calc ‖P χ Q s₀ * (g (Q + 1) : ℂ)
        + ∑ d ∈ Finset.Icc 1 Q, P χ d s₀ * ((g d : ℂ) - g (d + 1))‖
      ≤ ‖P χ Q s₀ * (g (Q + 1) : ℂ)‖
        + ∑ d ∈ Finset.Icc 1 Q, ‖P χ d s₀ * ((g d : ℂ) - g (d + 1))‖ :=
        le_trans (norm_add_le _ _) (by gcongr; exact norm_sum_le _ _)
    _ ≤ M * g (Q + 1) + ∑ d ∈ Finset.Icc 1 Q, M * (g (d + 1) - g d) := by
        gcongr with d _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
          exact mul_le_mul_of_nonneg_right (hA Q) (hg0 _)
        · rw [norm_mul, show ((g d : ℂ) - g (d + 1)) = ((g d - g (d + 1) : ℝ) : ℂ) by
              push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hginc d])]
          have := hA d; nlinarith [hginc d]
    _ = M * (2 * g (Q + 1) - 1) := by rw [← Finset.mul_sum, htel]; ring
    _ ≤ M * (4 * (Q : ℝ) ^ v) := by gcongr; linarith
    _ = 4 * (CZ + C) * (Q : ℝ) ^ (θ - 1 / 2 + δ) * (1 + |x|) ^ η := by rw [hM, hv]; ring

end AMate.Dirichlet
