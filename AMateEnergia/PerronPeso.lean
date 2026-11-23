import Mathlib

/-!
# Peso de Perron suavizado

`peso N h` vale `1` hasta `N`, baja linealmente en `[N, N + h]` y vale `0` después. Su
transformada de Mellin es `pesoMellin N h w = ((N+h)^{w+1} − N^{w+1})/(h w (w+1))`: la de
`peso` en `Re w > 0` (`mellin_peso`) y la de `peso − 1` en `−1 < Re w < 0`
(`mellin_peso_sub_one`). Por la inversión de Mellin de Mathlib,
`(1/2π) ∫ x^{−(σ+iy)} pesoMellin(σ+iy) dy` vale `peso N h x` si `σ > 0` y `peso N h x − 1` si
`−1 < σ < 0`. `norm_pesoMellin_le` y `norm_pesoMellin_le_int` dan las cotas en rectas verticales.
-/

open Complex MeasureTheory Set Filter Asymptotics

namespace AMate

/-! ### El peso -/

/-- Peso de Perron suavizado: `1` en `(−∞, N]`, lineal en `[N, N + h]`, `0` después. -/
noncomputable def peso (N h x : ℝ) : ℝ := max 0 (min 1 ((N + h - x) / h))

/-- Su transformada de Mellin, `((N+h)^{w+1} − N^{w+1})/(h w (w+1))`. -/
noncomputable def pesoMellin (N h : ℝ) (w : ℂ) : ℂ :=
  (((N + h : ℝ) : ℂ) ^ (w + 1) - ((N : ℝ) : ℂ) ^ (w + 1)) / ((h : ℂ) * w * (w + 1))

variable {N h : ℝ}

theorem peso_of_le (hh : 0 < h) {x : ℝ} (hx : x ≤ N) : peso N h x = 1 := by
  unfold peso
  have : 1 ≤ (N + h - x) / h := by rw [le_div_iff₀ hh]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem peso_of_mem (hh : 0 < h) {x : ℝ} (h1 : N ≤ x) (h2 : x ≤ N + h) :
    peso N h x = (N + h - x) / h := by
  unfold peso
  have a1 : (N + h - x) / h ≤ 1 := by rw [div_le_one hh]; linarith
  have a2 : 0 ≤ (N + h - x) / h := div_nonneg (by linarith) hh.le
  rw [min_eq_right a1, max_eq_right a2]

theorem peso_of_ge (hh : 0 < h) {x : ℝ} (hx : N + h ≤ x) : peso N h x = 0 := by
  unfold peso
  have : (N + h - x) / h ≤ 0 := by rw [div_le_iff₀ hh]; linarith
  rw [min_eq_right (le_trans this zero_le_one), max_eq_left this]

theorem peso_nonneg (x : ℝ) : 0 ≤ peso N h x := le_max_left _ _

theorem peso_le_one (x : ℝ) : peso N h x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_peso : Continuous (peso N h) := by
  unfold peso
  fun_prop

/-! ### Integrales de potencias en tramos -/

theorem integrableOn_Ioc_cpow {a b : ℝ} (ha : 0 < a) (r : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioc a b) := by
  rcases le_or_gt a b with hab | hab
  · exact (intervalIntegral.intervalIntegrable_cpow
      (Or.inr (Set.notMem_uIcc_of_lt ha (by linarith)))).1
  · rw [Ioc_eq_empty (not_lt.mpr hab.le)]
    exact integrableOn_empty

theorem integral_Ioc_cpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {r : ℂ} (hr : r ≠ -1) :
    ∫ t in Ioc a b, (t : ℂ) ^ r = ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hab,
    integral_cpow (Or.inr ⟨hr, Set.notMem_uIcc_of_lt ha (by linarith)⟩)]

theorem cpow_eq_cpow_sub_one_mul {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ w = (t : ℂ) ^ (w - 1) * t := by
  have h1 : (t : ℂ) ^ w = (t : ℂ) ^ ((w - 1) + 1) := by ring_nf
  rw [h1, cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one]

theorem cpow_add_one_eq {t : ℝ} (ht : 0 < t) (w : ℂ) : (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t := by
  rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one]

/-! ### Transformadas de Mellin del peso -/

theorem mellin_peso (hN : 0 < N) (hh : 0 < h) {w : ℂ} (hw : 0 < w.re) :
    mellin (fun x => ((peso N h x : ℝ) : ℂ)) w = pesoMellin N h w := by
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  have hw1 : w + 1 ≠ 0 := by
    intro h0
    have := congrArg re h0
    simp at this
    linarith
  have hw1' : w - 1 ≠ -1 := by intro h0; apply hw0; linear_combination h0
  have hw2 : w ≠ -1 := by intro h0; apply hw1; rw [h0]; ring
  have hNh : N ≤ N + h := by linarith
  have hNh0 : 0 < N + h := by linarith
  unfold mellin
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1) • ((peso N h t : ℝ) : ℂ) with hg
  have e1 : EqOn g (fun t => (t : ℂ) ^ (w - 1)) (Ioc 0 N) := fun t ht => by
    simp only [hg, peso_of_le hh ht.2, ofReal_one, smul_eq_mul, mul_one]
  have e2 : EqOn g (fun t => (((N + h : ℝ) : ℂ) / (h : ℂ)) * (t : ℂ) ^ (w - 1)
      - (1 / (h : ℂ)) * (t : ℂ) ^ w) (Ioc N (N + h)) := fun t ht => by
    have ht0 : (0 : ℝ) < t := lt_trans hN ht.1
    simp only [hg, peso_of_mem hh ht.1.le ht.2, smul_eq_mul]
    rw [cpow_eq_cpow_sub_one_mul ht0 w]
    have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    push_cast
    field_simp
  have e3 : EqOn g (fun _ => (0 : ℂ)) (Ioi (N + h)) := fun t ht => by
    simp only [hg, peso_of_ge hh (le_of_lt ht), ofReal_zero, smul_zero]
  have i1 : IntegrableOn g (Ioc 0 N) := by
    refine IntegrableOn.congr_fun ?_ e1.symm measurableSet_Ioc
    exact (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := N)
      (by simp; linarith)).1
  have i2 : IntegrableOn g (Ioc N (N + h)) :=
    IntegrableOn.congr_fun ((Integrable.const_mul (integrableOn_Ioc_cpow hN _) _).sub
      (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _)) e2.symm measurableSet_Ioc
  have i3 : IntegrableOn g (Ioi (N + h)) :=
    IntegrableOn.congr_fun integrableOn_zero e3.symm measurableSet_Ioi
  have i23 : IntegrableOn g (Ioi N) := by
    rw [← Ioc_union_Ioi_eq_Ioi hNh]
    exact i2.union i3
  rw [← Ioc_union_Ioi_eq_Ioi hN.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    i1 i23, ← Ioc_union_Ioi_eq_Ioi hNh, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi i2 i3, setIntegral_congr_fun measurableSet_Ioc e1,
    setIntegral_congr_fun measurableSet_Ioc e2, setIntegral_congr_fun measurableSet_Ioi e3,
    integral_zero, add_zero]
  have I1 : ∫ t in Ioc 0 N, (t : ℂ) ^ (w - 1) = ((N : ℝ) : ℂ) ^ w / w := by
    rw [← intervalIntegral.integral_of_le hN.le, integral_cpow (Or.inl (by simp; linarith)),
      show w - 1 + 1 = w by ring, ofReal_zero, zero_cpow hw0, sub_zero]
  rw [I1, integral_sub (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _)
      (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _),
    integral_const_mul, integral_const_mul, integral_Ioc_cpow hN hNh hw1',
    integral_Ioc_cpow hN hNh hw2, show w - 1 + 1 = w by ring]
  unfold pesoMellin
  rw [cpow_add_one_eq hNh0, cpow_add_one_eq hN]
  have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  push_cast
  field_simp
  ring

theorem mellin_peso_sub_one (hN : 0 < N) (hh : 0 < h) {w : ℂ} (hw1 : -1 < w.re)
    (hw : w.re < 0) :
    mellin (fun x => ((peso N h x - 1 : ℝ) : ℂ)) w = pesoMellin N h w := by
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  have hw1n : w + 1 ≠ 0 := by
    intro h0
    have := congrArg re h0
    simp at this
    linarith
  have hw1' : w - 1 ≠ -1 := by intro h0; apply hw0; linear_combination h0
  have hw2 : w ≠ -1 := by intro h0; apply hw1n; rw [h0]; ring
  have hNh : N ≤ N + h := by linarith
  have hNh0 : 0 < N + h := by linarith
  unfold mellin
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1) • ((peso N h t - 1 : ℝ) : ℂ) with hg
  have e1 : EqOn g (fun _ => (0 : ℂ)) (Ioc 0 N) := fun t ht => by
    simp only [hg, peso_of_le hh ht.2, sub_self, ofReal_zero, smul_zero]
  have e2 : EqOn g (fun t => (((N : ℝ) : ℂ) / (h : ℂ)) * (t : ℂ) ^ (w - 1)
      - (1 / (h : ℂ)) * (t : ℂ) ^ w) (Ioc N (N + h)) := fun t ht => by
    have ht0 : (0 : ℝ) < t := lt_trans hN ht.1
    simp only [hg, peso_of_mem hh ht.1.le ht.2, smul_eq_mul]
    rw [cpow_eq_cpow_sub_one_mul ht0 w]
    have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    push_cast
    field_simp
    ring
  have e3 : EqOn g (fun t => -(t : ℂ) ^ (w - 1)) (Ioi (N + h)) := fun t ht => by
    simp only [hg, peso_of_ge hh (le_of_lt ht), smul_eq_mul]
    push_cast
    ring
  have hlt : (w - 1).re < -1 := by simp; linarith
  have i1 : IntegrableOn g (Ioc 0 N) :=
    IntegrableOn.congr_fun integrableOn_zero e1.symm measurableSet_Ioc
  have i2 : IntegrableOn g (Ioc N (N + h)) :=
    IntegrableOn.congr_fun ((Integrable.const_mul (integrableOn_Ioc_cpow hN _) _).sub
      (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _)) e2.symm measurableSet_Ioc
  have i3 : IntegrableOn g (Ioi (N + h)) :=
    IntegrableOn.congr_fun (integrableOn_Ioi_cpow_of_lt hlt hNh0).neg e3.symm measurableSet_Ioi
  have i23 : IntegrableOn g (Ioi N) := by
    rw [← Ioc_union_Ioi_eq_Ioi hNh]
    exact i2.union i3
  rw [← Ioc_union_Ioi_eq_Ioi hN.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    i1 i23, ← Ioc_union_Ioi_eq_Ioi hNh, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi i2 i3, setIntegral_congr_fun measurableSet_Ioc e1,
    setIntegral_congr_fun measurableSet_Ioc e2, setIntegral_congr_fun measurableSet_Ioi e3,
    integral_zero, zero_add, integral_neg, integral_Ioi_cpow_of_lt hlt hNh0,
    integral_sub (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _)
      (Integrable.const_mul (integrableOn_Ioc_cpow hN _) _),
    integral_const_mul, integral_const_mul, integral_Ioc_cpow hN hNh hw1',
    integral_Ioc_cpow hN hNh hw2, show w - 1 + 1 = w by ring]
  unfold pesoMellin
  rw [cpow_add_one_eq hNh0, cpow_add_one_eq hN]
  have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  push_cast
  field_simp
  ring

/-! ### Cotas de `pesoMellin` -/

theorem norm_pesoMellin_le (hN : 0 < N) (hh : 0 < h) (w : ℂ) :
    ‖pesoMellin N h w‖ ≤ ((N + h) ^ (w.re + 1) + N ^ (w.re + 1)) / (h * ‖w‖ * ‖w + 1‖) := by
  unfold pesoMellin
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ‖((N + h : ℝ) : ℂ) ^ (w + 1) - ((N : ℝ) : ℂ) ^ (w + 1)‖
      ≤ ‖((N + h : ℝ) : ℂ) ^ (w + 1)‖ + ‖((N : ℝ) : ℂ) ^ (w + 1)‖ := norm_sub_le _ _
    _ = (N + h) ^ (w.re + 1) + N ^ (w.re + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
        simp

/-- En `Re w ≤ 0`: `‖pesoMellin w‖ ≤ N^{Re w}/‖w‖`, porque es `(1/(h w)) ∫_N^{N+h} t^w dt`. -/
theorem norm_pesoMellin_le_int (hN : 0 < N) (hh : 0 < h) {w : ℂ} (hw : w.re ≤ 0)
    (hw1 : w + 1 ≠ 0) : ‖pesoMellin N h w‖ ≤ N ^ w.re / ‖w‖ := by
  by_cases hw0 : w = 0
  · subst hw0
    simp [pesoMellin]
  have hw2 : w ≠ -1 := fun h0 => hw1 (by rw [h0]; ring)
  have hh0 : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  have hint : ∫ t in N..(N + h), (t : ℂ) ^ w
      = (((N + h : ℝ) : ℂ) ^ (w + 1) - ((N : ℝ) : ℂ) ^ (w + 1)) / (w + 1) :=
    integral_cpow (Or.inr ⟨hw2, Set.notMem_uIcc_of_lt hN (by linarith)⟩)
  have hF : pesoMellin N h w = (∫ t in N..(N + h), (t : ℂ) ^ w) / ((h : ℂ) * w) := by
    unfold pesoMellin
    rw [hint]
    field_simp
  have hbd : ‖∫ t in N..(N + h), (t : ℂ) ^ w‖ ≤ N ^ w.re * |N + h - N| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht0 : 0 < t := lt_trans hN ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    exact Real.rpow_le_rpow_of_nonpos hN ht.1.le hw
  rw [show N + h - N = h by ring, abs_of_pos hh] at hbd
  rw [hF, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [div_le_div_iff₀ (by positivity) hwpos]
  nlinarith

theorem norm_line_ge (σ y : ℝ) : min |σ| 1 / 2 * (1 + |y|) ≤ ‖(σ : ℂ) + y * I‖ := by
  have h1 : |σ| ≤ ‖(σ : ℂ) + y * I‖ := by simpa using Complex.abs_re_le_norm ((σ : ℂ) + y * I)
  have h2 : |y| ≤ ‖(σ : ℂ) + y * I‖ := by simpa using Complex.abs_im_le_norm ((σ : ℂ) + y * I)
  have hm1 : min |σ| 1 ≤ |σ| := min_le_left _ _
  have hm2 : min |σ| 1 ≤ 1 := min_le_right _ _
  have hm3 : min |σ| 1 * |y| ≤ |y| := mul_le_of_le_one_left (abs_nonneg y) hm2
  nlinarith

theorem integrable_pesoMellin_line (hN : 0 < N) (hh : 0 < h) {σ : ℝ} (hσ0 : σ ≠ 0)
    (hσ1 : σ ≠ -1) : Integrable (fun y : ℝ => pesoMellin N h ((σ : ℂ) + y * I)) := by
  have hc₁ : 0 < min |σ| 1 / 2 := by
    have : 0 < |σ| := abs_pos.mpr hσ0
    positivity
  have hc₂ : 0 < min |σ + 1| 1 / 2 := by
    have : 0 < |σ + 1| := abs_pos.mpr (fun h0 => hσ1 (by linarith))
    positivity
  set K : ℝ := ((N + h) ^ (σ + 1) + N ^ (σ + 1)) / (h * (min |σ| 1 / 2) * (min |σ + 1| 1 / 2))
    with hK
  have hbound : ∀ y : ℝ, ‖pesoMellin N h ((σ : ℂ) + y * I)‖ ≤ K * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro y
    have hw := norm_line_ge σ y
    have hw1 := norm_line_ge (σ + 1) y
    have e : ((σ : ℂ) + y * I) + 1 = ((σ + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    have hy : 0 < 1 + |y| := by positivity
    calc ‖pesoMellin N h ((σ : ℂ) + y * I)‖
        ≤ ((N + h) ^ (σ + 1) + N ^ (σ + 1))
          / (h * ‖(σ : ℂ) + y * I‖ * ‖(σ : ℂ) + y * I + 1‖) := by
          have := norm_pesoMellin_le hN hh ((σ : ℂ) + y * I)
          rwa [hre] at this
      _ ≤ ((N + h) ^ (σ + 1) + N ^ (σ + 1))
          / (h * (min |σ| 1 / 2 * (1 + |y|)) * (min |σ + 1| 1 / 2 * (1 + |y|))) := by
          rw [e]
          gcongr
      _ = K * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
          rw [Real.norm_eq_abs, Real.rpow_neg hy.le, Real.rpow_two, hK]
          field_simp
  have hcont : Continuous (fun y : ℝ => pesoMellin N h ((σ : ℂ) + y * I)) := by
    unfold pesoMellin
    have hden : ∀ y : ℝ, (h : ℂ) * ((σ : ℂ) + y * I) * ((σ : ℂ) + y * I + 1) ≠ 0 := by
      intro y
      refine mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hh.ne') ?_) ?_
      · intro h0
        have := congrArg re h0
        simp at this
        exact hσ0 this
      · intro h0
        have := congrArg re h0
        simp at this
        exact hσ1 (by linarith)
    refine Continuous.div (Continuous.sub ?_ ?_) (by fun_prop) hden
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr (by linarith)))
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hN.ne'))
  exact Integrable.mono' ((integrable_one_add_norm (by norm_num)).const_mul K)
    hcont.aestronglyMeasurable (Eventually.of_forall hbound)

/-! ### Inversión de Mellin -/

/-- `(1/2π) ∫ x^{−(σ+iy)} pesoMellin(σ+iy) dy = φ(x)` para `σ > 0`. -/
theorem mellinInv_pesoMellin (hN : 0 < N) (hh : 0 < h) {σ : ℝ} (hσ : 0 < σ) {x : ℝ}
    (hx : 0 < x) : mellinInv σ (pesoMellin N h) x = ((peso N h x : ℝ) : ℂ) := by
  set φ : ℝ → ℂ := fun x => ((peso N h x : ℝ) : ℂ) with hφ
  have hcφ : Continuous φ := continuous_ofReal.comp continuous_peso
  have hline : ∀ y : ℝ, mellin φ ((σ : ℂ) + y * I) = pesoMellin N h ((σ : ℂ) + y * I) :=
    fun y => mellin_peso hN hh (by simpa using hσ)
  have hconv : MellinConvergent φ σ := by
    apply mellinConvergent_of_isBigO_rpow (a := σ + 1) (b := 0)
    · exact hcφ.continuousOn.locallyIntegrableOn measurableSet_Ioi
    · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
      filter_upwards [eventually_ge_atTop (N + h)] with x hx
      simp [hφ, peso_of_ge hh hx]
    · simp
    · have e : (fun x : ℝ => x ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by funext x; simp
      rw [e]
      refine EventuallyEq.trans_isBigO ?_ (isBigO_const_const (1 : ℂ) one_ne_zero _)
      filter_upwards [Ioo_mem_nhdsGT hN] with x hx
      simp [hφ, peso_of_le hh hx.2.le]
    · simpa using hσ
  have hvert : VerticalIntegrable (mellin φ) σ := by
    unfold VerticalIntegrable
    simp_rw [hline]
    exact integrable_pesoMellin_line hN hh hσ.ne' (by linarith)
  have hinv := mellinInv_mellin_eq σ φ hx hconv hvert hcφ.continuousAt
  rw [show ((peso N h x : ℝ) : ℂ) = φ x from rfl, ← hinv]
  unfold mellinInv
  simp_rw [hline]

/-- `(1/2π) ∫ x^{−(σ+iy)} pesoMellin(σ+iy) dy = φ(x) − 1` para `−1 < σ < 0`. -/
theorem mellinInv_pesoMellin_neg (hN : 0 < N) (hh : 0 < h) {σ : ℝ} (hσ1 : -1 < σ) (hσ : σ < 0)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (pesoMellin N h) x = ((peso N h x - 1 : ℝ) : ℂ) := by
  set φ : ℝ → ℂ := fun x => ((peso N h x - 1 : ℝ) : ℂ) with hφ
  have hcφ : Continuous φ := continuous_ofReal.comp (continuous_peso.sub continuous_const)
  have hline : ∀ y : ℝ, mellin φ ((σ : ℂ) + y * I) = pesoMellin N h ((σ : ℂ) + y * I) :=
    fun y => mellin_peso_sub_one hN hh (by simpa using hσ1) (by simpa using hσ)
  have hconv : MellinConvergent φ σ := by
    apply mellinConvergent_of_isBigO_rpow (a := 0) (b := -1)
    · exact hcφ.continuousOn.locallyIntegrableOn measurableSet_Ioi
    · have e : (fun x : ℝ => x ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by funext x; simp
      rw [e]
      refine EventuallyEq.trans_isBigO ?_ (isBigO_const_const (-1 : ℂ) one_ne_zero _)
      filter_upwards [eventually_ge_atTop (N + h)] with x hx
      simp [hφ, peso_of_ge hh hx]
    · simpa using hσ
    · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
      filter_upwards [Ioo_mem_nhdsGT hN] with x hx
      simp [hφ, peso_of_le hh hx.2.le]
    · simpa using hσ1
  have hvert : VerticalIntegrable (mellin φ) σ := by
    unfold VerticalIntegrable
    simp_rw [hline]
    exact integrable_pesoMellin_line hN hh hσ.ne (by linarith)
  have hinv := mellinInv_mellin_eq σ φ hx hconv hvert hcφ.continuousAt
  rw [show ((peso N h x - 1 : ℝ) : ℂ) = φ x from rfl, ← hinv]
  unfold mellinInv
  simp_rw [hline]

end AMate
