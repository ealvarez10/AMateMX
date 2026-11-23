import AMateEnergia.CalibracionTheta
import AMateEnergia.DeficitPrimos

/-!
# Equivalencias completas entre `RH`, las ventanas `(V)` de von Mangoldt y `S_AMate(Y)`

Cierra las direcciones recíprocas de `VentanaLandau` y `DeficitPrimos`, estableciendo en Lean la
equivalencia cuádruple entre `RiemannHypothesis`, la energía canónica `E_Q`, las ventanas
unilaterales `(V)` de `G_vonMangoldt` y la suma aritmética de déficits sobre primos grandes
`S_AMate(Y)`:

* `H_zeta`, `mellin_φ_G`, `cota_G_vonMangoldt_de_sin_ceros`: usando `mellinInv_mellin_eq` en `σ = 3`
  y el desplazamiento de contorno `integral_vertical_eq` para `H_ζ(w) = Φ_ζ(w) − (1 + γ_E)/w`
  (holomorfa en todo `Re w > θ`, incluido `w = 1`, con decaimiento `O(|Im w|^{−3/2})`),
  `SinCerosDerecha θ` implica `|G_vonMangoldt y| ≤ C y^{σ₀}` para todo `σ₀ ∈ (θ, 1)` y `y ≥ 1`.
* `ventana_vonMangoldt_de_rh` y `rh_iff_ventana_vonMangoldt`: equivalencia exacta `RH ↔ (V)`.
* `deficit_primos_le_G_vonMangoldt`: desigualdad complementaria
  `γ_E x − A_primos x ≤ G_vonMangoldt x + √x log x + √x (log x)² / log 2 + log x + 1` para `x ≥ 2`.
* `deficit_primos_de_rh` y `rh_iff_deficit_primos`: equivalencia exacta
  `RH ↔ (∀ η > 0, ∀ Y₀, ∃ Y ≥ Y₀, S_AMate Y ≤ Y^η)`.
-/

open Complex MeasureTheory Set Filter Metric Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt

namespace AMate

/-! ### Inversión de Mellin y desplazamiento de contorno para `G_vonMangoldt` -/

theorem G_vonMangoldt_one : G_vonMangoldt 1 = 1 + Real.eulerMascheroniConstant := by
  unfold G_vonMangoldt rampaVonMangoldt
  rw [Nat.floor_one]
  simp

/-- Perfil reflejado en `(0, 1)`, continuo en todo `(0, ∞)` gracias a `G(1) = 1 + γ_E`. -/
noncomputable def φ_G (u : ℝ) : ℂ :=
  if u < 1 then ((G_vonMangoldt (1 / u) - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ) else 0

/-- Transformada de Mellin regularizada `H_ζ(w) = Φ_ζ(w) − (1 + γ_E)/w`. -/
noncomputable def H_zeta (w : ℂ) : ℂ :=
  Phi_zeta w - (1 + (Real.eulerMascheroniConstant : ℂ)) / w

theorem φ_G_inv_of_ge_one {y : ℝ} (hy : 1 ≤ y) :
    φ_G (1 / y) = ((G_vonMangoldt y - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hy with rfl | hgt
  · simp [φ_G, G_vonMangoldt_one]
  · have hu_lt : 1 / y < 1 := (div_lt_one (lt_trans one_pos hgt)).mpr hgt
    have hy_inv : 1 / (1 / y) = y := one_div_one_div y
    unfold φ_G
    rw [if_pos hu_lt, hy_inv]

theorem continuousOn_φ_G : ContinuousOn φ_G (Ioi 0) := by
  intro u hu
  have hu_pos : (0 : ℝ) < u := hu
  rcases lt_trichotomy u 1 with hlt | rfl | hgt
  · have hcont : ContinuousAt
        (fun t : ℝ => ((G_vonMangoldt (1 / t) - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ)) u := by
      refine continuous_ofReal.continuousAt.comp (ContinuousAt.sub ?_ continuousAt_const)
      have hG_at : ContinuousAt G_vonMangoldt (1 / u) :=
        continuousOn_G_vonMangoldt.continuousAt (isOpen_Ioi.mem_nhds (one_div_pos.mpr hu_pos))
      exact hG_at.comp (continuousAt_const.div continuousAt_id hu_pos.ne')
    have hev : (fun t : ℝ => ((G_vonMangoldt (1 / t) - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ))
        =ᶠ[𝓝 u] φ_G := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
      simp [φ_G, show t < 1 from ht]
    exact (hcont.congr hev).continuousWithinAt
  · have hcont_left : ContinuousAt
        (fun t : ℝ => ((G_vonMangoldt (1 / t) - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ)) 1 := by
      refine continuous_ofReal.continuousAt.comp (ContinuousAt.sub ?_ continuousAt_const)
      have hG_at : ContinuousAt G_vonMangoldt (1 / (1 : ℝ)) :=
        continuousOn_G_vonMangoldt.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
      exact hG_at.comp (continuousAt_const.div continuousAt_id one_ne_zero)
    have hval1 : ((G_vonMangoldt (1 / (1 : ℝ)) - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ) = 0 := by
      rw [div_one, G_vonMangoldt_one, sub_self, ofReal_zero]
    rw [ContinuousWithinAt, show φ_G 1 = 0 by simp [φ_G]]
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev := (Metric.tendsto_nhds.mp hcont_left) ε hε
    dsimp only at hev
    rw [hval1] at hev
    filter_upwards [hev] with t ht
    by_cases ht1 : t < 1
    · simpa [φ_G, ht1] using ht
    · simp [φ_G, ht1, hε]
  · have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 u] φ_G := by
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
      have hnot : ¬ t < 1 := not_lt.mpr (le_of_lt ht)
      simp [φ_G, hnot]
    exact (continuousAt_const.congr hev).continuousWithinAt

theorem mellin_φ_G {s : ℂ} (hs : 2 < s.re) : mellin φ_G s = H_zeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  unfold mellin H_zeta
  -- Cambio `y = e^v` para la constante `1 + γ_E`.
  have himg_exp : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext y; simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨v, hv, hy⟩ => hy ▸ Real.one_lt_exp_iff.mpr hv,
      fun hy => ⟨Real.log y, Real.log_pos hy, Real.exp_log (lt_trans one_pos hy)⟩⟩
  have hval_const : ∫ v in Ioi (0 : ℝ),
        (1 + (Real.eulerMascheroniConstant : ℂ)) * Complex.exp (-s * v)
      = (1 + (Real.eulerMascheroniConstant : ℂ)) / s := by
    have hchg : ∫ v in Ioi (0 : ℝ),
          (1 + (Real.eulerMascheroniConstant : ℂ)) * Complex.exp (-s * v)
        = ∫ y in Ioi (1 : ℝ), (1 + (Real.eulerMascheroniConstant : ℂ)) * (y : ℂ) ^ (-s - 1) := by
      rw [← himg_exp, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt) Real.exp_injective.injOn]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      rw [abs_of_pos (Real.exp_pos v), Complex.real_smul,
        Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
        ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp,
        mul_left_comm, ← Complex.exp_add]
      congr 2; ring
    rw [hchg, integral_const_mul, integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
    simp only [ofReal_one, one_cpow]
    have : -s - 1 + 1 = -s := by ring
    rw [this]
    field_simp
  -- Integrabilidad en `Ioi 0` para restar las dos integrales de Laplace.
  set C₀ : ℝ := 4 + |Real.eulerMascheroniConstant|
  have hint_G : IntegrableOn
      (fun v : ℝ => ((G_vonMangoldt (Real.exp v) : ℝ) : ℂ) * Complex.exp (-s * v)) (Ioi 0) := by
    have hdom : IntegrableOn (fun v : ℝ => C₀ * Real.exp (-(s.re - 2) * v)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul C₀
    refine hdom.mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (measurable_G_vonMangoldt.comp Real.measurable_exp)).mul
        (by measurability)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : (0 : ℝ) < v := hv
      have hg_bd : |G_vonMangoldt (Real.exp v)| ≤ C₀ * Real.exp (2 * v) := by
        have he2 : (Real.exp v) ^ 2 = Real.exp (2 * v) := by rw [sq, ← Real.exp_add]; ring_nf
        simpa [C₀, he2] using abs_G_vonMangoldt_le (Real.one_le_exp hv0.le)
      have hre : (-s * (v : ℂ)).re = -s.re * v := by simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
      calc |G_vonMangoldt (Real.exp v)| * Real.exp (-s.re * v)
          ≤ (C₀ * Real.exp (2 * v)) * Real.exp (-s.re * v) :=
            mul_le_mul_of_nonneg_right hg_bd (Real.exp_pos _).le
        _ = C₀ * Real.exp (-(s.re - 2) * v) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hint_const : IntegrableOn
      (fun v : ℝ => (1 + (Real.eulerMascheroniConstant : ℂ)) * Complex.exp (-s * v)) (Ioi 0) := by
    have hdom : IntegrableOn (fun v : ℝ => ‖(1 : ℂ) + Real.eulerMascheroniConstant‖ * Real.exp (-s.re * v))
        (Ioi 0) := (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
    refine hdom.mono' (by measurability) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => ?_)
    have hre : (-s * (v : ℂ)).re = -s.re * v := by simp
    rw [norm_mul, Complex.norm_exp, hre]
  -- Cambio `u = exp (−v)` entre `Ioi 0` e `Ioo 0 1`.
  let g_neg : ℝ → ℝ := fun v => Real.exp (-v)
  have himg_neg : g_neg '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext u; simp only [mem_image, mem_Ioi, mem_Ioo, g_neg]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Real.exp_pos (-v), Real.exp_lt_one_iff.mpr (by linarith)⟩
    · rintro ⟨hu0, hu1⟩
      exact ⟨-Real.log u, by linarith [Real.log_neg hu0 hu1], by rw [neg_neg, Real.exp_log hu0]⟩
  have hinj_neg : InjOn g_neg (Ioi 0) := fun v₁ _ v₂ _ h => by
    have := Real.exp_injective h; linarith
  have hderiv_neg : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt g_neg (-Real.exp (-v)) (Ioi 0) v :=
    fun v _ => by
      simpa [g_neg, mul_comm] using (hasDerivAt_neg v).exp.hasDerivWithinAt
  have hcongr_neg : ∀ v ∈ Ioi (0 : ℝ),
      |-Real.exp (-v)| • ((g_neg v : ℂ) ^ (s - 1) • φ_G (g_neg v))
        = ((G_vonMangoldt (Real.exp v) : ℝ) : ℂ) * Complex.exp (-s * v)
          - (1 + (Real.eulerMascheroniConstant : ℂ)) * Complex.exp (-s * v) := by
    intro v hv
    have hv_pos : (0 : ℝ) < v := hv
    have hu_lt : g_neg v < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hinv_exp : 1 / g_neg v = Real.exp v := by
      simp only [g_neg, one_div, ← Real.exp_neg, neg_neg]
    rw [abs_neg, abs_of_pos (Real.exp_pos (-v)), Complex.real_smul, smul_eq_mul,
      φ_G, if_pos hu_lt, hinv_exp]
    have hpow : (Real.exp (-v) : ℂ) * (g_neg v : ℂ) ^ (s - 1) = Complex.exp (-s * v) := by
      simp only [g_neg]
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos (-v)).ne'),
        ← Complex.ofReal_log (Real.exp_pos (-v)).le, Real.log_exp, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← mul_assoc, hpow]
    push_cast; ring
  have hint_Ioo : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • φ_G u) (Ioo 0 1) := by
    rw [← himg_neg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hderiv_neg hinj_neg]
    exact (hint_G.sub hint_const).congr_fun (fun v hv => (hcongr_neg v hv).symm) measurableSet_Ioi
  have hzero_Ici1 : EqOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • φ_G u) (fun _ => (0 : ℂ)) (Ici 1) :=
    fun u hu => by
      have hnot : ¬ u < 1 := not_lt.mpr hu
      simp [φ_G, hnot]
  have hint_Ici1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • φ_G u) (Ici 1) :=
    integrableOn_zero.congr_fun hzero_Ici1.symm measurableSet_Ici
  rw [← Ioo_union_Ici_eq_Ioi one_pos,
    setIntegral_union (s := Ioo 0 1) (t := Ici 1)
      (Set.disjoint_left.mpr fun u hu1 hu2 => not_lt.mpr hu2 hu1.2)
      measurableSet_Ici hint_Ioo hint_Ici1,
    setIntegral_congr_fun measurableSet_Ici hzero_Ici1, integral_zero, add_zero,
    ← himg_neg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv_neg hinj_neg,
    setIntegral_congr_fun measurableSet_Ioi hcongr_neg,
    integral_sub hint_G hint_const, ← Phi_zeta_eq_laplace hs, hval_const]

theorem H_zeta_eq_of_ne {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hζ : riemannZeta w ≠ 0) :
    H_zeta w = (-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ))
        / (w * (w - 1)) - 1 / (w - 1) ^ 2 := by
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  unfold H_zeta
  rw [Phi_zeta_of_ne_one hw1, deriv_zetaEntera_of_ne_one hw1, zetaEntera_of_ne_one hw1]
  field_simp
  ring

theorem differentiableOn_H_zeta {θ : ℝ} (hθ0 : 0 ≤ θ) (hZ : SinCerosDerecha θ) :
    DifferentiableOn ℂ H_zeta {w | θ < w.re} := by
  intro w hw
  have hw_re : θ < w.re := hw
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_re] at hw_re; linarith
  exact ((analyticAt_Phi_zeta hw0 (hZ w hw_re)).differentiableAt.sub
    ((differentiableAt_const _).div differentiableAt_id hw0)).differentiableWithinAt

/-- Bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`), en cualquier banda cerrada `σ₀ ≤ Re w ≤ 3` con
`θ < σ₀ < 1`, se tiene `‖H_zeta w‖ ≤ M_H (1 + |Im w|)^{−3/2}`. -/
theorem cota_banda_H_zeta {θ σ₀ : ℝ} (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₀) (hσ1 : σ₀ < 1)
    (hZ : SinCerosDerecha θ) :
    ∃ M_H : ℝ, 0 ≤ M_H ∧ ∀ w : ℂ, σ₀ ≤ w.re → w.re ≤ 3 →
      ‖H_zeta w‖ ≤ M_H * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by
  set δ : ℝ := (σ₀ - θ) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hθσ)
  have hθδ : θ + δ < 1 := by simp only [δ]; linarith
  obtain ⟨C_ld, hCld0, hCld⟩ :=
    inv_and_logDeriv_zeta_bound_theta hθ hδ hθδ (by norm_num : (0 : ℝ) < 1 / 2) hZ
  -- Compacidad en la caja `|Im w| ≤ 4`.
  set Kbox : Set ℂ := {w | σ₀ ≤ w.re ∧ w.re ≤ 3 ∧ |w.im| ≤ 4}
  have hKbox_c : IsCompact Kbox := by
    apply (isCompact_closedBall (0 : ℂ) 8).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_re).inter
        ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp continuous_im) continuous_const))
    · intro w hw
      rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im w
      have h1 : |w.re| ≤ 3 := abs_le.mpr ⟨by linarith [hw.1], hw.2.1⟩
      linarith [hw.2.2]
  have hcont_K : ContinuousOn H_zeta Kbox :=
    (differentiableOn_H_zeta (by linarith) hZ).continuousOn.mono fun w hw => by
      show θ < w.re; linarith [hw.1]
  obtain ⟨K₀, hK₀⟩ := hKbox_c.bddAbove_image hcont_K.norm
  set K₀' : ℝ := max K₀ 0
  set C_hi : ℝ := (C_ld + 2 + |Real.eulerMascheroniConstant|) * (2 : ℝ) ^ (3 / 2 : ℝ)
  set C_lo : ℝ := K₀' * (5 : ℝ) ^ (3 / 2 : ℝ)
  refine ⟨C_lo + C_hi, by positivity, fun w hw_lo hw_hi => ?_⟩
  rcases le_or_gt 4 |w.im| with him | him
  · have ht_pos : 0 < |w.im| := by linarith
    have hw0 : w ≠ 0 := by intro h; rw [h] at him; simp at him; linarith
    have hw1 : w ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
    have hζ_ne : riemannZeta w ≠ 0 := hZ w (by linarith)
    rw [H_zeta_eq_of_ne hw0 hw1 hζ_ne]
    have hld := (hCld w (by simp only [δ]; linarith) him).2
    have hnw : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hnw1 : |w.im| ≤ ‖w - 1‖ := by
      simpa using Complex.abs_im_le_norm (w - 1)
    have hden1 : |w.im| ^ 2 ≤ ‖w * (w - 1)‖ := by
      rw [norm_mul, sq]; exact mul_le_mul hnw hnw1 ht_pos.le (norm_nonneg _)
    have hden2 : |w.im| ^ 2 ≤ ‖(w - 1) ^ 2‖ := by
      rw [norm_pow]; exact (sq_le_sq₀ ht_pos.le (norm_nonneg _)).mpr hnw1
    have hnum_le : ‖-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ)‖
        ≤ (C_ld + 1 + |Real.eulerMascheroniConstant|) * |w.im| ^ (1 / 2 : ℝ) := by
      have ht12 : 1 ≤ |w.im| ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have htri1 := norm_add_le (-deriv riemannZeta w / riemannZeta w + 1)
        (Real.eulerMascheroniConstant : ℂ)
      have htri2 := norm_add_le (-deriv riemannZeta w / riemannZeta w) (1 : ℂ)
      rw [neg_div, Complex.norm_real, Real.norm_eq_abs] at htri1
      rw [neg_div, norm_neg, norm_one] at htri2
      rw [neg_div]
      nlinarith [abs_nonneg Real.eulerMascheroniConstant]
    have h1_le : ‖1 / (w - 1) ^ 2‖ ≤ |w.im| ^ (1 / 2 : ℝ) / |w.im| ^ 2 := by
      rw [norm_div, norm_one]
      have ht12 : 1 ≤ |w.im| ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      exact div_le_div₀ (by positivity) ht12 (by positivity) hden2
    have hdiv_le : ‖(-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ))
          / (w * (w - 1)) - 1 / (w - 1) ^ 2‖
        ≤ (C_ld + 2 + |Real.eulerMascheroniConstant|) * (|w.im| ^ (1 / 2 : ℝ) / |w.im| ^ 2) := by
      have htri := norm_sub_le
        ((-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ)) / (w * (w - 1)))
        (1 / (w - 1) ^ 2)
      rw [norm_div] at htri
      have hq : ‖-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ)‖
          / ‖w * (w - 1)‖
          ≤ ((C_ld + 1 + |Real.eulerMascheroniConstant|) * |w.im| ^ (1 / 2 : ℝ)) / |w.im| ^ 2 :=
        div_le_div₀ (by positivity) hnum_le (by positivity) hden1
      have hsum_q : ((C_ld + 1 + |Real.eulerMascheroniConstant|) * |w.im| ^ (1 / 2 : ℝ)) / |w.im| ^ 2
          + |w.im| ^ (1 / 2 : ℝ) / |w.im| ^ 2
          = (C_ld + 2 + |Real.eulerMascheroniConstant|) * (|w.im| ^ (1 / 2 : ℝ) / |w.im| ^ 2) := by
        ring
      linarith
    have hrpow_id : |w.im| ^ (1 / 2 : ℝ) / |w.im| ^ 2 = |w.im| ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_sub ht_pos]
      congr 1; norm_num
    have h1_add : |w.im| ^ (-(3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by
      have h2t : (1 + |w.im|) / 2 ≤ |w.im| := by linarith
      have hmon := Real.rpow_le_rpow_of_nonpos (by positivity) h2t (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
      rw [Real.div_rpow (by positivity) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at hmon
      linarith
    rw [hrpow_id] at hdiv_le
    calc ‖(-deriv riemannZeta w / riemannZeta w + 1 + (Real.eulerMascheroniConstant : ℂ))
          / (w * (w - 1)) - 1 / (w - 1) ^ 2‖
        ≤ (C_ld + 2 + |Real.eulerMascheroniConstant|)
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |w.im|) ^ (-(3 / 2 : ℝ))) :=
          hdiv_le.trans (mul_le_mul_of_nonneg_left h1_add (by positivity))
      _ = C_hi * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by simp only [C_hi]; ring
      _ ≤ (C_lo + C_hi) * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by
          gcongr; simp only [C_lo]; linarith [show (0 : ℝ) ≤ K₀' * (5 : ℝ) ^ (3 / 2 : ℝ) by positivity]
  · have hwK : w ∈ Kbox := ⟨hw_lo, hw_hi, him.le⟩
    have h1 : ‖H_zeta w‖ ≤ K₀' := (hK₀ ⟨w, hwK, rfl⟩).trans (le_max_left _ _)
    have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ (3 / 2 : ℝ) * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by
      have hle5 : 1 + |w.im| ≤ 5 := by linarith
      have hmon := Real.rpow_le_rpow_of_nonpos (by positivity) hle5 (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
      have hprod : (5 : ℝ) ^ (3 / 2 : ℝ) * (5 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num), show (3 / 2 : ℝ) + -(3 / 2) = 0 by ring, Real.rpow_zero]
      have := mul_le_mul_of_nonneg_left hmon (show 0 ≤ (5 : ℝ) ^ (3 / 2 : ℝ) by positivity)
      rwa [hprod] at this
    calc ‖H_zeta w‖ ≤ K₀' * 1 := by linarith
      _ ≤ K₀' * ((5 : ℝ) ^ (3 / 2 : ℝ) * (1 + |w.im|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (le_max_right _ _)
      _ = C_lo * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by simp only [C_lo]; ring
      _ ≤ (C_lo + C_hi) * (1 + |w.im|) ^ (-(3 / 2 : ℝ)) := by
          gcongr; simp only [C_hi]; linarith [show (0 : ℝ) ≤ C_hi by positivity]

/-- **Cota uniforme de `G_vonMangoldt` bajo `SinCerosDerecha θ`:**
si `1/2 ≤ θ < 1` y `ζ` no tiene ceros en `Re s > θ`, entonces para todo `σ₀ ∈ (θ, 1)` existe `C ≥ 0`
tal que `|G_vonMangoldt y| ≤ C y^{σ₀}` para todo `y ≥ 1`. -/
theorem cota_G_vonMangoldt_de_sin_ceros {θ σ₀ : ℝ} (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₀)
    (hσ1 : σ₀ < 1) (hZ : SinCerosDerecha θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |G_vonMangoldt y| ≤ C * y ^ σ₀ := by
  obtain ⟨M_H, hMH0, hMH⟩ := cota_banda_H_zeta hθ hθσ hσ1 hZ
  have hint_norm : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set I_H : ℝ := ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ))
  have hIH0 : 0 ≤ I_H := integral_nonneg fun _ => by positivity
  -- Convergencia de Mellin e integrabilidad vertical de `φ_G` en `σ = 3`.
  set C₀ : ℝ := 4 + |Real.eulerMascheroniConstant|
  have hconv3 : MellinConvergent φ_G 3 := by
    apply mellinConvergent_of_isBigO_rpow (a := 4) (b := 2)
    · exact continuousOn_φ_G.locallyIntegrableOn measurableSet_Ioi
    · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hnot : ¬ t < 1 := not_lt.mpr ht
      simp [φ_G, hnot]
    · norm_num
    · rw [Asymptotics.isBigO_iff]
      refine ⟨C₀ + |1 + Real.eulerMascheroniConstant|, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := ht.2
      have hinv1 : 1 ≤ 1 / t := (one_le_div ht0).mpr ht1.le
      have hG_bd : |G_vonMangoldt (1 / t)| ≤ C₀ * (1 / t) ^ 2 := abs_G_vonMangoldt_le hinv1
      have h1_sq : 1 ≤ (1 / t) ^ 2 := by nlinarith
      have hsub_abs : |G_vonMangoldt (1 / t) - (1 + Real.eulerMascheroniConstant)|
          ≤ |G_vonMangoldt (1 / t)| + |1 + Real.eulerMascheroniConstant| := by
        simpa [Real.norm_eq_abs] using
          norm_sub_le (G_vonMangoldt (1 / t)) (1 + Real.eulerMascheroniConstant)
      have hpow_inv : t ^ (-(2 : ℝ)) = (1 / t) ^ 2 := by
        rw [Real.rpow_neg ht0.le, Real.rpow_two]
        field_simp
      rw [φ_G, if_pos ht1, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), hpow_inv]
      nlinarith [abs_nonneg (1 + Real.eulerMascheroniConstant)]
    · norm_num
  have hline3 : ∀ t : ℝ, mellin φ_G (((3 : ℝ) : ℂ) + t * I) = H_zeta (((3 : ℝ) : ℂ) + t * I) :=
    fun t => mellin_φ_G (by simp; norm_num)
  have hcont_H_line : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 3 → Continuous (fun t : ℝ => H_zeta ((σ : ℂ) + t * I)) := by
    intro σ hlo _
    refine (differentiableOn_H_zeta (by linarith) hZ).continuousOn.comp_continuous (by fun_prop) fun t => ?_
    show θ < ((σ : ℂ) + t * I).re; simp; linarith
  have hvert3 : VerticalIntegrable (mellin φ_G) 3 := by
    unfold VerticalIntegrable
    have hfun_eq : (fun t : ℝ => mellin φ_G (((3 : ℝ) : ℂ) + t * I))
        = (fun t : ℝ => H_zeta (((3 : ℝ) : ℂ) + t * I)) :=
      funext hline3
    rw [hfun_eq]
    refine (hint_norm.const_mul M_H).mono' (hcont_H_line 3 (by linarith) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := hMH (((3 : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp)
    simpa [Real.norm_eq_abs] using hb
  set C_fin : ℝ := |1 + Real.eulerMascheroniConstant| + M_H * I_H / (2 * Real.pi)
  refine ⟨C_fin, by simp only [C_fin]; positivity, fun y hy => ?_⟩
  have hy_pos : 0 < y := lt_of_lt_of_le one_pos hy
  set u : ℝ := 1 / y
  have hu_pos : 0 < u := one_div_pos.mpr hy_pos
  have hinv_eq := mellinInv_mellin_eq 3 φ_G hu_pos hconv3 hvert3
    (continuousOn_φ_G.continuousAt (isOpen_Ioi.mem_nhds hu_pos))
  rw [φ_G_inv_of_ge_one hy] at hinv_eq
  unfold mellinInv at hinv_eq
  have hint3_mellin : (∫ t : ℝ, (u : ℂ) ^ (-(((3 : ℝ) : ℂ) + t * I)) • mellin φ_G (((3 : ℝ) : ℂ) + t * I))
      = ∫ t : ℝ, (u : ℂ) ^ (-(((3 : ℝ) : ℂ) + t * I)) • H_zeta (((3 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hline3 t]
  rw [hint3_mellin] at hinv_eq
  -- Identidad `(1 / y)^{−w} = y^w` para `y > 0`.
  have hu_cpow : ∀ w : ℂ, (u : ℂ) ^ (-w) = (y : ℂ) ^ w := fun w => by
    have hy_ne : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy_pos.ne'
    have hu_ne : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hu_ne, Complex.cpow_def_of_ne_zero hy_ne,
      ← Complex.ofReal_log hu_pos.le, ← Complex.ofReal_log hy_pos.le]
    congr 1
    simp only [u, one_div, Real.log_inv]
    push_cast; ring
  -- Desplazamiento de contorno de `f_y w = y^w H_ζ(w)` entre `σ₀` y `3`.
  let f_y : ℂ → ℂ := fun w => (y : ℂ) ^ w * H_zeta w
  have hf_diff : DifferentiableOn ℂ f_y {w | σ₀ ≤ w.re ∧ w.re ≤ 3} := by
    intro w hw
    have hw_θ : θ < w.re := lt_of_lt_of_le hθσ hw.1
    exact ((DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (ofReal_ne_zero.mpr hy_pos.ne'))).mul
      ((differentiableOn_H_zeta (by linarith) hZ).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hw_θ))).differentiableWithinAt
  have hf_line : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 3 → Integrable (fun t : ℝ => f_y ((σ : ℂ) + t * I)) := by
    intro σ hlo hhi
    have hcont : Continuous (fun t : ℝ => f_y ((σ : ℂ) + t * I)) :=
      (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hy_pos.ne'))).mul
        (hcont_H_line σ hlo hhi)
    refine (hint_norm.const_mul (y ^ σ * M_H)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := hMH ((σ : ℂ) + t * I) (by simp; exact hlo) (by simp; exact hhi)
    dsimp only [f_y]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [him] at hb
    rw [hre, Real.norm_eq_abs]
    calc y ^ σ * ‖H_zeta ((σ : ℂ) + t * I)‖
        ≤ y ^ σ * (M_H * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy_pos.le _)
      _ = y ^ σ * M_H * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by ring
  have hf_horiz : ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, σ₀ ≤ x → x ≤ 3 →
      ‖f_y (x + T * I)‖ ≤ (y ^ (3 : ℝ) * M_H) / T ∧
        ‖f_y (x + ((-T : ℝ) : ℂ) * I)‖ ≤ (y ^ (3 : ℝ) * M_H) / T := by
    intro T hT x hx1 hx2
    have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
    have haux : ∀ w : ℂ, w.re = x → |w.im| = T → ‖f_y w‖ ≤ (y ^ (3 : ℝ) * M_H) / T := by
      intro w hwre hwim
      have hb := hMH w (by linarith) (by linarith)
      rw [hwim] at hb
      dsimp only [f_y]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy_pos, hwre]
      have hy_x : y ^ x ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy hx2
      have hT_rpow : (1 + T) ^ (-(3 / 2 : ℝ)) ≤ 1 / T := by
        have h1 : T ^ (-(1 : ℝ)) ≤ 1 / T := by rw [Real.rpow_neg_one, one_div]
        have h2 : (1 + T) ^ (-(3 / 2 : ℝ)) ≤ (1 + T) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        have h3 : (1 + T) ^ (-(1 : ℝ)) ≤ T ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hT0 (by linarith) (by norm_num)
        exact h2.trans (h3.trans h1)
      calc y ^ x * ‖H_zeta w‖
          ≤ y ^ (3 : ℝ) * (M_H * (1 / T)) :=
            mul_le_mul hy_x (hb.trans (mul_le_mul_of_nonneg_left hT_rpow hMH0))
              (norm_nonneg _) (Real.rpow_nonneg hy_pos.le _)
        _ = (y ^ (3 : ℝ) * M_H) / T := by ring
    exact ⟨haux _ (by simp) (by simp [abs_of_pos hT0]),
      haux _ (by simp) (by simp [abs_of_pos hT0])⟩
  have hshift := integral_vertical_eq (by linarith : σ₀ ≤ 3) hf_diff
    (hf_line σ₀ le_rfl (by linarith)) (hf_line 3 (by linarith) le_rfl) hf_horiz
  have hint3_eq : (1 / (2 * Real.pi)) • ∫ t : ℝ, f_y (((3 : ℝ) : ℂ) + t * I)
      = ((G_vonMangoldt y - (1 + Real.eulerMascheroniConstant) : ℝ) : ℂ) := by
    rw [← hinv_eq]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [f_y]
    rw [← hu_cpow, smul_eq_mul]
  rw [← hshift] at hint3_eq
  -- Acotación de la norma en `Re w = σ₀`.
  have hnorm_σ₀ : ‖∫ t : ℝ, f_y ((σ₀ : ℂ) + t * I)‖ ≤ y ^ σ₀ * M_H * I_H := by
    rw [show I_H = ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) from rfl, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint_norm.const_mul (y ^ σ₀ * M_H))
      (Eventually.of_forall fun t => ?_)
    have hb := hMH ((σ₀ : ℂ) + t * I) (by simp) (by simp; linarith)
    dsimp only [f_y]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    have him : ((σ₀ : ℂ) + t * I).im = t := by simp
    rw [him] at hb
    rw [hre, Real.norm_eq_abs]
    calc y ^ σ₀ * ‖H_zeta ((σ₀ : ℂ) + t * I)‖
        ≤ y ^ σ₀ * (M_H * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy_pos.le _)
      _ = y ^ σ₀ * M_H * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by ring
  have hnorm_diff : |G_vonMangoldt y - (1 + Real.eulerMascheroniConstant)|
      ≤ (M_H * I_H / (2 * Real.pi)) * y ^ σ₀ := by
    have h1 := congrArg norm hint3_eq
    rw [Complex.norm_real, Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg (by positivity)] at h1
    rw [← h1]
    calc (1 / (2 * Real.pi)) * ‖∫ t : ℝ, f_y ((σ₀ : ℂ) + t * I)‖
        ≤ (1 / (2 * Real.pi)) * (y ^ σ₀ * M_H * I_H) :=
          mul_le_mul_of_nonneg_left hnorm_σ₀ (by positivity)
      _ = (M_H * I_H / (2 * Real.pi)) * y ^ σ₀ := by ring
  have hy_σ₀ : 1 ≤ y ^ σ₀ := Real.one_le_rpow hy (by linarith)
  have htri_G := abs_sub_abs_le_abs_sub (G_vonMangoldt y) (1 + Real.eulerMascheroniConstant)
  simp only [C_fin]
  nlinarith [abs_nonneg (1 + Real.eulerMascheroniConstant)]

/-! ### Equivalencia completa `RH ↔ (V)` -/

/-- Bajo `RiemannHypothesis`, para cada `1/2 < θ < 1` existen ventanas arbitrariamente lejanas
`[Y, Y^{3/2}]` donde `G_vonMangoldt y ≤ y^θ` (de hecho, vale para todo `y` suficientemente grande). -/
theorem ventana_vonMangoldt_de_rh (hRH : RiemannHypothesis) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)), G_vonMangoldt y ≤ y ^ θ := by
  intro θ hθ12 hθ1 Y₀
  have hZ : SinCerosDerecha (1 / 2) := sinCerosDerecha_half_iff_rh.mpr hRH
  set σ₀ : ℝ := (1 / 2 + θ) / 2
  have hσ_gt : 1 / 2 < σ₀ := by simp only [σ₀]; linarith
  have hσ_lt : σ₀ < θ := by simp only [σ₀]; linarith
  obtain ⟨C, hC0, hC⟩ := cota_G_vonMangoldt_de_sin_ceros le_rfl hσ_gt (lt_trans hσ_lt hθ1) hZ
  set d : ℝ := θ - σ₀
  have hd : 0 < d := sub_pos.mpr hσ_lt
  set Y : ℝ := max (max Y₀ 1) ((C + 1) ^ (1 / d))
  have hYY₀ : Y₀ ≤ Y := ((le_max_left _ _).trans (le_max_left _ _))
  have hY1 : 1 ≤ Y := ((le_max_right _ _).trans (le_max_left _ _))
  have hYC : (C + 1) ^ (1 / d) ≤ Y := le_max_right _ _
  refine ⟨Y, hYY₀, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans hY1 hy.1
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hC_yd : C ≤ y ^ d := by
    have h1 := Real.rpow_le_rpow (by positivity) (hYC.trans hy.1) hd.le
    rw [← Real.rpow_mul (by positivity), show (1 / d) * d = 1 by field_simp, Real.rpow_one] at h1
    linarith
  calc G_vonMangoldt y ≤ |G_vonMangoldt y| := le_abs_self _
    _ ≤ C * y ^ σ₀ := hC y hy1
    _ ≤ y ^ d * y ^ σ₀ := mul_le_mul_of_nonneg_right hC_yd (Real.rpow_nonneg hy0.le _)
    _ = y ^ θ := by rw [← Real.rpow_add hy0]; congr 1; simp only [d]; ring

/-- **Equivalencia bilateral completa `RH ↔ (V)` en conductor 1:**
`RiemannHypothesis` equivale a la cota unilateral en ventanas `G_vonMangoldt y ≤ y^θ` en `[Y, Y^{3/2}]`. -/
theorem rh_iff_ventana_vonMangoldt :
    RiemannHypothesis ↔
      ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
        Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)), G_vonMangoldt y ≤ y ^ θ :=
  ⟨ventana_vonMangoldt_de_rh, rh_de_ventana_vonMangoldt⟩

/-! ### Desigualdad complementaria `γ_E x − A_primos x ≤ G(x) + O(√x (log x)²)` y `RH ↔ S_AMate` -/

theorem sum_log_Icc_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  have hIco : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco]
  refine Nat.le_induction ?_ ?_ N hN
  · simp
  · intro n hn ih
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)
    rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hn_pos.le
    have hsimp : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by field_simp; ring
    rw [hsimp] at hmul
    push_cast at ih ⊢
    nlinarith

/-- Cota superior elemental del déficit sobre primos grandes en función de `G_vonMangoldt`:
para todo `x ≥ 2`,
`γ_E x − A_primos x ≤ G_vonMangoldt x + √x log x + √x (log x)² / log 2 + log x + 1`. -/
theorem deficit_primos_le_G_vonMangoldt {x : ℝ} (hx : 2 ≤ x) :
    Real.eulerMascheroniConstant * x - A_primos x
      ≤ G_vonMangoldt x + Real.sqrt x * Real.log x
        + Real.sqrt x * (Real.log x) ^ 2 / Real.log 2 + Real.log x + 1 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN_le_x : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hx_lt_N1 : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  -- Identidad exacta de `rampaVonMangoldt x`.
  have hramp_eq : rampaVonMangoldt x
      = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ)
        - ∑ n ∈ Finset.Icc 1 N, Λ n * (1 - Int.fract (x / (n : ℝ))) := by
    unfold rampaVonMangoldt
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        Λ n * (x / (n : ℝ) - 1)
          = Λ n * ((N / n : ℕ) : ℝ) - Λ n * (1 - Int.fract (x / (n : ℝ))) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hfl := cast_natFloor_eq_sub_fract (div_nonneg hx0.le hn_pos.le)
      rw [natFloor_div_natCast hx0.le n] at hfl
      change Λ n * (x / (n : ℝ) - 1)
        = Λ n * ((⌊x⌋₊ / n : ℕ) : ℝ) - Λ n * (1 - Int.fract (x / (n : ℝ)))
      rw [hfl]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_vonMangoldt_div_floor N]
  -- Cota inferior `∑_{m=1}^N log m ≥ x log x − x − log x − 1`.
  have hsum_log_ge : x * Real.log x - x - Real.log x - 1
      ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
    have h1 := sum_log_Icc_ge hN1
    have h2 := Real.log_le_sub_one_of_pos (div_pos hx0 hN_pos)
    rw [Real.log_div hx0.ne' hN_pos.ne'] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hN_pos.le
    have hsimp : (N : ℝ) * (x / (N : ℝ) - 1) = x - (N : ℝ) := by field_simp
    rw [hsimp] at h3
    have h4 : (x - (N : ℝ)) * Real.log x ≤ 1 * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlogx_nn
    nlinarith
  -- Descomposición de `∑_{n=1}^N Λ(n)(1 − {x/n})` en `A_primos x` + resto `≤ √x log x + √x (log x)² / log 2`.
  let P_set : Finset ℕ := (Finset.Icc 1 N).filter (fun p : ℕ => Nat.Prime p ∧ Real.sqrt x < (p : ℝ))
  let R_set : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => ¬ (Nat.Prime n ∧ Real.sqrt x < (n : ℝ)))
  have hsplit_P : ∑ n ∈ Finset.Icc 1 N, Λ n * (1 - Int.fract (x / (n : ℝ)))
      = A_primos x + ∑ n ∈ R_set, Λ n * (1 - Int.fract (x / (n : ℝ))) := by
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
      (fun n : ℕ => Nat.Prime n ∧ Real.sqrt x < (n : ℝ))
      (fun n => Λ n * (1 - Int.fract (x / (n : ℝ))))).symm
    rw [hpart]
    congr 1
    unfold A_primos
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2.1]
  -- Acotamos `∑_{n ∈ R_set} Λ(n)(1 − {x/n}) ≤ ∑_{n ∈ R_set} Λ(n)` y separamos `n ≤ ⌊√x⌋₊` de potencias `p^k` (`k ≥ 2`).
  have hR_term : ∀ n ∈ R_set, Λ n * (1 - Int.fract (x / (n : ℝ))) ≤ Λ n := fun n _ => by
    have h1 : 1 - Int.fract (x / (n : ℝ)) ≤ 1 := by linarith [Int.fract_nonneg (x / (n : ℝ))]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg h1
  let R₁ : Finset ℕ := R_set.filter (fun n : ℕ => n ≤ ⌊Real.sqrt x⌋₊)
  let R₂ : Finset ℕ := R_set.filter (fun n : ℕ => ¬ (n ≤ ⌊Real.sqrt x⌋₊) ∧ IsPrimePow n)
  have hR_split : ∑ n ∈ R_set, Λ n = (∑ n ∈ R₁, Λ n) + ∑ n ∈ R₂, Λ n := by
    have hsecond : ∑ n ∈ R_set.filter (fun n : ℕ => ¬ n ≤ ⌊Real.sqrt x⌋₊), Λ n = ∑ n ∈ R₂, Λ n := by
      have hzero_not_pp : ∀ n ∈ R_set.filter (fun n : ℕ => ¬ n ≤ ⌊Real.sqrt x⌋₊),
          ¬ IsPrimePow n → Λ n = 0 := fun n _ hnp => by
        rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnp]
      rw [← Finset.sum_filter_add_sum_filter_not
        (R_set.filter (fun n : ℕ => ¬ n ≤ ⌊Real.sqrt x⌋₊)) IsPrimePow]
      have hvan : ∑ n ∈ (R_set.filter (fun n : ℕ => ¬ n ≤ ⌊Real.sqrt x⌋₊)).filter (fun n => ¬ IsPrimePow n),
          Λ n = 0 := Finset.sum_eq_zero fun n hn =>
        hzero_not_pp n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
      have hR2_eq : (R_set.filter (fun n : ℕ => ¬ n ≤ ⌊Real.sqrt x⌋₊)).filter IsPrimePow = R₂ := by
        ext n; simp only [R₂, Finset.mem_filter, and_assoc]
      rw [hvan, add_zero, hR2_eq]
    rw [← Finset.sum_filter_add_sum_filter_not R_set (fun n : ℕ => n ≤ ⌊Real.sqrt x⌋₊), hsecond]
  have hΛ_le_logx : ∀ n ∈ Finset.Icc 1 N, Λ n ≤ Real.log x := fun n hn => by
    rw [Finset.mem_Icc] at hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hn_pos ((Nat.cast_le.mpr hn.2).trans hN_le_x))
  have hR₁_le : ∑ n ∈ R₁, Λ n ≤ Real.sqrt x * Real.log x := by
    have hsub : R₁ ⊆ Finset.Icc 1 ⌊Real.sqrt x⌋₊ := fun n hn => by
      have hnR := (Finset.mem_filter.mp hn).1
      have hn_le := (Finset.mem_filter.mp hn).2
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hnR).1).1, hn_le⟩
    calc ∑ n ∈ R₁, Λ n
        ≤ ∑ n ∈ R₁, Real.log x := Finset.sum_le_sum fun n hn =>
            hΛ_le_logx n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      _ = (R₁.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Finset.Icc 1 ⌊Real.sqrt x⌋₊).card : ℝ) * Real.log x :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hlogx_nn
      _ ≤ Real.sqrt x * Real.log x := by
          rw [Nat.card_Icc]
          have hcard : ((⌊Real.sqrt x⌋₊ + 1 - 1 : ℕ) : ℝ) ≤ Real.sqrt x := by
            simp only [Nat.add_sub_cancel]
            exact Nat.floor_le (Real.sqrt_nonneg x)
          exact mul_le_mul_of_nonneg_right hcard hlogx_nn
  -- `R₂` se inyecta en `Icc 1 ⌊√x⌋₊ ×ˢ Icc 1 ⌊log x / log 2⌋₊` mediante `(p, k) ↦ p^k` (`k ≥ 2`).
  have hR₂_le : ∑ n ∈ R₂, Λ n ≤ Real.sqrt x * (Real.log x) ^ 2 / Real.log 2 := by
    let G_pk : Finset (ℕ × ℕ) :=
      Finset.Icc 1 ⌊Real.sqrt x⌋₊ ×ˢ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊
    have hsub_img : R₂ ⊆ G_pk.image (fun pk => pk.1 ^ pk.2) := by
      intro n hn
      have hn_R : n ∈ R_set := (Finset.mem_filter.mp hn).1
      have hn_gt : ¬ n ≤ ⌊Real.sqrt x⌋₊ := (Finset.mem_filter.mp hn).2.1
      have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2.2
      have hn_Icc : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn_R).1
      have hn_notP : ¬ (Nat.Prime n ∧ Real.sqrt x < (n : ℝ)) := (Finset.mem_filter.mp hn_R).2
      have hsqrt_lt : Real.sqrt x < (n : ℝ) := by
        have h1 : ⌊Real.sqrt x⌋₊ + 1 ≤ n := by omega
        exact (Nat.lt_floor_add_one (Real.sqrt x)).trans_le (by exact_mod_cast h1)
      have hn_not_prime : ¬ Nat.Prime n := fun hp => hn_notP ⟨hp, hsqrt_lt⟩
      rcases hn_pp with ⟨p, k, hp_pr, hk_pos, hp_eq⟩
      have hp : Nat.Prime p := Nat.prime_iff.mpr hp_pr
      have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk1 : k = 1 := by omega
        subst hk1; simp only [pow_one] at hp_eq; exact hn_not_prime (hp_eq ▸ hp)
      have hp_le_sq : p ≤ ⌊Real.sqrt x⌋₊ := by
        apply Nat.le_floor
        apply Real.le_sqrt_of_sq_le
        have hpk : p ^ 2 ≤ n := hp_eq ▸ Nat.pow_le_pow_right hp.pos hk2
        exact (show ((p : ℝ) ^ 2) ≤ (n : ℝ) by exact_mod_cast hpk).trans
          ((Nat.cast_le.mpr (Finset.mem_Icc.mp hn_Icc).2).trans hN_le_x)
      have hk_le_log : k ≤ ⌊Real.log x / Real.log 2⌋₊ := by
        apply Nat.le_floor
        rw [le_div_iff₀ hl2]
        have h2k : (2 : ℝ) ^ k ≤ x := by
          have h2n : 2 ^ k ≤ n := hp_eq ▸ Nat.pow_le_pow_left hp.two_le k
          exact (show ((2 : ℝ) ^ k) ≤ (n : ℝ) by exact_mod_cast h2n).trans
            ((Nat.cast_le.mpr (Finset.mem_Icc.mp hn_Icc).2).trans hN_le_x)
        have hlog_2k := Real.log_le_log (by positivity) h2k
        rwa [Real.log_pow] at hlog_2k
      exact Finset.mem_image.mpr ⟨(p, k),
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hp_le_sq⟩,
          Finset.mem_Icc.mpr ⟨by omega, hk_le_log⟩⟩, hp_eq⟩
    have hcard_R₂ : (R₂.card : ℝ) ≤ Real.sqrt x * (Real.log x / Real.log 2) := by
      have hc1 : R₂.card ≤ G_pk.card :=
        (Finset.card_le_card hsub_img).trans Finset.card_image_le
      have hc2 : G_pk.card = ⌊Real.sqrt x⌋₊ * ⌊Real.log x / Real.log 2⌋₊ := by
        simp [G_pk]
      calc (R₂.card : ℝ) ≤ (G_pk.card : ℝ) := by exact_mod_cast hc1
        _ = (⌊Real.sqrt x⌋₊ : ℝ) * (⌊Real.log x / Real.log 2⌋₊ : ℝ) := by
            rw [hc2]; push_cast; rfl
        _ ≤ Real.sqrt x * (Real.log x / Real.log 2) :=
            mul_le_mul (Nat.floor_le (Real.sqrt_nonneg x))
              (Nat.floor_le (div_nonneg hlogx_nn hl2.le))
              (Nat.cast_nonneg _) (Real.sqrt_nonneg x)
    calc ∑ n ∈ R₂, Λ n
        ≤ ∑ n ∈ R₂, Real.log x := Finset.sum_le_sum fun n hn =>
            hΛ_le_logx n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      _ = (R₂.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Real.sqrt x * (Real.log x / Real.log 2)) * Real.log x :=
          mul_le_mul_of_nonneg_right hcard_R₂ hlogx_nn
      _ = Real.sqrt x * (Real.log x) ^ 2 / Real.log 2 := by ring
  have hR_sum_le : ∑ n ∈ R_set, Λ n * (1 - Int.fract (x / (n : ℝ)))
      ≤ Real.sqrt x * Real.log x + Real.sqrt x * (Real.log x) ^ 2 / Real.log 2 := by
    calc ∑ n ∈ R_set, Λ n * (1 - Int.fract (x / (n : ℝ)))
        ≤ ∑ n ∈ R_set, Λ n := Finset.sum_le_sum hR_term
      _ = (∑ n ∈ R₁, Λ n) + ∑ n ∈ R₂, Λ n := hR_split
      _ ≤ Real.sqrt x * Real.log x + Real.sqrt x * (Real.log x) ^ 2 / Real.log 2 :=
          add_le_add hR₁_le hR₂_le
  unfold G_vonMangoldt
  linarith

/-- Bajo `RiemannHypothesis`, para todo `η > 0` existe un umbral `Y₁` a partir del cual
`S_AMate Y ≤ Y^η` en **todas** las escalas `Y ≥ Y₁`. -/
theorem deficit_primos_uniforme_de_rh (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0 < η → ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → S_AMate Y ≤ Y ^ η := by
  intro η hη
  have hZ : SinCerosDerecha (1 / 2) := sinCerosDerecha_half_iff_rh.mpr hRH
  set u : ℝ := min (η / 6) (1 / 4)
  have hu_pos : 0 < u := lt_min (by positivity) (by norm_num)
  have hu_lt : 1 / 2 + u < 1 := by simp only [u]; linarith [min_le_right (η / 6) (1 / 4)]
  have h6u : 3 * u / 2 ≤ η / 4 := by
    have : u ≤ η / 6 := min_le_left _ _
    linarith
  obtain ⟨CG, hCG0, hCG⟩ :=
    cota_G_vonMangoldt_de_sin_ceros le_rfl (by linarith : (1 / 2 : ℝ) < 1 / 2 + u) hu_lt hZ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K_coef : ℝ := CG * (6 / η) + (10 + 16 / Real.log 2) * (6 / η) ^ 3 + 1
  have hK_pos : 0 < K_coef := by simp only [K_coef]; positivity
  set Y₁ : ℝ := max 16 (K_coef ^ (2 / η))
  refine ⟨Y₁, fun Y hYY₁ => ?_⟩
  have hY16 : 16 ≤ Y := (le_max_left _ _).trans hYY₁
  have hYK : K_coef ^ (2 / η) ≤ Y := (le_max_right _ _).trans hYY₁
  have hY_pos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  set N_top : ℕ := ⌊Y ^ (3 / 8 : ℝ)⌋₊
  unfold S_AMate
  have hterm_le : ∀ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
      max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ (CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2) * (1 / (m : ℝ)) := by
    intro m hm
    have hm_Icc := (Finset.mem_filter.mp hm).1
    have hm_Y := (Finset.mem_filter.mp hm).2.1
    have hm_Y32 := (Finset.mem_filter.mp hm).2.2
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_Icc).1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hm4_ge2 : (2 : ℝ) ≤ (m : ℝ) ^ 4 := le_trans (by linarith) hm_Y
    have hm4_ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := by linarith
    have hm4_pos : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
    have hlogY_ge1 : 1 ≤ Real.log Y := by
      have hexp1 : Real.exp 1 ≤ Y := Real.exp_one_lt_d9.le.trans (by linarith)
      have hl := Real.log_le_log (Real.exp_pos 1) hexp1
      rwa [Real.log_exp] at hl
    have hlog_m4 : Real.log ((m : ℝ) ^ 4) ≤ 2 * Real.log Y := by
      calc Real.log ((m : ℝ) ^ 4)
          ≤ Real.log (Y ^ (3 / 2 : ℝ)) := Real.log_le_log hm4_pos hm_Y32
        _ = (3 / 2 : ℝ) * Real.log Y := Real.log_rpow hY_pos (3 / 2 : ℝ)
        _ ≤ 2 * Real.log Y := by linarith
    have hlog_m4_nn : 0 ≤ Real.log ((m : ℝ) ^ 4) := Real.log_nonneg hm4_ge1
    have hsqrt_m4 : Real.sqrt ((m : ℝ) ^ 4) = (m : ℝ) ^ 2 := by
      rw [show (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hG_m4 : G_vonMangoldt ((m : ℝ) ^ 4) ≤ CG * Y ^ (3 * u / 2) * (m : ℝ) ^ 2 := by
      have h1 := (le_abs_self _).trans (hCG ((m : ℝ) ^ 4) hm4_ge1)
      have hrp : ((m : ℝ) ^ 4) ^ (1 / 2 + u) = (m : ℝ) ^ 2 * ((m : ℝ) ^ 4) ^ u := by
        rw [Real.rpow_add hm4_pos]
        have hhalf : ((m : ℝ) ^ 4) ^ (1 / 2 : ℝ) = (m : ℝ) ^ 2 := by
          rw [← Real.sqrt_eq_rpow, hsqrt_m4]
        rw [hhalf]
      have hu_Y : ((m : ℝ) ^ 4) ^ u ≤ Y ^ (3 * u / 2) := by
        calc ((m : ℝ) ^ 4) ^ u ≤ (Y ^ (3 / 2 : ℝ)) ^ u :=
              Real.rpow_le_rpow hm4_pos.le hm_Y32 hu_pos.le
          _ = Y ^ (3 * u / 2) := by rw [← Real.rpow_mul hY_pos.le]; congr 1; ring
      calc G_vonMangoldt ((m : ℝ) ^ 4)
          ≤ CG * ((m : ℝ) ^ 4) ^ (1 / 2 + u) := h1
        _ = CG * ((m : ℝ) ^ 2 * ((m : ℝ) ^ 4) ^ u) := by rw [hrp]
        _ ≤ CG * ((m : ℝ) ^ 2 * Y ^ (3 * u / 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hu_Y (by positivity)) hCG0
        _ = CG * Y ^ (3 * u / 2) * (m : ℝ) ^ 2 := by ring
    have hdef := deficit_primos_le_G_vonMangoldt hm4_ge2
    rw [hsqrt_m4] at hdef
    have hm2_ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith
    have hsq_log : (Real.log ((m : ℝ) ^ 4)) ^ 2 ≤ 4 * (Real.log Y) ^ 2 := by
      calc (Real.log ((m : ℝ) ^ 4)) ^ 2 ≤ (2 * Real.log Y) ^ 2 :=
            pow_le_pow_left₀ hlog_m4_nn hlog_m4 2
        _ = 4 * (Real.log Y) ^ 2 := by ring
    have hnum_bd : max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0
        ≤ (CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2) * (m : ℝ) ^ 2 := by
      refine max_le ?_ (by positivity)
      have hlogY_le_sq : Real.log Y ≤ (Real.log Y) ^ 2 := by nlinarith [hlogY_ge1]
      have hterm1 : (m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 4) ≤ 2 * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by
        have h2 : Real.log ((m : ℝ) ^ 4) ≤ 2 * (Real.log Y) ^ 2 := by linarith
        calc (m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 4)
            ≤ (m : ℝ) ^ 2 * (2 * (Real.log Y) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 2 * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by ring
      have hterm2 : (m : ℝ) ^ 2 * (Real.log ((m : ℝ) ^ 4)) ^ 2 / Real.log 2
          ≤ (4 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by
        rw [mul_div_assoc]
        have := div_le_div_of_nonneg_right hsq_log hl2.le
        have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ (m : ℝ) ^ 2 by positivity)
        linarith [show (m : ℝ) ^ 2 * (4 * (Real.log Y) ^ 2 / Real.log 2)
          = (4 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 by ring]
      have hterm3 : Real.log ((m : ℝ) ^ 4) + 1 ≤ 3 * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by
        have h1_sq : (1 : ℝ) ≤ (Real.log Y) ^ 2 := by nlinarith [hlogY_ge1]
        nlinarith [hm2_ge1]
      have hdiv_pos : 0 ≤ (Real.log Y) ^ 2 * (m : ℝ) ^ 2 / Real.log 2 :=
        div_nonneg (mul_nonneg (sq_nonneg (Real.log Y)) (by positivity)) hl2.le
      have hcoef2 : (4 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2
          ≤ (16 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by
        have h4 : (4 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2
            = 4 * ((Real.log Y) ^ 2 * (m : ℝ) ^ 2 / Real.log 2) := by ring
        have h16 : (16 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2
            = 16 * ((Real.log Y) ^ 2 * (m : ℝ) ^ 2 / Real.log 2) := by ring
        linarith
      have hexp_rhs : (CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2) * (m : ℝ) ^ 2
          = CG * Y ^ (3 * u / 2) * (m : ℝ) ^ 2
            + 10 * ((Real.log Y) ^ 2 * (m : ℝ) ^ 2)
            + (16 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by ring
      have hpos_prod : 0 ≤ (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by positivity
      linarith
    calc max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ ((CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2) * (m : ℝ) ^ 2)
            / (m : ℝ) ^ 3 := div_le_div_of_nonneg_right hnum_bd (by positivity)
      _ = (CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2) * (1 / (m : ℝ)) := by
          have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
          field_simp
  set B_fac : ℝ := CG * Y ^ (3 * u / 2) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2
  have hB_nn : 0 ≤ B_fac := by simp only [B_fac]; positivity
  have hlogY_nn : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hsum_le : ∑ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
      max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
      ≤ B_fac * Real.log Y := by
    have hN1 : 1 ≤ N_top :=
      Nat.le_floor (by exact_mod_cast Real.one_le_rpow hY1 (by norm_num : (0 : ℝ) ≤ 3 / 8))
    have hharm : ∑ m ∈ Finset.Icc 1 N_top, (1 / (m : ℝ)) ≤ Real.log Y := by
      have h1 := sum_inv_Icc_le hN1
      have hN_pos : (0 : ℝ) < N_top := by exact_mod_cast hN1
      have h2 : Real.log (N_top : ℝ) ≤ (3 / 8 : ℝ) * Real.log Y := by
        calc Real.log (N_top : ℝ)
            ≤ Real.log (Y ^ (3 / 8 : ℝ)) :=
              Real.log_le_log hN_pos (Nat.floor_le (by positivity))
          _ = (3 / 8 : ℝ) * Real.log Y := Real.log_rpow hY_pos (3 / 8 : ℝ)
      have hlogY_ge2 : 2 ≤ Real.log Y := by
        have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have hexp2 : Real.exp 2 ≤ Y := by
          have : Real.exp 2 ≤ 3 ^ 2 := by
            rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
            exact pow_le_pow_left₀ (Real.exp_pos 1).le h3 2
          exact this.trans (by linarith)
        have hl := Real.log_le_log (Real.exp_pos 2) hexp2
        rwa [Real.log_exp] at hl
      linarith
    calc ∑ m ∈ (Finset.Icc 1 N_top).filter
          (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
          max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ ∑ m ∈ (Finset.Icc 1 N_top).filter
          (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
          B_fac * (1 / (m : ℝ)) := Finset.sum_le_sum hterm_le
      _ ≤ ∑ m ∈ Finset.Icc 1 N_top, B_fac * (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = B_fac * ∑ m ∈ Finset.Icc 1 N_top, (1 / (m : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ B_fac * Real.log Y := mul_le_mul_of_nonneg_left hharm hB_nn
  have hlog_u : Real.log Y ≤ (6 / η) * Y ^ (η / 6) := by
    have h1 := Real.log_le_rpow_div hY_pos.le (show 0 < η / 6 by positivity)
    have heq : Y ^ (η / 6) / (η / 6) = (6 / η) * Y ^ (η / 6) := by field_simp
    linarith
  have hlog3 : (Real.log Y) ^ 3 ≤ (6 / η) ^ 3 * Y ^ (η / 2) := by
    calc (Real.log Y) ^ 3 ≤ ((6 / η) * Y ^ (η / 6)) ^ 3 :=
          pow_le_pow_left₀ hlogY_nn hlog_u 3
      _ = (6 / η) ^ 3 * (Y ^ (η / 6)) ^ 3 := mul_pow _ _ 3
      _ = (6 / η) ^ 3 * Y ^ (η / 2) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY_pos.le]
          congr 1; push_cast; ring
  have hY_term1 : Y ^ (3 * u / 2) * Real.log Y ≤ (6 / η) * Y ^ (η / 2) := by
    calc Y ^ (3 * u / 2) * Real.log Y
        ≤ Y ^ (3 * u / 2) * ((6 / η) * Y ^ (η / 6)) :=
          mul_le_mul_of_nonneg_left hlog_u (Real.rpow_nonneg hY_pos.le _)
      _ = (6 / η) * (Y ^ (3 * u / 2) * Y ^ (η / 6)) := by ring
      _ = (6 / η) * Y ^ (3 * u / 2 + η / 6) := by rw [← Real.rpow_add hY_pos]
      _ ≤ (6 / η) * Y ^ (η / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
            (by positivity)
  have hB_le_K : B_fac * Real.log Y ≤ K_coef * Y ^ (η / 2) := by
    have hexpand : B_fac * Real.log Y
        = CG * (Y ^ (3 * u / 2) * Real.log Y) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 3 := by
      simp only [B_fac]; ring
    rw [hexpand]
    have h1 := mul_le_mul_of_nonneg_left hY_term1 hCG0
    have h2 := mul_le_mul_of_nonneg_left hlog3 (show 0 ≤ 10 + 16 / Real.log 2 by positivity)
    have hY_nn : 0 ≤ Y ^ (η / 2) := Real.rpow_nonneg hY_pos.le _
    simp only [K_coef]
    nlinarith
  have hK_le_Y : K_coef ≤ Y ^ (η / 2) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hK_pos.le _) hYK (half_pos hη).le
    rw [← Real.rpow_mul hK_pos.le, show (2 / η) * (η / 2) = 1 by field_simp,
      Real.rpow_one] at h1
    exact h1
  calc ∑ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
        max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
      ≤ B_fac * Real.log Y := hsum_le
    _ ≤ K_coef * Y ^ (η / 2) := hB_le_K
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
        mul_le_mul_of_nonneg_right hK_le_Y (Real.rpow_nonneg hY_pos.le _)
    _ = Y ^ η := by rw [← Real.rpow_add hY_pos]; congr 1; ring

/-- Bajo `RiemannHypothesis`, para todo `η > 0` existen escalas arbitrariamente grandes `Y` con
`S_AMate Y ≤ Y^η`. -/
theorem deficit_primos_de_rh (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η := by
  intro η hη Y₀
  obtain ⟨Y₁, hY₁⟩ := deficit_primos_uniforme_de_rh hRH η hη
  exact ⟨max Y₀ Y₁, le_max_left _ _, hY₁ _ (le_max_right _ _)⟩

/-- **Equivalencia bilateral completa `RH ↔ S_AMate`:**
`RiemannHypothesis` equivale a que para cada `η > 0` existan escalas arbitrariamente grandes `Y`
donde la suma de déficits sobre primos grandes cumple `S_AMate Y ≤ Y^η`. -/
theorem rh_iff_deficit_primos :
    RiemannHypothesis ↔
      ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η :=
  ⟨deficit_primos_de_rh, rh_de_deficit_primos⟩

end AMate
