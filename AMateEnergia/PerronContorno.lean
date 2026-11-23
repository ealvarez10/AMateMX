import AMateEnergia.PerronZ
import AMateEnergia.Definiciones

/-!
# Fórmula de Perron suavizada y lema de Balazard–Saias

Segunda mitad del lema de Balazard–Saias (estado 45, §3). Con `N = n`, `h = √n` y
`a = Re s − 1/2 − δ/2`:

* `integral_vertical_eq`: Cauchy en rectángulos de altura `T → ∞` iguala las integrales sobre dos
  rectas verticales si los lados horizontales decaen como `1/T`.
* `contornoK`: `(Z(s+w) − Z(s)) pesoMellin(w)`, holomorfa en `w = 0` gracias a `dslope`.
* `horizontal_K`, `norm_pesoMellin_left`: cotas en los lados horizontales y en la recta
  `Re w = −a`, donde `‖pesoMellin‖ ≤ 3 N^{−a} N^{κ/2} (2/a)^{1+κ} (1+|y|)^{−1−κ}`.
* `smoothing_error`: el peso cambia la suma parcial en a lo sumo `n^{1/2 − Re s}`.
* `balazard_saias_Zinv`: con la inversión de Mellin del peso en `Re w = 2` y en `Re w = −a`, con
  `a = min (Re s − 1/2 − δ/2) (1/2)` (que da el término `Z(s)` sin calcular residuos),
  `‖∑_{d≤n} μ(d) d^{−s} − Z(s)‖ ≤ C n^{−δ/3} (1 + |t|)^η` bajo RH, para `n ≥ 1` y todo
  `Re s ≥ 1/2 + δ`, incluido `s = 1`.
* `balazard_saias_de`: el enunciado del estado 45, con `1/ζ(s)` y `s ≠ 1`.
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate

/-! ### Desplazamiento del contorno en una banda vertical -/

/-- Si `f` es holomorfa en la banda `α ≤ Re w ≤ β`, integrable en sus dos bordes y
`‖f(x ± iT)‖ ≤ D/T`, las integrales sobre las dos rectas coinciden. -/
theorem integral_vertical_eq {f : ℂ → ℂ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : DifferentiableOn ℂ f {w | α ≤ w.re ∧ w.re ≤ β})
    (hα : Integrable (fun y : ℝ => f (α + y * I))) (hβ : Integrable (fun y : ℝ => f (β + y * I)))
    {D : ℝ} (hD : ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, α ≤ x → x ≤ β →
      ‖f (x + T * I)‖ ≤ D / T ∧ ‖f (x + ((-T : ℝ) : ℂ) * I)‖ ≤ D / T) :
    ∫ y : ℝ, f (α + y * I) = ∫ y : ℝ, f (β + y * I) := by
  have key : ∀ n : ℕ, (∫ x in α..β, f (x + ((-(n : ℝ) : ℝ) : ℂ) * I)) - (∫ x in α..β, f (x + (n : ℝ) * I))
      + I • (∫ y in (-(n : ℝ))..n, f (β + y * I))
      - I • (∫ y in (-(n : ℝ))..n, f (α + y * I)) = 0 := by
    intro n
    apply integral_boundary_rect_eq_zero_of_differentiableOn f ⟨α, -n⟩ ⟨β, n⟩
    apply hf.mono
    intro w hw
    simp only [mem_reProdIm] at hw
    have h1 : w.re ∈ Set.uIcc α β := hw.1
    rw [Set.uIcc_of_le hαβ] at h1
    exact ⟨h1.1, h1.2⟩
  have hb1 : ∀ n : ℕ, 1 ≤ n → ‖∫ x in α..β, f (x + (n : ℝ) * I)‖ ≤ D / n * |β - α| := by
    intro n hn
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hαβ] at hx
    exact (hD n (by exact_mod_cast hn) x hx.1.le hx.2).1
  have hb2 : ∀ n : ℕ, 1 ≤ n → ‖∫ x in α..β, f (x + ((-(n : ℝ) : ℝ) : ℂ) * I)‖ ≤ D / n * |β - α| := by
    intro n hn
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hαβ] at hx
    exact (hD n (by exact_mod_cast hn) x hx.1.le hx.2).2
  have hlim0 : Tendsto (fun n : ℕ => D / n * |β - α|) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat D).mul_const |β - α|
  have h1 : Tendsto (fun n : ℕ => ∫ x in α..β, f (x + (n : ℝ) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.mpr ⟨1, hb1⟩) hlim0
  have h2 : Tendsto (fun n : ℕ => ∫ x in α..β, f (x + ((-(n : ℝ) : ℝ) : ℂ) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.mpr ⟨1, hb2⟩) hlim0
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have vβ := intervalIntegral_tendsto_integral hβ hneg tendsto_natCast_atTop_atTop
  have vα := intervalIntegral_tendsto_integral hα hneg tendsto_natCast_atTop_atTop
  have hlim := ((h2.sub h1).add (vβ.const_smul I)).sub (vα.const_smul I)
  have hlim' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
      (𝓝 (0 - 0 + I • (∫ y : ℝ, f (β + y * I)) - I • ∫ y : ℝ, f (α + y * I))) :=
    hlim.congr (fun n => key n)
  have heq := tendsto_nhds_unique hlim' tendsto_const_nhds
  simp only [sub_zero, zero_add, smul_eq_mul] at heq
  have : I * ((∫ y : ℝ, f (β + y * I)) - ∫ y : ℝ, f (α + y * I)) = 0 := by
    rw [mul_sub]
    exact heq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-! ### La función del contorno -/

/-- `G(w) = ((N+h)^{w+1} − N^{w+1})/(h (w+1))`, de modo que `pesoMellin w = G(w)/w`. -/
noncomputable def pesoG (N h : ℝ) (w : ℂ) : ℂ :=
  (((N + h : ℝ) : ℂ) ^ (w + 1) - ((N : ℝ) : ℂ) ^ (w + 1)) / ((h : ℂ) * (w + 1))

theorem pesoMellin_eq_div (N h : ℝ) (w : ℂ) : pesoMellin N h w = pesoG N h w / w := by
  unfold pesoMellin pesoG
  rw [div_div]
  ring_nf

/-- `K(w) = (Z(s+w) − Z(s))/w · G(w)`, holomorfa también en `w = 0`. -/
noncomputable def contornoK (N h : ℝ) (s : ℂ) (w : ℂ) : ℂ :=
  dslope (fun w => Zinv (s + w)) 0 w * pesoG N h w

theorem contornoK_eq {N h : ℝ} {s w : ℂ} (hw : w ≠ 0) :
    contornoK N h s w = Zinv (s + w) * pesoMellin N h w - Zinv s * pesoMellin N h w := by
  unfold contornoK
  rw [dslope_of_ne _ hw, slope_def_field, pesoMellin_eq_div, add_zero, sub_zero]
  field_simp

theorem differentiableOn_contornoK (hRH : RiemannHypothesis) {N h : ℝ} (hN : 0 < N)
    (hh : 0 < h) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableOn ℂ (contornoK N h s) {w | 1 / 2 < (s + w).re ∧ -1 < w.re} := by
  set U : Set ℂ := {w | 1 / 2 < (s + w).re ∧ -1 < w.re} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_re.comp (continuous_const.add continuous_id))).inter
      (isOpen_lt continuous_const continuous_re)
  have h0 : (0 : ℂ) ∈ U := ⟨by simpa using hs, by simp⟩
  have hZ : DifferentiableOn ℂ (fun w => Zinv (s + w)) U := by
    intro w hw
    have hd := (differentiableOn_Zinv hRH).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 / 2 < (s + w).re from hw.1))
    exact (hd.comp w ((differentiableAt_const s).add differentiableAt_id)).differentiableWithinAt
  have hdsl : DifferentiableOn ℂ (dslope (fun w => Zinv (s + w)) 0) U :=
    (differentiableOn_dslope (hUo.mem_nhds h0)).mpr hZ
  have hG : DifferentiableOn ℂ (pesoG N h) U := by
    intro w hw
    have hw1 : (h : ℂ) * (w + 1) ≠ 0 := by
      refine mul_ne_zero (ofReal_ne_zero.mpr hh.ne') ?_
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith [hw.2]
    unfold pesoG
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.div ?_ ?_ hw1)
    · exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr (by linarith)))).sub
        (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hN.ne')))
    · fun_prop
  exact hdsl.mul hG

/-! ### Cotas en rectas verticales -/

theorem norm_pesoMellin_line_le {N h : ℝ} (hN : 0 < N) (hh : 0 < h) {σ : ℝ} (hσ0 : σ ≠ 0)
    (hσ1 : σ ≠ -1) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      ‖pesoMellin N h ((σ : ℂ) + y * I)‖ ≤ K * (1 + |y|) ^ (-(2 : ℝ)) := by
  have hc₁ : 0 < min |σ| 1 / 2 := by
    have : 0 < |σ| := abs_pos.mpr hσ0
    positivity
  have hc₂ : 0 < min |σ + 1| 1 / 2 := by
    have : 0 < |σ + 1| := abs_pos.mpr (fun h0 => hσ1 (by linarith))
    positivity
  refine ⟨((N + h) ^ (σ + 1) + N ^ (σ + 1)) / (h * (min |σ| 1 / 2) * (min |σ + 1| 1 / 2)),
    by positivity, fun y => ?_⟩
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
    _ = ((N + h) ^ (σ + 1) + N ^ (σ + 1)) / (h * (min |σ| 1 / 2) * (min |σ + 1| 1 / 2))
        * (1 + |y|) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hy.le, Real.rpow_two]
        field_simp

theorem one_add_abs_add_rpow_le (t y : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (1 + |t + y|) ^ η ≤ (1 + |t|) ^ η * (1 + |y|) ^ η := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hη
  nlinarith [abs_add_le t y, abs_nonneg t, abs_nonneg y, mul_nonneg (abs_nonneg t) (abs_nonneg y)]

/-- `y ↦ Z(s + σ + iy) pesoMellin(σ + iy)` es integrable si `Re s + σ ≥ 1/2 + δ`. -/
theorem integrable_Zinv_mul_line (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 2) (hη : 0 < η) (hη1 : η < 1) {N h : ℝ} (hN : 0 < N) (hh : 0 < h)
    {s : ℂ} {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ -1) (hsσ : 1 / 2 + δ ≤ s.re + σ) :
    Integrable (fun y : ℝ => Zinv (s + ((σ : ℂ) + y * I)) * pesoMellin N h ((σ : ℂ) + y * I)) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound hRH hδ hδ' hη
  obtain ⟨K, hK0, hK⟩ := norm_pesoMellin_line_le hN hh hσ0 hσ1
  have hcont : Continuous (fun y : ℝ => Zinv (s + ((σ : ℂ) + y * I))) := by
    have hd := (differentiableOn_Zinv hRH).continuousOn
    refine hd.comp_continuous (by fun_prop) (fun y => ?_)
    show 1 / 2 < (s + ((σ : ℂ) + y * I)).re
    simp
    linarith
  have hF := integrable_pesoMellin_line hN hh hσ0 hσ1
  refine Integrable.mono' ((integrable_one_add_norm (r := 2 - η) (by norm_num; linarith)).const_mul
    (CZ * (1 + |s.im|) ^ η * K)) (hcont.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have him : (s + ((σ : ℂ) + y * I)).im = s.im + y := by simp
  have hre : 1 / 2 + δ ≤ (s + ((σ : ℂ) + y * I)).re := by simp; linarith
  have hy : 0 < 1 + |y| := by positivity
  rw [norm_mul, Real.norm_eq_abs y]
  calc ‖Zinv (s + ((σ : ℂ) + y * I))‖ * ‖pesoMellin N h ((σ : ℂ) + y * I)‖
      ≤ (CZ * (1 + |s.im + y|) ^ η) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        rw [← him]
        exact mul_le_mul (hCZ _ hre) (hK y) (norm_nonneg _) (by positivity)
    _ ≤ (CZ * ((1 + |s.im|) ^ η * (1 + |y|) ^ η)) * (K * (1 + |y|) ^ (-(2 : ℝ))) := by
        gcongr
        exact one_add_abs_add_rpow_le _ _ hη.le
    _ = CZ * (1 + |s.im|) ^ η * K * ((1 + |y|) ^ η * (1 + |y|) ^ (-(2 : ℝ))) := by ring
    _ = CZ * (1 + |s.im|) ^ η * K * (1 + |y|) ^ (-(2 - η)) := by
        rw [← Real.rpow_add hy]
        congr 2
        ring

/-! ### Cota en los lados horizontales -/

theorem horizontal_K (hRH : RiemannHypothesis) {δ₂ η' : ℝ} (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1 / 2)
    (hη' : 0 < η') (hη'1 : η' ≤ 1) {N h : ℝ} (hN : 1 ≤ N) (hh : 0 < h) {s : ℂ} {α β : ℝ}
    (hβ : β ≤ 2) (hreg : 1 / 2 + δ₂ ≤ s.re + α) :
    ∃ D : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, α ≤ x → x ≤ β →
      ‖contornoK N h s (x + T * I)‖ ≤ D / T ∧
        ‖contornoK N h s (x + ((-T : ℝ) : ℂ) * I)‖ ≤ D / T := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound hRH hδ₂ hδ₂' hη'
  set CZ' : ℝ := CZ * (1 + |s.im|) ^ η' with hCZ'
  have hCZ'0 : 0 ≤ CZ' := by positivity
  set E : ℝ := 2 * (N + h) ^ (3 : ℝ) / h with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨(2 * CZ' + ‖Zinv s‖) * E, fun T hT x hx1 hx2 => ?_⟩
  have hT0 : 0 < T := by linarith
  have main : ∀ w : ℂ, w.re = x → |w.im| = T →
      ‖contornoK N h s w‖ ≤ (2 * CZ' + ‖Zinv s‖) * E / T := by
    intro w hwre hwim
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hwim
      simp at hwim
      linarith
    rw [contornoK_eq hw0]
    have hnw : T ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
    have hnw1 : T ≤ ‖w + 1‖ := by
      have := Complex.abs_im_le_norm (w + 1)
      rw [add_im, one_im, add_zero, hwim] at this
      exact this
    have hZ : ‖Zinv (s + w)‖ ≤ 2 * CZ' * T := by
      have hre : 1 / 2 + δ₂ ≤ (s + w).re := by rw [add_re, hwre]; linarith
      have h1 := hCZ (s + w) hre
      rw [add_im] at h1
      have h2 := one_add_abs_add_rpow_le s.im w.im hη'.le
      have h3 : (1 + |w.im|) ^ η' ≤ 1 + |w.im| := by
        calc (1 + |w.im|) ^ η' ≤ (1 + |w.im|) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) hη'1
          _ = 1 + |w.im| := Real.rpow_one _
      rw [hwim] at h3
      calc ‖Zinv (s + w)‖ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |w.im|) ^ η') :=
            le_trans h1 (mul_le_mul_of_nonneg_left h2 hCZ0)
        _ = CZ' * (1 + |w.im|) ^ η' := by rw [hCZ']; ring
        _ ≤ CZ' * (1 + T) := by rw [hwim]; exact mul_le_mul_of_nonneg_left h3 hCZ'0
        _ ≤ 2 * CZ' * T := by nlinarith
    have hF : ‖pesoMellin N h w‖ * T ^ 2 ≤ E := by
      have h1 := norm_pesoMellin_le (N := N) (by linarith) hh w
      rw [hwre] at h1
      have hNh1 : 1 ≤ N + h := by linarith
      have hnum : (N + h) ^ (x + 1) + N ^ (x + 1) ≤ 2 * (N + h) ^ (3 : ℝ) := by
        have e1 : (N + h) ^ (x + 1) ≤ (N + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNh1 (by linarith)
        have e2 : N ^ (x + 1) ≤ N ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        have e3 : N ^ (3 : ℝ) ≤ (N + h) ^ (3 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        linarith
      have hden : h * T * T ≤ h * ‖w‖ * ‖w + 1‖ := by gcongr
      have h2 : ‖pesoMellin N h w‖ ≤ 2 * (N + h) ^ (3 : ℝ) / (h * T * T) := by
        calc ‖pesoMellin N h w‖ ≤ ((N + h) ^ (x + 1) + N ^ (x + 1)) / (h * ‖w‖ * ‖w + 1‖) := h1
          _ ≤ 2 * (N + h) ^ (3 : ℝ) / (h * T * T) := by
              gcongr
      rw [hE]
      have hpos : 0 < h * T * T := by positivity
      rw [le_div_iff₀ hpos] at h2
      rw [le_div_iff₀ hh]
      nlinarith [norm_nonneg (pesoMellin N h w)]
    rw [le_div_iff₀ hT0]
    have hsplit : ‖Zinv (s + w) * pesoMellin N h w - Zinv s * pesoMellin N h w‖
        ≤ (‖Zinv (s + w)‖ + ‖Zinv s‖) * ‖pesoMellin N h w‖ := by
      rw [← sub_mul, norm_mul]
      gcongr
      exact norm_sub_le _ _
    have hZs : ‖Zinv (s + w)‖ + ‖Zinv s‖ ≤ (2 * CZ' + ‖Zinv s‖) * T := by nlinarith [norm_nonneg (Zinv s)]
    calc ‖Zinv (s + w) * pesoMellin N h w - Zinv s * pesoMellin N h w‖ * T
        ≤ (‖Zinv (s + w)‖ + ‖Zinv s‖) * ‖pesoMellin N h w‖ * T := by gcongr
      _ ≤ (2 * CZ' + ‖Zinv s‖) * T * ‖pesoMellin N h w‖ * T := by gcongr
      _ = (2 * CZ' + ‖Zinv s‖) * (‖pesoMellin N h w‖ * T ^ 2) := by ring
      _ ≤ (2 * CZ' + ‖Zinv s‖) * E := by gcongr
  constructor
  · exact main _ (by simp) (by simp [abs_of_pos hT0])
  · exact main _ (by simp) (by simp [abs_of_pos hT0])

/-! ### Cota explícita en la recta izquierda -/

theorem norm_pesoMellin_left {N : ℝ} (hN : 1 ≤ N) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (y : ℝ) :
    ‖pesoMellin N (Real.sqrt N) (((-a : ℝ) : ℂ) + y * I)‖
      ≤ 3 * N ^ (-a) * N ^ (κ / 2) * (2 / a) ^ (1 + κ) * (1 + |y|) ^ (-(1 + κ)) := by
  set w : ℂ := ((-a : ℝ) : ℂ) + y * I with hw
  set h : ℝ := Real.sqrt N with hhdef
  have hN0 : 0 < N := by linarith
  have hh0 : 0 < h := Real.sqrt_pos.mpr hN0
  have hhsq : h ^ 2 = N := Real.sq_sqrt hN0.le
  have hh1 : 1 ≤ h := by nlinarith
  have hhN : h ≤ N := by nlinarith
  have hwre : w.re = -a := by simp [hw]
  have hu : a / 2 * (1 + |y|) ≤ ‖w‖ := by
    have := norm_line_ge (-a) y
    rwa [abs_neg, abs_of_pos ha0, min_eq_left (by linarith)] at this
  have hupos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hu
  set u : ℝ := ‖w‖ with hudef
  have hw1 : w + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hw] at this
    linarith
  have hw11 : u ≤ ‖w + 1‖ := by
    rw [hudef, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp [hw]
    nlinarith
  -- las dos cotas
  have hA : ‖pesoMellin N h w‖ ≤ N ^ (-a) / u := by
    have := norm_pesoMellin_le_int hN0 hh0 (w := w) (by rw [hwre]; linarith) hw1
    rwa [hwre] at this
  have hB : ‖pesoMellin N h w‖ ≤ 3 * N ^ (-a) * h / u ^ 2 := by
    have h1 := norm_pesoMellin_le hN0 hh0 w
    rw [hwre] at h1
    have e1 : (N + h) ^ (-a + 1) ≤ 2 * N ^ (-a + 1) := by
      calc (N + h) ^ (-a + 1) ≤ (2 * N) ^ (-a + 1) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ = 2 ^ (-a + 1) * N ^ (-a + 1) := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 2 * N ^ (-a + 1) := by
            gcongr
            calc (2 : ℝ) ^ (-a + 1) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
    have e2 : N ^ (-a + 1) = N ^ (-a) * N := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    have hden : h * u * u ≤ h * u * ‖w + 1‖ := by gcongr
    calc ‖pesoMellin N h w‖ ≤ ((N + h) ^ (-a + 1) + N ^ (-a + 1)) / (h * u * ‖w + 1‖) := h1
      _ ≤ (3 * N ^ (-a + 1)) / (h * u * u) := by
          gcongr
          linarith
      _ = 3 * N ^ (-a) * h / u ^ 2 := by
          rw [e2, ← hhsq]
          field_simp
  -- interpolación
  have hsqrtκ : h ^ κ = N ^ (κ / 2) := by
    rw [hhdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    ring_nf
  have hmain : ‖pesoMellin N h w‖ ≤ 3 * N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := by
    have hNa : 0 < N ^ (-a) := Real.rpow_pos_of_pos hN0 _
    rcases le_or_gt u h with hle | hgt
    · have e : u⁻¹ = u ^ (-(1 + κ)) * u ^ κ := by
        rw [← Real.rpow_add hupos, show -(1 + κ) + κ = -1 by ring, Real.rpow_neg_one]
      have huκ : u ^ κ ≤ h ^ κ := Real.rpow_le_rpow hupos.le hle hκ0
      calc ‖pesoMellin N h w‖ ≤ N ^ (-a) / u := hA
        _ = N ^ (-a) * (u ^ (-(1 + κ)) * u ^ κ) := by rw [div_eq_mul_inv, e]
        _ ≤ N ^ (-a) * (u ^ (-(1 + κ)) * h ^ κ) := by gcongr
        _ = N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := by rw [hsqrtκ]; ring
        _ ≤ 3 * N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := by
            have : 0 ≤ N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := by positivity
            linarith
    · have e : (u ^ 2)⁻¹ = u ^ (-(1 + κ)) * u ^ (κ - 1) := by
        rw [← Real.rpow_add hupos, show -(1 + κ) + (κ - 1) = -2 by ring, Real.rpow_neg hupos.le,
          Real.rpow_two]
      have huκ : u ^ (κ - 1) ≤ h ^ (κ - 1) :=
        Real.rpow_le_rpow_of_nonpos hh0 hgt.le (by linarith)
      have e2 : h * h ^ (κ - 1) = h ^ κ := by
        have := Real.rpow_add_one hh0.ne' (κ - 1)
        rw [show κ - 1 + 1 = κ by ring] at this
        rw [this]
        ring
      calc ‖pesoMellin N h w‖ ≤ 3 * N ^ (-a) * h / u ^ 2 := hB
        _ = 3 * N ^ (-a) * h * (u ^ (-(1 + κ)) * u ^ (κ - 1)) := by rw [div_eq_mul_inv, e]
        _ ≤ 3 * N ^ (-a) * h * (u ^ (-(1 + κ)) * h ^ (κ - 1)) := by gcongr
        _ = 3 * N ^ (-a) * (h * h ^ (κ - 1)) * u ^ (-(1 + κ)) := by ring
        _ = 3 * N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := by rw [e2, hsqrtκ]
  have hy : 0 < 1 + |y| := by positivity
  have hfin : u ^ (-(1 + κ)) ≤ (2 / a) ^ (1 + κ) * (1 + |y|) ^ (-(1 + κ)) := by
    calc u ^ (-(1 + κ)) ≤ (a / 2 * (1 + |y|)) ^ (-(1 + κ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hu (by linarith)
      _ = (a / 2) ^ (-(1 + κ)) * (1 + |y|) ^ (-(1 + κ)) := Real.mul_rpow (by positivity) hy.le
      _ = (2 / a) ^ (1 + κ) * (1 + |y|) ^ (-(1 + κ)) := by
          rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
  calc ‖pesoMellin N h w‖ ≤ 3 * N ^ (-a) * N ^ (κ / 2) * u ^ (-(1 + κ)) := hmain
    _ ≤ 3 * N ^ (-a) * N ^ (κ / 2) * ((2 / a) ^ (1 + κ) * (1 + |y|) ^ (-(1 + κ))) := by gcongr
    _ = 3 * N ^ (-a) * N ^ (κ / 2) * (2 / a) ^ (1 + κ) * (1 + |y|) ^ (-(1 + κ)) := by ring

/-! ### Error del suavizado -/

theorem smoothing_error {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    ‖∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)‖
      ≤ (n : ℝ) ^ (1 / 2 - s.re) := by
  set M := ⌊(n : ℝ) + Real.sqrt n⌋₊ with hM
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hnM : n ≤ M := Nat.le_floor (by linarith)
  have hMle : (M : ℝ) ≤ n + Real.sqrt n := Nat.floor_le (by positivity)
  have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := Finset.Icc_add_one_left_eq_Ioc 0 M
  have e2 : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
  rw [e1, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hnM, ← e2]
  have hfirst : ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)
        * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn : (d : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    rw [peso_of_le hsqpos hdn, ofReal_one, mul_one]
    simp [mu]
  rw [hfirst, add_sub_cancel_left]
  calc ‖∑ d ∈ Finset.Ioc n M, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)‖
      ≤ ∑ d ∈ Finset.Ioc n M, ‖(ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)
          * ((peso n (Real.sqrt n) d : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc n M, (n : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdn : n < d := (Finset.mem_Ioc.mp hd).1
        have hd0 : 0 < d := by omega
        rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hd0, Complex.norm_intCast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (peso_nonneg _)]
        have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have h2 : (d : ℝ) ^ (-s).re ≤ (n : ℝ) ^ (-s.re) := by
          rw [neg_re]
          exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hdn.le) (by linarith)
        have h3 := peso_le_one (N := (n : ℝ)) (h := Real.sqrt n) (d : ℝ)
        have h4 : 0 ≤ (d : ℝ) ^ (-s).re := by positivity
        calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * (d : ℝ) ^ (-s).re
              * peso (n : ℝ) (Real.sqrt n) d
            ≤ 1 * (n : ℝ) ^ (-s.re) * 1 :=
              mul_le_mul (mul_le_mul h1 h2 h4 zero_le_one) h3 (peso_nonneg _) (by positivity)
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

/-! ### Balazard–Saias -/

set_option maxHeartbeats 4000000 in
/-- **Balazard–Saias con `Z = 1/ζ` holomorfa**: bajo RH, para `n ≥ 1` y `Re s ≥ 1/2 + δ`
(incluido `s = 1`, donde `Z(1) = 0`), `‖∑_{d≤n} μ(d) d^{−s} − Z(s)‖ ≤ C n^{−δ/3} (1+|t|)^η`. -/
theorem balazard_saias_Zinv (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s : ℂ, 1 / 2 + δ ≤ s.re →
      ‖∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - Zinv s‖
        ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  set η' : ℝ := min η (δ / 6) with hη'
  have hη'0 : 0 < η' := lt_min hη (by positivity)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'δ : η' ≤ δ / 6 := min_le_right _ _
  have hη'1 : η' < 1 := by linarith
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ2' : δ / 2 < 1 / 2 := by linarith
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound hRH hδ2 hδ2' hη'0
  have hJint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(1 + η'))) :=
    integrable_one_add_norm (by norm_num; linarith)
  set J : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(1 + η')) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  set Cm : ℝ := CZ * (3 * (4 / δ) ^ (1 + 2 * η')) * J / (2 * Real.pi) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨1 + Cm, fun n hn s hsre => ?_⟩
  have hn1 : 1 ≤ n := hn
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hh0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN0
  set a : ℝ := min (s.re - 1 / 2 - δ / 2) (1 / 2) with ha
  have ha1 : δ / 2 ≤ a := le_min (by linarith) (by linarith)
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  have ha3 : a ≤ s.re - 1 / 2 - δ / 2 := min_le_left _ _
  have ha0 : 0 < a := by linarith
  have hs12 : 1 / 2 < s.re := by linarith
  -- lado de Dirichlet
  have hD := dirichlet_side hN0 hh0 (s := s) (by linarith)
  -- contorno
  have hU : {w : ℂ | -a ≤ w.re ∧ w.re ≤ 2} ⊆ {w | 1 / 2 < (s + w).re ∧ -1 < w.re} :=
    fun w hw => ⟨by simp; linarith [hw.1], by linarith [hw.1]⟩
  have hdiff := (differentiableOn_contornoK hRH hN0 hh0 hs12).mono hU
  have hlineK : ∀ σ : ℝ, σ ≠ 0 → σ ≠ -1 → 1 / 2 + δ / 2 ≤ s.re + σ →
      Integrable (fun y : ℝ => contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I)) ∧
      ∫ y : ℝ, contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I)
        = (∫ y : ℝ, Zinv (s + (σ + y * I)) * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I))
          - Zinv s * ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
    intro σ hσ0 hσ1 hσs
    have hZF := integrable_Zinv_mul_line hRH hδ2 hδ2' hη'0 hη'1 hN0 hh0 (s := s) hσ0 hσ1 hσs
    have hF := integrable_pesoMellin_line hN0 hh0 hσ0 hσ1
    have hfun : (fun y : ℝ => contornoK (n : ℝ) (Real.sqrt n) s (σ + y * I))
        = fun y : ℝ => Zinv (s + (σ + y * I)) * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I)
          - Zinv s * pesoMellin (n : ℝ) (Real.sqrt n) (σ + y * I) := by
      funext y
      apply contornoK_eq
      intro h0
      have := congrArg Complex.re h0
      simp at this
      exact hσ0 this
    rw [hfun]
    exact ⟨hZF.sub (hF.const_mul _), by rw [integral_sub hZF (hF.const_mul _), integral_const_mul]⟩
  obtain ⟨hKa, hIa⟩ := hlineK (-a) (by linarith) (by linarith) (by linarith)
  obtain ⟨hK2, hI2⟩ := hlineK 2 (by norm_num) (by norm_num) (by linarith)
  obtain ⟨Dh, hDh⟩ := horizontal_K hRH hδ2 hδ2' hη'0 hη'1.le hN1 hh0 (s := s) (α := -a) (β := 2)
    le_rfl (by linarith)
  have hshift := integral_vertical_eq (by linarith) hdiff hKa hK2 hDh
  -- integrales del peso
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have hint2 : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I)
      = 2 * Real.pi := by
    have h1 := mellinInv_pesoMellin hN0 hh0 (σ := 2) two_pos one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1] at h1
    simp only [ofReal_one, one_cpow, one_smul] at h1
    rw [Complex.real_smul] at h1
    have e : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
      push_cast
      field_simp
    exact mul_left_cancel₀ hc (h1.trans e.symm)
  have hinta : ∫ y : ℝ, pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) = 0 := by
    have h1 := mellinInv_pesoMellin_neg hN0 hh0 (σ := -a) (by linarith) (by linarith) one_pos
    unfold mellinInv at h1
    rw [peso_of_le hh0 hN1, sub_self] at h1
    simp only [ofReal_one, one_cpow, one_smul, ofReal_zero] at h1
    rw [Complex.real_smul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  have hrel : (∫ y : ℝ, Zinv (s + (((2 : ℝ) : ℂ) + y * I))
        * pesoMellin (n : ℝ) (Real.sqrt n) (((2 : ℝ) : ℂ) + y * I))
      = 2 * Real.pi * Zinv s + ∫ y : ℝ, Zinv (s + (((-a : ℝ) : ℂ) + y * I))
        * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) := by
    rw [hIa, hI2, hinta, hint2] at hshift
    linear_combination -hshift
  -- cota de la integral en la recta izquierda
  set A : ℂ := ∫ y : ℝ, Zinv (s + (((-a : ℝ) : ℂ) + y * I))
    * pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I) with hAdef
  set Q : ℝ := CZ * (1 + |s.im|) ^ η' * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η'))
    with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hAbound : ‖A‖ ≤ Q * J := by
    rw [hAdef, hJ, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hJint.const_mul Q) (Eventually.of_forall fun y => ?_)
    have hre : 1 / 2 + δ / 2 ≤ (s + (((-a : ℝ) : ℂ) + y * I)).re := by simp; linarith
    have him : (s + (((-a : ℝ) : ℂ) + y * I)).im = s.im + y := by simp
    have hZ := hCZ _ hre
    rw [him] at hZ
    have hZ2 : ‖Zinv (s + (((-a : ℝ) : ℂ) + y * I))‖
        ≤ CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by
      calc _ ≤ CZ * (1 + |s.im + y|) ^ η' := hZ
        _ ≤ CZ * ((1 + |s.im|) ^ η' * (1 + |y|) ^ η') :=
            mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le _ _ hη'0.le) hCZ0
        _ = CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η' := by ring
    have hF := norm_pesoMellin_left hN1 ha0 ha2 (κ := 2 * η') (by positivity) (by linarith) y
    have h2a : (2 / a) ^ (1 + 2 * η') ≤ (4 / δ) ^ (1 + 2 * η') := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [div_le_div_iff₀ ha0 hδ]
      linarith
    have hy : 0 < 1 + |y| := by positivity
    have hpow : (1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η')) = (1 + ‖y‖) ^ (-(1 + η')) := by
      rw [← Real.rpow_add hy, Real.norm_eq_abs]
      congr 1
      ring
    have hNe : (n : ℝ) ^ (2 * η' / 2) = (n : ℝ) ^ η' := by congr 1; ring
    rw [norm_mul]
    calc ‖Zinv (s + (((-a : ℝ) : ℂ) + y * I))‖
          * ‖pesoMellin (n : ℝ) (Real.sqrt n) (((-a : ℝ) : ℂ) + y * I)‖
        ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ (2 * η' / 2) * (2 / a) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := mul_le_mul hZ2 hF (norm_nonneg _) (by positivity)
      _ ≤ (CZ * (1 + |s.im|) ^ η' * (1 + |y|) ^ η')
          * (3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η')
            * (1 + |y|) ^ (-(1 + 2 * η'))) := by
          rw [hNe]
          gcongr
      _ = Q * ((1 + |y|) ^ η' * (1 + |y|) ^ (-(1 + 2 * η'))) := by rw [hQ]; ring
      _ = Q * (1 + ‖y‖) ^ (-(1 + η')) := by rw [hpow]
  -- combinación
  have hSφ : ∑ d ∈ Finset.Icc 1 ⌊(n : ℝ) + Real.sqrt n⌋₊,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * ((peso n (Real.sqrt n) d : ℝ) : ℂ)
      = Zinv s + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A := by
    rw [← hD, hrel, mul_add]
    congr 1
    rw [← mul_assoc]
    have e : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
      push_cast
      field_simp
    rw [e, one_mul]
  have hsm := smoothing_error hn1 (s := s) (by linarith)
  rw [hSφ] at hsm
  have hsplit : ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - Zinv s
      = -(Zinv s + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s))
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A := by ring
  rw [hsplit]
  have hexp1 : (n : ℝ) ^ (1 / 2 - s.re) ≤ (n : ℝ) ^ (-δ / 3) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hexp2 : (n : ℝ) ^ (-a) * (n : ℝ) ^ η' ≤ (n : ℝ) ^ (-δ / 3) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have ht1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have ht2 : (1 + |s.im|) ^ η' ≤ (1 + |s.im|) ^ η :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hη'η
  have hnδ : 0 ≤ (n : ℝ) ^ (-δ / 3) := by positivity
  have hsecond : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A‖ ≤ Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hQ' : Q ≤ CZ * (1 + |s.im|) ^ η * (3 * (n : ℝ) ^ (-δ / 3) * (4 / δ) ^ (1 + 2 * η')) := by
      rw [hQ]
      have e1 : 3 * (n : ℝ) ^ (-a) * (n : ℝ) ^ η' * (4 / δ) ^ (1 + 2 * η')
          = 3 * ((n : ℝ) ^ (-a) * (n : ℝ) ^ η') * (4 / δ) ^ (1 + 2 * η') := by ring
      rw [e1]
      gcongr
    calc 1 / (2 * Real.pi) * ‖A‖ ≤ 1 / (2 * Real.pi) * (Q * J) := by gcongr
      _ ≤ 1 / (2 * Real.pi) * (CZ * (1 + |s.im|) ^ η
            * (3 * (n : ℝ) ^ (-δ / 3) * (4 / δ) ^ (1 + 2 * η')) * J) := by gcongr
      _ = Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by rw [hCm]; ring
  calc ‖-(Zinv s + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s))
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A‖
      ≤ ‖Zinv s + ((1 / (2 * Real.pi) : ℝ) : ℂ) * A
          - ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)‖
        + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * A‖ := by
        rw [← norm_neg (Zinv s + _ - _)]
        exact norm_add_le _ _
    _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η + Cm * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
        gcongr
        calc _ ≤ (n : ℝ) ^ (1 / 2 - s.re) := hsm
          _ ≤ (n : ℝ) ^ (-δ / 3) := hexp1
          _ = (n : ℝ) ^ (-δ / 3) * 1 := (mul_one _).symm
          _ ≤ (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by gcongr
    _ = (1 + Cm) * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by ring

/-- **Lema de Balazard–Saias con `θ = 1/2`** (estado 45, §3), bajo la hipótesis de Riemann. -/
theorem balazard_saias_de (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 1 → s ≠ 1 →
      ‖∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s) - 1 / riemannZeta s‖
        ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  obtain ⟨C, hC⟩ := balazard_saias_Zinv hRH hδ hδ' hη
  refine ⟨C, fun n hn s hs _ hs1 => ?_⟩
  rw [one_div, ← Zinv_eq hs1]
  exact hC n (by omega) s hs

end AMate
