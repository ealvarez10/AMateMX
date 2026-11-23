import AMateEnergia.RutaFraccionariaPrimos
import AMateEnergia.CalibracionTheta

/-!
# Cuadratura hiperbólica de Chebyshev: truncamiento incondicional, calibración en `θ` y barrera de monotonía

Desarrollo profundo en Lean 4 (solo Mathlib, cero `sorry`) sobre el operador de discrepancia
hiperbólica `Δ_hip(m)` al que quedó reducida la Ruta B (`AMate.rh_iff_S_hiperbolica`):

1. **Cambio de variable hiperbólico exacto (`integral_hiperbolica_cambio_variable`,
   `operadorCuadratura_eq_suma_zonas`):**
   mediante `t = m⁴ / u`, el operador
   `𝒬_m(E) = m⁴ ∫_{m²}^{m⁴} (E(t) / t²) dt − ∑_{q=1}^{m²−1} E(m⁴ / q)`
   es idénticamente igual al error de cuadratura por rectángulos izquierdos de `u ↦ E(m⁴ / u)` en
   los `m² − 1` intervalos unitarios `[q, q + 1]`:
   `𝒬_m(E) = ∑_{q=1}^{m²−1} ∫_q^{q+1} (E(m⁴ / u) − E(m⁴ / q)) du`.
2. **Truncamiento unilateral incondicional de todas las zonas de intervalos cortos
   (`cota_zona_errorChebyshev`, `truncamiento_cola_discrepanciaHiperbolica`,
   `cota_incondicional_S_hiperbolica`):**
   usando únicamente que `ϑ` es monótona creciente, en cada zona `[q, q + 1]` se cumple
   `∫_q^{q+1} (E_ϑ(m⁴/u) − E_ϑ(m⁴/q)) du ≤ m⁴ (1/q − 1/(q+1))`,
   cuya cola `q > Q₀` se telescopa exactamente a `≤ m⁴ / (Q₀ + 1)`. Así:
   * las zonas de intervalos cortos (`q > Q₀`) quedan eliminadas incondicionalmente;
   * en `Q₀ = 0` resulta `Δ_hip(m) ≤ m⁴ − m²` y la cota global sin hipótesis
     `S_hiperbolica Y ≤ Y^{3/4}` para todo `Y ≥ 1`.
3. **Calibración en `θ ∈ [1/2, 1)` (`cota_S_hiperbolica_de_sin_ceros_theta`):**
   bajo `SinCerosDerecha θ`, para todo `η > 0` vale uniformemente para `Y` grande
   `S_hiperbolica Y ≤ S_AMate Y ≤ Y^{(3/2)(θ − 1/2) + η}`, interpolando continuamente entre el
   exponente incondicional `3/4` (`θ → 1`) y `0` (`θ = 1/2`, RH).
4. **Teorema de barrera / imposibilidad para argumentos de monotonía y regiones libres de ceros
   clásicas (`strictMonoOn_id_add_ondaPrueba`, `operadorCuadratura_ondaPrueba_ge`,
   `explosion_ventana_ondaPrueba`):**
   para cualquier `β ∈ (1/2, 1)`, la perturbación explícita `E_β(t) = −t^β` cumple:
   * `t + E_β(t) = t − t^β` es estrictamente creciente en `[1, ∞)` (como `ϑ(t)` en media suave);
   * `|E_β(t)| = t^β` es exponencialmente más pequeña que cualquier cota clásica incondicional del
     teorema de los números primos (de la Vallée Poussin / Vinogradov–Korobov `t exp(−c(log t)^{3/5})`);
   * sin embargo, `𝒬_m(E_β) ≥ c_β m^{4β}` con `c_β = (1/2)(1 − (3/2)^{−β}) > 0`, haciendo que su
     suma en ventanas `[Y, Y^{3/2}]` crezca como `≫ Y^{(3/2)(β − 1/2)}` y viole `≤ Y^η` para todo
     `0 < η < (3/2)(β − 1/2)`.
   Esto certifica por máquina que **ningún argumento basado solo en cuadratura, monotonía de `ϑ` y
   regiones libres de ceros sub-polinomiales puede demostrar `S_hiperbolica Y ≤ Y^η`**: cualquier
   prueba sin Alpöge debe excluir desviaciones `O(t^β)` para todo `β > 1/2`, lo que equivale
   exactamente a una demostración nueva e independiente de la Hipótesis de Riemann.
-/

open Complex MeasureTheory Set Filter Metric Topology intervalIntegral

namespace AMate

/-! ### 1. Operador general de cuadratura hiperbólica y cambio de variable `t = m⁴ / u` -/

/-- Operador general de cuadratura hiperbólica en escala `m⁴`:
`𝒬_m(E) = m⁴ ∫_{m²}^{m⁴} (E(t) / t²) dt − ∑_{q=1}^{m²−1} E(m⁴ / q)`. -/
noncomputable def operadorCuadratura (E_fn : ℝ → ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ 4 * (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), E_fn t / t ^ 2)
    - ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), E_fn ((m : ℝ) ^ 4 / (q : ℝ))

theorem operadorCuadratura_errorChebyshev (m : ℕ) :
    operadorCuadratura errorChebyshev m = discrepanciaHiperbolica m := rfl

/-- **Cambio de variable hiperbólico exacto `t = m⁴ / u`:**
para cualquier función `f : ℝ → ℝ` y todo entero `m ≥ 1`,
`m⁴ ∫_{m²}^{m⁴} (f(t) / t²) dt = ∫_1^{m²} f(m⁴ / u) du`. -/
theorem integral_hiperbolica_cambio_variable (f : ℝ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ 4 * (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), f t / t ^ 2)
      = ∫ u in (1 : ℝ)..((m : ℝ) ^ 2), f ((m : ℝ) ^ 4 / u) := by
  rcases eq_or_lt_of_le hm with rfl | hm_gt1
  · simp
  · have hm1_r : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm_gt1
    have hm2_gt1 : (1 : ℝ) < (m : ℝ) ^ 2 := by nlinarith
    have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hm4_pos : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
    have hm2_le_m4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
      pow_le_pow_right₀ hm1_r.le (by omega)
    let φ : ℝ → ℝ := fun u => (m : ℝ) ^ 4 / u
    have himg : φ '' Ioo (1 : ℝ) ((m : ℝ) ^ 2) = Ioo ((m : ℝ) ^ 2) ((m : ℝ) ^ 4) := by
      ext t
      simp only [mem_image, mem_Ioo, φ]
      constructor
      · rintro ⟨u, ⟨hu1, hum2⟩, rfl⟩
        have hu_pos : 0 < u := lt_trans one_pos hu1
        refine ⟨?_, ?_⟩
        · rw [lt_div_iff₀ hu_pos]
          calc (m : ℝ) ^ 2 * u < (m : ℝ) ^ 2 * (m : ℝ) ^ 2 :=
                mul_lt_mul_of_pos_left hum2 hm2_pos
            _ = (m : ℝ) ^ 4 := by ring
        · rw [div_lt_iff₀ hu_pos]
          nlinarith
      · rintro ⟨htm2, htm4⟩
        have ht_pos : 0 < t := lt_trans hm2_pos htm2
        refine ⟨(m : ℝ) ^ 4 / t, ⟨?_, ?_⟩, ?_⟩
        · exact (one_lt_div ht_pos).mpr htm4
        · rw [div_lt_iff₀ ht_pos]
          calc (m : ℝ) ^ 4 = (m : ℝ) ^ 2 * (m : ℝ) ^ 2 := by ring
            _ < (m : ℝ) ^ 2 * t := mul_lt_mul_of_pos_left htm2 hm2_pos
        · have ht_ne : t ≠ 0 := ht_pos.ne'
          field_simp
    have hinj : InjOn φ (Ioo (1 : ℝ) ((m : ℝ) ^ 2)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      dsimp only [φ] at heq
      have h1 : 0 < u₁ := lt_trans one_pos hu₁.1
      have h2 : 0 < u₂ := lt_trans one_pos hu₂.1
      have hm4_ne : (m : ℝ) ^ 4 ≠ 0 := hm4_pos.ne'
      have h1_ne : u₁ ≠ 0 := h1.ne'
      have h2_ne : u₂ ≠ 0 := h2.ne'
      field_simp at heq
      linarith
    have hderiv : ∀ u ∈ Ioo (1 : ℝ) ((m : ℝ) ^ 2),
        HasDerivWithinAt φ (-(m : ℝ) ^ 4 / u ^ 2) (Ioo 1 ((m : ℝ) ^ 2)) u := by
      intro u hu
      have hu0 : u ≠ 0 := (lt_trans one_pos hu.1).ne'
      exact ((hasDerivAt_const u ((m : ℝ) ^ 4)).div (hasDerivAt_id u) hu0).hasDerivWithinAt.congr_deriv
        (by simp only [id]; ring)
    rw [integral_of_le hm2_le_m4, integral_of_le hm2_gt1.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu_pos : 0 < u := lt_trans one_pos hu.1
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hm4_ne : (m : ℝ) ^ 4 ≠ 0 := hm4_pos.ne'
    have habs : |-(m : ℝ) ^ 4 / u ^ 2| = (m : ℝ) ^ 4 / u ^ 2 := by
      rw [neg_div, abs_neg, abs_of_pos (div_pos hm4_pos (pow_pos hu_pos 2))]
    rw [smul_eq_mul, habs]
    dsimp only [φ]
    field_simp

/-- Descomposición por zonas unitarias `[q, q + 1]` del operador de cuadratura cuando `u ↦ E(m⁴/u)`
es integrable en `[1, m²]`. -/
theorem operadorCuadratura_eq_suma_zonas {E_fn : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hint : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
      IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ)) :
    operadorCuadratura E_fn m
      = ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
          ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
            (E_fn ((m : ℝ) ^ 4 / u) - E_fn ((m : ℝ) ^ 4 / (q : ℝ))) := by
  unfold operadorCuadratura
  rw [integral_hiperbolica_cambio_variable E_fn hm]
  rcases eq_or_lt_of_le hm with rfl | hm_gt1
  · simp
  · have hm2_ge2 : 2 ≤ m ^ 2 := by nlinarith
    have hK : m ^ 2 - 1 + 1 = m ^ 2 := by omega
    -- Partición de `[1, m²]` en `[q, q+1]` para `1 ≤ q ≤ m² − 1`.
    have hadj : (∫ u in (1 : ℝ)..((m : ℝ) ^ 2), E_fn ((m : ℝ) ^ 4 / u))
        = ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
            ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ), E_fn ((m : ℝ) ^ 4 / u) := by
      set K : ℕ := m ^ 2 - 1
      have hint_span : ∀ n : ℕ, (∀ q ∈ Finset.Icc (1 : ℕ) n,
            IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ)) →
          IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (1 : ℝ) ((n + 1 : ℕ) : ℝ) := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ j ihj =>
          intro hj_all
          have hj_prev : ∀ q ∈ Finset.Icc (1 : ℕ) j,
              IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ) :=
            fun q hq => hj_all q (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
              (Finset.mem_Icc.mp hq).2.trans (Nat.le_succ j)⟩)
          exact (ihj hj_prev).trans (hj_all (j + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
      have hind : ∀ n : ℕ, (∀ q ∈ Finset.Icc (1 : ℕ) n,
            IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ)) →
          (∫ u in (1 : ℝ)..((n + 1 : ℕ) : ℝ), E_fn ((m : ℝ) ^ 4 / u))
            = ∑ q ∈ Finset.Icc (1 : ℕ) n,
                ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ), E_fn ((m : ℝ) ^ 4 / u) := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ k ih =>
          intro hint_n
          have hint_prev : ∀ q ∈ Finset.Icc (1 : ℕ) k,
              IntervalIntegrable (fun u : ℝ => E_fn ((m : ℝ) ^ 4 / u)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ) :=
            fun q hq => hint_n q (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
              (Finset.mem_Icc.mp hq).2.trans (Nat.le_succ k)⟩)
          have hint_left := hint_span k hint_prev
          have hint_last := hint_n (k + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
          rw [← integral_add_adjacent_intervals hint_left hint_last, ih hint_prev,
            Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      have hres := hind K hint
      have hm2_cast : ((K + 1 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
        rw [hK]; push_cast; rfl
      rwa [hm2_cast] at hres
    rw [hadj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hsub := integral_sub (hint q hq) (intervalIntegrable_const (c := E_fn ((m : ℝ) ^ 4 / (q : ℝ))))
    rw [hsub, intervalIntegral.integral_const]
    have hlen : ((q + 1 : ℕ) : ℝ) - (q : ℝ) = 1 := by push_cast; ring
    rw [hlen, one_smul]

/-! ### 2. Truncamiento unilateral incondicional de las colas `q > Q₀` -/

theorem intervalIntegrable_errorChebyshev_div (m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    IntervalIntegrable (fun u : ℝ => errorChebyshev ((m : ℝ) ^ 4 / u))
      volume (q : ℝ) ((q + 1 : ℕ) : ℝ) := by
  have hle : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  have hmeas : Measurable (fun u : ℝ => errorChebyshev ((m : ℝ) ^ 4 / u)) :=
    (measurable_thetaChebyshev.sub measurable_id).comp (measurable_const.div measurable_id)
  set B_max : ℝ := |thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ))| + (m : ℝ) ^ 4 / (q : ℝ)
  have hdom : IntegrableOn (fun _ : ℝ => B_max) (Ioc (q : ℝ) ((q + 1 : ℕ) : ℝ)) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  have hu_pos : 0 < u := lt_trans hq_pos hu.1
  have hdiv_le : (m : ℝ) ^ 4 / u ≤ (m : ℝ) ^ 4 / (q : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hq_pos hu.1.le
  have hθ_nn : 0 ≤ thetaChebyshev ((m : ℝ) ^ 4 / u) := by
    have h0 : thetaChebyshev 0 = 0 := by simp [thetaChebyshev]
    rw [← h0]; exact monotone_thetaChebyshev (by positivity)
  have hθ_le : thetaChebyshev ((m : ℝ) ^ 4 / u) ≤ |thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ))| :=
    (monotone_thetaChebyshev hdiv_le).trans (le_abs_self _)
  rw [Real.norm_eq_abs]
  unfold errorChebyshev
  have htri : |thetaChebyshev ((m : ℝ) ^ 4 / u) - (m : ℝ) ^ 4 / u|
      ≤ |thetaChebyshev ((m : ℝ) ^ 4 / u)| + |(m : ℝ) ^ 4 / u| := by
    simpa [Real.norm_eq_abs] using
      norm_sub_le (thetaChebyshev ((m : ℝ) ^ 4 / u)) ((m : ℝ) ^ 4 / u)
  rw [abs_of_nonneg hθ_nn, abs_of_nonneg (div_nonneg (by positivity) hu_pos.le)] at htri
  simp only [B_max]
  linarith

/-- **Cota unilateral en cada zona `[q, q + 1]` por monotonía de `ϑ`:**
para todo `m : ℕ` y todo `q ≥ 1`,
`∫_q^{q+1} (E_ϑ(m⁴/u) − E_ϑ(m⁴/q)) du ≤ m⁴ (1/q − 1/(q+1))`. -/
theorem cota_zona_errorChebyshev (m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
        (errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))))
      ≤ (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1_pos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hle : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ => errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ)))
      volume (q : ℝ) ((q + 1 : ℕ) : ℝ) :=
    (intervalIntegrable_errorChebyshev_div m hq).sub intervalIntegrable_const
  have hcont_rhs : ContinuousOn (fun u : ℝ => (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / u))
      (uIcc (q : ℝ) ((q + 1 : ℕ) : ℝ)) := by
    rw [uIcc_of_le hle]
    exact continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hq_pos hu.1).ne'))
  have hpt : ∀ u ∈ Icc (q : ℝ) ((q + 1 : ℕ) : ℝ),
      errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))
        ≤ (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / u) := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le hq_pos hu.1
    have hθ_le : thetaChebyshev ((m : ℝ) ^ 4 / u) ≤ thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ)) :=
      monotone_thetaChebyshev (div_le_div_of_nonneg_left (by positivity) hq_pos hu.1)
    unfold errorChebyshev
    have hlin : (m : ℝ) ^ 4 / (q : ℝ) - (m : ℝ) ^ 4 / u = (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / u) := by
      ring
    linarith
  have hint_mono := integral_mono_on hle hint_lhs hcont_rhs.intervalIntegrable hpt
  -- Evaluamos `∫_q^{q+1} (1/q − 1/u) du = 1/q − log((q+1)/q) ≤ 1/q − 1/(q+1)`.
  have hint_inv : (∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ), (1 / u))
      = Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ)) := by
    have hderiv : ∀ u ∈ uIcc (q : ℝ) ((q + 1 : ℕ) : ℝ), HasDerivAt Real.log (1 / u) u := by
      intro u hu
      rw [uIcc_of_le hle] at hu
      simpa [one_div] using Real.hasDerivAt_log (lt_of_lt_of_le hq_pos hu.1).ne'
    have hcont : ContinuousOn (fun u : ℝ => 1 / u) (uIcc (q : ℝ) ((q + 1 : ℕ) : ℝ)) := by
      rw [uIcc_of_le hle]
      exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hq_pos hu.1).ne'
    rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
      Real.log_div hq1_pos.ne' hq_pos.ne']
  have hrhs_val : (∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ), (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / u))
      = (m : ℝ) ^ 4 * (1 / (q : ℝ) - Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ))) := by
    have hc1 : IntervalIntegrable (fun _ : ℝ => 1 / (q : ℝ)) volume (q : ℝ) ((q + 1 : ℕ) : ℝ) :=
      intervalIntegrable_const
    have hc2 : IntervalIntegrable (fun u : ℝ => 1 / u) volume (q : ℝ) ((q + 1 : ℕ) : ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hq_pos hu.1).ne'
    rw [intervalIntegral.integral_const_mul, integral_sub hc1 hc2, intervalIntegral.integral_const, hint_inv]
    have hlen : ((q + 1 : ℕ) : ℝ) - (q : ℝ) = 1 := by push_cast; ring
    rw [hlen, one_smul]
  have hlog_ge : 1 / ((q + 1 : ℕ) : ℝ) ≤ Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ)) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq_pos hq1_pos)
    have hinv_eq : (((q + 1 : ℕ) : ℝ) / (q : ℝ))⁻¹ = (q : ℝ) / ((q + 1 : ℕ) : ℝ) := inv_div _ _
    have hlog_inv : Real.log ((q : ℝ) / ((q + 1 : ℕ) : ℝ))
        = -Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ)) := by
      rw [← hinv_eq, Real.log_inv]
    have hsub_eq : (q : ℝ) / ((q + 1 : ℕ) : ℝ) - 1 = -(1 / ((q + 1 : ℕ) : ℝ)) := by
      have hne : ((q + 1 : ℕ) : ℝ) ≠ 0 := hq1_pos.ne'
      push_cast at hne ⊢
      field_simp
      ring
    linarith
  calc (∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
          (errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))))
      ≤ (m : ℝ) ^ 4 * (1 / (q : ℝ) - Real.log (((q + 1 : ℕ) : ℝ) / (q : ℝ))) := by
        rwa [hrhs_val] at hint_mono
    _ ≤ (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Teorema de truncamiento unilateral de colas (`q > Q₀`):**
para todo `m ≥ 1` y cualquier corte `Q₀ ≤ m² − 1`, todas las zonas `q > Q₀` (intervalos cortos)
aportan en conjunto a lo sumo `m⁴ / (Q₀ + 1) − m²`:
`Δ_hip(m) ≤ ∑_{q=1}^{Q₀} ∫_q^{q+1} (E_ϑ(m⁴/u) − E_ϑ(m⁴/q)) du + m⁴ / (Q₀ + 1)`. -/
theorem truncamiento_cola_discrepanciaHiperbolica {m Q₀ : ℕ} (hm : 1 ≤ m) (hQ : Q₀ ≤ m ^ 2 - 1) :
    discrepanciaHiperbolica m
      ≤ (∑ q ∈ Finset.Icc (1 : ℕ) Q₀,
          ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
            (errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))))
        + (m : ℝ) ^ 4 / ((Q₀ : ℝ) + 1) := by
  rcases eq_or_lt_of_le hm with rfl | hm_gt1
  · have hQ0 : Q₀ = 0 := by omega
    subst hQ0
    simp [discrepanciaHiperbolica]
  · rw [← operadorCuadratura_errorChebyshev,
      operadorCuadratura_eq_suma_zonas hm (fun q hq => intervalIntegrable_errorChebyshev_div m (Finset.mem_Icc.mp hq).1)]
    set K : ℕ := m ^ 2 - 1
    have hsplit_set : Finset.Icc (1 : ℕ) K = Finset.Icc (1 : ℕ) Q₀ ∪ Finset.Ioc Q₀ K := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) Q₀) (Finset.Ioc Q₀ K) :=
      Finset.disjoint_left.mpr fun q h1 h2 => by
        have := (Finset.mem_Icc.mp h1).2
        have := (Finset.mem_Ioc.mp h2).1
        omega
    rw [hsplit_set, Finset.sum_union hdisj]
    have htail : (∑ q ∈ Finset.Ioc Q₀ K,
          ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
            (errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))))
        ≤ (m : ℝ) ^ 4 / ((Q₀ : ℝ) + 1) := by
      have hj : K = Q₀ + (K - Q₀) := by omega
      calc (∑ q ∈ Finset.Ioc Q₀ K,
            ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
              (errorChebyshev ((m : ℝ) ^ 4 / u) - errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))))
          ≤ ∑ q ∈ Finset.Ioc Q₀ K, (m : ℝ) ^ 4 * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) :=
            Finset.sum_le_sum fun q hq => cota_zona_errorChebyshev m (by have := (Finset.mem_Ioc.mp hq).1; omega)
        _ = (m : ℝ) ^ 4 * ∑ q ∈ Finset.Ioc Q₀ K, (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
        _ = (m : ℝ) ^ 4 * (1 / ((Q₀ + 1 : ℕ) : ℝ) - 1 / ((K + 1 : ℕ) : ℝ)) := by
            congr 1
            have htel := telescopio_Ioc (fun d : ℕ => 1 / (d : ℝ)) (n := Q₀) (K - Q₀)
            rw [← hj] at htel
            exact htel
        _ ≤ (m : ℝ) ^ 4 * (1 / ((Q₀ + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
        _ = (m : ℝ) ^ 4 / ((Q₀ : ℝ) + 1) := by push_cast; ring
    linarith

/-- Cota superior incondicional puntual `Δ_hip(m) ≤ m⁴` para todo `m ≥ 1`. -/
theorem discrepanciaHiperbolica_le_m4 {m : ℕ} (hm : 1 ≤ m) :
    discrepanciaHiperbolica m ≤ (m : ℝ) ^ 4 := by
  have h := truncamiento_cola_discrepanciaHiperbolica (Q₀ := 0) hm (Nat.zero_le _)
  simpa using h

/-- **Cota incondicional global sin hipótesis externas:**
`S_hiperbolica Y ≤ Y^{3/4}` para toda escala `Y ≥ 1`. -/
theorem cota_incondicional_S_hiperbolica {Y : ℝ} (hY : 1 ≤ Y) :
    S_hiperbolica Y ≤ Y ^ (3 / 4 : ℝ) := by
  have hY_pos : 0 < Y := lt_of_lt_of_le one_pos hY
  unfold S_hiperbolica
  set N_top : ℕ := ⌊Y ^ (3 / 8 : ℝ)⌋₊
  have hterm : ∀ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
      max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3 ≤ Y ^ (3 / 8 : ℝ) := by
    intro m hm
    have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm_Icc.1
    have hmax : max (discrepanciaHiperbolica m) 0 ≤ (m : ℝ) ^ 4 :=
      max_le (discrepanciaHiperbolica_le_m4 hm_Icc.1) (by positivity)
    calc max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3
        ≤ (m : ℝ) ^ 4 / (m : ℝ) ^ 3 := div_le_div_of_nonneg_right hmax (by positivity)
      _ = (m : ℝ) := by have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'; field_simp
      _ ≤ (N_top : ℝ) := by exact_mod_cast hm_Icc.2
      _ ≤ Y ^ (3 / 8 : ℝ) := Nat.floor_le (by positivity)
  calc ∑ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
        max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3
      ≤ ∑ _m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
        Y ^ (3 / 8 : ℝ) := Finset.sum_le_sum hterm
    _ ≤ ∑ _m ∈ Finset.Icc 1 N_top, Y ^ (3 / 8 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    _ = (N_top : ℝ) * Y ^ (3 / 8 : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ Y ^ (3 / 8 : ℝ) * Y ^ (3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
    _ = Y ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hY_pos]
        congr 1; norm_num

/-! ### 3. Calibración general en `θ ∈ [1/2, 1)` bajo `SinCerosDerecha θ` -/

/-- Bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`), para todo `η > 0` existe un umbral `Y₁` tal que
`S_hiperbolica Y ≤ S_AMate Y ≤ Y^{(3/2)(θ − 1/2) + η}` para todo `Y ≥ Y₁`. -/
theorem cota_S_hiperbolica_de_sin_ceros_theta {θ : ℝ} (hθ12 : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hZ : SinCerosDerecha θ) :
    ∀ η : ℝ, 0 < η → ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y →
      S_hiperbolica Y ≤ Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + η) := by
  intro η hη
  set u : ℝ := min (η / 6) ((1 - θ) / 2)
  have hu_pos : 0 < u := lt_min (by positivity) (by linarith)
  have hσ_gt : θ < θ + u := by linarith
  have hσ_lt : θ + u < 1 := by simp only [u]; linarith [min_le_right (η / 6) ((1 - θ) / 2)]
  have h3u : 3 * u / 2 ≤ η / 4 := by
    have : u ≤ η / 6 := min_le_left _ _
    linarith
  obtain ⟨CG, hCG0, hCG⟩ := cota_G_vonMangoldt_de_sin_ceros hθ12 hσ_gt hσ_lt hZ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K_coef : ℝ := CG * (6 / η) + (10 + 16 / Real.log 2) * (6 / η) ^ 3 + 1
  have hK_pos : 0 < K_coef := by simp only [K_coef]; positivity
  set Y₁ : ℝ := max 16 (K_coef ^ (2 / η))
  refine ⟨Y₁, fun Y hYY₁ => ?_⟩
  have hY16 : 16 ≤ Y := (le_max_left _ _).trans hYY₁
  have hYK : K_coef ^ (2 / η) ≤ Y := (le_max_right _ _).trans hYY₁
  have hY_pos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  refine (cota_bilateral_S_AMate_S_hiperbolica hY1).1.trans ?_
  set N_top : ℕ := ⌊Y ^ (3 / 8 : ℝ)⌋₊
  unfold S_AMate
  set B_fac : ℝ := CG * Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2)
    + (10 + 16 / Real.log 2) * (Real.log Y) ^ 2
  have hB_nn : 0 ≤ B_fac := by simp only [B_fac]; positivity
  have hterm_le : ∀ m ∈ (Finset.Icc 1 N_top).filter
        (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
      max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ B_fac * (1 / (m : ℝ)) := by
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
    have hG_m4 : G_vonMangoldt ((m : ℝ) ^ 4)
        ≤ CG * Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2) * (m : ℝ) ^ 2 := by
      have h1 := (le_abs_self _).trans (hCG ((m : ℝ) ^ 4) hm4_ge1)
      have hrp : ((m : ℝ) ^ 4) ^ (θ + u) = (m : ℝ) ^ 2 * ((m : ℝ) ^ 4) ^ ((θ - 1 / 2) + u) := by
        have hexp_eq : θ + u = (1 / 2 : ℝ) + ((θ - 1 / 2) + u) := by ring
        rw [hexp_eq, Real.rpow_add hm4_pos, ← Real.sqrt_eq_rpow, hsqrt_m4]
      have hu_Y : ((m : ℝ) ^ 4) ^ ((θ - 1 / 2) + u)
          ≤ Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2) := by
        calc ((m : ℝ) ^ 4) ^ ((θ - 1 / 2) + u)
            ≤ (Y ^ (3 / 2 : ℝ)) ^ ((θ - 1 / 2) + u) :=
              Real.rpow_le_rpow hm4_pos.le hm_Y32 (by linarith)
          _ = Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2) := by
              rw [← Real.rpow_mul hY_pos.le]; congr 1; ring
      calc G_vonMangoldt ((m : ℝ) ^ 4)
          ≤ CG * ((m : ℝ) ^ 4) ^ (θ + u) := h1
        _ = CG * ((m : ℝ) ^ 2 * ((m : ℝ) ^ 4) ^ ((θ - 1 / 2) + u)) := by rw [hrp]
        _ ≤ CG * ((m : ℝ) ^ 2 * Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_Y (by positivity)) hCG0
        _ = CG * Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2) * (m : ℝ) ^ 2 := by ring
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
        ≤ B_fac * (m : ℝ) ^ 2 := by
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
      have hexp_rhs : B_fac * (m : ℝ) ^ 2
          = CG * Y ^ ((3 / 2 : ℝ) * (θ - 1 / 2) + 3 * u / 2) * (m : ℝ) ^ 2
            + 10 * ((Real.log Y) ^ 2 * (m : ℝ) ^ 2)
            + (16 / Real.log 2) * (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by
        simp only [B_fac]; ring
      have hpos_prod : 0 ≤ (Real.log Y) ^ 2 * (m : ℝ) ^ 2 := by positivity
      linarith
    calc max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ (B_fac * (m : ℝ) ^ 2) / (m : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right hnum_bd (by positivity)
      _ = B_fac * (1 / (m : ℝ)) := by have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'; field_simp
  have hN1 : 1 ≤ N_top :=
    Nat.le_floor (by exact_mod_cast Real.one_le_rpow hY1 (by norm_num : (0 : ℝ) ≤ 3 / 8))
  have hharm : ∑ m ∈ Finset.Icc 1 N_top, (1 / (m : ℝ)) ≤ Real.log Y := by
    have h1 := sum_inv_Icc_le hN1
    have hN_pos : (0 : ℝ) < N_top := by exact_mod_cast hN1
    have h2 : Real.log (N_top : ℝ) ≤ (3 / 8 : ℝ) * Real.log Y :=
      (Real.log_le_log hN_pos (Nat.floor_le (by positivity))).trans_eq
        (Real.log_rpow hY_pos (3 / 8 : ℝ))
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
  let F_win : Finset ℕ := (Finset.Icc 1 N_top).filter
    (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ))
  have hsum_le : ∑ m ∈ F_win,
        max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
      ≤ B_fac * Real.log Y := by
    calc ∑ m ∈ F_win,
          max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ ∑ _m ∈ F_win, B_fac * (1 / (_m : ℝ)) := Finset.sum_le_sum hterm_le
      _ ≤ ∑ m ∈ Finset.Icc 1 N_top, B_fac * (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = B_fac * ∑ m ∈ Finset.Icc 1 N_top, (1 / (m : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ B_fac * Real.log Y := mul_le_mul_of_nonneg_left hharm hB_nn
  have hlog_u : Real.log Y ≤ (6 / η) * Y ^ (η / 6) := by
    have h1 := Real.log_le_rpow_div hY_pos.le (show 0 < η / 6 by positivity)
    have heq : Y ^ (η / 6) / (η / 6) = (6 / η) * Y ^ (η / 6) := by field_simp
    linarith
  have hlogY_nn : 0 ≤ Real.log Y := Real.log_nonneg hY1
  set α_θ : ℝ := (3 / 2 : ℝ) * (θ - 1 / 2)
  have hα_nn : 0 ≤ α_θ := by simp only [α_θ]; linarith
  have hlog3 : (Real.log Y) ^ 3 ≤ (6 / η) ^ 3 * Y ^ (α_θ + η / 2) := by
    calc (Real.log Y) ^ 3 ≤ ((6 / η) * Y ^ (η / 6)) ^ 3 :=
          pow_le_pow_left₀ hlogY_nn hlog_u 3
      _ = (6 / η) ^ 3 * (Y ^ (η / 6)) ^ 3 := mul_pow _ _ 3
      _ = (6 / η) ^ 3 * Y ^ (η / 2) := by
          congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hY_pos.le]; congr 1; push_cast; ring
      _ ≤ (6 / η) ^ 3 * Y ^ (α_θ + η / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) (by positivity)
  have hY_term1 : Y ^ (α_θ + 3 * u / 2) * Real.log Y ≤ (6 / η) * Y ^ (α_θ + η / 2) := by
    calc Y ^ (α_θ + 3 * u / 2) * Real.log Y
        ≤ Y ^ (α_θ + 3 * u / 2) * ((6 / η) * Y ^ (η / 6)) :=
          mul_le_mul_of_nonneg_left hlog_u (Real.rpow_nonneg hY_pos.le _)
      _ = (6 / η) * (Y ^ (α_θ + 3 * u / 2) * Y ^ (η / 6)) := by ring
      _ = (6 / η) * Y ^ (α_θ + 3 * u / 2 + η / 6) := by rw [← Real.rpow_add hY_pos]
      _ ≤ (6 / η) * Y ^ (α_θ + η / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) (by positivity)
  have hB_le_K : B_fac * Real.log Y ≤ K_coef * Y ^ (α_θ + η / 2) := by
    have hexpand : B_fac * Real.log Y
        = CG * (Y ^ (α_θ + 3 * u / 2) * Real.log Y) + (10 + 16 / Real.log 2) * (Real.log Y) ^ 3 := by
      simp only [B_fac, α_θ]; ring
    rw [hexpand]
    have h1 := mul_le_mul_of_nonneg_left hY_term1 hCG0
    have h2 := mul_le_mul_of_nonneg_left hlog3 (show 0 ≤ 10 + 16 / Real.log 2 by positivity)
    have hY_nn : 0 ≤ Y ^ (α_θ + η / 2) := Real.rpow_nonneg hY_pos.le _
    have hexp_K : K_coef * Y ^ (α_θ + η / 2)
        = CG * ((6 / η) * Y ^ (α_θ + η / 2))
          + (10 + 16 / Real.log 2) * ((6 / η) ^ 3 * Y ^ (α_θ + η / 2))
          + Y ^ (α_θ + η / 2) := by
      simp only [K_coef]; ring
    linarith
  have hK_le_Y : K_coef ≤ Y ^ (η / 2) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hK_pos.le _) hYK (half_pos hη).le
    rw [← Real.rpow_mul hK_pos.le, show (2 / η) * (η / 2) = 1 by field_simp,
      Real.rpow_one] at h1
    exact h1
  have hfinal : Y ^ (η / 2) * Y ^ (α_θ + η / 2) = Y ^ (α_θ + η) := by
    rw [← Real.rpow_add hY_pos]; congr 1; ring
  exact hsum_le.trans (hB_le_K.trans
    ((mul_le_mul_of_nonneg_right hK_le_Y (Real.rpow_nonneg hY_pos.le _)).trans_eq hfinal))

/-! ### 4. Teorema de barrera: por qué monotonía + regiones libres de ceros clásicas no bastan -/

/-- Perturbación modelo `E_β(t) = −t^β` (`1/2 < β < 1`). -/
noncomputable def ondaPrueba (β t : ℝ) : ℝ := -(t ^ β)

/-- Constante explícita estrictamente positiva `c_β = (1/2) (1 − (3/2)^{−β})`. -/
noncomputable def constanteBarrera (β : ℝ) : ℝ := (1 / 2 : ℝ) * (1 - (3 / 2 : ℝ) ^ (-β))

theorem constanteBarrera_pos {β : ℝ} (hβ : 0 < β) : 0 < constanteBarrera β := by
  unfold constanteBarrera
  have hlt1 : (3 / 2 : ℝ) ^ (-β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

/-- **Propiedad 1 de la perturbación de barrera:**
para todo `0 < β < 1`, la función tipo Chebyshev `t + E_β(t) = t − t^β` es estrictamente creciente
en `[1, ∞)`. -/
theorem strictMonoOn_id_add_ondaPrueba {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StrictMonoOn (fun t : ℝ => t + ondaPrueba β t) (Ici 1) := by
  have hfun : (fun t : ℝ => t + ondaPrueba β t) = (fun t : ℝ => t - t ^ β) := by
    funext t; unfold ondaPrueba; ring
  rw [hfun]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · exact continuousOn_id.sub (continuousOn_id.rpow_const fun t ht =>
      Or.inl (lt_of_lt_of_le one_pos ht).ne')
  · intro t ht
    rw [interior_Ici] at ht
    have ht_pos : 0 < t := lt_trans one_pos ht
    have hd : HasDerivAt (fun x : ℝ => x - x ^ β) (1 - β * t ^ (β - 1)) t :=
      (hasDerivAt_id' t).sub (Real.hasDerivAt_rpow_const (p := β) (Or.inl ht_pos.ne'))
    rw [hd.deriv]
    have hpow_le : t ^ (β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)
    nlinarith

/-- **Propiedad 2 (cota inferior del operador de cuadratura):**
para todo `β > 0` y todo entero `m ≥ 2`, `𝒬_m(E_β) ≥ c_β · m^{4β}`. -/
theorem operadorCuadratura_ondaPrueba_ge {β : ℝ} (hβ0 : 0 < β) {m : ℕ} (hm2 : 2 ≤ m) :
    constanteBarrera β * (m : ℝ) ^ (4 * β) ≤ operadorCuadratura (ondaPrueba β) m := by
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm4_pos : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  have hint : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
      IntervalIntegrable (fun u : ℝ => ondaPrueba β ((m : ℝ) ^ 4 / u))
        volume (q : ℝ) ((q + 1 : ℕ) : ℝ) := by
    intro q hq
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hle : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by push_cast; linarith
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    unfold ondaPrueba
    refine (ContinuousOn.rpow_const ?_ ?_).neg
    · exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hq_pos hu.1).ne'
    · intro u hu; exact Or.inr hβ0.le
  rw [operadorCuadratura_eq_suma_zonas hm1 hint]
  -- Todos los sumandos `q ∈ [1, m² − 1]` son no negativos.
  have hterm_nn : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
      0 ≤ ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
            (ondaPrueba β ((m : ℝ) ^ 4 / u) - ondaPrueba β ((m : ℝ) ^ 4 / (q : ℝ))) := by
    intro q hq
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hle : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by push_cast; linarith
    refine intervalIntegral.integral_nonneg hle fun u hu => ?_
    have hu_ge : (q : ℝ) ≤ u := hu.1
    unfold ondaPrueba
    have hdiv_le : (m : ℝ) ^ 4 / u ≤ (m : ℝ) ^ 4 / (q : ℝ) :=
      div_le_div_of_nonneg_left hm4_pos.le hq_pos hu_ge
    have hrpow_le := Real.rpow_le_rpow (div_nonneg hm4_pos.le (lt_of_lt_of_le hq_pos hu_ge).le)
      hdiv_le hβ0.le
    linarith
  -- Aislamos el sumando `q = 1 ∈ Icc 1 (m² − 1)`.
  have h1_mem : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1) := by
    rw [Finset.mem_Icc]
    have hm2_ge4 : 4 ≤ m ^ 2 := by nlinarith
    exact ⟨le_rfl, by omega⟩
  have hge_q1 : (∫ u in (1 : ℝ)..(2 : ℝ),
        (ondaPrueba β ((m : ℝ) ^ 4 / u) - ondaPrueba β ((m : ℝ) ^ 4 / 1)))
      ≤ ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
          ∫ u in (q : ℝ)..((q + 1 : ℕ) : ℝ),
            (ondaPrueba β ((m : ℝ) ^ 4 / u) - ondaPrueba β ((m : ℝ) ^ 4 / (q : ℝ))) := by
    have h := Finset.single_le_sum hterm_nn h1_mem
    norm_num at h ⊢
    exact h
  -- En `q = 1`, dividimos `[1, 2]` en `[1, 3/2]` y `[3/2, 2]`.
  let g₁ : ℝ → ℝ := fun u => ondaPrueba β ((m : ℝ) ^ 4 / u) - ondaPrueba β ((m : ℝ) ^ 4 / 1)
  have hg₁_cont : ContinuousOn g₁ (Icc 1 2) := by
    dsimp only [g₁]; unfold ondaPrueba
    refine (ContinuousOn.rpow_const ?_ (fun _ _ => Or.inr hβ0.le)).neg.sub continuousOn_const
    exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le one_pos hu.1).ne'
  have hint_1_32 : IntervalIntegrable g₁ volume 1 (3 / 2) :=
    (hg₁_cont.mono (by intro u hu; rw [uIcc_of_le (by norm_num)] at hu; exact ⟨hu.1, by linarith [hu.2]⟩)).intervalIntegrable
  have hint_32_2 : IntervalIntegrable g₁ volume (3 / 2) 2 :=
    (hg₁_cont.mono (by intro u hu; rw [uIcc_of_le (by norm_num)] at hu; exact ⟨by linarith [hu.1], hu.2⟩)).intervalIntegrable
  have hsplit_12 := (integral_add_adjacent_intervals hint_1_32 hint_32_2).symm
  have hleft_nn : 0 ≤ ∫ u in (1 : ℝ)..(3 / 2 : ℝ), g₁ u := by
    refine integral_nonneg (by norm_num) fun u hu => ?_
    dsimp only [g₁]; unfold ondaPrueba
    have hdiv_le : (m : ℝ) ^ 4 / u ≤ (m : ℝ) ^ 4 / 1 :=
      div_le_div_of_nonneg_left hm4_pos.le one_pos hu.1
    have hrpow_le := Real.rpow_le_rpow (div_nonneg hm4_pos.le (lt_of_lt_of_le one_pos hu.1).le)
      hdiv_le hβ0.le
    linarith
  have hright_ge : constanteBarrera β * (m : ℝ) ^ (4 * β) ≤ ∫ u in (3 / 2 : ℝ)..(2 : ℝ), g₁ u := by
    have hpt : ∀ u ∈ Icc (3 / 2 : ℝ) 2,
        (1 - (3 / 2 : ℝ) ^ (-β)) * (m : ℝ) ^ (4 * β) ≤ g₁ u := by
      intro u hu
      have hu_pos : 0 < u := by linarith [hu.1]
      dsimp only [g₁]; unfold ondaPrueba
      have hfactor : ((m : ℝ) ^ 4 / u) ^ β = (m : ℝ) ^ (4 * β) * u ^ (-β) := by
        rw [Real.div_rpow hm4_pos.le hu_pos.le, ← Real.rpow_natCast (m : ℝ) 4,
          ← Real.rpow_mul hm_pos.le, Real.rpow_neg hu_pos.le, div_eq_mul_inv]
        push_cast; ring_nf
      have hfactor1 : ((m : ℝ) ^ 4 / 1) ^ β = (m : ℝ) ^ (4 * β) := by
        rw [div_one, ← Real.rpow_natCast (m : ℝ) 4, ← Real.rpow_mul hm_pos.le]
        push_cast; ring_nf
      have hu_neg_le : u ^ (-β) ≤ (3 / 2 : ℝ) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hu.1 (by linarith)
      rw [hfactor, hfactor1]
      have h1 : -((m : ℝ) ^ (4 * β) * u ^ (-β)) - -(m : ℝ) ^ (4 * β)
          = (1 - u ^ (-β)) * (m : ℝ) ^ (4 * β) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hmono := integral_mono_on (by norm_num : (3 / 2 : ℝ) ≤ 2)
      intervalIntegrable_const hint_32_2 hpt
    rw [intervalIntegral.integral_const] at hmono
    have hlen : ((2 : ℝ) - 3 / 2) • ((1 - (3 / 2 : ℝ) ^ (-β)) * (m : ℝ) ^ (4 * β))
        = constanteBarrera β * (m : ℝ) ^ (4 * β) := by
      unfold constanteBarrera; rw [smul_eq_mul]; ring
    linarith
  linarith

/-- **Teorema de explosión en ventanas `[Y, Y^{3/2}]` (barrera para `S_hiperbolica`):**
para todo `β ∈ (1/2, 1)` y todo `0 < η < (3/2)(β − 1/2)`, existe `Y₁` tal que para **toda** escala
`Y ≥ Y₁` la suma en ventanas de `𝒬_m(E_β)` viola estrictamente la cota `Y^η`:
`Y^η < ∑_{Y ≤ m⁴ ≤ Y^{3/2}} max(𝒬_m(E_β), 0) / m³`. -/
theorem explosion_ventana_ondaPrueba {β η : ℝ} (hβ12 : 1 / 2 < β) (hβ1 : β < 1)
    (hη_lt : η < (3 / 2 : ℝ) * (β - 1 / 2)) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y →
      Y ^ η < ∑ m ∈ (Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊).filter
          (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
        max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 := by
  have hβ0 : 0 < β := by linarith
  have hc_pos : 0 < constanteBarrera β := constanteBarrera_pos hβ0
  set δ_gap : ℝ := (3 / 2 : ℝ) * (β - 1 / 2) - η
  have hδ_pos : 0 < δ_gap := by simp only [δ_gap]; linarith
  set C_low : ℝ := constanteBarrera β / (4 * (2 : ℝ) ^ (4 * β))
  have hC_pos : 0 < C_low := by simp only [C_low]; positivity
  set Y₁ : ℝ := max (2 ^ 16 : ℝ) ((2 / C_low) ^ (1 / δ_gap))
  refine ⟨Y₁, fun Y hYY₁ => ?_⟩
  have hY216 : (2 ^ 16 : ℝ) ≤ Y := (le_max_left _ _).trans hYY₁
  have hYC : (2 / C_low) ^ (1 / δ_gap) ≤ Y := (le_max_right _ _).trans hYY₁
  have hY_pos : 0 < Y := by positivity
  have hY1 : 1 ≤ Y := by linarith [show (1 : ℝ) ≤ 2 ^ 16 by norm_num]
  -- Rango mitad superior `M₁ = ⌊Y^{3/8} / 2⌋₊ + 1` hasta `M₂ = ⌊Y^{3/8}⌋₊`.
  set X_38 : ℝ := Y ^ (3 / 8 : ℝ)
  have hX_ge64 : 64 ≤ X_38 := by
    have h1 : ((2 : ℝ) ^ 16) ^ (3 / 8 : ℝ) = 64 := by
      rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hY216 (by norm_num)
  set M₁ : ℕ := ⌊X_38 / 2⌋₊ + 1
  set M₂ : ℕ := ⌊X_38⌋₊
  have hM₁_gt : X_38 / 2 < (M₁ : ℝ) := by
    simp only [M₁]; exact_mod_cast Nat.lt_floor_add_one (X_38 / 2)
  have hM₂_le : (M₂ : ℝ) ≤ X_38 := Nat.floor_le (by positivity)
  have hM₂_gt : X_38 - 1 < (M₂ : ℝ) := by
    have h := Nat.lt_floor_add_one X_38
    linarith
  have hM₁_le_r : (M₁ : ℝ) ≤ X_38 / 2 + 1 := by
    simp only [M₁]; push_cast
    linarith [Nat.floor_le (show 0 ≤ X_38 / 2 by positivity)]
  have hM₁_le_M₂ : M₁ ≤ M₂ := by
    have : (M₁ : ℝ) < (M₂ : ℝ) + 1 := by linarith
    have hnat : M₁ < M₂ + 1 := by exact_mod_cast this
    omega
  -- Todos los enteros `m ∈ Icc M₁ M₂` pertenecen a la ventana cuártica `Y ≤ m⁴ ≤ Y^{3/2}`.
  let W_set : Finset ℕ := (Finset.Icc 1 M₂).filter
    (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ))
  have hsub_W : Finset.Icc M₁ M₂ ⊆ W_set := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := by
      have : (32 : ℝ) < (M₁ : ℝ) := by linarith
      have hM1_gt : 32 < M₁ := by exact_mod_cast this
      omega
    have hm_ge_half : X_38 / 2 ≤ (m : ℝ) := hM₁_gt.le.trans (by exact_mod_cast hm.1)
    have hm_le_X : (m : ℝ) ≤ X_38 := (show (m : ℝ) ≤ M₂ by exact_mod_cast hm.2).trans hM₂_le
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm.2⟩, ?_, ?_⟩
    · -- `Y ≤ (X_38 / 2)⁴ ≤ m⁴` porque `Y^{1/8} ≥ 4` para `Y ≥ 2^{16}`.
      have hY18 : 4 ≤ Y ^ (1 / 8 : ℝ) := by
        have h4 : ((2 : ℝ) ^ 16) ^ (1 / 8 : ℝ) = 4 := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [← h4]
        exact Real.rpow_le_rpow (by positivity) hY216 (by norm_num)
      have hX4 : (X_38 / 2) ^ 4 = Y ^ (3 / 2 : ℝ) / 16 := by
        rw [div_pow, show (2 : ℝ) ^ 4 = 16 by norm_num]
        congr 1
        simp only [X_38]
        rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hY_pos.le]
        congr 1; norm_num
      have hY_le_Y32 : Y * 16 ≤ Y ^ (3 / 2 : ℝ) := by
        have hY12 : 16 ≤ Y ^ (1 / 2 : ℝ) := by
          calc (16 : ℝ) ≤ (4 : ℝ) ^ 4 := by norm_num
            _ ≤ (Y ^ (1 / 8 : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hY18 4
            _ = Y ^ (1 / 2 : ℝ) := by
                rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hY_pos.le]
                congr 1; norm_num
        calc Y * 16 ≤ Y * Y ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hY12 hY_pos.le
          _ = Y ^ (1 : ℝ) * Y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = Y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hY_pos]; congr 1; norm_num
      calc Y ≤ Y ^ (3 / 2 : ℝ) / 16 := by linarith
        _ = (X_38 / 2) ^ 4 := hX4.symm
        _ ≤ (m : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hm_ge_half 4
    · calc (m : ℝ) ^ 4 ≤ X_38 ^ 4 := pow_le_pow_left₀ (by positivity) hm_le_X 4
        _ = Y ^ (3 / 2 : ℝ) := by
            simp only [X_38]
            rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hY_pos.le]
            congr 1; norm_num
  -- Cada `m ∈ Icc M₁ M₂` cumple `m ≥ 2` y aporta al menos `(c_β / 2^{4β}) Y^{(3/2)β − 9/8}`.
  have hterm_ge : ∀ m ∈ Finset.Icc M₁ M₂,
      (constanteBarrera β / (2 : ℝ) ^ (4 * β)) * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)
        ≤ max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm2 : 2 ≤ m := by
      have : (32 : ℝ) < (M₁ : ℝ) := by linarith
      have hM1_gt : 32 < M₁ := by exact_mod_cast this
      omega
    have hm_ge_half : X_38 / 2 ≤ (m : ℝ) := hM₁_gt.le.trans (by exact_mod_cast hm.1)
    have hm_le_X : (m : ℝ) ≤ X_38 := (show (m : ℝ) ≤ M₂ by exact_mod_cast hm.2).trans hM₂_le
    have hQ_ge := operadorCuadratura_ondaPrueba_ge hβ0 hm2
    have hm4β : (X_38 / 2) ^ (4 * β) ≤ (m : ℝ) ^ (4 * β) :=
      Real.rpow_le_rpow (by positivity) hm_ge_half (by positivity)
    have hX_pow : (X_38 / 2) ^ (4 * β) = Y ^ ((3 / 2 : ℝ) * β) / (2 : ℝ) ^ (4 * β) := by
      rw [Real.div_rpow (by positivity) (by norm_num)]
      congr 1
      simp only [X_38]
      rw [← Real.rpow_mul hY_pos.le]
      congr 1; ring
    have hm3_le : (m : ℝ) ^ 3 ≤ Y ^ (9 / 8 : ℝ) := by
      calc (m : ℝ) ^ 3 ≤ X_38 ^ 3 := pow_le_pow_left₀ (by positivity) hm_le_X 3
        _ = Y ^ (9 / 8 : ℝ) := by
            simp only [X_38]
            rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hY_pos.le]
            congr 1; norm_num
    have hm3_pos : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    calc (constanteBarrera β / (2 : ℝ) ^ (4 * β)) * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)
        = (constanteBarrera β * (Y ^ ((3 / 2 : ℝ) * β) / (2 : ℝ) ^ (4 * β))) / Y ^ (9 / 8 : ℝ) := by
            rw [Real.rpow_sub hY_pos]; ring
      _ ≤ (constanteBarrera β * (m : ℝ) ^ (4 * β)) / (m : ℝ) ^ 3 := by
          refine div_le_div₀ (by positivity) ?_ hm3_pos hm3_le
          rw [← hX_pow]
          exact mul_le_mul_of_nonneg_left hm4β hc_pos.le
      _ ≤ max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (hQ_ge.trans (le_max_left _ _)) hm3_pos.le
  -- El cardinal de `Icc M₁ M₂` es al menos `X_38 / 4`.
  have hcard_ge : X_38 / 4 ≤ ((Finset.Icc M₁ M₂).card : ℝ) := by
    rw [Nat.card_Icc]
    have hsub_nat : ((M₂ + 1 - M₁ : ℕ) : ℝ) = (M₂ : ℝ) + 1 - (M₁ : ℝ) := by
      rw [Nat.cast_sub (by omega : M₁ ≤ M₂ + 1)]
      push_cast; ring
    rw [hsub_nat]
    linarith
  have hsum_ge : C_low * Y ^ ((3 / 2 : ℝ) * (β - 1 / 2))
      ≤ ∑ m ∈ W_set, max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 := by
    calc C_low * Y ^ ((3 / 2 : ℝ) * (β - 1 / 2))
        = (X_38 / 4) * ((constanteBarrera β / (2 : ℝ) ^ (4 * β))
            * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)) := by
            simp only [C_low, X_38]
            have hexp : Y ^ (3 / 8 : ℝ) * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)
                = Y ^ ((3 / 2 : ℝ) * (β - 1 / 2)) := by
              rw [← Real.rpow_add hY_pos]; congr 1; ring
            calc (constanteBarrera β / (4 * (2 : ℝ) ^ (4 * β))) * Y ^ ((3 / 2 : ℝ) * (β - 1 / 2))
                = (constanteBarrera β / (4 * (2 : ℝ) ^ (4 * β)))
                    * (Y ^ (3 / 8 : ℝ) * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)) := by rw [hexp]
              _ = (Y ^ (3 / 8 : ℝ) / 4) * ((constanteBarrera β / (2 : ℝ) ^ (4 * β))
                    * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)) := by ring
      _ ≤ ((Finset.Icc M₁ M₂).card : ℝ) * ((constanteBarrera β / (2 : ℝ) ^ (4 * β))
            * Y ^ ((3 / 2 : ℝ) * β - 9 / 8)) :=
          mul_le_mul_of_nonneg_right hcard_ge (by positivity)
      _ = ∑ _m ∈ Finset.Icc M₁ M₂,
            (constanteBarrera β / (2 : ℝ) ^ (4 * β)) * Y ^ ((3 / 2 : ℝ) * β - 9 / 8) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.Icc M₁ M₂,
            max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 :=
          Finset.sum_le_sum hterm_ge
      _ ≤ ∑ m ∈ W_set, max (operadorCuadratura (ondaPrueba β) m) 0 / (m : ℝ) ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_W fun _ _ _ =>
            div_nonneg (le_max_right _ _) (by positivity)
  -- Como `Y ≥ (2 / C_low)^{1 / δ_gap}`, `Y^η < 2 Y^η ≤ C_low Y^{η + δ_gap}`.
  have hYδ : 2 / C_low ≤ Y ^ δ_gap := by
    have hbase_nn : 0 ≤ 2 / C_low := by positivity
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hbase_nn _) hYC hδ_pos.le
    rw [← Real.rpow_mul hbase_nn, show (1 / δ_gap) * δ_gap = 1 by field_simp,
      Real.rpow_one] at h1
    exact h1
  have h2_le : 2 ≤ C_low * Y ^ δ_gap := by
    have := mul_le_mul_of_nonneg_left hYδ hC_pos.le
    have hcancel : C_low * (2 / C_low) = 2 := mul_div_cancel₀ 2 hC_pos.ne'
    linarith
  have hYη_pos : 0 < Y ^ η := Real.rpow_pos_of_pos hY_pos η
  have hlt_prod : Y ^ η < C_low * Y ^ ((3 / 2 : ℝ) * (β - 1 / 2)) := by
    calc Y ^ η < 2 * Y ^ η := by linarith
      _ ≤ (C_low * Y ^ δ_gap) * Y ^ η := mul_le_mul_of_nonneg_right h2_le hYη_pos.le
      _ = C_low * (Y ^ δ_gap * Y ^ η) := by ring
      _ = C_low * Y ^ (δ_gap + η) := by rw [← Real.rpow_add hY_pos]
      _ = C_low * Y ^ ((3 / 2 : ℝ) * (β - 1 / 2)) := by simp only [δ_gap]; congr 2; ring
  exact hlt_prod.trans_le hsum_ge

/-- **Corolario condicional con Alpöge (interfaz lista para `Composicion`):**
toda demostración de `RiemannHypothesis` (en particular `Main.riemannHypothesis` de Alpöge una vez
finalice la compilación en Google Colab) descarga inmediatamente `S_hiperbolica Y ≤ Y^η` de manera
uniforme a partir de un umbral `Y₁(η)`. -/
theorem S_hiperbolica_uniforme_de_rh (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0 < η → ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → S_hiperbolica Y ≤ Y ^ η := by
  intro η hη
  obtain ⟨Y₁, hY₁⟩ := deficit_primos_uniforme_de_rh hRH η hη
  refine ⟨max Y₁ 1, fun Y hY => ?_⟩
  exact (cota_bilateral_S_AMate_S_hiperbolica ((le_max_right Y₁ 1).trans hY)).1.trans
    (hY₁ Y ((le_max_left Y₁ 1).trans hY))

end AMate
