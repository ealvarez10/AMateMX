import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import AMateEnergia.EquivalenciaVentanas
import AMateEnergia.DeficitPrimos

/-!
# Ruta B: estructura modular exacta y discrepancia hiperbólica de `A_primos(m⁴)`

Investigación y formalización completa en Lean 4 (solo Mathlib, cero `sorry`) del problema
aritmético directo de la Ruta B (`AMate.rh_de_deficit_primos`) sobre partes fraccionarias de primos
grandes `A_primos(x) = ∑_{√x < p ≤ x} (log p)(1 − {x/p})`:

1. **Estructura modular y brecha de Euler–Mascheroni (`fract_div_nat_eq_mod`,
   `cota_inferior_uno_menos_fract_nat`, `media_periodo_uno_menos_fract`,
   `brecha_media_euler_mascheroni`):**
   * para todo entero `N : ℕ` y divisor `d > 0`, `{N / d} = (N % d) / d` y `1 − {N / d} ≥ 1 / d`;
   * el promedio exacto de `1 − {(a + j)/d}` sobre un período completo de `d` enteros consecutivos
     vale `1/2 + 1/(2d) → 1/2`, mientras que `γ_E > 1/2`: por tanto, la equidistribución ingenua de
     residuos módulo `p` no basta por sí sola; el exceso `(γ_E − 1/2) x ≈ 0,0772 x` proviene de las
     zonas hiperbólicas donde el cociente entero `q = ⌊x / p⌋` es pequeño.
2. **Identidad hiperbólica exacta sin término de error (`identidad_hiperbolica_A_primos`):**
   definiendo la función de Chebyshev sobre primos `thetaChebyshev t = ∑_{p ≤ t} log p`, para
   **todo** entero `m ≥ 1` se cumple con igualdad exacta (cero constantes asintóticas y cero restos):
   `A_primos(m⁴) = ∑_{q=1}^{m² − 1} ϑ(m⁴ / q) − m⁴ ∫_{m²}^{m⁴} (ϑ(t) / t²) dt`.
3. **Reducción exacta a la discrepancia hiperbólica de Chebyshev (`discrepanciaHiperbolica`,
   `cota_bilateral_deficit_discrepancia`, `cota_bilateral_S_AMate_S_hiperbolica`,
   `rh_iff_S_hiperbolica`):**
   escribiendo `ϑ(t) = t + E_ϑ(t)` (`errorChebyshev t = ϑ(t) − t`), los términos principales
   `m⁴ log(m²)` se cancelan idénticamente y la constante `γ_E m⁴` emerge de la serie armónica
   `H_{m²} − log(m²) → γ_E`, dejando para todo `m ≥ 1` la desigualdad bilateral exacta
   `Δ_hip(m) ≤ γ_E m⁴ − A_primos(m⁴) ≤ Δ_hip(m) + m²`,
   donde `Δ_hip(m) = m⁴ ∫_{m²}^{m⁴} (E_ϑ(t) / t²) dt − ∑_{q=1}^{m² − 1} E_ϑ(m⁴ / q)`.
   En consecuencia, `S_hiperbolica Y ≤ S_AMate Y ≤ S_hiperbolica Y + (1 + log Y)` para todo `Y ≥ 1`,
   y `RiemannHypothesis` equivale exactamente a la cota cofinal `S_hiperbolica Y ≤ Y^η`.
-/

open Complex MeasureTheory Set Filter Metric Topology intervalIntegral

namespace AMate

/-! ### 1. Leyes modulares exactas de `{N / d}` y brecha `γ_E > 1/2` -/

/-- Para `N : ℕ` y `d > 0`, la parte fraccionaria `{N / d}` es exactamente `(N % d) / d`. -/
theorem fract_div_nat_eq_mod (N : ℕ) {d : ℕ} (hd : 0 < d) :
    Int.fract ((N : ℝ) / (d : ℝ)) = ((N % d : ℕ) : ℝ) / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv_nn : 0 ≤ (N : ℝ) / (d : ℝ) := div_nonneg (Nat.cast_nonneg N) hd_pos.le
  have hfl := cast_natFloor_eq_sub_fract hdiv_nn
  rw [natFloor_div_natCast (Nat.cast_nonneg N) d, Nat.floor_natCast] at hfl
  have hdm : d * (N / d) + N % d = N := Nat.div_add_mod N d
  have hdm_r : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hdm
  have hsub : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) = ((N % d : ℕ) : ℝ) / (d : ℝ) := by
    field_simp
    linarith
  linarith

/-- Para todo entero `N : ℕ` y todo `d > 0`, `1 − {N / d} ≥ 1 / d`. -/
theorem cota_inferior_uno_menos_fract_nat (N : ℕ) {d : ℕ} (hd : 0 < d) :
    1 / (d : ℝ) ≤ 1 - Int.fract ((N : ℝ) / (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [fract_div_nat_eq_mod N hd]
  have hlt : N % d + 1 ≤ d := Nat.mod_lt N hd
  have hle_r : ((N % d : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hlt
  rw [le_sub_iff_add_le, ← add_div, div_le_one hd_pos]
  linarith

/-- Si `d ∣ N` (`d > 0`), entonces `1 − {N / d} = 1`. -/
theorem uno_menos_fract_dvd {N d : ℕ} (hd : 0 < d) (hdvd : d ∣ N) :
    1 - Int.fract ((N : ℝ) / (d : ℝ)) = 1 := by
  rw [fract_div_nat_eq_mod N hd, Nat.mod_eq_zero_of_dvd hdvd]
  simp

theorem dos_mul_sum_range_cast (d : ℕ) :
    2 * ∑ r ∈ Finset.range d, (r : ℝ) = (d : ℝ) * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- **Promedio exacto en un período completo módulo `d`:**
para cualquier inicio `a : ℕ` y cualquier `d > 0`, el promedio de `1 − {(a + j)/d}` sobre `d`
enteros consecutivos vale exactamente `1/2 + 1/(2d)`. -/
theorem media_periodo_uno_menos_fract (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (1 / (d : ℝ)) * ∑ j ∈ Finset.range d, (1 - Int.fract (((a + j : ℕ) : ℝ) / (d : ℝ)))
      = 1 / 2 + 1 / (2 * (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  let f : ℕ → ℕ := fun j => (a + j) % d
  have hinj : Set.InjOn f (Finset.range d) := by
    intro j₁ hj₁ j₂ hj₂ hfeq
    have h1 : j₁ < d := Finset.mem_coe.mp hj₁ |> Finset.mem_range.mp
    have h2 : j₂ < d := Finset.mem_coe.mp hj₂ |> Finset.mem_range.mp
    have hdiv1 := Nat.div_add_mod (a + j₁) d
    have hdiv2 := Nat.div_add_mod (a + j₂) d
    dsimp only [f] at hfeq
    rcases lt_trichotomy ((a + j₁) / d) ((a + j₂) / d) with hlt | heq | hgt
    · have hle : ((a + j₁) / d + 1) * d ≤ ((a + j₂) / d) * d := Nat.mul_le_mul_right d hlt
      have : d * ((a + j₁) / d) + d ≤ d * ((a + j₂) / d) := by nlinarith
      omega
    · rw [heq, hfeq] at hdiv1
      omega
    · have hle : ((a + j₂) / d + 1) * d ≤ ((a + j₁) / d) * d := Nat.mul_le_mul_right d hgt
      have : d * ((a + j₂) / d) + d ≤ d * ((a + j₁) / d) := by nlinarith
      omega
  have hsub : (Finset.range d).image f ⊆ Finset.range d := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨j, _, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  have himg_eq : (Finset.range d).image f = Finset.range d :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hsum_mod : ∑ j ∈ Finset.range d, ((f j : ℕ) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
    have h1 : ∑ j ∈ Finset.range d, ((f j : ℕ) : ℝ) = ∑ r ∈ Finset.range d, (r : ℝ) := by
      conv_rhs => rw [← himg_eq]
      rw [Finset.sum_image (f := fun r : ℕ => (r : ℝ)) hinj]
    rw [h1]
    linarith [dos_mul_sum_range_cast d]
  have hrew : ∑ j ∈ Finset.range d, (1 - Int.fract (((a + j : ℕ) : ℝ) / (d : ℝ)))
      = (d : ℝ) - (∑ j ∈ Finset.range d, ((f j : ℕ) : ℝ)) / (d : ℝ) := by
    have hcongr : ∀ j ∈ Finset.range d,
        1 - Int.fract (((a + j : ℕ) : ℝ) / (d : ℝ)) = 1 - ((f j : ℕ) : ℝ) / (d : ℝ) :=
      fun j _ => by rw [fract_div_nat_eq_mod (a + j) hd]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, ← Finset.sum_div]
  rw [hrew, hsum_mod]
  field_simp
  ring

/-- **Brecha estructural `γ_E > 1/2`:** el límite `1/2` del promedio uniforme de residuos es
estrictamente menor que `γ_E ≈ 0,5772`. -/
theorem brecha_media_euler_mascheroni : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
  Real.one_half_lt_eulerMascheroniConstant

/-! ### 2. Identidad hiperbólica exacta para `A_primos(m⁴)` -/

/-- Función primera de Chebyshev: `ϑ(t) = ∑_{p ≤ t, p primo} log p` (vale `0` para `t < 1`). -/
noncomputable def thetaChebyshev (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log (p : ℝ)

theorem monotone_thetaChebyshev : Monotone thetaChebyshev := by
  intro a b hab
  unfold thetaChebyshev
  by_cases hb0 : b < 0
  · have ha0 : a < 0 := lt_of_le_of_lt hab hb0
    rw [Nat.floor_of_nonpos ha0.le, Nat.floor_of_nonpos hb0.le]
  · push Not at hb0
    have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
    have hsub : (Finset.Icc 1 ⌊a⌋₊).filter Nat.Prime ⊆ (Finset.Icc 1 ⌊b⌋₊).filter Nat.Prime :=
      fun p hp => Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2.trans hfl⟩,
         (Finset.mem_filter.mp hp).2⟩
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)

theorem measurable_thetaChebyshev : Measurable thetaChebyshev :=
  monotone_thetaChebyshev.measurable

theorem integral_inv_sq_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 / t ^ 2)) = 1 / a - 1 / b := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun u : ℝ => (-1 : ℝ) * u⁻¹) (1 / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    have h1 := (hasDerivAt_inv ht0).const_mul (-1 : ℝ)
    exact h1.congr_deriv (by rw [neg_mul_neg, one_mul, one_div])
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
      pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [one_div]; ring

/-- **Identidad hiperbólica exacta de Ruta B (sin términos de error):**
para todo entero `m ≥ 1`,
`A_primos(m⁴) = ∑_{q=1}^{m² − 1} ϑ(m⁴ / q) − m⁴ ∫_{m²}^{m⁴} (ϑ(t) / t²) dt`. -/
theorem identidad_hiperbolica_A_primos {m : ℕ} (hm : 1 ≤ m) :
    A_primos ((m : ℝ) ^ 4)
      = (∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ)))
        - (m : ℝ) ^ 4 * ∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), thetaChebyshev t / t ^ 2 := by
  rcases eq_or_lt_of_le hm with rfl | hm_gt1
  · -- Caso `m = 1`: los tres miembros son `0`.
    have hA1 : A_primos 1 = 0 := by
      unfold A_primos
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx1 : x ≤ 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2.trans (by norm_num)
      exact absurd hx1 (not_le.mpr (Finset.mem_filter.mp hx).2.1.one_lt)
    push_cast
    simp [hA1]
  · -- Caso `m ≥ 2`.
    have hm2_pos : 0 < m ^ 2 := by positivity
    have hm2_ge4 : 4 ≤ m ^ 2 := by nlinarith
    have hm2_r_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hm4_r_pos : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
    have hm2_le_m4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
      pow_le_pow_right₀ (by exact_mod_cast hm) (by omega)
    let P_all : Finset ℕ := (Finset.Icc 1 (m ^ 4)).filter Nat.Prime
    let P_lo : Finset ℕ := P_all.filter (fun p : ℕ => p ≤ m ^ 2)
    let P_hi : Finset ℕ := P_all.filter (fun p : ℕ => ¬ p ≤ m ^ 2)
    -- Paso 1: intercambiar `∑_{q=1}^{m²-1} ϑ(m⁴/q)` con `∑_{p ∈ P_all}`.
    have hsum_q_eq : ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ))
        = (∑ p ∈ P_lo, ((m : ℝ) ^ 2 - 1) * Real.log (p : ℝ))
          + ∑ p ∈ P_hi, (((m ^ 4 / p : ℕ) : ℝ) * Real.log (p : ℝ)) := by
      have hterm_q : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1),
          thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ))
            = ∑ p ∈ P_all, if p ≤ m ^ 4 / q then Real.log (p : ℝ) else 0 := by
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        unfold thetaChebyshev
        have hfl_eq : ⌊(m : ℝ) ^ 4 / (q : ℝ)⌋₊ = m ^ 4 / q := by
          have h1 := natFloor_div_natCast (by positivity : (0 : ℝ) ≤ ((m ^ 4 : ℕ) : ℝ)) q
          rw [Nat.floor_natCast] at h1
          push_cast at h1
          exact h1
        rw [hfl_eq, ← Finset.sum_filter]
        congr 1
        ext p
        simp only [P_all, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp1, hpq⟩, hpr⟩
          exact ⟨⟨⟨hp1, hpq.trans (Nat.div_le_self _ _)⟩, hpr⟩, hpq⟩
        · rintro ⟨⟨⟨hp1, _⟩, hpr⟩, hpq⟩
          exact ⟨⟨hp1, hpq⟩, hpr⟩
      rw [Finset.sum_congr rfl hterm_q, Finset.sum_comm]
      have hp_count : ∀ p ∈ P_all,
          (∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), if p ≤ m ^ 4 / q then Real.log (p : ℝ) else 0)
            = if p ≤ m ^ 2 then ((m : ℝ) ^ 2 - 1) * Real.log (p : ℝ)
              else ((m ^ 4 / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
        intro p hp
        have hp_pr : Nat.Prime p := (Finset.mem_filter.mp hp).2
        have hp_pos : 0 < p := hp_pr.pos
        by_cases hplo : p ≤ m ^ 2
        · rw [if_pos hplo]
          have hall_q : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), p ≤ m ^ 4 / q := by
            intro q hq
            have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
            have hq_le : q ≤ m ^ 2 - 1 := (Finset.mem_Icc.mp hq).2
            rw [Nat.le_div_iff_mul_le hq_pos]
            calc p * q ≤ m ^ 2 * (m ^ 2 - 1) := Nat.mul_le_mul hplo hq_le
              _ ≤ m ^ 2 * m ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ = m ^ 4 := by ring
          rw [Finset.sum_congr rfl fun q hq => if_pos (hall_q q hq), Finset.sum_const,
            Nat.card_Icc, nsmul_eq_mul]
          have hsub_cast : (((m ^ 2 - 1 + 1 - 1 : ℕ) : ℝ)) = (m : ℝ) ^ 2 - 1 := by
            have h1 : m ^ 2 - 1 + 1 - 1 = m ^ 2 - 1 := by omega
            rw [h1, Nat.cast_sub (by omega : 1 ≤ m ^ 2)]
            push_cast; rfl
          rw [hsub_cast]
        · rw [if_neg hplo]
          have hdiv_le : m ^ 4 / p ≤ m ^ 2 - 1 := by
            have hlt : m ^ 4 / p < m ^ 2 := by
              rw [Nat.div_lt_iff_lt_mul hp_pos]
              have : m ^ 2 + 1 ≤ p := by omega
              calc m ^ 4 = m ^ 2 * m ^ 2 := by ring
                _ < m ^ 2 * p := Nat.mul_lt_mul_of_pos_left (by omega) hm2_pos
            omega
          have hiff_qp : ∀ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), (p ≤ m ^ 4 / q ↔ q ≤ m ^ 4 / p) := by
            intro q hq
            have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
            rw [Nat.le_div_iff_mul_le hq_pos, Nat.le_div_iff_mul_le hp_pos, mul_comm]
          have hfilt : (Finset.Icc (1 : ℕ) (m ^ 2 - 1)).filter (fun q => p ≤ m ^ 4 / q)
              = Finset.Icc 1 (m ^ 4 / p) := by
            ext q
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hq1, hq2⟩, hpq⟩
              exact ⟨hq1, (hiff_qp q (Finset.mem_Icc.mpr ⟨hq1, hq2⟩)).mp hpq⟩
            · rintro ⟨hq1, hqp⟩
              have hq2 : q ≤ m ^ 2 - 1 := hqp.trans hdiv_le
              exact ⟨⟨hq1, hq2⟩, (hiff_qp q (Finset.mem_Icc.mpr ⟨hq1, hq2⟩)).mpr hqp⟩
          rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc,
            Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hp_count,
        ← Finset.sum_filter_add_sum_filter_not P_all (fun p : ℕ => p ≤ m ^ 2)]
      congr 1
      · exact Finset.sum_congr rfl fun p hp => if_pos (Finset.mem_filter.mp hp).2
      · exact Finset.sum_congr rfl fun p hp => if_neg (Finset.mem_filter.mp hp).2
    -- Paso 2: calcular `m⁴ ∫_{m²}^{m⁴} (ϑ(t) / t²) dt` descomponiendo por primos `p ∈ P_all`.
    let g_p : ℕ → ℝ → ℝ := fun p t => if (p : ℝ) ≤ t then Real.log (p : ℝ) / t ^ 2 else 0
    have hg_int : ∀ p ∈ P_all, IntervalIntegrable (g_p p) volume ((m : ℝ) ^ 2) ((m : ℝ) ^ 4) := by
      intro p hp
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hm2_le_m4]
      have hmeas : Measurable (g_p p) :=
        Measurable.ite measurableSet_Ici (measurable_const.div (measurable_id.pow_const 2)) measurable_const
      have hdom : IntegrableOn (fun _ : ℝ => |Real.log (p : ℝ)| / ((m : ℝ) ^ 2) ^ 2)
          (Ioc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := integrableOn_const (hs := measure_Ioc_lt_top.ne)
      refine hdom.mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      dsimp only [g_p]
      split_ifs with hpt
      · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (lt_of_lt_of_le hm2_r_pos ht.1.le) 2)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
          (pow_le_pow_left₀ hm2_r_pos.le ht.1.le 2)
      · rw [norm_zero]; positivity
    have hθ_decomp : EqOn (fun t : ℝ => thetaChebyshev t / t ^ 2)
        (fun t : ℝ => ∑ p ∈ P_all, g_p p t) (uIcc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := by
      intro t ht
      rw [uIcc_of_le hm2_le_m4] at ht
      have ht_nn : 0 ≤ t := le_trans hm2_r_pos.le ht.1
      dsimp only
      unfold thetaChebyshev
      rw [Finset.sum_div]
      have hsub_t : (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime
          = P_all.filter (fun p : ℕ => (p : ℝ) ≤ t) := by
        ext p
        simp only [P_all, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp1, hpt⟩, hpr⟩
          have hp_le_t : (p : ℝ) ≤ t := (Nat.le_floor_iff ht_nn).mp hpt
          have hp_le_m4 : p ≤ m ^ 4 := by
            have : (p : ℝ) ≤ ((m ^ 4 : ℕ) : ℝ) := by push_cast; exact hp_le_t.trans ht.2
            exact_mod_cast this
          exact ⟨⟨⟨hp1, hp_le_m4⟩, hpr⟩, hp_le_t⟩
        · rintro ⟨⟨⟨hp1, _⟩, hpr⟩, hp_le_t⟩
          exact ⟨⟨hp1, Nat.le_floor hp_le_t⟩, hpr⟩
      rw [hsub_t, Finset.sum_filter]
    have hint_eq : (m : ℝ) ^ 4 * (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), thetaChebyshev t / t ^ 2)
        = (∑ p ∈ P_lo, ((m : ℝ) ^ 2 - 1) * Real.log (p : ℝ))
          + ∑ p ∈ P_hi, (((m : ℝ) ^ 4 / (p : ℝ) - 1) * Real.log (p : ℝ)) := by
      rw [integral_congr hθ_decomp, intervalIntegral.integral_finsetSum hg_int, Finset.mul_sum]
      have hp_int_val : ∀ p ∈ P_all,
          (m : ℝ) ^ 4 * (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), g_p p t)
            = if p ≤ m ^ 2 then ((m : ℝ) ^ 2 - 1) * Real.log (p : ℝ)
              else ((m : ℝ) ^ 4 / (p : ℝ) - 1) * Real.log (p : ℝ) := by
        intro p hp
        have hp_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
        have hp_pr := (Finset.mem_filter.mp hp).2
        have hp_r_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        by_cases hplo : p ≤ m ^ 2
        · rw [if_pos hplo]
          have hp_r_le : (p : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hplo
          have hcongr_lo : EqOn (g_p p) (fun t : ℝ => Real.log (p : ℝ) * (1 / t ^ 2))
              (uIcc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := by
            intro t ht
            rw [uIcc_of_le hm2_le_m4] at ht
            dsimp only [g_p]
            rw [if_pos (hp_r_le.trans ht.1)]
            ring
          rw [integral_congr hcongr_lo, intervalIntegral.integral_const_mul,
            integral_inv_sq_Icc hm2_r_pos hm2_le_m4]
          have hm_ne : (m : ℝ) ≠ 0 := by positivity
          field_simp
        · rw [if_neg hplo]
          have hp_gt : (m : ℝ) ^ 2 < (p : ℝ) := by
            have : m ^ 2 < p := by omega
            exact_mod_cast this
          have hp_le_m4 : (p : ℝ) ≤ (m : ℝ) ^ 4 := by exact_mod_cast hp_Icc.2
          have hint1 : IntervalIntegrable (g_p p) volume ((m : ℝ) ^ 2) (p : ℝ) :=
            (hg_int p hp).mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hm2_le_m4]; exact ⟨hp_gt.le, hp_le_m4⟩))
          have hint2 : IntervalIntegrable (g_p p) volume (p : ℝ) ((m : ℝ) ^ 4) :=
            (hg_int p hp).mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hm2_le_m4]; exact ⟨hp_gt.le, hp_le_m4⟩))
          rw [← integral_add_adjacent_intervals hint1 hint2]
          have hzero_left : (∫ t in ((m : ℝ) ^ 2)..(p : ℝ), g_p p t) = 0 := by
            have hae_ne : ∀ᵐ t : ℝ ∂volume, t ≠ (p : ℝ) := by
              rw [ae_iff]
              simp [Set.ofPred_eq_eq_singleton]
            have hae_eq : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc ((m : ℝ) ^ 2) (p : ℝ) → g_p p t = 0 := by
              filter_upwards [hae_ne] with t hne htI
              rw [uIoc_of_le hp_gt.le] at htI
              have hlt_p : t < (p : ℝ) := lt_of_le_of_ne htI.2 hne
              dsimp only [g_p]
              rw [if_neg (not_le.mpr hlt_p)]
            rw [integral_congr_ae hae_eq, intervalIntegral.integral_zero]
          have hright : (∫ t in (p : ℝ)..((m : ℝ) ^ 4), g_p p t)
              = Real.log (p : ℝ) * (1 / (p : ℝ) - 1 / (m : ℝ) ^ 4) := by
            have hae_r : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (p : ℝ) ((m : ℝ) ^ 4) →
                g_p p t = Real.log (p : ℝ) * (1 / t ^ 2) := by
              refine Eventually.of_forall fun t htI => ?_
              rw [uIoc_of_le hp_le_m4] at htI
              dsimp only [g_p]
              rw [if_pos htI.1.le]
              ring
            rw [integral_congr_ae hae_r, intervalIntegral.integral_const_mul,
              integral_inv_sq_Icc hp_r_pos hp_le_m4]
          rw [hzero_left, zero_add, hright]
          have hp_ne : (p : ℝ) ≠ 0 := hp_r_pos.ne'
          have hm_ne : (m : ℝ) ≠ 0 := by positivity
          field_simp
      rw [Finset.sum_congr rfl hp_int_val,
        ← Finset.sum_filter_add_sum_filter_not P_all (fun p : ℕ => p ≤ m ^ 2)]
      congr 1
      · exact Finset.sum_congr rfl fun p hp => if_pos (Finset.mem_filter.mp hp).2
      · exact Finset.sum_congr rfl fun p hp => if_neg (Finset.mem_filter.mp hp).2
    -- Paso 3: restar y comprobar que queda exactamente `A_primos ((m : ℝ) ^ 4)`.
    rw [hsum_q_eq, hint_eq]
    have hdiff_hi : (∑ p ∈ P_hi, (((m ^ 4 / p : ℕ) : ℝ) * Real.log (p : ℝ)))
        - (∑ p ∈ P_hi, (((m : ℝ) ^ 4 / (p : ℝ) - 1) * Real.log (p : ℝ)))
        = A_primos ((m : ℝ) ^ 4) := by
      rw [← Finset.sum_sub_distrib]
      unfold A_primos
      have hfl_m4 : ⌊(m : ℝ) ^ 4⌋₊ = m ^ 4 := by
        have : ((m ^ 4 : ℕ) : ℝ) = (m : ℝ) ^ 4 := by push_cast; rfl
        rw [← this, Nat.floor_natCast]
      have hsqrt_m4 : Real.sqrt ((m : ℝ) ^ 4) = (m : ℝ) ^ 2 := by
        rw [show (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      rw [hfl_m4, hsqrt_m4]
      have hset_eq : P_hi = (Finset.Icc 1 (m ^ 4)).filter
          (fun p : ℕ => Nat.Prime p ∧ (m : ℝ) ^ 2 < (p : ℝ)) := by
        ext p
        simp only [P_hi, P_all, Finset.mem_filter, and_assoc]
        refine and_congr_right fun _ => and_congr_right fun _ => ?_
        constructor
        · intro hnot
          have : m ^ 2 < p := not_le.mp hnot
          exact_mod_cast this
        · intro hlt hle
          have : (p : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hle
          linarith
      rw [hset_eq]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_pr := (Finset.mem_filter.mp hp).2.1
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
      have hfl_div := cast_natFloor_eq_sub_fract (div_nonneg hm4_r_pos.le hp_pos.le)
      have hnf := natFloor_div_natCast (by positivity : (0 : ℝ) ≤ ((m ^ 4 : ℕ) : ℝ)) p
      rw [Nat.floor_natCast] at hnf
      push_cast at hnf
      rw [hnf] at hfl_div
      rw [hfl_div]
      ring
    linarith

/-! ### 3. Discrepancia hiperbólica de Chebyshev y equivalencia exacta de Ruta B -/

/-- Error de Chebyshev sobre primos: `E_ϑ(t) = ϑ(t) − t`. -/
noncomputable def errorChebyshev (t : ℝ) : ℝ := thetaChebyshev t - t

/-- **Discrepancia hiperbólica de Chebyshev en escala cuártica `m⁴`:**
diferencia entre el promedio continuo de `E_ϑ(t) / t²` en `[m², m⁴]` y su muestreo hiperbólico en
`m⁴ / q` (`1 ≤ q ≤ m² − 1`). -/
noncomputable def discrepanciaHiperbolica (m : ℕ) : ℝ :=
  (m : ℝ) ^ 4 * (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), errorChebyshev t / t ^ 2)
    - ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))

/-- Suma en ventanas de las discrepancias hiperbólicas positivas:
`S_hip(Y) = ∑_{Y ≤ m⁴ ≤ Y^{3/2}} max(Δ_hip(m), 0) / m³`. -/
noncomputable def S_hiperbolica (Y : ℝ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊).filter
      (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
    max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3

theorem harmonic_cast_eq_sum_Icc (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ q ∈ Finset.Icc 1 n, (1 / (q : ℝ)) := by
  induction n with
  | zero => simp [harmonic_zero]
  | succ k ih =>
    rw [harmonic_succ, Rat.cast_add, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    ring

theorem integral_one_div_m2_m4 {m : ℕ} (hm : 1 ≤ m) :
    (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), (1 / t)) = Real.log (((m ^ 2 : ℕ) : ℝ)) := by
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hm2_le_m4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by exact_mod_cast hm) (by omega)
  have hderiv : ∀ t ∈ uIcc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4), HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [uIcc_of_le hm2_le_m4] at ht
    simpa [one_div] using Real.hasDerivAt_log (lt_of_lt_of_le hm2_pos ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ => 1 / t) (uIcc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := by
    rw [uIcc_of_le hm2_le_m4]
    exact continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hm2_pos ht.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hpow : (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 := by ring
  rw [hpow, Real.log_pow]
  push_cast
  ring

/-- **Encaje bilateral exacto entre el déficit de primos y la discrepancia hiperbólica:**
para todo `m ≥ 1`,
`Δ_hip(m) ≤ γ_E m⁴ − A_primos(m⁴) ≤ Δ_hip(m) + m²`. -/
theorem cota_bilateral_deficit_discrepancia {m : ℕ} (hm : 1 ≤ m) :
    discrepanciaHiperbolica m ≤ Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4) ∧
      Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)
        ≤ discrepanciaHiperbolica m + (m : ℝ) ^ 2 := by
  have hm2_pos : 0 < m ^ 2 := by positivity
  have hm2_r_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hm2_le_m4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by exact_mod_cast hm) (by omega)
  -- Integrabilidad en intervalo de `ϑ(t) / t²` y `1 / t`.
  have hint_θ : IntervalIntegrable (fun t : ℝ => thetaChebyshev t / t ^ 2)
      volume ((m : ℝ) ^ 2) ((m : ℝ) ^ 4) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hm2_le_m4]
    have hdom : IntegrableOn (fun _ : ℝ => |thetaChebyshev ((m : ℝ) ^ 4)| / ((m : ℝ) ^ 2) ^ 2)
        (Ioc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine hdom.mono' (measurable_thetaChebyshev.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have hθ_nn : 0 ≤ thetaChebyshev t := by
      have h0 : thetaChebyshev 0 = 0 := by simp [thetaChebyshev]
      rw [← h0]; exact monotone_thetaChebyshev (le_trans hm2_r_pos.le ht.1.le)
    have hθ_le : thetaChebyshev t ≤ |thetaChebyshev ((m : ℝ) ^ 4)| :=
      (monotone_thetaChebyshev ht.2).trans (le_abs_self _)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hθ_nn,
      abs_of_pos (pow_pos (lt_of_lt_of_le hm2_r_pos ht.1.le) 2)]
    exact div_le_div₀ (abs_nonneg _) hθ_le (by positivity)
      (pow_le_pow_left₀ hm2_r_pos.le ht.1.le 2)
  have hint_inv : IntervalIntegrable (fun t : ℝ => 1 / t)
      volume ((m : ℝ) ^ 2) ((m : ℝ) ^ 4) := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le hm2_le_m4]
    exact continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hm2_r_pos ht.1).ne'
  have herr_int : (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), errorChebyshev t / t ^ 2)
      = (∫ t in ((m : ℝ) ^ 2)..((m : ℝ) ^ 4), thetaChebyshev t / t ^ 2)
        - Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    have hcongr : EqOn (fun t : ℝ => errorChebyshev t / t ^ 2)
        (fun t : ℝ => thetaChebyshev t / t ^ 2 - 1 / t)
        (uIcc ((m : ℝ) ^ 2) ((m : ℝ) ^ 4)) := by
      intro t ht
      rw [uIcc_of_le hm2_le_m4] at ht
      have ht_ne : t ≠ 0 := (lt_of_lt_of_le hm2_r_pos ht.1).ne'
      unfold errorChebyshev
      field_simp
    rw [integral_congr hcongr, integral_sub hint_θ hint_inv, integral_one_div_m2_m4 hm]
  have herr_sum : ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), errorChebyshev ((m : ℝ) ^ 4 / (q : ℝ))
      = (∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), thetaChebyshev ((m : ℝ) ^ 4 / (q : ℝ)))
        - (m : ℝ) ^ 4 * (((harmonic (m ^ 2) : ℚ) : ℝ) - 1 / (m : ℝ) ^ 2) := by
    unfold errorChebyshev
    rw [Finset.sum_sub_distrib]
    congr 1
    have hharm := harmonic_cast_eq_sum_Icc (m ^ 2)
    have htop : m ^ 2 = (m ^ 2 - 1) + 1 := by omega
    have hsum_split : ∑ q ∈ Finset.Icc 1 (m ^ 2), (1 / (q : ℝ))
        = (∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), (1 / (q : ℝ))) + 1 / (m : ℝ) ^ 2 := by
      conv_lhs => rw [htop]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m ^ 2 - 1 + 1), ← htop]
      push_cast; rfl
    have hsub_harm : ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), (1 / (q : ℝ))
        = ((harmonic (m ^ 2) : ℚ) : ℝ) - 1 / (m : ℝ) ^ 2 := by linarith
    calc ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), (m : ℝ) ^ 4 / (q : ℝ)
        = (m : ℝ) ^ 4 * ∑ q ∈ Finset.Icc (1 : ℕ) (m ^ 2 - 1), (1 / (q : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun q _ => by ring
      _ = (m : ℝ) ^ 4 * (((harmonic (m ^ 2) : ℚ) : ℝ) - 1 / (m : ℝ) ^ 2) := by rw [hsub_harm]
  have hid := identidad_hiperbolica_A_primos hm
  -- Cotas de Euler–Mascheroni en `n = m² ≥ 1`: `0 < H_n − log n − γ_E < 1 / n`.
  have heuler_gt : Real.eulerMascheroniConstant
      < ((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (m ^ 2)
    simpa [Real.eulerMascheroniSeq', show m ≠ 0 by omega] using h
  have heuler_lt : ((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ))
      ≤ Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2 := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (m ^ 2)
    unfold Real.eulerMascheroniSeq at h
    have hlog_diff : Real.log (((m ^ 2 : ℕ) : ℝ) + 1) - Real.log (((m ^ 2 : ℕ) : ℝ))
        ≤ 1 / (m : ℝ) ^ 2 := by
      have hn_pos : (0 : ℝ) < ((m ^ 2 : ℕ) : ℝ) := by exact_mod_cast hm2_pos
      have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < ((m ^ 2 : ℕ) : ℝ) + 1) hn_pos)
      rw [Real.log_div (by positivity) hn_pos.ne'] at h1
      have h2 : (((m ^ 2 : ℕ) : ℝ) + 1) / ((m ^ 2 : ℕ) : ℝ) - 1 = 1 / (m : ℝ) ^ 2 := by
        push_cast; field_simp; ring
      linarith
    linarith
  -- Identidad exacta de diferencia `γ_E m⁴ − A_primos(m⁴) − Δ_hip(m)`.
  have hdiff_exact : Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)
      - discrepanciaHiperbolica m
      = (m : ℝ) ^ 4 * (Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2
          - (((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ)))) := by
    unfold discrepanciaHiperbolica
    rw [hid, herr_int, herr_sum]
    ring
  have hnonneg_rem : 0 ≤ (m : ℝ) ^ 4 * (Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2
      - (((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ)))) :=
    mul_nonneg (by positivity) (by linarith)
  have hle_m2 : (m : ℝ) ^ 4 * (Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2
      - (((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ)))) ≤ (m : ℝ) ^ 2 := by
    have h1 : Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2
        - (((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ))) ≤ 1 / (m : ℝ) ^ 2 := by
      linarith
    calc (m : ℝ) ^ 4 * (Real.eulerMascheroniConstant + 1 / (m : ℝ) ^ 2
          - (((harmonic (m ^ 2) : ℚ) : ℝ) - Real.log (((m ^ 2 : ℕ) : ℝ))))
        ≤ (m : ℝ) ^ 4 * (1 / (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (m : ℝ) ^ 2 := by
          have hm_ne : (m : ℝ) ≠ 0 := by positivity
          field_simp
  constructor <;> linarith

/-- **Comparación bilateral uniforme `S_hiperbolica Y ≤ S_AMate Y ≤ S_hiperbolica Y + 1 + log Y`:**
válida incondicionalmente para todo `Y ≥ 1`. -/
theorem cota_bilateral_S_AMate_S_hiperbolica {Y : ℝ} (hY : 1 ≤ Y) :
    S_hiperbolica Y ≤ S_AMate Y ∧
      S_AMate Y ≤ S_hiperbolica Y + 1 + Real.log Y := by
  have hY_pos : 0 < Y := lt_of_lt_of_le one_pos hY
  set M_set : Finset ℕ := (Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊).filter
    (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ))
  have hlo : S_hiperbolica Y ≤ S_AMate Y := by
    unfold S_hiperbolica S_AMate
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hbd := (cota_bilateral_deficit_discrepancia hm1).1
    exact div_le_div_of_nonneg_right (max_le_max_right 0 hbd) (by positivity)
  have hhi : S_AMate Y ≤ S_hiperbolica Y + 1 + Real.log Y := by
    unfold S_AMate S_hiperbolica
    have hterm : ∀ m ∈ M_set,
        max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
          ≤ max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3 + 1 / (m : ℝ) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
      have hbd := (cota_bilateral_deficit_discrepancia hm1).2
      have hmax : max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0
          ≤ max (discrepanciaHiperbolica m) 0 + (m : ℝ) ^ 2 := by
        refine max_le ?_ (add_nonneg (le_max_right _ _) (by positivity))
        linarith [le_max_left (discrepanciaHiperbolica m) 0]
      calc max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
          ≤ (max (discrepanciaHiperbolica m) 0 + (m : ℝ) ^ 2) / (m : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right hmax (by positivity)
        _ = max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3 + 1 / (m : ℝ) := by
            have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
            field_simp
    have hN1 : 1 ≤ ⌊Y ^ (3 / 8 : ℝ)⌋₊ :=
      Nat.le_floor (by exact_mod_cast Real.one_le_rpow hY (by norm_num : (0 : ℝ) ≤ 3 / 8))
    have hharm : ∑ m ∈ M_set, (1 / (m : ℝ)) ≤ 1 + Real.log Y := by
      calc ∑ m ∈ M_set, (1 / (m : ℝ))
          ≤ ∑ m ∈ Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊, (1 / (m : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
        _ ≤ 1 + Real.log (⌊Y ^ (3 / 8 : ℝ)⌋₊ : ℝ) := sum_inv_Icc_le hN1
        _ ≤ 1 + Real.log (Y ^ (3 / 8 : ℝ)) := by
            gcongr
            exact Nat.floor_le (by positivity)
        _ = 1 + (3 / 8 : ℝ) * Real.log Y := by rw [Real.log_rpow hY_pos (3 / 8 : ℝ)]
        _ ≤ 1 + Real.log Y := by linarith [Real.log_nonneg hY]
    calc ∑ m ∈ M_set,
          max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3
        ≤ ∑ m ∈ M_set, (max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3 + 1 / (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ M_set, max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3)
          + ∑ m ∈ M_set, (1 / (m : ℝ)) := Finset.sum_add_distrib
      _ ≤ (∑ m ∈ M_set, max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3) + (1 + Real.log Y) :=
          add_le_add le_rfl hharm
      _ = (∑ m ∈ M_set, max (discrepanciaHiperbolica m) 0 / (m : ℝ) ^ 3) + 1 + Real.log Y := by ring
  exact ⟨hlo, hhi⟩

/-- **Teorema fundamental de reducción de Ruta B (`RH ↔ S_hiperbolica`):**
`RiemannHypothesis` equivale exactamente a que para todo `η > 0` existan escalas arbitrariamente
grandes `Y` donde la suma de discrepancias hiperbólicas de Chebyshev cumple `S_hiperbolica Y ≤ Y^η`. -/
theorem rh_iff_S_hiperbolica :
    RiemannHypothesis ↔
      ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_hiperbolica Y ≤ Y ^ η := by
  rw [rh_iff_deficit_primos]
  constructor
  · intro hdef η hη Y₀
    obtain ⟨Y, hY0, hSY⟩ := hdef η hη (max Y₀ 1)
    have hY1 : 1 ≤ Y := (le_max_right Y₀ 1).trans hY0
    exact ⟨Y, (le_max_left Y₀ 1).trans hY0,
      (cota_bilateral_S_AMate_S_hiperbolica hY1).1.trans hSY⟩
  · intro hhip η hη Y₀
    set η₂ : ℝ := η / 2
    have hη₂ : 0 < η₂ := half_pos hη
    -- Para `Y` grande, `Y^{η/2} + 1 + log Y ≤ Y^η`.
    set K_c : ℝ := 2 + 2 / η₂
    have hKc_pos : 0 < K_c := by simp only [K_c]; positivity
    set Y_min : ℝ := max Y₀ (max 2 (K_c ^ (2 / η)))
    obtain ⟨Y, hY_ge, hSY⟩ := hhip η₂ hη₂ Y_min
    have hY0 : Y₀ ≤ Y := (le_max_left _ _).trans hY_ge
    have hY2 : 2 ≤ Y := ((le_max_left _ _).trans (le_max_right _ _)).trans hY_ge
    have hYK : K_c ^ (2 / η) ≤ Y := ((le_max_right _ _).trans (le_max_right _ _)).trans hY_ge
    have hY1 : 1 ≤ Y := by linarith
    have hY_pos : 0 < Y := by linarith
    refine ⟨Y, hY0, ?_⟩
    have hlog_le : Real.log Y ≤ (2 / η₂) * Y ^ (η₂ / 2) := by
      have h1 := Real.log_le_rpow_div hY_pos.le (half_pos hη₂)
      have heq : Y ^ (η₂ / 2) / (η₂ / 2) = (2 / η₂) * Y ^ (η₂ / 2) := by field_simp
      linarith
    have h1_le_rpow : 1 ≤ Y ^ (η₂ / 2) := Real.one_le_rpow hY1 (by positivity)
    have hrpow_mono : Y ^ (η₂ / 2) ≤ Y ^ η₂ :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hK_le_Y : K_c ≤ Y ^ η₂ := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hKc_pos.le _) hYK hη₂.le
      rw [← Real.rpow_mul hKc_pos.le, show (2 / η) * η₂ = 1 by simp only [η₂]; field_simp,
        Real.rpow_one] at h1
      exact h1
    have hY_ge2_rpow : 2 ≤ Y ^ η₂ := by
      have : (0 : ℝ) ≤ 2 / η₂ := by positivity
      linarith [show 2 ≤ K_c by simp only [K_c]; linarith]
    calc S_AMate Y
        ≤ S_hiperbolica Y + 1 + Real.log Y :=
          (cota_bilateral_S_AMate_S_hiperbolica hY1).2
      _ ≤ Y ^ η₂ + 1 + (2 / η₂) * Y ^ (η₂ / 2) := by linarith
      _ ≤ Y ^ η₂ + Y ^ η₂ + (2 / η₂) * Y ^ η₂ := by
          have : (2 / η₂) * Y ^ (η₂ / 2) ≤ (2 / η₂) * Y ^ η₂ :=
            mul_le_mul_of_nonneg_left hrpow_mono (by positivity)
          linarith
      _ = K_c * Y ^ η₂ := by simp only [K_c]; ring
      _ ≤ Y ^ η₂ * Y ^ η₂ :=
          mul_le_mul_of_nonneg_right hK_le_Y (Real.rpow_nonneg hY_pos.le _)
      _ = Y ^ η := by rw [← Real.rpow_add hY_pos]; congr 1; simp only [η₂]; ring

end AMate
