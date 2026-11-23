import AMateEnergia.EnergiaFourier

/-!
# Recíproco: la cota de energía implica la hipótesis de Riemann

Estados 39 (§§2–3) y 45 (§1, (1.1)–(1.4)).

* `cota_inferior_energia_cero`: si `ζ(ρ) = 0` con `Re ρ > 1/2`, entonces para todo `Q ≥ 2`,
  `(2 Re ρ − 1) / ‖ρ‖² ≤ E_Q · Q^{1 − 2 Re ρ}` (Cauchy–Schwarz en `(Q, ∞)` sobre `integral_sigma_floor`
  usando `σ_Q(k) = 0` para `1 ≤ k < Q`).
* `sin_ceros_de_energia_cofinal`: para todo `θ ≥ 1/2`, si para cada `ε > 0` hay valores
  arbitrariamente grandes de `Q` con `E_Q ≤ C_ε Q^{2θ − 1 + ε}`, entonces `ζ` no se anula en
  `Re s > θ`.
* `rh_of_no_zero_gt_half`: la ausencia de ceros en `Re s > 1/2` implica `RiemannHypothesis`
  mediante la ecuación funcional `riemannZeta_one_sub` aplicada a `1 − s`.
* `rh_de_energia_cofinal`, `rh_de_energia_subpolinomial` y `rh_de_energia_acotada_cofinal`:
  criterios recíprocos de los Estados 39 y 45.
-/

open MeasureTheory Set Complex Filter

namespace AMate

theorem integrableOn_sigma_sq (Q : ℕ) :
    IntegrableOn (fun x : ℝ => sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) := by
  obtain ⟨C, hC⟩ := sigma_acotado Q
  have hg : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
  refine hg.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      ((((measurable_from_nat (f := sigma Q)).comp Nat.measurable_floor).pow_const 2).mul
        (measurable_id.pow_const (-2 : ℝ)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hp := Real.rpow_nonneg hx0.le (-2 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
    have hsq : sigma Q ⌊x⌋₊ ^ 2 ≤ C ^ 2 := by
      have h1 := hC ⌊x⌋₊
      nlinarith [abs_nonneg (sigma Q ⌊x⌋₊), sq_abs (sigma Q ⌊x⌋₊)]
    exact mul_le_mul_of_nonneg_right hsq hp

theorem integrableOn_sigma_cpow (Q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨C, hC⟩ := sigma_acotado Q
  have hg : IntegrableOn (fun x : ℝ => C * x ^ (-s.re - 1)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) _
  refine hg.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      ((Complex.measurable_ofReal.comp
        ((measurable_from_nat (f := sigma Q)).comp Nat.measurable_floor)).mul (by measurability))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hC ⌊x⌋₊) (Real.rpow_nonneg hx0.le _)

/-- Estado 39, §3: un cero `ρ` de `ζ` con `Re ρ > 1/2` obliga a
`(2 Re ρ − 1) / ‖ρ‖² ≤ E_Q · Q^{1 − 2 Re ρ}` para todo `Q ≥ 2`. -/
theorem cota_inferior_energia_cero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hβ : 1 / 2 < ρ.re)
    {Q : ℕ} (hQ : 2 ≤ Q) :
    (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ≤ E Q * (Q : ℝ) ^ (1 - 2 * ρ.re) := by
  have hρ0 : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h1
    exact riemannZeta_ne_zero_of_one_le_re (by rw [h1]; norm_num) hζ
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hβ
    linarith
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQpos : (0 : ℝ) < Q := by positivity
  -- La integral de Mellin en `(1, ∞)` coincide con la de `(Q, ∞)` porque `σ_Q(k) = 0` para `k < Q`.
  have hintC := integrableOn_sigma_cpow Q hρ0
  have hsplit : ∫ x in Ioi (1 : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 1)
      = ∫ x in Ioi (Q : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 1) := by
    rw [← Ioc_union_Ioi_eq_Ioi hQ1,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hintC.mono_set Ioc_subset_Ioi_self) (hintC.mono_set (Ioi_subset_Ioi hQ1)),
      integral_Ioc_eq_integral_Ioo,
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_, zero_add]
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hk1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
    have hkQ : ⌊x⌋₊ < Q := (Nat.floor_lt hx0).mpr hx.2
    rw [sigma_eq_zero hQ hk1 hkQ]
    simp
  have hval : ∫ x in Ioi (Q : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 1) = 1 / ρ := by
    rw [← hsplit, integral_sigma_floor (by omega) hρ0 hρ1, hζ, zero_mul, sub_zero]
  -- Cota de la norma de la integral en `(Q, ∞)`.
  have hnorm_int : 1 / ‖ρ‖
      ≤ ∫ x in Ioi (Q : ℝ), |sigma Q ⌊x⌋₊| * x ^ (-ρ.re - 1) := by
    have h1 : 1 / ‖ρ‖ = ‖∫ x in Ioi (Q : ℝ), ((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 1)‖ := by
      rw [hval, norm_div, norm_one]
    rw [h1]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans hQpos hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
    rw [hre]
  -- Integrales cuadráticas en `(Q, ∞)`.
  have hint_sqQ : IntegrableOn (fun x : ℝ => sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ)) (Ioi (Q : ℝ)) :=
    (integrableOn_sigma_sq Q).mono_set (Ioi_subset_Ioi hQ1)
  have hE_le : ∫ x in Ioi (Q : ℝ), sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) ≤ E Q := by
    rw [← integral_sigma_sq_eq_E Q]
    refine setIntegral_mono_set (integrableOn_sigma_sq Q) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x (hx : 1 < x) => ?_)
      have hx0 : 0 ≤ x := by linarith
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0 _)
    · exact Eventually.of_forall fun x (hx : x ∈ Ioi (Q : ℝ)) => lt_of_le_of_lt hQ1 hx
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (-2 * ρ.re)) (Ioi (Q : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hQpos
  set I_Q : ℝ := (Q : ℝ) ^ (1 - 2 * ρ.re) / (2 * ρ.re - 1) with hIQ_def
  have h2β_pos : 0 < 2 * ρ.re - 1 := by linarith
  have hIQ_pos : 0 < I_Q := by
    rw [hIQ_def]
    exact div_pos (Real.rpow_pos_of_pos hQpos _) h2β_pos
  have hint_rpow_eq : ∫ x in Ioi (Q : ℝ), x ^ (-2 * ρ.re) = I_Q := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hQpos, hIQ_def,
      show -2 * ρ.re + 1 = 1 - 2 * ρ.re by ring]
    have h1 : 1 - 2 * ρ.re ≠ 0 := by linarith
    have h2 : 2 * ρ.re - 1 ≠ 0 := h2β_pos.ne'
    field_simp
    ring
  -- Cauchy–Schwarz mediante Young con `t = ‖ρ‖ * I_Q > 0`.
  set t : ℝ := ‖ρ‖ * I_Q with ht_def
  have ht_pos : 0 < t := mul_pos hρnorm hIQ_pos
  have hint_abs : IntegrableOn (fun x : ℝ => |sigma Q ⌊x⌋₊| * x ^ (-ρ.re - 1)) (Ioi (Q : ℝ)) := by
    have hnorm : IntegrableOn
        (fun x : ℝ => ‖((sigma Q ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 1)‖) (Ioi (Q : ℝ)) :=
      (hintC.mono_set (Ioi_subset_Ioi hQ1)).norm
    refine hnorm.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    have hx0 : 0 < x := lt_trans hQpos hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
    rw [hre]
  have hMaj : IntegrableOn
      (fun x : ℝ => (t / 2) * (sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ)) + (1 / (2 * t)) * x ^ (-2 * ρ.re))
      (Ioi (Q : ℝ)) :=
    (hint_sqQ.const_mul (t / 2)).add (hint_rpow.const_mul (1 / (2 * t)))
  have hpt : ∀ x ∈ Ioi (Q : ℝ), |sigma Q ⌊x⌋₊| * x ^ (-ρ.re - 1)
      ≤ (t / 2) * (sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ)) + (1 / (2 * t)) * x ^ (-2 * ρ.re) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hQpos hx
    set A : ℝ := |sigma Q ⌊x⌋₊| * x ^ (-1 : ℝ)
    set B : ℝ := x ^ (-ρ.re)
    have hAB : |sigma Q ⌊x⌋₊| * x ^ (-ρ.re - 1) = A * B := by
      simp only [A, B, mul_assoc]
      rw [← Real.rpow_add hx0, show (-1 : ℝ) + -ρ.re = -ρ.re - 1 by ring]
    have hx2 : (x ^ (-1 : ℝ)) ^ 2 = x ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hA2 : A ^ 2 = sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) := by
      simp only [A, mul_pow, sq_abs, hx2]
    have hB2 : B ^ 2 = x ^ (-2 * ρ.re) := by
      simp only [B]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      ring_nf
    rw [hAB, ← hA2, ← hB2]
    have hsq : 0 ≤ (t * A - B) ^ 2 := sq_nonneg _
    have hcomb : (t / 2) * A ^ 2 + (1 / (2 * t)) * B ^ 2 - A * B = (t * A - B) ^ 2 / (2 * t) := by
      field_simp
      ring
    have hpos_div : 0 ≤ (t * A - B) ^ 2 / (2 * t) := div_nonneg hsq (by positivity)
    linarith [hcomb]
  have hint_le := setIntegral_mono_on hint_abs hMaj measurableSet_Ioi hpt
  rw [integral_add (hint_sqQ.const_mul _) (hint_rpow.const_mul _),
    integral_const_mul, integral_const_mul, hint_rpow_eq] at hint_le
  have hstep1 : 1 / ‖ρ‖ ≤ (t / 2) * E Q + (1 / (2 * t)) * I_Q := by
    have h1 := hnorm_int.trans hint_le
    have h2 : (t / 2) * ∫ x in Ioi (Q : ℝ), sigma Q ⌊x⌋₊ ^ 2 * x ^ (-2 : ℝ) ≤ (t / 2) * E Q :=
      mul_le_mul_of_nonneg_left hE_le (by positivity)
    linarith
  have hcancel : (1 / (2 * t)) * I_Q = 1 / (2 * ‖ρ‖) := by
    rw [ht_def]
    have hIQ_ne : I_Q ≠ 0 := hIQ_pos.ne'
    have hρ_ne' : ‖ρ‖ ≠ 0 := hρnorm.ne'
    field_simp
  rw [hcancel] at hstep1
  have hhalf : 1 / ‖ρ‖ - 1 / (2 * ‖ρ‖) = 1 / (2 * ‖ρ‖) := by
    have hρ_ne' : ‖ρ‖ ≠ 0 := hρnorm.ne'
    field_simp
    ring
  have hstep2 : 1 / (2 * ‖ρ‖) ≤ (‖ρ‖ * I_Q / 2) * E Q := by
    rw [ht_def] at hstep1
    linarith [hhalf]
  have hstep3 : 1 ≤ ‖ρ‖ ^ 2 * I_Q * E Q := by
    have hm := mul_le_mul_of_nonneg_left hstep2 (show 0 ≤ 2 * ‖ρ‖ by positivity)
    have hL : (2 * ‖ρ‖) * (1 / (2 * ‖ρ‖)) = 1 := by field_simp
    have hR : (2 * ‖ρ‖) * ((‖ρ‖ * I_Q / 2) * E Q) = ‖ρ‖ ^ 2 * I_Q * E Q := by ring
    linarith
  rw [hIQ_def] at hstep3
  rw [div_le_iff₀ (sq_pos_of_pos hρnorm)]
  have hm := mul_le_mul_of_nonneg_left hstep3 h2β_pos.le
  have hR : (2 * ρ.re - 1) * (‖ρ‖ ^ 2 * ((Q : ℝ) ^ (1 - 2 * ρ.re) / (2 * ρ.re - 1)) * E Q)
      = E Q * (Q : ℝ) ^ (1 - 2 * ρ.re) * ‖ρ‖ ^ 2 := by
    have h2 : 2 * ρ.re - 1 ≠ 0 := h2β_pos.ne'
    field_simp
  linarith

/-- Estado 45, §1: si para `θ ≥ 1/2` y cada `ε > 0` existe `C` tal que `E_Q ≤ C Q^{2θ − 1 + ε}`
en valores arbitrariamente grandes de `Q`, entonces `ζ` no tiene ceros en `Re s > θ`. -/
theorem sin_ceros_de_energia_cofinal {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ,
      Q₀ ≤ Q ∧ E Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε)) :
    ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0 := by
  intro ρ hρ hζ
  have hβ : 1 / 2 < ρ.re := lt_of_le_of_lt hθ hρ
  set δ : ℝ := ρ.re - θ with hδ_def
  have hδ : 0 < δ := by linarith
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hβ
    linarith
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  set a : ℝ := (2 * ρ.re - 1) / ‖ρ‖ ^ 2 with ha_def
  have ha_pos : 0 < a := div_pos (by linarith) (sq_pos_of_pos hρnorm)
  obtain ⟨C, hC⟩ := hE δ hδ
  set C' : ℝ := max C 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'C : C ≤ C' := le_max_left _ _
  set M : ℝ := (C' / a + 1) ^ (1 / δ) with hM_def
  have hbase1 : 1 < C' / a + 1 := by
    have : 0 < C' / a := div_pos (by linarith) ha_pos
    linarith
  set Q₀ : ℕ := max (Nat.ceil M + 1) 2
  obtain ⟨Q, hQQ₀, hEQ⟩ := hC Q₀
  have hQ2 : 2 ≤ Q := le_trans (le_max_right _ _) hQQ₀
  have hQpos : (0 : ℝ) < Q := by positivity
  have hQM : M < (Q : ℝ) := by
    have h1 : Nat.ceil M + 1 ≤ Q := le_trans (le_max_left _ _) hQQ₀
    have h2 : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have h3 : (Nat.ceil M : ℝ) + 1 ≤ (Q : ℝ) := by exact_mod_cast h1
    linarith
  have hQδ_gt : C' / a + 1 < (Q : ℝ) ^ δ := by
    have h1 : M ^ δ < (Q : ℝ) ^ δ := Real.rpow_lt_rpow (by positivity) hQM hδ
    have h2 : M ^ δ = C' / a + 1 := by
      rw [hM_def, ← Real.rpow_mul (by linarith), one_div_mul_cancel hδ.ne', Real.rpow_one]
    linarith
  have hlow := cota_inferior_energia_cero hζ hβ hQ2
  rw [← ha_def] at hlow
  have hprod_le : a ≤ C' * (Q : ℝ) ^ (-δ) := by
    calc a ≤ E Q * (Q : ℝ) ^ (1 - 2 * ρ.re) := hlow
      _ ≤ (C * (Q : ℝ) ^ (2 * θ - 1 + δ)) * (Q : ℝ) ^ (1 - 2 * ρ.re) :=
          mul_le_mul_of_nonneg_right hEQ (Real.rpow_nonneg hQpos.le _)
      _ ≤ (C' * (Q : ℝ) ^ (2 * θ - 1 + δ)) * (Q : ℝ) ^ (1 - 2 * ρ.re) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC'C (Real.rpow_nonneg hQpos.le _))
            (Real.rpow_nonneg hQpos.le _)
      _ = C' * ((Q : ℝ) ^ (2 * θ - 1 + δ) * (Q : ℝ) ^ (1 - 2 * ρ.re)) := by ring
      _ = C' * (Q : ℝ) ^ (-δ) := by
          rw [← Real.rpow_add hQpos]
          congr 2
          rw [hδ_def]
          ring
  have haQ_le : a * (Q : ℝ) ^ δ ≤ C' := by
    have hm := mul_le_mul_of_nonneg_right hprod_le (Real.rpow_nonneg hQpos.le δ)
    have hR : C' * (Q : ℝ) ^ (-δ) * (Q : ℝ) ^ δ = C' := by
      rw [mul_assoc, ← Real.rpow_add hQpos, neg_add_cancel, Real.rpow_zero, mul_one]
    linarith
  have haQ_gt : C' < a * (Q : ℝ) ^ δ := by
    have hm := mul_lt_mul_of_pos_left hQδ_gt ha_pos
    have hL : a * (C' / a + 1) = C' + a := by field_simp
    linarith
  linarith

/-- Si `ζ` no tiene ceros en `Re s > 1/2`, entonces se cumple `RiemannHypothesis` (por la ecuación
funcional `riemannZeta_one_sub` aplicada a `1 − s` cuando `Re s < 1/2`). -/
theorem rh_of_no_zero_gt_half (hno : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0) :
    RiemannHypothesis := by
  intro s hs0 htriv hs1
  rcases lt_trichotomy (1 / 2) s.re with hgt | heq | hlt
  · exact absurd hs0 (hno s hgt)
  · exact heq.symm
  · exfalso
    have hs_ne0 : s ≠ 0 := by
      intro h0
      rw [h0, riemannZeta_zero] at hs0
      norm_num at hs0
    set w : ℂ := 1 - s with hw_def
    have hw_re : 1 / 2 < w.re := by simp [hw_def]; linarith
    have hw_neg : ∀ n : ℕ, w ≠ -(n : ℂ) := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hw1 : w ≠ 1 := by
      intro h
      apply hs_ne0
      linear_combination -h
    have hfe := riemannZeta_one_sub hw_neg hw1
    have h1w : 1 - w = s := by simp [hw_def]
    rw [h1w, hs0] at hfe
    have h2pi_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      have hpos : 0 < 2 * Real.pi := by positivity
      have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≠ 0 := by
        rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        exact (Real.rpow_pos_of_pos hpos _).ne'
      exact norm_ne_zero_iff.mp hnorm
    have hGamma_ne : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
      intro hcos
      rw [Complex.cos_eq_zero_iff] at hcos
      obtain ⟨k, hk⟩ := hcos
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hw_eq : w = 2 * (k : ℂ) + 1 := by
        apply mul_left_cancel₀ hpi_ne
        linear_combination 2 * hk
      have hk_re : w.re = 2 * (k : ℝ) + 1 := by
        have := congrArg Complex.re hw_eq
        simpa using this
      have hk_nonneg : (0 : ℤ) ≤ k := by
        by_contra! hk_neg
        have hk_le : k ≤ -1 := by omega
        have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
        linarith
      rcases eq_or_lt_of_le hk_nonneg with rfl | hk_pos
      · apply hw1
        simpa using hw_eq
      · apply htriv
        refine ⟨(k - 1).toNat, ?_⟩
        have hk_nat : ((k - 1).toNat : ℤ) + 1 = k := by omega
        have hk_C : (((k - 1).toNat : ℕ) : ℂ) + 1 = (k : ℂ) := by exact_mod_cast hk_nat
        rw [← hk_C] at hw_eq
        linear_combination -hw_eq
    have hζw_ne : riemannZeta w ≠ 0 := hno w hw_re
    have hprod_ne : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w
        * Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2pi_ne) hGamma_ne) hcos_ne) hζw_ne
    exact hprod_ne hfe.symm

/-- Estado 45, (1.4) ⇒ (1.2): si para cada `ε > 0` existe `C` tal que `E_Q ≤ C Q^ε` para valores
arbitrariamente grandes de `Q`, entonces se cumple la hipótesis de Riemann. -/
theorem rh_de_energia_cofinal
    (hE : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧ E Q ≤ C * (Q : ℝ) ^ ε) :
    RiemannHypothesis := by
  apply rh_of_no_zero_gt_half
  refine sin_ceros_de_energia_cofinal le_rfl fun ε hε => ?_
  simpa using hE ε hε

/-- Estado 45, (1.3) ⇒ (1.2): si `E_Q ≤ C_ε Q^ε` para todo `Q ≥ 2`, se cumple `RiemannHypothesis`. -/
theorem rh_de_energia_subpolinomial
    (hE : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε) :
    RiemannHypothesis := by
  apply rh_de_energia_cofinal
  intro ε hε
  obtain ⟨C, hC⟩ := hE ε hε
  exact ⟨C, fun Q₀ => ⟨max Q₀ 2, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩

/-- Estado 39, §2: una energía acotada sobre una sucesión ilimitada de escalas implica `RiemannHypothesis`. -/
theorem rh_de_energia_acotada_cofinal
    (hE : ∃ B : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧ E Q ≤ B) :
    RiemannHypothesis := by
  obtain ⟨B, hB⟩ := hE
  apply rh_de_energia_cofinal
  intro ε hε
  refine ⟨max B 0, fun Q₀ => ?_⟩
  obtain ⟨Q, hQ, hEB⟩ := hB (max Q₀ 1)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (le_trans (le_max_right _ _) hQ)
  refine ⟨Q, le_trans (le_max_left _ _) hQ, ?_⟩
  calc E Q ≤ B := hEB
    _ ≤ max B 0 * 1 := by linarith [le_max_left B 0]
    _ ≤ max B 0 * (Q : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.one_le_rpow hQ1 hε.le) (le_max_right B 0)

end AMate
