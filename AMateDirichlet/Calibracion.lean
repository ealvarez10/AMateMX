import AMateDirichlet.EnergiaFourier
import AMateDirichlet.LTresRectas
import AMateDirichlet.PerronL

/-!
# Recíproco y calibración para un carácter de Dirichlet

Para `χ ≠ 1` módulo `N` y `1/2 ≤ θ < 1`:

* `energia_cota_theta_L`: si `L(s,χ) ≠ 0` en `Re s > θ`, para todo `ε > 0` existe `C` con
  `E_{Q,χ} ≤ C Q^{2θ − 1 + ε}` para todo `Q ≥ 1`. Se combinan la identidad de Plancherel
  (`E_eq_integral`), la cota `|L(1/2 + ix, χ)| ≤ C (1 + |x|)^{1/3}` (`L_recta_critica`) y la cota
  de `P_{Q,χ}` en la recta crítica (`P_recta_critica_L`).
* `sin_ceros_iff_energia_theta_L`, `sin_ceros_iff_energia_cofinal_theta_L`: equivalencia con la
  ausencia de ceros en `Re s > θ`; con `θ = 1/2`, `grh_iff_energia_subpolinomial`:
  GRH para `χ` equivale a `E_{Q,χ} ≪_ε Q^ε`.
* `Theta_L`, `tendsto_log_energia_div_log_L`: sin hipótesis,
  `lim_{Q → ∞} log(2 + E_{Q,χ}) / log Q = 2 Θ_χ − 1`, con
  `Θ_χ = sup ({1/2} ∪ {Re ρ : L(ρ,χ) = 0, 0 < Re ρ < 1})`.
-/

open Complex MeasureTheory Set Filter Topology

namespace AMate.Dirichlet

variable {N : ℕ} [NeZero N]

/-! ### Cota superior -/

/-- Si `L(s,χ) ≠ 0` en `Re s > θ` (`1/2 ≤ θ < 1`), entonces `E_{Q,χ} ≤ C_ε Q^{2θ − 1 + ε}`. -/
theorem energia_cota_theta_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (hθ1 : θ < 1) (hZ : SinCerosDerechaL χ θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → E χ Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  intro ε hε
  set δ : ℝ := min (ε / 2) ((1 - θ) / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by linarith)
  have hθδ : θ + δ < 1 := by
    have : δ ≤ (1 - θ) / 2 := min_le_right _ _
    linarith
  set v : ℝ := θ - 1 / 2 + δ
  have hv0 : 0 < v := by simp only [v]; linarith
  have h2v_le : 2 * v ≤ 2 * θ - 1 + ε := by
    have : δ ≤ ε / 2 := min_le_left _ _
    simp only [v]; linarith
  obtain ⟨CL, -, hCL⟩ := L_recta_critica hχ
  obtain ⟨CP, hCP⟩ := P_recta_critica_L hχ hθ hδ hθδ (show (0 : ℝ) < 1 / 8 by norm_num) hZ
  set K : ℝ := CL ^ 2 * CP ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hint1 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hint2 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(13 / 12 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set I₁ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))
  set I₂ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(13 / 12 : ℝ))
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun x => by positivity
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun x => by positivity
  refine ⟨(16 * I₁ + 16 * K * I₂) / (2 * Real.pi), fun Q hQ => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ2v : (Q : ℝ) ^ (2 * v) ≤ (Q : ℝ) ^ (2 * θ - 1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h2v_le
  have hQ2v1 : 1 ≤ (Q : ℝ) ^ (2 * v) := Real.one_le_rpow hQ1 (by positivity)
  rw [E_eq_integral hχ Q]
  set g : ℝ → ℝ := fun x => 16 * (1 + ‖x‖) ^ (-(2 : ℝ))
    + 16 * K * (Q : ℝ) ^ (2 * v) * (1 + ‖x‖) ^ (-(13 / 12 : ℝ))
  have hgint : Integrable g := (hint1.const_mul 16).add (hint2.const_mul _)
  have hpt : ∀ x : ℝ,
      ‖1 - DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I) * P χ Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
        / (1 / 4 + x ^ 2) ≤ g x := by
    intro x
    set y : ℝ := 1 + |x|
    have hy0 : 0 < y := by positivity
    set z := DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I)
    set p := P χ Q (1 / 2 + (x : ℂ) * I)
    have hL2 : ‖z‖ ^ 2 ≤ CL ^ 2 * y ^ (2 / 3 : ℝ) := by
      have e : (y ^ (1 / 3 : ℝ)) ^ 2 = y ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
      calc ‖z‖ ^ 2 ≤ (CL * y ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCL x) 2
        _ = CL ^ 2 * y ^ (2 / 3 : ℝ) := by rw [mul_pow, e]
    have hP2 : ‖p‖ ^ 2 ≤ CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ) := by
      have e1 : ((Q : ℝ) ^ v) ^ 2 = (Q : ℝ) ^ (2 * v) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
      have e2 : (y ^ (1 / 8 : ℝ)) ^ 2 = y ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
      calc ‖p‖ ^ 2 ≤ (CP * (Q : ℝ) ^ v * y ^ (1 / 8 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hCP Q hQ x) 2
        _ = CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ) := by rw [mul_pow, mul_pow, e1, e2]
    have hprod : ‖z‖ ^ 2 * ‖p‖ ^ 2 ≤ K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ) := by
      have e : y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ) = y ^ (11 / 12 : ℝ) := by
        rw [← Real.rpow_add hy0]; norm_num
      calc ‖z‖ ^ 2 * ‖p‖ ^ 2
          ≤ (CL ^ 2 * y ^ (2 / 3 : ℝ)) * (CP ^ 2 * (Q : ℝ) ^ (2 * v) * y ^ (1 / 4 : ℝ)) :=
            mul_le_mul hL2 hP2 (by positivity) (by positivity)
        _ = K * (Q : ℝ) ^ (2 * v) * (y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ)) := by simp only [K]; ring
        _ = K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ) := by rw [e]
    have hnum : ‖1 - z * p‖ ^ 2 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ)) := by
      have h1 : ‖1 - z * p‖ ≤ 1 + ‖z‖ * ‖p‖ := by
        calc ‖1 - z * p‖ ≤ ‖(1 : ℂ)‖ + ‖z * p‖ := norm_sub_le _ _
          _ = 1 + ‖z‖ * ‖p‖ := by rw [norm_one, norm_mul]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (1 + ‖z‖ * ‖p‖) ^ 2 ≤ 2 + 2 * (‖z‖ ^ 2 * ‖p‖ ^ 2) := by
        nlinarith [sq_nonneg (‖z‖ * ‖p‖ - 1)]
      linarith
    have hden : y ^ 2 / 8 ≤ 1 / 4 + x ^ 2 := by
      simp only [y]; nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
    have hy2 : 0 < y ^ 2 / 8 := by positivity
    have hB0 : 0 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ)) := by positivity
    have hnx : (1 + ‖x‖) = y := by rw [Real.norm_eq_abs]
    calc ‖1 - z * p‖ ^ 2 / (1 / 4 + x ^ 2)
        ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ))) / (1 / 4 + x ^ 2) := by gcongr
      _ ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * v) * y ^ (11 / 12 : ℝ))) / (y ^ 2 / 8) :=
          div_le_div_of_nonneg_left hB0 hy2 hden
      _ = 16 * (y ^ 2)⁻¹ + 16 * K * (Q : ℝ) ^ (2 * v) * (y ^ (11 / 12 : ℝ) / y ^ 2) := by
          field_simp; ring
      _ = g x := by
          simp only [g, hnx]
          rw [Real.rpow_neg hy0.le, Real.rpow_two, ← Real.rpow_two y,
            show -(13 / 12 : ℝ) = 11 / 12 - 2 by norm_num, Real.rpow_sub hy0]
  have hf0 : ∀ x : ℝ, 0 ≤
      ‖1 - DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I) * P χ Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
        / (1 / 4 + x ^ 2) := fun _ => by positivity
  have hmono := integral_mono_of_nonneg (Eventually.of_forall hf0) hgint (Eventually.of_forall hpt)
  have hgval : ∫ x : ℝ, g x = 16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂ := by
    simp only [g]
    rw [integral_add (hint1.const_mul 16) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hgval] at hmono
  calc 1 / (2 * Real.pi) * ∫ x : ℝ,
        ‖1 - DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I) * P χ Q (1 / 2 + (x : ℂ) * I)‖ ^ 2
          / (1 / 4 + x ^ 2)
      ≤ 1 / (2 * Real.pi) * (16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂) := by gcongr
    _ ≤ 1 / (2 * Real.pi) * ((16 * I₁ + 16 * K * I₂) * (Q : ℝ) ^ (2 * θ - 1 + ε)) := by
        gcongr
        have : (16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * v) * I₂)
            ≤ (16 * I₁ + 16 * K * I₂) * (Q : ℝ) ^ (2 * v) := by
          nlinarith [mul_nonneg hK0 hI₂0]
        exact this.trans (mul_le_mul_of_nonneg_left hQ2v (by positivity))
    _ = (16 * I₁ + 16 * K * I₂) / (2 * Real.pi) * (Q : ℝ) ^ (2 * θ - 1 + ε) := by ring

/-! ### Equivalencias -/

/-- `L(s,χ) ≠ 0` en `Re s > θ` si y solo si `E_{Q,χ} ≤ C_ε Q^{2θ − 1 + ε}` para todo `Q ≥ 1`. -/
theorem sin_ceros_iff_energia_theta_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SinCerosDerechaL χ θ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → E χ Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  refine ⟨energia_cota_theta_L hχ hθ hθ1, fun h => sin_ceros_de_energia_cofinal hχ hθ
    fun ε hε => ?_⟩
  obtain ⟨C, hC⟩ := h ε hε
  exact ⟨C, fun Q₀ => ⟨max Q₀ 1, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩

/-- La misma equivalencia con la cota solo en una sucesión no acotada de valores de `Q`. -/
theorem sin_ceros_iff_energia_cofinal_theta_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SinCerosDerechaL χ θ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧
        E χ Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε) := by
  refine ⟨fun hZ ε hε => ?_, sin_ceros_de_energia_cofinal hχ hθ⟩
  obtain ⟨C, hC⟩ := energia_cota_theta_L hχ hθ hθ1 hZ ε hε
  exact ⟨C, fun Q₀ => ⟨max Q₀ 1, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩

/-- **Teorema 7, recíproco**: `L(s,χ) ≠ 0` en `Re s > 1/2` (GRH para `χ`) si y solo si
`E_{Q,χ} ≪_ε Q^ε`. -/
theorem grh_iff_energia_subpolinomial {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → E χ Q ≤ C * (Q : ℝ) ^ ε := by
  have h := sin_ceros_iff_energia_theta_L hχ (θ := 1 / 2) le_rfl (by norm_num)
  simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, zero_add] at h
  exact h

/-! ### Abscisa `Θ_χ` y teorema límite -/

/-- Partes reales de los ceros de `L(s,χ)` en `0 < Re ρ < 1`. -/
def CerosRealesL (χ : DirichletCharacter ℂ N) : Set ℝ :=
  {x : ℝ | ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re = x}

/-- `Θ_χ = sup ({1/2} ∪ {Re ρ : L(ρ,χ) = 0, 0 < Re ρ < 1})`. -/
noncomputable def Theta_L (χ : DirichletCharacter ℂ N) : ℝ :=
  sSup (insert (1 / 2 : ℝ) (CerosRealesL χ))

theorem bddAbove_insert_cerosRealesL (χ : DirichletCharacter ℂ N) :
    BddAbove (insert (1 / 2 : ℝ) (CerosRealesL χ)) := by
  refine ⟨1, fun x hx => ?_⟩
  rcases hx with rfl | ⟨ρ, -, -, h1, rfl⟩
  · norm_num
  · exact h1.le

theorem Theta_L_mem_Icc (χ : DirichletCharacter ℂ N) : 1 / 2 ≤ Theta_L χ ∧ Theta_L χ ≤ 1 := by
  refine ⟨le_csSup (bddAbove_insert_cerosRealesL χ) (mem_insert _ _),
    csSup_le (insert_nonempty _ _) fun x hx => ?_⟩
  rcases hx with rfl | ⟨ρ, -, -, h1, rfl⟩
  · norm_num
  · exact h1.le

theorem sinCerosDerechaL_of_gt_Theta_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hgt : Theta_L χ < θ) : SinCerosDerechaL χ θ := by
  intro ρ hρ hL0
  have h12 : 1 / 2 < ρ.re := lt_of_le_of_lt (Theta_L_mem_Icc χ).1 (lt_trans hgt hρ)
  rcases le_or_gt 1 ρ.re with hge1 | hlt1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge1 hL0
  · have hmem : ρ.re ∈ insert (1 / 2 : ℝ) (CerosRealesL χ) :=
      Or.inr ⟨ρ, hL0, by linarith, hlt1, rfl⟩
    have hle : ρ.re ≤ Theta_L χ := le_csSup (bddAbove_insert_cerosRealesL χ) hmem
    linarith

/-- `Θ_χ = 1/2` si y solo si `L(s,χ) ≠ 0` en `Re s > 1/2`. -/
theorem Theta_L_eq_half_iff {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Theta_L χ = 1 / 2 ↔ ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro heq ρ hρ
    exact sinCerosDerechaL_of_gt_Theta_L hχ (θ := (1 / 2 + ρ.re) / 2)
      (by rw [heq]; linarith) ρ (by linarith)
  · intro hZ
    apply le_antisymm _ (Theta_L_mem_Icc χ).1
    refine csSup_le (insert_nonempty _ _) fun x hx => ?_
    rcases hx with rfl | ⟨ρ, hL0, -, -, rfl⟩
    · exact le_rfl
    · by_contra! hgt
      exact hZ ρ hgt hL0

omit [NeZero N] in
theorem E_nonneg_L (χ : DirichletCharacter ℂ N) (Q : ℕ) : 0 ≤ E χ Q :=
  tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (by unfold w; positivity)

/-- Cota lineal sin hipótesis: `E_{Q,χ} ≤ (1 + QN)²/(Q + 1)`. -/
theorem E_le_lineal_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) :
    E χ Q ≤ (1 + Q * N) ^ 2 / ((Q : ℝ) + 1) := by
  rw [← integral_sigma_sq_eq_E hχ Q]
  have hQ0 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) + 1 := by linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)]
  have hint := integrableOn_sigma_sq hχ Q
  have hsub : Ioi ((Q : ℝ) + 1) ⊆ Ioi 1 := Ioi_subset_Ioi hQ1
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (Q : ℝ) + 1 := by
    filter_upwards [(Set.countable_singleton ((Q : ℝ) + 1)).ae_notMem volume] with x hx
    simpa using hx
  have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi 1 \ Ioi ((Q : ℝ) + 1) →
      ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) = 0 := by
    filter_upwards [hne] with x hx hmem
    obtain ⟨h1, h2⟩ := hmem
    simp only [mem_Ioi, not_lt] at h1 h2
    have hlt : x < (Q : ℝ) + 1 := lt_of_le_of_ne h2 hx
    have hk1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1.le)
    have hkQ : ⌊x⌋₊ ≤ Q := by
      have : ⌊x⌋₊ < Q + 1 := (Nat.floor_lt (by linarith)).mpr (by exact_mod_cast hlt)
      omega
    rw [sigma_eq_zero hk1 hkQ, norm_zero]
    ring
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub hzero]
  have hg : IntegrableOn (fun x : ℝ => ((1 : ℝ) + Q * N) ^ 2 * x ^ (-2 : ℝ)) (Ioi ((Q : ℝ) + 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hQ0).const_mul _
  calc ∫ x in Ioi ((Q : ℝ) + 1), ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ)
      ≤ ∫ x in Ioi ((Q : ℝ) + 1), ((1 : ℝ) + Q * N) ^ 2 * x ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (hint.mono_set hsub) hg measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 < x := lt_trans hQ0 hx
        have hσ := norm_sigma_le hχ Q ⌊x⌋₊
        have hp := Real.rpow_nonneg hx0.le (-2 : ℝ)
        gcongr
    _ = (1 + Q * N) ^ 2 / ((Q : ℝ) + 1) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hQ0,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- **Teorema límite**: sin hipótesis, `lim_{Q → ∞} log(2 + E_{Q,χ}) / log Q = 2 Θ_χ − 1`. -/
theorem tendsto_log_energia_div_log_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Tendsto (fun Q : ℕ => Real.log (2 + E χ Q) / Real.log (Q : ℝ))
      atTop (𝓝 (2 * Theta_L χ - 1)) := by
  rw [tendsto_order]
  have hΘ_lo := (Theta_L_mem_Icc χ).1
  have hΘ_hi := (Theta_L_mem_Icc χ).2
  constructor
  · intro a ha
    set ε : ℝ := (2 * Theta_L χ - 1) - a
    have hε : 0 < ε := sub_pos.mpr ha
    rcases le_or_gt (Theta_L χ) (1 / 2 + ε / 4) with hsmall | hbig
    · filter_upwards [eventually_ge_atTop 2] with Q hQ
      have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
      have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
      have h2E : 1 ≤ 2 + E χ Q := by linarith [E_nonneg_L χ Q]
      have hnn : 0 ≤ Real.log (2 + E χ Q) / Real.log (Q : ℝ) :=
        div_nonneg (Real.log_nonneg h2E) hlogQ_pos.le
      have ha_neg : a < 0 := by simp only [ε] at hsmall; linarith
      exact lt_of_lt_of_le ha_neg hnn
    · have hlt_sup : max (1 / 2) (Theta_L χ - ε / 4) < Theta_L χ :=
        max_lt (by linarith) (by linarith)
      obtain ⟨x, hx_mem, hx_gt⟩ :=
        (lt_csSup_iff (bddAbove_insert_cerosRealesL χ) (insert_nonempty _ _)).mp hlt_sup
      have hx_ne : x ≠ 1 / 2 := by
        have := (max_lt_iff.mp hx_gt).1; linarith
      rcases hx_mem with rfl | ⟨ρ, hL0, -, -, rfl⟩
      · exact absurd rfl hx_ne
      · have hβ_gt12 : 1 / 2 < ρ.re := (max_lt_iff.mp hx_gt).1
        have hβ_gtΘ : Theta_L χ - ε / 4 < ρ.re := (max_lt_iff.mp hx_gt).2
        have hρ_ne0 : ρ ≠ 0 := by intro h; rw [h] at hβ_gt12; simp at hβ_gt12; linarith
        set c₀ : ℝ := (2 * ρ.re - 1) / ‖ρ‖ ^ 2
        have hc₀_pos : 0 < c₀ :=
          div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hρ_ne0))
        have hdiv0 : Tendsto (fun Q : ℕ => Real.log c₀ / Real.log (Q : ℝ)) atTop (𝓝 0) := by
          have hlog_top : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
          simpa using tendsto_const_nhds.div_atTop hlog_top
        have hev_c := (tendsto_order.mp hdiv0).1 (-(ε / 2)) (by linarith)
        filter_upwards [eventually_ge_atTop 2, hev_c] with Q hQ hlog_c
        have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
        have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
        have hQp : (0 : ℝ) < (Q : ℝ) + 1 := by linarith
        have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
        have hlow := cota_inferior_energia_cero hχ hL0 hβ_gt12 Q
        have hmul := mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hQp.le (2 * ρ.re - 1))
        have hrp : ((Q : ℝ) + 1) ^ (1 - 2 * ρ.re) * ((Q : ℝ) + 1) ^ (2 * ρ.re - 1) = 1 := by
          rw [← Real.rpow_add hQp, show (1 - 2 * ρ.re) + (2 * ρ.re - 1) = 0 by ring,
            Real.rpow_zero]
        rw [mul_assoc, hrp, mul_one] at hmul
        have hmono : (Q : ℝ) ^ (2 * ρ.re - 1) ≤ ((Q : ℝ) + 1) ^ (2 * ρ.re - 1) :=
          Real.rpow_le_rpow hQ_pos.le (by linarith) (by linarith)
        have h2E_gt : c₀ * (Q : ℝ) ^ (2 * ρ.re - 1) < 2 + E χ Q := by
          have : c₀ * (Q : ℝ) ^ (2 * ρ.re - 1) ≤ c₀ * ((Q : ℝ) + 1) ^ (2 * ρ.re - 1) :=
            mul_le_mul_of_nonneg_left hmono hc₀_pos.le
          linarith
        have hlog_le := Real.log_le_log (by positivity) h2E_gt.le
        rw [Real.log_mul hc₀_pos.ne' (Real.rpow_pos_of_pos hQ_pos _).ne',
          Real.log_rpow hQ_pos] at hlog_le
        have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
        rw [add_div, mul_div_cancel_right₀ _ hlogQ_pos.ne'] at hdiv_le
        simp only [ε] at hβ_gtΘ hlog_c
        linarith
  · intro b hb
    set ε : ℝ := b - (2 * Theta_L χ - 1)
    have hε : 0 < ε := sub_pos.mpr hb
    have hlog_top : Tendsto (fun Q : ℕ => Real.log (Q : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    rcases eq_or_lt_of_le hΘ_hi with hΘ_eq1 | hΘ_lt1
    · set C_lin : ℝ := 2 + 2 * (1 + (N : ℝ)) ^ 2
      have hClin_pos : 0 < C_lin := by simp only [C_lin]; positivity
      have hdiv0 : Tendsto (fun Q : ℕ => Real.log C_lin / Real.log (Q : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop hlog_top
      have hev := (tendsto_order.mp hdiv0).2 (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop 2, hev] with Q hQ hlog_c
      have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      have hQp : (0 : ℝ) < (Q : ℝ) + 1 := by linarith
      have hlogQ_pos : 0 < Real.log (Q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hE := E_le_lineal_L hχ Q
      have hlin : (1 + Q * N) ^ 2 / ((Q : ℝ) + 1) ≤ (1 + (N : ℝ)) ^ 2 * ((Q : ℝ) + 1) := by
        rw [div_le_iff₀ hQp]
        have h1 : (1 : ℝ) + Q * N ≤ (1 + N) * ((Q : ℝ) + 1) := by nlinarith
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        nlinarith
      have h2E : 2 + E χ Q ≤ C_lin * (Q : ℝ) := by simp only [C_lin]; nlinarith
      have hlog_le := Real.log_le_log (by linarith [E_nonneg_L χ Q]) h2E
      rw [Real.log_mul hClin_pos.ne' hQ_pos.ne'] at hlog_le
      have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
      rw [add_div, div_self hlogQ_pos.ne'] at hdiv_le
      simp only [ε] at hlog_c
      linarith
    · set θ' : ℝ := min (Theta_L χ + ε / 4) ((Theta_L χ + 1) / 2)
      have hθ'_gt : Theta_L χ < θ' := lt_min (by linarith) (by linarith)
      have hθ'_lt1 : θ' < 1 := (min_le_right _ _).trans_lt (by linarith)
      have hθ'_ge12 : 1 / 2 ≤ θ' := hΘ_lo.trans hθ'_gt.le
      have hθ'_le : θ' ≤ Theta_L χ + ε / 4 := min_le_left _ _
      obtain ⟨C, hC⟩ := energia_cota_theta_L hχ hθ'_ge12 hθ'_lt1
        (sinCerosDerechaL_of_gt_Theta_L hχ hθ'_gt) (ε / 4) (by positivity)
      set C_up : ℝ := 2 + max C 0
      have hCup_pos : 0 < C_up := by simp only [C_up]; positivity
      have hdiv0 : Tendsto (fun Q : ℕ => Real.log C_up / Real.log (Q : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop hlog_top
      have hev := (tendsto_order.mp hdiv0).2 (ε / 8) (by positivity)
      filter_upwards [eventually_ge_atTop 2, hev] with Q hQ hlog_c
      have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      have hlogQ_pos : 0 < Real.log (Q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
      set p_exp : ℝ := 2 * θ' - 1 + ε / 4
      have hp_nn : 0 ≤ p_exp := by simp only [p_exp]; linarith
      have hp_le : p_exp ≤ 2 * Theta_L χ - 1 + 3 * ε / 4 := by simp only [p_exp]; linarith
      have hQp_ge1 : 1 ≤ (Q : ℝ) ^ p_exp := Real.one_le_rpow hQ1 hp_nn
      have hEQ := hC Q (by omega)
      have h2E : 2 + E χ Q ≤ C_up * (Q : ℝ) ^ p_exp := by
        have hC_max : C * (Q : ℝ) ^ p_exp ≤ max C 0 * (Q : ℝ) ^ p_exp :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hQ_pos.le _)
        simp only [C_up]; nlinarith
      have hlog_le := Real.log_le_log (by linarith [E_nonneg_L χ Q]) h2E
      rw [Real.log_mul hCup_pos.ne' (Real.rpow_pos_of_pos hQ_pos _).ne',
        Real.log_rpow hQ_pos] at hlog_le
      have hdiv_le := div_le_div_of_nonneg_right hlog_le hlogQ_pos.le
      rw [add_div, mul_div_cancel_right₀ _ hlogQ_pos.ne'] at hdiv_le
      simp only [ε] at hp_le hlog_c
      linarith

end AMate.Dirichlet
