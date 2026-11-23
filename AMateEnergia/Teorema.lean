import AMateEnergia.Elementales
import AMateEnergia.Analitica
import AMateEnergia.Reciproco

/-!
# Teorema principal: equivalencia entre la hipótesis de Riemann y la energía de AMate

Estado 45, §1 ((1.2) ↔ (1.3) ↔ (1.4)) y §6 ((6.3)–(6.4) con `θ = 1/2`), más el recíproco de los
Estados 39 y 45 (`AMateEnergia.Reciproco`).
-/

open Complex MeasureTheory

namespace AMate

/-- Bajo la hipótesis de Riemann, la energía de AMate crece más despacio que cualquier
potencia positiva de `Q`, con una constante válida para todos los `Q ≥ 2`.

Demostración (estado 45, §6): `δ = min (ε/2) (1/4)` y `η = 1/8`. Por `E_eq_integral` y
`|1 − z|² ≤ 2 + 2|z|²`, `E_Q` es a lo sumo `(1/2π) ∫ (2 + 2 |ζ|² |P|²)/(1/4 + x²)`.
Con `zeta_recta_critica` (exponente `1/3`) y `P_recta_critica` el integrando queda acotado
por `C (1 + Q^{2δ}) (1 + |x|)^{11/12}/(1/4 + x²)`, que es integrable porque `2/3 + 1/4 < 1`;
y `Q^{2δ} ≤ Q^ε`. -/
theorem energia_subpolinomial (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε := by
  intro ε hε
  set δ : ℝ := min (ε / 2) (1 / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ' : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : 2 * δ ≤ ε := by
    have := min_le_left (ε / 2) (1 / 4)
    linarith
  obtain ⟨Cζ, hCζ⟩ := zeta_recta_critica
  obtain ⟨CP, hCP⟩ := P_recta_critica hRH hδ hδ' (show (0 : ℝ) < 1 / 8 by norm_num)
  set K : ℝ := Cζ ^ 2 * CP ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hint1 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hint2 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(13 / 12 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set I₁ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ)) with hI₁
  set I₂ : ℝ := ∫ x : ℝ, (1 + ‖x‖) ^ (-(13 / 12 : ℝ)) with hI₂
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun x => by positivity
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun x => by positivity
  refine ⟨(16 * I₁ + 16 * K * I₂) / (2 * Real.pi), fun Q hQ => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ2δ : (Q : ℝ) ^ (2 * δ) ≤ (Q : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hQ1 hδε
  have hQ2δ1 : 1 ≤ (Q : ℝ) ^ (2 * δ) := Real.one_le_rpow hQ1 (by positivity)
  rw [E_eq_integral hQ]
  set g : ℝ → ℝ := fun x => 16 * (1 + ‖x‖) ^ (-(2 : ℝ))
    + 16 * K * (Q : ℝ) ^ (2 * δ) * (1 + ‖x‖) ^ (-(13 / 12 : ℝ)) with hg
  have hgint : Integrable g := (hint1.const_mul 16).add (hint2.const_mul _)
  have hpt : ∀ x : ℝ,
      ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2)
        ≤ g x := by
    intro x
    set y : ℝ := 1 + |x| with hy
    have hy0 : 0 < y := by positivity
    set z := riemannZeta (1 / 2 + (x : ℂ) * I) with hz
    set p := P Q (1 / 2 + (x : ℂ) * I) with hp
    have hζ2 : ‖z‖ ^ 2 ≤ Cζ ^ 2 * y ^ (2 / 3 : ℝ) := by
      have e : (y ^ (1 / 3 : ℝ)) ^ 2 = y ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
        norm_num
      calc ‖z‖ ^ 2 ≤ (Cζ * y ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCζ x) 2
        _ = Cζ ^ 2 * y ^ (2 / 3 : ℝ) := by rw [mul_pow, e]
    have hP2 : ‖p‖ ^ 2 ≤ CP ^ 2 * (Q : ℝ) ^ (2 * δ) * y ^ (1 / 4 : ℝ) := by
      have e1 : ((Q : ℝ) ^ δ) ^ 2 = (Q : ℝ) ^ (2 * δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
        ring_nf
      have e2 : (y ^ (1 / 8 : ℝ)) ^ 2 = y ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
        norm_num
      calc ‖p‖ ^ 2 ≤ (CP * (Q : ℝ) ^ δ * y ^ (1 / 8 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hCP Q hQ x) 2
        _ = CP ^ 2 * (Q : ℝ) ^ (2 * δ) * y ^ (1 / 4 : ℝ) := by rw [mul_pow, mul_pow, e1, e2]
    have hprod : ‖z‖ ^ 2 * ‖p‖ ^ 2 ≤ K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ) := by
      have e : y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ) = y ^ (11 / 12 : ℝ) := by
        rw [← Real.rpow_add hy0]
        norm_num
      calc ‖z‖ ^ 2 * ‖p‖ ^ 2
          ≤ (Cζ ^ 2 * y ^ (2 / 3 : ℝ)) * (CP ^ 2 * (Q : ℝ) ^ (2 * δ) * y ^ (1 / 4 : ℝ)) :=
            mul_le_mul hζ2 hP2 (by positivity) (by positivity)
        _ = K * (Q : ℝ) ^ (2 * δ) * (y ^ (2 / 3 : ℝ) * y ^ (1 / 4 : ℝ)) := by rw [hK]; ring
        _ = K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ) := by rw [e]
    have hnum : ‖1 - z * p‖ ^ 2 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ)) := by
      have h1 : ‖1 - z * p‖ ≤ 1 + ‖z‖ * ‖p‖ := by
        calc ‖1 - z * p‖ ≤ ‖(1 : ℂ)‖ + ‖z * p‖ := norm_sub_le _ _
          _ = 1 + ‖z‖ * ‖p‖ := by rw [norm_one, norm_mul]
      have h2 : ‖1 - z * p‖ ^ 2 ≤ (1 + ‖z‖ * ‖p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (1 + ‖z‖ * ‖p‖) ^ 2 ≤ 2 + 2 * (‖z‖ ^ 2 * ‖p‖ ^ 2) := by
        nlinarith [sq_nonneg (‖z‖ * ‖p‖ - 1)]
      linarith
    have hden : y ^ 2 / 8 ≤ 1 / 4 + x ^ 2 := by
      rw [hy]
      nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
    have hy2 : 0 < y ^ 2 / 8 := by positivity
    have hB0 : 0 ≤ 2 + 2 * (K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ)) := by positivity
    have hnx : (1 + ‖x‖) = y := by rw [Real.norm_eq_abs]
    calc ‖1 - z * p‖ ^ 2 / (1 / 4 + x ^ 2)
        ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ))) / (1 / 4 + x ^ 2) := by
          gcongr
      _ ≤ (2 + 2 * (K * (Q : ℝ) ^ (2 * δ) * y ^ (11 / 12 : ℝ))) / (y ^ 2 / 8) :=
          div_le_div_of_nonneg_left hB0 hy2 hden
      _ = 16 * (y ^ 2)⁻¹ + 16 * K * (Q : ℝ) ^ (2 * δ) * (y ^ (11 / 12 : ℝ) / y ^ 2) := by
          field_simp
          ring
      _ = g x := by
          simp only [hg, hnx]
          rw [Real.rpow_neg hy0.le, Real.rpow_two, ← Real.rpow_two y,
            show -(13 / 12 : ℝ) = 11 / 12 - 2 by norm_num, Real.rpow_sub hy0]
  have hf0 : ∀ x : ℝ, 0 ≤
      ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2) :=
    fun x => by positivity
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall hf0) hgint
    (Filter.Eventually.of_forall hpt)
  have hgval : ∫ x : ℝ, g x = 16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * δ) * I₂ := by
    simp only [hg]
    rw [integral_add (hint1.const_mul 16) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hgval] at hmono
  have hpi : 0 < 2 * Real.pi := by positivity
  calc 1 / (2 * Real.pi) * ∫ x : ℝ,
        ‖1 - riemannZeta (1 / 2 + (x : ℂ) * I) * P Q (1 / 2 + (x : ℂ) * I)‖ ^ 2 / (1 / 4 + x ^ 2)
      ≤ 1 / (2 * Real.pi) * (16 * I₁ + 16 * K * (Q : ℝ) ^ (2 * δ) * I₂) := by gcongr
    _ ≤ 1 / (2 * Real.pi) * ((16 * I₁ + 16 * K * I₂) * (Q : ℝ) ^ ε) := by
        gcongr
        nlinarith [mul_nonneg hK0 hI₂0]
    _ = (16 * I₁ + 16 * K * I₂) / (2 * Real.pi) * (Q : ℝ) ^ ε := by ring

/-- Estado 45, (1.2) ↔ (1.3): la hipótesis de Riemann equivale al crecimiento subpolinomial
uniforme de la energía canónica `E_Q`. -/
theorem rh_iff_energia_subpolinomial :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε :=
  ⟨energia_subpolinomial, rh_de_energia_subpolinomial⟩

/-- Estado 45, (1.2) ↔ (1.4): la hipótesis de Riemann equivale al crecimiento subpolinomial
de `E_Q` sobre una sucesión ilimitada de escalas. -/
theorem rh_iff_energia_cofinal :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧ E Q ≤ C * (Q : ℝ) ^ ε :=
  ⟨fun hRH ε hε =>
      let ⟨C, hC⟩ := energia_subpolinomial hRH ε hε
      ⟨C, fun Q₀ => ⟨max Q₀ 2, le_max_left _ _, hC _ (le_max_right _ _)⟩⟩,
    rh_de_energia_cofinal⟩

end AMate
