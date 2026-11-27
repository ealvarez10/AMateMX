import AMateDirichlet.Calibracion
import Main

/-!
# Composición con Alpöge: energía de los caracteres de Dirichlet

`LFunction_ne_zero_of_half_lt_re` (módulo `Main` de la biblioteca de Alpöge) da
`L(s,χ) ≠ 0` en `Re s > 1/2` para todo carácter de Dirichlet. Con el recíproco del Teorema 7
(`AMate.Dirichlet.grh_iff_energia_subpolinomial`) se obtiene, sin hipótesis:

* `energia_dirichlet_subpolinomial_alpoge`: `E_{Q,χ} ≤ C_ε Q^ε` para todo `Q ≥ 1`;
* `Theta_L_alpoge`: `Θ_χ = 1/2`;
* `tendsto_log_energia_dirichlet_alpoge`: `log(2 + E_{Q,χ}) / log Q → 0`.

Como `Composicion.lean`, este archivo no se compila por defecto: necesita la biblioteca completa
de Alpöge.
-/

namespace AMate.Dirichlet

variable {N : ℕ} [NeZero N]

/-- GRH para `χ`, a partir del teorema de Alpöge. -/
theorem sin_ceros_mitad_alpoge {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro s hs
  have h : DirichletLNonvanishingRightOfHalf := LFunction_ne_zero_of_half_lt_re
  unfold DirichletLNonvanishingRightOfHalf at h
  exact h N χ s hs (Or.inl hχ)

/-- Energía de un carácter sin hipótesis: `E_{Q,χ} ≤ C_ε Q^ε`. -/
theorem energia_dirichlet_subpolinomial_alpoge {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → E χ Q ≤ C * (Q : ℝ) ^ ε :=
  (grh_iff_energia_subpolinomial hχ).mp (sin_ceros_mitad_alpoge hχ)

theorem Theta_L_alpoge {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : Theta_L χ = 1 / 2 :=
  (Theta_L_eq_half_iff hχ).mpr (sin_ceros_mitad_alpoge hχ)

/-- `log(2 + E_{Q,χ}) / log Q → 0` sin hipótesis. -/
theorem tendsto_log_energia_dirichlet_alpoge {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Filter.Tendsto (fun Q : ℕ => Real.log (2 + E χ Q) / Real.log (Q : ℝ)) Filter.atTop
      (nhds 0) := by
  have h := tendsto_log_energia_div_log_L hχ
  rwa [Theta_L_alpoge hχ, show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num] at h

end AMate.Dirichlet

#print axioms AMate.Dirichlet.energia_dirichlet_subpolinomial_alpoge
#print axioms AMate.Dirichlet.tendsto_log_energia_dirichlet_alpoge
