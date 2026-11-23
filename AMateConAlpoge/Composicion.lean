import AMateEnergia.Teorema
import Main

/-!
# Composición con el teorema de Alpöge

`riemannHypothesis : RiemannHypothesis` está en el módulo `Main` de la biblioteca de Alpöge
(paquete `tree`, Lean 4.33.1, Mathlib `0df444a`). Este archivo no se compila por defecto:
ver `lakefile.toml`.
-/

/-- Cota de energía de AMate sin hipótesis, usando el teorema de Alpöge (2026). -/
theorem AMate.energia_subpolinomial_alpoge :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → AMate.E Q ≤ C * (Q : ℝ) ^ ε :=
  AMate.energia_subpolinomial riemannHypothesis
