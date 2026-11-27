import AMateMiller.Determinista
import AMateConAlpoge.HipotesisAlpoge
import Main
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula

/-!
# Composición con Alpöge: test de Miller determinista sin hipótesis

La biblioteca de Alpöge demuestra las tres hipótesis de `AMate.Miller.esPrimoMiller_de_grh`:

* `explicitFormula_closed : PI.ExplicitFormula` (fórmula explícita truncada para `ψ(x,χ)`);
* `zerosWindow_closed : PI.ZerosWindow` (ceros en ventanas de altura `1`);
* `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine` (GRH, caracteres
  primitivos).

Las definiciones de `AMate.Miller.PI` son copias literales de las de Alpöge, así que encajan por
igualdad definicional. Resultado: existe `K > 0` tal que el test de Miller con `⌊K (1 + log n)^4⌋`
bases decide la primalidad, sin hipótesis, y lo mismo con `⌊K (1 + log n)^2⌋` bases
(`esPrimoMiller_cuad_alpoge`).

Con las hipótesis analíticas de `HipotesisAlpoge.lean` y GRH, la cota tiene constante explícita:
`a ≤ 2 (log n)²` si `log n ≥ 64` (`cota_bach_explicita_alpoge`), y el test
`esPrimoMiller basesExplicitas`, con `(⌊log₂ n⌋ + 1)²` bases para `n ≥ 2^93`, es un test
ejecutable y certificado sin hipótesis (`esPrimoMiller_explicito_alpoge`).

Como `Composicion.lean`, este archivo no se compila por defecto: necesita la biblioteca
completa de Alpöge.
-/

namespace AMate.Miller

/-- Cota de tipo Bach sin hipótesis, con `O((log n)^4)` bases. -/
theorem cota_bach_alpoge : ∃ K : ℝ, 0 < K ∧ CotaCaracteres (basesBach K) := by
  obtain ⟨K, hK, h⟩ := cota_caracteres_de_grh' explicitFormula_closed zerosWindow_closed
    LFunction_eq_zero_re_of_isPrimitive
  exact ⟨K, hK, cotaCaracteres_basesBach h⟩

/-- Test de Miller determinista con `⌊K (1 + log n)^4⌋` bases, correcto sin hipótesis. -/
theorem esPrimoMiller_alpoge :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, esPrimoMiller (basesBach K) n = true ↔ n.Prime :=
  esPrimoMiller_de_grh explicitFormula_closed zerosWindow_closed
    LFunction_eq_zero_re_of_isPrimitive

/-- Cota de tipo Bach sin hipótesis, con `O((log n)^2)` bases. -/
theorem cota_bach_cuad_alpoge : ∃ K : ℝ, 0 < K ∧ CotaCaracteres (basesBach2 K) := by
  obtain ⟨K, hK, h⟩ := cota_caracteres_de_grh_cuad' explicitFormula_closed zerosWindow_closed
    LFunction_eq_zero_re_of_isPrimitive
  exact ⟨K, hK, cotaCaracteres_basesBach2 h⟩

/-- Test de Miller determinista con `⌊K (1 + log n)^2⌋` bases, correcto sin hipótesis. -/
theorem esPrimoMiller_cuad_alpoge :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, esPrimoMiller (basesBach2 K) n = true ↔ n.Prime :=
  esPrimoMiller_de_grh_cuad explicitFormula_closed zerosWindow_closed
    LFunction_eq_zero_re_of_isPrimitive

/-- Cota de Bach con constante explícita, sin hipótesis: si `log n ≥ 64`, todo carácter
`χ ≠ 1` módulo `n` toma un valor `≠ 1` en algún `a ≤ 2 (log n)²` coprimo con `n`. -/
theorem cota_bach_explicita_alpoge :
    ∀ n : ℕ, 64 ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 :=
  cota_bach_explicita_de_grh LFunction_eq_zero_re_of_isPrimitive

/-- Test de Miller ejecutable y certificado, sin hipótesis. -/
theorem esPrimoMiller_explicito_alpoge (n : ℕ) :
    esPrimoMiller basesExplicitas n = true ↔ n.Prime :=
  esPrimoMiller_explicito_de_grh LFunction_eq_zero_re_of_isPrimitive n

end AMate.Miller

#print axioms AMate.Miller.cota_bach_alpoge
#print axioms AMate.Miller.esPrimoMiller_alpoge
#print axioms AMate.Miller.cota_bach_cuad_alpoge
#print axioms AMate.Miller.esPrimoMiller_cuad_alpoge
#print axioms AMate.Miller.cota_bach_explicita_alpoge
#print axioms AMate.Miller.esPrimoMiller_explicito_alpoge
