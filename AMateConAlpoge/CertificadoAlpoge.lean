import AMateMiller.MillerCertificado
import AMateMiller.Rapido
import AMateConAlpoge.HipotesisAlpoge
import Main

/-!
# Composición con Alpöge: test certificado para todo `n` y menor no-residuo, sin hipótesis

Con las hipótesis analíticas de `HipotesisAlpoge.lean` y la GRH de la biblioteca de Alpöge
(`LFunction_eq_zero_re_of_isPrimitive`):

* `esPrimoMiller_certificado_alpoge`: el test de Miller con `basesCertificadas` (todas las bases
  solo por debajo de `4096`) decide la primalidad;
* `noResiduo_16_alpoge`, `noResiduo_explicito_alpoge`: todo primo impar `p` con `log p ≥ 8.3`
  tiene un no-residuo cuadrático `a ≤ 16 (log p)²`, y `a ≤ 2 (log p)²` si `log p ≥ 64`;
* `esPrimo_alpoge`: el programa `amate-primo` (`AMate.Primo.esPrimo`) decide la primalidad.

Como `MillerAlpoge.lean`, importa `Main` y no se compila por defecto.
-/

namespace AMate.Miller

/-- Test de Miller certificado para todo `n`, sin hipótesis. -/
theorem esPrimoMiller_certificado_alpoge (n : ℕ) :
    esPrimoMiller basesCertificadas n = true ↔ n.Prime :=
  esPrimoMiller_certificado hipHadamard_alpoge serieDigamma_alpoge
    LFunction_eq_zero_re_of_isPrimitive n

/-- Menor no-residuo cuadrático con constante `16`, sin hipótesis. -/
theorem noResiduo_16_alpoge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : 83 / 10 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 16 * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) :=
  noResiduo_16 hipHadamard_alpoge serieDigamma_alpoge LFunction_eq_zero_re_of_isPrimitive hp hp2 hL

/-- Menor no-residuo cuadrático con constante `2`, sin hipótesis. -/
theorem noResiduo_explicito_alpoge {p : ℕ} (hp : p.Prime) (hL : 64 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) :=
  noResiduo_explicito hipHadamard_alpoge serieDigamma_alpoge LFunction_eq_zero_re_of_isPrimitive
    hp hL

/-- El programa `amate-primo` decide la primalidad, sin hipótesis. -/
theorem esPrimo_alpoge (n : ℕ) : AMate.Primo.esPrimo n = true ↔ n.Prime :=
  esPrimo_correcto hipHadamard_alpoge serieDigamma_alpoge LFunction_eq_zero_re_of_isPrimitive n

end AMate.Miller

#print axioms AMate.Miller.esPrimoMiller_certificado_alpoge
#print axioms AMate.Miller.noResiduo_16_alpoge
#print axioms AMate.Miller.noResiduo_explicito_alpoge
#print axioms AMate.Miller.esPrimo_alpoge
