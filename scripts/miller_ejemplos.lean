import AMateMiller.DeterministaExplicito

/-!
# Ejemplos ejecutables del test de Miller

No forma parte de las bibliotecas. Ejecutar desde la raíz del repositorio, después de `lake build`, con `lake env lean scripts/miller_ejemplos.lean`.

* `esPrimoMiller id` es correcto sin hipótesis (`esPrimoMiller_id_correcto`), pero usa hasta `n`
  bases.
* `basesExplicitas n = (⌊log₂ n⌋ + 1)²` para `n ≥ 2^93` (todas las bases `a ≤ n` por debajo).
  Bajo GRH y las hipótesis analíticas de Alpöge, `esPrimoMiller basesExplicitas` decide la
  primalidad (`esPrimoMiller_explicito`, a partir de la cota de Bach explícita `a ≤ 2 (log n)²`
  para `log n ≥ 64`); `AMateConAlpoge/MillerAlpoge.lean` lo da sin hipótesis.
* `bach n = 2 (⌊log₂ n⌋ + 1)²` imita la cota de Bach para `n` pequeños, donde la cota formalizada
  no se aplica; las comparaciones con `bach` son solo una comprobación numérica.
-/

open AMate.Miller

/-- Cota de Bach con logaritmo en base 2 (solo para los ejemplos). -/
def bach (n : ℕ) : ℕ := 2 * (Nat.log 2 n + 1) ^ 2

-- Cota trivial, sin hipótesis: coincide con `Nat.Prime` para `n < 3000`.
#eval (List.range 3000).all fun n => esPrimoMiller id n == decide n.Prime

-- Cota de Bach: coincide con `Nat.Prime` para `n < 100000`.
#eval (List.range 100000).all fun n => esPrimoMiller bach n == decide n.Prime

-- Números de Carmichael: compuestos que engañan al test de Fermat.
#eval [561, 1105, 1729, 2465, 2821, 6601, 8911, 41041, 825265].map (esPrimoMiller bach)

-- Primo de Mersenne 2^61 − 1 y un compuesto cercano.
#eval (esPrimoMiller bach (2 ^ 61 - 1), esPrimoMiller bach (2 ^ 61 + 1))

-- Test certificado: número de bases para 2^127 − 1 (16129 = 127²).
#eval basesExplicitas (2 ^ 127 - 1)

-- Test certificado: primos de Mersenne 2^107 − 1 y 2^127 − 1, y dos compuestos.
#eval (esPrimoMiller basesExplicitas (2 ^ 107 - 1), esPrimoMiller basesExplicitas (2 ^ 127 - 1),
  esPrimoMiller basesExplicitas (2 ^ 127 + 1),
  esPrimoMiller basesExplicitas ((2 ^ 127 - 1) * (2 ^ 61 - 1)))
