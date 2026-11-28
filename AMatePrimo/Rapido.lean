/-!
# Test de Miller certificado: versión sin dependencias

Copia, solo con el núcleo de Lean (sin Mathlib), de las funciones ejecutables de
`AMateMiller/Ejecutable.lean` y de `basesCertificadas`, para compilar un ejecutable pequeño.
`AMateMiller/Rapido.lean` demuestra que `esPrimo n = esPrimoMiller basesCertificadas n`, así que
este programa hereda la corrección del test certificado.
-/

namespace AMate.Primo

/-- Exponenciación modular por cuadrados. -/
def powMod (a e n : Nat) : Nat :=
  if e = 0 then 1 % n
  else
    let r := powMod a (e / 2) n
    if e % 2 = 0 then r * r % n else r * r % n * (a % n) % n
termination_by e
decreasing_by omega

/-- `(s, d)` con `m = 2^s d` y `d` impar (para `m ≠ 0`). -/
def partePar (m : Nat) : Nat × Nat :=
  if m ≠ 0 ∧ m % 2 = 0 then ((partePar (m / 2)).1 + 1, (partePar (m / 2)).2) else (0, m)
termination_by m
decreasing_by omega

/-- Decide si `a` es mentiroso fuerte para `n`. -/
def pasaMiller (n a : Nat) : Bool :=
  powMod a (partePar (n - 1)).2 n == 1 % n
    || (List.range (partePar (n - 1)).1).any
      (fun r => powMod a (2 ^ r * (partePar (n - 1)).2) n == n - 1)

/-- Test de Miller con las bases `a ≤ B n` coprimas con `n`. -/
def testMiller (B : Nat → Nat) (n : Nat) : Bool :=
  (List.range (B n + 1)).all (fun a => Nat.gcd a n != 1 || pasaMiller n a)

/-- Test completo. -/
def esPrimoMiller (B : Nat → Nat) (n : Nat) : Bool :=
  if n < 2 then false else if n = 2 then true else if n % 2 = 0 then false else testMiller B n

/-- Número de bases certificado por tramos (`basesCertificadas`, con `Nat.log2`). -/
def bases (n : Nat) : Nat :=
  if n < 2 ^ 12 then n
  else if n < 2 ^ 34 then 8 * (Nat.log2 n + 1) ^ 2
  else if n < 2 ^ 93 then 2 * (Nat.log2 n + 1) ^ 2
  else (Nat.log2 n + 1) ^ 2

/-- El test certificado. -/
def esPrimo (n : Nat) : Bool := esPrimoMiller bases n

end AMate.Primo
