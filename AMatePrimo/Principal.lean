import AMatePrimo.Rapido

/-!
# `amate-primo`: test de primalidad certificado desde la línea de comandos

Uso: `amate-primo N [N ...]`. Para cada `N` imprime si es primo o compuesto y cuántas bases usa.
La corrección está en `AMateMiller/Rapido.lean` (`esPrimo_correcto`, bajo GRH y las hipótesis
analíticas de Alpöge) y, sin hipótesis, en `AMateConAlpoge/CertificadoAlpoge.lean`.
-/

open AMate.Primo

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Uso: amate-primo N [N ...]"
    return 1
  let mut codigo : UInt32 := 0
  for s in args do
    match s.toNat? with
    | some n =>
      let r := if esPrimo n then "primo" else "compuesto"
      IO.println s!"{n}: {r} ({bases n} bases)"
    | none =>
      IO.eprintln s!"No es un número natural: {s}"
      codigo := 1
  return codigo
