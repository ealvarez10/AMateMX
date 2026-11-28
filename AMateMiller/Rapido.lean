import AMateMiller.MillerCertificado
import AMatePrimo.Rapido

/-!
# El programa `amate-primo` calcula el test certificado

`AMatePrimo/Rapido.lean` copia, sin Mathlib, las funciones ejecutables del test. Aquí se demuestra
que coinciden con las de la biblioteca (`esPrimo_eq`): `AMate.Primo.esPrimo n` es
`esPrimoMiller basesCertificadas n`. Por tanto el programa decide la primalidad bajo GRH y las
hipótesis analíticas de Alpöge (`esPrimo_correcto`), y sin hipótesis con la composición de
`AMateConAlpoge/CertificadoAlpoge.lean`.
-/

namespace AMate.Miller

open AMate.Miller.Hadamard AMate.Miller.PI.Digamma

theorem powMod_rapido (a e n : ℕ) : AMate.Primo.powMod a e n = powMod a e n := by
  rw [powMod_eq]
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [AMate.Primo.powMod]
    split_ifs with h0 h2
    · subst h0
      simp
    · simp only
      rw [ih (e / 2) (by omega), ← Nat.mul_mod, ← pow_add]
      congr 2
      omega
    · simp only
      have he : a ^ e = a ^ (e / 2) * a ^ (e / 2) * a := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      rw [ih (e / 2) (by omega), he, Nat.mul_mod (a ^ (e / 2) * a ^ (e / 2)) a n,
        Nat.mul_mod (a ^ (e / 2)) (a ^ (e / 2)) n]

theorem partePar_rapido (m : ℕ) : AMate.Primo.partePar m = partePar m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [AMate.Primo.partePar, partePar]
    split_ifs with h
    · rw [ih (m / 2) (by omega)]
    · rfl

theorem pasaMiller_rapido (n a : ℕ) : AMate.Primo.pasaMiller n a = pasaMiller n a := by
  unfold AMate.Primo.pasaMiller pasaMiller
  simp only [powMod_rapido, partePar_rapido]

theorem esPrimoMiller_rapido (B : ℕ → ℕ) (n : ℕ) :
    AMate.Primo.esPrimoMiller B n = esPrimoMiller B n := by
  unfold AMate.Primo.esPrimoMiller esPrimoMiller AMate.Primo.testMiller testMiller
  simp only [pasaMiller_rapido]

theorem bases_rapido (n : ℕ) : AMate.Primo.bases n = basesCertificadas n := by
  unfold AMate.Primo.bases basesCertificadas
  simp only [Nat.log2_eq_log_two]

/-- **El programa calcula el test certificado.** -/
theorem esPrimo_eq (n : ℕ) : AMate.Primo.esPrimo n = esPrimoMiller basesCertificadas n := by
  unfold AMate.Primo.esPrimo
  rw [esPrimoMiller_rapido]
  congr 1
  funext m
  exact bases_rapido m

/-- **Corrección del programa** bajo GRH y las hipótesis analíticas de Alpöge. -/
theorem esPrimo_correcto (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) (n : ℕ) :
    AMate.Primo.esPrimo n = true ↔ n.Prime := by
  rw [esPrimo_eq]
  exact esPrimoMiller_certificado h hS hG n

end AMate.Miller
