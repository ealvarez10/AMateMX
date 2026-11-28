import AMateMiller.Determinista
import AMateMiller.BachExplicito

/-!
# Test de Miller certificado con constante explícita

Con la cota de Bach explícita (`cota_bach_explicita`: `a ≤ 2 (log n)²` si `log n ≥ 64`), el
número de bases

  `basesExplicitas n = (⌊log₂ n⌋ + 1)²`  si `n ≥ 2^93`,   `n`  si `n < 2^93`,

es computable y cumple `CotaCaracteres` bajo GRH y las hipótesis analíticas de Alpöge. Por tanto
`esPrimoMiller basesExplicitas` decide la primalidad (`esPrimoMiller_explicito`).

* Si `n ≥ 2^93`, entonces `log n ≥ 93 log 2 > 64` y `2 (log n)² ≤ 2 (log 2)² (⌊log₂ n⌋ + 1)²
  ≤ (⌊log₂ n⌋ + 1)²`, porque `2 (log 2)² < 0.961`.
* Si `n < 2^93` se usan todas las bases `a ≤ n` (correcto sin hipótesis, pero lento).

`basesCertificadas` (`MillerCertificado.lean`) lo mejora: con las cotas de constante `16` y `4`
solo usa todas las bases por debajo de `4096`. `basesExplicitas` se conserva porque es la versión
que se compiló con la biblioteca de Alpöge en la máquina virtual (`MillerAlpoge.lean`).
-/

namespace AMate.Miller

open AMate.Miller.Hadamard AMate.Miller.PI.Digamma

/-- Número de bases explícito y computable. -/
def basesExplicitas (n : ℕ) : ℕ := if n < 2 ^ 93 then n else (Nat.log 2 n + 1) ^ 2

/-- Todo carácter no trivial toma un valor `≠ 1` en una unidad `a < n`. -/
theorem existe_base_trivial {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1) :
    ∃ a : ℕ, a ≤ n ∧ Nat.Coprime a n ∧ χ (a : ZMod n) ≠ 1 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  refine ⟨(u : ZMod n).val, (ZMod.val_lt _).le, ZMod.val_coe_unit_coprime u, ?_⟩
  rwa [ZMod.natCast_zmod_val]

/-- `log n ≥ 64` si `n ≥ 2^93`. -/
theorem log_ge_64 {n : ℕ} (hn : 2 ^ 93 ≤ n) : 64 ≤ Real.log n := by
  have h1 : Real.log ((2 : ℝ) ^ 93) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn)
  rw [Real.log_pow] at h1
  have := Real.log_two_gt_d9
  push_cast at h1
  linarith

/-- `2 (log n)² ≤ (⌊log₂ n⌋ + 1)²` para `n ≥ 1`. -/
theorem dos_log_sq_le {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.log n ^ 2 ≤ (((Nat.log 2 n + 1) ^ 2 : ℕ) : ℝ) := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log n < Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
    Real.log_lt_log hn0 (by exact_mod_cast hlt)
  rw [Real.log_pow] at h1
  push_cast at h1 ⊢
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hl2 := Real.log_two_lt_d9
  have hk : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  have h2 : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * (6932 / 10000) := by
    have : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ ((Nat.log 2 n : ℝ) + 1) * (6932 / 10000) :=
      mul_le_mul_of_nonneg_left (by norm_num at hl2 ⊢; linarith) hk
    linarith
  have h3 : Real.log n ^ 2 ≤ (((Nat.log 2 n : ℝ) + 1) * (6932 / 10000)) ^ 2 :=
    pow_le_pow_left₀ hl0 h2 2
  nlinarith

/-- **Cota para caracteres explícita.** -/
theorem cotaCaracteres_basesExplicitas (h : HipHadamard) (hS : SerieDigamma)
    (hG : GRHPrimitivo) : CotaCaracteres basesExplicitas := by
  intro n hn χ hχ
  have : NeZero n := ⟨by omega⟩
  unfold basesExplicitas
  split_ifs with hsmall
  · exact existe_base_trivial hχ
  · push Not at hsmall
    obtain ⟨a, ha, hcop, hχa⟩ := Explicito.cota_bach_explicita h hS hG n (log_ge_64 hsmall) χ hχ
    refine ⟨a, ?_, hcop, hχa⟩
    have := ha.trans (dos_log_sq_le (by omega))
    exact_mod_cast this

/-- **Test de Miller certificado.** Bajo GRH y las hipótesis analíticas de Alpöge,
`esPrimoMiller basesExplicitas` decide la primalidad; para `n ≥ 2^93` usa
`(⌊log₂ n⌋ + 1)²` bases. -/
theorem esPrimoMiller_explicito (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo)
    (n : ℕ) : esPrimoMiller basesExplicitas n = true ↔ n.Prime :=
  esPrimoMiller_correcto_de_caracteres (cotaCaracteres_basesExplicitas h hS hG) n

end AMate.Miller
