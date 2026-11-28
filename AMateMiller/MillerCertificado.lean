import AMateMiller.DeterministaExplicito
import AMateMiller.BachGeneral

/-!
# Test de Miller certificado para todo `n`, y el menor no-residuo cuadrático

Con las tres cotas de Bach explícitas (constante `16` si `n ≥ 2^12`, `4` si `n ≥ 2^34` y `2` si
`n ≥ 2^93`), el número de bases

* `n` si `n < 2^12`;
* `8 (⌊log₂ n⌋ + 1)²` si `2^12 ≤ n < 2^34`;
* `2 (⌊log₂ n⌋ + 1)²` si `2^34 ≤ n < 2^93`;
* `(⌊log₂ n⌋ + 1)²` si `n ≥ 2^93`

cumple `CotaCaracteres` bajo GRH y las hipótesis analíticas de Alpöge, así que
`esPrimoMiller basesCertificadas` decide la primalidad (`esPrimoMiller_certificado`). A diferencia
de `basesExplicitas`, solo usa todas las bases por debajo de `4096`.

Como aplicación clásica de la cota de Bach: todo primo impar `p` con `log p ≥ 8.3` tiene un
no-residuo cuadrático `a ≤ 16 (log p)²`, y `a ≤ 2 (log p)²` si `log p ≥ 64`
(`noResiduo_16`, `noResiduo_explicito`).
-/

namespace AMate.Miller

open AMate.Miller.Hadamard AMate.Miller.PI.Digamma

/-- Número de bases certificado por tramos. -/
def basesCertificadas (n : ℕ) : ℕ :=
  if n < 2 ^ 12 then n
  else if n < 2 ^ 34 then 8 * (Nat.log 2 n + 1) ^ 2
  else if n < 2 ^ 93 then 2 * (Nat.log 2 n + 1) ^ 2
  else (Nat.log 2 n + 1) ^ 2

/-- `c ≤ log n` si `n ≥ 2^k` y `c ≤ k · 0.6931471803`. -/
theorem log_ge_de_pot {n k : ℕ} {c : ℝ} (hn : 2 ^ k ≤ n)
    (hc : c ≤ k * (6931471803 / 10000000000)) : c ≤ Real.log n := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn)
  rw [Real.log_pow] at h1
  have h2 := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (k : ℝ) * (6931471803 / 10000000000) ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by norm_num at h2 ⊢; linarith) hk
  linarith

/-- `c (log n)² ≤ m (⌊log₂ n⌋ + 1)²` si `c · 0.6932² ≤ m`. -/
theorem c_log_sq_le {n : ℕ} (hn : 1 ≤ n) {c m : ℝ} (hc : 0 ≤ c)
    (hcm : c * (6932 / 10000) ^ 2 ≤ m) :
    c * Real.log n ^ 2 ≤ m * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 2 := by
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
  have h4 : c * Real.log n ^ 2 ≤ c * (((Nat.log 2 n : ℝ) + 1) * (6932 / 10000)) ^ 2 :=
    mul_le_mul_of_nonneg_left h3 hc
  have h5 : c * (6932 / 10000) ^ 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤
      m * ((Nat.log 2 n : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_right hcm (by positivity)
  nlinarith

/-- **Cota para caracteres por tramos.** -/
theorem cotaCaracteres_basesCertificadas (h : HipHadamard) (hS : SerieDigamma)
    (hG : GRHPrimitivo) : CotaCaracteres basesCertificadas := by
  intro n hn χ hχ
  have : NeZero n := ⟨by omega⟩
  unfold basesCertificadas
  split_ifs with h12 h34 h93
  · exact existe_base_trivial hχ
  · push Not at h12
    obtain ⟨a, ha, hcop, hχa⟩ := Explicito.cota_bach_16 h hS hG n
      (log_ge_de_pot h12 (by norm_num)) χ hχ
    refine ⟨a, ?_, hcop, hχa⟩
    have := ha.trans (c_log_sq_le (c := 16) (m := 8) (by omega) (by norm_num) (by norm_num))
    exact_mod_cast this
  · push Not at h34
    obtain ⟨a, ha, hcop, hχa⟩ := Explicito.cota_bach_4 h hS hG n
      (log_ge_de_pot h34 (by norm_num)) χ hχ
    refine ⟨a, ?_, hcop, hχa⟩
    have := ha.trans (c_log_sq_le (c := 4) (m := 2) (by omega) (by norm_num) (by norm_num))
    exact_mod_cast this
  · push Not at h93
    obtain ⟨a, ha, hcop, hχa⟩ := Explicito.cota_bach_explicita h hS hG n (log_ge_64 h93) χ hχ
    refine ⟨a, ?_, hcop, hχa⟩
    have := ha.trans (dos_log_sq_le (by omega))
    exact_mod_cast this

/-- **Test de Miller certificado para todo `n`.** Bajo GRH y las hipótesis analíticas de
Alpöge, `esPrimoMiller basesCertificadas` decide la primalidad. -/
theorem esPrimoMiller_certificado (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo)
    (n : ℕ) : esPrimoMiller basesCertificadas n = true ↔ n.Prime :=
  esPrimoMiller_correcto_de_caracteres (cotaCaracteres_basesCertificadas h hS hG) n

/-! ### El menor no-residuo cuadrático -/

/-- De una cota de tipo Bach para caracteres sale un no-residuo cuadrático pequeño módulo `p`. -/
theorem noResiduo_de_cota {C L₀ : ℝ}
    (hB : ∀ n : ℕ, L₀ ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ C * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : L₀ ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ C * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) := by
  haveI := Fact.mk hp
  let χ : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)]
    exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨a, ha, hcop, hχa⟩ := hB p hL χ hχ
  refine ⟨a, ha, ?_⟩
  rw [← quadraticChar_neg_one_iff_not_isSquare]
  have h0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h1 := Nat.dvd_gcd hd (dvd_refl p)
    rw [Nat.Coprime.gcd_eq_one hcop] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  rcases quadraticChar_dichotomy h0 with h1 | h1
  · exfalso
    apply hχa
    simp [χ, MulChar.ringHomComp_apply, h1]
  · exact h1

/-- Todo primo impar `p` con `log p ≥ 8.3` (por ejemplo `p ≥ 2^12`) tiene un no-residuo
cuadrático `a ≤ 16 (log p)²`. -/
theorem noResiduo_16 (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : 83 / 10 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 16 * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) :=
  noResiduo_de_cota (Explicito.cota_bach_16 h hS hG) hp hp2 hL

/-- Todo primo `p` con `log p ≥ 64` tiene un no-residuo cuadrático `a ≤ 2 (log p)²`. -/
theorem noResiduo_explicito (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {p : ℕ}
    (hp : p.Prime) (hL : 64 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    norm_num at hL; linarith
  exact noResiduo_de_cota (Explicito.cota_bach_explicita h hS hG) hp hp2 hL

end AMate.Miller
