import AMateMiller.Corolarios

/-!
# Test de Solovay–Strassen (Euler) determinista

`a` es **mentiroso de Euler** para `n` si `a^((n−1)/2) ≡ J(a|n) (mod n)`, con `J` el símbolo de
Jacobi. Para un primo impar todos los `a` lo son (criterio de Euler). Para `n` impar compuesto, las
unidades que lo son forman un subgrupo propio de `(ℤ/nℤ)ˣ` (`subgrupoEuler_ne_top`):

* si `p² ∣ n`, hay una unidad de orden `p`, que no puede cumplir `u^(n−1) = 1` porque `p ∤ n − 1`;
* si no, `n = p m` con `p ∤ m` y `m ≥ 3`; por el teorema chino, hay `a` que es no-residuo módulo
  `p` y `≡ 1 (mod m)`; entonces `J(a|n) = −1`, pero `a^((n−1)/2) ≡ 1 (mod m)`.

Con una cota de tipo Bach para subgrupos propios, el test de Euler con las bases `a ≤ B n` decide la
primalidad (`test_euler_correcto`), y en particular con `basesCertificadas`
(`test_euler_certificado`).
-/

namespace AMate.Miller

open NumberTheorySymbols AMate.Miller.Hadamard AMate.Miller.PI.Digamma

/-- `a` es mentiroso de Euler para `n`. -/
def MentirosoEuler (n a : ℕ) : Prop :=
  (a : ZMod n) ^ ((n - 1) / 2) = ((J(a | n) : ℤ) : ZMod n)

/-- El símbolo de Jacobi solo depende de la clase módulo `n`. -/
theorem jacobi_val {n : ℕ} [NeZero n] (a : ℕ) :
    J(((a : ZMod n).val : ℕ) | n) = J((a : ℤ) | n) := by
  rw [ZMod.val_natCast]
  push_cast
  exact (jacobiSym.mod_left _ _).symm

/-- `a` es mentiroso de Euler sii lo es su representante en `[0, n)`. -/
theorem mentiroso_val {n : ℕ} [NeZero n] (a : ℕ) :
    MentirosoEuler n (a : ZMod n).val ↔ MentirosoEuler n a := by
  unfold MentirosoEuler
  rw [ZMod.natCast_zmod_val, jacobi_val]

/-- El símbolo de Jacobi de un producto de unidades. -/
theorem jacobi_mul_units {n : ℕ} [NeZero n] (u v : (ZMod n)ˣ) :
    J((((u * v : (ZMod n)ˣ) : ZMod n).val : ℕ) | n) =
      J((((u : ZMod n).val : ℕ) : ℤ) | n) * J((((v : ZMod n).val : ℕ) : ℤ) | n) := by
  rw [← jacobiSym.mul_left, Units.val_mul, ZMod.val_mul]
  push_cast
  exact (jacobiSym.mod_left _ _).symm

/-- Las unidades que son mentirosas de Euler forman un subgrupo. -/
def subgrupoEuler (n : ℕ) (hn : 2 ≤ n) : Subgroup (ZMod n)ˣ where
  carrier := {u | MentirosoEuler n (u : ZMod n).val}
  one_mem' := by
    have : Fact (1 < n) := ⟨by omega⟩
    show MentirosoEuler n (1 : ZMod n).val
    rw [ZMod.val_one]
    simp [MentirosoEuler, jacobiSym.one_left]
  mul_mem' := by
    intro u v hu hv
    have : NeZero n := ⟨by omega⟩
    simp only [Set.mem_ofPred_eq, MentirosoEuler, ZMod.natCast_zmod_val] at hu hv ⊢
    rw [jacobi_mul_units, Units.val_mul, mul_pow, hu, hv, Int.cast_mul]
  inv_mem' := by
    intro u hu
    have : NeZero n := ⟨by omega⟩
    simp only [Set.mem_ofPred_eq, MentirosoEuler, ZMod.natCast_zmod_val] at hu ⊢
    have h2 : J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℕ) | n) *
        J((((u : ZMod n).val : ℕ) : ℤ) | n) = 1 := by
      rw [← jacobi_mul_units, inv_mul_cancel, Units.val_one]
      have : Fact (1 < n) := ⟨by omega⟩
      rw [ZMod.val_one]
      simp [jacobiSym.one_left]
    have h2' := congrArg (fun z : ℤ => (z : ZMod n)) h2
    simp only [Int.cast_mul, Int.cast_one] at h2'
    have h3 : (((u⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ ((n - 1) / 2) * ((u : ZMod n)) ^ ((n - 1) / 2) = 1 := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
    linear_combination (-(((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2))) * h2' +
      ((J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℕ) | n) : ℤ) : ZMod n) * h3 -
      ((J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℕ) | n) : ℤ) : ZMod n) *
        (((u⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ ((n - 1) / 2) * hu

theorem mem_subgrupoEuler {n : ℕ} (hn : 2 ≤ n) (u : (ZMod n)ˣ) :
    u ∈ subgrupoEuler n hn ↔ MentirosoEuler n (u : ZMod n).val := Iff.rfl

/-- **Criterio de Euler**: para un primo impar `p`, todo `a` es mentiroso de Euler. -/
theorem primo_mentiroso_euler {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    MentirosoEuler p a := by
  have := Fact.mk hp
  have hodd : (p - 1) / 2 = p / 2 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  unfold MentirosoEuler
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow, Int.cast_natCast, hodd]

/-- Si una unidad es mentirosa de Euler, `u^(n−1) = 1`. -/
theorem pow_sub_one_de_euler {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (u : (ZMod n)ˣ)
    (hu : u ∈ subgrupoEuler n (by omega)) : u ^ (n - 1) = 1 := by
  have : NeZero n := ⟨by omega⟩
  rw [mem_subgrupoEuler, MentirosoEuler, ZMod.natCast_zmod_val] at hu
  have hgcd : Int.gcd (((u : ZMod n).val : ℕ) : ℤ) (n : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ZMod.val_coe_unit_coprime u
  have h2 : (n - 1) = (n - 1) / 2 * 2 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, h2, pow_mul, hu]
  rcases jacobiSym.eq_one_or_neg_one hgcd with h | h <;> rw [h] <;> norm_num

/-- **Los mentirosos de Euler de un impar compuesto forman un subgrupo propio.** Dicho al revés:
si todas las unidades son mentirosas de Euler, `n` es primo. -/
theorem primo_de_euler {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hE : subgrupoEuler n (by omega) = ⊤) : n.Prime := by
  by_contra hnp
  have hall : ∀ u : (ZMod n)ˣ, u ∈ subgrupoEuler n (by omega) := fun u => hE ▸ Subgroup.mem_top u
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p * p ∣ n
  · -- `p² ∣ n`: una unidad de orden `p` contradice `u^(n−1) = 1`
    obtain ⟨p, hp, hpp⟩ := hsq
    have : NeZero n := ⟨by omega⟩
    have := Fact.mk hp
    have hdvd : p ∣ Fintype.card (ZMod n)ˣ := by
      rw [ZMod.card_units_eq_totient]
      have h1 : p ∣ Nat.totient (p ^ 2) := by
        rw [Nat.totient_prime_pow hp (by norm_num)]
        exact Dvd.dvd.mul_right (by simp) _
      exact h1.trans (Nat.totient_dvd_of_dvd (by rw [sq]; exact hpp))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
    have h1 : p ∣ n - 1 := hx ▸ orderOf_dvd_of_pow_eq_one (pow_sub_one_de_euler hn hodd x (hall x))
    have h2 : p ∣ n := (dvd_mul_right p p).trans hpp
    have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp (by rwa [show n - 1 + 1 = n by omega])
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  · -- `n = p m` libre de cuadrados: teorema chino
    push Not at hsq
    obtain ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p ∣ n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    obtain ⟨m, rfl⟩ := hpn
    have := Fact.mk hp
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hm1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hnp; exact hnp hp
    have hcop : Nat.Coprime p m :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hsq p hp (mul_dvd_mul_left p h)
    have hmodd : Odd m := Nat.Odd.of_mul_right hodd
    have hpodd : Odd p := Nat.Odd.of_mul_left hodd
    have hm3 : 3 ≤ m := by
      obtain ⟨j, hj⟩ := hmodd
      omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    have : NeZero m := ⟨hm0⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    have hg0 : g ≠ 0 := by rintro rfl; exact hg IsSquare.zero
    obtain ⟨k, hkp, hkm⟩ := Nat.chineseRemainder hcop g.val 1
    have hkpz : (k : ZMod p) = g := by
      rw [(ZMod.natCast_eq_natCast_iff k g.val p).mpr hkp, ZMod.natCast_zmod_val]
    have hkmz : (k : ZMod m) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff k 1 m).mpr hkm, Nat.cast_one]
    have hcopk : Nat.Coprime k (p * m) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => hg0 ?_)
        rw [← hkpz, ZMod.natCast_eq_zero_iff]
        exact hd
      · unfold Nat.Coprime
        rw [hkm.gcd_eq, Nat.gcd_one_left]
    have hmem := hall (ZMod.unitOfCoprime k hcopk)
    rw [mem_subgrupoEuler, ZMod.coe_unitOfCoprime, mentiroso_val] at hmem
    have hJp : J((k : ℤ) | p) = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      unfold legendreSym
      rw [Int.cast_natCast, hkpz]
      exact quadraticChar_neg_one_iff_not_isSquare.mpr hg
    have hJm : J((k : ℤ) | m) = 1 := by
      have hmod : (k : ℤ) % m = 1 % m := by
        have := congrArg (fun t : ℕ => (t : ℤ)) hkm
        push_cast at this
        exact this
      rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
    unfold MentirosoEuler at hmem
    rw [jacobiSym.mul_right, hJp, hJm] at hmem
    have hf := congrArg (ZMod.castHom (dvd_mul_left m p) (ZMod m)) hmem
    rw [map_pow, map_natCast, hkmz, one_pow] at hf
    simp only [mul_one, Int.reduceNeg, Int.cast_neg, Int.cast_one, map_neg, map_one] at hf
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination hf
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

/-- **Test de Euler determinista**: con una cota de tipo Bach para subgrupos propios, un impar
`n ≥ 3` es primo si y solo si todo `a ≤ B n` coprimo con `n` es mentiroso de Euler. -/
theorem test_euler_correcto {B : ℕ → ℕ} (hB : CotaSubgruposPropios B) {n : ℕ} (hn : 3 ≤ n)
    (hodd : Odd n) :
    n.Prime ↔ ∀ a : ℕ, a ≤ B n → Nat.Coprime a n → MentirosoEuler n a := by
  constructor
  · intro hp a _ _
    exact primo_mentiroso_euler hp (by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two) a
  · intro hall
    by_contra hnp
    have : NeZero n := ⟨by omega⟩
    have hE : subgrupoEuler n (by omega) ≠ ⊤ := fun h => hnp (primo_de_euler hn hodd h)
    obtain ⟨a, haB, u, hu, huE⟩ := hB n hn _ hE
    apply huE
    have hcop : Nat.Coprime a n := by
      rw [← ZMod.isUnit_iff_coprime, ← hu]
      exact u.isUnit
    rw [mem_subgrupoEuler, hu]
    exact (mentiroso_val a).mpr (hall a haB hcop)

/-- **Test de Solovay–Strassen determinista certificado**: bajo GRH y las hipótesis analíticas de
Alpöge, un impar `n ≥ 3` es primo si y solo si todo `a ≤ basesCertificadas n` coprimo con `n` es
mentiroso de Euler. -/
theorem test_euler_certificado (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    n.Prime ↔ ∀ a : ℕ, a ≤ basesCertificadas n → Nat.Coprime a n → MentirosoEuler n a :=
  test_euler_correcto (cotaSubgruposPropios_of_cotaCaracteres
    (cotaCaracteres_basesCertificadas h hS hG)) hn hodd

end AMate.Miller
