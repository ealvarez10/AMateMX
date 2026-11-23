import Mathlib

/-!
# Test de Miller: parte algebraica

Para `n` impar, `n − 1 = 2^s d` con `d` impar. Una unidad `a` es *mentirosa fuerte* si
`a^d = 1` o `a^{2^r d} = −1` para algún `r < s`.

* `primo_todos_mentirosos`: si `n` es primo, toda unidad es mentirosa fuerte.
* `mentirosos_en_subgrupo_propio`: si `n ≥ 3` es impar y compuesto, los mentirosos fuertes
  están contenidos en un subgrupo propio de `(ℤ/nℤ)ˣ`.
* `test_miller_correcto`: dada una cota `B` tal que todo subgrupo propio de `(ℤ/nℤ)ˣ` omite
  alguna unidad representada por un entero `a ≤ B n` (Bach, bajo GRH, da `B n = 2 (log n)²`),
  `n` es primo si y solo si todos los `a ≤ B n` coprimos con `n` son mentirosos fuertes.
-/

namespace AMate.Miller

/-- `s = v₂(n − 1)`. -/
def s2 (n : ℕ) : ℕ := (n - 1).factorization 2

/-- `d = (n − 1)/2^s`, la parte impar de `n − 1`. -/
def dodd (n : ℕ) : ℕ := (n - 1) / 2 ^ s2 n

/-- `a` es mentirosa fuerte para `n`. -/
def MentirosoFuerte (n : ℕ) (a : ZMod n) : Prop :=
  a ^ dodd n = 1 ∨ ∃ r < s2 n, a ^ (2 ^ r * dodd n) = -1

theorem pow_s2_mul_dodd (n : ℕ) : 2 ^ s2 n * dodd n = n - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2

theorem dodd_odd {n : ℕ} (hn : 2 ≤ n) : Odd (dodd n) := by
  have h0 : n - 1 ≠ 0 := by omega
  have hcop := Nat.coprime_ordCompl Nat.prime_two h0
  rw [Nat.coprime_two_left] at hcop
  exact hcop

/-! ## Si `n` es primo, toda unidad es mentirosa fuerte -/

theorem primo_todos_mentirosos {p : ℕ} [hp : Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    MentirosoFuerte p a := by
  have hfermat : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  rw [← pow_s2_mul_dodd p] at hfermat
  -- `x r = a^{2^r d}`; `x s = 1`. Tomamos el menor `r` con `x r = 1`.
  have hex : ∃ r, a ^ (2 ^ r * dodd p) = 1 := ⟨s2 p, hfermat⟩
  classical
  set r₀ := Nat.find hex with hr₀
  have hr₀spec : a ^ (2 ^ r₀ * dodd p) = 1 := Nat.find_spec hex
  have hr₀le : r₀ ≤ s2 p := Nat.find_min' hex hfermat
  rcases Nat.eq_zero_or_pos r₀ with h0 | hpos
  · left
    rw [h0] at hr₀spec
    simpa using hr₀spec
  · right
    refine ⟨r₀ - 1, by omega, ?_⟩
    have hne : a ^ (2 ^ (r₀ - 1) * dodd p) ≠ 1 := Nat.find_min hex (by omega)
    have hexp : 2 ^ (r₀ - 1) * dodd p * 2 = 2 ^ r₀ * dodd p := by
      obtain ⟨k, hk⟩ : ∃ k, r₀ = k + 1 := ⟨r₀ - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      ring
    have hsq : (a ^ (2 ^ (r₀ - 1) * dodd p)) ^ 2 = 1 := by
      rw [← pow_mul, hexp]
      exact hr₀spec
    rw [sq] at hsq
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h hne
    · exact h

/-! ## Si `n` es compuesto, los mentirosos fuertes caben en un subgrupo propio -/

/-- `{a : a^k = ±1}` como subgrupo de `(ℤ/nℤ)ˣ`. -/
def subgrupoSigno (n k : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {a | a ^ k = 1 ∨ a ^ k = -1}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;> simp [mul_pow, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    rintro a (ha | ha) <;> simp [inv_pow, ha]

theorem val_pow_eq_one {n k : ℕ} {u : (ZMod n)ˣ} : (u : ZMod n) ^ k = 1 ↔ u ^ k = 1 := by
  rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]

theorem val_pow_eq_neg_one {n k : ℕ} {u : (ZMod n)ˣ} : (u : ZMod n) ^ k = -1 ↔ u ^ k = -1 := by
  rw [← Units.val_pow_eq_pow_val, Units.ext_iff, Units.val_neg, Units.val_one]

theorem s2_pos {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) : 0 < s2 n := by
  unfold s2
  refine Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) ?_
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

theorem mentirosos_en_subgrupo_propio {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hnp : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod n)ˣ, MentirosoFuerte n (u : ZMod n) → u ∈ H := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hs : 2 ^ s2 n * dodd n = n - 1 := pow_s2_mul_dodd n
  have hd : Odd (dodd n) := dodd_odd (by omega)
  by_cases hsq : p * p ∣ n
  · -- Caso `p² ∣ n`: el subgrupo de los mentirosos de Fermat.
    refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
    · intro htop
      obtain ⟨m, hm⟩ := hsq
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm; omega
        · exact h
      set c : ZMod n := ((p * m : ℕ) : ZMod n) with hc
      have hc2 : c * c = 0 := by
        rw [hc, ← Nat.cast_mul, show p * m * (p * m) = n * m by rw [hm]; ring, Nat.cast_mul,
          ZMod.natCast_self, zero_mul]
      have hc0 : c ≠ 0 := by
        rw [hc, Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have hle : n ≤ p * m := Nat.le_of_dvd (by positivity) hdvd
        have : p * m < n := by rw [hm]; nlinarith
        omega
      have hpow : ∀ k : ℕ, (1 + c) ^ k = 1 + (k : ZMod n) * c := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, ih]
          push_cast
          linear_combination (k : ZMod n) * hc2
      let u : (ZMod n)ˣ := ⟨1 + c, 1 - c, by linear_combination -hc2, by linear_combination -hc2⟩
      have hmem : u ∈ (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := htop ▸ Subgroup.mem_top u
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hmem
      have hval := congrArg Units.val hmem
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hval
      change (1 + c) ^ (n - 1) = 1 at hval
      rw [hpow, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one] at hval
      apply hc0
      linear_combination -hval
    · intro u hu
      rw [MonoidHom.mem_ker, powMonoidHom_apply, ← val_pow_eq_one]
      rcases hu with h | ⟨r, hr, h⟩
      · rw [← hs, mul_comm (2 ^ s2 n) (dodd n), pow_mul, h, one_pow]
      · have hexp : n - 1 = 2 ^ r * dodd n * 2 ^ (s2 n - r) := by
          rw [← hs, mul_comm (2 ^ r), mul_assoc, ← pow_add, Nat.add_sub_cancel' hr.le, mul_comm]
        rw [hexp, pow_mul, h]
        exact Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  · -- Caso libre de cuadrados en `p`: `n = p m` con `p, m` coprimos.
    classical
    obtain ⟨m, rfl⟩ := hpn
    have hcop : Nat.Coprime p m := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      rintro ⟨k, rfl⟩
      exact hsq ⟨k, by ring⟩
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hnp
      exact hnp hp
    have hmodd : Odd m := (Nat.odd_mul.mp hodd).2
    have hm3 : 3 ≤ m := by
      obtain ⟨k, hk⟩ := hmodd
      omega
    set k₀ := dodd (p * m)
    set R : Finset ℕ := (Finset.range (s2 (p * m))).filter
      (fun r => ∃ a : (ZMod (p * m))ˣ, a ^ (2 ^ r * k₀) = -1) with hR
    have h0R : 0 ∈ R := by
      rw [hR, Finset.mem_filter, Finset.mem_range]
      refine ⟨s2_pos hn hodd, -1, ?_⟩
      rw [pow_zero, one_mul]
      exact hd.neg_one_pow
    set r₀ := R.max' ⟨0, h0R⟩ with hr₀
    have hr₀R : r₀ ∈ R := R.max'_mem _
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hr₀R).2
    set k := 2 ^ r₀ * k₀ with hk
    refine ⟨subgrupoSigno (p * m) k, ?_, ?_⟩
    · intro htop
      set e := ZMod.chineseRemainder hcop
      have hbval : (b : ZMod (p * m)) ^ k = -1 := val_pow_eq_neg_one.mpr hb
      set bp : ZMod p := (e b).1
      set bpinv : ZMod p := (e ↑b⁻¹).1
      have hbp : bp * bpinv = 1 := by
        simp only [bp, bpinv]
        rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
      set x : ZMod (p * m) := e.symm (bp, 1)
      set y : ZMod (p * m) := e.symm (bpinv, 1)
      have hxy : x * y = 1 := by
        simp only [x, y]
        rw [← map_mul, Prod.mk_mul_mk, hbp, mul_one]
        exact map_one e.symm
      let ux : (ZMod (p * m))ˣ := ⟨x, y, hxy, by rw [mul_comm y x]; exact hxy⟩
      have hmem : ux ∈ subgrupoSigno (p * m) k := htop ▸ Subgroup.mem_top ux
      have hbpk : bp ^ k = -1 := by
        simp only [bp]
        rw [← Prod.pow_fst, ← map_pow, hbval, map_neg, map_one, Prod.fst_neg, Prod.fst_one]
      have hex : e (x ^ k) = (-1, 1) := by
        simp only [x]
        rw [map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk, one_pow, hbpk]
      have : Fact (2 < p) := ⟨by omega⟩
      have : Fact (2 < m) := ⟨by omega⟩
      rcases hmem with h | h
      · have hx : x ^ k = 1 := by
          have := val_pow_eq_one.mpr h
          exact this
        rw [hx, map_one] at hex
        exact ZMod.neg_one_ne_one (congrArg Prod.fst hex).symm
      · have hx : x ^ k = -1 := by
          have := val_pow_eq_neg_one.mpr h
          exact this
        rw [hx, map_neg, map_one] at hex
        exact ZMod.neg_one_ne_one (congrArg Prod.snd hex)
    · intro u hu
      rcases hu with h | ⟨r, hr, h⟩
      · left
        rw [← val_pow_eq_one, hk, mul_comm (2 ^ r₀) k₀, pow_mul, h, one_pow]
      · have hrR : r ∈ R := by
          rw [hR, Finset.mem_filter, Finset.mem_range]
          exact ⟨hr, u, val_pow_eq_neg_one.mp h⟩
        have hle : r ≤ r₀ := R.le_max' r hrR
        rcases hle.lt_or_eq with hlt | heq
        · left
          rw [← val_pow_eq_one]
          have hexp : k = 2 ^ r * k₀ * 2 ^ (r₀ - r) := by
            rw [hk, mul_comm (2 ^ r), mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, mul_comm]
          rw [hexp, pow_mul, h]
          exact Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        · right
          rw [← val_pow_eq_neg_one, hk, ← heq]
          exact h

/-! ## Corrección del test con una cota para subgrupos propios -/

/-- Cota de tipo Bach: todo subgrupo propio de `(ℤ/nℤ)ˣ` omite alguna unidad representada por un
entero `a ≤ B n`. Bach (1990), suponiendo GRH para los caracteres de Dirichlet, da `B n = 2 (log n)²`;
aquí queda como hipótesis explícita. -/
def CotaSubgruposPropios (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ a : ℕ, a ≤ B n ∧ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H

/-- Corrección del test de Miller: con una cota `B` de tipo Bach, un impar `n ≥ 3` es primo si y
solo si todo `a ≤ B n` coprimo con `n` es mentiroso fuerte. -/
theorem test_miller_correcto {B : ℕ → ℕ} (hB : CotaSubgruposPropios B) {n : ℕ} (hn : 3 ≤ n)
    (hodd : Odd n) :
    n.Prime ↔ ∀ a : ℕ, a ≤ B n → Nat.Coprime a n → MentirosoFuerte n (a : ZMod n) := by
  constructor
  · intro hp a _ hcop
    have := Fact.mk hp
    apply primo_todos_mentirosos
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.Coprime.eq_one_of_dvd hcop.symm h0
    omega
  · intro hall
    by_contra hnp
    obtain ⟨H, hH, hliar⟩ := mentirosos_en_subgrupo_propio hn hodd hnp
    obtain ⟨a, haB, u, hu, huH⟩ := hB n hn H hH
    have hcop : Nat.Coprime a n := by
      rw [← ZMod.isUnit_iff_coprime, ← hu]
      exact u.isUnit
    apply huH
    apply hliar u
    rw [hu]
    exact hall a haB hcop

end AMate.Miller
