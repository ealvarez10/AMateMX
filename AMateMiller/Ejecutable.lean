import AMateMiller.Puente

/-!
# Test de Miller ejecutable

* `powMod`: exponenciación modular por cuadrados, con `powMod_eq : powMod a e n = a ^ e % n`.
* `partePar`: descomposición `m = 2^s d` con `d` impar por divisiones sucesivas; para `n ≥ 2`
  coincide con `(s2 n, dodd n)` (`s2_eq_partePar`, `dodd_eq_partePar`).
* `pasaMiller n a`: decide si `a` es mentiroso fuerte para `n` (`pasaMiller_iff`).
* `esPrimoMiller B n`: test completo con las bases `a ≤ B n` coprimas con `n`.
  `esPrimoMiller_correcto`: si `CotaSubgruposPropios B`, entonces `esPrimoMiller B n = true ↔
  n.Prime` para todo `n`. Con `B = id` vale sin hipótesis (`esPrimoMiller_id_correcto`), aunque
  con un número exponencial de bases; una cota `B n` polilogarítmica da un test polinomial.
-/

namespace AMate.Miller

/-! ### Exponenciación modular -/

/-- Exponenciación modular por cuadrados. -/
def powMod (a e n : ℕ) : ℕ :=
  if e = 0 then 1 % n
  else
    let r := powMod a (e / 2) n
    if e % 2 = 0 then r * r % n else r * r % n * (a % n) % n
termination_by e
decreasing_by omega

theorem powMod_eq (a e n : ℕ) : powMod a e n = a ^ e % n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powMod]
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

/-! ### Descomposición `m = 2^s d` -/

/-- `(s, d)` con `m = 2^s d` y `d` impar (para `m ≠ 0`). -/
def partePar (m : ℕ) : ℕ × ℕ :=
  if m ≠ 0 ∧ m % 2 = 0 then ((partePar (m / 2)).1 + 1, (partePar (m / 2)).2) else (0, m)
termination_by m
decreasing_by omega

theorem partePar_spec (m : ℕ) (hm : m ≠ 0) :
    2 ^ (partePar m).1 * (partePar m).2 = m ∧ (partePar m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [partePar]
    split_ifs with h
    · obtain ⟨-, h2⟩ := h
      obtain ⟨e1, e2⟩ := ih (m / 2) (by omega) (by omega)
      refine ⟨?_, e2⟩
      rw [pow_succ, mul_comm (2 ^ _) 2, mul_assoc, e1]
      omega
    · refine ⟨by simp, ?_⟩
      simp only
      omega

theorem s2_eq_partePar {n : ℕ} (hn : 2 ≤ n) : s2 n = (partePar (n - 1)).1 := by
  obtain ⟨e1, e2⟩ := partePar_spec (n - 1) (by omega)
  set s := (partePar (n - 1)).1
  set d := (partePar (n - 1)).2
  have hd0 : d ≠ 0 := by omega
  have hnd : ¬ 2 ∣ d := by omega
  unfold s2
  rw [← e1, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hd0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hnd]
  simp

theorem dodd_eq_partePar {n : ℕ} (hn : 2 ≤ n) : dodd n = (partePar (n - 1)).2 := by
  obtain ⟨e1, -⟩ := partePar_spec (n - 1) (by omega)
  unfold dodd
  rw [s2_eq_partePar hn]
  set s := (partePar (n - 1)).1
  set d := (partePar (n - 1)).2
  rw [← e1]
  exact Nat.mul_div_cancel_left _ (pow_pos two_pos _)

/-! ### Mentirosos fuertes -/

/-- Decide si `a` es mentiroso fuerte para `n`. -/
def pasaMiller (n a : ℕ) : Bool :=
  powMod a (partePar (n - 1)).2 n == 1 % n
    || (List.range (partePar (n - 1)).1).any
      (fun r => powMod a (2 ^ r * (partePar (n - 1)).2) n == n - 1)

theorem natCast_pow_eq_one_iff {n : ℕ} (a k : ℕ) :
    (a : ZMod n) ^ k = 1 ↔ powMod a k n = 1 % n := by
  rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff']

theorem natCast_pow_eq_neg_one_iff {n : ℕ} (hn : 1 ≤ n) (a k : ℕ) :
    (a : ZMod n) ^ k = -1 ↔ powMod a k n = n - 1 := by
  have hneg : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hn, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [powMod_eq, hneg, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (show n - 1 < n by omega)]

theorem pasaMiller_iff {n : ℕ} (hn : 2 ≤ n) (a : ℕ) :
    pasaMiller n a = true ↔ MentirosoFuerte n (a : ZMod n) := by
  unfold pasaMiller MentirosoFuerte
  rw [s2_eq_partePar hn, dodd_eq_partePar hn]
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
    natCast_pow_eq_one_iff, natCast_pow_eq_neg_one_iff (show 1 ≤ n by omega)]

/-! ### El test completo -/

/-- Test de Miller con las bases `a ≤ B n` coprimas con `n`, para impares `n ≥ 3`. -/
def testMiller (B : ℕ → ℕ) (n : ℕ) : Bool :=
  (List.range (B n + 1)).all (fun a => Nat.gcd a n != 1 || pasaMiller n a)

theorem testMiller_iff {B : ℕ → ℕ} {n : ℕ} (hn : 3 ≤ n) :
    testMiller B n = true
      ↔ ∀ a : ℕ, a ≤ B n → Nat.Coprime a n → MentirosoFuerte n (a : ZMod n) := by
  unfold testMiller
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    pasaMiller_iff (show 2 ≤ n by omega)]
  constructor
  · intro h a ha hcop
    rcases h a (by omega) with h1 | h1
    · exact absurd hcop h1
    · exact h1
  · intro h a ha
    by_cases hcop : Nat.gcd a n = 1
    · exact Or.inr (h a (by omega) hcop)
    · exact Or.inl hcop

/-- Test de primalidad completo: `n` es `2`, o es impar `≥ 3` y pasa el test de Miller. -/
def esPrimoMiller (B : ℕ → ℕ) (n : ℕ) : Bool :=
  if n < 2 then false else if n = 2 then true else if n % 2 = 0 then false else testMiller B n

/-- **Corrección**: con una cota de tipo Bach, `esPrimoMiller B` decide la primalidad. -/
theorem esPrimoMiller_correcto {B : ℕ → ℕ} (hB : CotaSubgruposPropios B) (n : ℕ) :
    esPrimoMiller B n = true ↔ n.Prime := by
  unfold esPrimoMiller
  split_ifs with h1 h2 h3
  · simp only [false_iff]
    intro hp
    have := hp.two_le
    omega
  · subst h2
    simp [Nat.prime_two]
  · simp only [false_iff]
    intro hp
    rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h3) with h | h <;> omega
  · rw [testMiller_iff (by omega), ← test_miller_correcto hB (by omega)]
    exact Nat.odd_iff.mpr (by omega)

/-- Sin hipótesis, con todas las bases `a ≤ n`: `esPrimoMiller id` decide la primalidad. -/
theorem esPrimoMiller_id_correcto (n : ℕ) : esPrimoMiller id n = true ↔ n.Prime :=
  esPrimoMiller_correcto cotaSubgruposPropios_id n

/-- Con una cota para caracteres (la forma que da el análisis), el test es correcto. -/
theorem esPrimoMiller_correcto_de_caracteres {B : ℕ → ℕ} (hB : CotaCaracteres B) (n : ℕ) :
    esPrimoMiller B n = true ↔ n.Prime :=
  esPrimoMiller_correcto (cotaSubgruposPropios_of_cotaCaracteres hB) n

end AMate.Miller
