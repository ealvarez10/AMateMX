import AMateMiller.PesoPrimos

/-!
# Comparación entre `χ*` y `ζ`

Si `χ(m) = 1` para todo `m ≤ x` coprimo con `n` y `χ*` (módulo `q`) es el carácter primitivo que
induce `χ`:

  `Re S(χ*) ≥ S(ζ) − E − E'`   (`re_S_ge`),

con `E = ∑_{m ≤ x, (m, n) > 1} Λ(m) w(m)` y `E'` la misma suma restringida a `(m, q) = 1`.
Además `E ≤ ∑_{p | n} (A₁ + B₁ log p)` y `E' ≤ ∑_{p | n, p ∤ q} (A₁ + B₁ log p)` (`cota_E`).
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Ponderada

/-- `A₁ + B₁ log p`, la cota por primo. -/
def cotaP (p : ℕ) : ℝ :=
  (1 / (Real.exp 1 * (2 / 5) ^ 2) + 1 / (2 / 5) ^ 2) + Real.log p * (1 / (Real.exp 1 * (2 / 5)))

/-- **Suma sobre potencias de primos de un conjunto `Q`.** -/
theorem cota_suma_potencias {x : ℝ} (hx : 1 ≤ x) (F : Finset ℕ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hF : ∀ m ∈ F, IsPrimePow m → m.minFac ∈ Q)
    (hFx : ∀ m ∈ F, (m : ℝ) ≤ x) :
    ∑ m ∈ F, ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m ≤ ∑ p ∈ Q, cotaP p := by
  classical
  have hx0 : 0 < x := by linarith
  set f : ℕ → ℕ → ℝ := fun m p =>
    if IsPrimePow m ∧ m.minFac = p then Real.log p * w x (2 / 5) (9 / 20) m else 0 with hfdef
  have hwn : ∀ m, 0 ≤ w x (2 / 5) (9 / 20) m := fun m => w_nonneg hx0 (by norm_num) (by norm_num) m
  have hf0 : ∀ m, ∀ p ∈ Q, 0 ≤ f m p := by
    intro m p hp
    simp only [hfdef]
    split_ifs
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (hQ p hp).one_lt.le)) (hwn m)
    · exact le_rfl
  have ha : ∀ m ∈ F, ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m ≤
      ∑ p ∈ Q, f m p := by
    intro m hm
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · have hmem := hF m hm hpp
      have hs := Finset.single_le_sum (fun p hp => hf0 m p hp) hmem
      have hfm : f m m.minFac = Real.log m.minFac * w x (2 / 5) (9 / 20) m := by
        simp only [hfdef, hpp, true_and, if_true]
      rw [hfm] at hs
      exact hs
    · rw [zero_mul]; exact Finset.sum_nonneg fun p hp => hf0 m p hp
  have hc : ∀ p ∈ Q, ∑ m ∈ F, f m p ≤ cotaP p := by
    intro p hp
    have hpp := hQ p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    set G := F.filter (fun m => IsPrimePow m ∧ m.minFac = p) with hGdef
    have hsum : ∑ m ∈ F, f m p = ∑ m ∈ G, Real.log p * w x (2 / 5) (9 / 20) m := by
      simp only [hfdef]
      rw [← Finset.sum_filter]
    set K := ⌊Real.log x / Real.log p⌋₊ with hK
    have hG : G ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
      intro m hm
      rw [hGdef, Finset.mem_filter] at hm
      obtain ⟨hmF, hpp', hmin⟩ := hm
      rw [Finset.mem_image]
      have hpk : p ^ (m.factorization m.minFac) = m := by
        rw [← hmin]
        exact hpp'.minFac_pow_factorization_eq
      refine ⟨m.factorization m.minFac, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hpk⟩
      · by_contra hk
        push Not at hk
        have h0 : m.factorization m.minFac = 0 := by omega
        rw [h0, pow_zero] at hpk
        exact hpp'.ne_one hpk.symm
      · apply Nat.le_floor
        rw [le_div_iff₀ hlogp]
        have hle : ((p : ℝ)) ^ (m.factorization m.minFac) ≤ x := by
          have := hFx m hmF
          rw [← hpk] at this
          exact_mod_cast this
        calc ((m.factorization m.minFac : ℕ) : ℝ) * Real.log p
            = Real.log (((p : ℝ)) ^ (m.factorization m.minFac)) := by rw [Real.log_pow]
          _ ≤ Real.log x := Real.log_le_log (by positivity) hle
    have hinj : Set.InjOn (fun k => p ^ k) (Finset.Icc 1 K : Set ℕ) := fun a _ b _ h =>
      Nat.pow_right_injective hpp.two_le h
    rw [hsum]
    calc ∑ m ∈ G, Real.log p * w x (2 / 5) (9 / 20) m
        ≤ ∑ m ∈ (Finset.Icc 1 K).image (fun k => p ^ k), Real.log p * w x (2 / 5) (9 / 20) m :=
          Finset.sum_le_sum_of_subset_of_nonneg hG fun m _ _ =>
            mul_nonneg hlogp.le (hwn m)
      _ = ∑ k ∈ Finset.Icc 1 K, Real.log p * w x (2 / 5) (9 / 20) (p ^ k) :=
          Finset.sum_image fun a ha b hb h => hinj ha hb h
      _ ≤ cotaP p := suma_potencias_le hx hpp
  calc ∑ m ∈ F, ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m
      ≤ ∑ m ∈ F, ∑ p ∈ Q, f m p := Finset.sum_le_sum ha
    _ = ∑ p ∈ Q, ∑ m ∈ F, f m p := Finset.sum_comm
    _ ≤ ∑ p ∈ Q, cotaP p := Finset.sum_le_sum hc

/-- `∑_{p ∈ Q} log p ≤ log n` si los primos de `Q` dividen a `n`. -/
theorem suma_log_primos_le {n : ℕ} (hn : 1 ≤ n) {Q : Finset ℕ} (hQ : Q ⊆ n.primeFactors) :
    ∑ p ∈ Q, Real.log p ≤ Real.log n := by
  have hdvd : ∏ p ∈ Q, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset Q n.primeFactors id hQ).trans (Nat.prod_primeFactors_dvd n)
  have hle : ∏ p ∈ Q, p ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hpos : ∀ p ∈ Q, (0 : ℝ) < p := fun p hp =>
    by exact_mod_cast (Nat.prime_of_mem_primeFactors (hQ hp)).pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Real.log_le_log (Finset.prod_pos hpos)
  have : ((∏ p ∈ Q, p : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
  rwa [Nat.cast_prod] at this

/-- `log q + ∑_{p | n, p ∤ q} log p ≤ log n` si `q ∣ n`. -/
theorem log_q_add_suma_le {n q : ℕ} (hn : 1 ≤ n) (hq : q ∣ n) (hq1 : 1 ≤ q) :
    Real.log q + ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), Real.log p ≤ Real.log n := by
  set Q := n.primeFactors.filter (fun p => ¬ p ∣ q) with hQ
  have hcop : Nat.Coprime q (∏ p ∈ Q, p) := by
    apply Nat.Coprime.prod_right
    intro p hp
    rw [hQ, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hp.2))
  have hdvdQ : ∏ p ∈ Q, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset Q n.primeFactors id (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have hdvd : q * ∏ p ∈ Q, p ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hq hdvdQ
  have hle : q * ∏ p ∈ Q, p ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hpos : ∀ p ∈ Q, (0 : ℝ) < p := fun p hp => by
    rw [hQ, Finset.mem_filter] at hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne'), ← Real.log_mul (by positivity)
    (Finset.prod_pos hpos).ne']
  apply Real.log_le_log (mul_pos (by exact_mod_cast hq1) (Finset.prod_pos hpos))
  have : ((q * ∏ p ∈ Q, p : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
  rwa [Nat.cast_mul, Nat.cast_prod] at this

/-- `A₁ ≤ 8.55` y `B₁ ≤ 0.92`. -/
theorem cotas_A1_B1 :
    1 / (Real.exp 1 * (2 / 5) ^ 2) + 1 / (2 / 5) ^ 2 ≤ 855 / 100 ∧
      1 / (Real.exp 1 * (2 / 5)) ≤ 92 / 100 := by
  have he := Real.exp_one_gt_d9
  constructor
  · rw [show (1 : ℝ) / (Real.exp 1 * (2 / 5) ^ 2) = (25 / 4) / Real.exp 1 by field_simp; norm_num]
    have : (25 / 4 : ℝ) / Real.exp 1 ≤ 23 / 10 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    norm_num; linarith
  · rw [show (1 : ℝ) / (Real.exp 1 * (2 / 5)) = (5 / 2) / Real.exp 1 by field_simp,
      div_le_iff₀ (by positivity)]
    nlinarith

theorem cotaP_le (p : ℕ) : cotaP p ≤ 855 / 100 + 92 / 100 * Real.log p := by
  obtain ⟨h1, h2⟩ := cotas_A1_B1
  unfold cotaP
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have := mul_le_mul_of_nonneg_left h2 hl
  linarith

/-- `log 2 ≥ 0.693` y `log 16 ≥ 2.772`. -/
theorem log_dos_ge : 693 / 1000 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- **Cota de `E`**: `∑_{p | n} (A₁ + B₁ log p) ≤ 51.3 + 4.01 log n`. -/
theorem suma_cotaP_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ n.primeFactors, cotaP p ≤ 513 / 10 + 401 / 100 * Real.log n := by
  classical
  have hpos : ∀ p ∈ n.primeFactors, (1 : ℝ) < p := fun p hp =>
    by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hl16 : 2772 / 1000 ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith [log_dos_ge]
  have hlog := suma_log_primos_le hn (Finset.Subset.refl n.primeFactors)
  -- cada primo: `A₁ + B₁ log p ≤ 8.55 [p < 16] + (8.55/2.772 + 0.92) log p`
  have hterm : ∀ p ∈ n.primeFactors, cotaP p ≤
      (if p < 16 then 855 / 100 else 0) + (855 / 100 / (2772 / 1000) + 92 / 100) * Real.log p := by
    intro p hp
    have hp1 := hpos p hp
    have hl0 : 0 < Real.log p := Real.log_pos hp1
    refine (cotaP_le p).trans ?_
    split_ifs with h
    · have : 0 ≤ 855 / 100 / (2772 / 1000) * Real.log p := by positivity
      linarith
    · push Not at h
      have h16 : Real.log 16 ≤ Real.log p :=
        Real.log_le_log (by norm_num) (by exact_mod_cast h)
      have : 855 / 100 ≤ 855 / 100 / (2772 / 1000) * Real.log p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
        nlinarith
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : ((n.primeFactors.filter (fun p => p < 16)).card : ℝ) ≤ 6 := by
    have hsub : n.primeFactors.filter (fun p => p < 16) ⊆ {2, 3, 5, 7, 11, 13} := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have h16 := hp.2
      interval_cases p <;> first | (norm_num at hpp; done) | simp
    have := Finset.card_le_card hsub
    have h6 : ({2, 3, 5, 7, 11, 13} : Finset ℕ).card = 6 := by decide
    rw [h6] at this
    exact_mod_cast this
  have hc : (855 / 100 / (2772 / 1000) + 92 / 100 : ℝ) ≤ 401 / 100 := by norm_num
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hsum0 : 0 ≤ ∑ p ∈ n.primeFactors, Real.log p :=
    Finset.sum_nonneg fun p hp => (Real.log_pos (hpos p hp)).le
  nlinarith

/-- **Cota de `E'`**: `∑_{p | n, p ∤ q} (A₁ + B₁ log p) ≤ 13.27 (log n − log q)`. -/
theorem suma_cotaP_le' {n q : ℕ} (hn : 1 ≤ n) (hq : q ∣ n) (hq1 : 1 ≤ q) :
    ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), cotaP p ≤
      1327 / 100 * (Real.log n - Real.log q) := by
  have hl := log_q_add_suma_le hn hq hq1
  have hterm : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), cotaP p ≤
      1327 / 100 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    have hl2 : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
    have h2 := log_dos_ge
    refine (cotaP_le p).trans ?_
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith

/-- `S(ζ) = ∑ Λ(m) w(m)`. -/
theorem S_uno (x α β : ℝ) :
    S (1 : DirichletCharacter ℂ 1) x α β =
      ((∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m * w x α β m : ℝ) : ℂ) := by
  unfold S
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]

/-- **Comparación.** -/
theorem re_S_ge {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} {x : ℝ} (hx : 0 < x)
    (h : ∀ m : ℕ, (m : ℝ) ≤ x → Nat.Coprime m n → χ m = 1) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m) -
        (∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => ¬ Nat.Coprime m n),
          ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m) -
        (∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => ¬ Nat.Coprime m n ∧ Nat.Coprime m χ.conductor),
          ArithmeticFunction.vonMangoldt m * w x (2 / 5) (9 / 20) m) ≤
      (S χ.primitiveCharacter x (2 / 5) (9 / 20)).re := by
  classical
  set Λ := ArithmeticFunction.vonMangoldt
  set W : ℕ → ℝ := fun m => w x (2 / 5) (9 / 20) m with hW
  have hW0 : ∀ m, 0 ≤ W m := fun m => w_nonneg hx (by norm_num) (by norm_num) m
  have hval : ∀ m : ℕ, Nat.Coprime m n →
      χ.primitiveCharacter (m : ZMod χ.conductor) = χ (m : ZMod n) := by
    intro m hm
    have e := χ.primitiveCharacter.changeLevel_eq_cast_of_dvd' χ.conductor_dvd_level
      (a := (m : ℤ)) (Nat.isCoprime_iff_coprime.mpr hm)
    rw [χ.changeLevel_primitiveCharacter] at e
    simpa using e.symm
  unfold S
  rw [Complex.re_sum]
  set c : ℕ → ℝ := fun m => if Nat.Coprime m n then 1 else if Nat.Coprime m χ.conductor then -1 else 0
  have key : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊, Λ m * W m * c m ≤
      ((Λ m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) * (W m : ℂ)).re := by
    intro m hm
    have hmx : (m : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Icc.mp hm).2
    have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
    have hre : ((Λ m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) * (W m : ℂ)).re =
        Λ m * W m * (χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
      rw [show (Λ m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) * (W m : ℂ) =
        ((Λ m * W m : ℝ) : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hΛ (hW0 m))
    simp only [c]
    split_ifs with h1 h2
    · rw [hval m h1, h m hmx h1, Complex.one_re]
    · have h3 := Complex.abs_re_le_norm (χ.primitiveCharacter (m : ZMod χ.conductor))
      have h4 := DirichletCharacter.norm_le_one χ.primitiveCharacter (m : ZMod χ.conductor)
      have := neg_abs_le (χ.primitiveCharacter (m : ZMod χ.conductor)).re
      linarith
    · have hnu : ¬ IsUnit ((m : ℕ) : ZMod χ.conductor) := by
        rw [ZMod.isUnit_iff_coprime]; exact h2
      rw [MulChar.map_nonunit _ hnu, Complex.zero_re]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
  simp only [c, mul_ite, mul_one, mul_neg, mul_zero]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib,
    Finset.filter_filter]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) (fun m => Nat.Coprime m n)]
  ring

end AMate.Miller.Explicito
