import AMateMiller.Comparacion

/-!
# La cota de Bach con constante explícita

**Teorema** (`cota_bach_explicita`). Bajo GRH y las hipótesis analíticas de Alpöge
(`HipHadamard`, `ReflexionLogDeriv`, `SerieDigamma`): si `log n ≥ 64`, todo carácter `χ ≠ 1`
módulo `n` cumple `χ(a) ≠ 1` para algún `a ≤ 2 (log n)²` coprimo con `n`.

Con `x = 2 (log n)²`, `α = 2/5`, `β = 9/20` y el peso `w`: si `χ(a) = 1` para todo `a ≤ x`
coprimo con `n`, la fórmula explícita (`cota_S`) para `χ*` y para `ζ`, junto con la cota de
Hadamard, los residuos, el lado izquierdo y las potencias de primos que dividen a `n`, da

  `x/((1 + α)(1 + β)) ≤ 0.765 L² + 11.45 L + 96`  (`L = log n`),

imposible para `L ≥ 64`.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Hadamard AMate.Miller.Ponderada AMate.Miller.DigammaExp

set_option linter.unusedSectionVars false

/-- Aritmética final. -/
theorem aritmetica_final {L ℓ r Zs Zz LE Rd E E' : ℝ} (hL : 64 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L)
    (hr0 : 0 ≤ r) (hr : r ≤ 70711 / 100000)
    (hZs : Zs ≤ r * L * ((ℓ + 43287 / 10000) * (5 / 9) + (ℓ + 37738 / 10000) * (10 / 19)))
    (hZz : Zz ≤ r * L * (52434 / 10000))
    (hLE : LE ≤ 1460 / 100) (hRd : Rd ≤ 625 / 1000 * ℓ + 30)
    (hE : E ≤ 513 / 10 + 401 / 100 * L) (hE' : E' ≤ 1327 / 100 * (L - ℓ))
    (hmain : 200 * L ^ 2 / 203 ≤ Zs + Zz + LE + Rd + E + E') : False := by
  have hL0 : 0 ≤ L := by linarith
  have h1 : r * L * ((ℓ + 43287 / 10000) * (5 / 9) + (ℓ + 37738 / 10000) * (10 / 19)) ≤
      70711 / 100000 * L * ((ℓ + 43287 / 10000) * (5 / 9) + (ℓ + 37738 / 10000) * (10 / 19)) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hL0) (by positivity)
  have h2 : r * L * (52434 / 10000) ≤ 70711 / 100000 * L * (52434 / 10000) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hL0) (by norm_num)
  have h3 : 0 ≤ (L - ℓ) * (70711 / 100000 * (5 / 9 + 10 / 19) * L + 625 / 1000 - 1327 / 100) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have h4 : 0 ≤ (L - 64) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ L - 64 := by linarith
  nlinarith

/-- `x^{2/5} ≥ 32` para `x ≥ 2^{13}`. -/
theorem rpow_dos_quintos_ge {x : ℝ} (hx : 8192 ≤ x) : 32 ≤ x ^ (2 / 5 : ℝ) := by
  have h : (32 : ℝ) = (2 ^ (25 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num)]; norm_num
  rw [h]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  have : (2 : ℝ) ^ (25 / 2 : ℝ) ≤ 2 ^ (13 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have e : (2 : ℝ) ^ (13 : ℝ) = 8192 := by norm_num
  linarith

/-- `D ≤ 0.625` y `24 X' ≤ 30` para `x ≥ 8192`. -/
theorem cotas_D_X {x : ℝ} (hx : 8192 ≤ x) :
    (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) ≤ 625 / 1000 ∧
      0 ≤ (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) ∧
      24 * ((x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5)) ≤ 30 := by
  have hx0 : 0 < x := by linarith
  have h32 := rpow_dos_quintos_ge hx
  have ha : x ^ (-(2 / 5 : ℝ)) ≤ 1 / 32 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h32
  have hb : x ^ (-(9 / 20 : ℝ)) ≤ x ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hb0 : 0 < x ^ (-(9 / 20 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)]; linarith
  · apply div_nonneg (by linarith) (by norm_num)
  · rw [mul_div_assoc', div_le_iff₀ (by norm_num)]; linarith

/-- `√(2 L²) = √2 · L`. -/
theorem sqrt_dos_L {L : ℝ} (hL : 0 ≤ L) : Real.sqrt (2 * L ^ 2) = Real.sqrt 2 * L := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hL]

theorem sqrt_dos_le : Real.sqrt 2 ≤ 141422 / 100000 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt_dos_ge : 141421 / 100000 ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

theorem log_pi_ge : 1 ≤ Real.log Real.pi := by
  rw [Real.le_log_iff_exp_le Real.pi_pos]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_three
  linarith

theorem log_pi_le : Real.log Real.pi ≤ 139 / 100 := by
  have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  linarith

variable {N : ℕ} [NeZero N]

/-- Cota de `H(σ) = log(N/π) + max(…) + 2 VM(σ)` en `σ = 7/5` y `σ = 29/20`. -/
theorem cotas_H (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) :
    max (Real.log ((1 + 2 / 5) / 2)) (Real.log ((1 + 2 / 5 + 1) / 2)) + 2 * VM (1 + 2 / 5) ≤
        43287 / 10000 + Real.log Real.pi ∧
      max (Real.log ((1 + 9 / 20) / 2)) (Real.log ((1 + 9 / 20 + 1) / 2)) + 2 * VM (1 + 9 / 20) ≤
        37738 / 10000 + Real.log Real.pi := by
  have hpi := log_pi_ge
  have v1 := VM_le h hS hG (σ := 1 + 2 / 5) (by norm_num) (by norm_num)
  have v2 := VM_le h hS hG (σ := 1 + 9 / 20) (by norm_num) (by norm_num)
  have l1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 2 / 5) / 2 by norm_num)
  have l2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 2 / 5 + 1) / 2 by norm_num)
  have l3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 9 / 20) / 2 by norm_num)
  have l4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 9 / 20 + 1) / 2 by norm_num)
  constructor
  · have hm : max (Real.log ((1 + 2 / 5) / 2)) (Real.log ((1 + 2 / 5 + 1) / 2)) ≤ 1 / 5 :=
      max_le (by linarith) (by linarith)
    linarith
  · have hm : max (Real.log ((1 + 9 / 20) / 2)) (Real.log ((1 + 9 / 20 + 1) / 2)) ≤ 9 / 40 :=
      max_le (by linarith) (by linarith)
    linarith

/-- Cota de las dos sumas de Hadamard de `ζ`. -/
theorem cotas_Hz :
    2 * (1 / (1 + 2 / 5) + 1 / (1 + 2 / 5 - 1) - Real.log Real.pi / 2 +
        Real.log ((1 + 2 / 5) / 2) / 2) / (1 + 2 * (2 / 5)) +
      2 * (1 / (1 + 9 / 20) + 1 / (1 + 9 / 20 - 1) - Real.log Real.pi / 2 +
        Real.log ((1 + 9 / 20) / 2) / 2) / (1 + 2 * (9 / 20)) ≤ 52434 / 10000 := by
  have hpi := log_pi_ge
  have l1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 2 / 5) / 2 by norm_num)
  have l3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 9 / 20) / 2 by norm_num)
  norm_num at l1 l3 ⊢
  linarith

theorem log_div_pi (M : ℕ) [NeZero M] :
    Real.log ((M : ℝ) / Real.pi) = Real.log M - Real.log Real.pi :=
  Real.log_div (by exact_mod_cast NeZero.ne M) Real.pi_ne_zero

theorem re_eps0_div_nonneg (χ : DirichletCharacter ℂ N) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (eps0 χ / ((a : ℂ) * (b : ℂ))).re := by
  rw [← Complex.ofReal_mul, Complex.div_ofReal_re]
  refine div_nonneg ?_ (by positivity)
  unfold eps0
  split_ifs <;> simp

theorem K_uno (x α β : ℝ) : K x α β 1 = ((x / ((1 + α) * (1 + β)) : ℝ) : ℂ) := by
  unfold K
  rw [Complex.cpow_one]
  norm_cast

/-- Si `m` es potencia de primo, `m` es coprimo con `n` sii su primo no divide a `n`. -/
theorem coprime_iff_minFac {m n : ℕ} (hm : IsPrimePow m) :
    Nat.Coprime m n ↔ ¬ m.minFac ∣ n := by
  have hp : m.minFac.Prime := Nat.minFac_prime hm.ne_one
  have hpk := hm.minFac_pow_factorization_eq
  have hk : 0 < m.factorization m.minFac := by
    by_contra hk
    push Not at hk
    have h0 : m.factorization m.minFac = 0 := by omega
    rw [h0, pow_zero] at hpk
    exact hm.ne_one hpk.symm
  have hiff := Nat.coprime_pow_left_iff hk m.minFac n
  rw [hpk] at hiff
  rw [hiff, Nat.Prime.coprime_iff_not_dvd hp]

/-- Aritmética del lado izquierdo. -/
theorem cota_LE_num {t L A B V P : ℝ} (hL : 64 ≤ L) (ht0 : 0 ≤ t)
    (htL : t * L * (141421 / 100000) ≤ 1) (hA : A ≤ L + 139 / 100) (hB : B ≤ 139 / 100)
    (hV : V ≤ 3) (hP : P ≤ 255 / 100) :
    t * ((A + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) + P) +
      t * ((B + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) + P) ≤ 1460 / 100 := by
  have e : ∀ u : ℝ, (u + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) = 10 * (u + 29 + V) :=
    fun u => by ring
  rw [e, e]
  have h1 : t * (10 * (A + 29 + V) + P) ≤ t * (10 * (L + 139 / 100 + 32) + 255 / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0
  have h2 : t * (10 * (B + 29 + V) + P) ≤ t * (10 * (139 / 100 + 32) + 255 / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0
  have h3 : t * 64 ≤ t * L := mul_le_mul_of_nonneg_left hL ht0
  linarith

/-- **Cota de Bach con constante explícita.** Bajo GRH y las hipótesis analíticas de Alpöge, si
`log n ≥ 64`, todo carácter `χ ≠ 1` módulo `n` toma un valor `≠ 1` en algún `a ≤ 2 (log n)²`
coprimo con `n`. -/
theorem cota_bach_explicita (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) :
    ∀ n : ℕ, 64 ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.cast_zero, Real.log_zero] at hn; linarith
  have : NeZero n := ⟨by omega⟩
  have hL0 : 0 ≤ Real.log n := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 2 * Real.log n ^ 2 := ⟨_, rfl⟩
  rw [← hxdef] at hcon
  have hx8192 : 8192 ≤ x := by rw [hxdef]; nlinarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hsx : Real.sqrt x / 2 = Real.sqrt 2 / 2 * Real.log n := by
    rw [hxdef, sqrt_dos_L hL0]; ring
  -- carácter primitivo asociado y carácter trivial módulo 1
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
  have hp1 : (1 : DirichletCharacter ℂ 1).IsPrimitive :=
    DirichletCharacter.isPrimitive_one_level_one
  have hqn : χ.conductor ∣ n := χ.conductor_dvd_level
  have hq1 : 1 ≤ χ.conductor := NeZero.one_le
  have hℓ0 : 0 ≤ Real.log χ.conductor := Real.log_nonneg (by exact_mod_cast hq1)
  have hℓL : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast Nat.le_of_dvd (by omega) hqn)
  have hlq := log_div_pi χ.conductor
  have hl1 : Real.log (((1 : ℕ) : ℝ) / Real.pi) = -Real.log Real.pi := by
    rw [log_div_pi, Nat.cast_one, Real.log_one, zero_sub]
  have hpi0 := log_pi_ge
  have hpi1 := log_pi_le
  obtain ⟨hH1, hH2⟩ := cotas_H h hS hG
  have hHz := cotas_Hz
  -- sumas sobre ceros
  have hZs : ∀ (T' : ℝ) (hfin : (ZerosBelow χ.primitiveCharacter T').Finite),
      ‖∑ ρ ∈ hfin.toFinset, (mult χ.primitiveCharacter ρ : ℂ) * K x (2 / 5) (9 / 20) ρ‖ ≤
        Real.sqrt 2 / 2 * Real.log n *
          ((Real.log χ.conductor + 43287 / 10000) * (5 / 9) +
            (Real.log χ.conductor + 37738 / 10000) * (10 / 19)) := by
    intro T' hfin
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_natCast]
    refine (suma_K_le hG hp hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
      hfin).trans ?_
    have h1 := hadamard_chi_le h hS hG hp hχ' (σ := 1 + 2 / 5) (by norm_num) (by norm_num) hfin
    have h2 := hadamard_chi_le h hS hG hp hχ' (σ := 1 + 9 / 20) (by norm_num) (by norm_num) hfin
    rw [hsx]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hL0)
    have k1 := div_le_div_of_nonneg_right h1 (show (0 : ℝ) ≤ 1 + 2 * (2 / 5) by norm_num)
    have k2 := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 1 + 2 * (9 / 20) by norm_num)
    refine (add_le_add k1 k2).trans ?_
    rw [show (1 : ℝ) + 2 * (2 / 5) = 9 / 5 by norm_num, show (1 : ℝ) + 2 * (9 / 20) = 19 / 10 by norm_num]
    linarith
  have hZz : ∀ (T' : ℝ) (hfin : (ZerosBelow (1 : DirichletCharacter ℂ 1) T').Finite),
      ‖∑ ρ ∈ hfin.toFinset, (mult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * K x (2 / 5) (9 / 20) ρ‖ ≤
        Real.sqrt 2 / 2 * Real.log n * (52434 / 10000) := by
    intro T' hfin
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_natCast]
    refine (suma_K_le hG hp1 hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
      hfin).trans ?_
    have h1 := hadamard_zeta_le h hS hG (σ := 1 + 2 / 5) (by norm_num) (by norm_num) hfin
    have h2 := hadamard_zeta_le h hS hG (σ := 1 + 9 / 20) (by norm_num) (by norm_num) hfin
    rw [hsx]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hL0)
    have k1 := div_le_div_of_nonneg_right h1 (show (0 : ℝ) ≤ 1 + 2 * (2 / 5) by norm_num)
    have k2 := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 1 + 2 * (9 / 20) by norm_num)
    exact (add_le_add k1 k2).trans hHz
  -- fórmula explícita para `χ*` y para `ζ`
  have hLEs := cota_LE h.refl hS h.zl hp hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num)
    (by norm_num) (by norm_num)
  have hLE1 := cota_LE h.refl hS h.zl hp1 hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num)
    (by norm_num) (by norm_num)
  have hSs := cota_S h hp hx1 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
    (by norm_num) hLEs.1 hZs
  have hS1 := cota_S h hp1 hx1 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
    (by norm_num) hLE1.1 hZz
  have hd : del1 χ.primitiveCharacter = 0 := by unfold del1; rw [if_neg hχ']
  have hd1 : del1 (1 : DirichletCharacter ℂ 1) = 1 := by unfold del1; rw [if_pos rfl]
  have he1 : eps0 (1 : DirichletCharacter ℂ 1) = 0 := by
    unfold eps0; rw [if_neg (fun h => h.2 rfl)]
  have he := re_eps0_div_nonneg χ.primitiveCharacter (a := 2 / 5) (b := 9 / 20) (by norm_num)
    (by norm_num)
  have r1 := (Complex.re_le_norm _).trans hSs
  rw [hd, zero_mul, sub_zero] at r1
  simp only [Complex.add_re] at r1
  have r2 := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hS1)
  rw [he1, zero_div, add_zero, hd1, one_mul, K_uno, S_uno] at r2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at r2
  -- comparación
  have hcmp := re_S_ge hx0 hcon
  -- residuos
  have hRs := abs_le.mp (cota_res h h.refl hS hG hp hx0)
  have hR1 := abs_le.mp (cota_res h h.refl hS hG hp1 hx0)
  rw [hl1] at hR1
  obtain ⟨hD1, hD0, hX⟩ := cotas_D_X hx8192
  have hRd : (Res (1 : DirichletCharacter ℂ 1) x (2 / 5) (9 / 20)).re -
      (Res χ.primitiveCharacter x (2 / 5) (9 / 20)).re ≤ 625 / 1000 * Real.log χ.conductor + 30 := by
    have := mul_le_mul_of_nonneg_left hD1 hℓ0
    rw [hlq] at hRs
    nlinarith [hRs.1, hR1.2]
  -- lado izquierdo
  have ht0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have htL : x ^ (-(1 / 2 : ℝ)) * Real.log n * (141421 / 100000) ≤ 1 := by
    have e : x ^ (-(1 / 2 : ℝ)) * (Real.sqrt 2 * Real.log n) = 1 := by
      rw [← sqrt_dos_L hL0, ← hxdef, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
    have h2 := mul_le_mul_of_nonneg_left sqrt_dos_ge (mul_nonneg ht0 hL0)
    linarith
  have hA : |Real.log ((χ.conductor : ℝ) / Real.pi)| ≤ Real.log n + 139 / 100 := by
    rw [hlq, abs_le]; constructor <;> linarith
  have hB : |Real.log (((1 : ℕ) : ℝ) / Real.pi)| ≤ 139 / 100 := by
    rw [hl1, abs_neg, abs_of_nonneg (by linarith)]; exact hpi1
  have hV := VM_le_tres h hS hG (σ := 3 / 2) (by norm_num)
  have hP : 8 / Real.pi ≤ 255 / 100 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_d2]
  have hLEb := le_trans (add_le_add hLEs.2 hLE1.2) (cota_LE_num hn ht0 htL hA hB hV hP)
  -- potencias de primos que dividen a `n`
  have hE := (cota_suma_potencias hx1 ((Finset.Icc 1 ⌊x⌋₊).filter (fun m => ¬ Nat.Coprime m n))
    n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun m hm hpp => by
      rw [Finset.mem_filter, coprime_iff_minFac hpp, not_not] at hm
      exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hpp.ne_one, hm.2, by omega⟩)
    (fun m hm => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      exact (Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le hx0.le))).trans (suma_cotaP_le hn1)
  have hE' := (cota_suma_potencias hx1 ((Finset.Icc 1 ⌊x⌋₊).filter
      (fun m => ¬ Nat.Coprime m n ∧ Nat.Coprime m χ.conductor))
    (n.primeFactors.filter (fun p => ¬ p ∣ χ.conductor))
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (fun m hm hpp => by
      rw [Finset.mem_filter, coprime_iff_minFac hpp, coprime_iff_minFac hpp, not_not] at hm
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hpp.ne_one, hm.2.1, by omega⟩, hm.2.2⟩)
    (fun m hm => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      exact (Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le hx0.le))).trans
    (suma_cotaP_le' hn1 hqn hq1)
  -- aritmética final
  rw [show ((1 : ℝ) + 2 / 5) * (1 + 9 / 20) = 203 / 100 by norm_num] at r2
  exact aritmetica_final hn hℓ0 hℓL (r := Real.sqrt 2 / 2) (by positivity)
    (by linarith [sqrt_dos_le]) le_rfl le_rfl hLEb hRd hE hE' (by linarith)

end AMate.Miller.Explicito
