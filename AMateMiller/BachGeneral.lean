import AMateMiller.BachExplicito

/-!
# La cota de Bach explícita con umbral bajo

`desigualdad_bach` extrae de la demostración de `cota_bach_explicita` la desigualdad que vale
para todo `x ≥ 1`: si `χ ≠ 1` vale `1` en todos los `a ≤ x` coprimos con `n`, entonces

  `100 x/203 ≤ (√x/2)(…ℓ…) + x^{-1/2}(10ℓ + 672.9) + ℓ D(x) + 24 X'(x) + 51.3 + 4.01 L + 13.27 (L − ℓ)`

con `L = log n` y `ℓ = log q` (`q` el conductor). Con `x = c L²` es imposible si `L` es grande;
cuanto mayor es `c`, menor es el umbral:

* `cota_bach_explicita` (otro archivo): `c = 2`, `log n ≥ 64`;
* `cota_bach_4`: `c = 4`, `log n ≥ 23.5` (`n ≥ 2^34`);
* `cota_bach_16`: `c = 16`, `log n ≥ 8.3` (`n ≥ 2^12`).
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Hadamard AMate.Miller.Ponderada AMate.Miller.DigammaExp

set_option linter.unusedSectionVars false

/-- Aritmética del lado izquierdo, para `x` cualquiera. -/
theorem cota_LE_gen {t ℓ A B V P : ℝ} (ht0 : 0 ≤ t) (hA : A ≤ ℓ + 139 / 100)
    (hB : B ≤ 139 / 100) (hV : V ≤ 3) (hP : P ≤ 255 / 100) :
    t * ((A + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) + P) +
      t * ((B + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) + P) ≤ t * (10 * ℓ + 6729 / 10) := by
  have e : ∀ u : ℝ, (u + 17 + V + 12) / (2 * (1 / 2 - 9 / 20)) = 10 * (u + 29 + V) :=
    fun u => by ring
  rw [e, e, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) ht0

/-- **Desigualdad principal** para todo `x ≥ 1`. -/
theorem desigualdad_bach (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {n : ℕ}
    (hn1 : 1 ≤ n) {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1) {x : ℝ} (hx1 : 1 ≤ x)
    (hcon : ∀ a : ℕ, (a : ℝ) ≤ x → Nat.Coprime a n → χ a = 1) :
    100 / 203 * x ≤
      Real.sqrt x / 2 * ((Real.log χ.conductor + 43287 / 10000) * (5 / 9) +
          (Real.log χ.conductor + 37738 / 10000) * (10 / 19) + 52434 / 10000) +
        x ^ (-(1 / 2 : ℝ)) * (10 * Real.log χ.conductor + 6729 / 10) +
        (Real.log χ.conductor * (20 * (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ)))) +
          24 * (20 * (x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ))))) +
        (513 / 10 + 401 / 100 * Real.log n) +
        1327 / 100 * (Real.log n - Real.log χ.conductor) := by
  have : NeZero n := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
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
        Real.sqrt x / 2 *
          ((Real.log χ.conductor + 43287 / 10000) * (5 / 9) +
            (Real.log χ.conductor + 37738 / 10000) * (10 / 19)) := by
    intro T' hfin
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_natCast]
    refine (suma_K_le hG hp hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
      hfin).trans ?_
    have h1 := hadamard_chi_le h hS hG hp hχ' (σ := 1 + 2 / 5) (by norm_num) (by norm_num) hfin
    have h2 := hadamard_chi_le h hS hG hp hχ' (σ := 1 + 9 / 20) (by norm_num) (by norm_num) hfin
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have k1 := div_le_div_of_nonneg_right h1 (show (0 : ℝ) ≤ 1 + 2 * (2 / 5) by norm_num)
    have k2 := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 1 + 2 * (9 / 20) by norm_num)
    refine (add_le_add k1 k2).trans ?_
    rw [show (1 : ℝ) + 2 * (2 / 5) = 9 / 5 by norm_num, show (1 : ℝ) + 2 * (9 / 20) = 19 / 10 by norm_num]
    linarith
  have hZz : ∀ (T' : ℝ) (hfin : (ZerosBelow (1 : DirichletCharacter ℂ 1) T').Finite),
      ‖∑ ρ ∈ hfin.toFinset, (mult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * K x (2 / 5) (9 / 20) ρ‖ ≤
        Real.sqrt x / 2 * (52434 / 10000) := by
    intro T' hfin
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_natCast]
    refine (suma_K_le hG hp1 hx0 (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
      hfin).trans ?_
    have h1 := hadamard_zeta_le h hS hG (σ := 1 + 2 / 5) (by norm_num) (by norm_num) hfin
    have h2 := hadamard_zeta_le h hS hG (σ := 1 + 9 / 20) (by norm_num) (by norm_num) hfin
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
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
  have hRd : (Res (1 : DirichletCharacter ℂ 1) x (2 / 5) (9 / 20)).re -
      (Res χ.primitiveCharacter x (2 / 5) (9 / 20)).re ≤
        Real.log χ.conductor * (20 * (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ)))) +
          24 * (20 * (x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ)))) := by
    rw [hlq] at hRs
    have e1 : (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) =
        20 * (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) := by ring
    have e2 : (x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) =
        20 * (x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ))) := by ring
    rw [e1, e2] at hRs hR1
    linarith [hRs.1, hR1.2]
  -- lado izquierdo
  have ht0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hA : |Real.log ((χ.conductor : ℝ) / Real.pi)| ≤ Real.log χ.conductor + 139 / 100 := by
    rw [hlq, abs_le]; constructor <;> linarith
  have hB : |Real.log (((1 : ℕ) : ℝ) / Real.pi)| ≤ 139 / 100 := by
    rw [hl1, abs_neg, abs_of_nonneg (by linarith)]; exact hpi1
  have hV := VM_le_tres h hS hG (σ := 3 / 2) (by norm_num)
  have hP : 8 / Real.pi ≤ 255 / 100 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_d2]
  have hLEb := le_trans (add_le_add hLEs.2 hLE1.2) (cota_LE_gen ht0 hA hB hV hP)
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
  -- combinación
  rw [show ((1 : ℝ) + 2 / 5) * (1 + 9 / 20) = 203 / 100 by norm_num] at r2
  linarith

/-- Si `a² s ≤ x` con `√a ≤ s`, entonces `x^{2/5} ≥ a`, y de ahí cotas de `D(x)` y `X'(x)`. -/
theorem cotas_D_X_gen {x a s : ℝ} (ha : 0 < a) (hs : Real.sqrt a ≤ s) (hx1 : 1 ≤ x)
    (hx : a ^ 2 * s ≤ x) :
    20 * (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) ≤ 20 / a ∧
      0 ≤ 20 * (x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) ∧
      24 * (20 * (x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ)))) ≤ 960 / a := by
  have hx0 : 0 < x := by linarith
  have h52 : a ^ (5 / 2 : ℝ) ≤ x := by
    have e : a ^ (5 / 2 : ℝ) = a ^ 2 * Real.sqrt a := by
      rw [Real.sqrt_eq_rpow, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add ha,
        Real.rpow_two]
    rw [e]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans hx
  have hge : a ≤ x ^ (2 / 5 : ℝ) := by
    have e : a = (a ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_mul ha.le]; norm_num
    rw [e]
    exact Real.rpow_le_rpow (by positivity) h52 (by norm_num)
  have hu : x ^ (-(2 / 5 : ℝ)) ≤ 1 / a := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le ha hge
  have hv : x ^ (-(9 / 20 : ℝ)) ≤ x ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hv0 : 0 < x ^ (-(9 / 20 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  rw [div_eq_mul_one_div 20 a, div_eq_mul_one_div 960 a]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Aritmética final con `x = 16 L²` y `L ≥ 8.3`. -/
theorem aritmetica_16 {L ℓ x sx t D X : ℝ} (hL : 83 / 10 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L)
    (hx : x = 16 * L ^ 2) (hsx : sx = 4 * L) (ht0 : 0 ≤ t) (ht : t * (4 * L) = 1)
    (hD : D ≤ 20 / 15) (hD0 : 0 ≤ D) (hX : X ≤ 960 / 15)
    (hmain : 100 / 203 * x ≤
      sx / 2 * ((ℓ + 43287 / 10000) * (5 / 9) + (ℓ + 37738 / 10000) * (10 / 19) +
          52434 / 10000) +
        t * (10 * ℓ + 6729 / 10) + (ℓ * D + X) + (513 / 10 + 401 / 100 * L) +
        1327 / 100 * (L - ℓ)) : False := by
  subst hx hsx
  have hℓD : ℓ * D ≤ L * (20 / 15) :=
    (mul_le_mul_of_nonneg_right hℓL hD0).trans (mul_le_mul_of_nonneg_left hD (by linarith))
  have htℓ : t * ℓ ≤ t * L := mul_le_mul_of_nonneg_left hℓL ht0
  have htL : t * (83 / 10) ≤ t * L := mul_le_mul_of_nonneg_left hL ht0
  have h3 : 0 ≤ (L - ℓ) * (370 / 171 * L - 1327 / 100) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (L - 83 / 10) ^ 2 := sq_nonneg _
  nlinarith

/-- Aritmética final con `x = 4 L²` y `L ≥ 23.5`. -/
theorem aritmetica_4 {L ℓ x sx t D X : ℝ} (hL : 47 / 2 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L)
    (hx : x = 4 * L ^ 2) (hsx : sx = 2 * L) (ht0 : 0 ≤ t) (ht : t * (2 * L) = 1)
    (hD : D ≤ 20 / 20) (hD0 : 0 ≤ D) (hX : X ≤ 960 / 20)
    (hmain : 100 / 203 * x ≤
      sx / 2 * ((ℓ + 43287 / 10000) * (5 / 9) + (ℓ + 37738 / 10000) * (10 / 19) +
          52434 / 10000) +
        t * (10 * ℓ + 6729 / 10) + (ℓ * D + X) + (513 / 10 + 401 / 100 * L) +
        1327 / 100 * (L - ℓ)) : False := by
  subst hx hsx
  have hℓD : ℓ * D ≤ L * (20 / 20) :=
    (mul_le_mul_of_nonneg_right hℓL hD0).trans (mul_le_mul_of_nonneg_left hD (by linarith))
  have htℓ : t * ℓ ≤ t * L := mul_le_mul_of_nonneg_left hℓL ht0
  have htL : t * (47 / 2) ≤ t * L := mul_le_mul_of_nonneg_left hL ht0
  have h3 : 0 ≤ (L - ℓ) * (185 / 171 * L - 1327 / 100) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (L - 47 / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- `√(c² L²) = c L` y `x^{-1/2} · √x = 1`. -/
theorem raiz_y_potencia {x L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c) (hx : x = c ^ 2 * L ^ 2)
    (hx0 : 0 < x) :
    Real.sqrt x = c * L ∧ x ^ (-(1 / 2 : ℝ)) * (c * L) = 1 := by
  have hs : Real.sqrt x = c * L := by
    rw [hx, show c ^ 2 * L ^ 2 = (c * L) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hc hL)]
  refine ⟨hs, ?_⟩
  rw [← hs, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
  norm_num

/-- **Cota de Bach con constante 16**: si `log n ≥ 8.3`, todo carácter `χ ≠ 1` módulo `n`
toma un valor `≠ 1` en algún `a ≤ 16 (log n)²` coprimo con `n`. -/
theorem cota_bach_16 (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) :
    ∀ n : ℕ, 83 / 10 ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ 16 * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.cast_zero, Real.log_zero] at hn; linarith
  have hL0 : 0 ≤ Real.log n := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 16 * Real.log n ^ 2 := ⟨_, rfl⟩
  rw [← hxdef] at hcon
  have hxL : (873 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hx1 : 1 ≤ x := by linarith
  have key := desigualdad_bach h hS hG hn1 hχ hx1 hcon
  obtain ⟨hsx, ht⟩ := raiz_y_potencia (x := x) hL0 (c := 4) (by norm_num)
    (by rw [hxdef]; ring) (by linarith)
  have hs15 : Real.sqrt 15 ≤ 388 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  obtain ⟨hD, hD0, hX⟩ := cotas_D_X_gen (a := 15) (by norm_num) hs15 hx1 (by linarith)
  have : NeZero n := ⟨by omega⟩
  have hq1 : 1 ≤ χ.conductor := by
    have := χ.conductor_ne_zero; omega
  have hℓ0 : 0 ≤ Real.log χ.conductor := Real.log_nonneg (by exact_mod_cast hq1)
  have hℓL : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hq1)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  exact aritmetica_16 hn hℓ0 hℓL hxdef hsx (Real.rpow_nonneg (by linarith) _) ht hD hD0 hX key

/-- **Cota de Bach con constante 4**: si `log n ≥ 23.5`, todo carácter `χ ≠ 1` módulo `n`
toma un valor `≠ 1` en algún `a ≤ 4 (log n)²` coprimo con `n`. -/
theorem cota_bach_4 (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) :
    ∀ n : ℕ, 47 / 2 ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ 4 * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.cast_zero, Real.log_zero] at hn; linarith
  have hL0 : 0 ≤ Real.log n := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 4 * Real.log n ^ 2 := ⟨_, rfl⟩
  rw [← hxdef] at hcon
  have hxL : (1790 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hx1 : 1 ≤ x := by linarith
  have key := desigualdad_bach h hS hG hn1 hχ hx1 hcon
  obtain ⟨hsx, ht⟩ := raiz_y_potencia (x := x) hL0 (c := 2) (by norm_num)
    (by rw [hxdef]; ring) (by linarith)
  have hs20 : Real.sqrt 20 ≤ 4473 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  obtain ⟨hD, hD0, hX⟩ := cotas_D_X_gen (a := 20) (by norm_num) hs20 hx1 (by linarith)
  have : NeZero n := ⟨by omega⟩
  have hq1 : 1 ≤ χ.conductor := by
    have := χ.conductor_ne_zero; omega
  have hℓ0 : 0 ≤ Real.log χ.conductor := Real.log_nonneg (by exact_mod_cast hq1)
  have hℓL : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hq1)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  exact aritmetica_4 hn hℓ0 hℓL hxdef hsx (Real.rpow_nonneg (by linarith) _) ht hD hD0 hX key

end AMate.Miller.Explicito
