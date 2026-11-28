import AMateMiller.BachExplicito

/-!
# La cota de Bach explícita con umbral bajo

La desigualdad principal `desigualdad_bach` (`BachExplicito.lean`) vale para todo `x ≥ 1`. Con
`x = c L²` (`L = log n`) es imposible si `L` es grande; cuanto mayor es `c`, menor es el umbral:

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
