import AMateMiller.FormulaExplicita

/-!
# Cota de tipo Bach para caracteres de Dirichlet, a partir de GRH

Supongamos tres enunciados sobre las funciones `L(s,χ)` de caracteres primitivos: la fórmula
explícita truncada (`PI.ExplicitFormulaWith C₁`), la cota de ceros en ventanas
(`PI.ZerosWindowWith C₂`) y que sus ceros con `0 < Re ρ < 1` están en `Re ρ = 1/2` (GRH).
Entonces existe `K` tal que todo carácter `χ ≠ 1` módulo `n ≥ 3` toma un valor distinto de `1` en
algún `a ≤ K (1 + log n)⁴` coprimo con `n` (`cota_caracteres_de_grh`).

Esquema: si `χ(a) = 1` para todo `a ≤ B` coprimo con `n`, con `χ*` el carácter primitivo que
induce `χ`, la parte real de `ψ₀(B, χ*)` es al menos `ψ(B) − 2 E`, con `E` la contribución de los
`m ≤ B` no coprimos con `n` (`E ≤ 2 log n · log B`). La fórmula explícita para `χ*` y para el
carácter trivial módulo `1` acota `|ψ₀(B, χ*)|` y `|ψ(B) − B|` por `√B · log² + log²`; juntas dan
`B ≪ √B (1 + log n)² log² B`, imposible si `B ≈ K (1 + log n)⁴` con `K` grande.

* `suma_ceros_le`: `∑_{|Im ρ| < T} m_ρ/|ρ| ≤ 4 C₂ log(N(T + 2)) (1 + log(T + 1))`, cubriendo
  `|Im ρ| < T` con las ventanas centradas en `±j`.
* `norm_psi0_le`: `|ψ₀(B, χ)| ≤ √B · (…) + C₁ (…)` para `χ` primitivo y `B ≥ 2`.
* `suma_no_coprimos_le`: `∑_{m ≤ B, (m,n) > 1} Λ(m) ≤ 2 log n log B`.
* `cota_caracteres_de_grh`: el resultado.
-/

open Complex

namespace AMate.Miller

open PI

/-- GRH para caracteres primitivos, en la forma de `PrimitiveDirichletLZerosOnLine`. -/
def GRHPrimitivo : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-! ### Sumas sobre ceros -/

section Ceros

variable {N : ℕ} [NeZero N]

theorem re_eq_half_de_mem (hGRH : GRHPrimitivo) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow χ T) : ρ.re = 1 / 2 :=
  hGRH N χ hp ρ hρ.1 hρ.2.1 hρ.2.2.2

/-- Si `Re ρ = 1/2`, entonces `|ρ| ≥ (⌊|Im ρ|⌋ + 1)/2`. -/
theorem norm_ge_floor {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ((⌊|ρ.im|⌋₊ : ℝ) + 1) / 2 ≤ ‖ρ‖ := by
  have h1 : 1 / 2 ≤ ‖ρ‖ := by
    have := Complex.abs_re_le_norm ρ
    rw [hre] at this
    linarith [abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  have h2 : (⌊|ρ.im|⌋₊ : ℝ) ≤ ‖ρ‖ :=
    (Nat.floor_le (abs_nonneg _)).trans (Complex.abs_im_le_norm ρ)
  rcases Nat.eq_zero_or_pos ⌊|ρ.im|⌋₊ with h | h
  · rw [h]
    simpa using h1
  · have : (1 : ℝ) ≤ ⌊|ρ.im|⌋₊ := by exact_mod_cast h
    linarith

/-- **Suma de `m_ρ/|ρ|` por ventanas**: con GRH y la cota de ceros en ventanas,
`∑_{ρ ∈ ZerosBelow χ T} m_ρ/|ρ| ≤ 4 C₂ log(N(T + 2)) (1 + log(T + 1))`. -/
theorem suma_ceros_le {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hZW : ZerosWindowWith C₂) (hGRH : GRHPrimitivo)
    (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (ZerosBelow χ T).Finite) :
    ∑ᶠ ρ ∈ ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖
      ≤ 4 * C₂ * Real.log (N * (T + 2)) * (1 + Real.log (T + 1)) := by
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
    with hmdef
  have hm0 : ∀ ρ, 0 ≤ m ρ := fun ρ => Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set Z := hfin.toFinset with hZdef
  set M := ⌊T⌋₊ with hMdef
  have hMT : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hmaps : ∀ ρ ∈ Z, ⌊|ρ.im|⌋₊ ∈ Finset.range (M + 1) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor hρ.2.2.1.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set Λ₀ : ℝ := Real.log (N * (T + 2)) with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := Real.log_nonneg (by nlinarith)
  have hfib : ∀ j ∈ Finset.range (M + 1),
      ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖ ≤ 4 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjT : (j : ℝ) ≤ T := (Nat.cast_le.mpr hjM).trans hMT
    obtain ⟨hfinA, hA⟩ := hZW N χ hp (j : ℝ)
    obtain ⟨hfinB, hB⟩ := hZW N χ hp (-(j : ℝ))
    rw [abs_neg, Nat.abs_cast] at hB
    rw [Nat.abs_cast] at hA
    have hlogj : Real.log (N * ((j : ℝ) + 2)) ≤ Λ₀ :=
      Real.log_le_log (by positivity) (by nlinarith)
    -- la fibra cabe en las dos ventanas centradas en `±j`
    have hsub : (Z.filter fun ρ => ⌊|ρ.im|⌋₊ = j) ⊆ hfinA.toFinset ∪ hfinB.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter, hZdef, Set.Finite.mem_toFinset] at hρ
      obtain ⟨⟨h0, h1, -, hL⟩, hfl⟩ := hρ
      have hlo : (j : ℝ) ≤ |ρ.im| := by rw [← hfl]; exact Nat.floor_le (abs_nonneg _)
      have hhi : |ρ.im| < (j : ℝ) + 1 := by rw [← hfl]; exact Nat.lt_floor_add_one _
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      rcases le_or_gt 0 ρ.im with him | him
      · left
        refine ⟨h0, h1, ?_, hL⟩
        rw [abs_of_nonneg him] at hlo hhi
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨h0, h1, ?_, hL⟩
        rw [abs_of_neg him] at hlo hhi
        rw [abs_le]
        constructor <;> linarith
    have hsumF : ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ ≤ 2 * C₂ * Λ₀ := by
      calc ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ
          ≤ ∑ ρ ∈ hfinA.toFinset ∪ hfinB.toFinset, m ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ => hm0 ρ
        _ ≤ ∑ ρ ∈ hfinA.toFinset, m ρ + ∑ ρ ∈ hfinB.toFinset, m ρ := by
            rw [← Finset.sum_union_inter]
            have : 0 ≤ ∑ ρ ∈ hfinA.toFinset ∩ hfinB.toFinset, m ρ :=
              Finset.sum_nonneg fun ρ _ => hm0 ρ
            linarith
        _ = (∑ᶠ ρ ∈ ZerosNear χ (j : ℝ), m ρ) + ∑ᶠ ρ ∈ ZerosNear χ (-(j : ℝ)), m ρ := by
            rw [finsum_mem_eq_finite_toFinset_sum _ hfinA, finsum_mem_eq_finite_toFinset_sum _ hfinB]
        _ ≤ C₂ * Real.log (N * ((j : ℝ) + 2)) + C₂ * Real.log (N * ((j : ℝ) + 2)) :=
            add_le_add hA hB
        _ ≤ 2 * C₂ * Λ₀ := by nlinarith
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = j),
        m ρ / ‖ρ‖ ≤ m ρ * (2 / ((j : ℝ) + 1)) := by
      intro ρ hρ
      have hmem := hρ
      rw [Finset.mem_filter, hZdef, Set.Finite.mem_toFinset] at hmem
      have hre := re_eq_half_de_mem hGRH hp hmem.1
      have hn := norm_ge_floor hre
      rw [hmem.2] at hn
      have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by positivity) hn
      rw [div_le_iff₀ hpos]
      have := hm0 ρ
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      calc m ρ = m ρ * (2 / ((j : ℝ) + 1)) * (((j : ℝ) + 1) / 2) := by field_simp
        _ ≤ m ρ * (2 / ((j : ℝ) + 1)) * ‖ρ‖ := by gcongr
    calc ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖
        ≤ ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ * (2 / ((j : ℝ) + 1)) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ) * (2 / ((j : ℝ) + 1)) := by rw [Finset.sum_mul]
      _ ≤ (2 * C₂ * Λ₀) * (2 / ((j : ℝ) + 1)) := by gcongr
      _ = 4 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1)) := by ring
  have hharm : ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) ≤ 1 + Real.log (T + 1) := by
    have hh := harmonic_le_one_add_log (M + 1)
    have heq : ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) = (harmonic (M + 1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [heq]
    refine hh.trans ?_
    have : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (T + 1) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    linarith
  calc ∑ j ∈ Finset.range (M + 1), ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖
      ≤ ∑ j ∈ Finset.range (M + 1), 4 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1)) := Finset.sum_le_sum hfib
    _ = 4 * C₂ * Λ₀ * ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) := by rw [Finset.mul_sum]
    _ ≤ 4 * C₂ * Λ₀ * (1 + Real.log (T + 1)) := by gcongr

/-- `|∑_ρ m_ρ u^ρ/ρ| ≤ √u ∑_ρ m_ρ/|ρ|` si todos los ceros están en `Re ρ = 1/2`. -/
theorem norm_suma_ceros_le (hGRH : GRHPrimitivo) (χ : DirichletCharacter ℂ N)
    (hp : χ.IsPrimitive) {u T : ℝ} (hu : 0 < u) (hfin : (ZerosBelow χ T).Finite) :
    ‖∑ᶠ ρ ∈ ZerosBelow χ T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖
      ≤ Real.sqrt u * ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  have hre := re_eq_half_de_mem hGRH hp hρ
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre,
    ← Real.sqrt_eq_rpow]
  ring_nf
  rfl

/-- **Fórmula explícita con GRH**: para `χ` primitivo y `B ≥ 2`,
`|ψ₀(B,χ)| ≤ √B · 4C₂ log(N(B+2))(1 + log(B+1)) + C₁ (log²(NB²) + log(NB) + 4C₂ log(3N)(1 + log 2))`. -/
theorem norm_psi0_le {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hEF : ExplicitFormulaWith C₁)
    (hZW : ZerosWindowWith C₂) (hGRH : GRHPrimitivo) (χ : DirichletCharacter ℂ N)
    (hp : χ.IsPrimitive) {B : ℝ} (hB : 2 ≤ B) :
    ‖psi0 χ B‖ ≤ Real.sqrt B * (4 * C₂ * Real.log (N * (B + 2)) * (1 + Real.log (B + 1)))
      + C₁ * (Real.log (N * B * B) ^ 2 + Real.log (N * B)
        + 4 * C₂ * Real.log (N * (1 + 2)) * (1 + Real.log (1 + 1))) := by
  obtain ⟨hfin, hbound⟩ := hEF N χ hp B B hB le_rfl
  have hfin1 : (ZerosBelow χ 1).Finite := hfin.subset fun ρ hρ =>
    ⟨hρ.1, hρ.2.1, lt_of_lt_of_le hρ.2.2.1 (by linarith), hρ.2.2.2⟩
  have hS := suma_ceros_le hC₂ hZW hGRH χ hp (by linarith : (1 : ℝ) ≤ B) hfin
  have hS1 := suma_ceros_le hC₂ hZW hGRH χ hp le_rfl hfin1
  have hZ := norm_suma_ceros_le hGRH χ hp (by linarith : (0 : ℝ) < B) hfin
  have hB0 : B ≠ 0 := by linarith
  rw [mul_div_cancel_left₀ _ hB0] at hbound
  set Zs := ∑ᶠ ρ ∈ ZerosBelow χ B,
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((B : ℂ) ^ ρ / ρ) with hZs
  have htri : ‖psi0 χ B‖ ≤ ‖psi0 χ B + Zs‖ + ‖Zs‖ := by
    calc ‖psi0 χ B‖ = ‖(psi0 χ B + Zs) - Zs‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖psi0 χ B + Zs‖ + ‖Zs‖ := norm_sub_le _ _
  have hsq := Real.sqrt_nonneg B
  have e1 := mul_le_mul_of_nonneg_left hS hsq
  have e2 := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (Real.log (N * B * B) ^ 2 + Real.log (N * B))) hS1) hC₁
  exact htri.trans ((add_le_add hbound hZ).trans ((add_le_add e2 e1).trans
    (le_of_eq (add_comm _ _))))

end Ceros

/-! ### El carácter trivial y la comparación con `ψ` -/

/-- Para el carácter trivial módulo `1`, `ψ₀(u) = ψ(u) − u`. -/
theorem psi0_one (u : ℝ) :
    psi0 (1 : DirichletCharacter ℂ 1) u
      = ((∑ m ∈ Finset.Icc 1 ⌊u⌋₊, ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) - u := by
  unfold psi0
  rw [if_pos rfl]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]

/-- Si `χ(m) = 1` para todo `m ≤ B` coprimo con `n`, entonces
`Re ψ₀(B, χ*) ≥ ψ(B) − 2 ∑_{m ≤ B, (m,n) > 1} Λ(m)`. -/
theorem re_psi0_ge {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1) {B : ℕ}
    (h : ∀ m : ℕ, m ≤ B → Nat.Coprime m n → χ m = 1) :
    (∑ m ∈ Finset.Icc 1 B, ArithmeticFunction.vonMangoldt m)
      - 2 * ∑ m ∈ (Finset.Icc 1 B).filter (fun m => ¬ Nat.Coprime m n),
          ArithmeticFunction.vonMangoldt m
      ≤ (psi0 χ.primitiveCharacter (B : ℝ)).re := by
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
  have hval : ∀ m : ℕ, Nat.Coprime m n →
      χ.primitiveCharacter (m : ZMod χ.conductor) = χ (m : ZMod n) := by
    intro m hm
    have e := χ.primitiveCharacter.changeLevel_eq_cast_of_dvd' χ.conductor_dvd_level
      (a := (m : ℤ)) (Nat.isCoprime_iff_coprime.mpr hm)
    rw [χ.changeLevel_primitiveCharacter] at e
    simpa using e.symm
  unfold psi0
  rw [if_neg hχ', sub_zero, Nat.floor_natCast, Complex.re_sum]
  set Λ := ArithmeticFunction.vonMangoldt
  have key : ∀ m ∈ Finset.Icc 1 B, (if Nat.Coprime m n then Λ m else -Λ m)
      ≤ (((Λ m : ℝ) : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
    intro m hm
    rw [Complex.re_ofReal_mul]
    have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
    split_ifs with hc
    · have hmB : m ≤ B := (Finset.mem_Icc.mp hm).2
      rw [hval m hc, h m hmB hc, Complex.one_re, mul_one]
    · have h1 := Complex.abs_re_le_norm (χ.primitiveCharacter (m : ZMod χ.conductor))
      have h2 := DirichletCharacter.norm_le_one χ.primitiveCharacter (m : ZMod χ.conductor)
      have h3 : -1 ≤ (χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
        have := neg_abs_le (χ.primitiveCharacter (m : ZMod χ.conductor)).re
        linarith
      nlinarith
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
  rw [Finset.sum_ite, Finset.sum_neg_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 B) (fun m => Nat.Coprime m n)]
  ring

/-- `∑_{m ≤ B, (m,n) > 1} Λ(m) ≤ 2 log n · log B`: cada término es `log p` con `p^k = m ≤ B` y
`p ∣ n`, hay a lo sumo `log B / log p` potencias de cada `p` y a lo sumo `log₂ n` primos. -/
theorem suma_no_coprimos_le {n B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) :
    ∑ m ∈ (Finset.Icc 1 B).filter (fun m => ¬ Nat.Coprime m n), ArithmeticFunction.vonMangoldt m
      ≤ 2 * Real.log n * Real.log B := by
  set F := (Finset.Icc 1 B).filter (fun m => ¬ Nat.Coprime m n) with hF
  set PF := n.primeFactors with hPF
  set f : ℕ → ℕ → ℝ := fun m p => if IsPrimePow m ∧ m.minFac = p then Real.log p else 0
    with hfdef
  have hlogp : ∀ p ∈ PF, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hf0 : ∀ m, ∀ p ∈ PF, 0 ≤ f m p := by
    intro m p hp
    simp only [hfdef]
    split_ifs
    · exact hlogp p hp
    · exact le_rfl
  have ha : ∀ m ∈ F, ArithmeticFunction.vonMangoldt m ≤ ∑ p ∈ PF, f m p := by
    intro m hm
    rw [hF, Finset.mem_filter] at hm
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · have hm1 : m ≠ 1 := hpp.ne_one
      have hprime : m.minFac.Prime := Nat.minFac_prime hm1
      have hdvd : m.minFac ∣ n := by
        by_contra hnd
        have hc : Nat.Coprime m.minFac n := (Nat.Prime.coprime_iff_not_dvd hprime).mpr hnd
        apply hm.2
        rw [← hpp.minFac_pow_factorization_eq]
        exact Nat.Coprime.pow_left _ hc
      have hmem : m.minFac ∈ PF := Nat.mem_primeFactors.mpr ⟨hprime, hdvd, by omega⟩
      have hs := Finset.single_le_sum (fun p hp => hf0 m p hp) hmem
      have hfm : f m m.minFac = Real.log m.minFac := by
        simp only [hfdef, hpp, true_and, if_true]
      rw [hfm] at hs
      exact hs
    · exact Finset.sum_nonneg fun p hp => hf0 m p hp
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hc : ∀ p ∈ PF, ∑ m ∈ F, f m p ≤ Real.log B := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hlogpos : 0 < Real.log p := Real.log_pos hp1
    set G := F.filter (fun m => IsPrimePow m ∧ m.minFac = p) with hGdef
    have hsum : ∑ m ∈ F, f m p = (G.card : ℝ) * Real.log p := by
      simp only [hfdef]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    set x := Real.log B / Real.log p with hxdef
    have hG : G ⊆ (Finset.Icc 1 ⌊x⌋₊).image (fun k => p ^ k) := by
      intro m hm
      rw [hGdef, Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨⟨-, hmB⟩, -⟩, hpp, hmin⟩ := hm
      rw [Finset.mem_image]
      have hpk : p ^ (m.factorization m.minFac) = m := by
        rw [← hmin]
        exact hpp.minFac_pow_factorization_eq
      refine ⟨m.factorization m.minFac, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hpk⟩
      · by_contra hk
        push Not at hk
        have h0 : m.factorization m.minFac = 0 := by omega
        rw [h0, pow_zero] at hpk
        exact hpp.ne_one hpk.symm
      · apply Nat.le_floor
        rw [hxdef, le_div_iff₀ hlogpos]
        have hle : ((p : ℝ)) ^ (m.factorization m.minFac) ≤ B := by
          have : p ^ (m.factorization m.minFac) ≤ B := by rw [hpk]; exact hmB
          exact_mod_cast this
        calc ((m.factorization m.minFac : ℕ) : ℝ) * Real.log p
            = Real.log (((p : ℝ)) ^ (m.factorization m.minFac)) := by rw [Real.log_pow]
          _ ≤ Real.log B := Real.log_le_log (by positivity) hle
    have hcard : (G.card : ℝ) ≤ x := by
      have h1 : G.card ≤ ⌊x⌋₊ :=
        (Finset.card_le_card hG).trans (Finset.card_image_le.trans (by simp))
      calc (G.card : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
        _ ≤ x := Nat.floor_le (div_nonneg hlogB hlogpos.le)
    rw [hsum]
    calc (G.card : ℝ) * Real.log p ≤ x * Real.log p := by gcongr
      _ = Real.log B := by rw [hxdef]; field_simp
  have hd : (PF.card : ℝ) ≤ 2 * Real.log n := by
    have h2 : 2 ^ PF.card ≤ ∏ p ∈ PF, p :=
      Finset.pow_card_le_prod PF (fun p => p) 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    have h3 : ∏ p ∈ PF, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have h4 : ((2 : ℝ)) ^ PF.card ≤ n := by exact_mod_cast h2.trans h3
    have h5 : (PF.card : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h4
    have h6 := Real.log_two_gt_d9
    nlinarith [mul_nonneg (Nat.cast_nonneg PF.card) (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]
  calc ∑ m ∈ F, ArithmeticFunction.vonMangoldt m ≤ ∑ m ∈ F, ∑ p ∈ PF, f m p :=
        Finset.sum_le_sum ha
    _ = ∑ p ∈ PF, ∑ m ∈ F, f m p := Finset.sum_comm
    _ ≤ ∑ _p ∈ PF, Real.log B := Finset.sum_le_sum hc
    _ = (PF.card : ℝ) * Real.log B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log n * Real.log B := by gcongr

/-! ### El teorema -/

/-- `log B ≤ 12 M L` si `0 < B ≤ M⁸ L⁴` con `M, L ≥ 1`. -/
theorem log_le_doce {Mm L Bv : ℝ} (hM : 1 ≤ Mm) (hL : 1 ≤ L) (hB : 0 < Bv)
    (hBX : Bv ≤ Mm ^ 8 * L ^ 4) : Real.log Bv ≤ 12 * (Mm * L) := by
  have h1 : Real.log Bv ≤ Real.log (Mm ^ 8 * L ^ 4) := Real.log_le_log hB hBX
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
  have hm := Real.log_le_sub_one_of_pos (show 0 < Mm by linarith)
  have hl := Real.log_le_sub_one_of_pos (show 0 < L by linarith)
  have hmL : Mm ≤ Mm * L := le_mul_of_one_le_right (by linarith) hL
  have hLm : L ≤ Mm * L := le_mul_of_one_le_left (by linarith) hM
  push_cast at h1
  linarith

/-- Aritmética final: las cotas son incompatibles con `M⁸ L⁴ < B + 1`. -/
theorem final_contradiccion {D Mm L Bv ψ E ln lB : ℝ} (hD : 0 ≤ D) (hMm : Mm = 2 * D + 48 + 2)
    (hL : 1 ≤ L) (hX : Mm ^ 8 * L ^ 4 < Bv + 1) (k1 : Bv - ψ ≤ D * (Mm ^ 6 * L ^ 4))
    (k2 : ψ - 2 * E ≤ D * (Mm ^ 6 * L ^ 4)) (hE : E ≤ 2 * ln * lB) (hln : ln ≤ L)
    (hlB : lB ≤ 12 * (Mm * L)) (hlB0 : 0 ≤ lB) : False := by
  have hM1 : 1 ≤ Mm := by linarith
  set Q : ℝ := Mm ^ 6 * L ^ 4 with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) (one_le_pow₀ hL)
  have hp : ln * lB ≤ L * (12 * (Mm * L)) := mul_le_mul hln hlB hlB0 (by linarith)
  have hML : Mm * L ^ 2 ≤ Q := by
    have hM6 : Mm ≤ Mm ^ 6 := le_self_pow₀ hM1 (by norm_num)
    have hL4 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    exact mul_le_mul hM6 hL4 (by positivity) (by positivity)
  have hp' : L * (12 * (Mm * L)) = 12 * (Mm * L ^ 2) := by ring
  have h8 : Mm ^ 8 * L ^ 4 = Mm ^ 2 * Q := by rw [hQ]; ring
  have hM2 : Mm ≤ Mm ^ 2 := by nlinarith
  have hMQ : Mm * Q ≤ Mm ^ 2 * Q := mul_le_mul_of_nonneg_right hM2 (by positivity)
  have hlin : Mm * Q = 2 * (D * Q) + 48 * Q + 2 * Q := by rw [hMm]; ring
  linarith

/-- Cota del lado derecho de `norm_psi0_le` cuando `2 ≤ B ≤ M⁸ L⁴`, `1 ≤ N` y `log N ≤ L`. -/
theorem cota_lado_derecho {C₁ C₂ Mm L Bv Nv : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM : 1 ≤ Mm)
    (hL : 1 ≤ L) (hB2 : 2 ≤ Bv) (hBX : Bv ≤ Mm ^ 8 * L ^ 4) (hN1 : 1 ≤ Nv)
    (hNL : Real.log Nv ≤ L) :
    Real.sqrt Bv * (4 * C₂ * Real.log (Nv * (Bv + 2)) * (1 + Real.log (Bv + 1)))
      + C₁ * (Real.log (Nv * Bv * Bv) ^ 2 + Real.log (Nv * Bv)
        + 4 * C₂ * Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1)))
      ≤ (784 * C₂ + C₁ * (638 + 24 * C₂)) * (Mm ^ 6 * L ^ 4) := by
  set P : ℝ := Mm * L with hPdef
  have hP1 : 1 ≤ P := by nlinarith
  have hLP : L ≤ P := by nlinarith
  have hB0 : 0 < Bv := by linarith
  have hlogN0 : 0 ≤ Real.log Nv := Real.log_nonneg hN1
  have hlogB0 : 0 ≤ Real.log Bv := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlogB : Real.log Bv ≤ 12 * P := by
    have h1 : Real.log Bv ≤ Real.log (Mm ^ 8 * L ^ 4) := Real.log_le_log hB0 hBX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    have hm := Real.log_le_sub_one_of_pos (show 0 < Mm by linarith)
    have hl := Real.log_le_sub_one_of_pos (show 0 < L by linarith)
    push_cast at h1
    nlinarith
  have hlog2B : Real.log (2 * Bv) ≤ 1 + 12 * P := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith
  have a1 : Real.log (Nv * (Bv + 2)) ≤ 14 * P := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have : Real.log (Bv + 2) ≤ Real.log (2 * Bv) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have a1' : 0 ≤ Real.log (Nv * (Bv + 2)) := Real.log_nonneg (by nlinarith)
  have a2 : 1 + Real.log (Bv + 1) ≤ 14 * P := by
    have : Real.log (Bv + 1) ≤ Real.log (2 * Bv) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have a2' : 0 ≤ 1 + Real.log (Bv + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Bv + 1 by linarith)
    linarith
  have a3 : Real.log (Nv * Bv * Bv) ≤ 25 * P := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by linarith) (by linarith)]
    linarith
  have a3' : 0 ≤ Real.log (Nv * Bv * Bv) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 (by linarith)) (by linarith))
  have a4 : Real.log (Nv * Bv) ≤ 13 * P := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have a5 : Real.log (Nv * (1 + 2)) ≤ 3 * P := by
    rw [Real.log_mul (by linarith) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 by norm_num)
    linarith
  have a5' : 0 ≤ Real.log (Nv * (1 + 2)) := Real.log_nonneg (by linarith)
  have a6 : 1 + Real.log (1 + 1) ≤ 2 := by norm_num; linarith
  have a6' : 0 ≤ 1 + Real.log (1 + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 1 by norm_num)
    linarith
  have hsqrt : Real.sqrt Bv ≤ Mm ^ 4 * L ^ 2 := by
    calc Real.sqrt Bv ≤ Real.sqrt (Mm ^ 8 * L ^ 4) := Real.sqrt_le_sqrt hBX
      _ = Mm ^ 4 * L ^ 2 := by
          rw [show Mm ^ 8 * L ^ 4 = (Mm ^ 4 * L ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have t1 : Real.sqrt Bv * (4 * C₂ * Real.log (Nv * (Bv + 2)) * (1 + Real.log (Bv + 1)))
      ≤ (Mm ^ 4 * L ^ 2) * (4 * C₂ * (14 * P) * (14 * P)) := by
    have hab := mul_le_mul a1 a2 a2' (by positivity)
    have h4 : 4 * C₂ * Real.log (Nv * (Bv + 2)) * (1 + Real.log (Bv + 1))
        ≤ 4 * C₂ * (14 * P) * (14 * P) := by
      have := mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ 4 * C₂)
      linarith [this]
    exact mul_le_mul hsqrt h4 (by positivity) (by positivity)
  have t2 : C₁ * (Real.log (Nv * Bv * Bv) ^ 2 + Real.log (Nv * Bv)
        + 4 * C₂ * Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1)))
      ≤ C₁ * ((25 * P) ^ 2 + 13 * P + 4 * C₂ * (3 * P) * 2) := by
    apply mul_le_mul_of_nonneg_left _ hC₁
    have h3 : Real.log (Nv * Bv * Bv) ^ 2 ≤ (25 * P) ^ 2 := pow_le_pow_left₀ a3' a3 2
    have h5 : Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1)) ≤ (3 * P) * 2 :=
      mul_le_mul a5 a6 a6' (by positivity)
    have h5' := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * C₂)
    nlinarith
  have hP2 : P ^ 2 ≤ Mm ^ 6 * L ^ 4 := by
    have hM2 : Mm ^ 2 ≤ Mm ^ 6 := pow_le_pow_right₀ hM (by norm_num)
    have hL2 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    calc P ^ 2 = Mm ^ 2 * L ^ 2 := by rw [hPdef]; ring
      _ ≤ Mm ^ 6 * L ^ 4 := mul_le_mul hM2 hL2 (by positivity) (by positivity)
  have hPP : P ≤ P ^ 2 := by nlinarith
  calc _ ≤ (Mm ^ 4 * L ^ 2) * (4 * C₂ * (14 * P) * (14 * P))
        + C₁ * ((25 * P) ^ 2 + 13 * P + 4 * C₂ * (3 * P) * 2) := add_le_add t1 t2
    _ = 784 * C₂ * (Mm ^ 4 * L ^ 2 * P ^ 2) + C₁ * (625 * P ^ 2 + (13 + 24 * C₂) * P) := by ring
    _ = 784 * C₂ * (Mm ^ 6 * L ^ 4) + C₁ * (625 * P ^ 2 + (13 + 24 * C₂) * P) := by
        rw [hPdef]; ring
    _ ≤ 784 * C₂ * (Mm ^ 6 * L ^ 4) + C₁ * ((638 + 24 * C₂) * (Mm ^ 6 * L ^ 4)) := by
        gcongr
        nlinarith
    _ = (784 * C₂ + C₁ * (638 + 24 * C₂)) * (Mm ^ 6 * L ^ 4) := by ring

/-- **Cota de tipo Bach a partir de GRH.** Con la fórmula explícita, la cota de ceros en ventanas y
GRH para los caracteres primitivos, existe `K > 0` tal que todo carácter `χ ≠ 1` módulo `n ≥ 3`
cumple `χ(a) ≠ 1` para algún `a ≤ K (1 + log n)⁴` coprimo con `n`. -/
theorem cota_caracteres_de_grh {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hEF : PI.ExplicitFormulaWith C₁) (hZW : PI.ZerosWindowWith C₂)
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 4 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  have hG : GRHPrimitivo := hGRH
  set D : ℝ := 784 * C₂ + C₁ * (638 + 24 * C₂) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set A : ℝ := 2 * D + 48 with hAdef
  set Mm : ℝ := A + 2 with hMm
  have hM1 : 1 ≤ Mm := by linarith
  refine ⟨Mm ^ 8, by positivity, fun n hn χ hχ => ?_⟩
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set L : ℝ := 1 + Real.log n with hLdef
  have hL1 : 1 ≤ L := by linarith
  set X : ℝ := Mm ^ 8 * L ^ 4 with hXdef
  have hX0 : 0 ≤ X := by positivity
  set B : ℕ := ⌊X⌋₊ with hBdef
  have hBX : (B : ℝ) ≤ X := Nat.floor_le hX0
  have hXB : X < (B : ℝ) + 1 := Nat.lt_floor_add_one X
  have hX256 : (256 : ℝ) ≤ X := by
    have h1 : (2 : ℝ) ^ 8 ≤ Mm ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have h2 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL1
    have h3 : Mm ^ 8 ≤ Mm ^ 8 * L ^ 4 := le_mul_of_one_le_right (by positivity) h2
    norm_num at h1
    linarith
  have hB256 : 256 ≤ B := Nat.le_floor (by exact_mod_cast hX256)
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast (by omega : 2 ≤ B)
  have hB1 : 1 ≤ B := by omega
  have hcop : ∀ m : ℕ, m ≤ B → Nat.Coprime m n → χ m = 1 := fun m hm hc =>
    hcon m (le_trans (by exact_mod_cast hm) hBX) hc
  -- carácter primitivo asociado y carácter trivial módulo 1
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp' : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hqn : χ.conductor ≤ n := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hp1 : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have b1 := norm_psi0_le hC₁.le hC₂.le hEF hZW hG (1 : DirichletCharacter ℂ 1) hp1 hB2
  have bq := norm_psi0_le hC₁.le hC₂.le hEF hZW hG χ.primitiveCharacter hp' hB2
  have hre := re_psi0_ge hχ hcop
  have hE := suma_no_coprimos_le (n := n) (B := B) (by omega) hB1
  -- cotas del lado derecho
  have hq1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast NeZero.one_le
  have hlogq : Real.log (χ.conductor : ℝ) ≤ L := by
    have : Real.log (χ.conductor : ℝ) ≤ Real.log n :=
      Real.log_le_log (by linarith) (by exact_mod_cast hqn)
    linarith
  have r1 := cota_lado_derecho (Nv := ((1 : ℕ) : ℝ)) hC₁.le hC₂.le hM1 hL1 hB2 hBX
    (by norm_num) (by rw [Nat.cast_one, Real.log_one]; linarith)
  have rq := cota_lado_derecho (Nv := (χ.conductor : ℝ)) hC₁.le hC₂.le hM1 hL1 hB2 hBX hq1 hlogq
  rw [psi0_one, Nat.floor_natCast] at b1
  set ψ : ℝ := ∑ m ∈ Finset.Icc 1 B, ArithmeticFunction.vonMangoldt m with hψ
  set E : ℝ := ∑ m ∈ (Finset.Icc 1 B).filter (fun m => ¬ Nat.Coprime m n),
    ArithmeticFunction.vonMangoldt m with hEdef
  have hψB : (B : ℝ) - ψ ≤ ‖((ψ : ℝ) : ℂ) - ((B : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact le_abs_self _
  have hreq := Complex.re_le_norm (psi0 χ.primitiveCharacter (B : ℝ))
  have k1 : (B : ℝ) - ψ ≤ D * (Mm ^ 6 * L ^ 4) := hψB.trans (b1.trans r1)
  have k2 : ψ - 2 * E ≤ D * (Mm ^ 6 * L ^ 4) := hre.trans (hreq.trans (bq.trans rq))
  have hlogB := log_le_doce hM1 hL1 (by linarith) hBX
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  exact final_contradiccion hD0 (by rw [hMm, hAdef]) hL1 hXB k1 k2 hE (by linarith) hlogB hlogB0

/-- La misma cota con los enunciados existenciales `PI.ExplicitFormula` y `PI.ZerosWindow`. -/
theorem cota_caracteres_de_grh' (hEF : PI.ExplicitFormula) (hZW : PI.ZerosWindow)
    (hGRH : GRHPrimitivo) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 4 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  obtain ⟨C₁, hC₁, h₁⟩ := hEF
  obtain ⟨C₂, hC₂, h₂⟩ := hZW
  exact cota_caracteres_de_grh hC₁ hC₂ h₁ h₂ hGRH

end AMate.Miller
