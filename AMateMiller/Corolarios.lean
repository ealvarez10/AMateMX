import AMateMiller.MillerCertificado

/-!
# Corolarios de la cota de Bach

A partir de la cota para caracteres (de un `n` fijo) sale la cota para subgrupos propios de
`(ℤ/nℤ)ˣ` (`subgrupo_de_caracteres`), y de ahí dos corolarios clásicos de Bach (1990):

* **Generadores pequeños** (`generan_*`): las unidades representadas por enteros
  `a ≤ 2 (log n)²` generan `(ℤ/nℤ)ˣ` si `log n ≥ 64` (`a ≤ 16 (log n)²` si `log n ≥ 8.3`; para
  todo `n ≥ 3`, las representadas por `a ≤ basesCertificadas n`).
* **No-residuos de potencia `k`** (`noPotencia_*`): si `p` es primo y `k ≥ 2` divide a `p − 1`,
  hay un `a ≤ 16 (log p)²` (si `log p ≥ 8.3`) que no es potencia `k`-ésima módulo `p`, y
  `a ≤ 2 (log p)²` si `log p ≥ 64`. Con `k = 2` es el no-residuo cuadrático.
-/

namespace AMate.Miller

open AMate.Miller.Hadamard AMate.Miller.PI.Digamma

/-- **Puente para un `n` fijo**: si todo carácter `χ ≠ 1` módulo `n` toma un valor `≠ 1` en algún
`a` con la propiedad `P`, a todo subgrupo propio de `(ℤ/nℤ)ˣ` le falta una unidad `a` con `P a`. -/
theorem subgrupo_de_caracteres {n : ℕ} [NeZero n] {P : ℕ → Prop}
    (hB : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, P a ∧ Nat.Coprime a n ∧ χ (a : ZMod n) ≠ 1)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≠ ⊤) :
    ∃ a : ℕ, P a ∧ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H := by
  obtain ⟨χ, hχ, hχH⟩ := existe_caracter_trivial_en H hH
  obtain ⟨a, haP, hcop, hχa⟩ := hB χ hχ
  have hunit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr hcop
  refine ⟨a, haP, hunit.unit, by simp, fun hmem => hχa ?_⟩
  have h := hχH _ hmem
  rwa [IsUnit.unit_spec] at h

/-- Las unidades de `ZMod n` representadas por enteros con la propiedad `P`. -/
def unidadesCon (n : ℕ) (P : ℕ → Prop) : Set (ZMod n)ˣ :=
  {u | ∃ a : ℕ, P a ∧ (u : ZMod n) = a}

/-- **Generadores**: si a todo subgrupo propio le falta una unidad con `P`, esas unidades generan
`(ℤ/nℤ)ˣ`. -/
theorem generan_de_subgrupos {n : ℕ} {P : ℕ → Prop}
    (hB : ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
      ∃ a : ℕ, P a ∧ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H) :
    Subgroup.closure (unidadesCon n P) = ⊤ := by
  by_contra h
  obtain ⟨a, haP, u, hu, huH⟩ := hB _ h
  exact huH (Subgroup.subset_closure ⟨a, haP, hu⟩)

/-- **Generadores pequeños** (Bach): si `log n ≥ 64`, las unidades representadas por enteros
`a ≤ 2 (log n)²` generan `(ℤ/nℤ)ˣ`. -/
theorem generan_explicito (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {n : ℕ}
    (hn : 64 ≤ Real.log n) :
    Subgroup.closure (unidadesCon n fun a => (a : ℝ) ≤ 2 * Real.log n ^ 2) = ⊤ := by
  have : NeZero n := ⟨fun h0 => by rw [h0, Nat.cast_zero, Real.log_zero] at hn; linarith⟩
  exact generan_de_subgrupos (subgrupo_de_caracteres
    (Explicito.cota_bach_explicita h hS hG n hn))

/-- Si `log n ≥ 8.3`, las unidades representadas por enteros `a ≤ 16 (log n)²` generan
`(ℤ/nℤ)ˣ`. -/
theorem generan_16 (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {n : ℕ}
    (hn : 83 / 10 ≤ Real.log n) :
    Subgroup.closure (unidadesCon n fun a => (a : ℝ) ≤ 16 * Real.log n ^ 2) = ⊤ := by
  have : NeZero n := ⟨fun h0 => by rw [h0, Nat.cast_zero, Real.log_zero] at hn; linarith⟩
  exact generan_de_subgrupos (subgrupo_de_caracteres (Explicito.cota_bach_16 h hS hG n hn))

/-- Para todo `n ≥ 3`, las unidades representadas por enteros `a ≤ basesCertificadas n` generan
`(ℤ/nℤ)ˣ`. -/
theorem generan_certificadas (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {n : ℕ}
    (hn : 3 ≤ n) :
    Subgroup.closure (unidadesCon n fun a => a ≤ basesCertificadas n) = ⊤ :=
  generan_de_subgrupos fun H hH =>
    cotaSubgruposPropios_of_cotaCaracteres (cotaCaracteres_basesCertificadas h hS hG) n hn H hH

/-! ### No-residuos de potencia `k` -/

/-- Si `p` es primo y `k ≥ 2` divide a `p − 1`, las potencias `k`-ésimas forman un subgrupo
propio de `(ℤ/pℤ)ˣ`. -/
theorem potencias_propio {p k : ℕ} [Fact p.Prime] (hk : 2 ≤ k) (hkp : k ∣ p - 1) :
    (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range ≠ ⊤ := by
  have hq : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
  have : Fact (Nat.minFac k).Prime := ⟨hq⟩
  have hdvd : Nat.minFac k ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    exact (Nat.minFac_dvd k).trans hkp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (Nat.minFac k) hdvd
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact hq.one_lt.ne hx
  have hxk : x ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx ▸ Nat.minFac_dvd k)
  rw [Ne, MonoidHom.range_eq_top, ← Finite.injective_iff_surjective]
  intro hinj
  apply hx1
  apply hinj
  simp [powMonoidHom_apply, hxk]

/-- De una cota de tipo Bach sale un no-residuo de potencia `k` pequeño módulo `p`. -/
theorem noPotencia_de_cota {C L₀ : ℝ}
    (hB : ∀ n : ℕ, L₀ ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ C * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1)
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k ∣ p - 1) (hL : L₀ ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ C * Real.log p ^ 2 ∧ ¬ ∃ y : ZMod p, y ^ k = a := by
  haveI := Fact.mk hp
  obtain ⟨a, ha, u, hu, huH⟩ := subgrupo_de_caracteres (hB p hL) _ (potencias_propio hk hkp)
  refine ⟨a, ha, ?_⟩
  rintro ⟨y, hy⟩
  have hyu : IsUnit (y ^ k) := by rw [hy, ← hu]; exact u.isUnit
  rw [isUnit_pow_iff (by omega)] at hyu
  apply huH
  refine ⟨hyu.unit, Units.ext ?_⟩
  simp [powMonoidHom_apply, hy, hu]

/-- Si `p` es primo, `k ≥ 2` divide a `p − 1` y `log p ≥ 8.3`, hay un `a ≤ 16 (log p)²` que no
es potencia `k`-ésima módulo `p`. -/
theorem noPotencia_16 (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {p k : ℕ}
    (hp : p.Prime) (hk : 2 ≤ k) (hkp : k ∣ p - 1) (hL : 83 / 10 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 16 * Real.log p ^ 2 ∧ ¬ ∃ y : ZMod p, y ^ k = a :=
  noPotencia_de_cota (Explicito.cota_bach_16 h hS hG) hp hk hkp hL

/-- Lo mismo con `a ≤ 2 (log p)²` si `log p ≥ 64`. -/
theorem noPotencia_explicito (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo)
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k ∣ p - 1) (hL : 64 ≤ Real.log p) :
    ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log p ^ 2 ∧ ¬ ∃ y : ZMod p, y ^ k = a :=
  noPotencia_de_cota (Explicito.cota_bach_explicita h hS hG) hp hk hkp hL

end AMate.Miller
