import AMateMiller.Miller

/-!
# Test de Miller: de subgrupos propios a caracteres de Dirichlet

* `existe_caracter_trivial_en`: si `H` es un subgrupo propio de `(ℤ/nℤ)ˣ`, existe un carácter de
  Dirichlet `χ ≠ 1` módulo `n` con `χ(u) = 1` para todo `u ∈ H` (dualidad de grupos abelianos
  finitos aplicada a `(ℤ/nℤ)ˣ/H`).
* `CotaCaracteres B`: todo carácter `χ ≠ 1` módulo `n ≥ 3` toma un valor distinto de `1` en algún
  `a ≤ B n` coprimo con `n`. Es la forma de la cota de Bach que da el análisis.
* `cotaSubgruposPropios_of_cotaCaracteres`: `CotaCaracteres B → CotaSubgruposPropios B`.
* `cotaSubgruposPropios_id`: la cota trivial `B n = n` vale sin hipótesis.
-/

namespace AMate.Miller

/-- Si `H` es un subgrupo propio de `(ℤ/nℤ)ˣ`, hay un carácter de Dirichlet no trivial que vale `1`
en `H`. -/
theorem existe_caracter_trivial_en {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod n) = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : (ZMod n)ˣ, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun g _ => h g)
  have hq : (QuotientGroup.mk g : (ZMod n)ˣ ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have : NeZero (Monoid.exponent ((ZMod n)ˣ ⧸ H) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (by exact @Monoid.exponent_ne_zero_of_finite ((ZMod n)ˣ ⧸ H) _ _)⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hq
  set ψ : (ZMod n)ˣ →* ℂˣ := φ.comp (QuotientGroup.mk' H) with hψ
  refine ⟨MulChar.ofUnitHom ψ, ?_, ?_⟩
  · intro h1
    apply hφ
    have h := congrArg (fun χ : DirichletCharacter ℂ n => χ (g : ZMod n)) h1
    simp only [MulChar.ofUnitHom_coe, MulChar.one_apply_coe] at h
    exact Units.ext (by simpa [hψ] using h)
  · intro u hu
    rw [MulChar.ofUnitHom_coe]
    have : (u : (ZMod n)ˣ ⧸ H) = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    simp [hψ, this]

/-- **Cota para caracteres**: todo carácter de Dirichlet no trivial módulo `n ≥ 3` toma un valor
distinto de `1` en algún `a ≤ B n` coprimo con `n`. -/
def CotaCaracteres (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
    ∃ a : ℕ, a ≤ B n ∧ Nat.Coprime a n ∧ χ (a : ZMod n) ≠ 1

/-- **Puente algebraico**: una cota para caracteres es una cota para subgrupos propios. -/
theorem cotaSubgruposPropios_of_cotaCaracteres {B : ℕ → ℕ} (hB : CotaCaracteres B) :
    CotaSubgruposPropios B := by
  intro n hn H hH
  have : NeZero n := ⟨by omega⟩
  obtain ⟨χ, hχ, hχH⟩ := existe_caracter_trivial_en H hH
  obtain ⟨a, haB, hcop, hχa⟩ := hB n hn χ hχ
  have hunit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr hcop
  refine ⟨a, haB, hunit.unit, by simp, fun hmem => hχa ?_⟩
  have h := hχH _ hmem
  rwa [IsUnit.unit_spec] at h

/-- La cota trivial `B n = n` vale sin hipótesis: toda unidad está representada por su
representante en `[0, n)`. -/
theorem cotaSubgruposPropios_id : CotaSubgruposPropios id := by
  intro n hn H hH
  have : NeZero n := ⟨by omega⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod n)ˣ, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun g _ => h g)
  refine ⟨(g : ZMod n).val, (ZMod.val_lt _).le, g, by simp, hg⟩

end AMate.Miller
