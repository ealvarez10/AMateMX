import AMateMiller.HadamardBase

/-!
# Reflexión de `Λd` para la función zeta

`ReflexionLogDeriv` (de Alpöge) cubre los caracteres primitivos de módulo `N > 1`. Para `N = 1`
(la zeta de Riemann) se deduce aquí de la ecuación funcional de Mathlib
`completedRiemannZeta (1 − s) = completedRiemannZeta s`: con `ζ = Λ/Γℝ`,

  `Λd(s) = −½ log π + ½ ψ(s/2) + ζ'/ζ(s) = Λ'/Λ(s)`, y `Λ'/Λ(1 − s) = −Λ'/Λ(s)`.

`reflexion_gen` reúne los dos casos.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- `logDeriv Γℝ(s) = −½ log π + ½ ψ(s/2)`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Gammaℝ s = -((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hdΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hs
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := differentiableAt_id.div_const 2
  have hP : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
    simpa using h
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have e : Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; rfl
  rw [e, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s hpow hΓ hP.differentiableAt (hdΓ.comp s hd2)]
  have h1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -((Real.log Real.pi : ℝ) : ℂ) / 2 := by
    rw [logDeriv_apply, hP.deriv, ← Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have h2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) hdΓ hd2
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) = Complex.Gamma ∘ (fun z : ℂ => z / 2) from rfl,
      this, deriv_div_const, deriv_id'', Complex.digamma_def]
    ring
  rw [h1, h2]

/-- `Γℝ` es holomorfa y no se anula fuera de `{0, −2, −4, …}`. -/
theorem Gammaℝ_ne_zero' {s : ℂ} (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hs n
  rw [hn]; ring

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero' hs))
  have e : (fun z => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by funext z; simp
  rwa [e] at h

/-- `ζ'/ζ = Λ'/Λ − Γℝ'/Γℝ`. -/
theorem logDeriv_zeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0)
    (hg : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv riemannZeta s = logDeriv completedRiemannZeta s - logDeriv Gammaℝ s := by
  have hG := Gammaℝ_ne_zero' hg
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h; apply hz; rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have heq : riemannZeta =ᶠ[𝓝 s] fun z => completedRiemannZeta z / Gammaℝ z := by
    filter_upwards [isOpen_ne.mem_nhds hs0] with z hz
    exact riemannZeta_def_of_ne_zero hz
  have hld : logDeriv riemannZeta s = logDeriv (fun z => completedRiemannZeta z / Gammaℝ z) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [hld, logDeriv_div s hΛ hG (differentiableAt_completedZeta hs0 hs1) (differentiableAt_Gammaℝ hg)]

/-- `Λ'/Λ(1 − s) = −Λ'/Λ(s)`. -/
theorem logDeriv_completed_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have e : completedRiemannZeta = completedRiemannZeta ∘ fun z => 1 - z := by
    funext z; simp [completedRiemannZeta_one_sub]
  have h1 : (1 - s) ≠ 0 := by intro h; apply hs1; linear_combination -h
  have h2 : (1 - s) ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) := differentiableAt_completedZeta h1 h2
  have := logDeriv_comp (f := completedRiemannZeta) (g := fun z : ℂ => 1 - z) (x := s) hd
    (by fun_prop)
  rw [← e] at this
  rw [this]
  simp

/-- **Reflexión para `ζ`** (el carácter trivial módulo `1`). -/
theorem reflexion_zeta (χ : DirichletCharacter ℂ 1) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hz0 : riemannZeta s ≠ 0) (hz1 : riemannZeta (1 - s) ≠ 0)
    (hg0 : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) (hg1 : ∀ n : ℕ, (1 - s) / 2 ≠ -(n : ℂ)) :
    Λd χ s = -Λd χ⁻¹ (1 - s) := by
  have hpar : par χ = 0 := by
    rcases par_spec χ with ⟨-, h⟩ | ⟨ho, -⟩
    · exact h
    · exfalso
      have : χ (-1) = 1 := by
        rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
      unfold DirichletCharacter.Odd at ho
      rw [this] at ho
      norm_num at ho
  have hpar' : par χ⁻¹ = 0 := by rw [par_inv]; exact hpar
  have h1s0 : (1 - s) ≠ 0 := by intro h; apply hs1; linear_combination -h
  have h1s1 : (1 - s) ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hA : Λd χ s = logDeriv completedRiemannZeta s := by
    unfold Λd
    rw [hpar, add_zero, DirichletCharacter.LFunction_modOne_eq, logDeriv_zeta_eq hs0 hs1 hz0 hg0,
      logDeriv_Gammaℝ hg0, Nat.cast_one, one_div, Real.log_inv]
    push_cast
    ring
  have hB : Λd χ⁻¹ (1 - s) = logDeriv completedRiemannZeta (1 - s) := by
    unfold Λd
    rw [hpar', add_zero, DirichletCharacter.LFunction_modOne_eq,
      logDeriv_zeta_eq h1s0 h1s1 hz1 hg1, logDeriv_Gammaℝ hg1, Nat.cast_one, one_div, Real.log_inv]
    push_cast
    ring
  rw [hA, hB, logDeriv_completed_one_sub hs0 hs1, neg_neg]

/-- **Reflexión para todo carácter primitivo** (`N > 1` por `ReflexionLogDeriv`, `N = 1` por
`reflexion_zeta`). -/
theorem reflexion_gen (hR : ReflexionLogDeriv) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {s : ℂ} (h1 : ∀ n : ℕ, (s + par χ) / 2 ≠ -(n : ℂ))
    (h2 : ∀ n : ℕ, (1 - s + par χ) / 2 ≠ -(n : ℂ))
    (h3 : DirichletCharacter.LFunction χ s ≠ 0)
    (h4 : DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0) :
    Λd χ s = -Λd χ⁻¹ (1 - s) := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · exact reflexion hR hN hp h1 h2 h3 h4
  · have hN1 : N = 1 := by have := NeZero.one_le (n := N); omega
    subst hN1
    have hpar : par χ = 0 := by
      rcases par_spec χ with ⟨-, h⟩ | ⟨ho, -⟩
      · exact h
      · exfalso
        have : χ (-1) = 1 := by
          rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
        unfold DirichletCharacter.Odd at ho
        rw [this] at ho
        norm_num at ho
    rw [hpar, add_zero] at h1 h2
    have hs0 : s ≠ 0 := by intro e; apply h1 0; rw [e]; simp
    have hs1 : s ≠ 1 := by intro e; apply h2 0; rw [e]; simp
    rw [DirichletCharacter.LFunction_modOne_eq] at h3 h4
    exact reflexion_zeta χ hs0 hs1 h3 h4 h1 h2

end AMate.Miller.Hadamard
