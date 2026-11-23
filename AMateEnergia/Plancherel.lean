import Mathlib

/-!
# Plancherel en `L¹ ∩ L²`

Mathlib da la transformada de Fourier en `L²` como isometría (`Lp.fourierTransformₗᵢ`).
`fourier_toLp_ae_eq` la identifica con la transformada integral cuando `f ∈ L¹ ∩ L²`, a través de
las distribuciones temperadas y del lema fundamental `ae_eq_of_integral_contDiff_smul_eq`.
`plancherel` deduce `∫ |𝓕 f|² = ∫ |f|²`, con la normalización `e^{−2πixξ}`.
-/

open MeasureTheory Complex FourierTransform SchwartzMap
open scoped ContDiff

namespace AMate

/-- Para `f ∈ L¹ ∩ L²` en `ℝ`, la transformada de Fourier en `L²` coincide en casi todo punto
con la transformada integral. -/
theorem fourier_toLp_ae_eq {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    ⇑(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕 f := by
  set H : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (h2.toLp f) with hH
  have hHloc : LocallyIntegrable (H : ℝ → ℂ) volume :=
    (Lp.memLp H).locallyIntegrable (by norm_num)
  have hFcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  refine ae_eq_of_integral_contDiff_smul_eq hHloc hFcont.locallyIntegrable fun g hg hgc => ?_
  have hφs : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := ofRealCLM.contDiff.comp hg
  have hφc : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left ofReal_zero
  set φ : 𝓢(ℝ, ℂ) := hφc.toSchwartzMap hφs with hφ
  have key := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at key
  have hswap : ∫ x, (𝓕 (φ : ℝ → ℂ)) x • f x = ∫ ξ, φ ξ • 𝓕 f ξ := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable h1
  have hL : ∫ x, (𝓕 φ) x • (h2.toLp f : ℝ → ℂ) x = ∫ x, (𝓕 (φ : ℝ → ℂ)) x • f x := by
    refine integral_congr_ae (h2.coeFn_toLp.mono fun x hx => ?_)
    simp only [fourier_coe, hx]
  rw [hL, hswap] at key
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  simp only [hφx] at key
  simp only [Complex.real_smul]
  exact key.symm

theorem norm_sq_Lp_eq (g : Lp ℂ 2 (volume : Measure ℝ)) : ‖g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) g g
  simp only [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h' : (((‖g‖ ^ 2 : ℝ)) : ℂ) = ((∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact h
  exact_mod_cast h'

/-- **Plancherel** para `f ∈ L¹ ∩ L²` en `ℝ`, con la normalización `e^{−2πixξ}` de Mathlib. -/
theorem plancherel {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    MemLp (𝓕 f) 2 ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hae := fourier_toLp_ae_eq h1 h2
  refine ⟨(Lp.memLp _).ae_eq hae, ?_⟩
  have hnorm := Lp.norm_fourier_eq (h2.toLp f)
  calc ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ ξ, ‖(⇑(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2 :=
        (integral_congr_ae (hae.mono fun x hx => by simp only [hx])).symm
    _ = ‖𝓕 (h2.toLp f)‖ ^ 2 := (norm_sq_Lp_eq _).symm
    _ = ‖h2.toLp f‖ ^ 2 := by rw [hnorm]
    _ = ∫ x, ‖(h2.toLp f : ℝ → ℂ) x‖ ^ 2 := norm_sq_Lp_eq _
    _ = ∫ x, ‖f x‖ ^ 2 := integral_congr_ae (h2.coeFn_toLp.mono fun x hx => by simp only [hx])

end AMate
