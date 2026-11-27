import AMateMiller.ReflexionZeta

/-!
# La identidad de Hadamard en un rectángulo

Para `χ` primitivo módulo `N > 1`, `1 < σ < 3/2` y una altura `T'` sin ordenadas de ceros, en el
rectángulo `R = [−1/2, 3/2] × [−T', T']` y con `G(s) = 1/(s − (1 − σ)) − 1/(s − σ)`:

  `∑_{|Im ρ| < T'} m_ρ (1/(σ − ρ) − 1/(1 − σ − ρ)) = Λd(σ, χ) + Λd(σ, χ⁻¹) + (2πi)⁻¹ ∮_R Λd·G`.

* `regΛd`: `Λd = H₁ + ∑ m_ρ/(s − ρ)` en `R` (la parte regular de `L'/L` de `RegularPart` más el
  término arquimediano; el polo de `ψ(s/2)` en `0` se cancela con el cero trivial).
* `rectInt_Λd_div`: `∮_R Λd(s)/(s − w) = 2πi H₁(w)` para `w` interior.
* `identidad_rect`: la identidad de arriba.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- `ψ` es holomorfa en `w` si `Re w > −1` y `w ≠ 0`. -/
theorem differentiableAt_digamma' {w : ℂ} (hw : -1 < w.re) (h0 : w ≠ 0) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hU : IsOpen {z : ℂ | -1 < z.re ∧ z ≠ 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have heq : (fun z => Complex.digamma (z + 1) - 1 / z) =ᶠ[𝓝 w] Complex.digamma := by
    filter_upwards [hU.mem_nhds ⟨hw, h0⟩] with z hz
    rw [← digamma_add_inv hz.1 hz.2]
    ring
  have hd : DifferentiableAt ℂ (fun z => Complex.digamma (z + 1) - 1 / z) w := by
    have h1 : DifferentiableAt ℂ (fun z => Complex.digamma (z + 1)) w :=
      (differentiableAt_digamma (by simp; linarith)).comp w (differentiableAt_id.add_const 1)
    exact h1.sub ((differentiableAt_const _).div differentiableAt_id h0)
  exact hd.congr_of_eventuallyEq heq.symm

variable {N : ℕ} [NeZero N]

/-- `L(·, χ)` y su derivada son holomorfas si `χ ≠ 1`. -/
theorem differentiableAt_logDeriv_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) s := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
    (hL.differentiableOn (s := univ)).analyticAt (isOpen_univ.mem_nhds (mem_univ s))
  have h := han.deriv.differentiableAt.div han.differentiableAt hs
  have he : logDeriv (DirichletCharacter.LFunction χ) =
      fun z => deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z := by
    funext z; rw [logDeriv_apply]
  rw [he]
  exact h

/-- `L'/L` es holomorfa en `s ≠ 1` con `L(s) ≠ 0` (cualquier `χ`). -/
theorem differentiableAt_logDeriv_L' (χ : DirichletCharacter ℂ N) {s : ℂ} (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := fun z hz =>
    (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := hd.analyticAt (hU.mem_nhds hs1)
  have h := han.deriv.differentiableAt.div han.differentiableAt hL
  have he : logDeriv (DirichletCharacter.LFunction χ) =
      fun z => deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z := by
    funext z; rw [logDeriv_apply]
  rw [he]; exact h

/-- `L'/L` es continua en `s ≠ 1` con `L(s) ≠ 0` (cualquier `χ`). -/
theorem continuousAt_logDeriv_L (χ : DirichletCharacter ℂ N) {s : ℂ} (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) s :=
  (differentiableAt_logDeriv_L' χ hs1 hL).continuousAt

/-- Parte holomorfa de `ψ((s + a)/2)`: `ψ((s + 2)/2)` si `χ` es par, `ψ((s + 1)/2)` si es impar. -/
def ψt (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := by
  classical exact if χ.Even then Complex.digamma ((s + 2) / 2) else Complex.digamma ((s + 1) / 2)

theorem differentiableAt_ψt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    DifferentiableAt ℂ (ψt χ) s := by
  classical
  unfold ψt
  by_cases he : χ.Even
  · simp only [he, if_true]
    exact (differentiableAt_digamma (by simp; linarith)).comp s
      ((differentiableAt_id.add_const 2).div_const 2)
  · simp only [he, if_false]
    exact (differentiableAt_digamma (by simp; linarith)).comp s
      ((differentiableAt_id.add_const 1).div_const 2)

open Classical in
/-- `ε₀ + δ₁ = [χ par]`. -/
theorem eps0_add_del1 (χ : DirichletCharacter ℂ N) :
    eps0 χ + del1 χ = if χ.Even then 1 else 0 := by
  classical
  unfold eps0 del1
  by_cases h1 : χ = 1
  · have he : χ.Even := by
      rw [h1]
      show (1 : DirichletCharacter ℂ N) (-1) = 1
      exact MulChar.one_apply isUnit_one.neg
    subst h1
    simp [he]
  · by_cases he : χ.Even <;> simp [h1, he]

/-- `ψ((s + a)/2)/2 + (ε₀ + δ₁)/s = ψt(s)/2` para `s ≠ 0` con `Re s ≥ −1/2`. -/
theorem digamma_par_add_eps0 {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : -1 / 2 ≤ s.re)
    (h0 : s ≠ 0) :
    Complex.digamma ((s + par χ) / 2) / 2 + (eps0 χ + del1 χ) / s = ψt χ s / 2 := by
  classical
  rw [eps0_add_del1]
  unfold ψt
  rcases par_spec χ with ⟨he, hpar⟩ | ⟨ho, hpar⟩
  · simp only [he, if_true, hpar, add_zero]
    have h := digamma_add_inv (w := s / 2) (by simp; linarith) (div_ne_zero h0 two_ne_zero)
    rw [show s / 2 + 1 = (s + 2) / 2 by ring] at h
    rw [← h]
    field_simp
  · simp only [ho.not_even, if_false, hpar, zero_div, add_zero]

/-- La parte regular de `Λd`. -/
def H₁ (χ : DirichletCharacter ℂ N) (H₀ : ℂ → ℂ) (s : ℂ) : ℂ :=
  H₀ s + ((Real.log (N / Real.pi) / 2 : ℝ) : ℂ) + ψt χ s / 2

theorem differentiableOn_H₁ {χ : DirichletCharacter ℂ N} {H₀ : ℂ → ℂ} {x₁ T' : ℝ}
    (hH : IsRegPart χ x₁ T' H₀) : DifferentiableOn ℂ (H₁ χ H₀) (rect (-1 / 2) x₁ (-T') T') := by
  intro s hs
  have hs' : -1 / 2 ≤ s.re := by
    simp only [rect, Complex.mem_reProdIm, Set.mem_Icc] at hs
    exact hs.1.1
  unfold H₁
  exact ((hH.1 s hs).add (differentiableWithinAt_const _)).add
    (((differentiableAt_ψt χ hs').div_const 2).differentiableWithinAt)

/-- **Parte regular de `Λd`**: `Λd = H₁ + ∑ m_ρ/(s − ρ) − δ₁/(s − 1) − δ₁/s` en el rectángulo. -/
theorem regΛd {χ : DirichletCharacter ℂ N} {H₀ : ℂ → ℂ}
    {x₁ T' : ℝ} (hH : IsRegPart χ x₁ T' H₀) {s : ℂ} (hs : s ∈ rect (-1 / 2) x₁ (-T') T')
    (hL : DirichletCharacter.LFunction χ s ≠ 0) (h1 : s ≠ 1) (h0 : s ≠ 0) :
    Λd χ s = H₁ χ H₀ s + (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / (s - ρ)) -
      del1 χ / (s - 1) - del1 χ / s := by
  have hs' : -1 / 2 ≤ s.re := by
    simp only [rect, Complex.mem_reProdIm, Set.mem_Icc] at hs
    exact hs.1.1
  have h := hH.2 s hs hL h1
  have hψ := digamma_par_add_eps0 (χ := χ) hs' h0
  have hψ' : Complex.digamma ((s + par χ) / 2) / 2 + eps0 χ / s + del1 χ / s = ψt χ s / 2 := by
    rw [← hψ]; ring
  unfold Λd H₁
  rw [h]
  linear_combination hψ'

/-! ### La integral sobre el borde -/

theorem contBorde_of_continuousOn {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ContinuousOn f (rect x₀ x₁ y₀ y₁)) : ContBorde f x₀ x₁ y₀ y₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.comp (by fun_prop) fun t ht => mem_rect_iff'.2 ⟨ht, le_rfl, hy⟩
  · exact h.comp (by fun_prop) fun t ht => mem_rect_iff'.2 ⟨ht, hy, le_rfl⟩
  · exact h.comp (by fun_prop) fun t ht => mem_rect_iff'.2 ⟨⟨hx, le_rfl⟩, ht⟩
  · exact h.comp (by fun_prop) fun t ht => mem_rect_iff'.2 ⟨⟨le_rfl, hx⟩, ht⟩

theorem ContBorde.mul {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hf : ContBorde f x₀ x₁ y₀ y₁)
    (hg : ContBorde g x₀ x₁ y₀ y₁) : ContBorde (fun s => f s * g s) x₀ x₁ y₀ y₁ :=
  ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.1.mul hg.2.2.1, hf.2.2.2.mul hg.2.2.2⟩

theorem contBorde_inv {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {w : ℂ} (h1 : x₀ < w.re)
    (h2 : w.re < x₁) (h3 : y₀ < w.im) (h4 : w.im < y₁) :
    ContBorde (fun s => 1 / (s - w)) x₀ x₁ y₀ y₁ :=
  contBorde_of_continuousAt hx hy fun s hs =>
    continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr (ne_of_enBorde hs h1 h2 h3 h4))

/-- En el borde de `[−1/2, 3/2] × [−T', T']` no hay ceros de `L`, ni `0` ni `1`. -/
theorem borde_buenos (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    {T' : ℝ} (hT' : 0 < T') (hno : NoOrdinate χ T') {s : ℂ}
    (hs : EnBorde (-1 / 2) (3 / 2) (-T') T' s) :
    DirichletCharacter.LFunction χ s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 0 := by
  have hr := mem_rect_iff'.1 (show ((s.re : ℂ) + s.im * I) ∈ rect (-1 / 2) (3 / 2) (-T') T' by
    rw [Complex.re_add_im]; exact hs.1)
  have h1 : s ≠ 1 := by
    rintro rfl
    rcases hs.2 with e | e | e | e <;> norm_num at e <;> linarith
  have h0 : s ≠ 0 := by
    rintro rfl
    rcases hs.2 with e | e | e | e <;> norm_num at e <;> linarith
  refine ⟨fun hL => ?_, h1, h0⟩
  rcases hZL N χ hp s (by linarith [hr.1.1]) h1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
  · rcases hs.2 with e | e | e | e
    · linarith [h.1]
    · linarith [h.2]
    · exact hno s h.1 h.2 hL (by rw [e, abs_neg, abs_of_pos hT'])
    · exact hno s h.1 h.2 hL (by rw [e, abs_of_pos hT'])
  · exact h0 h
  · rw [h] at hr; norm_num at hr

/-- Los ceros de `ZerosBelow χ T'` son interiores al rectángulo. -/
theorem cero_interior {χ : DirichletCharacter ℂ N} {T' : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow χ T') :
    -1 / 2 < ρ.re ∧ ρ.re < 3 / 2 ∧ -T' < ρ.im ∧ ρ.im < T' := by
  obtain ⟨h0, h1, him, -⟩ := hρ
  rw [abs_lt] at him
  exact ⟨by linarith, by linarith, him.1, him.2⟩

/-- `Λd` es continua en los puntos del borde. -/
theorem continuousAt_Λd (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {T' : ℝ} (hT' : 0 < T') (hno : NoOrdinate χ T') {s : ℂ}
    (hs : EnBorde (-1 / 2) (3 / 2) (-T') T' s) : ContinuousAt (Λd χ) s := by
  obtain ⟨hL, hs1, h0⟩ := borde_buenos hZL hp hT' hno hs
  have hr := mem_rect_iff'.1 (show ((s.re : ℂ) + s.im * I) ∈ rect (-1 / 2) (3 / 2) (-T') T' by
    rw [Complex.re_add_im]; exact hs.1)
  have hw0 : (s + par χ) / 2 ≠ 0 := by
    intro h
    have hs' : s = -par χ := by linear_combination 2 * h
    rcases par_spec χ with ⟨-, hpar⟩ | ⟨-, hpar⟩ <;> rw [hpar] at hs'
    · exact h0 (by simpa using hs')
    · rw [hs'] at hr; norm_num at hr
  have hwre : -1 < ((s + par χ) / 2).re := by
    have := (par_re_nonneg χ).1
    simp only [Complex.div_ofNat_re, Complex.add_re]
    linarith [hr.1.1]
  have hc1 : ContinuousAt (fun z : ℂ => (z + par χ) / 2) s := by fun_prop
  have hd' : ContinuousAt (fun z => Complex.digamma ((z + par χ) / 2)) s :=
    ContinuousAt.comp (f := fun z : ℂ => (z + par χ) / 2) (g := Complex.digamma)
      (differentiableAt_digamma' hwre hw0).continuousAt hc1
  have hd : ContinuousAt (fun z => Complex.digamma ((z + par χ) / 2) / 2) s := hd'.div_const 2
  have hl : ContinuousAt (logDeriv (DirichletCharacter.LFunction χ)) s :=
    continuousAt_logDeriv_L χ hs1 hL
  exact (continuousAt_const.add hd).add hl

/-- `∮ Λd(s)/(s − w) = 2πi H₁(w)` para `w` interior que no es cero de `L`, ni `0`, ni `1`. -/
theorem rectInt_Λd_div (hC : RectCauchy) (hZL : ZeroLocus)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {H₀ : ℂ → ℂ} {T' : ℝ} (hT' : 0 < T')
    (hno : NoOrdinate χ T') (hH : IsRegPart χ (3 / 2) T' H₀) (hfin : (ZerosBelow χ T').Finite)
    {w : ℂ} (h1 : -1 / 2 < w.re) (h2 : w.re < 3 / 2) (h3 : -T' < w.im) (h4 : w.im < T')
    (hLw : DirichletCharacter.LFunction χ w ≠ 0) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    rectInt (fun s => Λd χ s / (s - w)) (-1 / 2) (3 / 2) (-T') T' =
      2 * Real.pi * I * H₁ χ H₀ w := by
  have hx : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hy : -T' ≤ T' := by linarith
  set Zf := hfin.toFinset with hZf
  have hcong : rectInt (fun s => Λd χ s / (s - w)) (-1 / 2) (3 / 2) (-T') T' =
      rectInt (fun s => H₁ χ H₀ s * (1 / (s - w)) +
        ((∑ ρ ∈ Zf, (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w)))) -
          (del1 χ * (1 / ((s - 1) * (s - w))) + del1 χ * (1 / ((s - 0) * (s - w))))))
        (-1 / 2) (3 / 2) (-T') T' := by
    refine rectInt_congr hx hy fun s hs => ?_
    obtain ⟨hL, hs1, hs0⟩ := borde_buenos hZL hp hT' hno hs
    have hsw : s - w ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs h1 h2 h3 h4)
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [regΛd hH hs.1 hL hs1 hs0, finsum_mem_eq_finite_toFinset_sum _ hfin, sub_zero]
    have e : (∑ ρ ∈ Zf, (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w)))) =
        (∑ ρ ∈ Zf, (mult χ ρ : ℂ) / (s - ρ)) / (s - w) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [div_div, mul_one_div]
    rw [e]
    field_simp
    ring
  have hcH : ContBorde (fun s => H₁ χ H₀ s * (1 / (s - w))) (-1 / 2) (3 / 2) (-T') T' :=
    (contBorde_of_continuousOn hx hy (differentiableOn_H₁ hH).continuousOn).mul
      (contBorde_inv hx hy h1 h2 h3 h4)
  have hcq : ∀ q : ℂ, -1 / 2 < q.re → q.re < 3 / 2 → -T' < q.im → q.im < T' →
      ContBorde (fun s => 1 / ((s - q) * (s - w))) (-1 / 2) (3 / 2) (-T') T' := by
    intro q g1 g2 g3 g4
    refine contBorde_of_continuousAt hx hy fun s hs => ?_
    have a : s - q ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs g1 g2 g3 g4)
    have b : s - w ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs h1 h2 h3 h4)
    exact continuousAt_const.div
      ((continuousAt_id.sub continuousAt_const).mul (continuousAt_id.sub continuousAt_const))
      (mul_ne_zero a b)
  have hcρ : ∀ ρ ∈ Zf, ContBorde (fun s => (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨g1, g2, g3, g4⟩ := cero_interior hρ
    exact (hcq ρ g1 g2 g3 g4).const_mul _
  have hcS : ContBorde (fun s => ∑ ρ ∈ Zf, (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' := by
    have : ∀ (Z : Finset ℂ), (∀ ρ ∈ Z, ContBorde (fun s => (mult χ ρ : ℂ) *
        (1 / ((s - ρ) * (s - w)))) (-1 / 2) (3 / 2) (-T') T') →
        ContBorde (fun s => ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w))))
          (-1 / 2) (3 / 2) (-T') T' := by
      intro Z
      classical
      induction Z using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact ⟨continuousOn_const, continuousOn_const, continuousOn_const, continuousOn_const⟩
      | insert a Z ha ih =>
        intro hZ
        have := (hZ a (Finset.mem_insert_self _ _)).add
          (ih fun ρ hρ => hZ ρ (Finset.mem_insert_of_mem hρ))
        simpa [Finset.sum_insert ha] using this
    exact this Zf hcρ
  have z1 : -1 / 2 < (0 : ℂ).re := by rw [Complex.zero_re]; norm_num
  have z2 : (0 : ℂ).re < 3 / 2 := by rw [Complex.zero_re]; norm_num
  have z3 : -T' < (0 : ℂ).im := by rw [Complex.zero_im]; linarith
  have z4 : (0 : ℂ).im < T' := by rw [Complex.zero_im]; linarith
  have u1 : -1 / 2 < (1 : ℂ).re := by rw [Complex.one_re]; norm_num
  have u2 : (1 : ℂ).re < 3 / 2 := by rw [Complex.one_re]; norm_num
  have u3 : -T' < (1 : ℂ).im := by rw [Complex.one_im]; linarith
  have u4 : (1 : ℂ).im < T' := by rw [Complex.one_im]; linarith
  have hc1 := (hcq 1 u1 u2 u3 u4).const_mul (del1 χ)
  have hc0 := (hcq 0 z1 z2 z3 z4).const_mul (del1 χ)
  rw [hcong, rectInt_add hx hy hcH (hcS.sub (hc1.add hc0)),
    rectInt_sub hx hy hcS (hc1.add hc0), rectInt_add hx hy hc1 hc0,
    rectInt_sum Zf hx hy hcρ, rectInt_const_mul, rectInt_const_mul,
    rectInt_inv_mul_inv hC hx hy (fun e => hw1 e.symm) h1 h2 h3 h4 u1 u2 u3 u4,
    rectInt_inv_mul_inv hC hx hy (fun e => hw0 e.symm) h1 h2 h3 h4 z1 z2 z3 z4]
  have hz : ∀ ρ ∈ Zf, rectInt (fun s => (mult χ ρ : ℂ) * (1 / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' = 0 := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨g1, g2, g3, g4⟩ := cero_interior hρ
    have hρw : ρ ≠ w := by
      rintro rfl
      exact hLw hρ.2.2.2
    rw [rectInt_const_mul, rectInt_inv_mul_inv hC hx hy hρw h1 h2 h3 h4 g1 g2 g3 g4, mul_zero]
  rw [Finset.sum_eq_zero hz]
  simp only [mul_zero, add_zero, sub_zero]
  have hc := hC (-1 / 2) (3 / 2) (-T') T' (H₁ χ H₀) w h1 h2 h3 h4 (differentiableOn_H₁ hH)
  rw [← hc]
  congr 1
  funext s
  exact (div_eq_mul_one_div _ _).symm

/-- El núcleo `G(s) = 1/(s − (1 − σ)) − 1/(s − σ)`. -/
def G (σ : ℝ) (s : ℂ) : ℂ := 1 / (s - (1 - σ : ℝ)) - 1 / (s - σ)

/-- `L(1 − σ, χ) ≠ 0` para `1 < σ < 3/2`. -/
theorem L_uno_menos_ne (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) :
    DirichletCharacter.LFunction χ ((1 - σ : ℝ) : ℂ) ≠ 0 := by
  intro hL
  have hne1 : ((1 - σ : ℝ) : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rcases hZL N χ hp _ (by simp; linarith) hne1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
  · simp at h; linarith [h.1]
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

theorem L_sigma_ne (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ1 : 1 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (Or.inr (fun h => by have := congrArg Complex.re h; simp at this; linarith)) (by simp; linarith)

/-- **Identidad de Hadamard en el rectángulo.** -/
theorem identidad_rect (hC : RectCauchy) (hZL : ZeroLocus) (hR : ReflexionLogDeriv)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {H₀ : ℂ → ℂ} {T' : ℝ} (hT' : 0 < T')
    (hno : NoOrdinate χ T') (hH : IsRegPart χ (3 / 2) T' H₀) (hfin : (ZerosBelow χ T').Finite)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2) :
    ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ)) =
      Λd χ σ + Λd χ⁻¹ σ + rectInt (fun s => Λd χ s * G σ s) (-1 / 2) (3 / 2) (-T') T' /
        (2 * Real.pi * I) + del1 χ * (2 / σ + 2 / (σ - 1)) := by
  have hx : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hy : -T' ≤ T' := by linarith
  set w₁ : ℂ := ((1 - σ : ℝ) : ℂ) with hw₁
  set w₂ : ℂ := (σ : ℂ) with hw₂
  have hcΛ : ∀ w : ℂ, -1 / 2 < w.re → w.re < 3 / 2 → -T' < w.im → w.im < T' →
      ContBorde (fun s => Λd χ s / (s - w)) (-1 / 2) (3 / 2) (-T') T' := by
    intro w a1 a2 a3 a4
    exact contBorde_of_continuousAt hx hy fun s hs =>
      (continuousAt_Λd hZL hp hT' hno hs).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (ne_of_enBorde hs a1 a2 a3 a4))
  have e1 : -1 / 2 < w₁.re := by simp [hw₁]; linarith
  have e2 : w₁.re < 3 / 2 := by simp [hw₁]; linarith
  have e3 : -T' < w₁.im := by simp [hw₁]; linarith
  have e4 : w₁.im < T' := by simp [hw₁]; linarith
  have f1 : -1 / 2 < w₂.re := by simp [hw₂]; linarith
  have f2 : w₂.re < 3 / 2 := by simp [hw₂]; linarith
  have f3 : -T' < w₂.im := by simp [hw₂]; linarith
  have f4 : w₂.im < T' := by simp [hw₂]; linarith
  have hL1 := L_uno_menos_ne hZL hp hσ1 hσ2
  have hL2 := L_sigma_ne χ hσ1
  have hG : rectInt (fun s => Λd χ s * G σ s) (-1 / 2) (3 / 2) (-T') T' =
      rectInt (fun s => Λd χ s / (s - w₁)) (-1 / 2) (3 / 2) (-T') T' -
        rectInt (fun s => Λd χ s / (s - w₂)) (-1 / 2) (3 / 2) (-T') T' := by
    rw [← rectInt_sub hx hy (hcΛ w₁ e1 e2 e3 e4) (hcΛ w₂ f1 f2 f3 f4)]
    refine rectInt_congr hx hy fun s _ => ?_
    unfold G
    rw [hw₁, hw₂]
    ring
  have hw₁1 : w₁ ≠ 1 := by intro h; have := congrArg Complex.re h; simp [hw₁] at this; linarith
  have hw₁0 : w₁ ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hw₁] at this; linarith
  have hw₂1 : w₂ ≠ 1 := by intro h; have := congrArg Complex.re h; simp [hw₂] at this; linarith
  have hw₂0 : w₂ ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hw₂] at this; linarith
  rw [hG, rectInt_Λd_div hC hZL hp hT' hno hH hfin e1 e2 e3 e4 hL1 hw₁0 hw₁1,
    rectInt_Λd_div hC hZL hp hT' hno hH hfin f1 f2 f3 f4 hL2 hw₂0 hw₂1]
  -- valores de `H₁` en `w₁` y `w₂`
  have hr1 : w₁ ∈ rect (-1 / 2) (3 / 2) (-T') T' := by
    rw [show w₁ = ((w₁.re : ℝ) : ℂ) + (w₁.im : ℝ) * I from (Complex.re_add_im w₁).symm]
    exact mem_rect_iff'.2 ⟨⟨e1.le, e2.le⟩, ⟨e3.le, e4.le⟩⟩
  have hr2 : w₂ ∈ rect (-1 / 2) (3 / 2) (-T') T' := by
    rw [show w₂ = ((w₂.re : ℝ) : ℂ) + (w₂.im : ℝ) * I from (Complex.re_add_im w₂).symm]
    exact mem_rect_iff'.2 ⟨⟨f1.le, f2.le⟩, ⟨f3.le, f4.le⟩⟩
  have hv1 := regΛd hH hr1 hL1 hw₁1 hw₁0
  have hv2 := regΛd hH hr2 hL2 hw₂1 hw₂0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hv1 hv2
  -- reflexión en `w₁`
  have href : Λd χ w₁ = -Λd χ⁻¹ σ := by
    have h1 : ∀ n : ℕ, (w₁ + par χ) / 2 ≠ -(n : ℂ) := by
      intro n h
      have hre := congrArg Complex.re h
      have hpar := par_re_nonneg χ
      simp [hw₁] at hre
      rcases par_spec χ with ⟨-, hp0⟩ | ⟨-, hp1⟩
      · rw [hp0] at hre; simp at hre
        rcases n with _ | n
        · simp at hre; linarith
        · push_cast at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · rw [hp1] at hre; simp at hre
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : ∀ n : ℕ, (1 - w₁ + par χ) / 2 ≠ -(n : ℂ) := by
      intro n h
      have hre := congrArg Complex.re h
      have hpar := par_re_nonneg χ
      simp [hw₁] at hre
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h4 : DirichletCharacter.LFunction χ⁻¹ (1 - w₁) ≠ 0 := by
      have : (1 : ℂ) - w₁ = (σ : ℂ) := by rw [hw₁]; push_cast; ring
      rw [this]
      exact L_sigma_ne χ⁻¹ hσ1
    have := reflexion_gen hR hp h1 h2 hL1 h4
    rw [this]
    congr 2
    rw [hw₁]; push_cast; ring
  have h2π : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  rw [← mul_sub, mul_div_cancel_left₀ _ h2π]
  have hsplit : ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ)) =
      (∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) / (w₂ - ρ)) -
        ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) / (w₁ - ρ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hw₁, hw₂]
    ring
  rw [hsplit]
  have hH1 : H₁ χ H₀ w₁ = Λd χ w₁ - ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) / (w₁ - ρ) +
      del1 χ / (w₁ - 1) + del1 χ / w₁ := by
    rw [hv1]; ring
  have hH2 : H₁ χ H₀ w₂ = Λd χ w₂ - ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) / (w₂ - ρ) +
      del1 χ / (w₂ - 1) + del1 χ / w₂ := by
    rw [hv2]; ring
  rw [hH1, hH2, href]
  have a1 : w₁ - 1 = -(σ : ℂ) := by rw [hw₁]; push_cast; ring
  have a2 : w₁ = 1 - (σ : ℂ) := by rw [hw₁]; push_cast; ring
  rw [a1, a2, hw₂]
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < σ by linarith).ne'
  have hσ1' : (σ : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hσ1'' : (1 : ℂ) - σ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [div_neg, show (1 : ℂ) - σ = -((σ : ℂ) - 1) by ring, div_neg]
  field_simp
  ring

end AMate.Miller.Hadamard
