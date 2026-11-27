import AMateMiller.FormulaPonderada

/-!
# Fórmula explícita ponderada: el rectángulo

Para `χ` primitivo (cualquier módulo), `x > 0`, `0 < γ < 1/2` y una altura `T'` sin ordenadas
de ceros, en `R = [−1/2, 3/2] × [−T', T']`:

  `(2πi)⁻¹ ∮_R L'/L(s) x^s/(s + γ) ds =
     L'/L(−γ) x^{−γ} + ∑_{|Im ρ| < T'} m_ρ x^ρ/(ρ + γ) + ε₀/γ − δ₁ x/(1 + γ)`   (`rect_un_polo`),

y combinando `γ = α, β` se obtiene la identidad para `K(s) = x^s/((s + α)(s + β))`
(`rect_K`).
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF

noncomputable section

namespace AMate.Miller.Ponderada

open AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- `∮ x^s/((s − p)(s − w)) = 2πi (x^p − x^w)/(p − w)` para `p ≠ w` interiores. -/
theorem rectInt_cpow_div (hC : RectCauchy) {x : ℝ} (hx : 0 < x) {x₀ x₁ y₀ y₁ : ℝ}
    (hxx : x₀ ≤ x₁) (hyy : y₀ ≤ y₁) {p w : ℂ} (hpw : p ≠ w)
    (h1 : x₀ < w.re) (h2 : w.re < x₁) (h3 : y₀ < w.im) (h4 : w.im < y₁)
    (g1 : x₀ < p.re) (g2 : p.re < x₁) (g3 : y₀ < p.im) (g4 : p.im < y₁) :
    rectInt (fun s => (x : ℂ) ^ s / ((s - p) * (s - w))) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (((x : ℂ) ^ p - (x : ℂ) ^ w) / (p - w)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd : Differentiable ℂ fun s : ℂ => (x : ℂ) ^ s := fun s =>
    (differentiableAt_id.const_cpow (Or.inl hx0))
  have hpw' : p - w ≠ 0 := sub_ne_zero.mpr hpw
  have hcb : ∀ q : ℂ, x₀ < q.re → q.re < x₁ → y₀ < q.im → q.im < y₁ →
      ContBorde (fun s => (x : ℂ) ^ s / (s - q)) x₀ x₁ y₀ y₁ := by
    intro q a1 a2 a3 a4
    exact contBorde_of_continuousAt hxx hyy fun s hs =>
      (hd s).continuousAt.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (ne_of_enBorde hs a1 a2 a3 a4))
  have hcong : rectInt (fun s => (x : ℂ) ^ s / ((s - p) * (s - w))) x₀ x₁ y₀ y₁ =
      rectInt (fun s => (1 / (p - w)) * ((x : ℂ) ^ s / (s - p) - (x : ℂ) ^ s / (s - w)))
        x₀ x₁ y₀ y₁ := by
    refine rectInt_congr hxx hyy fun s hs => ?_
    have a : s - p ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs g1 g2 g3 g4)
    have b : s - w ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs h1 h2 h3 h4)
    field_simp
    ring
  rw [hcong, rectInt_const_mul, rectInt_sub hxx hyy (hcb p g1 g2 g3 g4) (hcb w h1 h2 h3 h4),
    hC x₀ x₁ y₀ y₁ _ p g1 g2 g3 g4 (hd.differentiableOn),
    hC x₀ x₁ y₀ y₁ _ w h1 h2 h3 h4 (hd.differentiableOn)]
  field_simp

variable {N : ℕ} [NeZero N]

/-- `L(−γ) ≠ 0` para `0 < γ < 1/2`. -/
theorem L_menos_gamma_ne (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    DirichletCharacter.LFunction χ ((-γ : ℝ) : ℂ) ≠ 0 := by
  intro hL
  have hne1 : ((-γ : ℝ) : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rcases hZL N χ hp _ (by simp; linarith) hne1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
  · simp at h; linarith [h.1]
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

/-- **Un polo**: `(2πi)⁻¹ ∮ L'/L(s) x^s/(s + γ)`. -/
theorem rect_un_polo (hC : RectCauchy) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {H₀ : ℂ → ℂ} {T' : ℝ} (hT' : 0 < T') (hno : NoOrdinate χ T')
    (hH : IsRegPart χ (3 / 2) T' H₀) (hfin : (ZerosBelow χ T').Finite) {x γ : ℝ} (hx : 0 < x)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / (s + γ)))
        (-1 / 2) (3 / 2) (-T') T' =
      2 * Real.pi * I * (logDeriv (DirichletCharacter.LFunction χ) ((-γ : ℝ) : ℂ) * (x : ℂ) ^ ((-γ : ℝ) : ℂ) +
        (∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ + γ))) + eps0 χ / γ -
        del1 χ * (x / (1 + γ))) := by
  have hxx : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hyy : -T' ≤ T' := by linarith
  set w : ℂ := ((-γ : ℝ) : ℂ) with hw
  have w1 : -1 / 2 < w.re := by simp [hw]; linarith
  have w2 : w.re < 3 / 2 := by simp [hw]; linarith
  have w3 : -T' < w.im := by simp [hw]; linarith
  have w4 : w.im < T' := by simp [hw]; linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd : Differentiable ℂ fun s : ℂ => (x : ℂ) ^ s := fun s =>
    (differentiableAt_id.const_cpow (Or.inl hx0))
  set Zf := hfin.toFinset with hZf
  have hsw : ∀ s : ℂ, s + γ = s - w := fun s => by rw [hw]; push_cast; ring
  -- descomposición en el borde
  have hcong : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / (s + γ)))
        (-1 / 2) (3 / 2) (-T') T' =
      rectInt (fun s => (H₀ s * (x : ℂ) ^ s) / (s - w) +
        ((∑ ρ ∈ Zf, (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w)))) +
        (eps0 χ * ((x : ℂ) ^ s / ((s - 0) * (s - w))) -
          del1 χ * ((x : ℂ) ^ s / ((s - 1) * (s - w)))))) (-1 / 2) (3 / 2) (-T') T' := by
    refine rectInt_congr hxx hyy fun s hs => ?_
    obtain ⟨hL, hs1, hs0⟩ := borde_buenos hZL hp hT' hno hs
    have hsw' : s - w ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs w1 w2 w3 w4)
    rw [hH.2 s hs.1 hL hs1, finsum_mem_eq_finite_toFinset_sum _ hfin, hsw s]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hρ : ∀ ρ ∈ Zf, s - ρ ≠ 0 := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      obtain ⟨g1, g2, g3, g4⟩ := cero_interior hρ
      exact sub_ne_zero.mpr (ne_of_enBorde hs g1 g2 g3 g4)
    rw [← hZf]
    have e1 : ∑ ρ ∈ Zf, (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w))) =
        (∑ ρ ∈ Zf, (mult χ ρ : ℂ) / (s - ρ)) * ((x : ℂ) ^ s / (s - w)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ρ hρ' => ?_
      have := hρ ρ hρ'
      field_simp
    rw [e1, sub_zero]
    field_simp
    ring
  -- continuidad en el borde de cada pieza
  have hHx : DifferentiableOn ℂ (fun s => H₀ s * (x : ℂ) ^ s) (rect (-1 / 2) (3 / 2) (-T') T') :=
    hH.1.mul hd.differentiableOn
  have hcH : ContBorde (fun s => (H₀ s * (x : ℂ) ^ s) / (s - w)) (-1 / 2) (3 / 2) (-T') T' := by
    have h1 := (contBorde_of_continuousOn hxx hyy hHx.continuousOn).mul
      (contBorde_inv hxx hyy w1 w2 w3 w4)
    rwa [show (fun s => (H₀ s * (x : ℂ) ^ s) * (1 / (s - w))) =
      fun s => (H₀ s * (x : ℂ) ^ s) / (s - w) from funext fun s => mul_one_div _ _] at h1
  have hcq : ∀ q : ℂ, -1 / 2 < q.re → q.re < 3 / 2 → -T' < q.im → q.im < T' →
      ContBorde (fun s => (x : ℂ) ^ s / ((s - q) * (s - w))) (-1 / 2) (3 / 2) (-T') T' := by
    intro q a1 a2 a3 a4
    exact contBorde_of_continuousAt hxx hyy fun s hs =>
      (hd s).continuousAt.div ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_id.sub continuousAt_const))
        (mul_ne_zero (sub_ne_zero.mpr (ne_of_enBorde hs a1 a2 a3 a4))
          (sub_ne_zero.mpr (ne_of_enBorde hs w1 w2 w3 w4)))
  have hcρ : ∀ ρ ∈ Zf, ContBorde (fun s => (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨g1, g2, g3, g4⟩ := cero_interior hρ
    exact (hcq ρ g1 g2 g3 g4).const_mul _
  have hcS : ContBorde (fun s => ∑ ρ ∈ Zf, (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' := by
    have : ∀ (Z : Finset ℂ), (∀ ρ ∈ Z, ContBorde (fun s => (mult χ ρ : ℂ) *
        ((x : ℂ) ^ s / ((s - ρ) * (s - w)))) (-1 / 2) (3 / 2) (-T') T') →
        ContBorde (fun s => ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w))))
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
  have h0w : (0 : ℂ) ≠ w := by intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  have h1w : (1 : ℂ) ≠ w := by intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  rw [hcong, rectInt_add hxx hyy hcH (hcS.add (((hcq 0 z1 z2 z3 z4).const_mul _).sub
      ((hcq 1 u1 u2 u3 u4).const_mul _))),
    rectInt_add hxx hyy hcS (((hcq 0 z1 z2 z3 z4).const_mul _).sub ((hcq 1 u1 u2 u3 u4).const_mul _)),
    rectInt_sub hxx hyy ((hcq 0 z1 z2 z3 z4).const_mul _) ((hcq 1 u1 u2 u3 u4).const_mul _),
    rectInt_const_mul, rectInt_const_mul, rectInt_sum Zf hxx hyy hcρ,
    rectInt_cpow_div hC hx hxx hyy h0w w1 w2 w3 w4 z1 z2 z3 z4,
    rectInt_cpow_div hC hx hxx hyy h1w w1 w2 w3 w4 u1 u2 u3 u4,
    hC (-1 / 2) (3 / 2) (-T') T' _ w w1 w2 w3 w4 hHx]
  have hsumρ : ∀ ρ ∈ Zf, rectInt (fun s => (mult χ ρ : ℂ) * ((x : ℂ) ^ s / ((s - ρ) * (s - w))))
      (-1 / 2) (3 / 2) (-T') T' = 2 * Real.pi * I * ((mult χ ρ : ℂ) * (((x : ℂ) ^ ρ - (x : ℂ) ^ w) /
        (ρ - w))) := by
    intro ρ hρ
    have hρ' := hρ
    rw [Set.Finite.mem_toFinset] at hρ'
    obtain ⟨g1, g2, g3, g4⟩ := cero_interior hρ'
    have hρw : ρ ≠ w := by
      intro e; have := congrArg Complex.re e; simp [hw] at this; linarith [hρ'.1]
    rw [rectInt_const_mul, rectInt_cpow_div hC hx hxx hyy hρw w1 w2 w3 w4 g1 g2 g3 g4]
    ring
  rw [Finset.sum_congr rfl hsumρ, ← Finset.mul_sum]
  -- valor de `H₀(w)`
  have hrw : w ∈ rect (-1 / 2) (3 / 2) (-T') T' := by
    rw [show w = ((w.re : ℝ) : ℂ) + (w.im : ℝ) * I from (Complex.re_add_im w).symm]
    exact mem_rect_iff'.2 ⟨⟨w1.le, w2.le⟩, ⟨w3.le, w4.le⟩⟩
  have hw1 : w ≠ 1 := fun e => h1w e.symm
  have hLw := L_menos_gamma_ne hZL hp hγ0 hγ1
  have hreg := hH.2 w hrw hLw hw1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hreg
  have hw0 : w ≠ 0 := fun e => h0w e.symm
  have hpw : ∀ ρ ∈ Zf, ρ - w ≠ 0 := by
    intro ρ hρ e
    rw [Set.Finite.mem_toFinset] at hρ
    have := congrArg Complex.re (sub_eq_zero.mp e); simp [hw] at this; linarith [hρ.1]
  have hH0 : H₀ w = logDeriv (DirichletCharacter.LFunction χ) w -
      (∑ ρ ∈ Zf, (mult χ ρ : ℂ) / (w - ρ)) - eps0 χ / w + del1 χ / (w - 1) := by
    rw [hreg]; ring
  rw [hH0]
  have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0.ne'
  have h1γ : (1 : ℂ) + γ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have ew : w = -(γ : ℂ) := by rw [hw]; push_cast; ring
  rw [ew] at hpw ⊢
  have hsum2 : ∑ ρ ∈ Zf, (mult χ ρ : ℂ) * (((x : ℂ) ^ ρ - (x : ℂ) ^ (-(γ : ℂ))) / (ρ - -(γ : ℂ))) =
      (∑ ρ ∈ Zf, (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ + γ))) +
        (∑ ρ ∈ Zf, (mult χ ρ : ℂ) / (-(γ : ℂ) - ρ)) * (x : ℂ) ^ (-(γ : ℂ)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have h1 := hpw ρ hρ
    have h2 : -(γ : ℂ) - ρ ≠ 0 := by
      intro e; apply h1; linear_combination -e
    have h3 : ρ + γ ≠ 0 := by
      intro e; apply h1; linear_combination e
    field_simp
    ring
  rw [hsum2, Complex.cpow_one, Complex.cpow_zero]
  have h1γ' : -(γ : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h0γ : (0 : ℂ) - -(γ : ℂ) ≠ 0 := by rw [zero_sub, neg_neg]; exact hγ'
  have h1γ'' : (1 : ℂ) - -(γ : ℂ) ≠ 0 := by rw [sub_neg_eq_add]; exact h1γ
  have hnγ : -(γ : ℂ) ≠ 0 := neg_ne_zero.mpr hγ'
  set S1 := ∑ ρ ∈ Zf, (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ + γ)) with hS1
  set S2 := ∑ ρ ∈ Zf, (mult χ ρ : ℂ) / (-(γ : ℂ) - ρ) with hS2
  rw [zero_sub, neg_neg, sub_neg_eq_add, show (1 : ℂ) + γ = 1 + γ from rfl]
  rw [div_neg, show -(γ : ℂ) - 1 = -(1 + γ) by ring, div_neg]
  field_simp
  ring

/-- Los residuos en `−α` y `−β`. -/
def Res (χ : DirichletCharacter ℂ N) (x α β : ℝ) : ℂ :=
  (logDeriv (DirichletCharacter.LFunction χ) ((-α : ℝ) : ℂ) * (x : ℂ) ^ ((-α : ℝ) : ℂ) -
    logDeriv (DirichletCharacter.LFunction χ) ((-β : ℝ) : ℂ) * (x : ℂ) ^ ((-β : ℝ) : ℂ)) / (β - α)

/-- **Identidad del rectángulo para `K`**. -/
theorem rect_K (hC : RectCauchy) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {H₀ : ℂ → ℂ} {T' : ℝ} (hT' : 0 < T') (hno : NoOrdinate χ T')
    (hH : IsRegPart χ (3 / 2) T' H₀) (hfin : (ZerosBelow χ T').Finite) {x α β : ℝ} (hx : 0 < x)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) :
    rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * K x α β s)
        (-1 / 2) (3 / 2) (-T') T' / (2 * Real.pi * I) =
      Res χ x α β + (∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * K x α β ρ) + eps0 χ / (α * β) -
        del1 χ * K x α β 1 := by
  have hxx : (-1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  have hyy : -T' ≤ T' := by linarith
  have hβα : (β : ℂ) - α ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd : Differentiable ℂ fun s : ℂ => (x : ℂ) ^ s := fun s =>
    (differentiableAt_id.const_cpow (Or.inl hx0))
  have hcb : ∀ γ : ℝ, 0 < γ → γ < 1 / 2 → ContBorde (fun s =>
      logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / (s + γ))) (-1 / 2) (3 / 2) (-T') T' := by
    intro γ hγ0 hγ1
    refine contBorde_of_continuousAt hxx hyy fun s hs => ?_
    obtain ⟨hL, hs1, -⟩ := borde_buenos hZL hp hT' hno hs
    have hsγ : s + γ ≠ 0 := by
      have h := ne_of_enBorde hs (w := ((-γ : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith)
        (by simp; linarith) (by simp; linarith)
      intro e; apply h; push_cast; linear_combination e
    exact (continuousAt_logDeriv_L χ hs1 hL).mul ((hd s).continuousAt.div
      (continuousAt_id.add continuousAt_const) hsγ)
  have hcong : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * K x α β s)
      (-1 / 2) (3 / 2) (-T') T' = rectInt (fun s => (1 / ((β : ℂ) - α)) *
        (logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / (s + α)) -
          logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / (s + β))))
        (-1 / 2) (3 / 2) (-T') T' := by
    refine rectInt_congr hxx hyy fun s hs => ?_
    have h1 : s + α ≠ 0 := by
      have h := ne_of_enBorde hs (w := ((-α : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith)
        (by simp; linarith) (by simp; linarith)
      intro e; apply h; push_cast; linear_combination e
    have h2 : s + β ≠ 0 := by
      have h := ne_of_enBorde hs (w := ((-β : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith)
        (by simp; linarith) (by simp; linarith)
      intro e; apply h; push_cast; linear_combination e
    unfold K
    field_simp
    ring
  rw [hcong, rectInt_const_mul, rectInt_sub hxx hyy (hcb α hα (by linarith)) (hcb β (by linarith) hβ),
    rect_un_polo hC hZL hp hT' hno hH hfin hx hα (by linarith),
    rect_un_polo hC hZL hp hT' hno hH hfin hx (by linarith) hβ]
  have h2π : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < β by linarith).ne'
  have h1α : (1 : ℂ) + α ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1β : (1 : ℂ) + β ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsum : ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * K x α β ρ =
      (1 / ((β : ℂ) - α)) * ((∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ + α))) -
        ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ + β))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [Set.Finite.mem_toFinset] at hρ
    have a : ρ + α ≠ 0 := by intro e; have := congrArg Complex.re e; simp at this; linarith [hρ.1]
    have b : ρ + β ≠ 0 := by intro e; have := congrArg Complex.re e; simp at this; linarith [hρ.1]
    unfold K
    field_simp
    ring
  rw [hsum]
  unfold Res K
  rw [Complex.cpow_one]
  field_simp
  ring

end AMate.Miller.Ponderada
