import AMateMiller.HipotesisAnaliticas
import AMateMiller.Desplazamiento
import AMateMiller.CotaBach

/-!
# Preliminares para la cota de Hadamard

* `differentiableAt_digamma`: `ψ` es holomorfa en `Re w > 0`.
* `par χ ∈ {0, 1}`: la paridad de `χ`; `χ⁻¹` tiene la misma.
* `Λd χ s = ½ log(N/π) + ½ ψ((s + a)/2) + L'/L(s, χ)`: derivada logarítmica de la función `L`
  completada, y `reflexion`: `Λd(s, χ) = −Λd(1 − s, χ⁻¹)` (de `ReflexionLogDeriv`).
* `ContBorde`, `rectInt_add`, …: linealidad de la integral sobre el borde de un rectángulo para
  funciones continuas en el borde.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Hadamard

/-! ### Digamma -/

theorem ne_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem differentiableAt_digamma {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hΓ : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (ne_neg_nat_of_re_pos hz)).differentiableWithinAt
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have han : AnalyticAt ℂ Complex.Gamma w := hΓ.analyticAt (hopen.mem_nhds hw)
  have h := han.deriv.differentiableAt.div han.differentiableAt
    (Complex.Gamma_ne_zero_of_re_pos hw)
  have he : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z; rw [Complex.digamma_def, logDeriv_apply]
  rw [he]
  exact h

/-- `ψ(w) + 1/w = ψ(w + 1)` para `Re w > −1`, `w ≠ 0`. -/
theorem digamma_add_inv {w : ℂ} (hw : -1 < w.re) (h0 : w ≠ 0) :
    Complex.digamma w + 1 / w = Complex.digamma (w + 1) := by
  have h' : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hm
    rcases m with _ | m
    · exact h0 (by simpa using hm)
    · have := congrArg Complex.re hm
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [Complex.digamma_apply_add_one w h', one_div]

/-! ### Paridad -/

variable {N : ℕ} [NeZero N]

set_option linter.unusedSectionVars false

/-- Paridad de `χ`: `0` si es par, `1` si es impar. -/
def par (χ : DirichletCharacter ℂ N) : ℂ := by
  classical exact if χ.Even then 0 else 1

theorem par_spec (χ : DirichletCharacter ℂ N) :
    (χ.Even ∧ par χ = 0) ∨ (χ.Odd ∧ par χ = 1) := by
  classical
  rcases χ.even_or_odd with h | h
  · left; exact ⟨h, by simp [par, h]⟩
  · right; exact ⟨h, by simp [par, h.not_even]⟩

theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = (χ (-1))⁻¹ :=
  MulChar.inv_apply_eq_inv' χ (-1)

theorem even_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [inv_apply_neg_one]
  constructor
  · intro h; rwa [inv_eq_one] at h
  · intro h; rw [h, inv_one]

theorem par_inv (χ : DirichletCharacter ℂ N) : par χ⁻¹ = par χ := by
  classical
  unfold par
  simp only [even_inv_iff]

theorem par_re_nonneg (χ : DirichletCharacter ℂ N) : 0 ≤ (par χ).re ∧ (par χ).re ≤ 1 ∧
    (par χ).im = 0 := by
  rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num

theorem ne_one_of_primitive (hN : 1 < N) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) :
    χ ≠ 1 := by
  intro h
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
  omega

theorem isPrimitive_inv {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive at hp ⊢
  rw [DirichletCharacter.conductor_inv, hp]

open Classical in
theorem eps0_eq (hN : 1 < N) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) :
    eps0 χ = if χ.Even then 1 else 0 := by
  classical
  have h1 := ne_one_of_primitive hN hp
  unfold eps0
  by_cases he : χ.Even <;> simp [he, h1]

/-! ### La derivada logarítmica completada -/

/-- `Λd χ s = ½ log(N/π) + ½ ψ((s + a)/2) + L'/L(s, χ)`. -/
def Λd (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ((Real.log (N / Real.pi) / 2 : ℝ) : ℂ) + Complex.digamma ((s + par χ) / 2) / 2 +
    logDeriv (DirichletCharacter.LFunction χ) s

/-- **Reflexión**: `Λd(s, χ) = −Λd(1 − s, χ⁻¹)`. -/
theorem reflexion (hR : ReflexionLogDeriv) (hN : 1 < N) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) {s : ℂ} (h1 : ∀ n : ℕ, (s + par χ) / 2 ≠ -(n : ℂ))
    (h2 : ∀ n : ℕ, (1 - s + par χ) / 2 ≠ -(n : ℂ))
    (h3 : DirichletCharacter.LFunction χ s ≠ 0)
    (h4 : DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0) :
    Λd χ s = -Λd χ⁻¹ (1 - s) := by
  have hpar : (χ.Even ∧ par χ = 0 ∨ χ.Odd ∧ par χ = 1) := par_spec χ
  have h := hR N χ hN hp (par χ) hpar s h1 h2 h3 h4
  unfold Λd
  rw [logDeriv_apply, logDeriv_apply, h, par_inv]
  have e : (1 - s + par χ) / 2 = ((1 - s) + par χ) / 2 := by ring
  rw [e]
  push_cast
  ring

/-! ### La integral sobre el borde de un rectángulo -/

/-- Continuidad de `f` en los cuatro lados de `[x₀, x₁] × [y₀, y₁]`. -/
def ContBorde (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : Prop :=
  ContinuousOn (fun x : ℝ => f (x + y₀ * I)) (Icc x₀ x₁) ∧
  ContinuousOn (fun x : ℝ => f (x + y₁ * I)) (Icc x₀ x₁) ∧
  ContinuousOn (fun y : ℝ => f (x₁ + y * I)) (Icc y₀ y₁) ∧
  ContinuousOn (fun y : ℝ => f (x₀ + y * I)) (Icc y₀ y₁)

/-- Puntos del borde. -/
def EnBorde (x₀ x₁ y₀ y₁ : ℝ) (s : ℂ) : Prop :=
  s ∈ rect x₀ x₁ y₀ y₁ ∧ (s.re = x₀ ∨ s.re = x₁ ∨ s.im = y₀ ∨ s.im = y₁)

theorem mem_rect_iff' {x₀ x₁ y₀ y₁ x y : ℝ} :
    ((x : ℂ) + y * I) ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ x ∧ x ≤ x₁) ∧ (y₀ ≤ y ∧ y ≤ y₁) := by
  simp [rect, Complex.mem_reProdIm]

theorem contBorde_of_continuousAt {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ s, EnBorde x₀ x₁ y₀ y₁ s → ContinuousAt f s) : ContBorde f x₀ x₁ y₀ y₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro t ht <;> rw [Set.mem_Icc] at ht
  · refine (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + y₀ * I) (h _ ⟨mem_rect_iff'.2 ⟨ht, le_rfl, hy⟩, Or.inr (Or.inr (Or.inl (by simp)))⟩)
      (by fun_prop)).continuousWithinAt
  · refine (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + y₁ * I) (h _ ⟨mem_rect_iff'.2 ⟨ht, hy, le_rfl⟩, Or.inr (Or.inr (Or.inr (by simp)))⟩)
      (by fun_prop)).continuousWithinAt
  · refine (ContinuousAt.comp (f := fun y : ℝ => (x₁ : ℂ) + y * I) (h _ ⟨mem_rect_iff'.2 ⟨⟨hx, le_rfl⟩, ht⟩, Or.inr (Or.inl (by simp))⟩)
      (by fun_prop)).continuousWithinAt
  · refine (ContinuousAt.comp (f := fun y : ℝ => (x₀ : ℂ) + y * I) (h _ ⟨mem_rect_iff'.2 ⟨⟨le_rfl, hx⟩, ht⟩, Or.inl (by simp)⟩)
      (by fun_prop)).continuousWithinAt

theorem ContBorde.add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hf : ContBorde f x₀ x₁ y₀ y₁)
    (hg : ContBorde g x₀ x₁ y₀ y₁) : ContBorde (fun s => f s + g s) x₀ x₁ y₀ y₁ :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem ContBorde.sub {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hf : ContBorde f x₀ x₁ y₀ y₁)
    (hg : ContBorde g x₀ x₁ y₀ y₁) : ContBorde (fun s => f s - g s) x₀ x₁ y₀ y₁ :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, hf.2.2.1.sub hg.2.2.1, hf.2.2.2.sub hg.2.2.2⟩

theorem ContBorde.const_mul {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (c : ℂ) (hf : ContBorde f x₀ x₁ y₀ y₁) :
    ContBorde (fun s => c * f s) x₀ x₁ y₀ y₁ :=
  ⟨hf.1.const_smul c, hf.2.1.const_smul c, hf.2.2.1.const_smul c, hf.2.2.2.const_smul c⟩

theorem intervalIntegrable_of_contOn {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    IntervalIntegrable g volume a b :=
  (hg.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

theorem rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContBorde f x₀ x₁ y₀ y₁) (hg : ContBorde g x₀ x₁ y₀ y₁) :
    rectInt (fun s => f s + g s) x₀ x₁ y₀ y₁ = rectInt f x₀ x₁ y₀ y₁ + rectInt g x₀ x₁ y₀ y₁ := by
  unfold rectInt
  rw [intervalIntegral.integral_add (intervalIntegrable_of_contOn hx hf.1) (intervalIntegrable_of_contOn hx hg.1),
    intervalIntegral.integral_add (intervalIntegrable_of_contOn hx hf.2.1) (intervalIntegrable_of_contOn hx hg.2.1),
    intervalIntegral.integral_add (intervalIntegrable_of_contOn hy hf.2.2.1) (intervalIntegrable_of_contOn hy hg.2.2.1),
    intervalIntegral.integral_add (intervalIntegrable_of_contOn hy hf.2.2.2) (intervalIntegrable_of_contOn hy hg.2.2.2)]
  simp only [smul_eq_mul]
  ring

theorem rectInt_sub {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContBorde f x₀ x₁ y₀ y₁) (hg : ContBorde g x₀ x₁ y₀ y₁) :
    rectInt (fun s => f s - g s) x₀ x₁ y₀ y₁ = rectInt f x₀ x₁ y₀ y₁ - rectInt g x₀ x₁ y₀ y₁ := by
  unfold rectInt
  rw [intervalIntegral.integral_sub (intervalIntegrable_of_contOn hx hf.1) (intervalIntegrable_of_contOn hx hg.1),
    intervalIntegral.integral_sub (intervalIntegrable_of_contOn hx hf.2.1) (intervalIntegrable_of_contOn hx hg.2.1),
    intervalIntegral.integral_sub (intervalIntegrable_of_contOn hy hf.2.2.1) (intervalIntegrable_of_contOn hy hg.2.2.1),
    intervalIntegral.integral_sub (intervalIntegrable_of_contOn hy hf.2.2.2) (intervalIntegrable_of_contOn hy hg.2.2.2)]
  simp only [smul_eq_mul]
  ring

theorem rectInt_const_mul {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (c : ℂ) :
    rectInt (fun s => c * f s) x₀ x₁ y₀ y₁ = c * rectInt f x₀ x₁ y₀ y₁ := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem rectInt_sum {ι : Type*} (Z : Finset ι) {f : ι → ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁)
    (hy : y₀ ≤ y₁) (hf : ∀ i ∈ Z, ContBorde (f i) x₀ x₁ y₀ y₁) :
    rectInt (fun s => ∑ i ∈ Z, f i s) x₀ x₁ y₀ y₁ = ∑ i ∈ Z, rectInt (f i) x₀ x₁ y₀ y₁ := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp [rectInt]
  | insert a Z ha ih =>
    have hZ : ∀ i ∈ Z, ContBorde (f i) x₀ x₁ y₀ y₁ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContBorde (fun s => ∑ i ∈ Z, f i s) x₀ x₁ y₀ y₁ := by
      clear ih
      induction Z using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨continuousOn_const, continuousOn_const, continuousOn_const, continuousOn_const⟩
      | insert b Z hb ih2 =>
        have := (hZ b (Finset.mem_insert_self _ _)).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hf i ?_)
            (fun i hi => hZ i (Finset.mem_insert_of_mem hi)))
        · simpa [Finset.sum_insert hb] using this
        · rcases Finset.mem_insert.mp hi with h | h
          · exact h ▸ Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
    simp only [Finset.sum_insert ha]
    rw [rectInt_add hx hy (hf a (Finset.mem_insert_self _ _)) hsum, ih hZ]

/-- `rectInt (1/(s − w)) = 2πi` para `w` interior. -/
theorem rectInt_inv (hC : RectCauchy) {x₀ x₁ y₀ y₁ : ℝ} {w : ℂ} (h1 : x₀ < w.re) (h2 : w.re < x₁)
    (h3 : y₀ < w.im) (h4 : w.im < y₁) :
    rectInt (fun s => 1 / (s - w)) x₀ x₁ y₀ y₁ = 2 * Real.pi * I := by
  have := hC x₀ x₁ y₀ y₁ (fun _ => 1) w h1 h2 h3 h4 (differentiableOn_const 1)
  simpa using this

/-- Los puntos del borde no son puntos interiores. -/
theorem ne_of_enBorde {x₀ x₁ y₀ y₁ : ℝ} {s w : ℂ} (hs : EnBorde x₀ x₁ y₀ y₁ s) (h1 : x₀ < w.re)
    (h2 : w.re < x₁) (h3 : y₀ < w.im) (h4 : w.im < y₁) : s ≠ w := by
  rintro rfl
  rcases hs.2 with e | e | e | e <;> linarith

/-- `1/((s − ρ)(s − w))` integra `0` sobre el borde si `ρ ≠ w` son interiores. -/
theorem rectInt_inv_mul_inv (hC : RectCauchy) {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    {ρ w : ℂ} (hρw : ρ ≠ w)
    (h1 : x₀ < w.re) (h2 : w.re < x₁) (h3 : y₀ < w.im) (h4 : w.im < y₁)
    (g1 : x₀ < ρ.re) (g2 : ρ.re < x₁) (g3 : y₀ < ρ.im) (g4 : ρ.im < y₁) :
    rectInt (fun s => 1 / ((s - ρ) * (s - w))) x₀ x₁ y₀ y₁ = 0 := by
  have hρw' : ρ - w ≠ 0 := sub_ne_zero.mpr hρw
  have hcb : ∀ p : ℂ, x₀ < p.re → p.re < x₁ → y₀ < p.im → p.im < y₁ →
      ContBorde (fun s => 1 / (s - p)) x₀ x₁ y₀ y₁ := by
    intro p a1 a2 a3 a4
    refine contBorde_of_continuousAt hx hy fun s hs => ?_
    have : s - p ≠ 0 := sub_ne_zero.mpr (ne_of_enBorde hs a1 a2 a3 a4)
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) this)
  have hcong : rectInt (fun s => 1 / ((s - ρ) * (s - w))) x₀ x₁ y₀ y₁ =
      rectInt (fun s => (1 / (ρ - w)) * (1 / (s - ρ) - 1 / (s - w))) x₀ x₁ y₀ y₁ := by
    unfold rectInt
    have key : ∀ s : ℂ, s ≠ ρ → s ≠ w →
        1 / ((s - ρ) * (s - w)) = (1 / (ρ - w)) * (1 / (s - ρ) - 1 / (s - w)) := by
      intro s hs1 hs2
      have a : s - ρ ≠ 0 := sub_ne_zero.mpr hs1
      have b : s - w ≠ 0 := sub_ne_zero.mpr hs2
      field_simp
      ring
    have hb : ∀ s, EnBorde x₀ x₁ y₀ y₁ s →
        1 / ((s - ρ) * (s - w)) = (1 / (ρ - w)) * (1 / (s - ρ) - 1 / (s - w)) := fun s hs =>
      key s (ne_of_enBorde hs g1 g2 g3 g4) (ne_of_enBorde hs h1 h2 h3 h4)
    congr 1
    · congr 1
      · congr 1
        · refine intervalIntegral.integral_congr fun x hx' => ?_
          rw [Set.uIcc_of_le hx] at hx'
          exact hb _ ⟨mem_rect_iff'.2 ⟨hx', le_rfl, hy⟩, Or.inr (Or.inr (Or.inl (by simp)))⟩
        · refine intervalIntegral.integral_congr fun x hx' => ?_
          rw [Set.uIcc_of_le hx] at hx'
          exact hb _ ⟨mem_rect_iff'.2 ⟨hx', hy, le_rfl⟩, Or.inr (Or.inr (Or.inr (by simp)))⟩
      · congr 1
        refine intervalIntegral.integral_congr fun y hy' => ?_
        rw [Set.uIcc_of_le hy] at hy'
        exact hb _ ⟨mem_rect_iff'.2 ⟨⟨hx, le_rfl⟩, hy'⟩, Or.inr (Or.inl (by simp))⟩
    · congr 1
      refine intervalIntegral.integral_congr fun y hy' => ?_
      rw [Set.uIcc_of_le hy] at hy'
      exact hb _ ⟨mem_rect_iff'.2 ⟨⟨le_rfl, hx⟩, hy'⟩, Or.inl (by simp)⟩
  rw [hcong, rectInt_const_mul, rectInt_sub hx hy (hcb ρ g1 g2 g3 g4) (hcb w h1 h2 h3 h4),
    rectInt_inv hC g1 g2 g3 g4, rectInt_inv hC h1 h2 h3 h4, sub_self, mul_zero]

/-- `rectInt` solo depende de los valores en el borde. -/
theorem rectInt_congr {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ s, EnBorde x₀ x₁ y₀ y₁ s → f s = g s) :
    rectInt f x₀ x₁ y₀ y₁ = rectInt g x₀ x₁ y₀ y₁ := by
  unfold rectInt
  congr 1
  · congr 1
    · congr 1
      · refine intervalIntegral.integral_congr fun x hx' => ?_
        rw [Set.uIcc_of_le hx] at hx'
        exact h _ ⟨mem_rect_iff'.2 ⟨hx', le_rfl, hy⟩, Or.inr (Or.inr (Or.inl (by simp)))⟩
      · refine intervalIntegral.integral_congr fun x hx' => ?_
        rw [Set.uIcc_of_le hx] at hx'
        exact h _ ⟨mem_rect_iff'.2 ⟨hx', hy, le_rfl⟩, Or.inr (Or.inr (Or.inr (by simp)))⟩
    · congr 1
      refine intervalIntegral.integral_congr fun y hy' => ?_
      rw [Set.uIcc_of_le hy] at hy'
      exact h _ ⟨mem_rect_iff'.2 ⟨⟨hx, le_rfl⟩, hy'⟩, Or.inr (Or.inl (by simp))⟩
  · congr 1
    refine intervalIntegral.integral_congr fun y hy' => ?_
    rw [Set.uIcc_of_le hy] at hy'
    exact h _ ⟨mem_rect_iff'.2 ⟨⟨le_rfl, hx⟩, hy'⟩, Or.inl (by simp)⟩

end AMate.Miller.Hadamard
