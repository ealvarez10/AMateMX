import AMateMiller.Perron
import AMateMiller.HadamardVertical

/-!
# Fórmula explícita ponderada: el lado derecho

Para `x > 0` y `0 < α < β`, con el núcleo `K(s) = x^s/((s + α)(s + β))` y el peso
`w(m) = ((m/x)^α − (m/x)^β)/(β − α)` para `m < x` (y `0` si `m ≥ x`):

  `(1/2π) ∫ −L'/L(3/2 + it, χ) K(3/2 + it) dt = S(x) = ∑_{m ≤ x} Λ(m) χ(m) w(m)`

(`perron_L`). Se desarrolla `−L'/L` en serie de Dirichlet, se intercambia con la integral y en
cada término se aplica `Perron.perron`.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF

noncomputable section

namespace AMate.Miller.Ponderada

open AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- El núcleo `K(s) = x^s/((s + α)(s + β))`. -/
def K (x α β : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / ((s + α) * (s + β))

/-- El peso `w(m) = [m < x]((m/x)^α − (m/x)^β)/(β − α)`. -/
def w (x α β : ℝ) (m : ℕ) : ℝ :=
  if (m : ℝ) < x then (((m : ℝ) / x) ^ α - ((m : ℝ) / x) ^ β) / (β - α) else 0

variable {N : ℕ} [NeZero N]

/-- La suma ponderada `S(x) = ∑_{1 ≤ m ≤ x} Λ(m) χ(m) w(m)`. -/
def S (χ : DirichletCharacter ℂ N) (x α β : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod N) * (w x α β m : ℂ)

/-- `x^s / n^s = (x/n)^s` para reales positivos. -/
theorem cpow_div_cpow {x n : ℝ} (hx : 0 < x) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ s / (n : ℂ) ^ s = ((x / n : ℝ) : ℂ) ^ s := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hxn0 : ((x / n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx hn).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hxn0, ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hn.le,
    ← Complex.ofReal_log (div_pos hx hn).le, Real.log_div hx.ne' hn.ne', ← Complex.exp_sub]
  push_cast
  ring_nf

/-- El peso como valor del núcleo de Perron. -/
theorem w_eq_perron {x α β : ℝ} (hx : 0 < x) (hα : 0 < 3 / 2 + α) (hβ : 0 < 3 / 2 + β)
    (hab : α ≠ β) {m : ℕ} (hm : 1 ≤ m) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ((x / m : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * I) /
        ((((3 / 2 : ℝ) : ℂ) + t * I + α) * (((3 / 2 : ℝ) : ℂ) + t * I + β)) = (w x α β m : ℂ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Perron.perron hα hβ hab (div_pos hx hm0)]
  unfold w
  have hiff : 1 < x / m ↔ (m : ℝ) < x := by rw [one_lt_div hm0]
  by_cases h : (m : ℝ) < x
  · rw [if_pos (hiff.mpr h), if_pos h]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), ← Real.inv_rpow (by positivity), inv_div]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    simp

/-- `g(t) = 1/(|a + it||b + it|)` es integrable para `a, b > 0`. -/
theorem integrable_g {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable fun t : ℝ => 1 / (‖(a : ℂ) + t * I‖ * ‖(b : ℂ) + t * I‖) := by
  set m : ℝ := min a 1 * min b 1 / 4 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hdom : Integrable (fun t : ℝ => m⁻¹ * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  have hpos : ∀ (c : ℝ), 0 < c → ∀ t : ℝ, 0 < ‖(c : ℂ) + t * I‖ := by
    intro c hc t
    rw [norm_pos_iff]
    intro h; have := congrArg Complex.re h; simp at this; linarith
  refine hdom.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t =>
      (mul_pos (hpos a ha t) (hpos b hb t)).ne').aestronglyMeasurable
  · have h1 := Perron.norm_add_mul_I_ge ha t
    have h2 := Perron.norm_add_mul_I_ge hb t
    have hpt : 0 < 1 + |t| := by positivity
    have hprod : m * (1 + |t|) ^ 2 ≤ ‖(a : ℂ) + t * I‖ * ‖(b : ℂ) + t * I‖ := by
      have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
      rw [hm]; nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      div_le_iff₀ (mul_pos (hpos a ha t) (hpos b hb t))]
    have e : m⁻¹ * (1 + |t|) ^ (-(2 : ℝ)) * (m * (1 + |t|) ^ 2) = 1 := by
      rw [Real.rpow_neg hpt.le, Real.rpow_two]; field_simp
    calc (1 : ℝ) = m⁻¹ * (1 + |t|) ^ (-(2 : ℝ)) * (m * (1 + |t|) ^ 2) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- Norma de `y^{c+it}/((c + it + α)(c + it + β))`. -/
theorem norm_kernel {y c α β : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖(y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I + α) * ((c : ℂ) + t * I + β))‖ =
      y ^ c * (1 / (‖((c + α : ℝ) : ℂ) + t * I‖ * ‖((c + β : ℝ) : ℂ) + t * I‖)) := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
  push_cast
  rw [show (c : ℂ) + t * I + α = (c : ℂ) + α + t * I by ring,
    show (c : ℂ) + t * I + β = (c : ℂ) + β + t * I by ring]
  ring

theorem integrable_kernel {y c α β : ℝ} (hy : 0 < y) (ha : 0 < c + α) (hb : 0 < c + β) :
    Integrable fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I + α) * ((c : ℂ) + t * I + β)) := by
  have hne : ∀ (d : ℝ), 0 < c + d → ∀ t : ℝ, (c : ℂ) + t * I + d ≠ 0 := by
    intro d hd t h; have := congrArg Complex.re h; simp at this; linarith
  have hcont : Continuous fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I + α) * ((c : ℂ) + t * I + β)) := by
    refine Continuous.div ?_ (by fun_prop) fun t => mul_ne_zero (hne α ha t) (hne β hb t)
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))
  refine ((integrable_g ha hb).const_mul (y ^ c)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_kernel hy t]

/-- **Perron para `L'/L`**: `(1/2π) ∫ −L'/L(3/2 + it) K(3/2 + it) dt = S(x)`. -/
theorem perron_L (χ : DirichletCharacter ℂ N) {x α β : ℝ} (hx : 0 < x) (hα : 0 < α)
    (hαβ : α < β) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, -logDeriv (DirichletCharacter.LFunction χ)
        (((3 / 2 : ℝ) : ℂ) + t * I) * K x α β (((3 / 2 : ℝ) : ℂ) + t * I) = S χ x α β := by
  set f : ℕ → ℂ := fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ) with hf
  set sl : ℝ → ℂ := fun t => ((3 / 2 : ℝ) : ℂ) + t * I with hsl
  have hre : ∀ t, 1 < (sl t).re := fun t => by simp [hsl]; norm_num
  have ha : 0 < (3 / 2 : ℝ) + α := by linarith
  have hb : 0 < (3 / 2 : ℝ) + β := by linarith
  set F : ℕ → ℝ → ℂ := fun n t => LSeries.term f (sl t) n * K x α β (sl t) with hF
  -- el integrando es la suma de los `F n`
  have hsum : ∀ t, -logDeriv (DirichletCharacter.LFunction χ) (sl t) * K x α β (sl t) =
      ∑' n, F n t := by
    intro t
    rw [logDeriv_eq_neg_LSeries χ (hre t), neg_neg]
    exact (tsum_mul_right).symm
  -- cada `F n` es `f n` por el núcleo de Perron en `x/n`
  have hFn : ∀ n : ℕ, 1 ≤ n → ∀ t, F n t = f n * (((x / n : ℝ) : ℂ) ^ (sl t) /
      ((sl t + α) * (sl t + β))) := by
    intro n hn t
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hF, K, LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    rw [← cpow_div_cpow hx hn0]
    push_cast
    ring
  have hF0 : ∀ t, F 0 t = 0 := fun t => by simp [hF, LSeries.term_zero]
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : F 0 = fun _ => 0 := funext hF0
      rw [this]; exact integrable_zero _ _ _
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have := (integrable_kernel (c := 3 / 2) (div_pos hx hn0) ha hb).const_mul (f n)
      refine this.congr (Eventually.of_forall fun t => ?_)
      rw [hFn n hn t]
  -- sumabilidad de las normas
  set Ig : ℝ := ∫ t : ℝ, 1 / (‖(((3 / 2 + α : ℝ)) : ℂ) + t * I‖ * ‖(((3 / 2 + β : ℝ)) : ℂ) + t * I‖)
    with hIg
  have hnormF : ∀ n, ∫ t, ‖F n t‖ ≤ x ^ (3 / 2 : ℝ) * Ig *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp_rw [hF0, norm_zero, integral_zero]; simp [LSeries.term_zero]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have heq : ∀ t, ‖F n t‖ = ‖f n‖ * ((x / n) ^ (3 / 2 : ℝ) *
          (1 / (‖(((3 / 2 + α : ℝ)) : ℂ) + t * I‖ * ‖(((3 / 2 + β : ℝ)) : ℂ) + t * I‖))) := by
        intro t
        rw [hFn n hn t, norm_mul, norm_kernel (div_pos hx hn0) t]
      simp_rw [heq]
      rw [integral_const_mul, integral_const_mul]
      have hfn : ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n := by
        rw [hf]; simp only [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (DirichletCharacter.norm_le_one χ _)
      have hIg0 : 0 ≤ Ig := integral_nonneg fun t => by positivity
      rw [LSeries.norm_term_eq, if_neg (by omega)]
      simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [Real.div_rpow hx.le hn0.le]
      have : ‖f n‖ * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) * Ig) ≤
          ArithmeticFunction.vonMangoldt n * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) * Ig) :=
        mul_le_mul_of_nonneg_right hfn (by positivity)
      calc _ = ‖f n‖ * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) * Ig) := by ring
        _ ≤ _ := this
        _ = _ := by ring
  have hsumm : Summable fun n => ∫ t, ‖F n t‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hnormF
      ((summable_VM (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left _)
  -- intercambio de suma e integral
  have hint : ∫ t, -logDeriv (DirichletCharacter.LFunction χ) (sl t) * K x α β (sl t) =
      ∑' n, ∫ t, F n t := by
    simp_rw [hsum]
    exact (integral_tsum_of_summable_integral_norm hFi hsumm).symm
  have hval : ∀ n, (1 / (2 * Real.pi) : ℂ) * ∫ t, F n t =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) * (w x α β n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp_rw [hF0, integral_zero]; simp
    · rw [show (fun t => F n t) = fun t => f n * (((x / n : ℝ) : ℂ) ^ (sl t) /
          ((sl t + α) * (sl t + β))) from funext (hFn n hn), integral_const_mul,
        mul_left_comm, w_eq_perron hx ha hb hαβ.ne hn]
      rw [hf]; ring
  show (1 / (2 * Real.pi) : ℂ) * ∫ t, -logDeriv (DirichletCharacter.LFunction χ) (sl t) *
    K x α β (sl t) = S χ x α β
  rw [hint, ← tsum_mul_left]
  simp_rw [hval]
  unfold S
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  intro n hn
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with h | h
  · have : n = 0 := by omega
    subst this; simp
  · have : ¬ ((n : ℝ) < x) := by
      intro h'
      apply h
      exact Nat.le_floor h'.le
    simp [w, this]

end AMate.Miller.Ponderada
