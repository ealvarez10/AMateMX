import AMateMiller.LadoIzquierdo

/-!
# Los residuos en `−α` y `−β`

Con `α = 2/5`, `β = 9/20` y la reflexión en `s = −γ`:

  `L'/L(−γ, χ) = −log(N/π) − ½ψ((a − γ)/2) − ½ψ((1 + γ + a)/2) − L'/L(1 + γ, χ⁻¹)`,

y como `|ψ| ≤ 9` en esos cuatro puntos y `VM(1 + γ) ≤ 3`:

  `|Re Res + log(N/π)(x^{−α} − x^{−β})/(β − α)| ≤ 12 (x^{−α} + x^{−β})/(β − α)`   (`cota_res`).
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Hadamard AMate.Miller.Ponderada AMate.Miller.DigammaExp

set_option linter.unusedSectionVars false

/-- `|ψ(y)| ≤ y + 2/y` para `y > 0`. -/
theorem abs_digamma_real_le (hS : SerieDigamma) {y : ℝ} (hy : 0 < y) :
    |(Complex.digamma y).re| ≤ y + 2 / y := by
  have h1 := digamma_real_le hS hy
  have h2 := digamma_real_ge hS hy
  have h3 := Real.log_le_sub_one_of_pos hy
  have h4 : 1 - 1 / y ≤ Real.log y := by
    have := Real.one_sub_inv_le_log_of_pos hy; rwa [one_div]
  have h5 : 2 / y = 2 * (1 / y) := by ring
  have h6 : 0 < 1 / y := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- `|ψ(y)| ≤ (y + 1) + 2/(y + 1) − 1/y` para `−1 < y < 0`. -/
theorem abs_digamma_real_neg (hS : SerieDigamma) {y : ℝ} (hy1 : -1 < y) (hy0 : y < 0) :
    |(Complex.digamma y).re| ≤ (y + 1) + 2 / (y + 1) - 1 / y := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne
  have e := digamma_add_inv (w := (y : ℂ)) (by simpa using hy1) hy'
  have h := abs_digamma_real_le hS (show 0 < y + 1 by linarith)
  have e' : (Complex.digamma (y : ℂ)).re = (Complex.digamma ((y + 1 : ℝ) : ℂ)).re - 1 / y := by
    have : Complex.digamma (y : ℂ) = Complex.digamma ((y + 1 : ℝ) : ℂ) - ((1 / y : ℝ) : ℂ) := by
      push_cast; rw [← e]; ring
    rw [this, Complex.sub_re, Complex.ofReal_re]
  rw [e']
  have : 0 < -(1 / y) := by rw [neg_pos]; exact div_neg_of_pos_of_neg one_pos hy0
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `|ψ| ≤ 9` en los cuatro puntos de la reflexión (`a ∈ {0, 1}`, `γ ∈ [2/5, 9/20]`). -/
theorem abs_digamma_puntos (hS : SerieDigamma) {γ : ℝ} (hγ1 : 2 / 5 ≤ γ) (hγ2 : γ ≤ 9 / 20)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    |(Complex.digamma (((a - γ) / 2 : ℝ) : ℂ)).re| ≤ 9 ∧
      |(Complex.digamma (((1 + γ + a) / 2 : ℝ) : ℂ)).re| ≤ 9 := by
  rcases ha with rfl | rfl
  · constructor
    · have h := abs_digamma_real_neg hS (y := (0 - γ) / 2) (by linarith) (by linarith)
      refine h.trans ?_
      have hp : 0 < (0 - γ) / 2 + 1 := by linarith
      rw [show (0 - γ) / 2 + 1 = 1 - γ / 2 by ring, show (0 - γ) / 2 = -(γ / 2) by ring]
      rw [div_neg, sub_neg_eq_add, div_div_eq_mul_div]
      have h1 : 2 / (1 - γ / 2) ≤ 2 / (31 / 40) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      have h2 : 1 * 2 / γ ≤ 2 / (2 / 5) := by
        rw [one_mul]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hγ1
      norm_num at h1 h2 ⊢
      linarith
    · have h := abs_digamma_real_le hS (y := (1 + γ + 0) / 2) (by linarith)
      refine h.trans ?_
      have h2 : 2 / ((1 + γ + 0) / 2) ≤ 2 / (7 / 10) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      norm_num at h2 ⊢
      linarith
  · constructor
    · have h := abs_digamma_real_le hS (y := (1 - γ) / 2) (by linarith)
      refine h.trans ?_
      have h2 : 2 / ((1 - γ) / 2) ≤ 2 / (11 / 40) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      norm_num at h2 ⊢
      linarith
    · have h := abs_digamma_real_le hS (y := (1 + γ + 1) / 2) (by linarith)
      refine h.trans ?_
      have h2 : 2 / ((1 + γ + 1) / 2) ≤ 2 / (6 / 5) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      norm_num at h2 ⊢
      linarith

/-- `VM(1 + γ) ≤ 3` para `γ ≥ 2/5`. -/
theorem VM_le_tres (h : HipHadamard) (hS : SerieDigamma) (hG : GRHPrimitivo) {σ : ℝ}
    (hσ : 7 / 5 ≤ σ) : VM σ ≤ 3 := by
  refine (VM_anti (by norm_num) hσ).trans ?_
  have h1 := VM_le h hS hG (show (1 : ℝ) < 7 / 5 by norm_num) (by norm_num)
  have h2 : Real.log ((7 / 5 : ℝ) / 2) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h3 : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_three
    linarith
  norm_num at h1 h2 ⊢
  linarith

variable {N : ℕ} [NeZero N]

/-- `x^{−γ}` es real. -/
theorem cpow_neg_real {x : ℝ} (hx : 0 < x) (γ : ℝ) :
    (x : ℂ) ^ ((-γ : ℝ) : ℂ) = ((x ^ (-γ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow hx.le]

/-- `Re L'/L(−γ) + log(N/π)` está acotado por `9 + VM(1 + γ)`. -/
theorem re_logDeriv_menos (hR : ReflexionLogDeriv) (hS : SerieDigamma) (hZL : ZeroLocus)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {γ : ℝ} (hγ1 : 2 / 5 ≤ γ) (hγ2 : γ ≤ 9 / 20) :
    |(logDeriv (DirichletCharacter.LFunction χ) ((-γ : ℝ) : ℂ)).re + Real.log (N / Real.pi)| ≤
      9 + VM (1 + γ) := by
  set s : ℂ := ((-γ : ℝ) : ℂ) with hs
  have hpar := par_re_nonneg χ
  have hγ0 : 0 < γ := by linarith
  have c1 : ∀ n : ℕ, (s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [hs, Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.neg_re,
      Complex.natCast_re] at hre
    rcases par_spec χ with ⟨-, h0⟩ | ⟨-, h1⟩
    · rw [h0] at hre; simp at hre
      rcases n with _ | n
      · simp at hre; linarith
      · push_cast at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rw [h1] at hre; simp at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have c2 : ∀ n : ℕ, (1 - s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [hs, Complex.div_ofNat_re, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hpar.1]
  have c3 := L_menos_gamma_ne hZL hp hγ0 (by linarith)
  have hre1 : 1 < (1 - s).re := by simp [hs]; linarith
  have c4 : DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 := L_sigma_ne' χ⁻¹ hre1
  have href := reflexion_gen hR hp c1 c2 c3 c4
  have hL' : logDeriv (DirichletCharacter.LFunction χ) s =
      -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((s + par χ) / 2) / 2 -
        Complex.digamma ((1 - s + par χ) / 2) / 2 -
        logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) := by
    unfold Λd at href
    rw [par_inv] at href
    have e : (1 - s + par χ) / 2 = ((1 - s) + par χ) / 2 := by ring
    rw [e]
    push_cast at href ⊢
    linear_combination href
  rw [hL']
  -- los dos puntos reales
  obtain ⟨a, ha, hpa⟩ : ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ par χ = (a : ℂ) := by
    rcases par_spec χ with ⟨-, h0⟩ | ⟨-, h1⟩
    · exact ⟨0, Or.inl rfl, by rw [h0]; simp⟩
    · exact ⟨1, Or.inr rfl, by rw [h1]; simp⟩
  have e2 : (s + par χ) / 2 = (((a - γ) / 2 : ℝ) : ℂ) := by rw [hs, hpa]; push_cast; ring
  have e3 : (1 - s + par χ) / 2 = (((1 + γ + a) / 2 : ℝ) : ℂ) := by rw [hs, hpa]; push_cast; ring
  rw [e2, e3]
  obtain ⟨d1, d2⟩ := abs_digamma_puntos hS hγ1 hγ2 ha
  have hV := norm_logDeriv_le_VM χ⁻¹ hre1
  have e4 : (1 - s).re = 1 + γ := by simp [hs]
  rw [e4] at hV
  have hV' := (Complex.abs_re_le_norm (logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s))).trans hV
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofNat_re]
  rw [abs_le] at d1 d2 hV' ⊢
  constructor <;> linarith [d1.1, d1.2, d2.1, d2.2, hV'.1, hV'.2]

/-- **Cota de los residuos.** -/
theorem cota_res (h : HipHadamard) (hR : ReflexionLogDeriv) (hS : SerieDigamma)
    (hG : GRHPrimitivo) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {x : ℝ} (hx : 0 < x) :
    |(Res χ x (2 / 5) (9 / 20)).re + Real.log (N / Real.pi) *
        ((x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5))| ≤
      12 * ((x ^ (-(2 / 5 : ℝ)) + x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5)) := by
  have hα := re_logDeriv_menos hR hS h.zl hp (γ := 2 / 5) le_rfl (by norm_num)
  have hβ := re_logDeriv_menos hR hS h.zl hp (γ := 9 / 20) (by norm_num) le_rfl
  have hVα := VM_le_tres h hS hG (σ := 1 + 2 / 5) (by norm_num)
  have hVβ := VM_le_tres h hS hG (σ := 1 + 9 / 20) (by norm_num)
  set Eα := (logDeriv (DirichletCharacter.LFunction χ) ((-(2 / 5 : ℝ) : ℝ) : ℂ)).re
  set Eβ := (logDeriv (DirichletCharacter.LFunction χ) ((-(9 / 20 : ℝ) : ℝ) : ℂ)).re
  set ℓ := Real.log (N / Real.pi)
  have hxα : 0 < x ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hxβ : 0 < x ^ (-(9 / 20 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hRe : (Res χ x (2 / 5) (9 / 20)).re =
      (Eα * x ^ (-(2 / 5 : ℝ)) - Eβ * x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) := by
    unfold Res
    rw [cpow_neg_real hx, cpow_neg_real hx]
    rw [show ((9 / 20 : ℝ) : ℂ) - ((2 / 5 : ℝ) : ℂ) = ((9 / 20 - 2 / 5 : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re, Complex.sub_re, Complex.re_mul_ofReal, Complex.re_mul_ofReal]
  rw [hRe]
  have key : (Eα * x ^ (-(2 / 5 : ℝ)) - Eβ * x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) +
      ℓ * ((x ^ (-(2 / 5 : ℝ)) - x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5)) =
      ((Eα + ℓ) * x ^ (-(2 / 5 : ℝ)) - (Eβ + ℓ) * x ^ (-(9 / 20 : ℝ))) / (9 / 20 - 2 / 5) := by
    ring
  rw [key, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 20 - 2 / 5), ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [abs_le] at hα hβ
  rw [abs_le]
  constructor <;> nlinarith [hα.1, hα.2, hβ.1, hβ.2]

end AMate.Miller.Explicito
