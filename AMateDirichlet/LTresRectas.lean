import AMateDirichlet.LRectaCero

/-!
# Cota de `L(1/2 + it, χ)` por las tres rectas de Hadamard

Para `χ ≠ 1`, tres rectas aplicadas a `f(s) = L(s,χ) e^{(s − s₀)²}` en `0 ≤ Re s ≤ 1`:

* `norm_inv_Gamma_le`: `|1/Γ(w)| ≤ |Γ(1 − w)| |sin(πw)|/π` para `0 ≤ Re w < 1`.
* `LFunction_strip_bound`: cota cruda `|L(s,χ)| ≤ P (1 + |t|)² e^{2|t|}` en la banda (ecuación
  funcional en `Re s < 1/2`); da la acotación que pide el teorema de las tres rectas.
* `norm_sq_LFunction_critica`: `|L(1/2 + it₀, χ)|² ≤ K (1 + |t₀|)^{1/2} (2 + log(2 + |t₀|))²`.
* `L_recta_critica`: `|L(1/2 + ix, χ)| ≤ C (1 + |x|)^{1/3}`.
-/

open Complex Set

namespace AMate.Dirichlet

/-! ### `Γ` y `1/Γ` en la banda -/

theorem Gamma_bdd_cuarto_uno : ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc (1 / 4 : ℝ) 1, Real.Gamma x ≤ G := by
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 4 : ℝ) 1) := by
    intro x hx
    apply (Real.differentiableAt_Gamma _).continuousAt.continuousWithinAt
    intro m hm
    have h1 : (0 : ℝ) < x := by linarith [hx.1]
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max G 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hG x hx
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

theorem norm_Gamma_le_de_Icc {G : ℝ} (hG : ∀ x ∈ Icc (1 / 4 : ℝ) 1, Real.Gamma x ≤ G) {w : ℂ}
    (h1 : 1 / 4 ≤ w.re) (h2 : w.re ≤ 1) : ‖Gamma w‖ ≤ G :=
  (AMate.norm_Gamma_le_Gamma_re (by linarith)).trans (hG _ ⟨h1, h2⟩)

theorem norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [← Complex.cos_sub_pi_div_two]
  refine (AMate.norm_cos_le_exp _).trans (le_of_eq ?_)
  congr 2
  simp

/-- `|1/Γ(w)| ≤ |Γ(1 − w)| |sin(πw)|/π` para `0 ≤ Re w < 1` (fórmula de reflexión). -/
theorem norm_inv_Gamma_le {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re < 1) :
    ‖(Gamma w)⁻¹‖ ≤ ‖Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖ / Real.pi := by
  by_cases hΓ : Gamma w = 0
  · rw [hΓ, inv_zero, norm_zero]
    positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * w) ≠ 0 := by
    intro hs
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hw : w = k := by
      rw [mul_comm (k : ℂ)] at hk
      exact mul_left_cancel₀ hpi hk
    have hre : w.re = (k : ℝ) := by rw [hw]; simp
    have hk0 : k = 0 := by
      have a1 : (0 : ℝ) ≤ k := hre ▸ h0
      have a2 : (k : ℝ) < 1 := hre ▸ h1
      have b1 : (0 : ℤ) ≤ k := by exact_mod_cast a1
      have b2 : k < 1 := by exact_mod_cast a2
      omega
    apply hΓ
    rw [hw, hk0]
    simp [Complex.Gamma_zero]
  have hrefl := Gamma_mul_Gamma_one_sub w
  have heq : (Gamma w)⁻¹ = Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
    field_simp
    rw [hrefl]
    field_simp
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-! ### Cota cruda en la banda -/

variable {N : ℕ} [NeZero N]

/-- En `1/2 ≤ Re s ≤ 1`: `|L(s,χ)| ≤ (1 + 3N)(1 + |t|)`. -/
theorem norm_LFunction_le_derecha {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z : ℂ}
    (h0 : 1 / 2 ≤ z.re) (h1 : z.re ≤ 1) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ (1 + 3 * N) * (1 + |z.im|) := by
  have hσ : 0 < z.re := by linarith
  have h := norm_LFunction_le_trunc hχ hσ (X := 1) le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.one_rpow, mul_one] at h
  have hzn : ‖z‖ ≤ 1 + |z.im| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |z.im| := by rw [abs_of_pos hσ]; linarith
  have hinv : ‖z‖ * (N / z.re) ≤ 2 * N * (1 + |z.im|) := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [mul_div_assoc', div_le_iff₀ hσ]
    nlinarith [mul_nonneg (mul_nonneg hN (by positivity : (0 : ℝ) ≤ 1 + |z.im|))
        (by linarith : (0 : ℝ) ≤ 2 * z.re - 1),
      mul_nonneg hN (by linarith : (0 : ℝ) ≤ 1 + |z.im| - ‖z‖)]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [abs_nonneg z.im]

omit [NeZero N] in
/-- En `0 ≤ Re s < 1/2`: `|γ(1 − s)| ≤ G` y `|1/γ(s)| ≤ G e^{2|t|}`. -/
theorem gammaFactor_izq (χ : DirichletCharacter ℂ N) {G : ℝ}
    (hG : ∀ x ∈ Icc (1 / 4 : ℝ) 1, Real.Gamma x ≤ G) {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re < 1 / 2) :
    ‖DirichletCharacter.gammaFactor χ (1 - z)‖ ≤ G
      ∧ ‖(DirichletCharacter.gammaFactor χ z)⁻¹‖ ≤ G * Real.exp (2 * |z.im|) := by
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp : Real.exp |(Real.pi * (z / 2) : ℂ).im| ≤ Real.exp (2 * |z.im|) := by
    apply Real.exp_le_exp.mpr
    have him : ((Real.pi : ℂ) * (z / 2)).im = Real.pi / 2 * z.im := by simp [mul_im]; ring
    rw [him, abs_mul, abs_of_pos (by positivity)]
    have := Real.pi_lt_four
    nlinarith [abs_nonneg z.im]
  have hexp' : Real.exp |(Real.pi * ((z + 1) / 2) : ℂ).im| ≤ Real.exp (2 * |z.im|) := by
    apply Real.exp_le_exp.mpr
    have him : ((Real.pi : ℂ) * ((z + 1) / 2)).im = Real.pi / 2 * z.im := by simp [mul_im]; ring
    rw [him, abs_mul, abs_of_pos (by positivity)]
    have := Real.pi_lt_four
    nlinarith [abs_nonneg z.im]
  have hG0 : 0 ≤ G := le_trans (Real.Gamma_nonneg_of_nonneg (by norm_num)) (hG 1 ⟨by norm_num, le_rfl⟩)
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, he.gammaFactor_def]
    constructor
    · rw [norm_Gammaℝ]
      have hre : (1 - z).re = 1 - z.re := by simp
      have hw := norm_Gamma_le_de_Icc hG (w := (1 - z) / 2) (by simp; linarith) (by simp; linarith)
      have hp : Real.pi ^ (-(1 - z).re / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hpi1 (by rw [hre]; linarith)
      calc Real.pi ^ (-(1 - z).re / 2) * ‖Gamma ((1 - z) / 2)‖ ≤ 1 * G := by gcongr
        _ = G := one_mul G
    · rw [Gammaℝ_def, mul_inv, norm_mul]
      have hp : ‖((Real.pi : ℂ) ^ (-z / 2))⁻¹‖ ≤ Real.pi := by
        rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
          ← Real.rpow_neg Real.pi_pos.le]
        have : -(-z / 2).re ≤ 1 := by simp; linarith
        calc Real.pi ^ (-(-z / 2).re) ≤ Real.pi ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hpi1 this
          _ = Real.pi := Real.rpow_one _
      have hi := norm_inv_Gamma_le (w := z / 2) (by simp; linarith) (by simp; linarith)
      have hg := norm_Gamma_le_de_Icc hG (w := 1 - z / 2) (by simp; linarith) (by simp; linarith)
      have hs := norm_sin_le_exp ((Real.pi : ℂ) * (z / 2))
      calc ‖((Real.pi : ℂ) ^ (-z / 2))⁻¹‖ * ‖(Gamma (z / 2))⁻¹‖
          ≤ Real.pi * (G * Real.exp (2 * |z.im|) / Real.pi) := by
            gcongr
            refine hi.trans ?_
            gcongr
            exact hs.trans hexp
        _ = G * Real.exp (2 * |z.im|) := by field_simp
  · rw [ho.gammaFactor_def, ho.gammaFactor_def]
    constructor
    · rw [norm_Gammaℝ]
      have hre : (1 - z + 1).re = 2 - z.re := by simp; ring
      have hw := norm_Gamma_le_de_Icc hG (w := (1 - z + 1) / 2) (by simp; linarith)
        (by simp; linarith)
      have hp : Real.pi ^ (-(1 - z + 1).re / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hpi1 (by rw [hre]; linarith)
      calc Real.pi ^ (-(1 - z + 1).re / 2) * ‖Gamma ((1 - z + 1) / 2)‖ ≤ 1 * G := by gcongr
        _ = G := one_mul G
    · rw [Gammaℝ_def, mul_inv, norm_mul]
      have hp : ‖((Real.pi : ℂ) ^ (-(z + 1) / 2))⁻¹‖ ≤ Real.pi := by
        rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
          ← Real.rpow_neg Real.pi_pos.le]
        have : -(-(z + 1) / 2).re ≤ 1 := by simp; linarith
        calc Real.pi ^ (-(-(z + 1) / 2).re) ≤ Real.pi ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hpi1 this
          _ = Real.pi := Real.rpow_one _
      have hi := norm_inv_Gamma_le (w := (z + 1) / 2) (by simp; linarith) (by simp; linarith)
      have hg := norm_Gamma_le_de_Icc hG (w := 1 - (z + 1) / 2) (by simp; linarith)
        (by simp; linarith)
      have hs := norm_sin_le_exp ((Real.pi : ℂ) * ((z + 1) / 2))
      calc ‖((Real.pi : ℂ) ^ (-(z + 1) / 2))⁻¹‖ * ‖(Gamma ((z + 1) / 2))⁻¹‖
          ≤ Real.pi * (G * Real.exp (2 * |z.im|) / Real.pi) := by
            gcongr
            refine hi.trans ?_
            gcongr
            exact hs.trans hexp'
        _ = G * Real.exp (2 * |z.im|) := by field_simp

/-- Primitivo, `0 ≤ Re s < 1/2`: ecuación funcional con cotas crudas. -/
theorem norm_LFunction_izq_primitivo {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hp : χ.IsPrimitive) {G : ℝ} (hG0 : 0 ≤ G) (hG : ∀ x ∈ Icc (1 / 4 : ℝ) 1, Real.Gamma x ≤ G)
    {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re < 1 / 2) :
    ‖DirichletCharacter.LFunction χ z‖
      ≤ N * N * ((1 + 3 * N) * (1 + |z.im|) * G) * (G * Real.exp (2 * |z.im|)) := by
  have hN1 : N ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  obtain ⟨hga, hgb⟩ := gammaFactor_izq χ hG h0 h1
  set γ := DirichletCharacter.gammaFactor χ with hγdef
  have hγinv : DirichletCharacter.gammaFactor χ⁻¹ = γ := funext (gammaFactor_inv χ)
  have hre1 : (1 - z).re = 1 - z.re := by simp
  have hγ1 : γ (1 - z) ≠ 0 := gammaFactor_ne_zero_re_pos χ (by rw [hre1]; linarith)
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1)
  have hL' := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - z) (Or.inr hN1)
  rw [hγinv] at hL'
  have hFE := hp.completedLFunction_one_sub (1 - z)
  rw [show (1 : ℂ) - (1 - z) = z by ring] at hFE
  have hΛ' : DirichletCharacter.completedLFunction χ⁻¹ (1 - z)
      = DirichletCharacter.LFunction χ⁻¹ (1 - z) * γ (1 - z) := by
    rw [hL', div_mul_cancel₀ _ hγ1]
  have hmain : DirichletCharacter.LFunction χ z
      = (N : ℂ) ^ ((1 - z) - 1 / 2) * DirichletCharacter.rootNumber χ
        * (DirichletCharacter.LFunction χ⁻¹ (1 - z) * γ (1 - z)) * (γ z)⁻¹ := by
    rw [hL, div_eq_mul_inv, hFE, hΛ']
  have hpow : ‖(N : ℂ) ^ ((1 - z) - 1 / 2)‖ ≤ N := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
    have : ((1 : ℂ) - z - 1 / 2).re ≤ 1 := by simp; linarith
    calc (N : ℝ) ^ ((1 : ℂ) - z - 1 / 2).re ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1r this
      _ = N := Real.rpow_one _
  have hroot : ‖DirichletCharacter.rootNumber χ‖ ≤ N := by
    refine (norm_rootNumber_le χ).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hLd : ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ ≤ (1 + 3 * N) * (1 + |z.im|) := by
    have := norm_LFunction_le_derecha hχi (z := 1 - z) (by rw [hre1]; linarith)
      (by rw [hre1]; linarith)
    simpa [abs_neg] using this
  rw [hmain, norm_mul, norm_mul, norm_mul, norm_mul]
  gcongr

/-- **Cota cruda en la banda**: `|L(s,χ)| ≤ P (1 + |t|)² e^{2|t|}` para `0 ≤ Re s ≤ 1`. -/
theorem LFunction_strip_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖DirichletCharacter.LFunction χ z‖ ≤ P * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|) := by
  obtain ⟨G, hG0, hG⟩ := Gamma_bdd_cuarto_uno
  set q := χ.conductor with hqdef
  have : NeZero q := ⟨χ.conductor_ne_zero⟩
  set χ' := χ.primitiveCharacter with hχ'def
  have hrec : DirichletCharacter.changeLevel χ.conductor_dvd_level χ' = χ :=
    χ.changeLevel_primitiveCharacter
  have hχ' : χ' ≠ 1 := by
    intro h
    apply hχ
    rw [← hrec, h, map_one]
  have hp : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
  set k := N.primeFactors.card with hkdef
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set A : ℝ := 1 + 3 * N with hA
  set B : ℝ := (2 : ℝ) ^ k * (q * q * (1 + 3 * q) * G * G) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨A + B, by positivity, fun z h0 h1 => ?_⟩
  set t := z.im with htdef
  have hat := abs_nonneg t
  have hE1 : 1 ≤ Real.exp (2 * |t|) := Real.one_le_exp (by positivity)
  have hT1 : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith
  by_cases hre : 1 / 2 ≤ z.re
  · have h := norm_LFunction_le_derecha hχ hre h1
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ A * (1 + |t|) := h
      _ ≤ (A + B) * ((1 + |t|) ^ 2 * Real.exp (2 * |t|)) := by
          have : 1 + |t| ≤ (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by nlinarith
          nlinarith
      _ = (A + B) * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by ring
  push Not at hre
  have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ' (s := z)
    (Or.inl hχ')
  rw [hrec] at hcl
  have hprod : ‖∏ p ∈ N.primeFactors, (1 - χ' p * (p : ℂ) ^ (-z))‖ ≤ 2 ^ k := by
    rw [norm_prod]
    calc ∏ p ∈ N.primeFactors, ‖1 - χ' p * (p : ℂ) ^ (-z)‖ ≤ ∏ _p ∈ N.primeFactors, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul,
            Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos]
          have hpow : (p : ℝ) ^ (-z).re ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hp1 (by simp; linarith)
          have hc := DirichletCharacter.norm_le_one χ' (p : ZMod q)
          nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ p by linarith) (-z).re, norm_nonneg (χ' p)]
      _ = 2 ^ k := by rw [Finset.prod_const]
  have hprim := norm_LFunction_izq_primitivo hχ' hp hG0 hG h0 hre
  rw [hcl, norm_mul]
  calc ‖DirichletCharacter.LFunction χ' z‖ * ‖∏ p ∈ N.primeFactors, (1 - χ' p * (p : ℂ) ^ (-z))‖
      ≤ (q * q * ((1 + 3 * q) * (1 + |t|) * G) * (G * Real.exp (2 * |t|))) * 2 ^ k := by
        gcongr
    _ = B * (1 + |t|) * Real.exp (2 * |t|) := by rw [hB]; ring
    _ ≤ (A + B) * (1 + |t|) ^ 2 * Real.exp (2 * |t|) := by
        have hEpos := Real.exp_pos (2 * |t|)
        have h1' : B * (1 + |t|) ≤ (A + B) * (1 + |t|) ^ 2 := by nlinarith
        nlinarith

/-! ### Tres rectas de Hadamard -/

/-- `|L(1/2 + it₀, χ)|² ≤ K (1 + |t₀|)^{1/2} (2 + log(2 + |t₀|))²`. -/
theorem norm_sq_LFunction_critica {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t₀ : ℝ,
      ‖DirichletCharacter.LFunction χ (1 / 2 + t₀ * I)‖ ^ 2
        ≤ K * (1 + |t₀|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)) ^ 2 := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_LFunction_mul_I_le hχ
  obtain ⟨P, hP0, hP⟩ := LFunction_strip_bound hχ
  set A : ℝ := 1 + 3 * N with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨Real.exp (1 / 2) * 256 * C₀ * A, by positivity, fun t₀ => ?_⟩
  have hL0 : 0 ≤ Real.log (2 + |t₀|) := Real.log_nonneg (by linarith [abs_nonneg t₀])
  have hpos0 : (0 : ℝ) < 1 + |t₀| := by positivity
  set F : ℂ → ℂ := fun z =>
    DirichletCharacter.LFunction χ z * cexp ((z - (1 / 2 + t₀ * I)) ^ 2) with hFdef
  have hf : Differentiable ℂ F :=
    (DirichletCharacter.differentiable_LFunction hχ).mul
      (((differentiable_id.sub_const (1 / 2 + t₀ * I)).pow 2).cexp)
  have hnf : ∀ z, ‖F z‖ = ‖DirichletCharacter.LFunction χ z‖
      * Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2) := by
    intro z
    simp only [hFdef]
    rw [norm_mul, AMate.norm_exp_sq]
  have ha : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖F z‖
      ≤ Real.exp (1 / 4) * C₀ * (16 * ((1 + |t₀|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have hzI : z = (z.im : ℂ) * I := Complex.ext (by simp [hz0]) (by simp)
    have hL := hC₀ z.im
    rw [← hzI] at hL
    have hL' : ‖DirichletCharacter.LFunction χ z‖
        ≤ C₀ * ((1 + |z.im|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |z.im|))) := by
      rw [← mul_assoc]
      exact hL
    rw [hnf, hz0, show ((0 : ℝ) - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 = 1 / 4 + (-(z.im - t₀) ^ 2) by ring,
      Real.exp_add]
    have hg := AMate.gauss_sup (1 / 2) (by norm_num) (by norm_num) z.im t₀
    calc ‖DirichletCharacter.LFunction χ z‖ * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2))
        ≤ C₀ * ((1 + |z.im|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |z.im|)))
          * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) := by gcongr
      _ = Real.exp (1 / 4) * C₀ * ((1 + |z.im|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |z.im|))
          * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ Real.exp (1 / 4) * C₀
          * (16 * ((1 + |t₀|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) := by gcongr
  have hb : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖F z‖
      ≤ Real.exp (1 / 4) * A * (16 * ((1 + |t₀|) ^ (0 : ℝ) * (2 + Real.log (2 + |t₀|)))) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have hz1I : z = 1 + (z.im : ℂ) * I := Complex.ext (by simp [hz1]) (by simp)
    have hL := norm_LFunction_one_add_le hχ z.im
    rw [← hz1I] at hL
    rw [hnf, hz1, show ((1 : ℝ) - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 = 1 / 4 + (-(z.im - t₀) ^ 2) by ring,
      Real.exp_add]
    have hg := AMate.gauss_sup 0 le_rfl (by norm_num) z.im t₀
    simp only [Real.rpow_zero, one_mul] at hg ⊢
    calc ‖DirichletCharacter.LFunction χ z‖ * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2))
        ≤ A * (2 + Real.log (2 + |z.im|)) * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) := by
          gcongr
      _ = Real.exp (1 / 4) * A * ((2 + Real.log (2 + |z.im|)) * Real.exp (-(z.im - t₀) ^ 2)) := by
          ring
      _ ≤ Real.exp (1 / 4) * A * (16 * (2 + Real.log (2 + |t₀|))) := by gcongr
  have hBdd : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨P * Real.exp (1 / 4) * ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4), ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
    have hPz := hP z hz'.1 hz'.2
    simp only [Function.comp]
    rw [hnf]
    have hsig : (z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2 ≤ 1 / 4 + (-(z.im - t₀) ^ 2) := by
      nlinarith [hz'.1, hz'.2]
    have hexp_le : Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2)
        ≤ Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hsig
    have hcg := AMate.crude_gauss z.im t₀
    calc ‖DirichletCharacter.LFunction χ z‖ * Real.exp ((z.re - 1 / 2) ^ 2 - (z.im - t₀) ^ 2)
        ≤ (P * (1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|))
          * (Real.exp (1 / 4) * Real.exp (-(z.im - t₀) ^ 2)) := by gcongr
      _ = P * Real.exp (1 / 4) * ((1 + |z.im|) ^ 2 * Real.exp (2 * |z.im|)
          * Real.exp (-(z.im - t₀) ^ 2)) := by ring
      _ ≤ P * Real.exp (1 / 4) * ((1 + |t₀|) ^ 2 * Real.exp (2 * |t₀|) * Real.exp 4) := by
          gcongr
  have hre : (1 / 2 + (t₀ : ℂ) * I).re = 1 / 2 := by simp
  have hmem : (1 / 2 + (t₀ : ℂ) * I) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    show (1 / 2 + (t₀ : ℂ) * I).re ∈ Icc (0 : ℝ) 1
    rw [hre]
    constructor <;> norm_num
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' zero_lt_one hmem
    hf.diffContOnCl hBdd ha hb
  rw [hre, show ((1 : ℝ) / 2 - 0) / (1 - 0) = 1 / 2 by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h3
  have hfs : F (1 / 2 + t₀ * I) = DirichletCharacter.LFunction χ (1 / 2 + t₀ * I) := by
    simp [hFdef]
  rw [hfs] at h3
  set a := Real.exp (1 / 4) * C₀
    * (16 * ((1 + |t₀|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |t₀|)))) with hadef
  set b := Real.exp (1 / 4) * A * (16 * ((1 + |t₀|) ^ (0 : ℝ) * (2 + Real.log (2 + |t₀|))))
    with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hsq : (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ 2 = a * b := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ha0, Real.sq_sqrt hb0]
  have hab : a * b = Real.exp (1 / 2) * 256 * C₀ * A * (1 + |t₀|) ^ (1 / 2 : ℝ)
      * (2 + Real.log (2 + |t₀|)) ^ 2 := by
    rw [hadef, hbdef, Real.rpow_zero,
      show Real.exp (1 / 2) = Real.exp (1 / 4) * Real.exp (1 / 4) by
        rw [← Real.exp_add]; norm_num]
    ring
  calc ‖DirichletCharacter.LFunction χ (1 / 2 + t₀ * I)‖ ^ 2
      ≤ (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = a * b := hsq
    _ = _ := hab

/-- **Cota de `L` en la recta crítica**: `|L(1/2 + ix, χ)| ≤ C (1 + |x|)^{1/3}`. -/
theorem L_recta_critica {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I)‖ ≤ C * (1 + |x|) ^ (1 / 3 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := norm_sq_LFunction_critica hχ
  refine ⟨Real.sqrt (K * 676), Real.sqrt_nonneg _, fun x => ?_⟩
  have hax := abs_nonneg x
  have hpos : (0 : ℝ) < 1 + |x| := by positivity
  have h1 := hK x
  have hL := AMate.two_add_log_le |x| hax
  have hLnn : 0 ≤ 2 + Real.log (2 + |x|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |x| by linarith)
    linarith
  have hy12 : ((1 + |x|) ^ (1 / 12 : ℝ)) ^ 2 = (1 + |x|) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hy3 : ((1 + |x|) ^ (1 / 3 : ℝ)) ^ 2 = (1 + |x|) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hy26 : (1 + |x|) ^ (1 / 2 : ℝ) * (1 + |x|) ^ (1 / 6 : ℝ) = (1 + |x|) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hL2 : (2 + Real.log (2 + |x|)) ^ 2 ≤ 676 * (1 + |x|) ^ (1 / 6 : ℝ) := by
    calc (2 + Real.log (2 + |x|)) ^ 2 ≤ (26 * (1 + |x|) ^ (1 / 12 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hLnn hL 2
      _ = 676 * (1 + |x|) ^ (1 / 6 : ℝ) := by rw [mul_pow, hy12]; norm_num
  have hfin : ‖DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I)‖ ^ 2
      ≤ (Real.sqrt (K * 676) * (1 + |x|) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hy3]
    calc ‖DirichletCharacter.LFunction χ (1 / 2 + (x : ℂ) * I)‖ ^ 2
        ≤ K * (1 + |x|) ^ (1 / 2 : ℝ) * (2 + Real.log (2 + |x|)) ^ 2 := h1
      _ ≤ K * (1 + |x|) ^ (1 / 2 : ℝ) * (676 * (1 + |x|) ^ (1 / 6 : ℝ)) := by gcongr
      _ = K * 676 * ((1 + |x|) ^ (1 / 2 : ℝ) * (1 + |x|) ^ (1 / 6 : ℝ)) := by ring
      _ = K * 676 * (1 + |x|) ^ (2 / 3 : ℝ) := by rw [hy26]
  have h5 := Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h5

end AMate.Dirichlet
