import AMateMiller.CotaBach

/-!
# Cota de tipo Bach con `O((log n)^2)` bases

Misma situación que `CotaBach.lean` (fórmula explícita truncada, ceros en ventanas y GRH para los
caracteres primitivos), pero ahora se integra la fórmula explícita en `u ∈ [T, x]` con la altura
`T` fija. La integral de `u^ρ/ρ` es `(x^{ρ+1} − T^{ρ+1})/(ρ(ρ+1))`, de tamaño `x^{3/2}/|ρ|²`, y
`∑ m_ρ/|ρ|²` ya no tiene el factor `log T`. Con `T = x/2` esto da

  `x² ≪ x · (log² (n x) + √x · log (n x))`,

imposible si `x ≈ K (1 + log n)²` con `K` grande (`cota_caracteres_de_grh_cuad`).

* `intervalIntegrable_psi0`: `ψ₀(·, χ)` es integrable en intervalos.
* `suma_ceros_cuad_le`: `∑_{|Im ρ| < T} m_ρ/|ρ|² ≤ 16 C₂ log(N(T + 2))`.
* `norm_integral_psi0_le`: `‖∫_T^x ψ₀(u, χ) du‖ ≤ (x − T) C₁ R(x) + 2 x √x ∑ m_ρ/|ρ|²`.
* `cota_caracteres_de_grh_cuad`: el resultado.
-/

open Complex MeasureTheory

namespace AMate.Miller

open PI

section Integrales

variable {N : ℕ} [NeZero N]

/-- `ψ₀(·, χ)` es integrable en cualquier intervalo: es una función escalonada menos, si `χ = 1`,
la identidad. -/
theorem intervalIntegrable_psi0 (χ : DirichletCharacter ℂ N) (a b : ℝ) :
    IntervalIntegrable (psi0 χ) volume a b := by
  classical
  set f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)
    with hfdef
  set g : ℕ → ℂ := fun k => ∑ n ∈ Finset.Icc 1 k, f n with hgdef
  have hstep : IntervalIntegrable (fun u : ℝ => g ⌊u⌋₊) volume a b := by
    rw [intervalIntegrable_iff]
    set K : ℕ := ⌊|a| + |b|⌋₊ with hK
    refine Measure.integrableOn_of_bounded (M := ∑ n ∈ Finset.Icc 1 K, ‖f n‖) ?_ ?_ ?_
    · exact (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
    · exact ((measurable_from_nat (f := g)).comp Nat.measurable_floor).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun u hu => ?_
      have hub : u ≤ |a| + |b| := by
        have := (Set.uIoc_subset_uIcc hu).2
        rcases le_total a b with h | h
        · rw [max_eq_right h] at this
          linarith [le_abs_self b, abs_nonneg a]
        · rw [max_eq_left h] at this
          linarith [le_abs_self a, abs_nonneg b]
      have hfl : ⌊u⌋₊ ≤ K := Nat.floor_le_floor hub
      calc ‖g ⌊u⌋₊‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 K, ‖f n‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hfl)
            fun _ _ _ => norm_nonneg _
  unfold psi0
  refine hstep.sub ?_
  by_cases h : χ = 1
  · simp only [h, if_true]
    exact Complex.continuous_ofReal.intervalIntegrable _ _
  · simp only [h, if_false]
    exact intervalIntegrable_const

/-- `∑_{k ≤ M} 1/(k + 1)² ≤ 2 − 1/(M + 1)`. -/
theorem suma_inv_cuad_le (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((M : ℝ) + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have key : 1 / (((M + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((M : ℝ) + 1) - 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ hM.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

/-- **Suma de `m_ρ/|ρ|²` por ventanas**: con GRH y la cota de ceros en ventanas,
`∑_{ρ ∈ ZerosBelow χ T} m_ρ/|ρ|² ≤ 16 C₂ log(N(T + 2))`. -/
theorem suma_ceros_cuad_le {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hZW : ZerosWindowWith C₂)
    (hGRH : GRHPrimitivo) (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (ZerosBelow χ T).Finite) :
    ∑ᶠ ρ ∈ ZerosBelow χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ^ 2
      ≤ 16 * C₂ * Real.log (N * (T + 2)) := by
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
    with hmdef
  have hm0 : ∀ ρ, 0 ≤ m ρ := fun ρ => Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set Z := hfin.toFinset with hZdef
  set M := ⌊T⌋₊ with hMdef
  have hMT : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hmaps : ∀ ρ ∈ Z, ⌊|ρ.im|⌋₊ ∈ Finset.range (M + 1) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor hρ.2.2.1.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set Λ₀ : ℝ := Real.log (N * (T + 2)) with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := Real.log_nonneg (by nlinarith)
  have hfib : ∀ j ∈ Finset.range (M + 1),
      ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖ ^ 2 ≤ 8 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjT : (j : ℝ) ≤ T := (Nat.cast_le.mpr hjM).trans hMT
    obtain ⟨hfinA, hA⟩ := hZW N χ hp (j : ℝ)
    obtain ⟨hfinB, hB⟩ := hZW N χ hp (-(j : ℝ))
    rw [abs_neg, Nat.abs_cast] at hB
    rw [Nat.abs_cast] at hA
    have hlogj : Real.log (N * ((j : ℝ) + 2)) ≤ Λ₀ :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hsub : (Z.filter fun ρ => ⌊|ρ.im|⌋₊ = j) ⊆ hfinA.toFinset ∪ hfinB.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter, hZdef, Set.Finite.mem_toFinset] at hρ
      obtain ⟨⟨h0, h1, -, hL⟩, hfl⟩ := hρ
      have hlo : (j : ℝ) ≤ |ρ.im| := by rw [← hfl]; exact Nat.floor_le (abs_nonneg _)
      have hhi : |ρ.im| < (j : ℝ) + 1 := by rw [← hfl]; exact Nat.lt_floor_add_one _
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      rcases le_or_gt 0 ρ.im with him | him
      · left
        refine ⟨h0, h1, ?_, hL⟩
        rw [abs_of_nonneg him] at hlo hhi
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨h0, h1, ?_, hL⟩
        rw [abs_of_neg him] at hlo hhi
        rw [abs_le]
        constructor <;> linarith
    have hsumF : ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ ≤ 2 * C₂ * Λ₀ := by
      calc ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ
          ≤ ∑ ρ ∈ hfinA.toFinset ∪ hfinB.toFinset, m ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ => hm0 ρ
        _ ≤ ∑ ρ ∈ hfinA.toFinset, m ρ + ∑ ρ ∈ hfinB.toFinset, m ρ := by
            rw [← Finset.sum_union_inter]
            have : 0 ≤ ∑ ρ ∈ hfinA.toFinset ∩ hfinB.toFinset, m ρ :=
              Finset.sum_nonneg fun ρ _ => hm0 ρ
            linarith
        _ = (∑ᶠ ρ ∈ ZerosNear χ (j : ℝ), m ρ) + ∑ᶠ ρ ∈ ZerosNear χ (-(j : ℝ)), m ρ := by
            rw [finsum_mem_eq_finite_toFinset_sum _ hfinA, finsum_mem_eq_finite_toFinset_sum _ hfinB]
        _ ≤ C₂ * Real.log (N * ((j : ℝ) + 2)) + C₂ * Real.log (N * ((j : ℝ) + 2)) :=
            add_le_add hA hB
        _ ≤ 2 * C₂ * Λ₀ := by nlinarith
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = j),
        m ρ / ‖ρ‖ ^ 2 ≤ m ρ * (4 / ((j : ℝ) + 1) ^ 2) := by
      intro ρ hρ
      have hmem := hρ
      rw [Finset.mem_filter, hZdef, Set.Finite.mem_toFinset] at hmem
      have hre := re_eq_half_de_mem hGRH hp hmem.1
      have hn := norm_ge_floor hre
      rw [hmem.2] at hn
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by positivity) hn
      have hsq : ((j : ℝ) + 1) ^ 2 / 4 ≤ ‖ρ‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hn 2
        rw [div_pow] at this
        norm_num at this ⊢
        linarith
      rw [div_le_iff₀ (by positivity)]
      have := hm0 ρ
      calc m ρ = m ρ * (4 / ((j : ℝ) + 1) ^ 2) * (((j : ℝ) + 1) ^ 2 / 4) := by field_simp
        _ ≤ m ρ * (4 / ((j : ℝ) + 1) ^ 2) * ‖ρ‖ ^ 2 := by gcongr
    calc ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖ ^ 2
        ≤ ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ * (4 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ) * (4 / ((j : ℝ) + 1) ^ 2) := by rw [Finset.sum_mul]
      _ ≤ (2 * C₂ * Λ₀) * (4 / ((j : ℝ) + 1) ^ 2) := by gcongr
      _ = 8 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1) ^ 2) := by ring
  have hsum2 : ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
    have := suma_inv_cuad_le M
    have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith
  calc ∑ j ∈ Finset.range (M + 1), ∑ ρ ∈ Z with ⌊|ρ.im|⌋₊ = j, m ρ / ‖ρ‖ ^ 2
      ≤ ∑ j ∈ Finset.range (M + 1), 8 * C₂ * Λ₀ * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum hfib
    _ = 8 * C₂ * Λ₀ * ∑ j ∈ Finset.range (M + 1), 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 8 * C₂ * Λ₀ * 2 := by gcongr
    _ = 16 * C₂ * Λ₀ := by ring

/-- `|ρ| ≤ |ρ + 1|` si `Re ρ ≥ 0`. -/
theorem norm_le_norm_add_one {ρ : ℂ} (h : 0 ≤ ρ.re) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  have h2 : ‖ρ‖ ^ 2 ≤ ‖ρ + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2

/-- **Fórmula explícita integrada.** Para `χ` primitivo y `2 ≤ T ≤ x`,
`‖∫_T^x ψ₀(u, χ) du‖ ≤ (x − T) C₁ (x log²(NxT)/T + log(Nx) + S₁) + 2 x √x ∑_{|Im ρ| < T} m_ρ/|ρ|²`. -/
theorem norm_integral_psi0_le {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hEF : ExplicitFormulaWith C₁)
    (hGRH : GRHPrimitivo) (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) {T x : ℝ}
    (hT : 2 ≤ T) (hTx : T ≤ x) :
    ‖∫ u in T..x, psi0 χ u‖ ≤
      (x - T) * (C₁ * (x * Real.log (N * x * T) ^ 2 / T + Real.log (N * x) +
        ∑ᶠ ρ ∈ ZerosBelow χ 1, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖))
      + 2 * x * Real.sqrt x * ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ^ 2 := by
  classical
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  obtain ⟨hfin, -⟩ := hEF N χ hp T T hT le_rfl
  set Zf := hfin.toFinset with hZf
  set mc : ℂ → ℂ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) with hmc
  set S₁ : ℝ := ∑ᶠ ρ ∈ ZerosBelow χ 1,
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ with hS₁
  set zs : ℝ → ℂ := fun u => ∑ ρ ∈ Zf, mc ρ * ((u : ℂ) ^ ρ / ρ) with hzs
  set R : ℝ → ℝ := fun u => u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + S₁ with hR
  -- cota puntual de la fórmula explícita, con `T` fijo
  have hF : ∀ u ∈ Set.uIoc T x, ‖psi0 χ u + zs u‖ ≤ C₁ * R x := by
    intro u hu
    rw [Set.uIoc_of_le hTx] at hu
    obtain ⟨-, hb⟩ := hEF N χ hp u T hT hu.1.le
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
    have hu0 : 0 < u := by linarith [hu.1]
    have h1 : 1 ≤ N * u * T :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 (by linarith [hu.1]))
        (by linarith)
    have hl1 : Real.log (N * u * T) ≤ Real.log (N * x * T) :=
      Real.log_le_log (by positivity) (by gcongr; exact hu.2)
    have hl0 : 0 ≤ Real.log (N * u * T) := Real.log_nonneg h1
    have hl2 : Real.log (N * u) ≤ Real.log (N * x) :=
      Real.log_le_log (by positivity) (by gcongr; exact hu.2)
    have hsq : Real.log (N * u * T) ^ 2 ≤ Real.log (N * x * T) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
    have hdiv : u * Real.log (N * u * T) ^ 2 / T ≤ x * Real.log (N * x * T) ^ 2 / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      exact mul_le_mul hu.2 hsq (by positivity) hx0.le
    simp only [hR]
    linarith
  -- integrabilidad
  have hcpow : ∀ ρ : ℂ, IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ ρ) volume T x := fun ρ =>
    intervalIntegral.intervalIntegrable_cpow (Or.inr (by
      rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith))
  have hzsI : IntervalIntegrable zs volume T x := by
    have h := IntervalIntegrable.sum Zf (f := fun ρ (u : ℝ) => mc ρ * ((u : ℂ) ^ ρ / ρ))
      fun ρ _ => ((hcpow ρ).div_const ρ).const_mul (mc ρ)
    have he : zs = ∑ ρ ∈ Zf, fun u : ℝ => mc ρ * ((u : ℂ) ^ ρ / ρ) := by
      funext u
      simp only [hzs, Finset.sum_apply]
    rw [he]
    exact h
  have hψI := intervalIntegrable_psi0 χ T x
  -- la integral de la suma sobre ceros
  have hint : ∫ u in T..x, zs u =
      ∑ ρ ∈ Zf, mc ρ * ((((x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)) / (ρ + 1)) / ρ) := by
    simp only [hzs]
    rw [intervalIntegral.integral_finsetSum fun ρ _ => ((hcpow ρ).div_const ρ).const_mul (mc ρ)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    congr 2
    have hre : -1 < ρ.re := by
      rw [Set.Finite.mem_toFinset] at hρ
      linarith [hρ.1]
    rw [integral_cpow (Or.inl hre)]
  have hdescomp : ∫ u in T..x, psi0 χ u =
      (∫ u in T..x, (psi0 χ u + zs u)) - ∫ u in T..x, zs u := by
    rw [intervalIntegral.integral_add hψI hzsI, add_sub_cancel_right]
  rw [hdescomp, hint]
  have hA : ‖∫ u in T..x, (psi0 χ u + zs u)‖ ≤ (x - T) * (C₁ * R x) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const hF
    rw [abs_of_nonneg (by linarith : 0 ≤ x - T)] at this
    linarith
  have hB : ‖∑ ρ ∈ Zf, mc ρ * ((((x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)) / (ρ + 1)) / ρ)‖ ≤
      2 * x * Real.sqrt x * ∑ ρ ∈ Zf,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [Set.Finite.mem_toFinset] at hρ
    have hre := re_eq_half_de_mem hGRH hp hρ
    have hre1 : (ρ + 1).re = 3 / 2 := by rw [Complex.add_re, hre, Complex.one_re]; norm_num
    have hρ0 : 0 < ‖ρ‖ := by
      have := Complex.abs_re_le_norm ρ
      rw [hre] at this
      linarith [abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hρ1 : ‖ρ‖ ≤ ‖ρ + 1‖ := norm_le_norm_add_one (by rw [hre]; norm_num)
    have hpx : ‖(x : ℂ) ^ (ρ + 1)‖ = x * Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre1, Real.sqrt_eq_rpow,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have hpT : ‖(T : ℂ) ^ (ρ + 1)‖ ≤ x * Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0, hre1, Real.sqrt_eq_rpow,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hT0, Real.rpow_one]
      exact mul_le_mul hTx (Real.rpow_le_rpow hT0.le hTx (by norm_num)) (by positivity) hx0.le
    have hnum : ‖(x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)‖ ≤ 2 * (x * Real.sqrt x) := by
      calc _ ≤ ‖(x : ℂ) ^ (ρ + 1)‖ + ‖(T : ℂ) ^ (ρ + 1)‖ := norm_sub_le _ _
        _ ≤ 2 * (x * Real.sqrt x) := by rw [hpx]; linarith
    have hm : ‖mc ρ‖ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      simp only [hmc, Complex.norm_natCast]
    rw [norm_mul, norm_div, norm_div, hm]
    have hm0 : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
      Nat.cast_nonneg _
    have hden : ‖ρ‖ ^ 2 ≤ ‖ρ + 1‖ * ‖ρ‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hρ1 hρ0.le
    calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
          (‖(x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)‖ / ‖ρ + 1‖ / ‖ρ‖)
        = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
          (‖(x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)‖ / (‖ρ + 1‖ * ‖ρ‖)) := by rw [div_div]
      _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
          (2 * (x * Real.sqrt x) / ‖ρ‖ ^ 2) := by
          gcongr
      _ = 2 * x * Real.sqrt x *
          ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖ ^ 2) := by ring
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc _ ≤ ‖∫ u in T..x, (psi0 χ u + zs u)‖ +
        ‖∑ ρ ∈ Zf, mc ρ * ((((x : ℂ) ^ (ρ + 1) - (T : ℂ) ^ (ρ + 1)) / (ρ + 1)) / ρ)‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add hA hB

end Integrales

/-! ### El teorema -/

/-- Si `χ ≠ 1`, `ψ₀(u, χ)` solo depende de `⌊u⌋`. -/
theorem psi0_floor {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (u : ℝ) :
    psi0 χ u = psi0 χ (⌊u⌋₊ : ℝ) := by
  unfold psi0
  rw [if_neg hχ, if_neg hχ, Nat.floor_natCast]

/-- Cota puntual inferior: si `χ(m) = 1` para todo `m ≤ B` coprimo con `n`, para `u ∈ [2, B]`,
`Re (ψ₀(u, χ*) − ψ₀(u, 1)) ≥ u − 4 log n · log B`. -/
theorem re_dif_ge {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1) {B : ℕ}
    (h : ∀ m : ℕ, m ≤ B → Nat.Coprime m n → χ m = 1) {u : ℝ} (hu2 : 2 ≤ u) (huB : u ≤ B) :
    u - 4 * Real.log n * Real.log B ≤
      (psi0 χ.primitiveCharacter u - psi0 (1 : DirichletCharacter ℂ 1) u).re := by
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
  set k := ⌊u⌋₊ with hk
  have hkB : k ≤ B := by
    have := Nat.floor_le_floor (R := ℝ) huB
    rwa [Nat.floor_natCast] at this
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hu2)
  have hre := re_psi0_ge hχ (B := k) fun m hm hc => h m (hm.trans hkB) hc
  have hE := suma_no_coprimos_le (n := n) (B := k) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogk : Real.log k ≤ Real.log B :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hkB)
  rw [psi0_floor hχ' u, psi0_one u, Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_re]
  have : 2 * Real.log n * Real.log k ≤ 2 * Real.log n * Real.log B := by gcongr
  linarith

/-- `log B ≤ 6 M L` si `0 < B ≤ M⁴ L²` con `M, L ≥ 1`. -/
theorem log_le_seis {Mm L Bv : ℝ} (hM : 1 ≤ Mm) (hL : 1 ≤ L) (hB : 0 < Bv)
    (hBX : Bv ≤ Mm ^ 4 * L ^ 2) : Real.log Bv ≤ 6 * (Mm * L) := by
  have h1 : Real.log Bv ≤ Real.log (Mm ^ 4 * L ^ 2) := Real.log_le_log hB hBX
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
  have hm := Real.log_le_sub_one_of_pos (show 0 < Mm by linarith)
  have hl := Real.log_le_sub_one_of_pos (show 0 < L by linarith)
  have hMP : Mm ≤ Mm * L := le_mul_of_one_le_right (by linarith) hL
  have hLP : L ≤ Mm * L := le_mul_of_one_le_left (by linarith) hM
  push_cast at h1
  linarith

/-- Lado derecho de la fórmula integrada para `T = x/2` y `256 ≤ x ≤ M⁴ L²`. -/
theorem cota_integral_lado_derecho {C₁ C₂ Mm L x Nv S₁ Z : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hM : 1 ≤ Mm) (hL : 1 ≤ L) (hx : 256 ≤ x) (hxX : x ≤ Mm ^ 4 * L ^ 2) (hN1 : 1 ≤ Nv)
    (hNL : Real.log Nv ≤ L)
    (hS₁ : S₁ ≤ 4 * C₂ * Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1)))
    (hZ : Z ≤ 16 * C₂ * Real.log (Nv * (x / 2 + 2))) :
    (x - x / 2) * (C₁ * (x * Real.log (Nv * x * (x / 2)) ^ 2 / (x / 2) + Real.log (Nv * x) + S₁))
      + 2 * x * Real.sqrt x * Z
      ≤ x * (Mm ^ 3 * L ^ 2) * (C₁ * (345 + 24 * C₂) + 224 * C₂) := by
  have hx0 : 0 < x := by linarith
  set P : ℝ := Mm * L with hP
  have hMP : Mm ≤ P := le_mul_of_one_le_right (by linarith) hL
  have hLP : L ≤ P := le_mul_of_one_le_left (by linarith) hM
  have hP1 : 1 ≤ P := hL.trans hLP
  have hlogN0 : 0 ≤ Real.log Nv := Real.log_nonneg hN1
  have hlogx : Real.log x ≤ 6 * P := by
    have h1 : Real.log x ≤ Real.log (Mm ^ 4 * L ^ 2) := Real.log_le_log hx0 hxX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    have hm := Real.log_le_sub_one_of_pos (show 0 < Mm by linarith)
    have hl := Real.log_le_sub_one_of_pos (show 0 < L by linarith)
    push_cast at h1
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogT : Real.log (x / 2) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  have hlogT0 : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith)
  have hlog3 : Real.log (Nv * x * (x / 2)) = Real.log Nv + Real.log x + Real.log (x / 2) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by linarith) (by linarith)]
  have a1 : Real.log (Nv * x * (x / 2)) ≤ 13 * P := by rw [hlog3]; linarith
  have a1' : 0 ≤ Real.log (Nv * x * (x / 2)) := by rw [hlog3]; linarith
  have a2 : Real.log (Nv * x) ≤ 7 * P := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hl3 : Real.log (Nv * (1 + 2)) ≤ 3 * L := by
    rw [Real.log_mul (by linarith) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 by norm_num)
    linarith
  have hl2 : 1 + Real.log (1 + 1) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 by norm_num)
    linarith
  have hl2' : 0 ≤ 1 + Real.log (1 + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 1 by norm_num)
    linarith
  have hS : S₁ ≤ 24 * C₂ * P := by
    have h1 : Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1)) ≤ 3 * L * 2 :=
      mul_le_mul hl3 hl2 hl2' (by positivity)
    have h2 : 4 * C₂ * (Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1))) ≤ 4 * C₂ * (3 * L * 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : C₂ * L ≤ C₂ * P := mul_le_mul_of_nonneg_left hLP hC₂
    calc S₁ ≤ 4 * C₂ * (Real.log (Nv * (1 + 2)) * (1 + Real.log (1 + 1))) := by linarith
      _ ≤ 4 * C₂ * (3 * L * 2) := h2
      _ = 24 * (C₂ * L) := by ring
      _ ≤ 24 * (C₂ * P) := by linarith
      _ = 24 * C₂ * P := by ring
  have hZ' : Z ≤ 112 * C₂ * P := by
    have h1 : Real.log (Nv * (x / 2 + 2)) ≤ 7 * P := by
      rw [Real.log_mul (by linarith) (by linarith)]
      have : Real.log (x / 2 + 2) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
      linarith
    have h2 : 16 * C₂ * Real.log (Nv * (x / 2 + 2)) ≤ 16 * C₂ * (7 * P) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hsqrt : Real.sqrt x ≤ Mm ^ 2 * L := by
    calc Real.sqrt x ≤ Real.sqrt (Mm ^ 4 * L ^ 2) := Real.sqrt_le_sqrt hxX
      _ = Mm ^ 2 * L := by
          rw [show Mm ^ 4 * L ^ 2 = (Mm ^ 2 * L) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hdiv : x * Real.log (Nv * x * (x / 2)) ^ 2 / (x / 2) = 2 * Real.log (Nv * x * (x / 2)) ^ 2 := by
    field_simp
  have hsq : Real.log (Nv * x * (x / 2)) ^ 2 ≤ (13 * P) ^ 2 := pow_le_pow_left₀ a1' a1 2
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hC₂P : C₂ * P ≤ C₂ * P ^ 2 := mul_le_mul_of_nonneg_left hPP hC₂
  have hR : x * Real.log (Nv * x * (x / 2)) ^ 2 / (x / 2) + Real.log (Nv * x) + S₁
      ≤ (345 + 24 * C₂) * P ^ 2 := by
    rw [hdiv]
    have e : (13 * P) ^ 2 = 169 * P ^ 2 := by ring
    have e2 : (345 + 24 * C₂) * P ^ 2 = 345 * P ^ 2 + 24 * (C₂ * P ^ 2) := by ring
    rw [e] at hsq
    rw [e2]
    linarith
  have hP3 : P ^ 2 ≤ Mm ^ 3 * L ^ 2 := by
    have : Mm ^ 2 ≤ Mm ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    calc P ^ 2 = Mm ^ 2 * L ^ 2 := by rw [hP]; ring
      _ ≤ Mm ^ 3 * L ^ 2 := by gcongr
  set Q : ℝ := Mm ^ 3 * L ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have t1 : (x - x / 2) * (C₁ * (x * Real.log (Nv * x * (x / 2)) ^ 2 / (x / 2)
        + Real.log (Nv * x) + S₁)) ≤ x * (C₁ * ((345 + 24 * C₂) * Q)) := by
    have h1 : C₁ * (x * Real.log (Nv * x * (x / 2)) ^ 2 / (x / 2) + Real.log (Nv * x) + S₁)
        ≤ C₁ * ((345 + 24 * C₂) * Q) :=
      mul_le_mul_of_nonneg_left (hR.trans (mul_le_mul_of_nonneg_left hP3 (by positivity))) hC₁
    have h0 : 0 ≤ C₁ * ((345 + 24 * C₂) * Q) := by positivity
    calc _ ≤ (x - x / 2) * (C₁ * ((345 + 24 * C₂) * Q)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ x * (C₁ * ((345 + 24 * C₂) * Q)) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
  have t2 : 2 * x * Real.sqrt x * Z ≤ x * (224 * C₂ * Q) := by
    by_cases hz : Z ≤ 0
    · have h1 : 2 * x * Real.sqrt x * Z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
      have h2 : 0 ≤ x * (224 * C₂ * Q) := by positivity
      linarith
    · push Not at hz
      have h1 : 2 * x * Real.sqrt x * Z ≤ 2 * x * (Mm ^ 2 * L) * (112 * C₂ * P) := by
        apply mul_le_mul _ hZ' hz.le (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
      have e : 2 * x * (Mm ^ 2 * L) * (112 * C₂ * P) = x * (224 * C₂ * Q) := by
        rw [hP, hQ]; ring
      linarith
  calc _ ≤ x * (C₁ * ((345 + 24 * C₂) * Q)) + x * (224 * C₂ * Q) := add_le_add t1 t2
    _ = x * Q * (C₁ * (345 + 24 * C₂) + 224 * C₂) := by ring

/-- **Cota de tipo Bach con `O((log n)^2)` bases.** Con la fórmula explícita, la cota de ceros en
ventanas y GRH para los caracteres primitivos, existe `K > 0` tal que todo carácter `χ ≠ 1`
módulo `n ≥ 3` cumple `χ(a) ≠ 1` para algún `a ≤ K (1 + log n)²` coprimo con `n`. -/
theorem cota_caracteres_de_grh_cuad {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hEF : PI.ExplicitFormulaWith C₁) (hZW : PI.ZerosWindowWith C₂) (hG : GRHPrimitivo) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  set E₀ : ℝ := C₁ * (345 + 24 * C₂) + 224 * C₂ with hE₀
  have hE₀0 : 0 ≤ E₀ := by positivity
  set D : ℝ := 2 * E₀ + 24 with hDdef
  set Mm : ℝ := 6 * D + 4 with hMm
  have hM4 : 4 ≤ Mm := by linarith
  have hM1 : 1 ≤ Mm := by linarith
  refine ⟨Mm ^ 4, by positivity, fun n hn χ hχ => ?_⟩
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set L : ℝ := 1 + Real.log n with hLdef
  have hL1 : 1 ≤ L := by linarith
  set X : ℝ := Mm ^ 4 * L ^ 2 with hXdef
  have hX0 : 0 ≤ X := by positivity
  set B : ℕ := ⌊X⌋₊ with hBdef
  have hBX : (B : ℝ) ≤ X := Nat.floor_le hX0
  have hXB : X < (B : ℝ) + 1 := Nat.lt_floor_add_one X
  have hX256 : (256 : ℝ) ≤ X := by
    have h1 : (4 : ℝ) ^ 4 ≤ Mm ^ 4 := pow_le_pow_left₀ (by norm_num) hM4 4
    have h2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    have h3 : Mm ^ 4 ≤ Mm ^ 4 * L ^ 2 := le_mul_of_one_le_right (by positivity) h2
    norm_num at h1
    linarith
  have hB256 : 256 ≤ B := Nat.le_floor (by exact_mod_cast hX256)
  have hx256 : (256 : ℝ) ≤ B := by exact_mod_cast hB256
  have hcop : ∀ m : ℕ, m ≤ B → Nat.Coprime m n → χ m = 1 := fun m hm hc =>
    hcon m (le_trans (by exact_mod_cast hm) hBX) hc
  set x : ℝ := (B : ℝ) with hxdef
  set T : ℝ := x / 2 with hTdef
  have hT2 : 2 ≤ T := by rw [hTdef]; linarith
  have hTx : T ≤ x := by rw [hTdef]; linarith
  -- carácter primitivo asociado y carácter trivial módulo 1
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp' : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hqn : χ.conductor ≤ n := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hp1 : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  -- la integral de la diferencia
  set dif : ℝ → ℂ := fun u => psi0 χ.primitiveCharacter u - psi0 (1 : DirichletCharacter ℂ 1) u
    with hdif
  have hdifI : IntervalIntegrable dif volume T x :=
    (intervalIntegrable_psi0 _ T x).sub (intervalIntegrable_psi0 _ T x)
  set c : ℝ := 4 * Real.log n * Real.log B with hc
  have hlow : ∫ u in T..x, (u - c) ≤ (∫ u in T..x, dif u).re := by
    have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hdifI
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine intervalIntegral.integral_mono_on hTx
      ((continuous_id.sub continuous_const).intervalIntegrable _ _) ⟨hdifI.1.re, hdifI.2.re⟩ ?_
    intro u hu
    exact re_dif_ge hχ hcop (hT2.trans hu.1) hu.2
  have hlowval : ∫ u in T..x, (u - c) = (x ^ 2 - T ^ 2) / 2 - c * (x - T) := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hup : (∫ u in T..x, dif u).re ≤
      ‖∫ u in T..x, psi0 χ.primitiveCharacter u‖ + ‖∫ u in T..x, psi0 (1 : DirichletCharacter ℂ 1) u‖ := by
    have he : ∫ u in T..x, dif u = (∫ u in T..x, psi0 χ.primitiveCharacter u) -
        ∫ u in T..x, psi0 (1 : DirichletCharacter ℂ 1) u :=
      intervalIntegral.integral_sub (intervalIntegrable_psi0 _ T x) (intervalIntegrable_psi0 _ T x)
    rw [he]
    exact (Complex.re_le_norm _).trans (norm_sub_le _ _)
  -- cotas de las dos integrales
  have bound : ∀ (Nn : ℕ) [NeZero Nn] (ψc : DirichletCharacter ℂ Nn), ψc.IsPrimitive →
      Real.log Nn ≤ L → ‖∫ u in T..x, psi0 ψc u‖ ≤ x * (Mm ^ 3 * L ^ 2) * E₀ := by
    intro Nn _ ψc hpc hlogN
    have hNn1 : (1 : ℝ) ≤ Nn := by exact_mod_cast NeZero.one_le
    obtain ⟨hfinT, -⟩ := hEF Nn ψc hpc T T hT2 le_rfl
    have hfin1 : (ZerosBelow ψc 1).Finite := hfinT.subset fun ρ hρ =>
      ⟨hρ.1, hρ.2.1, lt_of_lt_of_le hρ.2.2.1 (by linarith), hρ.2.2.2⟩
    have h1 := norm_integral_psi0_le hC₁.le hEF hG ψc hpc hT2 hTx
    have hS1 := suma_ceros_le hC₂.le hZW hG ψc hpc le_rfl hfin1
    have hZ := suma_ceros_cuad_le hC₂.le hZW hG ψc hpc (by linarith) hfinT
    have h2 := cota_integral_lado_derecho (Nv := (Nn : ℝ)) hC₁.le hC₂.le hM1 hL1 hx256
      hBX hNn1 hlogN hS1 hZ
    exact h1.trans h2
  have hq1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast NeZero.one_le
  have hlogq : Real.log (χ.conductor : ℝ) ≤ L := by
    have : Real.log (χ.conductor : ℝ) ≤ Real.log n :=
      Real.log_le_log (by linarith) (by exact_mod_cast hqn)
    linarith
  have bq := bound χ.conductor χ.primitiveCharacter hp' hlogq
  have b1 := bound 1 (1 : DirichletCharacter ℂ 1) hp1 (by rw [Nat.cast_one, Real.log_one]; linarith)
  -- aritmética final
  have hlogB : Real.log B ≤ 6 * (Mm * L) := log_le_seis hM1 hL1 (by linarith) hBX
  have hc24 : c ≤ 24 * (Mm * L ^ 2) := by
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have : Real.log n ≤ L := by linarith
    calc c = 4 * Real.log n * Real.log B := rfl
      _ ≤ 4 * L * (6 * (Mm * L)) := by gcongr
      _ = 24 * (Mm * L ^ 2) := by ring
  have hc0 : 0 ≤ c := by
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    positivity
  have hmain : (x ^ 2 - T ^ 2) / 2 - c * (x - T) ≤ 2 * (x * (Mm ^ 3 * L ^ 2) * E₀) := by
    have := hlow.trans hup
    rw [hlowval] at this
    linarith
  set Q : ℝ := Mm ^ 3 * L ^ 2 with hQ
  have hQ0 : 0 < Q := by positivity
  have hx0 : 0 < x := by linarith
  have hMLQ : Mm * L ^ 2 ≤ Q := by
    have : Mm ≤ Mm ^ 3 := le_self_pow₀ hM1 (by norm_num)
    rw [hQ]; gcongr
  have e1 : (x ^ 2 - T ^ 2) / 2 - c * (x - T) = 3 * x ^ 2 / 8 - c * x / 2 := by
    rw [hTdef]; ring
  have e2 : c * x / 2 ≤ 12 * (x * Q) := by
    have : c ≤ 24 * Q := hc24.trans (by linarith)
    have := mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have h38 : x * (3 * x / 8) ≤ x * (Q * D) := by
    have e3 : x * (Q * D) = 2 * (x * Q * E₀) + 24 * (x * Q) := by rw [hDdef]; ring
    have e4 : x * (3 * x / 8) = 3 * x ^ 2 / 8 := by ring
    rw [e3, e4]
    have hxQ : 0 ≤ x * Q := by positivity
    rw [e1] at hmain
    linarith
  have h38' : 3 * x / 8 ≤ Q * D := le_of_mul_le_mul_left h38 hx0
  have hXx : Mm * Q / 2 ≤ x := by
    have e : X = Mm * Q := by rw [hXdef, hQ]; ring
    have : (1 : ℝ) ≤ X / 2 := by linarith
    linarith
  have h3 : 3 * Mm * Q ≤ 16 * D * Q := by linarith
  have h4 : 3 * Mm ≤ 16 * D := le_of_mul_le_mul_right h3 hQ0
  have hD0 : 0 ≤ D := by rw [hDdef]; linarith
  linarith

/-- La misma cota con los enunciados existenciales `PI.ExplicitFormula` y `PI.ZerosWindow`. -/
theorem cota_caracteres_de_grh_cuad' (hEF : PI.ExplicitFormula) (hZW : PI.ZerosWindow)
    (hGRH : GRHPrimitivo) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 := by
  obtain ⟨C₁, hC₁, h₁⟩ := hEF
  obtain ⟨C₂, hC₂, h₂⟩ := hZW
  exact cota_caracteres_de_grh_cuad hC₁ hC₂ h₁ h₂ hGRH

end AMate.Miller
