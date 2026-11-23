import Mathlib

/-!
# Testigo de AMate para un carácter de Dirichlet

Para un carácter de Dirichlet `χ` módulo `N` se define
`S χ y = ∑_{1 ≤ n ≤ y} χ(n)` y el testigo
`σ_{Q,χ}(k) = 1 − ∑_{d ≤ Q} μ(d) χ(d) S_χ(⌊k/d⌋)`.

Su transformada de Mellin es `(1 − L(s,χ) P_{Q,χ}(s))/s`, con
`P_{Q,χ}(s) = ∑_{d ≤ Q} μ(d) χ(d) d^{-s}`. Aquí se prueba la recurrencia
`σ(k+1) = σ(k) − χ(k+1) c_Q(k+1)`, con `c_Q(n) = ∑_{d ∣ n, d ≤ Q} μ(d)`, y la anulación
`σ_{Q,χ}(k) = 0` para `1 ≤ k ≤ Q`, que es la propiedad que usa el recíproco.
-/

open Finset ArithmeticFunction

namespace AMate.Dirichlet

variable {N : ℕ}

/-- `S_χ(y) = ∑_{1 ≤ n ≤ y} χ(n)`. -/
noncomputable def S (χ : DirichletCharacter ℂ N) (y : ℕ) : ℂ := ∑ n ∈ Icc 1 y, χ n

/-- Parte de Möbius del testigo: `T_{Q,χ}(k) = ∑_{d ≤ Q} μ(d) χ(d) S_χ(⌊k/d⌋)`. -/
noncomputable def T (χ : DirichletCharacter ℂ N) (Q k : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 Q, ((moebius d : ℤ) : ℂ) * χ d * S χ (k / d)

/-- Testigo `σ_{Q,χ}(k) = 1 − T_{Q,χ}(k)`. -/
noncomputable def sigma (χ : DirichletCharacter ℂ N) (Q k : ℕ) : ℂ := 1 - T χ Q k

/-- `c_Q(n) = ∑_{d ∣ n, d ≤ Q} μ(d)`. -/
noncomputable def c (Q n : ℕ) : ℂ := ∑ d ∈ n.divisors.filter (· ≤ Q), ((moebius d : ℤ) : ℂ)

theorem S_zero (χ : DirichletCharacter ℂ N) : S χ 0 = 0 := by simp [S]

theorem S_succ (χ : DirichletCharacter ℂ N) (a : ℕ) : S χ (a + 1) = S χ a + χ (a + 1) := by
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ a + 1)]
  push_cast
  ring

theorem S_div_succ (χ : DirichletCharacter ℂ N) (a d : ℕ) :
    S χ ((a + 1) / d) = S χ (a / d) + if d ∣ a + 1 then χ ((a + 1) / d : ℕ) else 0 := by
  by_cases h : d ∣ a + 1
  · rw [if_pos h, Nat.succ_div_of_dvd h, S_succ]
    push_cast
    ring
  · rw [if_neg h, Nat.succ_div_of_not_dvd h, add_zero]

theorem filter_Icc_dvd (Q n : ℕ) (hn : n ≠ 0) :
    (Icc 1 Q).filter (· ∣ n) = n.divisors.filter (· ≤ Q) := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, hQ⟩, hd⟩
    exact ⟨⟨hd, hn⟩, hQ⟩
  · rintro ⟨⟨hd, -⟩, hQ⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn), hQ⟩, hd⟩

theorem T_succ (χ : DirichletCharacter ℂ N) (Q k : ℕ) :
    T χ Q (k + 1) = T χ Q k + χ (k + 1 : ℕ) * c Q (k + 1) := by
  unfold T c
  have hpaso : ∀ d ∈ Icc 1 Q,
      ((moebius d : ℤ) : ℂ) * χ d * S χ ((k + 1) / d)
        = ((moebius d : ℤ) : ℂ) * χ d * S χ (k / d)
          + if d ∣ k + 1 then χ (k + 1 : ℕ) * ((moebius d : ℤ) : ℂ) else 0 := by
    intro d _
    rw [S_div_succ]
    split_ifs with h
    · have hmul : ((d : ℕ) : ZMod N) * (((k + 1) / d : ℕ) : ZMod N) = ((k + 1 : ℕ) : ZMod N) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
      have hχ : χ (d : ZMod N) * χ (((k + 1) / d : ℕ) : ZMod N) = χ ((k + 1 : ℕ) : ZMod N) := by
        rw [← map_mul, hmul]
      linear_combination ((moebius d : ℤ) : ℂ) * hχ
    · ring
  rw [Finset.sum_congr rfl hpaso, Finset.sum_add_distrib, ← Finset.sum_filter,
    filter_Icc_dvd Q (k + 1) (Nat.succ_ne_zero k), Finset.mul_sum]

theorem T_zero (χ : DirichletCharacter ℂ N) (Q : ℕ) : T χ Q 0 = 0 := by
  simp [T, S_zero]

/-- `T_{Q,χ}(k) = ∑_{1 ≤ n ≤ k} χ(n) c_Q(n)`. -/
theorem T_eq_sum (χ : DirichletCharacter ℂ N) (Q k : ℕ) :
    T χ Q k = ∑ n ∈ Icc 1 k, χ n * c Q n := by
  induction k with
  | zero => simp [T_zero]
  | succ k ih =>
    rw [T_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- Para `1 ≤ n ≤ Q`, `c_Q(n) = [n = 1]`. -/
theorem c_of_le {Q n : ℕ} (_hn : 1 ≤ n) (hnQ : n ≤ Q) : c Q n = if n = 1 then 1 else 0 := by
  unfold c
  have hfil : n.divisors.filter (· ≤ Q) = n.divisors := by
    refine Finset.filter_true_of_mem fun d hd => ?_
    exact (Nat.divisor_le hd).trans hnQ
  rw [hfil]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

/-- Anulación del testigo: `σ_{Q,χ}(k) = 0` para `1 ≤ k ≤ Q`. -/
theorem sigma_eq_zero {χ : DirichletCharacter ℂ N} {Q k : ℕ} (hk : 1 ≤ k) (hkQ : k ≤ Q) :
    sigma χ Q k = 0 := by
  unfold sigma
  rw [T_eq_sum]
  have hsum : ∑ n ∈ Icc 1 k, χ n * c Q n = ∑ n ∈ Icc 1 k, if n = 1 then (1 : ℂ) else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hn
    rw [c_of_le h1 (hn.trans hkQ)]
    split_ifs with h
    · subst h; simp
    · simp
  rw [hsum, Finset.sum_ite_eq' (Icc 1 k) 1, if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)]
  ring

/-! ## Periodicidad y acotación de `S_χ` para `χ ≠ 1` -/

section Acotacion

theorem norm_S_le_self (χ : DirichletCharacter ℂ N) (y : ℕ) : ‖S χ y‖ ≤ y := by
  unfold S
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Icc 1 y, ‖χ (n : ZMod N)‖ ≤ ∑ _n ∈ Icc 1 y, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
    _ = y := by simp

/-- `S_χ(y) + χ(0) = ∑_{0 ≤ i ≤ y} χ(i)`. -/
theorem S_add_chi_zero (χ : DirichletCharacter ℂ N) (y : ℕ) :
    S χ y + χ ((0 : ℕ) : ZMod N) = ∑ i ∈ range (y + 1), χ (i : ZMod N) := by
  induction y with
  | zero => simp [S_zero]
  | succ y ih =>
    rw [S_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

variable [NeZero N]

/-- La suma sobre un período completo: `S_χ(N) = ∑_{a ∈ ℤ/N} χ(a)`. -/
theorem S_N_eq_sum (χ : DirichletCharacter ℂ N) : S χ N = ∑ a : ZMod N, χ a := by
  have h := S_add_chi_zero χ N
  rw [Finset.sum_range_succ, ZMod.natCast_self, ← Nat.cast_zero (R := ZMod N)] at h
  have hS : S χ N = ∑ i ∈ range N, χ (i : ZMod N) := add_right_cancel h
  rw [hS]
  refine Finset.sum_nbij (fun i : ℕ => (i : ZMod N)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro i hi j hj hij
    have hi' : i < N := Finset.mem_range.mp hi
    have hj' : j < N := Finset.mem_range.mp hj
    have := congrArg ZMod.val hij
    simp only [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] at this
    exact this
  · intro a _
    exact ⟨a.val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt a)), ZMod.natCast_zmod_val a⟩

theorem S_N_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : S χ N = 0 := by
  rw [S_N_eq_sum]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem S_add_N {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (y : ℕ) : S χ (y + N) = S χ y := by
  induction y with
  | zero => simp [S_N_eq_zero hχ, S_zero]
  | succ y ih =>
    rw [show y + 1 + N = (y + N) + 1 by omega, S_succ, S_succ, ih]
    congr 2
    push_cast
    rw [ZMod.natCast_self, add_zero]

/-- Para `χ ≠ 1`, `‖S_χ(y)‖ ≤ N` para todo `y`. -/
theorem norm_S_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (y : ℕ) : ‖S χ y‖ ≤ N := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    by_cases hy : y < N
    · exact (norm_S_le_self χ y).trans (by exact_mod_cast hy.le)
    · obtain ⟨z, rfl⟩ : ∃ z, y = z + N := ⟨y - N, by omega⟩
      rw [S_add_N hχ]
      exact ih z (by have := NeZero.pos N; omega)

/-- Cota uniforme del testigo: `‖σ_{Q,χ}(k)‖ ≤ 1 + Q N`. -/
theorem norm_sigma_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q k : ℕ) :
    ‖sigma χ Q k‖ ≤ 1 + Q * N := by
  unfold sigma T
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Icc 1 Q, ‖((moebius d : ℤ) : ℂ) * χ d * S χ (k / d)‖
      ≤ ∑ _d ∈ Icc 1 Q, (N : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, norm_mul]
        have hμ : ‖((moebius d : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one
        have hχd := DirichletCharacter.norm_le_one χ (d : ZMod N)
        calc ‖((moebius d : ℤ) : ℂ)‖ * ‖χ d‖ * ‖S χ (k / d)‖ ≤ 1 * 1 * N := by
              gcongr
              · exact norm_S_le hχ _
          _ = N := by ring
    _ = Q * N := by simp

end Acotacion

/-! ## Representación integral de `L(s,χ)` en `Re s > 0` -/

section Mellin

open MeasureTheory Set Complex Filter Topology Asymptotics

variable [NeZero N]

omit [NeZero N] in
theorem measurable_S_floor (χ : DirichletCharacter ℂ N) :
    Measurable (fun x : ℝ => S χ ⌊x⌋₊) :=
  (measurable_from_nat (f := S χ)).comp Nat.measurable_floor

theorem integrableOn_S_floor_cpow {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ => (N : ℝ) * x ^ (-s.re - 1)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) _
  refine hg.mono' ?_ ?_
  · exact ((measurable_S_floor χ).mul (by measurability)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (norm_S_le hχ _) (Real.rpow_nonneg hx0.le _)

/-- Para `Re s > 1`, sumación de Abel: `L(s,χ) = s ∫_1^∞ S_χ(⌊x⌋) x^{−s−1} dx`. -/
theorem LFunction_eq_integral_of_one_lt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      = s * ∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ‖χ (k : ZMod N)‖) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    calc ∑ k ∈ Icc 1 n, ‖χ (k : ZMod N)‖ ≤ ∑ _k ∈ Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
      _ = n := by simp
  rw [LSeries_eq_mul_integral' (fun n : ℕ => χ (n : ZMod N)) zero_le_one hs hO]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [S, neg_add']

/-- La función `S_χ(⌊t⌋)` cortada a `t > 1`, cuya transformada de Mellin en `−s` da `L(s,χ)/s`. -/
noncomputable def Scorte (χ : DirichletCharacter ℂ N) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => S χ ⌊x⌋₊

omit [NeZero N] in
theorem integral_eq_mellin (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) = mellin (Scorte χ) (-s) := by
  unfold mellin Scorte
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator (fun x => S χ ⌊x⌋₊) t
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ => S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
    · simp [Set.indicator_of_notMem ht]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]

theorem differentiableAt_mellin_Scorte {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (mellin (Scorte χ)) (-s) := by
  have hmeas : Measurable (Scorte χ) := (measurable_S_floor χ).indicator measurableSet_Ioi
  have hbound : ∀ t, ‖Scorte χ t‖ ≤ N := by
    intro t
    unfold Scorte
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht]; exact norm_S_le hχ _
    · rw [Set.indicator_of_notMem ht, norm_zero]; positivity
  have hloc : LocallyIntegrableOn (Scorte χ) (Ioi 0) := by
    intro x _
    refine ⟨Ioo (x - 1) (x + 1),
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
    exact Measure.integrableOn_of_bounded (M := N) (by simp [Real.volume_Ioo])
      hmeas.aestronglyMeasurable (Eventually.of_forall hbound)
  have htop : Scorte χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound N (Eventually.of_forall fun t => ?_)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hbound t
  have hbot : Scorte χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    have hzero : Scorte χ =ᶠ[𝓝[>] 0] 0 := by
      have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      filter_upwards [this] with t ht
      unfold Scorte
      rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact (mem_Iio.mp ht).le)]
      rfl
    exact hzero.trans_isBigO (isBigO_zero _ _)
  exact mellin_differentiableAt_of_isBigO_rpow hloc htop (by simp; linarith) hbot (by linarith)

/-- Continuación: `L(s,χ) = s ∫_1^∞ S_χ(⌊x⌋) x^{−s−1} dx` para `Re s > 0` y `χ ≠ 1`. -/
theorem LFunction_eq_integral {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s
      = s * ∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun z => z * mellin (Scorte χ) (-z)) U := by
    intro z hz
    exact (differentiableAt_id.mul
      ((differentiableAt_mellin_Scorte hχ hz).comp z differentiableAt_id.neg)).differentiableWithinAt
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have h2 : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      fun z => z * mellin (Scorte χ) (-z) := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    rw [LFunction_eq_integral_of_one_lt χ hz, integral_eq_mellin]
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hL.analyticOnNhd hUo)
    (hF.analyticOnNhd hUo) (convex_halfSpace_re_gt 0).isPreconnected h2 hev hs
  rw [heq, integral_eq_mellin]

end Mellin

/-! ## Transformada de Mellin del testigo -/

section MellinTestigo

open MeasureTheory Set Complex Filter Topology

variable [NeZero N]

/-- `P_{Q,χ}(s) = ∑_{d ≤ Q} μ(d) χ(d) d^{−s}`. -/
noncomputable def P (χ : DirichletCharacter ℂ N) (Q : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 Q, ((moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s)

omit [NeZero N] in
theorem mul_cpow_neg_sub_one {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) * (y : ℂ) ^ (-s - 1) = (y : ℂ) ^ (-s) := by
  have hne : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have h1 : (y : ℂ) ^ (-s) = (y : ℂ) ^ ((-s - 1) + 1) := by ring_nf
  rw [h1, cpow_add _ _ hne, cpow_one]
  ring

omit [NeZero N] in
theorem integrableOn_bdd_cpow {s : ℂ} (hs : 0 < s.re) {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) :
    IntegrableOn (fun x : ℝ => g x * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hint : IntegrableOn (fun x : ℝ => C * x ^ (-s.re - 1)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) _
  refine hint.mono' ?_ ?_
  · exact (hg.mul (by measurability)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hb x) (Real.rpow_nonneg hx0.le _)

/-- Cambio de escala: `∫_1^∞ S_χ(⌊x⌋/d) x^{−s−1} dx = d^{−s} ∫_1^∞ S_χ(⌊y⌋) y^{−s−1} dy`. -/
theorem integral_S_floor_div {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) {d : ℕ} (hd : 1 ≤ d) :
    ∫ x in Ioi (1 : ℝ), S χ (⌊x⌋₊ / d) * (x : ℂ) ^ (-s - 1)
      = (d : ℂ) ^ (-s) * ∫ x in Ioi (1 : ℝ), S χ ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) := by
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hDne : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  set g : ℝ → ℂ := fun x => S χ (⌊x⌋₊ / d) * (x : ℂ) ^ (-s - 1) with hg
  have hsub := integral_comp_mul_left_Ioi g (1 / (d : ℝ)) hD
  rw [show (d : ℝ) * (1 / d) = 1 by field_simp] at hsub
  have hcongr : ∫ y in Ioi (1 / (d : ℝ)), g (d * y)
      = (d : ℂ) ^ (-s - 1) * ∫ y in Ioi (1 / (d : ℝ)), S χ ⌊y⌋₊ * (y : ℂ) ^ (-s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := lt_trans (by positivity) hy
    have hfl : ⌊(d : ℝ) * y⌋₊ / d = ⌊y⌋₊ := by
      rw [← Nat.floor_div_natCast, mul_div_cancel_left₀ _ hD.ne']
    simp only [g, hfl]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hD.le hy0.le, ofReal_natCast]
    ring
  have h1d : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hD]; exact_mod_cast hd
  have hIoo : ∀ y ∈ Ioo (1 / (d : ℝ)) 1, S χ ⌊y⌋₊ * (y : ℂ) ^ (-s - 1) = 0 := by
    intro y hy
    have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy.2
    simp [this, S_zero]
  have hIoc : IntegrableOn (fun y : ℝ => S χ ⌊y⌋₊ * (y : ℂ) ^ (-s - 1)) (Ioc (1 / (d : ℝ)) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (integrableOn_zero).congr_fun (fun y hy => (hIoo y hy).symm) measurableSet_Ioo
  have hsplit : ∫ y in Ioi (1 / (d : ℝ)), S χ ⌊y⌋₊ * (y : ℂ) ^ (-s - 1)
      = ∫ y in Ioi (1 : ℝ), S χ ⌊y⌋₊ * (y : ℂ) ^ (-s - 1) := by
    rw [← Ioc_union_Ioi_eq_Ioi h1d, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hIoc (integrableOn_S_floor_cpow hχ hs), integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hIoo, integral_zero, zero_add]
  have hmul : (d : ℂ) * (d : ℂ) ^ (-s - 1) = (d : ℂ) ^ (-s) := by
    have := mul_cpow_neg_sub_one hD s
    rwa [ofReal_natCast] at this
  have h2 : ∫ x in Ioi (1 : ℝ), g x = (d : ℂ) * ∫ y in Ioi (1 / (d : ℝ)), g (d * y) := by
    rw [hsub, Complex.real_smul, ← mul_assoc, ofReal_inv, ofReal_natCast,
      mul_inv_cancel₀ hDne, one_mul]
  rw [h2, hcongr, ← mul_assoc, hmul, hsplit]

/-- Mellin del testigo: `∫_1^∞ σ_{Q,χ}(⌊x⌋) x^{−s−1} dx = (1 − L(s,χ) P_{Q,χ}(s))/s`
para `Re s > 0` y `χ ≠ 1`. -/
theorem integral_sigma_floor {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∫ x in Ioi (1 : ℝ), sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)
      = (1 - DirichletCharacter.LFunction χ s * P χ Q s) / s := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hcint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hdint : ∀ d ∈ Finset.Icc 1 Q, IntegrableOn (fun x : ℝ =>
      ((moebius d : ℤ) : ℂ) * χ d * (S χ (⌊x⌋₊ / d) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := by
    intro d _
    refine Integrable.const_mul ?_ _
    exact integrableOn_bdd_cpow hs ((measurable_from_nat (f := fun n => S χ (n / d))).comp
      Nat.measurable_floor) (fun x => norm_S_le hχ _)
  have hpt : ∀ x ∈ Ioi (1 : ℝ), sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)
      = (x : ℂ) ^ (-s - 1) - ∑ d ∈ Finset.Icc 1 Q,
          ((moebius d : ℤ) : ℂ) * χ d * (S χ (⌊x⌋₊ / d) * (x : ℂ) ^ (-s - 1)) := by
    intro x _
    unfold sigma T
    rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hcint (integrable_finsetSum _ hdint),
    integral_finsetSum _ hdint]
  have hone : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) = 1 / s := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
    simp only [ofReal_one, one_cpow, sub_add_cancel]
    field_simp
  have hterm : ∀ d ∈ Finset.Icc 1 Q, ∫ x in Ioi (1 : ℝ),
      ((moebius d : ℤ) : ℂ) * χ d * (S χ (⌊x⌋₊ / d) * (x : ℂ) ^ (-s - 1))
        = ((moebius d : ℤ) : ℂ) * χ d * (d : ℂ) ^ (-s) * (DirichletCharacter.LFunction χ s / s) := by
    intro d hd
    rw [integral_const_mul, integral_S_floor_div hχ hs (Finset.mem_Icc.mp hd).1,
      LFunction_eq_integral hχ hs]
    field_simp
  rw [Finset.sum_congr rfl hterm, hone, ← Finset.sum_mul]
  unfold P
  field_simp

end MellinTestigo

/-! ## Energía y recíproco -/

section Energia

open MeasureTheory Set Complex Filter Topology

/-- Peso `w_k = 1/(k(k+1))`. -/
noncomputable def w (k : ℕ) : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1))

theorem w_succ (j : ℕ) : w (j + 1) = 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := by
  unfold w
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Energía de AMate para `χ`: `E_{Q,χ} = ∑_{k ≥ 1} ‖σ_{Q,χ}(k)‖² w_k`. -/
noncomputable def E (χ : DirichletCharacter ℂ N) (Q : ℕ) : ℝ :=
  ∑' k : ℕ, ‖sigma χ Q (k + 1)‖ ^ 2 * w (k + 1)

variable [NeZero N]

theorem integrableOn_sigma_sq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) :
    IntegrableOn (fun x : ℝ => ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) := by
  set C : ℝ := 1 + Q * N
  have hg : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
  refine hg.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      ((((measurable_from_nat (f := sigma χ Q)).comp Nat.measurable_floor).norm.pow_const 2).mul
        (measurable_id.pow_const (-2 : ℝ)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hp := Real.rpow_nonneg hx0.le (-2 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
    have hsq : ‖sigma χ Q ⌊x⌋₊‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sigma_le hχ Q _) 2
    exact mul_le_mul_of_nonneg_right hsq hp

theorem integral_sigma_sq_eq_E {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (Q : ℕ) :
    ∫ x in Ioi (1 : ℝ), ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) = E χ Q := by
  set f : ℝ → ℝ := fun x => ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) with hf
  set B : ℕ → Set ℝ := fun k => Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2) with hB
  have hU : (⋃ k, B k) = Set.Ici 1 := by
    ext t
    simp only [B, Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
    constructor
    · rintro ⟨k, hk, -⟩
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · intro ht
      have ht0 : 0 ≤ t := by linarith
      have hf1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
      refine ⟨⌊t⌋₊ - 1, ?_, ?_⟩
      · rw [Nat.cast_sub hf1]
        push_cast
        linarith [Nat.floor_le ht0]
      · rw [Nat.cast_sub hf1]
        push_cast
        linarith [Nat.lt_floor_add_one t]
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    simp only [Function.onFun, B]
    rw [Set.Ico_disjoint_Ico]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      exact le_trans (min_le_left _ _) (le_trans (by linarith) (le_max_right _ _))
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      exact le_trans (min_le_right _ _) (le_trans (by linarith) (le_max_left _ _))
  have hint' : IntegrableOn f (⋃ k, B k) := by
    rw [hU]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_sigma_sq hχ Q)
  have hsum := hasSum_integral_iUnion (fun k => measurableSet_Ico) hd hint'
  rw [hU, integral_Ici_eq_integral_Ioi] at hsum
  have hblock : ∀ k : ℕ, ∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2), f x
      = ‖sigma χ Q (k + 1)‖ ^ 2 * w (k + 1) := by
    intro k
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hcongr : ∀ x ∈ Ioo ((k : ℝ) + 1) ((k : ℝ) + 2),
        f x = ‖sigma χ Q (k + 1)‖ ^ 2 * x ^ (-2 : ℝ) := by
      intro x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hfl : ⌊x⌋₊ = k + 1 := by
        rw [Nat.floor_eq_iff hx0]
        push_cast
        constructor <;> linarith [hx.1, hx.2]
      simp only [f, hfl]
    rw [integral_Ico_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hcongr,
      integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      integral_rpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt hk0 (by positivity)⟩), w_succ,
      show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
    ring
  simp only [hblock] at hsum
  unfold E
  exact hsum.tsum_eq.symm

/-- Recíproco: un cero `ρ` de `L(s,χ)` con `Re ρ > 1/2` obliga a
`(2 Re ρ − 1)/‖ρ‖² ≤ E_{Q,χ} (Q+1)^{1 − 2 Re ρ}` para todo `Q`. -/
theorem cota_inferior_energia_cero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hL : DirichletCharacter.LFunction χ ρ = 0) (hβ : 1 / 2 < ρ.re) (Q : ℕ) :
    (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ≤ E χ Q * ((Q : ℝ) + 1) ^ (1 - 2 * ρ.re) := by
  have hρ0 : 0 < ρ.re := by linarith
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hβ
    linarith
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  set R : ℝ := (Q : ℝ) + 1 with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)]
  have hRpos : (0 : ℝ) < R := by linarith
  have hintC : IntegrableOn (fun x : ℝ => sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1)) (Ioi 1) :=
    integrableOn_bdd_cpow hρ0 ((measurable_from_nat (f := sigma χ Q)).comp Nat.measurable_floor)
      (fun x => norm_sigma_le hχ Q _)
  -- `σ_{Q,χ}(⌊x⌋) = 0` en `(1, Q + 1)`.
  have hsplit : ∫ x in Ioi (1 : ℝ), sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1)
      = ∫ x in Ioi R, sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1) := by
    rw [← Ioc_union_Ioi_eq_Ioi hR1,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hintC.mono_set Ioc_subset_Ioi_self) (hintC.mono_set (Ioi_subset_Ioi hR1)),
      integral_Ioc_eq_integral_Ioo,
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_, zero_add]
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hk1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1.le)
    have hkQ : ⌊x⌋₊ < Q + 1 := (Nat.floor_lt hx0).mpr (by push_cast; exact hx.2)
    rw [sigma_eq_zero hk1 (by omega)]
    simp
  have hval : ∫ x in Ioi R, sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1) = 1 / ρ := by
    rw [← hsplit, integral_sigma_floor hχ Q hρ0, hL, zero_mul, sub_zero]
  have hnorm_int : 1 / ‖ρ‖ ≤ ∫ x in Ioi R, ‖sigma χ Q ⌊x⌋₊‖ * x ^ (-ρ.re - 1) := by
    have h1 : 1 / ‖ρ‖ = ‖∫ x in Ioi R, sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1)‖ := by
      rw [hval, norm_div, norm_one]
    rw [h1]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans hRpos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
    rw [hre]
  have hint_sqR : IntegrableOn (fun x : ℝ => ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ)) (Ioi R) :=
    (integrableOn_sigma_sq hχ Q).mono_set (Ioi_subset_Ioi hR1)
  have hE_le : ∫ x in Ioi R, ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) ≤ E χ Q := by
    rw [← integral_sigma_sq_eq_E hχ Q]
    refine setIntegral_mono_set (integrableOn_sigma_sq hχ Q) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x (hx : 1 < x) => ?_)
      have hx0 : 0 ≤ x := by linarith
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0 _)
    · exact Eventually.of_forall fun x (hx : x ∈ Ioi R) => lt_of_le_of_lt hR1 hx
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (-2 * ρ.re)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hRpos
  set I_R : ℝ := R ^ (1 - 2 * ρ.re) / (2 * ρ.re - 1) with hIR_def
  have h2β_pos : 0 < 2 * ρ.re - 1 := by linarith
  have hIR_pos : 0 < I_R := div_pos (Real.rpow_pos_of_pos hRpos _) h2β_pos
  have hint_rpow_eq : ∫ x in Ioi R, x ^ (-2 * ρ.re) = I_R := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hRpos, hIR_def,
      show -2 * ρ.re + 1 = 1 - 2 * ρ.re by ring]
    have h1 : 1 - 2 * ρ.re ≠ 0 := by linarith
    have h2 : 2 * ρ.re - 1 ≠ 0 := h2β_pos.ne'
    field_simp
    ring
  set t : ℝ := ‖ρ‖ * I_R with ht_def
  have ht_pos : 0 < t := mul_pos hρnorm hIR_pos
  have hint_abs : IntegrableOn (fun x : ℝ => ‖sigma χ Q ⌊x⌋₊‖ * x ^ (-ρ.re - 1)) (Ioi R) := by
    have hnorm : IntegrableOn
        (fun x : ℝ => ‖sigma χ Q ⌊x⌋₊ * (x : ℂ) ^ (-ρ - 1)‖) (Ioi R) :=
      (hintC.mono_set (Ioi_subset_Ioi hR1)).norm
    refine hnorm.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only
    have hx0 : 0 < x := lt_trans hRpos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-ρ - 1).re = -ρ.re - 1 := by simp
    rw [hre]
  have hMaj : IntegrableOn
      (fun x : ℝ => (t / 2) * (‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ))
        + (1 / (2 * t)) * x ^ (-2 * ρ.re)) (Ioi R) :=
    (hint_sqR.const_mul (t / 2)).add (hint_rpow.const_mul (1 / (2 * t)))
  have hpt : ∀ x ∈ Ioi R, ‖sigma χ Q ⌊x⌋₊‖ * x ^ (-ρ.re - 1)
      ≤ (t / 2) * (‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ)) + (1 / (2 * t)) * x ^ (-2 * ρ.re) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hRpos hx
    set A : ℝ := ‖sigma χ Q ⌊x⌋₊‖ * x ^ (-1 : ℝ)
    set B : ℝ := x ^ (-ρ.re)
    have hAB : ‖sigma χ Q ⌊x⌋₊‖ * x ^ (-ρ.re - 1) = A * B := by
      simp only [A, B, mul_assoc]
      rw [← Real.rpow_add hx0, show (-1 : ℝ) + -ρ.re = -ρ.re - 1 by ring]
    have hx2 : (x ^ (-1 : ℝ)) ^ 2 = x ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hA2 : A ^ 2 = ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) := by
      simp only [A, mul_pow, hx2]
    have hB2 : B ^ 2 = x ^ (-2 * ρ.re) := by
      simp only [B]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      ring_nf
    rw [hAB, ← hA2, ← hB2]
    have hsq : 0 ≤ (t * A - B) ^ 2 := sq_nonneg _
    have hcomb : (t / 2) * A ^ 2 + (1 / (2 * t)) * B ^ 2 - A * B = (t * A - B) ^ 2 / (2 * t) := by
      field_simp
      ring
    have hpos_div : 0 ≤ (t * A - B) ^ 2 / (2 * t) := div_nonneg hsq (by positivity)
    linarith [hcomb]
  have hint_le := setIntegral_mono_on hint_abs hMaj measurableSet_Ioi hpt
  rw [integral_add (hint_sqR.const_mul _) (hint_rpow.const_mul _),
    integral_const_mul, integral_const_mul, hint_rpow_eq] at hint_le
  have hstep1 : 1 / ‖ρ‖ ≤ (t / 2) * E χ Q + (1 / (2 * t)) * I_R := by
    have h1 := hnorm_int.trans hint_le
    have h2 : (t / 2) * ∫ x in Ioi R, ‖sigma χ Q ⌊x⌋₊‖ ^ 2 * x ^ (-2 : ℝ) ≤ (t / 2) * E χ Q :=
      mul_le_mul_of_nonneg_left hE_le (by positivity)
    linarith
  have hcancel : (1 / (2 * t)) * I_R = 1 / (2 * ‖ρ‖) := by
    rw [ht_def]
    have hIR_ne : I_R ≠ 0 := hIR_pos.ne'
    have hρ_ne' : ‖ρ‖ ≠ 0 := hρnorm.ne'
    field_simp
  rw [hcancel] at hstep1
  have hhalf : 1 / ‖ρ‖ - 1 / (2 * ‖ρ‖) = 1 / (2 * ‖ρ‖) := by
    have hρ_ne' : ‖ρ‖ ≠ 0 := hρnorm.ne'
    field_simp
    ring
  have hstep2 : 1 / (2 * ‖ρ‖) ≤ (‖ρ‖ * I_R / 2) * E χ Q := by
    rw [ht_def] at hstep1
    linarith [hhalf]
  have hstep3 : 1 ≤ ‖ρ‖ ^ 2 * I_R * E χ Q := by
    have hm := mul_le_mul_of_nonneg_left hstep2 (show 0 ≤ 2 * ‖ρ‖ by positivity)
    have hL1 : (2 * ‖ρ‖) * (1 / (2 * ‖ρ‖)) = 1 := by field_simp
    have hR1' : (2 * ‖ρ‖) * ((‖ρ‖ * I_R / 2) * E χ Q) = ‖ρ‖ ^ 2 * I_R * E χ Q := by ring
    linarith
  rw [hIR_def] at hstep3
  rw [div_le_iff₀ (sq_pos_of_pos hρnorm)]
  have hm := mul_le_mul_of_nonneg_left hstep3 h2β_pos.le
  have hR2 : (2 * ρ.re - 1) * (‖ρ‖ ^ 2 * (R ^ (1 - 2 * ρ.re) / (2 * ρ.re - 1)) * E χ Q)
      = E χ Q * R ^ (1 - 2 * ρ.re) * ‖ρ‖ ^ 2 := by
    have h2 : 2 * ρ.re - 1 ≠ 0 := h2β_pos.ne'
    field_simp
  linarith

/-- Recíproco cofinal: si para `θ ≥ 1/2` y cada `ε > 0` hay `C` con `E_{Q,χ} ≤ C Q^{2θ−1+ε}` en
valores arbitrariamente grandes de `Q`, entonces `L(s,χ)` no se anula en `Re s > θ`. -/
theorem sin_ceros_de_energia_cofinal {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ,
      Q₀ ≤ Q ∧ E χ Q ≤ C * (Q : ℝ) ^ (2 * θ - 1 + ε)) :
    ∀ ρ : ℂ, θ < ρ.re → DirichletCharacter.LFunction χ ρ ≠ 0 := by
  intro ρ hρ hL
  have hβ : 1 / 2 < ρ.re := lt_of_le_of_lt hθ hρ
  set δ : ℝ := ρ.re - θ with hδ_def
  have hδ : 0 < δ := by linarith
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hβ
    linarith
  have hρnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  set a : ℝ := (2 * ρ.re - 1) / ‖ρ‖ ^ 2 with ha_def
  have ha_pos : 0 < a := div_pos (by linarith) (sq_pos_of_pos hρnorm)
  obtain ⟨C, hC⟩ := hE δ hδ
  set C' : ℝ := max C 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'C : C ≤ C' := le_max_left _ _
  set M : ℝ := (C' / a + 1) ^ (1 / δ) with hM_def
  have hbase1 : 1 < C' / a + 1 := by
    have : 0 < C' / a := div_pos (by linarith) ha_pos
    linarith
  set Q₀ : ℕ := max (Nat.ceil M + 1) 2
  obtain ⟨Q, hQQ₀, hEQ⟩ := hC Q₀
  have hQ2 : 2 ≤ Q := le_trans (le_max_right _ _) hQQ₀
  have hQpos : (0 : ℝ) < Q := by positivity
  have hQM : M < (Q : ℝ) := by
    have h1 : Nat.ceil M + 1 ≤ Q := le_trans (le_max_left _ _) hQQ₀
    have h2 : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have h3 : (Nat.ceil M : ℝ) + 1 ≤ (Q : ℝ) := by exact_mod_cast h1
    linarith
  have hQδ_gt : C' / a + 1 < (Q : ℝ) ^ δ := by
    have h1 : M ^ δ < (Q : ℝ) ^ δ := Real.rpow_lt_rpow (by positivity) hQM hδ
    have h2 : M ^ δ = C' / a + 1 := by
      rw [hM_def, ← Real.rpow_mul (by linarith), one_div_mul_cancel hδ.ne', Real.rpow_one]
    linarith
  have hlow := cota_inferior_energia_cero hχ hL hβ Q
  rw [← ha_def] at hlow
  have hE0 : 0 ≤ E χ Q := by
    unfold E
    exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (by unfold w; positivity)
  have hmono : ((Q : ℝ) + 1) ^ (1 - 2 * ρ.re) ≤ (Q : ℝ) ^ (1 - 2 * ρ.re) :=
    Real.rpow_le_rpow_of_nonpos hQpos (by linarith) (by linarith)
  have hprod_le : a ≤ C' * (Q : ℝ) ^ (-δ) := by
    calc a ≤ E χ Q * ((Q : ℝ) + 1) ^ (1 - 2 * ρ.re) := hlow
      _ ≤ E χ Q * (Q : ℝ) ^ (1 - 2 * ρ.re) := mul_le_mul_of_nonneg_left hmono hE0
      _ ≤ (C * (Q : ℝ) ^ (2 * θ - 1 + δ)) * (Q : ℝ) ^ (1 - 2 * ρ.re) :=
          mul_le_mul_of_nonneg_right hEQ (Real.rpow_nonneg hQpos.le _)
      _ ≤ (C' * (Q : ℝ) ^ (2 * θ - 1 + δ)) * (Q : ℝ) ^ (1 - 2 * ρ.re) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC'C (Real.rpow_nonneg hQpos.le _))
            (Real.rpow_nonneg hQpos.le _)
      _ = C' * ((Q : ℝ) ^ (2 * θ - 1 + δ) * (Q : ℝ) ^ (1 - 2 * ρ.re)) := by ring
      _ = C' * (Q : ℝ) ^ (-δ) := by
          rw [← Real.rpow_add hQpos]
          congr 2
          rw [hδ_def]
          ring
  have haQ_le : a * (Q : ℝ) ^ δ ≤ C' := by
    have hm := mul_le_mul_of_nonneg_right hprod_le (Real.rpow_nonneg hQpos.le δ)
    have hR : C' * (Q : ℝ) ^ (-δ) * (Q : ℝ) ^ δ = C' := by
      rw [mul_assoc, ← Real.rpow_add hQpos, neg_add_cancel, Real.rpow_zero, mul_one]
    linarith
  have haQ_gt : C' < a * (Q : ℝ) ^ δ := by
    have hm := mul_lt_mul_of_pos_left hQδ_gt ha_pos
    have hL' : a * (C' / a + 1) = C' + a := by field_simp
    linarith
  linarith

/-- Criterio de AMate para `χ`: si `E_{Q,χ} ≤ C_ε Q^ε` en valores arbitrariamente grandes
de `Q`, entonces `L(s,χ) ≠ 0` en `Re s > 1/2` (la forma de GRH de `Statements.lean`). -/
theorem LFunction_ne_zero_de_energia_cofinal {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q₀ : ℕ, ∃ Q : ℕ, Q₀ ≤ Q ∧ E χ Q ≤ C * (Q : ℝ) ^ ε) :
    ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
  refine sin_ceros_de_energia_cofinal hχ le_rfl fun ε hε => ?_
  obtain ⟨C, hC⟩ := hE ε hε
  refine ⟨C, fun Q₀ => ?_⟩
  obtain ⟨Q, hQ, hEQ⟩ := hC Q₀
  refine ⟨Q, hQ, ?_⟩
  rw [show 2 * (1 / 2 : ℝ) - 1 + ε = ε by ring]
  exact hEQ

end Energia

end AMate.Dirichlet
