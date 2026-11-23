import AMateEnergia.Definiciones

/-!
# Propiedades elementales del testigo

Identidades finitas, las series `∑ u_d(k) w_k = log d / d`, `t_Q = ⟨χ, φ_Q⟩` y
`‖h_Q‖² = log 2 / Q`, y la cota lineal incondicional del estado 45, §7.
Ninguna usa ceros de `ζ`.
-/

open Finset Filter Topology

namespace AMate

/-! ### Cotas puntuales -/

theorem u_nonneg (d k : ℕ) : 0 ≤ u d k := Int.fract_nonneg _

theorem u_lt_one (d k : ℕ) : u d k < 1 := Int.fract_lt_one _

theorem abs_mu_le_one (d : ℕ) : |mu d| ≤ 1 := by
  unfold mu
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem abs_u_le_one (d k : ℕ) : |u d k| ≤ 1 := by
  rw [abs_of_nonneg (u_nonneg d k)]
  exact (u_lt_one d k).le

theorem abs_h_le (Q k : ℕ) : |h Q k| ≤ 3 := by
  unfold h
  calc |2 * u (2 * Q) k - u Q k| ≤ |2 * u (2 * Q) k| + |u Q k| := abs_sub _ _
    _ = 2 * |u (2 * Q) k| + |u Q k| := by rw [abs_mul, abs_two]
    _ ≤ 2 * 1 + 1 := by gcongr <;> exact abs_u_le_one _ _
    _ = 3 := by norm_num

theorem abs_phi_le (Q k : ℕ) : |phi Q k| ≤ 1 + Q + Q * |m Q| := by
  unfold phi
  have hsum : |∑ d ∈ Icc 1 Q, mu d * u d k| ≤ Q := by
    calc |∑ d ∈ Icc 1 Q, mu d * u d k| ≤ ∑ d ∈ Icc 1 Q, |mu d * u d k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Icc 1 Q, (1 : ℝ) := by
          gcongr with d hd
          rw [abs_mul]
          exact mul_le_one₀ (abs_mu_le_one d) (abs_nonneg _) (abs_u_le_one d k)
      _ = Q := by simp
  have hlast : |(Q : ℝ) * m Q * u Q k| ≤ Q * |m Q| := by
    rw [abs_mul, abs_mul, Nat.abs_cast]
    calc (Q : ℝ) * |m Q| * |u Q k| ≤ Q * |m Q| * 1 := by
          gcongr
          exact abs_u_le_one Q k
      _ = Q * |m Q| := mul_one _
  calc |1 + ∑ d ∈ Icc 1 Q, mu d * u d k - (Q : ℝ) * m Q * u Q k|
      ≤ |1 + ∑ d ∈ Icc 1 Q, mu d * u d k| + |(Q : ℝ) * m Q * u Q k| := abs_sub _ _
    _ ≤ (|(1 : ℝ)| + |∑ d ∈ Icc 1 Q, mu d * u d k|) + |(Q : ℝ) * m Q * u Q k| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ (1 + Q) + Q * |m Q| := by
        rw [abs_one]
        gcongr
    _ = 1 + Q + Q * |m Q| := by ring

/-- El testigo está acotado para cada `Q` fijo: `0 ≤ u_d < 1` y hay finitos sumandos. -/
theorem sigma_acotado (Q : ℕ) : ∃ C : ℝ, ∀ k : ℕ, |sigma Q k| ≤ C := by
  refine ⟨1 + Q + Q * |m Q| + 3 * |gam Q|, fun k => ?_⟩
  unfold sigma
  calc |phi Q k - gam Q * h Q k| ≤ |phi Q k| + |gam Q * h Q k| := abs_sub _ _
    _ = |phi Q k| + |gam Q| * |h Q k| := by rw [abs_mul]
    _ ≤ (1 + Q + Q * |m Q|) + |gam Q| * 3 := by
        gcongr
        · exact abs_phi_le Q k
        · exact abs_h_le Q k
    _ = 1 + Q + Q * |m Q| + 3 * |gam Q| := by ring

/-! ### Convergencia de la energía -/

theorem w_nonneg (k : ℕ) : 0 ≤ w k := by
  unfold w
  positivity

theorem summable_w_succ : Summable (fun k : ℕ => w (k + 1)) := by
  have h2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_nonneg_of_le (fun k => w_nonneg (k + 1)) (fun k => ?_) h2
  unfold w
  push_cast
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

/-- La serie de la energía converge: el testigo está acotado y `∑ w_k` converge. -/
theorem summable_energia (Q : ℕ) :
    Summable (fun k : ℕ => sigma Q (k + 1) ^ 2 * w (k + 1)) := by
  obtain ⟨C, hC⟩ := sigma_acotado Q
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (w_nonneg _))
    (fun k => ?_) (summable_w_succ.mul_left (C ^ 2))
  have h1 : sigma Q (k + 1) ^ 2 ≤ C ^ 2 := by
    have hk := hC (k + 1)
    have h0 : 0 ≤ |sigma Q (k + 1)| := abs_nonneg _
    nlinarith [sq_abs (sigma Q (k + 1))]
  exact mul_le_mul_of_nonneg_right h1 (w_nonneg _)

/-! ### Identidad de Möbius y parte fraccionaria -/

/-- `∑_{d ≤ N} μ(d) ⌊N/d⌋ = 1` para `N ≥ 1`. -/
theorem sum_moebius_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Icc 1 N, mu d * ((N / d : ℕ) : ℝ) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.moebius N
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  have h1 : ∑ n ∈ Finset.Ioc 0 N, (1 : ArithmeticFunction ℤ) n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb1
      simp [ArithmeticFunction.one_apply_ne hb1]
    · intro h1
      exfalso
      exact h1 (by simp; omega)
  rw [h1] at h
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc] at h
  unfold mu
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_one, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h2
  exact h2.symm

/-- La misma identidad truncada en cualquier `Q ≥ k`. -/
theorem sum_moebius_div_le {k Q : ℕ} (hk1 : 1 ≤ k) (hkQ : k ≤ Q) :
    ∑ d ∈ Icc 1 Q, mu d * ((k / d : ℕ) : ℝ) = 1 := by
  rw [← sum_moebius_div k hk1]
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d hdQ hdk
    simp only [Finset.mem_Icc, not_and, not_le] at hdQ hdk
    have : k / d = 0 := Nat.div_eq_of_lt (hdk hdQ.1)
    simp [this]

/-- `u_d(k) = k/d − ⌊k/d⌋`. -/
theorem u_eq (d k : ℕ) (hd : 1 ≤ d) : u d k = (k : ℝ) / d - ((k / d : ℕ) : ℝ) := by
  unfold u
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : ((k % d : ℕ) : ℝ) + d * ((k / d : ℕ) : ℝ) = k := by
    exact_mod_cast Nat.mod_add_div k d
  field_simp
  linear_combination h

/-! ### El testigo se anula antes de `Q` -/

theorem h_eq_zero {Q k : ℕ} (hQ : 1 ≤ Q) (hk : k < Q) : h Q k = 0 := by
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have huQ : u Q k = (k : ℝ) / Q := by
    rw [u_eq Q k hQ, Nat.div_eq_of_lt hk]
    simp
  have hu2Q : u (2 * Q) k = (k : ℝ) / (2 * Q) := by
    rw [u_eq (2 * Q) k (by omega), Nat.div_eq_of_lt (by omega)]
    push_cast
    simp
  unfold h
  rw [hu2Q, huQ]
  field_simp
  ring

theorem phi_eq_zero {Q k : ℕ} (hk1 : 1 ≤ k) (hk : k < Q) : phi Q k = 0 := by
  have hQ1 : 1 ≤ Q := by omega
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have huQ : u Q k = (k : ℝ) / Q := by
    rw [u_eq Q k hQ1, Nat.div_eq_of_lt hk]
    simp
  have hsum : ∑ d ∈ Icc 1 Q, mu d * u d k
      = k * m Q - ∑ d ∈ Icc 1 Q, mu d * ((k / d : ℕ) : ℝ) := by
    unfold m
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [u_eq d k hd.1]
    ring
  unfold phi
  rw [hsum, sum_moebius_div_le hk1 hk.le, huQ]
  field_simp
  ring

/-- Estado 45, (2.2): `σ_Q(k) = 0` para `1 ≤ k < Q`. -/
theorem sigma_eq_zero {Q k : ℕ} (hQ : 2 ≤ Q) (hk1 : 1 ≤ k) (hk : k < Q) :
    sigma Q k = 0 := by
  unfold sigma
  rw [phi_eq_zero hk1 hk, h_eq_zero (by omega) hk]
  ring

/-! ### Series del peso -/

theorem w_eq (k : ℕ) (hk : 1 ≤ k) : w k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  unfold w
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Cola del peso: `∑_{k ≥ Q} w_k = 1/Q`. -/
theorem hasSum_w_tail (Q : ℕ) (hQ : 1 ≤ Q) : HasSum (fun j => w (j + Q)) (1 / (Q : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => w_nonneg _)]
  have hpart : ∀ n : ℕ, ∑ j ∈ range n, w (j + Q) = 1 / (Q : ℝ) - 1 / ((n : ℝ) + Q) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, w_eq (n + Q) (by omega)]
      push_cast
      ring
  simp_rw [hpart]
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + Q)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by positivity) (fun n => ?_)
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  simpa using (tendsto_const_nhds (x := 1 / (Q : ℝ))).sub h0

theorem hasSum_w_succ : HasSum (fun j => w (j + 1)) 1 := by
  simpa using hasSum_w_tail 1 le_rfl

theorem w_succ (j : ℕ) : w (j + 1) = 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := by
  rw [w_eq (j + 1) (by omega)]
  push_cast
  ring

/-- `∑_{k ≤ n} u_d(k) w_k = (H_n − H_{⌊n/d⌋})/d − u_d(n)/(n+1)`. -/
theorem partial_u_w (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    ∑ j ∈ range n, u d (j + 1) * w (j + 1)
      = (1 / (d : ℝ)) * ((harmonic n : ℝ) - (harmonic (n / d) : ℝ)) - u d n / ((n : ℝ) + 1) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  induction n with
  | zero => simp [u]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, u_eq d (n + 1) hd, u_eq d n hd, w_succ, harmonic_succ]
    by_cases hdiv : d ∣ n + 1
    · have hq : d * (n / d + 1) = n + 1 := by
        have := Nat.mul_div_cancel' hdiv
        rw [Nat.succ_div, if_pos hdiv] at this
        exact this
      have hqR : (d : ℝ) * (((n / d : ℕ) : ℝ) + 1) = (n : ℝ) + 1 := by exact_mod_cast hq
      simp only [Nat.succ_div, if_pos hdiv, harmonic_succ]
      have hn : (n : ℝ) = (d : ℝ) * (((n / d : ℕ) : ℝ) + 1) - 1 := by linarith
      push_cast
      rw [hn]
      have hq1 : ((n / d : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · simp only [Nat.succ_div, if_neg hdiv, add_zero]
      push_cast
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring

theorem tendsto_div_floor_div (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n / d : ℕ) : ℝ)) atTop (𝓝 (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : Tendsto (fun n : ℕ => (n : ℝ) / d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hdpos
  have hfl := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hx
  have hfl' : Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / ((n : ℝ) / d)) atTop (𝓝 1) := by
    refine hfl.congr (fun n => ?_)
    simp only [Function.comp, Nat.floor_div_eq_div]
  have hlim := (tendsto_const_nhds (x := (d : ℝ))).div hfl' one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop d] with n hn
  have hq : 1 ≤ n / d := (Nat.one_le_div_iff (by omega)).mpr hn
  have hq0 : ((n / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  simp only [Pi.div_apply]
  field_simp

theorem tendsto_harmonic_sub_harmonic_div (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) - (harmonic (n / d) : ℝ)) atTop (𝓝 (Real.log d)) := by
  have hγ := Real.tendsto_harmonic_sub_log
  have hdiv : Tendsto (fun n : ℕ => n / d) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have h1 := hγ.sub (hγ.comp hdiv)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : Tendsto (fun n : ℕ => Real.log n - Real.log ((n / d : ℕ) : ℝ)) atTop
      (𝓝 (Real.log d)) := by
    refine ((tendsto_div_floor_div d hd).log hd0).congr' ?_
    filter_upwards [eventually_ge_atTop d] with n hn
    have hq : 1 ≤ n / d := (Nat.one_le_div_iff (by omega)).mpr hn
    rw [Real.log_div (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))]
  have h3 := h1.add h2
  simp only [sub_self, zero_add] at h3
  refine h3.congr (fun n => ?_)
  simp only [Function.comp]
  ring

/-- Estado 45: `∑_{k ≥ 1} u_d(k) w_k = log d / d`. -/
theorem hasSum_u_w (d : ℕ) (hd : 1 ≤ d) :
    HasSum (fun j => u d (j + 1) * w (j + 1)) (Real.log d / d) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => mul_nonneg (u_nonneg _ _) (w_nonneg _))]
  simp_rw [partial_u_w d hd]
  have h4 : Tendsto (fun n : ℕ => u d n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => div_nonneg (u_nonneg _ _) (by positivity)) (fun n => ?_)
    exact div_le_div_of_nonneg_right (u_lt_one _ _).le (by positivity)
  have := ((tendsto_harmonic_sub_harmonic_div d hd).const_mul (1 / (d : ℝ))).sub h4
  convert this using 2
  ring

/-! ### Cotas de `φ_Q` y valores de `h_Q` -/

theorem u_one (k : ℕ) : u 1 k = 0 := by
  unfold u
  simp

theorem abs_one_add_sum_le (Q k : ℕ) (hQ : 1 ≤ Q) :
    |1 + ∑ d ∈ Icc 1 Q, mu d * u d k| ≤ Q := by
  have hsplit : ∑ d ∈ Icc 1 Q, mu d * u d k = ∑ d ∈ Ioc 1 Q, mu d * u d k := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hQ]
    simp [u_one]
  rw [hsplit]
  have hb : |∑ d ∈ Ioc 1 Q, mu d * u d k| ≤ (Q : ℝ) - 1 := by
    calc |∑ d ∈ Ioc 1 Q, mu d * u d k| ≤ ∑ d ∈ Ioc 1 Q, |mu d * u d k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Ioc 1 Q, (1 : ℝ) := by
          gcongr with d hd
          rw [abs_mul]
          exact mul_le_one₀ (abs_mu_le_one d) (abs_nonneg _) (abs_u_le_one d k)
      _ = (Q : ℝ) - 1 := by
          simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
          rw [Nat.cast_sub hQ]
          simp
  calc |1 + ∑ d ∈ Ioc 1 Q, mu d * u d k| ≤ |(1 : ℝ)| + |∑ d ∈ Ioc 1 Q, mu d * u d k| :=
        abs_add_le _ _
    _ ≤ 1 + ((Q : ℝ) - 1) := by
        rw [abs_one]
        gcongr
    _ = Q := by ring

/-- `Q m_Q = 1 + ∑_{d ≤ Q} μ(d) u_d(Q)`. -/
theorem Q_mul_m (Q : ℕ) (hQ : 1 ≤ Q) : (Q : ℝ) * m Q = 1 + ∑ d ∈ Icc 1 Q, mu d * u d Q := by
  have h1 := sum_moebius_div Q hQ
  have hu : ∑ d ∈ Icc 1 Q, mu d * u d Q
      = ∑ d ∈ Icc 1 Q, (Q : ℝ) * (mu d / d) - ∑ d ∈ Icc 1 Q, mu d * ((Q / d : ℕ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [u_eq d Q hd.1]
    ring
  unfold m
  rw [Finset.mul_sum, hu, h1]
  ring

/-- Estado 45, §7: `|φ_Q(k)| ≤ 2Q`. -/
theorem abs_phi_le_two (Q k : ℕ) (hQ : 1 ≤ Q) : |phi Q k| ≤ 2 * Q := by
  have h1 := abs_one_add_sum_le Q k hQ
  have h2 : |(Q : ℝ) * m Q| ≤ Q := by
    rw [Q_mul_m Q hQ]
    exact abs_one_add_sum_le Q Q hQ
  have h3 := abs_u_le_one Q k
  unfold phi
  calc |1 + ∑ d ∈ Icc 1 Q, mu d * u d k - (Q : ℝ) * m Q * u Q k|
      ≤ |1 + ∑ d ∈ Icc 1 Q, mu d * u d k| + |(Q : ℝ) * m Q * u Q k| := abs_sub _ _
    _ = |1 + ∑ d ∈ Icc 1 Q, mu d * u d k| + |(Q : ℝ) * m Q| * |u Q k| := by rw [abs_mul]
    _ ≤ Q + Q * 1 := by gcongr
    _ = 2 * Q := by ring

/-- `h_Q` solo toma los valores `0` y `1`. -/
theorem h_cases (Q k : ℕ) (hQ : 1 ≤ Q) : h Q k = 0 ∨ h Q k = 1 := by
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmod : k % Q = (k % (2 * Q)) % Q := (Nat.mod_mod_of_dvd k (Dvd.intro_left 2 rfl)).symm
  have hr2 : k % (2 * Q) < 2 * Q := Nat.mod_lt _ (by omega)
  unfold h u
  rw [Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod, hmod]
  by_cases hrQ : k % (2 * Q) < Q
  · left
    rw [Nat.mod_eq_of_lt hrQ]
    push_cast
    field_simp
    ring
  · right
    have hsub : k % (2 * Q) % Q = k % (2 * Q) - Q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub, Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring

theorem h_sq (Q k : ℕ) (hQ : 1 ≤ Q) : h Q k ^ 2 = h Q k := by
  rcases h_cases Q k hQ with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num

/-! ### Las series de `h_Q` y de `φ_Q` -/

/-- `∑_{k ≥ 1} h_Q(k) w_k = log 2 / Q`. -/
theorem hasSum_h_w (Q : ℕ) (hQ : 1 ≤ Q) :
    HasSum (fun j => h Q (j + 1) * w (j + 1)) (Real.log 2 / Q) := by
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 := (hasSum_u_w (2 * Q) (by omega)).mul_left 2
  have h1 := hasSum_u_w Q hQ
  have h3 := h2.sub h1
  have hf : (fun j => h Q (j + 1) * w (j + 1))
      = (fun j => 2 * (u (2 * Q) (j + 1) * w (j + 1)) - u Q (j + 1) * w (j + 1)) := by
    funext j
    unfold h
    ring
  have hval : Real.log 2 / Q
      = 2 * (Real.log ((2 * Q : ℕ) : ℝ) / ((2 * Q : ℕ) : ℝ)) - Real.log Q / Q := by
    push_cast
    rw [Real.log_mul two_ne_zero hQ0]
    field_simp
    ring
  rw [hf, hval]
  exact h3

/-- Estado 45, (2.1): `t_Q = ⟨χ, φ_Q⟩`. -/
theorem hasSum_phi_w (Q : ℕ) (hQ : 1 ≤ Q) :
    HasSum (fun j => phi Q (j + 1) * w (j + 1)) (t Q) := by
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum : HasSum (fun j => ∑ d ∈ Icc 1 Q, mu d * (u d (j + 1) * w (j + 1)))
      (∑ d ∈ Icc 1 Q, mu d * (Real.log d / d)) :=
    hasSum_sum (fun d hd => (hasSum_u_w d (Finset.mem_Icc.mp hd).1).mul_left (mu d))
  have hQu := (hasSum_u_w Q hQ).mul_left ((Q : ℝ) * m Q)
  have htot := (hasSum_w_succ.add hsum).sub hQu
  have hf : (fun j => phi Q (j + 1) * w (j + 1))
      = (fun j => w (j + 1) + ∑ d ∈ Icc 1 Q, mu d * (u d (j + 1) * w (j + 1))
          - (Q : ℝ) * m Q * (u Q (j + 1) * w (j + 1))) := by
    funext j
    unfold phi
    simp only [add_mul, sub_mul, one_mul, Finset.sum_mul, mul_assoc]
  have hlog : ∀ d ∈ Icc 1 Q, mu d / d * Real.log ((Q : ℝ) / d)
      = mu d / d * Real.log Q - mu d * (Real.log d / d) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp at hd; omega)
    rw [Real.log_div hQ0 hd0]
    ring
  have hval : t Q = 1 + ∑ d ∈ Icc 1 Q, mu d * (Real.log d / d)
      - (Q : ℝ) * m Q * (Real.log Q / Q) := by
    unfold t
    rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib, ← Finset.sum_mul]
    unfold m
    field_simp
    ring
  rw [hf, hval]
  exact htot

/-- Desplazamiento de índices cuando los primeros términos se anulan. -/
theorem hasSum_shift {F : ℕ → ℝ} {Q : ℕ} (hQ : 1 ≤ Q) (hF : ∀ k, 1 ≤ k → k < Q → F k = 0)
    {a : ℝ} (hs : HasSum (fun j => F (j + 1)) a) : HasSum (fun i => F (i + Q)) a := by
  have h0 : ∑ i ∈ range (Q - 1), F (i + 1) = 0 :=
    Finset.sum_eq_zero (fun i hi => hF _ (by omega) (by simp at hi; omega))
  have h1 := (hasSum_nat_add_iff' (f := fun j => F (j + 1)) (Q - 1)).mpr hs
  rw [h0, sub_zero] at h1
  have hf : (fun i => F (i + Q)) = (fun n => F (n + (Q - 1) + 1)) := by
    funext i
    congr 1
    omega
  rw [hf]
  exact h1

/-! ### Cota lineal de la energía -/

theorem summable_phi_sq (Q : ℕ) (hQ : 1 ≤ Q) :
    Summable (fun j => phi Q (j + 1) ^ 2 * w (j + 1)) := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (w_nonneg _)) (fun j => ?_)
    (summable_w_succ.mul_left ((2 * Q : ℝ) ^ 2))
  have hb := abs_phi_le_two Q (j + 1) hQ
  have h0 : 0 ≤ |phi Q (j + 1)| := abs_nonneg _
  have h1 : phi Q (j + 1) ^ 2 ≤ (2 * Q : ℝ) ^ 2 := by nlinarith [sq_abs (phi Q (j + 1))]
  exact mul_le_mul_of_nonneg_right h1 (w_nonneg _)

/-- Estado 45, (7.1): cota lineal incondicional `E_Q ≤ 8 (1 + 1/log 2) Q`. -/
theorem E_le_lineal {Q : ℕ} (hQ : 2 ≤ Q) :
    E Q ≤ 8 * (1 + 1 / Real.log 2) * (Q : ℝ) := by
  have hQ1 : 1 ≤ Q := by omega
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : Real.log 2 ≠ 0 := hL.ne'
  -- `b = ‖φ_Q‖²` y sus versiones desplazadas a `k ≥ Q`
  set b := ∑' j, phi Q (j + 1) ^ 2 * w (j + 1) with hbdef
  have hb : HasSum (fun j => phi Q (j + 1) ^ 2 * w (j + 1)) b := (summable_phi_sq Q hQ1).hasSum
  have hb' : HasSum (fun i => phi Q (i + Q) ^ 2 * w (i + Q)) b :=
    hasSum_shift (F := fun k => phi Q k ^ 2 * w k) hQ1
      (fun k hk1 hk => by simp [phi_eq_zero hk1 hk]) hb
  have ha' : HasSum (fun i => phi Q (i + Q) * w (i + Q)) (t Q) :=
    hasSum_shift (F := fun k => phi Q k * w k) hQ1
      (fun k hk1 hk => by simp [phi_eq_zero hk1 hk]) (hasSum_phi_w Q hQ1)
  have hc' := hasSum_w_tail Q hQ1
  -- `b ≤ 4Q`
  have hpt4 : ∀ i, phi Q (i + Q) ^ 2 * w (i + Q) ≤ (2 * Q : ℝ) ^ 2 * w (i + Q) := by
    intro i
    have h0 := abs_phi_le_two Q (i + Q) hQ1
    have h1 : phi Q (i + Q) ^ 2 ≤ (2 * Q : ℝ) ^ 2 := by
      nlinarith [sq_abs (phi Q (i + Q)), abs_nonneg (phi Q (i + Q))]
    exact mul_le_mul_of_nonneg_right h1 (w_nonneg _)
  have hb4 : b ≤ 4 * Q := by
    have hle := hasSum_le hpt4 hb' (hc'.mul_left ((2 * Q : ℝ) ^ 2))
    have e : (2 * Q : ℝ) ^ 2 * (1 / Q) = 4 * Q := by
      field_simp
      ring
    linarith
  -- Cauchy–Schwarz: `Q t_Q² ≤ b`
  have hCS : (Q : ℝ) * t Q ^ 2 ≤ b := by
    set lam := (Q : ℝ) * t Q with hlam
    have hq := (hb'.sub (ha'.mul_left (2 * lam))).add (hc'.mul_left (lam ^ 2))
    have hnn : 0 ≤ b - 2 * lam * t Q + lam ^ 2 * (1 / Q) := by
      refine hq.nonneg (fun i => ?_)
      show 0 ≤ phi Q (i + Q) ^ 2 * w (i + Q) - 2 * lam * (phi Q (i + Q) * w (i + Q))
        + lam ^ 2 * w (i + Q)
      have e : phi Q (i + Q) ^ 2 * w (i + Q) - 2 * lam * (phi Q (i + Q) * w (i + Q))
          + lam ^ 2 * w (i + Q) = (phi Q (i + Q) - lam) ^ 2 * w (i + Q) := by ring
      rw [e]
      exact mul_nonneg (sq_nonneg _) (w_nonneg _)
    have e : b - 2 * lam * t Q + lam ^ 2 * (1 / Q) = b - Q * t Q ^ 2 := by
      rw [hlam]
      field_simp
      ring
    linarith
  -- la energía, término a término
  have hE : HasSum (fun j => sigma Q (j + 1) ^ 2 * w (j + 1)) (E Q) := (summable_energia Q).hasSum
  have hup := (hb.mul_left 2).add ((hasSum_h_w Q hQ1).mul_left (2 * gam Q ^ 2))
  have hpt : ∀ j, sigma Q (j + 1) ^ 2 * w (j + 1)
      ≤ 2 * (phi Q (j + 1) ^ 2 * w (j + 1)) + 2 * gam Q ^ 2 * (h Q (j + 1) * w (j + 1)) := by
    intro j
    have hhsq := h_sq Q (j + 1) hQ1
    have key : sigma Q (j + 1) ^ 2 ≤ 2 * phi Q (j + 1) ^ 2 + 2 * gam Q ^ 2 * h Q (j + 1) := by
      unfold sigma
      have hsq : (phi Q (j + 1) - gam Q * h Q (j + 1)) ^ 2
          ≤ 2 * phi Q (j + 1) ^ 2 + 2 * (gam Q * h Q (j + 1)) ^ 2 := by
        nlinarith [sq_nonneg (phi Q (j + 1) + gam Q * h Q (j + 1))]
      calc (phi Q (j + 1) - gam Q * h Q (j + 1)) ^ 2
          ≤ 2 * phi Q (j + 1) ^ 2 + 2 * (gam Q * h Q (j + 1)) ^ 2 := hsq
        _ = 2 * phi Q (j + 1) ^ 2 + 2 * gam Q ^ 2 * h Q (j + 1) ^ 2 := by ring
        _ = 2 * phi Q (j + 1) ^ 2 + 2 * gam Q ^ 2 * h Q (j + 1) := by rw [hhsq]
    calc sigma Q (j + 1) ^ 2 * w (j + 1)
        ≤ (2 * phi Q (j + 1) ^ 2 + 2 * gam Q ^ 2 * h Q (j + 1)) * w (j + 1) :=
          mul_le_mul_of_nonneg_right key (w_nonneg _)
      _ = 2 * (phi Q (j + 1) ^ 2 * w (j + 1)) + 2 * gam Q ^ 2 * (h Q (j + 1) * w (j + 1)) := by
          ring
  have hEle := hasSum_le hpt hE hup
  have hγ : 2 * gam Q ^ 2 * (Real.log 2 / Q) = 2 * ((Q : ℝ) * t Q ^ 2) / Real.log 2 := by
    unfold gam
    field_simp
  have h1 : 2 * ((Q : ℝ) * t Q ^ 2) / Real.log 2 ≤ 2 * b / Real.log 2 :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have hk : 0 ≤ 2 * (1 + 1 / Real.log 2) := by positivity
  have h2 : 2 * b + 2 * b / Real.log 2 = 2 * (1 + 1 / Real.log 2) * b := by
    field_simp
  have h3 : 2 * (1 + 1 / Real.log 2) * b ≤ 2 * (1 + 1 / Real.log 2) * (4 * Q) :=
    mul_le_mul_of_nonneg_left hb4 hk
  calc E Q ≤ 2 * b + 2 * gam Q ^ 2 * (Real.log 2 / Q) := hEle
    _ = 2 * b + 2 * ((Q : ℝ) * t Q ^ 2) / Real.log 2 := by rw [hγ]
    _ ≤ 2 * b + 2 * b / Real.log 2 := by linarith
    _ = 2 * (1 + 1 / Real.log 2) * b := h2
    _ ≤ 2 * (1 + 1 / Real.log 2) * (4 * Q) := h3
    _ = 8 * (1 + 1 / Real.log 2) * Q := by ring

end AMate
