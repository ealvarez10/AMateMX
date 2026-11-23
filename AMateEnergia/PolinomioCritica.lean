import AMateEnergia.PerronContorno

/-!
# El polinomio de Dirichlet en la recta crítica

Estado 45, (5.2)–(5.4), bajo RH, a partir de `balazard_saias_Zinv` con `b = 1/2 + δ`:

* `abel_Icc`, `telescopio_Ioc`: sumación de Abel y sumas telescópicas.
* `m_bound`: `|m_Q| ≤ K Q^{−1/2 + 2δ/3}`. Por Abel desde `Re s = b`, el resto de Balazard–Saias
  se telescopa; el límite `m_Q → 0` sale de `balazard_saias_Zinv` en `s = 1`, donde `Z(1) = 0`.
* `t_cauchy`, `t_bound`: `t_Q → 0` por la estimación de Cauchy para la derivada de
  `∑_{d≤Q} μ(d) d^{−s} − Z(s)` en `s = 1` (con `Z'(1) = 1`); la identidad
  `t_n − t_{n+j} = ∑ m_k log(1 + 1/k)` y el valor medio dan `|t_Q| ≤ K Q^{−1/2 + 2δ/3}`.
* `Dsum_critica`: `‖∑_{d≤Q} μ(d) d^{−1/2−ix}‖ ≤ K Q^δ (1+|x|)^η`, por Abel desde `Re s = b`.
* `P_recta_critica_de`: `‖P_Q(1/2 + ix)‖ ≤ C Q^δ (1+|x|)^η`.
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate

/-! ### Sumación de Abel -/

theorem abel_Icc (a g : ℕ → ℂ) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, a d * g d
      = (∑ d ∈ Finset.Icc 1 n, a d) * g (n + 1)
        + ∑ d ∈ Finset.Icc 1 n, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
    simp only [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    ring

theorem telescopio_Ioc (f : ℕ → ℝ) {n : ℕ} (j : ℕ) :
    ∑ d ∈ Finset.Ioc n (n + j), (f d - f (d + 1)) = f (n + 1) - f (n + j + 1) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
    ring

/-- Suma parcial de la serie de `1/ζ`. -/
noncomputable def Dsum (n : ℕ) (s : ℂ) : ℂ := ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)

theorem Zinv_one : Zinv 1 = 0 := by simp [Zinv]

theorem Dsum_one (n : ℕ) : Dsum n 1 = ((m n : ℝ) : ℂ) := by
  unfold Dsum m
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [cpow_neg_one]
  ring

/-! ### Cota de `m_Q` -/

/-- Bajo RH, `|m_n| ≤ K n^{−1/2 + 2δ/3}`. -/
theorem m_bound (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |m n| ≤ K * (n : ℝ) ^ (-(1 / 2 - 2 * δ / 3)) := by
  obtain ⟨C, hC⟩ := balazard_saias_Zinv hRH hδ hδ' (η := 1) one_pos
  set b : ℝ := 1 / 2 + δ with hb
  -- restos en `s = b`
  have hR : ∀ d : ℕ, 1 ≤ d → ‖Dsum d b - Zinv b‖ ≤ C * (d : ℝ) ^ (-δ / 3) := by
    intro d hd
    have := hC d hd (b : ℂ) (by simp [hb])
    simpa [Dsum] using this
  have hC0 : 0 ≤ C := by
    have h1 := hR 1 le_rfl
    simp at h1
    exact le_trans (norm_nonneg _) h1
  -- `m_n → 0`
  have hm0 : ∀ n : ℕ, 1 ≤ n → |m n| ≤ C * (n : ℝ) ^ (-δ / 3) := by
    intro n hn
    have := hC n hn 1 (by simp; linarith)
    rw [show ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 : ℂ)) = Dsum n 1 from rfl,
      Dsum_one, Zinv_one, sub_zero, Complex.norm_real, Real.norm_eq_abs] at this
    simpa using this
  -- fórmula de Abel con `g_d = d^{b−1}`
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ (b - 1) with hg
  set R : ℕ → ℂ := fun d => Dsum d b - Zinv b with hRdef
  have hgdec : ∀ d : ℕ, 1 ≤ d → g (d + 1) ≤ g d := by
    intro d hd
    simp only [hg]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hd) (by push_cast; linarith)
      (by linarith)
  have hg0 : ∀ d, 0 ≤ g d := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hformula : ∀ n : ℕ, ((m n : ℝ) : ℂ)
      = Zinv b + R n * g (n + 1)
        + ∑ d ∈ Finset.Icc 1 n, R d * ((g d : ℂ) - g (d + 1)) := by
    intro n
    have hterm : ∀ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 : ℂ))
        = (((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(b : ℂ))) * (g d : ℂ) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      simp only [hg]
      rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc, ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
      congr 2
      push_cast
      ring
    rw [← Dsum_one, Dsum, Finset.sum_congr rfl hterm, abel_Icc]
    have hA : ∀ d, ∑ e ∈ Finset.Icc 1 d, ((mu e : ℝ) : ℂ) * (e : ℂ) ^ (-(b : ℂ)) = Dsum d b :=
      fun d => rfl
    simp only [hA, hRdef]
    have htel : ∑ d ∈ Finset.Icc 1 n, ((g d : ℂ) - g (d + 1)) = (g 1 : ℂ) - g (n + 1) := by
      have := telescopio_Ioc g (n := 0) n
      rw [zero_add, zero_add] at this
      rw [show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_add_one_left_eq_Ioc 0 n]
      exact_mod_cast this
    have hg1 : g 1 = 1 := by simp [hg]
    have hsplit : ∑ d ∈ Finset.Icc 1 n, Dsum d b * ((g d : ℂ) - g (d + 1))
        = Zinv b * ∑ d ∈ Finset.Icc 1 n, ((g d : ℂ) - g (d + 1))
          + ∑ d ∈ Finset.Icc 1 n, (Dsum d b - Zinv b) * ((g d : ℂ) - g (d + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hsplit, htel, hg1]
    push_cast
    ring
  set β : ℝ := 1 / 2 - 2 * δ / 3 with hβ
  have hexp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (-δ / 3) * g (n + 1) ≤ (n : ℝ) ^ (-β) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : g (n + 1) ≤ g n := hgdec n hn
    calc (n : ℝ) ^ (-δ / 3) * g (n + 1) ≤ (n : ℝ) ^ (-δ / 3) * g n := by gcongr
      _ = (n : ℝ) ^ (-β) := by
          simp only [hg]
          rw [← Real.rpow_add hn0]
          congr 1
          rw [hβ, hb]
          ring
  refine ⟨2 * C, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- diferencia entre `n` y `n + j`
  have hdiff : ∀ j : ℕ, ‖((m (n + j) : ℝ) : ℂ) - ((m n : ℝ) : ℂ)‖ ≤ 2 * C * (n : ℝ) ^ (-β) := by
    intro j
    rw [hformula (n + j), hformula n]
    have hsum : ∑ d ∈ Finset.Icc 1 (n + j), R d * ((g d : ℂ) - g (d + 1))
        - ∑ d ∈ Finset.Icc 1 n, R d * ((g d : ℂ) - g (d + 1))
        = ∑ d ∈ Finset.Ioc n (n + j), R d * ((g d : ℂ) - g (d + 1)) := by
      have e1 : Finset.Icc 1 (n + j) = Finset.Ioc 0 (n + j) :=
        Finset.Icc_add_one_left_eq_Ioc 0 (n + j)
      have e2 : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
      rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) (Nat.le_add_right n j)]
      ring
    have hrw : Zinv b + R (n + j) * g (n + j + 1)
          + ∑ d ∈ Finset.Icc 1 (n + j), R d * ((g d : ℂ) - g (d + 1))
        - (Zinv b + R n * g (n + 1) + ∑ d ∈ Finset.Icc 1 n, R d * ((g d : ℂ) - g (d + 1)))
        = R (n + j) * g (n + j + 1) - R n * g (n + 1)
          + ∑ d ∈ Finset.Ioc n (n + j), R d * ((g d : ℂ) - g (d + 1)) := by
      rw [← hsum]
      ring
    rw [hrw]
    have hRn : ∀ d : ℕ, n ≤ d → ‖R d‖ ≤ C * (n : ℝ) ^ (-δ / 3) := by
      intro d hd
      have hd1 : 1 ≤ d := le_trans hn hd
      calc ‖R d‖ ≤ C * (d : ℝ) ^ (-δ / 3) := hR d hd1
        _ ≤ C * (n : ℝ) ^ (-δ / 3) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hd) (by linarith)) hC0
    have hT : ‖∑ d ∈ Finset.Ioc n (n + j), R d * ((g d : ℂ) - g (d + 1))‖
        ≤ C * (n : ℝ) ^ (-δ / 3) * (g (n + 1) - g (n + j + 1)) := by
      calc _ ≤ ∑ d ∈ Finset.Ioc n (n + j), ‖R d * ((g d : ℂ) - g (d + 1))‖ := norm_sum_le _ _
        _ ≤ ∑ d ∈ Finset.Ioc n (n + j), C * (n : ℝ) ^ (-δ / 3) * (g d - g (d + 1)) := by
            apply Finset.sum_le_sum
            intro d hd
            have hd' := Finset.mem_Ioc.mp hd
            rw [norm_mul, show ((g d : ℂ) - g (d + 1)) = ((g d - g (d + 1) : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [hgdec d (by omega)])]
            exact mul_le_mul_of_nonneg_right (hRn d hd'.1.le) (by linarith [hgdec d (by omega)])
        _ = C * (n : ℝ) ^ (-δ / 3) * (g (n + 1) - g (n + j + 1)) := by
            rw [← Finset.mul_sum, telescopio_Ioc]
    have h1 : ‖R (n + j) * (g (n + j + 1) : ℂ)‖ ≤ C * (n : ℝ) ^ (-δ / 3) * g (n + j + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact mul_le_mul_of_nonneg_right (hRn _ (Nat.le_add_right n j)) (hg0 _)
    have h2 : ‖R n * (g (n + 1) : ℂ)‖ ≤ C * (n : ℝ) ^ (-δ / 3) * g (n + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact mul_le_mul_of_nonneg_right (hRn _ le_rfl) (hg0 _)
    have h3 := hexp n hn
    calc ‖R (n + j) * (g (n + j + 1) : ℂ) - R n * (g (n + 1) : ℂ)
          + ∑ d ∈ Finset.Ioc n (n + j), R d * ((g d : ℂ) - g (d + 1))‖
        ≤ ‖R (n + j) * (g (n + j + 1) : ℂ)‖ + ‖R n * (g (n + 1) : ℂ)‖
          + ‖∑ d ∈ Finset.Ioc n (n + j), R d * ((g d : ℂ) - g (d + 1))‖ := by
          refine le_trans (norm_add_le _ _) ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ C * (n : ℝ) ^ (-δ / 3) * g (n + j + 1) + C * (n : ℝ) ^ (-δ / 3) * g (n + 1)
          + C * (n : ℝ) ^ (-δ / 3) * (g (n + 1) - g (n + j + 1)) := by gcongr
      _ = 2 * C * ((n : ℝ) ^ (-δ / 3) * g (n + 1)) := by ring
      _ ≤ 2 * C * (n : ℝ) ^ (-β) := by gcongr
  -- paso al límite
  have h0 : Tendsto (fun j : ℕ => ((n + j : ℕ) : ℝ) ^ (-δ / 3)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < δ / 3 by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
    refine h.congr (fun j => ?_)
    show ((j + n : ℕ) : ℝ) ^ (-(δ / 3)) = ((n + j : ℕ) : ℝ) ^ (-δ / 3)
    rw [add_comm j n, neg_div]
  have hlim : Tendsto (fun j : ℕ => C * ((n + j : ℕ) : ℝ) ^ (-δ / 3) + 2 * C * (n : ℝ) ^ (-β))
      atTop (𝓝 (2 * C * (n : ℝ) ^ (-β))) := by
    have := (h0.const_mul C).add (tendsto_const_nhds (x := 2 * C * (n : ℝ) ^ (-β)))
    simpa using this
  refine ge_of_tendsto' hlim fun j => ?_
  have hj := hdiff j
  have hmj := hm0 (n + j) (by omega)
  have e : ‖((m (n + j) : ℝ) : ℂ) - ((m n : ℝ) : ℂ)‖ = |m (n + j) - m n| := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e] at hj
  have h1 := abs_sub_abs_le_abs_sub (m n) (m (n + j))
  rw [abs_sub_comm] at h1
  linarith

/-! ### `t_Q → 0`, por la estimación de Cauchy -/

theorem hasDerivAt_Dsum (n : ℕ) :
    HasDerivAt (Dsum n)
      (∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * ((d : ℂ) ^ (-(1 : ℂ)) * Complex.log d * (-1))) 1 := by
  have h : ∀ d ∈ Finset.Icc 1 n, HasDerivAt (fun s : ℂ => ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s))
      (((mu d : ℝ) : ℂ) * ((d : ℂ) ^ (-(1 : ℂ)) * Complex.log d * (-1))) 1 := by
    intro d hd
    have hd0 : (d : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hd).1
      exact_mod_cast (show d ≠ 0 by omega)
    exact ((hasDerivAt_neg 1).const_cpow (Or.inl hd0)).const_mul _
  have := HasDerivAt.fun_sum h
  unfold Dsum
  exact this

theorem hasDerivAt_Zinv_one : HasDerivAt Zinv 1 1 := by
  have h1 : HasDerivAt (fun z : ℂ => z - 1) 1 1 := (hasDerivAt_id 1).sub_const 1
  have h2 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ 1) 1 :=
    differentiable_riemannZeta₁.differentiableAt.hasDerivAt
  have h3 := h1.div h2 (by rw [riemannZeta₁_one]; exact one_ne_zero)
  have e : ((1 : ℂ) * riemannZeta₁ 1 - (1 - 1) * deriv riemannZeta₁ 1) / riemannZeta₁ 1 ^ 2 = 1 := by
    rw [riemannZeta₁_one]
    ring
  rw [e] at h3
  exact h3

/-- Bajo RH, `|t_n| ≤ C n^{−δ/3} (log n + c)`; en particular `t_n → 0`. -/
theorem t_cauchy (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C c : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |t n| ≤ C * (n : ℝ) ^ (-δ / 3) * (Real.log n + c) := by
  obtain ⟨C, hC⟩ := balazard_saias_Zinv hRH hδ hδ' (η := 1) one_pos
  set r : ℝ := 1 / 2 - δ with hr
  have hr0 : 0 < r := by linarith
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    simp at h1
    exact le_trans (norm_nonneg _) (by linarith)
  refine ⟨C, (1 + r) / r, hC0, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set E : ℂ → ℂ := fun s => Dsum n s - Zinv s with hE
  have hE1 : E 1 = ((m n : ℝ) : ℂ) := by simp [hE, Dsum_one, Zinv_one]
  set D' : ℂ := ∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * ((d : ℂ) ^ (-(1 : ℂ)) * Complex.log d * (-1))
    with hD'
  have hEd : HasDerivAt E (D' - 1) 1 := (hasDerivAt_Dsum n).sub hasDerivAt_Zinv_one
  -- la identidad para `t_n`
  have hD'val : D' = -∑ d ∈ Finset.Icc 1 n, ((mu d / (d : ℝ) * Real.log d : ℝ) : ℂ) := by
    rw [hD', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [cpow_neg_one, ← Complex.natCast_log]
    push_cast
    ring
  have ht : ((t n : ℝ) : ℂ) = -(Real.log n : ℂ) * E 1 - (D' - 1) := by
    have hsum : ∑ d ∈ Finset.Icc 1 n, mu d / (d : ℝ) * Real.log ((n : ℝ) / (d : ℝ))
        = Real.log n * m n - ∑ d ∈ Finset.Icc 1 n, mu d / (d : ℝ) * Real.log d := by
      unfold m
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [Real.log_div hn0.ne' hd0.ne']
      ring
    rw [hE1, hD'val]
    unfold t
    rw [hsum]
    push_cast
    ring
  -- cotas
  have hb1 : ‖E 1‖ ≤ C * (n : ℝ) ^ (-δ / 3) := by
    have := hC n hn 1 (by simp; linarith)
    simpa [hE, Dsum] using this
  have hdiff : DifferentiableOn ℂ E (closedBall 1 r) := by
    intro z hz
    have hz' : 1 / 2 < z.re := by
      have h1 : ‖z - 1‖ ≤ r := by rw [← dist_eq_norm]; exact hz
      have h2 := Complex.abs_re_le_norm (z - 1)
      rw [sub_re, one_re] at h2
      have := (abs_le.mp (le_trans h2 h1)).1
      linarith
    have hD : DifferentiableAt ℂ (Dsum n) z := by
      unfold Dsum
      refine DifferentiableAt.fun_sum fun d hd => ?_
      have hd0 : (d : ℂ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hd).1
        exact_mod_cast (show d ≠ 0 by omega)
      exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hd0) |>.const_mul _
    have hZ : DifferentiableAt ℂ Zinv z :=
      (differentiableOn_Zinv hRH).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hz')
    exact (hD.sub hZ).differentiableWithinAt
  have hcl : DiffContOnCl ℂ E (ball 1 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr0.ne']
    exact hdiff
  have hsph : ∀ z ∈ sphere (1 : ℂ) r, ‖E z‖ ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + r) := by
    intro z hz
    have h1 : ‖z - 1‖ = r := by rw [← dist_eq_norm]; exact hz
    have hre : 1 / 2 + δ ≤ z.re := by
      have h2 := Complex.abs_re_le_norm (z - 1)
      rw [sub_re, one_re, h1] at h2
      have := (abs_le.mp h2).1
      linarith
    have him : |z.im| ≤ r := by
      have h2 := Complex.abs_im_le_norm (z - 1)
      rw [sub_im, one_im, sub_zero, h1] at h2
      exact h2
    have := hC n hn z hre
    rw [Real.rpow_one] at this
    calc ‖E z‖ = ‖∑ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-z) - Zinv z‖ := rfl
      _ ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + |z.im|) := this
      _ ≤ C * (n : ℝ) ^ (-δ / 3) * (1 + r) := by gcongr
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hcl hsph
  rw [hEd.deriv] at hcauchy
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc |t n| = ‖((t n : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖-(Real.log n : ℂ) * E 1 - (D' - 1)‖ := by rw [ht]
    _ ≤ Real.log n * ‖E 1‖ + ‖D' - 1‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ Real.log n * (C * (n : ℝ) ^ (-δ / 3)) + C * (n : ℝ) ^ (-δ / 3) * (1 + r) / r := by
        gcongr
    _ = C * (n : ℝ) ^ (-δ / 3) * (Real.log n + (1 + r) / r) := by ring

/-! ### Cota de `t_Q` -/

theorem Ut_eq (n : ℕ) : t n = 1 - ∑ d ∈ Finset.Icc 1 n, mu d / (d : ℝ) * Real.log ((n : ℝ) / (d : ℝ)) :=
  rfl

theorem t_succ {k : ℕ} (hk : 1 ≤ k) :
    t (k + 1) = t k - m k * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  rw [Ut_eq, Ut_eq]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
    div_self (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0), Real.log_one, mul_zero, add_zero]
  unfold m
  rw [Finset.sum_mul]
  have hterm : ∀ d ∈ Finset.Icc 1 k, mu d / (d : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (d : ℝ))
      = mu d / (d : ℝ) * Real.log ((k : ℝ) / (d : ℝ))
        + mu d / (d : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
    congr 2
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  ring

theorem t_diff {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    t n - t (n + j)
      = ∑ i ∈ Finset.range j, m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ)) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, show n + (k + 1) = n + k + 1 by ring, t_succ (by omega)]
    ring

theorem rpow_neg_sub_ge {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 1 ≤ x) :
    β * (2 : ℝ) ^ (-β - 1) * x ^ (-β - 1) ≤ x ^ (-β) - (x + 1) ^ (-β) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ (-β))
    (fun y => -β * y ^ (-β - 1)) (show x < x + 1 by linarith)
    (fun y hy => (Real.continuousAt_rpow_const y (-β)
      (Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1)))).continuousWithinAt)
    (fun y hy => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hx0 hy.1))))
  have hc0 : 0 < c := lt_trans hx0 hc.1
  simp only [add_sub_cancel_left, div_one] at hcd
  have h1 : (x + 1) ^ (-β - 1) ≤ c ^ (-β - 1) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  have h2 : (2 * x) ^ (-β - 1) ≤ (x + 1) ^ (-β - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  rw [Real.mul_rpow (by norm_num) hx0.le] at h2
  nlinarith [Real.rpow_nonneg hc0.le (-β - 1)]

/-- Bajo RH, `|t_n| ≤ K n^{−1/2 + 2δ/3}`. -/
theorem t_bound (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |t n| ≤ K * (n : ℝ) ^ (-(1 / 2 - 2 * δ / 3)) := by
  obtain ⟨Km, hKm0, hKm⟩ := m_bound hRH hδ hδ'
  obtain ⟨Ct, ct, hCt0, hCt⟩ := t_cauchy hRH hδ hδ'
  set β : ℝ := 1 / 2 - 2 * δ / 3 with hβ
  have hβ0 : 0 < β := by linarith
  set K : ℝ := Km * ((2 : ℝ) ^ (β + 1) / β) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h22 : (2 : ℝ) ^ (β + 1) * (2 : ℝ) ^ (-β - 1) = 1 := by
    rw [← Real.rpow_add (by norm_num), show β + 1 + (-β - 1) = 0 by ring, Real.rpow_zero]
  have hdiff : ∀ j : ℕ, |t n - t (n + j)| ≤ K * (n : ℝ) ^ (-β) := by
    intro j
    rw [t_diff hn j]
    have hterm : ∀ i ∈ Finset.range j,
        |m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))|
          ≤ K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) := by
      intro i _
      have hk1 : (1 : ℝ) ≤ ((n + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + i by omega)
      have hk0 : (0 : ℝ) < ((n + i : ℕ) : ℝ) := by linarith
      have hq : ((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ) = 1 + 1 / ((n + i : ℕ) : ℝ) := by
        push_cast
        field_simp
      have hlog0 : 0 ≤ Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ)) := by
        rw [hq]
        exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
      have hlog1 : Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ)) ≤ 1 / ((n + i : ℕ) : ℝ) := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / ((n + i : ℕ) : ℝ) by positivity)
        rw [hq]
        linarith
      have hm := hKm (n + i) (by omega)
      have hmvt := rpow_neg_sub_ge hβ0 hk1
      have hpow : ((n + i : ℕ) : ℝ) ^ (-β) * (1 / ((n + i : ℕ) : ℝ))
          = ((n + i : ℕ) : ℝ) ^ (-β - 1) := by
        rw [Real.rpow_sub_one hk0.ne']
        ring
      rw [abs_mul, abs_of_nonneg hlog0]
      calc |m (n + i)| * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))
          ≤ (Km * ((n + i : ℕ) : ℝ) ^ (-β)) * (1 / ((n + i : ℕ) : ℝ)) :=
            mul_le_mul hm hlog1 hlog0 (by positivity)
        _ = Km * ((n + i : ℕ) : ℝ) ^ (-β - 1) := by rw [mul_assoc, hpow]
        _ = Km * ((2 : ℝ) ^ (β + 1) / β) * (β * (2 : ℝ) ^ (-β - 1) * ((n + i : ℕ) : ℝ) ^ (-β - 1)) := by
            field_simp
            rw [mul_assoc, h22, mul_one]
        _ ≤ K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) := by
            rw [hK]
            gcongr
    calc |∑ i ∈ Finset.range j, m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))|
        ≤ ∑ i ∈ Finset.range j,
            |m (n + i) * Real.log (((n + i + 1 : ℕ) : ℝ) / ((n + i : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, K * (((n + i : ℕ) : ℝ) ^ (-β) - (((n + i : ℕ) : ℝ) + 1) ^ (-β)) :=
          Finset.sum_le_sum hterm
      _ = K * ((n : ℝ) ^ (-β) - ((n + j : ℕ) : ℝ) ^ (-β)) := by
          rw [← Finset.mul_sum]
          congr 1
          have := Finset.sum_range_sub' (fun i => ((n + i : ℕ) : ℝ) ^ (-β)) j
          simp only [Nat.cast_add, Nat.cast_one, add_zero] at this ⊢
          rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring_nf
      _ ≤ K * (n : ℝ) ^ (-β) := by
          have : 0 ≤ ((n + j : ℕ) : ℝ) ^ (-β) := by positivity
          nlinarith
  -- paso al límite, con `t_{n+j} → 0`
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ (δ / 3)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (show 0 < δ / 3 by positivity)).tendsto_div_nhds_zero
  have hpowt : Tendsto (fun x : ℝ => x ^ (-(δ / 3))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (show 0 < δ / 3 by positivity)
  have hcomb : Tendsto (fun x : ℝ => Ct * (Real.log x / x ^ (δ / 3)) + Ct * ct * x ^ (-(δ / 3)))
      atTop (𝓝 0) := by
    simpa using (hlog.const_mul Ct).add (hpowt.const_mul (Ct * ct))
  have hseq := hcomb.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n))
  have hlim : Tendsto (fun j : ℕ => (Ct * (Real.log ((j + n : ℕ) : ℝ) / ((j + n : ℕ) : ℝ) ^ (δ / 3))
      + Ct * ct * ((j + n : ℕ) : ℝ) ^ (-(δ / 3))) + K * (n : ℝ) ^ (-β)) atTop
      (𝓝 (K * (n : ℝ) ^ (-β))) := by
    simpa using hseq.add (tendsto_const_nhds (x := K * (n : ℝ) ^ (-β)))
  refine ge_of_tendsto' hlim fun j => ?_
  have hj0 : (0 : ℝ) < ((j + n : ℕ) : ℝ) := by exact_mod_cast (show 0 < j + n by omega)
  have htj := hCt (n + j) (by omega)
  rw [add_comm n j] at htj
  have e : Ct * ((j + n : ℕ) : ℝ) ^ (-δ / 3) * (Real.log ((j + n : ℕ) : ℝ) + ct)
      = Ct * (Real.log ((j + n : ℕ) : ℝ) / ((j + n : ℕ) : ℝ) ^ (δ / 3))
        + Ct * ct * ((j + n : ℕ) : ℝ) ^ (-(δ / 3)) := by
    rw [neg_div, Real.rpow_neg hj0.le]
    field_simp
  rw [e] at htj
  have hd := hdiff j
  rw [add_comm n j] at hd
  have := abs_sub_abs_le_abs_sub (t n) (t (j + n))
  linarith

/-! ### La suma de Möbius en la recta crítica -/

/-- Bajo RH, `‖∑_{d≤Q} μ(d) d^{−1/2−ix}‖ ≤ K Q^δ (1+|x|)^η`, por Abel desde `Re s = 1/2 + δ`. -/
theorem Dsum_critica (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ x : ℝ,
      ‖Dsum Q (1 / 2 + (x : ℂ) * I)‖ ≤ K * (Q : ℝ) ^ δ * (1 + |x|) ^ η := by
  obtain ⟨C, hC⟩ := balazard_saias_Zinv hRH hδ hδ' hη
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound hRH hδ hδ' hη
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    simp at h1
    exact le_trans (norm_nonneg _) (by linarith)
  refine ⟨4 * (CZ + C), by positivity, fun Q hQ x => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set s₀ : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (x : ℂ) * I with hs₀
  have hs₀re : s₀.re = 1 / 2 + δ := by simp [hs₀]
  have hs₀im : s₀.im = x := by simp [hs₀]
  set M : ℝ := (CZ + C) * (1 + |x|) ^ η with hM
  have hM0 : 0 ≤ M := by positivity
  have hA : ∀ d : ℕ, ‖Dsum d s₀‖ ≤ M := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp [Dsum, hM0]
    have h1 := hC d hd s₀ (by rw [hs₀re])
    rw [hs₀im] at h1
    have h2 := hCZ s₀ (by rw [hs₀re])
    rw [hs₀im] at h2
    have h3 : (d : ℝ) ^ (-δ / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    have hp : 0 ≤ (1 + |x|) ^ η := by positivity
    calc ‖Dsum d s₀‖ ≤ ‖Dsum d s₀ - Zinv s₀‖ + ‖Zinv s₀‖ := norm_le_norm_sub_add _ _
      _ ≤ C * (d : ℝ) ^ (-δ / 3) * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := add_le_add h1 h2
      _ ≤ C * 1 * (1 + |x|) ^ η + CZ * (1 + |x|) ^ η := by gcongr
      _ = M := by rw [hM]; ring
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ δ with hg
  have hginc : ∀ d : ℕ, g d ≤ g (d + 1) := fun d =>
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by push_cast; linarith) hδ.le
  have hterm : ∀ d ∈ Finset.Icc 1 Q, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(1 / 2 + (x : ℂ) * I))
      = (((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s₀)) * (g d : ℂ) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    simp only [hg]
    rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc, ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
    congr 2
    rw [hs₀]
    push_cast
    ring
  have hab : Dsum Q (1 / 2 + (x : ℂ) * I)
      = Dsum Q s₀ * (g (Q + 1) : ℂ) + ∑ d ∈ Finset.Icc 1 Q, Dsum d s₀ * ((g d : ℂ) - g (d + 1)) := by
    unfold Dsum
    rw [Finset.sum_congr rfl hterm, abel_Icc]
  have htel : ∑ d ∈ Finset.Icc 1 Q, (g (d + 1) - g d) = g (Q + 1) - 1 := by
    have := telescopio_Ioc (fun d => -g d) (n := 0) Q
    have e2 : Finset.Icc 1 Q = Finset.Ioc 0 Q := Finset.Icc_add_one_left_eq_Ioc 0 Q
    rw [e2]
    simp only [zero_add] at this
    have hg1 : g 1 = 1 := by simp [hg]
    rw [hg1] at this
    linarith [this, show ∑ d ∈ Finset.Ioc 0 Q, (g (d + 1) - g d)
      = ∑ d ∈ Finset.Ioc 0 Q, (-g d - -g (d + 1)) from Finset.sum_congr rfl fun d _ => by ring]
  have hgQ : g (Q + 1) ≤ 2 * (Q : ℝ) ^ δ := by
    simp only [hg]
    calc ((Q + 1 : ℕ) : ℝ) ^ δ ≤ (2 * (Q : ℝ)) ^ δ :=
          Real.rpow_le_rpow (by positivity) (by push_cast; linarith [show (1 : ℝ) ≤ Q by exact_mod_cast hQ]) hδ.le
      _ = 2 ^ δ * (Q : ℝ) ^ δ := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ 2 * (Q : ℝ) ^ δ := by
          gcongr
          calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hg0 : ∀ d, 0 ≤ g d := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  rw [hab]
  calc ‖Dsum Q s₀ * (g (Q + 1) : ℂ) + ∑ d ∈ Finset.Icc 1 Q, Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖
      ≤ ‖Dsum Q s₀ * (g (Q + 1) : ℂ)‖
        + ∑ d ∈ Finset.Icc 1 Q, ‖Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖ :=
        le_trans (norm_add_le _ _) (by gcongr; exact norm_sum_le _ _)
    _ ≤ M * g (Q + 1) + ∑ d ∈ Finset.Icc 1 Q, M * (g (d + 1) - g d) := by
        gcongr with d hd
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
          exact mul_le_mul_of_nonneg_right (hA Q) (hg0 _)
        · rw [norm_mul, show ((g d : ℂ) - g (d + 1)) = ((g d - g (d + 1) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hginc d])]
          have := hA d
          nlinarith [hginc d]
    _ = M * (2 * g (Q + 1) - 1) := by rw [← Finset.mul_sum, htel]; ring
    _ ≤ M * (4 * (Q : ℝ) ^ δ) := by gcongr; linarith
    _ = 4 * (CZ + C) * (Q : ℝ) ^ δ * (1 + |x|) ^ η := by rw [hM]; ring

/-! ### El polinomio en la recta crítica -/

/-- **Estado 45, (5.4)**: bajo RH, `‖P_Q(1/2 + ix)‖ ≤ C Q^δ (1 + |x|)^η`. -/
theorem P_recta_critica_de (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → ∀ x : ℝ,
      ‖P Q (1 / 2 + (x : ℂ) * I)‖ ≤ C * (Q : ℝ) ^ δ * (1 + |x|) ^ η := by
  obtain ⟨KD, hKD0, hKD⟩ := Dsum_critica hRH hδ hδ' hη
  obtain ⟨Km, hKm0, hKm⟩ := m_bound hRH hδ hδ'
  obtain ⟨Kt, hKt0, hKt⟩ := t_bound hRH hδ hδ'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨KD + Km + 3 * Kt / Real.log 2, fun Q hQ x => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ0 : (0 : ℝ) < Q := by linarith
  set s : ℂ := 1 / 2 + (x : ℂ) * I with hs
  have hsre : (-s).re = -(1 / 2) := by simp [hs]
  have hQs : ‖(Q : ℂ) ^ (-s)‖ = (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hsre]
  have h2Qs : ‖((2 * Q : ℕ) : ℂ) ^ (-s)‖ ≤ (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hsre]
    exact Real.rpow_le_rpow_of_nonpos hQ0 (by push_cast; linarith) (by norm_num)
  set β : ℝ := 1 / 2 - 2 * δ / 3 with hβ
  have hexp : (Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Q : ℝ) ^ δ := by
    have e : (Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) = (Q : ℝ) ^ (2 * δ / 3) := by
      rw [mul_assoc, ← Real.rpow_add hQ0, ← Real.rpow_one_add' hQ0.le (by
        rw [hβ]
        intro h
        linarith)]
      congr 1
      rw [hβ]
      ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hpow1 : 1 ≤ (1 + |x|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg x]) hη.le
  have hQδ : 0 ≤ (Q : ℝ) ^ δ := by positivity
  have hD := hKD Q (by omega) x
  have hm := hKm Q (by omega)
  have ht := hKt Q (by omega)
  have hP : P Q s = Dsum Q s - (Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)
      - ((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)) := rfl
  have hT2 : ‖(Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)‖ ≤ Km * (Q : ℝ) ^ δ := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, hQs]
    calc (Q : ℝ) * |m Q| * (Q : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ (Q : ℝ) * (Km * (Q : ℝ) ^ (-β)) * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = Km * ((Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ Km * (Q : ℝ) ^ δ := by gcongr
  have hT3 : ‖((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖
      ≤ 3 * Kt / Real.log 2 * (Q : ℝ) ^ δ := by
    have hg : |gam Q| ≤ (Q : ℝ) * (Kt * (Q : ℝ) ^ (-β)) / Real.log 2 := by
      unfold gam
      rw [abs_div, abs_mul, abs_of_pos hQ0, abs_of_pos hl2]
      gcongr
    have hinner : ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)‖ ≤ 3 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s)‖ + ‖(Q : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ ≤ 2 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) + (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [norm_mul, hQs]
            gcongr
            simp
        _ = 3 * (Q : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |gam Q| * ‖2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s)‖
        ≤ ((Q : ℝ) * (Kt * (Q : ℝ) ^ (-β)) / Real.log 2) * (3 * (Q : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hg hinner (norm_nonneg _) (by positivity)
      _ = 3 * Kt / Real.log 2 * ((Q : ℝ) * (Q : ℝ) ^ (-β) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 3 * Kt / Real.log 2 * (Q : ℝ) ^ δ := by gcongr
  rw [hP]
  calc ‖Dsum Q s - (Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)
        - ((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖
      ≤ ‖Dsum Q s‖ + ‖(Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)‖
        + ‖((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))‖ :=
        le_trans (norm_sub_le _ _) (by gcongr; exact norm_sub_le _ _)
    _ ≤ KD * (Q : ℝ) ^ δ * (1 + |x|) ^ η + Km * (Q : ℝ) ^ δ * (1 + |x|) ^ η
        + 3 * Kt / Real.log 2 * (Q : ℝ) ^ δ * (1 + |x|) ^ η := by
        gcongr
        all_goals first
          | exact hD
          | exact le_trans hT2 (le_mul_of_one_le_right (by positivity) hpow1)
          | exact le_trans hT3 (le_mul_of_one_le_right (by positivity) hpow1)
    _ = (KD + Km + 3 * Kt / Real.log 2) * (Q : ℝ) ^ δ * (1 + |x|) ^ η := by ring

end AMate
