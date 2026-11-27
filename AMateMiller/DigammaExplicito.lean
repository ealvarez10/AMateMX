import AMateMiller.HipotesisAnaliticas
import AMateMiller.CotaBachCuadrada

/-!
# Cotas explícitas de la función digamma

A partir de la serie `ψ(z) = lim (log n − ∑_{k ≤ n} 1/(z + k))` (`SerieDigamma`, de Alpöge):

* `digamma_real_le`, `digamma_real_ge`, `digamma_real_im`: para `y > 0` real,
  `log y − 1/y ≤ ψ(y) ≤ log y` y `ψ(y)` es real.
* `norm_digamma_le`: si `0 ≤ Re w ≤ 2` y `w ≠ 0`, `|ψ(w)| ≤ 9 + 1/|w| + 2 log(1 + |w|)`.
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.DigammaExp

/-- `log((y + n + 1)/y) ≤ ∑_{k ≤ n} 1/(y + k)`. -/
theorem log_le_sum_inv {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.log ((y + n + 1) / y) ≤ ∑ k ∈ Finset.range (n + 1), 1 / (y + k) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 / (y + t)) (Icc 0 (0 + ((n + 1 : ℕ) : ℝ))) := by
    intro a ha b hb hab
    simp only [mem_Icc] at ha hb
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h := hanti.integral_le_sum
  simp only [zero_add] at h
  have hint : ∫ t in (0 : ℝ)..((n + 1 : ℕ) : ℝ), 1 / (y + t) = Real.log ((y + n + 1) / y) := by
    have := intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) (a := 0)
      (b := ((n + 1 : ℕ) : ℝ)) y
    simp only [one_div]
    rw [this, add_zero, integral_inv_of_pos hy (by positivity)]
    push_cast
    ring_nf
  rw [hint] at h
  exact h

/-- `∑_{k ≤ n} 1/(y + k) ≤ 1/y + log((y + n)/y)`. -/
theorem sum_inv_le {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 1 / (y + k) ≤ 1 / y + Real.log ((y + n) / y) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 / (y + t)) (Icc 0 (0 + (n : ℝ))) := by
    intro a ha b hb hab
    simp only [mem_Icc] at ha hb
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h := hanti.sum_le_integral
  simp only [zero_add] at h
  have hint : ∫ t in (0 : ℝ)..(n : ℝ), 1 / (y + t) = Real.log ((y + n) / y) := by
    have := intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) (a := 0) (b := (n : ℝ)) y
    simp only [one_div]
    rw [this, add_zero, integral_inv_of_pos hy (by positivity)]
  rw [hint] at h
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, add_zero]
  linarith

variable (hS : SerieDigamma)
include hS

omit hS in
/-- La sucesión de la serie es real para `y` real. -/
theorem seq_real (y : ℝ) (n : ℕ) :
    ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / ((y : ℂ) + (k : ℂ)) =
      ((Real.log n - ∑ k ∈ Finset.range (n + 1), 1 / (y + k) : ℝ) : ℂ) := by
  push_cast; rfl

/-- La sucesión de la serie, en reales. -/
theorem tendsto_real {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ => Real.log n - ∑ k ∈ Finset.range (n + 1), 1 / (y + k)) atTop
      (𝓝 (Complex.digamma y).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (hS (y : ℂ) (by simpa using hy))
  refine h.congr fun n => ?_
  show (((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / ((y : ℂ) + (k : ℂ))).re = _
  rw [seq_real, Complex.ofReal_re]

theorem digamma_real_im {y : ℝ} (hy : 0 < y) : (Complex.digamma y).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (hS (y : ℂ) (by simpa using hy))
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (Complex.digamma y).im) := by
    refine h.congr fun n => ?_
    show (((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / ((y : ℂ) + (k : ℂ))).im = _
    rw [seq_real, Complex.ofReal_im]
  exact (tendsto_nhds_unique tendsto_const_nhds h0).symm

/-- `ψ(y) ≤ log y` para `y > 0`. -/
theorem digamma_real_le {y : ℝ} (hy : 0 < y) : (Complex.digamma y).re ≤ Real.log y := by
  refine le_of_tendsto (tendsto_real hS hy) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h1 := log_le_sum_inv hy n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log n ≤ Real.log ((y + n + 1) / y) + Real.log y := by
    rw [← Real.log_mul (by positivity) hy.ne', div_mul_cancel₀ _ hy.ne']
    exact Real.log_le_log hn' (by linarith)
  linarith

/-- `ψ(y) ≥ log y − 1/y` para `y > 0`. -/
theorem digamma_real_ge {y : ℝ} (hy : 0 < y) : Real.log y - 1 / y ≤ (Complex.digamma y).re := by
  have hb : Tendsto (fun n : ℕ => Real.log y - 1 / y + Real.log (n / (y + n))) atTop
      (𝓝 (Real.log y - 1 / y)) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (y + n)) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 / (y / n + 1)) atTop (𝓝 (1 / (0 + 1))) := by
        refine tendsto_const_nhds.div ((tendsto_const_div_atTop_nhds_zero_nat y).add_const 1)
          (by norm_num)
      simp only [zero_add, div_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at h2
    simpa using h2.const_add (Real.log y - 1 / y)
  refine le_of_tendsto_of_tendsto hb (tendsto_real hS hy) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h1 := sum_inv_le hy n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((y + n) / y) = Real.log n - Real.log (n / (y + n)) - Real.log y := by
    rw [Real.log_div (by positivity) hy.ne', Real.log_div hn'.ne' (by positivity)]
    ring
  linarith

/-! ### Rectas verticales -/

omit hS in
/-- `∑_{k=1}^n 1/k² ≤ 2 − 1/n` para `n ≥ 1`. -/
theorem sum_inv_sq_le' (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have key : 1 / (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ hM.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

omit hS in
theorem sum_inv_sq_le (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := sum_inv_sq_le' n hn
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith

omit hS in
/-- `∑_{k ≤ n} f k = f 0 + ∑_{1 ≤ k ≤ n} f k`. -/
theorem sum_range_succ_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), add_assoc]

omit hS in
/-- `∑_{M < k ≤ M + j} 1/k² ≤ 1/M − 1/(M + j)` para `M ≥ 1`. -/
theorem sum_Ioc_inv_sq_aux {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    ∑ k ∈ Finset.Ioc M (M + j), 1 / (k : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + j : ℕ) : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show M + (j + 1) = (M + j) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
    have hA : (0 : ℝ) < ((M + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + j)
    have key : 1 / (((M + j + 1 : ℕ) : ℝ)) ^ 2 ≤
        1 / ((M + j : ℕ) : ℝ) - 1 / (((M + j + 1 : ℕ) : ℝ)) := by
      push_cast at hA ⊢
      rw [div_sub_div _ _ hA.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

omit hS in
theorem sum_Ioc_inv_sq {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    ∑ k ∈ Finset.Ioc M n, 1 / (k : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  rcases le_or_gt n M with h | h
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
  · obtain ⟨j, rfl⟩ : ∃ j, n = M + j := ⟨n - M, by omega⟩
    have := sum_Ioc_inv_sq_aux hM j
    have : 0 ≤ 1 / ((M + j : ℕ) : ℝ) := by positivity
    linarith

omit hS in
/-- Cota de `∑_{k ≤ n} |1/k − 1/(w + k)|` para `0 ≤ Re w ≤ 2`. -/
theorem sum_dif_le {w : ℂ} (h0 : 0 ≤ w.re) (h2 : w.re ≤ 2) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ‖1 / (k : ℂ) - 1 / (w + k)‖ ≤ 8 + 2 * Real.log (1 + ‖w‖) := by
  set R := ‖w‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg w
  have hl0 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  -- cota de cada término
  have hterm : ∀ k ∈ Finset.Icc 1 n, ‖1 / (k : ℂ) - 1 / (w + k)‖ = R / ((k : ℝ) * ‖w + k‖) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hwk : w + k ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith
    have hk0 : (k : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      exact_mod_cast (show k ≠ 0 by omega)
    rw [show (1 : ℂ) / k - 1 / (w + k) = w / (k * (w + k)) by field_simp; ring, norm_div,
      norm_mul, Complex.norm_natCast]
  have hge_k : ∀ k : ℕ, (k : ℝ) ≤ ‖w + k‖ := by
    intro k
    have := Complex.abs_re_le_norm (w + k)
    simp at this
    linarith [le_abs_self (w.re + k)]
  have hge_R : ∀ k : ℕ, R - 2 ≤ ‖w + k‖ := by
    intro k
    have h1 : R ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    have h2' : |w.im| ≤ ‖w + k‖ := by
      have := Complex.abs_im_le_norm (w + k); simpa using this
    rw [abs_of_nonneg h0] at h1
    linarith
  rw [Finset.sum_congr rfl hterm]
  rcases le_or_gt R 4 with hR4 | hR4
  · -- `R ≤ 4`
    have hb : ∀ k ∈ Finset.Icc 1 n, R / ((k : ℝ) * ‖w + k‖) ≤ 4 * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have := hge_k k
      rw [div_le_iff₀ (by nlinarith)]
      calc R ≤ 4 := hR4
        _ = 4 * (1 / (k : ℝ) ^ 2) * ((k : ℝ) * k) := by field_simp
        _ ≤ 4 * (1 / (k : ℝ) ^ 2) * ((k : ℝ) * ‖w + k‖) := by gcongr
    calc ∑ k ∈ Finset.Icc 1 n, R / ((k : ℝ) * ‖w + k‖) ≤ ∑ k ∈ Finset.Icc 1 n, 4 * (1 / (k : ℝ) ^ 2) :=
          Finset.sum_le_sum hb
      _ = 4 * ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * 2 := by gcongr; exact sum_inv_sq_le n
      _ ≤ 8 + 2 * Real.log (1 + R) := by linarith
  · -- `R > 4`
    set M : ℕ := ⌊R / 2⌋₊ with hM
    have hM2 : 2 ≤ M := Nat.le_floor (by push_cast; linarith)
    have hMR : (M : ℝ) ≤ R / 2 := Nat.floor_le (by linarith)
    have hMR' : R / 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    set g : ℕ → ℝ := fun k => if k ≤ M then 2 / (k : ℝ) else R * (1 / (k : ℝ) ^ 2) with hg
    have hb : ∀ k ∈ Finset.Icc 1 n, R / ((k : ℝ) * ‖w + k‖) ≤ g k := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      simp only [hg]
      split_ifs with hkM
      · have hkM' : (k : ℝ) ≤ R / 2 := (Nat.cast_le.mpr hkM).trans hMR
        have h3 : R / 2 ≤ ‖w + k‖ := by linarith [hge_R k]
        rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
        nlinarith
      · push Not at hkM
        have := hge_k k
        rw [div_le_iff₀ (by nlinarith)]
        calc R = R * (1 / (k : ℝ) ^ 2) * ((k : ℝ) * k) := by field_simp
          _ ≤ R * (1 / (k : ℝ) ^ 2) * ((k : ℝ) * ‖w + k‖) := by gcongr
    have hsplit : ∑ k ∈ Finset.Icc 1 n, g k ≤
        ∑ k ∈ Finset.Icc 1 M, 2 / (k : ℝ) + R * ∑ k ∈ Finset.Ioc M n, 1 / (k : ℝ) ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun k => k ≤ M), Finset.mul_sum]
      apply add_le_add
      · calc ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ≤ M), g k
            = ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ≤ M), 2 / (k : ℝ) :=
              Finset.sum_congr rfl fun k hk => by
                rw [Finset.mem_filter] at hk; simp only [hg, if_pos hk.2]
          _ ≤ ∑ k ∈ Finset.Icc 1 M, 2 / (k : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                rw [Finset.mem_filter, Finset.mem_Icc] at hk
                rw [Finset.mem_Icc]; omega
              · intro k _ _; positivity
      · calc ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ k ≤ M), g k
            = ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ k ≤ M), R * (1 / (k : ℝ) ^ 2) :=
              Finset.sum_congr rfl fun k hk => by
                rw [Finset.mem_filter] at hk; simp only [hg, if_neg hk.2]
          _ ≤ ∑ k ∈ Finset.Ioc M n, R * (1 / (k : ℝ) ^ 2) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                rw [Finset.mem_filter, Finset.mem_Icc] at hk
                rw [Finset.mem_Ioc]; omega
              · intro k _ _; positivity
    have hH : ∑ k ∈ Finset.Icc 1 M, 2 / (k : ℝ) ≤ 2 + 2 * Real.log R := by
      have h1 := harmonic_le_one_add_log M
      rw [harmonic_eq_sum_Icc] at h1
      have e : ∑ k ∈ Finset.Icc 1 M, 2 / (k : ℝ) = 2 * ((∑ i ∈ Finset.Icc 1 M, ((i : ℚ))⁻¹ : ℚ) : ℝ) := by
        push_cast; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      have hlogM : Real.log M ≤ Real.log R :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by linarith)
      have h1' : ((∑ i ∈ Finset.Icc 1 M, ((i : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 + Real.log M := by exact_mod_cast h1
      linarith
    have hT := sum_Ioc_inv_sq (by omega : 1 ≤ M) n
    have hRM : R * (1 / (M : ℝ)) ≤ 4 := by
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      rw [mul_one_div, div_le_iff₀ hM0]
      linarith
    have hlogR : Real.log R ≤ Real.log (1 + R) := Real.log_le_log (by linarith) (by linarith)
    calc ∑ k ∈ Finset.Icc 1 n, R / ((k : ℝ) * ‖w + k‖) ≤ ∑ k ∈ Finset.Icc 1 n, g k :=
          Finset.sum_le_sum hb
      _ ≤ _ := hsplit
      _ ≤ (2 + 2 * Real.log R) + R * (1 / (M : ℝ)) := by
          gcongr
      _ ≤ 8 + 2 * Real.log (1 + R) := by linarith

/-- **Cota de `ψ` en rectas verticales**: `|ψ(w)| ≤ 9 + 1/|w| + 2 log(1 + |w|)` si `0 < Re w ≤ 2`. -/
theorem norm_digamma_le {w : ℂ} (h0 : 0 < w.re) (h2 : w.re ≤ 2) :
    ‖Complex.digamma w‖ ≤ 9 + 1 / ‖w‖ + 2 * Real.log (1 + ‖w‖) := by
  have hw0 : w ≠ 0 := by intro e; rw [e] at h0; simp at h0
  have hR0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  refine le_of_tendsto (hS w h0).norm ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sum_range_succ_Icc]
  simp only [Nat.cast_zero, add_zero]
  have hHn : |Real.log n - ((harmonic n : ℚ) : ℝ)| ≤ 1 := by
    have h1 := harmonic_le_one_add_log n
    have h2 := log_add_one_le_harmonic n
    have h3 : Real.log n ≤ Real.log (n + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [abs_le]; constructor <;> push_cast at h1 h2 ⊢ <;> linarith
  have hHsum : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; refine Finset.sum_congr rfl fun k _ => by ring
  have hdesc : ((Real.log n : ℝ) : ℂ) - (1 / w + ∑ k ∈ Finset.Icc 1 n, 1 / (w + (k : ℂ))) =
      ((Real.log n - ((harmonic n : ℚ) : ℝ) : ℝ) : ℂ) - 1 / w +
        ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℂ) - 1 / (w + k)) := by
    rw [Finset.sum_sub_distrib, hHsum]
    push_cast
    ring
  rw [hdesc]
  have hs := sum_dif_le h0.le h2 n
  calc ‖((Real.log n - ((harmonic n : ℚ) : ℝ) : ℝ) : ℂ) - 1 / w +
        ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℂ) - 1 / (w + k))‖
      ≤ ‖((Real.log n - ((harmonic n : ℚ) : ℝ) : ℝ) : ℂ)‖ + ‖1 / w‖ +
        ∑ k ∈ Finset.Icc 1 n, ‖1 / (k : ℂ) - 1 / (w + k)‖ := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
    _ ≤ 1 + 1 / ‖w‖ + (8 + 2 * Real.log (1 + ‖w‖)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one]
        linarith
    _ = 9 + 1 / ‖w‖ + 2 * Real.log (1 + ‖w‖) := by ring

end AMate.Miller.DigammaExp
