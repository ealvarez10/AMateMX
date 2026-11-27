import AMateMiller.Residuos

/-!
# El peso en las potencias de primos

* `w_le`: `w(m) ≤ (m/x)^α log(x/m)` para `1 ≤ m ≤ x`.
* `suma_potencias_le`: para `p` primo y `α = 2/5`,
  `∑_{p^k ≤ x} log p · w(p^k) ≤ A₁ + B₁ log p` con `A₁ = (1 + 1/e)/α²`, `B₁ = 1/(eα)`.
  Se escribe `log(x/p^k) = v₀ + j log p` y se suman las series geométricas.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace AMate.Miller.Explicito

open AMate.Miller.Ponderada

/-- `w(m) ≥ 0`. -/
theorem w_nonneg {x α β : ℝ} (hx : 0 < x) (hα : 0 < α) (hαβ : α < β) (m : ℕ) :
    0 ≤ w x α β m := by
  unfold w
  split_ifs with h
  · apply div_nonneg _ (by linarith)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Real.zero_rpow hα.ne', Real.zero_rpow (show β ≠ 0 by linarith)]
    · have hu0 : 0 < (m : ℝ) / x := by positivity
      have hu1 : (m : ℝ) / x ≤ 1 := by rw [div_le_one hx]; exact h.le
      have := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hαβ.le
      linarith
  · exact le_rfl

/-- `w(m) ≤ (m/x)^α log(x/m)` para `1 ≤ m ≤ x`. -/
theorem w_le {x α β : ℝ} (hx : 0 < x) (hα : 0 < α) (hαβ : α < β) {m : ℕ} (hm : 1 ≤ m)
    (hmx : (m : ℝ) ≤ x) : w x α β m ≤ ((m : ℝ) / x) ^ α * Real.log (x / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : 0 < (m : ℝ) / x := by positivity
  have hlog : 0 ≤ Real.log (x / m) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
  unfold w
  split_ifs with h
  · have hu : ((m : ℝ) / x) ^ β = ((m : ℝ) / x) ^ α * ((m : ℝ) / x) ^ (β - α) := by
      rw [← Real.rpow_add hu0]; ring_nf
    have hexp : 1 - (β - α) * Real.log (x / m) ≤ ((m : ℝ) / x) ^ (β - α) := by
      rw [Real.rpow_def_of_pos hu0, show Real.log ((m : ℝ) / x) = -Real.log (x / m) by
        rw [← Real.log_inv, inv_div]]
      have := Real.add_one_le_exp (-Real.log (x / m) * (β - α))
      linarith
    rw [div_le_iff₀ (by linarith), hu]
    have hp : 0 ≤ ((m : ℝ) / x) ^ α := by positivity
    nlinarith
  · positivity

/-- `v e^{−a v} ≤ 1/(e a)`. -/
theorem mul_exp_neg_le {a v : ℝ} (ha : 0 < a) : v * Real.exp (-a * v) ≤ 1 / (Real.exp 1 * a) := by
  have h := Real.add_one_le_exp (a * v - 1)
  rw [show a * v - 1 + 1 = a * v by ring, Real.exp_sub] at h
  rw [le_div_iff₀ (by positivity)]
  have hpos : 0 < Real.exp (-a * v) := Real.exp_pos _
  have e : Real.exp (-a * v) * Real.exp (a * v) = 1 := by rw [← Real.exp_add]; simp
  have h' : a * v * Real.exp 1 ≤ Real.exp (a * v) := by
    rwa [le_div_iff₀ (Real.exp_pos 1)] at h
  nlinarith

/-- `h/(1 − e^{−ah}) ≤ (1 + ah)/a`. -/
theorem div_one_sub_exp_le {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    h / (1 - Real.exp (-a * h)) ≤ (1 + a * h) / a := by
  have hq : Real.exp (-a * h) < 1 := by
    have := Real.exp_lt_exp.mpr (show -a * h < 0 by nlinarith); rwa [Real.exp_zero] at this
  have h1 := Real.add_one_le_exp (a * h)
  have e : Real.exp (-a * h) * Real.exp (a * h) = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_div_iff₀ (by linarith) ha]
  have hpos := Real.exp_pos (-a * h)
  nlinarith

/-- `h² e^{−ah}/(1 − e^{−ah})² ≤ 1/a²`. -/
theorem sq_div_le {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    h ^ 2 * Real.exp (-a * h) / (1 - Real.exp (-a * h)) ^ 2 ≤ 1 / a ^ 2 := by
  set u : ℝ := a * h with hu
  have hu0 : 0 < u := by positivity
  have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ u / 2 by linarith)
  rw [Real.sinh_eq] at hs
  have hq : Real.exp (-u) < 1 := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith); rwa [Real.exp_zero] at this
  have e1 : Real.exp (-u) = Real.exp (-(u / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have e2 : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(u / 2))
  -- `u e^{−u/2} ≤ 1 − e^{−u}`
  have key : u * Real.exp (-(u / 2)) ≤ 1 - Real.exp (-u) := by
    rw [e1]
    have : u ≤ Real.exp (u / 2) - Real.exp (-(u / 2)) := by linarith
    nlinarith
  have hneg : -a * h = -u := by rw [hu]; ring
  rw [hneg, div_le_div_iff₀ (by nlinarith) (by positivity)]
  have hk2 : (u * Real.exp (-(u / 2))) ^ 2 ≤ (1 - Real.exp (-u)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) key 2
  have : (u * Real.exp (-(u / 2))) ^ 2 = u ^ 2 * Real.exp (-u) := by rw [e1]; ring
  rw [this, hu] at hk2
  nlinarith

/-- `∑_{j<K} q^j ≤ 1/(1 − q)` y `∑_{j<K} j q^j ≤ q/(1 − q)²` para `0 ≤ q < 1`. -/
theorem geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, q ^ j ≤ 1 / (1 - q) ∧
      ∑ j ∈ Finset.range K, (j : ℝ) * q ^ j ≤ q / (1 - q) ^ 2 := by
  constructor
  · rw [geom_sum_eq hq1.ne K, show (q ^ K - 1) / (q - 1) = (1 - q ^ K) / (1 - q) by
      rw [← neg_div_neg_eq]; ring_nf]
    have : 0 ≤ q ^ K := pow_nonneg hq0 K
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · have hn : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq1
    have hs : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
      have := summable_pow_mul_geometric_of_norm_lt_one 1 hn
      simpa using this
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hn]
    exact hs.sum_le_tsum _ fun j _ => by positivity

/-- **Potencias de un primo**: `∑_{p^k ≤ x} log p · w(p^k) ≤ (1 + 1/e)/α² + log p/(eα)`, `α = 2/5`. -/
theorem suma_potencias_le {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) :
    ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log p⌋₊, Real.log p * w x (2 / 5) (9 / 20) (p ^ k) ≤
      (1 / (Real.exp 1 * (2 / 5) ^ 2) + 1 / (2 / 5) ^ 2) +
        Real.log p * (1 / (Real.exp 1 * (2 / 5))) := by
  set α : ℝ := 2 / 5 with hα
  have hα0 : 0 < α := by norm_num
  have hx0 : 0 < x := by linarith
  set h : ℝ := Real.log p with hh
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hh0 : 0 < h := Real.log_pos hp1
  set K : ℕ := ⌊Real.log x / h⌋₊ with hK
  have hKle : (K : ℝ) * h ≤ Real.log x := by
    have := Nat.floor_le (div_nonneg (Real.log_nonneg hx) hh0.le)
    rw [← hK] at this
    rwa [le_div_iff₀ hh0] at this
  set v₀ : ℝ := Real.log x - K * h with hv₀
  have hv₀0 : 0 ≤ v₀ := by rw [hv₀]; linarith
  set q : ℝ := Real.exp (-α * h) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have := Real.exp_lt_exp.mpr (show -α * h < 0 by nlinarith); rwa [Real.exp_zero] at this
  -- cota término a término
  have hterm : ∀ j ∈ Finset.range K, Real.log p * w x (2 / 5) (9 / 20) (p ^ (K - j)) ≤
      h * Real.exp (-α * v₀) * ((v₀ + j * h) * q ^ j) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    have hk1 : 1 ≤ p ^ (K - j) := Nat.one_le_pow _ _ hp.pos
    have hcast : ((p ^ (K - j) : ℕ) : ℝ) = (p : ℝ) ^ (K - j) := by push_cast; ring
    have hlogk : Real.log ((p ^ (K - j) : ℕ) : ℝ) = ((K - j : ℕ) : ℝ) * h := by
      rw [hcast, Real.log_pow]
    have hkx : ((p ^ (K - j) : ℕ) : ℝ) ≤ x := by
      rw [← Real.log_le_log_iff (by positivity) hx0, hlogk]
      have : ((K - j : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K j
      nlinarith
    have hw := w_le (α := 2 / 5) (β := 9 / 20) hx0 (by norm_num) (by norm_num) hk1 hkx
    have hv : Real.log (x / ((p ^ (K - j) : ℕ) : ℝ)) = v₀ + j * h := by
      rw [Real.log_div hx0.ne' (by positivity), hlogk, hv₀]
      push_cast [Nat.cast_sub hjK.le]
      ring
    have hpow : (((p ^ (K - j) : ℕ) : ℝ) / x) ^ (2 / 5 : ℝ) = Real.exp (-α * (v₀ + j * h)) := by
      rw [Real.rpow_def_of_pos (by positivity), show Real.log (((p ^ (K - j) : ℕ) : ℝ) / x) =
        -Real.log (x / ((p ^ (K - j) : ℕ) : ℝ)) by rw [← Real.log_inv, inv_div], hv, hα]
      ring_nf
    rw [hpow, hv] at hw
    have hexp : Real.exp (-α * (v₀ + j * h)) = Real.exp (-α * v₀) * q ^ j := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [hexp] at hw
    calc Real.log p * w x (2 / 5) (9 / 20) (p ^ (K - j)) ≤
          h * (Real.exp (-α * v₀) * q ^ j * (v₀ + j * h)) :=
          mul_le_mul_of_nonneg_left hw hh0.le
      _ = h * Real.exp (-α * v₀) * ((v₀ + j * h) * q ^ j) := by ring
  -- reindexado `k = K − j`
  have hre : ∑ k ∈ Finset.Icc 1 K, Real.log p * w x (2 / 5) (9 / 20) (p ^ k) =
      ∑ j ∈ Finset.range K, Real.log p * w x (2 / 5) (9 / 20) (p ^ (K - j)) := by
    apply Finset.sum_nbij' (fun k => K - k) (fun j => K - j)
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro j hj; simp only [Finset.mem_range] at hj; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk
      rw [show K - (K - k) = k by omega]
  rw [hre]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsplit : ∑ j ∈ Finset.range K, (v₀ + j * h) * q ^ j =
      v₀ * ∑ j ∈ Finset.range K, q ^ j + h * ∑ j ∈ Finset.range K, (j : ℝ) * q ^ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  obtain ⟨g1, g2⟩ := geom_le hq0 hq1 K
  have hE := Real.exp_pos (-α * v₀)
  have hE1 : Real.exp (-α * v₀) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hb1 := mul_exp_neg_le (v := v₀) hα0
  have hb2 := div_one_sub_exp_le hα0 hh0
  have hb3 := sq_div_le hα0 hh0
  rw [← hq] at hb2 hb3
  have hS1 : 0 ≤ ∑ j ∈ Finset.range K, q ^ j := Finset.sum_nonneg fun j _ => by positivity
  have hS2 : 0 ≤ ∑ j ∈ Finset.range K, (j : ℝ) * q ^ j := Finset.sum_nonneg fun j _ => by positivity
  have t1 : h * Real.exp (-α * v₀) * (v₀ * ∑ j ∈ Finset.range K, q ^ j) ≤
      (1 / (Real.exp 1 * α)) * ((1 + α * h) / α) := by
    calc h * Real.exp (-α * v₀) * (v₀ * ∑ j ∈ Finset.range K, q ^ j)
        = (v₀ * Real.exp (-α * v₀)) * (h * ∑ j ∈ Finset.range K, q ^ j) := by ring
      _ ≤ (1 / (Real.exp 1 * α)) * (h * (1 / (1 - q))) := by
          apply mul_le_mul hb1 (mul_le_mul_of_nonneg_left g1 hh0.le) (by positivity) (by positivity)
      _ = (1 / (Real.exp 1 * α)) * (h / (1 - q)) := by ring
      _ ≤ (1 / (Real.exp 1 * α)) * ((1 + α * h) / α) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
  have t2 : h * Real.exp (-α * v₀) * (h * ∑ j ∈ Finset.range K, (j : ℝ) * q ^ j) ≤ 1 / α ^ 2 := by
    calc h * Real.exp (-α * v₀) * (h * ∑ j ∈ Finset.range K, (j : ℝ) * q ^ j)
        ≤ h * 1 * (h * (q / (1 - q) ^ 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hE1 hh0.le)
            (mul_le_mul_of_nonneg_left g2 hh0.le) (by positivity) (by positivity)
      _ = h ^ 2 * q / (1 - q) ^ 2 := by ring
      _ ≤ 1 / α ^ 2 := hb3
  rw [mul_add]
  have e : (1 / (Real.exp 1 * α)) * ((1 + α * h) / α) = 1 / (Real.exp 1 * α ^ 2) +
      h * (1 / (Real.exp 1 * α)) := by
    field_simp
  linarith

end AMate.Miller.Explicito
