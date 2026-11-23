import AMateEnergia.PerfilVonMangoldt
import AMateEnergia.Teorema

/-!
# Teorema unilateral en ventanas de Landau–Alpöge especializado a conductor 1

Pieza 2 del puente de conductor 1 hacia `RiemannHypothesis` y `E_Q`:

* `erlang_max`, `erlang_integral`, `cola_erlang_ventana`: el núcleo no negativo
  `(u^k / k!) e^{−σu}` concentra su masa en la ventana logarítmica `[U, (1 + δ) U]` cuando
  `k = ⌈(1 + δ/2) σ U⌉₊`, con colas `O(σ^{−k})`.
* `iteratedDeriv_Phi_zeta_laplace`: derivación reiterada de la transformada de Laplace de
  `G_vonMangoldt` en `Re s > 2`.
* `cota_derivadas_de_ventana`: bajo la hipótesis unilateral integral `HipotesisVentanaZeta θ δ`,
  `‖(−1)^k Φ_ζ^{(k)}(σ + iγ)/k!‖ + Re((−1)^k Φ_ζ^{(k)}(σ)/k!) ≤ C e^{η U} / (σ − θ)^k`.
* `geometria_polo_conductor_uno`: usando que `ζ` no tiene ceros reales en `(0, ∞)`
  (`zeta_ofReal_ne_zero`), un cero en `Re ρ > θ` produce un punto `z = σ + iγ` con un único cero
  más cercano a distancia `d < min(D, σ − θ)`, donde `B(σ, D)` está libre de ceros.
* `sin_ceros_de_ventana_integral`, `sin_ceros_de_ventana_puntual`, `rh_de_ventana_vonMangoldt` y
  `energia_de_ventana_vonMangoldt`: cierre completo `(V) ⇒ RH ⇒ E_Q ≤ C_ε Q^ε`.
-/

open MeasureTheory Set Filter Topology Complex

namespace AMate

/-! ### Hipótesis unilateral integral en ventanas para `ζ(s)` -/

/-- Hipótesis unilateral integral en ventanas `[Y, Y^{1 + δ}]` para `G_vonMangoldt`:
para cada `η > 0` y `Y₀` existe `Y ≥ Y₀` y un mayorante no negativo `R ≥ G_vonMangoldt` en
`[Y, Y^{1 + δ}]` cuya integral con peso `y^{−θ − 1}` es `≤ Y^η`. -/
def HipotesisVentanaZeta (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 1 ≤ Y ∧ ∃ R : ℝ → ℝ,
    IntegrableOn (fun y => R y * y ^ (-θ - 1)) (Icc Y (Y ^ (1 + δ))) ∧
    (∀ y ∈ Icc Y (Y ^ (1 + δ)), 0 ≤ R y ∧ G_vonMangoldt y ≤ R y) ∧
    ∫ y in Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η

/-! ### Núcleo de Erlang `(u^k / k!) e^{−au}` y acotación de colas -/

theorem erlang_max (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) ≤ 1 / a ^ k := by
  have hterm : (a * u) ^ k / (k.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), (a * u) ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => (a * u) ^ i / (i.factorial : ℝ))
      (fun i _ => div_nonneg (pow_nonneg (mul_nonneg ha.le hu) i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hexp : ∑ i ∈ Finset.range (k + 1), (a * u) ^ i / (i.factorial : ℝ) ≤ Real.exp (a * u) :=
    Real.sum_le_exp_of_nonneg (mul_nonneg ha.le hu) (k + 1)
  have hle := hterm.trans hexp
  have hmul := mul_le_mul_of_nonneg_right hle (show 0 ≤ Real.exp (-a * u) / a ^ k by positivity)
  have hL : ((a * u) ^ k / (k.factorial : ℝ)) * (Real.exp (-a * u) / a ^ k)
      = u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) := by
    rw [mul_pow]
    have hak : a ^ k ≠ 0 := (pow_pos ha k).ne'
    field_simp
  have hR : Real.exp (a * u) * (Real.exp (-a * u) / a ^ k) = 1 / a ^ k := by
    rw [← mul_div_assoc, ← Real.exp_add, show a * u + -a * u = 0 by ring, Real.exp_zero]
  linarith

theorem erlang_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by
  have ha2 : 0 < a / 2 := half_pos ha
  have hmaj : IntegrableOn
      (fun u : ℝ => (1 / (a / 2) ^ k) * Real.exp (-(a / 2) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ha2).const_mul _
  refine hmaj.mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_of_nonneg (by positivity)]
  have hsplit : u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)
      = (u ^ k * Real.exp (-(a / 2) * u) / (k.factorial : ℝ)) * Real.exp (-(a / 2) * u) := by
    have : -a * u = -(a / 2) * u + -(a / 2) * u := by ring
    rw [this, Real.exp_add]
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (erlang_max k ha2 hu0) (Real.exp_pos _).le

theorem erlang_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) = 1 / a ^ (k + 1) := by
  induction k with
  | zero =>
    have hd : ∀ u ∈ Ici (0 : ℝ),
        HasDerivAt (fun t : ℝ => -(1 / a) * Real.exp (-a * t)) (Real.exp (-a * u)) u := by
      intro u _
      have h1 : HasDerivAt (fun t : ℝ => -a * t) (-a) u := by
        simpa using (hasDerivAt_id u).const_mul (-a)
      refine (h1.exp.const_mul (-(1 / a))).congr_deriv ?_
      field_simp
    have htend : Tendsto (fun t : ℝ => -(1 / a) * Real.exp (-a * t)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun t : ℝ => a * t) atTop atTop :=
          Filter.Tendsto.const_mul_atTop ha tendsto_id
        exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).congr fun t => by
          simp [Function.comp, neg_mul]
      simpa using h0.const_mul (-(1 / a))
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd (exp_neg_integrableOn_Ioi 0 ha) htend
    have hcongr : (fun u : ℝ => u ^ 0 * Real.exp (-a * u) / ((0 : ℕ).factorial : ℝ))
        = fun u : ℝ => Real.exp (-a * u) := by
      funext u; simp
    rw [hcongr, hftc]
    simp
  | succ k ih =>
    let F : ℝ → ℝ := fun t => -(t ^ (k + 1) * Real.exp (-a * t) / (((k + 1).factorial : ℝ) * a))
    have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt F
        (u ^ (k + 1) * Real.exp (-a * u) / ((k + 1).factorial : ℝ)
          - (1 / a) * (u ^ k * Real.exp (-a * u) / (k.factorial : ℝ))) u := by
      intro u _
      have h1 : HasDerivAt (fun t : ℝ => t ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * u ^ k) u := by
        simpa using hasDerivAt_pow (k + 1) u
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-a * t)) (-a * Real.exp (-a * u)) u := by
        have hlin : HasDerivAt (fun t : ℝ => -a * t) (-a) u := by
          simpa using (hasDerivAt_id' u).const_mul (-a)
        simpa [mul_comm] using hlin.exp
      have h3 := ((h1.mul h2).div_const (((k + 1).factorial : ℝ) * a)).neg
      refine h3.congr_deriv ?_
      rw [Nat.factorial_succ]
      push_cast
      have hfk : (k.factorial : ℝ) ≠ 0 := by positivity
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have ha' : a ≠ 0 := ha.ne'
      field_simp
      ring
    have htend : Tendsto F atTop (𝓝 0) := by
      have ha2 : 0 < a / 2 := half_pos ha
      have h0 : Tendsto (fun t : ℝ => (1 / (a / 2) ^ (k + 1) / a) * Real.exp (-(a / 2) * t))
          atTop (𝓝 0) := by
        have hlin : Tendsto (fun t : ℝ => (a / 2) * t) atTop atTop :=
          Filter.Tendsto.const_mul_atTop ha2 tendsto_id
        have hexp0 : Tendsto (fun t : ℝ => Real.exp (-(a / 2) * t)) atTop (𝓝 0) :=
          (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).congr fun t => by
            simp [Function.comp, neg_mul]
        simpa using hexp0.const_mul (1 / (a / 2) ^ (k + 1) / a)
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp only [F, Real.norm_eq_abs, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      have hmax := erlang_max (k + 1) ha2 ht
      have hsplit : t ^ (k + 1) * Real.exp (-a * t) / (((k + 1).factorial : ℝ) * a)
          = (t ^ (k + 1) * Real.exp (-(a / 2) * t) / ((k + 1).factorial : ℝ)) / a
              * Real.exp (-(a / 2) * t) := by
        have : -a * t = -(a / 2) * t + -(a / 2) * t := by ring
        rw [this, Real.exp_add]
        ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmax ha.le) (Real.exp_pos _).le
    have hi1 := erlang_integrable (k + 1) ha
    have hi2 := (erlang_integrable k ha).const_mul (1 / a)
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd (Integrable.sub hi1 hi2) htend
    rw [integral_sub hi1 hi2, integral_const_mul, ih] at hftc
    have F0 : F 0 = 0 := by simp [F]
    rw [F0, zero_sub] at hftc
    have ha' : a ≠ 0 := ha.ne'
    rw [pow_succ]
    field_simp at hftc ⊢
    linarith

theorem cola_chernoff_erlang (k : ℕ) {s l U V : ℝ} (hl : 0 ≤ l) (hs : l < s) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ)
      ≤ Real.exp (-(l * V)) / (s - l) ^ (k + 1) + Real.exp (l * U) / (s + l) ^ (k + 1) := by
  have ha : 0 < s - l := by linarith
  have hb : 0 < s + l := by linarith
  have hs0 : 0 < s := by linarith
  have i1 := (erlang_integrable k ha).const_mul (Real.exp (-(l * V)))
  have i2 := (erlang_integrable k hb).const_mul (Real.exp (l * U))
  have i0 := erlang_integrable k hs0
  have i3 : IntegrableOn
      (fun u : ℝ => Real.exp (-(l * V)) * (u ^ k * Real.exp (-(s - l) * u) / (k.factorial : ℝ))
        + Real.exp (l * U) * (u ^ k * Real.exp (-(s + l) * u) / (k.factorial : ℝ))) (Ioi 0) :=
    i1.add i2
  have hval : Real.exp (-(l * V)) / (s - l) ^ (k + 1) + Real.exp (l * U) / (s + l) ^ (k + 1)
      = ∫ u in Ioi (0 : ℝ),
          (Real.exp (-(l * V)) * (u ^ k * Real.exp (-(s - l) * u) / (k.factorial : ℝ))
            + Real.exp (l * U) * (u ^ k * Real.exp (-(s + l) * u) / (k.factorial : ℝ))) := by
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
      erlang_integral k ha, erlang_integral k hb]
    ring
  rw [hval]
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  refine (setIntegral_mono_on (i0.mono_set sdiff_subset) (i3.mono_set sdiff_subset) hm ?_).trans
    (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)
  · intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
    have hn := hu.2
    rw [mem_Icc, not_and_or, not_le, not_le] at hn
    have key : Real.exp (-s * u)
        ≤ Real.exp (-(l * V)) * Real.exp (-(s - l) * u)
          + Real.exp (l * U) * Real.exp (-(s + l) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      rcases hn with hlt | hgt
      · have hle : -s * u ≤ l * U + -(s + l) * u := by nlinarith
        linarith [Real.exp_le_exp.mpr hle, Real.exp_pos (-(l * V) + -(s - l) * u)]
      · have hle : -s * u ≤ -(l * V) + -(s - l) * u := by nlinarith
        linarith [Real.exp_le_exp.mpr hle, Real.exp_pos (l * U + -(s + l) * u)]
    calc u ^ k * Real.exp (-s * u) / (k.factorial : ℝ)
        = (u ^ k / (k.factorial : ℝ)) * Real.exp (-s * u) := by ring
      _ ≤ (u ^ k / (k.factorial : ℝ)) *
            (Real.exp (-(l * V)) * Real.exp (-(s - l) * u)
              + Real.exp (l * U) * Real.exp (-(s + l) * u)) :=
          mul_le_mul_of_nonneg_left key hp
      _ = _ := by ring
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := hu.le
    positivity

theorem cota_potencia_cola (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + (k : ℝ) * ((σ - a) / a) ≤ c) :
    Real.exp x / a ^ (k + 1) ≤ (Real.exp c / a) / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp ((k : ℝ) * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc Real.exp x * (σ / a) ^ k
        ≤ Real.exp x * Real.exp ((k : ℝ) * ((σ - a) / a)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos x).le
      _ = Real.exp (x + (k : ℝ) * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp c := Real.exp_le_exp.mpr h
  calc Real.exp x / a ^ (k + 1)
      = (Real.exp x * (σ / a) ^ k / a) / σ ^ k := by
          rw [div_pow, pow_succ]
          field_simp
    _ ≤ (Real.exp c / a) / σ ^ k := by gcongr

/-- Selección de `σ > 2` y `k = ⌈(1 + δ/2) σ U⌉₊` para localizar el núcleo en `[U, (1 + δ) U]`. -/
theorem cola_erlang_ventana {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C_cola : ℝ, 0 ≤ C_cola ∧ ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U),
        u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) ≤ C_cola / σ ^ k := by
  set l : ℝ := 2 + 6 / δ with hl_def
  have hl2 : 2 < l := by
    have h6 : 0 < 6 / δ := div_pos (by norm_num) hδ
    linarith [hl_def]
  have hld : l * δ = 6 + 2 * δ := by rw [hl_def]; field_simp; ring_nf
  set M : ℝ := l * (1 + δ) with hM_def
  have hMl : l < M := by rw [hM_def]; nlinarith
  set σ : ℝ := M * (2 + l) with hσ_def
  have hσ_gt : l * (2 + l) < σ := by rw [hσ_def]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  set C_cola : ℝ := Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l)
  refine ⟨σ, by linarith, C_cola, by positivity, fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  set k : ℕ := ⌈(1 + δ / 2) * σ * U⌉₊
  have hk1 : (1 + δ / 2) * σ * U ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ (1 + δ / 2) * σ * U + 1 := (Nat.ceil_lt_add_one hx).le
  refine ⟨k, ?_, ?_⟩
  · have hσU : 0 ≤ σ * U := by positivity
    nlinarith [mul_nonneg hδ.le hσU]
  · have e_exp : (2 - σ) = -(σ - 2) := by ring
    simp only [e_exp, C_cola, add_div]
    refine (cola_chernoff_erlang k (by linarith) hs).trans (add_le_add ?_ ?_)
    · apply cota_potencia_cola k hσ0 ha
      have hM1_pos : 0 < M - 1 := by linarith
      have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
        rw [div_eq_div_iff ha.ne' hM1_pos.ne', hσ_def]; ring
      have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
        have : (1 + δ / 2) * (2 + l) = M - 1 := by rw [hM_def]; nlinarith
        rw [hσ_def, ← this]; ring
      have hM1_ge : 1 ≤ M - 1 := by linarith
      have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
        rw [mul_one_div, div_le_iff₀ hM1_pos]
        nlinarith [hk2, e2]
      have e4 : l * ((1 + δ) * U) = M * U := by rw [hM_def]; ring
      rw [e1, e4]; linarith
    · apply cota_potencia_cola k hσ0 hb
      have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l))
          = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by ring
      have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
      have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
        rw [le_div_iff₀ hb]
        have p1 : (1 + δ / 2) * σ * U * (l - 2) ≤ (k : ℝ) * (l - 2) :=
          mul_le_mul_of_nonneg_right hk1 (by linarith)
        have p2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
        have p3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
        have p4 := mul_le_mul_of_nonneg_right p3 (by linarith : 0 ≤ U)
        nlinarith
      rw [e1]; linarith

/-! ### Derivadas reiteradas de `Phi_zeta` en `Re s > 2` -/

theorem iteratedDeriv_Phi_zeta_laplace (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Phi_zeta s / (k.factorial : ℂ)
      = ∫ u in Ioi (0 : ℝ),
          ((G_vonMangoldt (Real.exp u) : ℝ) : ℂ) * (u : ℂ) ^ k * Complex.exp (-s * u)
            / (k.factorial : ℂ) := by
  set g : ℝ → ℝ := fun u => G_vonMangoldt (Real.exp u)
  have hg_meas : Measurable g := measurable_G_vonMangoldt.comp Real.measurable_exp
  set C₀ : ℝ := 4 + |Real.eulerMascheroniConstant|
  have hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u) := by
    intro u hu
    have he2 : (Real.exp u) ^ 2 = Real.exp (2 * u) := by rw [sq, ← Real.exp_add]; ring_nf
    simpa [g, C₀, he2] using abs_G_vonMangoldt_le (Real.one_le_exp hu)
  have hint_pow : ∀ (n : ℕ) {b : ℝ}, 0 < b →
      IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
    intro n b hb
    have hmul : IntegrableOn
        (fun u : ℝ => u ^ n * Real.exp (-b * u) / (n.factorial : ℝ) * (n.factorial : ℝ)) (Ioi 0) :=
      (erlang_integrable n hb).mul_const (n.factorial : ℝ)
    refine hmul.congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp only
    have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  have hmeas_F : ∀ (n : ℕ) (z : ℂ),
      AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ n * Complex.exp (-z * u))
        (volume.restrict (Ioi (0 : ℝ))) := fun n z =>
    (((Complex.measurable_ofReal.comp hg_meas).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  have hbound_F : ∀ (n : ℕ) {b : ℝ} {z : ℂ}, 2 + b ≤ z.re → ∀ u : ℝ, 0 < u →
      ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ n * Complex.exp (-z * u)‖
        ≤ C₀ * (u ^ n * Real.exp (-b * u)) := by
    intro n b z hz u hu
    have h1 : ‖(g u : ℂ)‖ ≤ C₀ * Real.exp (2 * u) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hgC u hu.le
    have h2 : ‖((-u : ℝ) : ℂ) ^ n‖ = u ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
    have h3 : ‖Complex.exp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
      rw [Complex.norm_exp]
      have hre : (-z * (u : ℂ)).re = -z.re * u := by simp
      rw [hre]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [norm_mul, norm_mul, h2]
    calc ‖(g u : ℂ)‖ * u ^ n * ‖Complex.exp (-z * u)‖
        ≤ (C₀ * Real.exp (2 * u)) * u ^ n * Real.exp (-(2 + b) * u) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
            (by positivity)
      _ = C₀ * (u ^ n * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
      _ = C₀ * (u ^ n * Real.exp (-b * u)) := by rw [← Real.exp_add]; congr 2; ring
  have hstep : ∀ (n : ℕ) {z : ℂ}, 2 < z.re →
      HasDerivAt (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ n * Complex.exp (-w * u))
        (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (n + 1) * Complex.exp (-z * u)) z := by
    intro n z hz
    set b : ℝ := (z.re - 2) / 2 with hb_def
    have hb : 0 < b := by rw [hb_def]; linarith
    have hball_re : ∀ w ∈ Metric.ball z b, 2 + b ≤ w.re := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (w - z)).trans hw.le)).1
      simp only [sub_re] at h1
      linarith [hb_def]
    have hint0 : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ n * Complex.exp (-z * u))
        (volume.restrict (Ioi 0)) := by
      refine ((hint_pow n hb).const_mul C₀).mono' (hmeas_F n z) ?_
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
        hbound_F n (hball_re z (Metric.mem_ball_self hb)) u hu)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ n * Complex.exp (-w * u))
      (F' := fun w u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (n + 1) * Complex.exp (-w * u))
      (Metric.ball_mem_nhds z hb)
      (Eventually.of_forall fun w => hmeas_F n w) hint0 (hmeas_F (n + 1) z) ?_
      ((hint_pow (n + 1) hb).const_mul C₀) ?_).2
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu w hw =>
        hbound_F (n + 1) (hball_re w hw) u hu)
    · refine Eventually.of_forall fun u w _ => ?_
      have hlin : HasDerivAt (fun ζ : ℂ => -ζ * (u : ℂ)) (-(u : ℂ)) w := by
        simpa using (hasDerivAt_id' w).neg.mul_const (u : ℂ)
      refine (hlin.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ n)).congr_deriv ?_
      push_cast; ring
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hiter : ∀ (j : ℕ) {z : ℂ}, 2 < z.re →
      iteratedDeriv j Phi_zeta z
        = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * Complex.exp (-z * u) := by
    intro j
    induction j with
    | zero =>
      intro z hz
      simpa [g] using Phi_zeta_eq_laplace hz
    | succ j ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j Phi_zeta
          =ᶠ[𝓝 z] fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * Complex.exp (-w * u) :=
        Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ih hw
      rw [hev.deriv_eq]
      exact (hstep j hz).deriv
  rw [hiter k hs, ← integral_const_mul, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have hneg_pow : (-1 : ℂ) ^ k * ((-u : ℝ) : ℂ) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]
    push_cast
    ring_nf
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * Complex.exp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * ((-u : ℝ) : ℂ) ^ k) * Complex.exp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * Complex.exp (-s * u) / (k.factorial : ℂ) := by rw [hneg_pow]

/-! ### Cota unilateral de las derivadas de `Phi_zeta` en `σ` y `σ + iγ` -/

theorem cota_derivadas_de_ventana {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : HipotesisVentanaZeta θ δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      ∀ γ : ℝ,
        ‖(-1) ^ k * iteratedDeriv k Phi_zeta ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖
          + ((-1) ^ k * iteratedDeriv k Phi_zeta (σ : ℂ) / (k.factorial : ℂ)).re
            ≤ C * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, C_cola, hC_cola0, hcola⟩ := cola_erlang_ventana hδ
  set C₀ : ℝ := 4 + |Real.eulerMascheroniConstant|
  have hC₀_pos : 0 < C₀ := by positivity
  set g : ℝ → ℝ := fun u => G_vonMangoldt (Real.exp u)
  have hg_meas : Measurable g := measurable_G_vonMangoldt.comp Real.measurable_exp
  have hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u) := by
    intro u hu
    have he2 : (Real.exp u) ^ 2 = Real.exp (2 * u) := by rw [sq, ← Real.exp_add]; ring_nf
    simpa [g, C₀, he2] using abs_G_vonMangoldt_le (Real.one_le_exp hu)
  refine ⟨σ, hσ, 2 + 2 * C₀ * C_cola, fun η hη U₀ => ?_⟩
  obtain ⟨Y, hYU₀, hY1, R_y, hRy_int, hRy_bd, hRy_le⟩ := hW η hη (Real.exp (max U₀ 1))
  have hY_ge_e : Real.exp 1 ≤ Y := (Real.exp_le_exp.mpr (le_max_right U₀ 1)).trans hYU₀
  set U : ℝ := Real.log Y
  have hU_ge1 : 1 ≤ U := by
    have := Real.log_le_log (Real.exp_pos 1) hY_ge_e
    rwa [Real.log_exp] at this
  have hU_geU₀ : U₀ ≤ U := by
    have h1 : Real.exp U₀ ≤ Y := (Real.exp_le_exp.mpr (le_max_left U₀ 1)).trans hYU₀
    have h2 := Real.log_le_log (Real.exp_pos U₀) h1
    rwa [Real.log_exp] at h2
  have hY_eq : Real.exp U = Y := Real.exp_log (lt_of_lt_of_le (Real.exp_pos 1) hY_ge_e)
  have hYδ_eq : Real.exp ((1 + δ) * U) = Y ^ (1 + δ) := by
    rw [Real.rpow_def_of_pos (lt_of_lt_of_le (Real.exp_pos 1) hY_ge_e), mul_comm]
  -- Cambio de variable `y = e^u` en la ventana `[U, (1 + δ) U]`.
  let R : ℝ → ℝ := fun u => R_y (Real.exp u)
  have himg_win : Real.exp '' Icc U ((1 + δ) * U) = Icc Y (Y ^ (1 + δ)) := by
    ext y
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      exact ⟨hY_eq ▸ Real.exp_le_exp.mpr hu1, hYδ_eq ▸ Real.exp_le_exp.mpr hu2⟩
    · rintro ⟨hy1, hy2⟩
      have hy_pos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le (Real.exp_pos 1) hY_ge_e) hy1
      refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy_pos⟩
      · rw [← Real.exp_le_exp, Real.exp_log hy_pos, hY_eq]; exact hy1
      · rw [← Real.exp_le_exp, Real.exp_log hy_pos, hYδ_eq]; exact hy2
  have hR_int : IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U ((1 + δ) * U)) := by
    have hcomp : IntegrableOn
        (fun u : ℝ => |Real.exp u| • (R_y (Real.exp u) * (Real.exp u) ^ (-θ - 1)))
        (Icc U ((1 + δ) * U)) :=
      (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
        (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn
        (fun y => R_y y * y ^ (-θ - 1))).mp
        (by rwa [himg_win] : IntegrableOn (fun y => R_y y * y ^ (-θ - 1))
          (Real.exp '' Icc U ((1 + δ) * U)))
    refine hcomp.congr_fun (fun u _ => ?_) measurableSet_Icc
    dsimp only [R]
    rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos u),
      Real.log_exp]
    calc Real.exp u * (R_y (Real.exp u) * Real.exp (u * (-θ - 1)))
        = R_y (Real.exp u) * (Real.exp u * Real.exp (u * (-θ - 1))) := by ring
      _ = R_y (Real.exp u) * Real.exp (-θ * u) := by rw [← Real.exp_add]; congr 2; ring
  have hR_le : ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) ≤ Real.exp (η * U) := by
    have hchg : ∫ y in Icc Y (Y ^ (1 + δ)), R_y y * y ^ (-θ - 1)
        = ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) := by
      rw [← himg_win, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
        (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
      refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
      rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos u),
        Real.log_exp]
      simp only [R]
      calc Real.exp u * (R_y (Real.exp u) * Real.exp (u * (-θ - 1)))
          = R_y (Real.exp u) * (Real.exp u * Real.exp (u * (-θ - 1))) := by ring
        _ = R_y (Real.exp u) * Real.exp (-θ * u) := by rw [← Real.exp_add]; congr 2; ring
    have hYη : Y ^ η = Real.exp (η * U) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le (Real.exp_pos 1) hY_ge_e), mul_comm]
    linarith [hRy_le]
  have hR_bd : ∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ R u ∧ g u ≤ R u := by
    intro u hu
    have hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← himg_win]; exact mem_image_of_mem _ hu
    exact hRy_bd (Real.exp u) hmem
  obtain ⟨k, hkU, hk_cola⟩ := hcola U hU_ge1
  refine ⟨U, hU_geU₀, k, hkU, fun γ => ?_⟩
  rw [iteratedDeriv_Phi_zeta_laplace k (by simp; linarith),
    iteratedDeriv_Phi_zeta_laplace k (by simp; linarith)]
  -- Desigualdad en `(0, ∞)` separando `[U, (1 + δ) U]` y su complemento.
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ)
  set h : ℝ → ℝ := fun u => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)
  have hhi : IntegrableOn h (Ioi 0) := by
    have heq : h = fun u => u ^ k * Real.exp (-(σ - 2) * u) / (k.factorial : ℝ) := by
      funext u; simp only [h]; congr 2; ring
    rw [heq]
    exact erlang_integrable k (by linarith : 0 < σ - 2)
  have hw0 : ∀ u, 0 ≤ u → 0 ≤ w u := fun u hu => by simp only [w]; positivity
  have hwm : Measurable w := by simp only [w]; fun_prop
  have hb_pt : ∀ u, 0 ≤ u → |g u| * w u ≤ C₀ * h u := by
    intro u hu
    have heq : C₀ * h u = (C₀ * Real.exp (2 * u)) * w u := by
      simp only [w, h]
      have : (2 - σ) * u = 2 * u + -σ * u := by ring
      rw [this, Real.exp_add]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hgC u hu) (hw0 u hu)
  have hI1 : IntegrableOn (fun u => |g u| * w u) (Ioi 0) := by
    refine (hhi.const_mul C₀).mono' (hg_meas.abs.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hw0 u hu.le))]
    exact hb_pt u hu.le
  have hI2 : IntegrableOn (fun u => g u * w u) (Ioi 0) := by
    refine (hhi.const_mul C₀).mono' (hg_meas.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hw0 u hu.le), Real.norm_eq_abs]
    exact hb_pt u hu.le
  have hL : ‖∫ u in Ioi (0 : ℝ),
        (g u : ℂ) * (u : ℂ) ^ k * Complex.exp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖
      ≤ ∫ u in Ioi (0 : ℝ), |g u| * w u := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := hu.le
    have hre : (-((σ : ℂ) + γ * I) * (u : ℂ)).re = -σ * u := by simp
    simp only [w, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, hre,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hu0]
    ring
  have hRe : (∫ u in Ioi (0 : ℝ),
        (g u : ℂ) * (u : ℂ) ^ k * Complex.exp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re
      = ∫ u in Ioi (0 : ℝ), g u * w u := by
    have hfun : (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ k * Complex.exp (-(σ : ℂ) * u) / (k.factorial : ℂ))
        = fun u : ℝ => ((g u * w u : ℝ) : ℂ) := by
      funext u
      simp only [w]
      push_cast; ring
    rw [hfun, integral_complex_ofReal, ofReal_re]
  have hI3 : IntegrableOn (fun u => |g u| * w u + g u * w u) (Ioi 0) := hI1.add hI2
  set V : ℝ := (1 + δ) * U
  have hsub : Icc U V ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le (by linarith) hu.1
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ)) (t := Icc U V)
    measurableSet_Icc hI3
  rw [inter_eq_right.mpr hsub, integral_add hI1 hI2] at hsplit
  have hA : ∫ u in Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * (1 / (σ - θ) ^ k) * ∫ u in Icc U V, R u * Real.exp (-θ * u) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hI3.mono_set hsub) (hR_int.const_mul _) measurableSet_Icc fun u hu => ?_
    have hu0 : 0 ≤ u := (hsub hu).le
    obtain ⟨hR0, hgR⟩ := hR_bd u hu
    have h2R : |g u| + g u ≤ 2 * R u := by
      rcases abs_cases (g u) with hc | hc <;> linarith [hc.1]
    have hw_bd : w u ≤ (1 / (σ - θ) ^ k) * Real.exp (-θ * u) := by
      have hm := erlang_max k (by linarith : 0 < σ - θ) hu0
      have heq : w u = (u ^ k * Real.exp (-(σ - θ) * u) / (k.factorial : ℝ)) * Real.exp (-θ * u) := by
        simp only [w]
        have : -σ * u = -(σ - θ) * u + -θ * u := by ring
        rw [this, Real.exp_add]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    calc |g u| * w u + g u * w u = (|g u| + g u) * w u := by ring
      _ ≤ (2 * R u) * w u := mul_le_mul_of_nonneg_right h2R (hw0 u hu0)
      _ ≤ (2 * R u) * ((1 / (σ - θ) ^ k) * Real.exp (-θ * u)) :=
          mul_le_mul_of_nonneg_left hw_bd (by linarith)
      _ = _ := by ring
  have hB : ∫ u in Ioi (0 : ℝ) \ Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, h u := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hI3.mono_set sdiff_subset) ((hhi.mono_set sdiff_subset).const_mul _)
      (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
    have hu0 : 0 ≤ u := hu.1.le
    have h1 := hb_pt u hu0
    have h2 : g u * w u ≤ |g u| * w u := mul_le_mul_of_nonneg_right (le_abs_self _) (hw0 u hu0)
    linarith
  have hst : 0 < σ - θ := by linarith
  have hstk : 0 < (σ - θ) ^ k := pow_pos hst k
  have hexp1 : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have htail_final : C_cola / σ ^ k ≤ C_cola * Real.exp (η * U) / (σ - θ) ^ k := by
    apply div_le_div₀ (by positivity) _ hstk (pow_le_pow_left₀ hst.le (by linarith) k)
    exact le_mul_of_one_le_right hC_cola0 hexp1
  have hmain1 : 2 * (1 / (σ - θ) ^ k) * ∫ u in Icc U V, R u * Real.exp (-θ * u)
      ≤ 2 * Real.exp (η * U) / (σ - θ) ^ k := by
    have := mul_le_mul_of_nonneg_left hR_le (show 0 ≤ 2 * (1 / (σ - θ) ^ k) by positivity)
    linarith [show 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) = 2 * Real.exp (η * U) / (σ - θ) ^ k by ring]
  have hmain2 : 2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, h u
      ≤ 2 * C₀ * (C_cola * Real.exp (η * U) / (σ - θ) ^ k) :=
    mul_le_mul_of_nonneg_left (hk_cola.trans htail_final) (by positivity)
  rw [hRe]
  have hsum_final : (2 + 2 * C₀ * C_cola) * Real.exp (η * U) / (σ - θ) ^ k
      = 2 * Real.exp (η * U) / (σ - θ) ^ k + 2 * C₀ * (C_cola * Real.exp (η * U) / (σ - θ) ^ k) := by ring
  linarith

/-! ### Estimación de Cauchy, asintótica del polo simple y geometría de conductor 1 -/

theorem cauchy_iteratedDeriv {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ}
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r)) (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩
  have hR : (R : ℝ) = r' := rfl
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hsub : Metric.closedBall z (R : ℝ) ⊆ Metric.ball z r := by
    rw [hR]; exact Metric.closedBall_subset_ball h1
  have hRpos : (0 : NNReal) < R := by show (0 : ℝ) < (R : ℝ); rw [hR]; exact h0
  have hp := (hd.mono hsub).hasFPowerSeriesOnBall hRpos
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by rw [hR, abs_of_pos h0, inv_pow, div_eq_mul_inv]

theorem asintotica_polo_simple {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ}
    (hρ : ρ ∈ Metric.ball z r) (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  let H : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ)
  have hHeq : H =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · subst hsρ; simp [H]
    · simp only [H, if_neg hsρ]; rw [hs (Set.mem_compl_singleton_iff.mpr hsρ)]; ring
  have hHd : DifferentiableOn ℂ H (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · subst hsρ
      exact (hHeq.differentiableAt_iff.mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : H =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        have htρ : t ≠ ρ := ht.2
        simp only [H, if_neg htρ]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact (hloc.differentiableAt_iff.mpr hd').differentiableWithinAt
  obtain ⟨M, hM⟩ := cauchy_iteratedDeriv hHd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hmemz : z ∈ Metric.ball z r \ {ρ} := ⟨Metric.mem_ball_self hr, hzρ⟩
  have hloc : Φ =ᶠ[𝓝 z] H + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmemz] with t ht
    have htρ : t ≠ ρ := ht.2
    simp only [Pi.add_apply, H, if_neg htρ, div_eq_mul_inv]; ring
  have hHc : ContDiffAt ℂ k H z :=
    (hHd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzρ))
  have hpole_deriv : iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z
      = c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z
    rw [e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv,
      show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hHc hPc, hpole_deriv]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  set iH := iteratedDeriv k H z
  set X := (z - ρ) ^ (k + 1)
  have e : (-1) ^ k * (iH + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X
      = (-1) ^ k * (iH / k.factorial) := by
    calc _ = (-1) ^ k * (iH / k.factorial)
            + ((-1) ^ k * (-1) ^ k) * c * ((k.factorial : ℂ) / k.factorial) * X⁻¹ - c / X := by ring
      _ = _ := by rw [hpow, div_self hfac, div_eq_mul_inv c]; ring
  rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

/-- Conjunto de ceros de `ζ` en el semiplano derecho `{Re w > 0}`. -/
def cerosDerecha : Set ℂ := {w : ℂ | 0 < w.re ∧ riemannZeta w = 0}

theorem cerosDerecha_conj {w : ℂ} (hw : w ∈ cerosDerecha) : starRingEnd ℂ w ∈ cerosDerecha := by
  obtain ⟨hw_re, hw0⟩ := hw
  have hw1 : w ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hw0)
  have hcw_re : 0 < (starRingEnd ℂ w).re := by simpa using hw_re
  have hcw1 : starRingEnd ℂ w ≠ 1 := fun h => hw1 (by simpa using congrArg (starRingEnd ℂ) h)
  refine ⟨hcw_re, ?_⟩
  have hfract_conj : fractIntegral (starRingEnd ℂ w) = starRingEnd ℂ (fractIntegral w) := by
    unfold fractIntegral
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    rw [map_mul, conj_ofReal]
    congr 1
    rw [cpow_def_of_ne_zero htC, cpow_def_of_ne_zero htC, ← Complex.exp_conj, map_mul,
      ← ofReal_log ht0.le, conj_ofReal]
    congr 2
    simp
  rw [zeta_eq_integral_fract hcw_re hcw1, hfract_conj]
  have h := congrArg (starRingEnd ℂ) (zeta_eq_integral_fract hw_re hw1)
  rw [hw0, map_zero, map_sub, map_div₀, map_sub, map_one, map_mul] at h
  exact h.symm

theorem finite_closedBall_inter_cerosDerecha (c : ℂ) (R : ℝ) :
    (Metric.closedBall c R ∩ cerosDerecha).Finite := by
  have hiso : ∀ z : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ Metric.ball z ε, w ≠ z → riemannZeta w ≠ 0 := by
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp (ceros_aislados_zeta z))
    exact ⟨ε, hε, fun w hw hne => hball hw hne⟩
  choose rad hrad_pos hrad_ne using hiso
  obtain ⟨t, ht_cover⟩ := (isCompact_closedBall c R).elim_finite_subcover
    (fun z : ℂ => Metric.ball z (rad z)) (fun _ => Metric.isOpen_ball)
    (fun z _ => mem_iUnion.mpr ⟨z, Metric.mem_ball_self (hrad_pos z)⟩)
  refine (t.finite_toSet.biUnion fun z _ => Set.finite_singleton z).subset ?_
  intro w ⟨hw_ball, hw_zero⟩
  obtain ⟨z, hz_mem, hw_in⟩ := mem_iUnion₂.mp (ht_cover hw_ball)
  refine mem_iUnion₂.mpr ⟨z, hz_mem, ?_⟩
  by_contra hne
  exact hrad_ne z w hw_in hne hw_zero.2

/-- Desempate vertical: si existe un cero `w₀ ∈ cerosDerecha` a distancia `< L` de `σ + i t₀`
(con `0 < L` y `2 < σ`), perturbando ligeramente `t₀` se obtiene un único cero más cercano. -/
theorem unico_cero_cercano {σ t₀ L : ℝ} (hσ : 2 < σ) (_hL0 : 0 < L)
    {w₀ : ℂ} (hw₀ : w₀ ∈ cerosDerecha) (hd₀ : dist w₀ ((σ : ℂ) + t₀ * I) < L) :
    ∃ γ : ℝ, ∃ ρ ∈ cerosDerecha, ∃ r : ℝ,
      dist ρ ((σ : ℂ) + γ * I) < L ∧
      dist ρ ((σ : ℂ) + γ * I) < r ∧
      (∀ w ∈ cerosDerecha, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ) := by
  set z₀ : ℂ := (σ : ℂ) + t₀ * I
  set R₁ : ℝ := L + 1
  let F₁ : Finset ℂ := (finite_closedBall_inter_cerosDerecha z₀ R₁).toFinset
  have hmem_F₁ : ∀ w, w ∈ F₁ ↔ w ∈ Metric.closedBall z₀ R₁ ∧ w ∈ cerosDerecha := fun w =>
    Set.Finite.mem_toFinset _
  have hw₀_F₁ : w₀ ∈ F₁ := (hmem_F₁ w₀).mpr ⟨Metric.mem_closedBall.mpr (by linarith), hw₀⟩
  obtain ⟨w_min, hw_min_F₁, hw_min_le⟩ := Finset.exists_min_image F₁ (fun w => dist w z₀) ⟨w₀, hw₀_F₁⟩
  set d₀ : ℝ := dist w_min z₀
  have hd₀_lt : d₀ < L := (hw_min_le w₀ hw₀_F₁).trans_lt hd₀
  have hd₀_nn : 0 ≤ d₀ := dist_nonneg
  let S₀ : Finset ℂ := F₁.filter (fun w => dist w z₀ = d₀)
  have hS₀_ne : S₀.Nonempty := ⟨w_min, Finset.mem_filter.mpr ⟨hw_min_F₁, rfl⟩⟩
  obtain ⟨ρ, hρ_S₀, hρ_im_max⟩ := Finset.exists_max_image S₀ Complex.im hS₀_ne
  have hρ_F₁ : ρ ∈ F₁ := (Finset.mem_filter.mp hρ_S₀).1
  have hρ_dist : dist ρ z₀ = d₀ := (Finset.mem_filter.mp hρ_S₀).2
  have hρ_Z : ρ ∈ cerosDerecha := ((hmem_F₁ ρ).mp hρ_F₁).2
  -- Todo `w ∈ S₀ \ {ρ}` tiene `w.im < ρ.im` porque `Re w < 1 < σ`.
  have hS₀_im_lt : ∀ w ∈ S₀, w ≠ ρ → w.im < ρ.im := by
    intro w hw hne
    have hw_le := hρ_im_max w hw
    rcases lt_or_eq_of_le hw_le with hlt | heq
    · exact hlt
    · exfalso
      have hw_Z : w ∈ cerosDerecha := ((hmem_F₁ w).mp (Finset.mem_filter.mp hw).1).2
      have hw_re1 : w.re < 1 := by
        by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw_Z.2
      have hρ_re1 : ρ.re < 1 := by
        by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hρ_Z.2
      have hw_d : dist w z₀ = d₀ := (Finset.mem_filter.mp hw).2
      have hsq_eq : ‖w - z₀‖ ^ 2 = ‖ρ - z₀‖ ^ 2 := by
        rw [← dist_eq_norm, ← dist_eq_norm, hw_d, hρ_dist]
      have hnorm_sq : ∀ u : ℂ, ‖u - z₀‖ ^ 2 = (u.re - σ) ^ 2 + (u.im - t₀) ^ 2 := by
        intro u
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [z₀]; ring
      rw [hnorm_sq w, hnorm_sq ρ, heq] at hsq_eq
      have hre_sq : (w.re - σ) ^ 2 = (ρ.re - σ) ^ 2 := by linarith
      have hre_eq : w.re = ρ.re := by nlinarith
      exact hne (Complex.ext hre_eq heq)
  -- Si `F₁.erase ρ` es vacío, no hace falta perturbar `t₀`.
  by_cases hrem : (F₁.erase ρ).Nonempty
  · let Resto : Finset ℂ := (F₁.erase ρ).filter (fun w => w ∉ S₀)
    have hgap_pos : ∀ w ∈ Resto, 0 < ‖w - z₀‖ ^ 2 - d₀ ^ 2 := by
      intro w hw
      have hw_F₁ : w ∈ F₁ := Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
      have hw_not : w ∉ S₀ := (Finset.mem_filter.mp hw).2
      have hle : d₀ ≤ dist w z₀ := hw_min_le w hw_F₁
      have hne_d : dist w z₀ ≠ d₀ := fun h => hw_not (Finset.mem_filter.mpr ⟨hw_F₁, h⟩)
      have hlt_d : d₀ < ‖w - z₀‖ := by rw [← dist_eq_norm]; exact lt_of_le_of_ne hle hne_d.symm
      nlinarith [norm_nonneg (w - z₀)]
    set ε₁ : ℝ := min ((L - d₀) / 2) (1 / 4)
    have hε₁_pos : 0 < ε₁ := lt_min (by linarith) (by norm_num)
    obtain ⟨ε, hε_pos, hε_le1, hε_resto⟩ :
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₁ ∧
          ∀ w ∈ Resto, 2 * ε * |ρ.im - w.im| < ‖w - z₀‖ ^ 2 - d₀ ^ 2 := by
      by_cases hR_ne : Resto.Nonempty
      · obtain ⟨w₁, hw₁, hw₁_min⟩ := Finset.exists_min_image Resto
          (fun w => (‖w - z₀‖ ^ 2 - d₀ ^ 2) / (2 * (|ρ.im - w.im| + 1))) hR_ne
        set B_min := (‖w₁ - z₀‖ ^ 2 - d₀ ^ 2) / (2 * (|ρ.im - w₁.im| + 1))
        have hB_pos : 0 < B_min := div_pos (hgap_pos w₁ hw₁) (by positivity)
        refine ⟨min ε₁ (B_min / 2), lt_min hε₁_pos (half_pos hB_pos), min_le_left _ _, fun w hw => ?_⟩
        have hle_B : min ε₁ (B_min / 2) < (‖w - z₀‖ ^ 2 - d₀ ^ 2) / (2 * (|ρ.im - w.im| + 1)) :=
          (min_le_right _ _).trans_lt ((half_lt_self hB_pos).trans_le (hw₁_min w hw))
        have hden_pos : 0 < 2 * (|ρ.im - w.im| + 1) := by positivity
        have hm := (lt_div_iff₀ hden_pos).mp hle_B
        have h_nn : 0 < min ε₁ (B_min / 2) := lt_min hε₁_pos (half_pos hB_pos)
        nlinarith [abs_nonneg (ρ.im - w.im)]
      · exact ⟨ε₁, hε₁_pos, le_rfl, fun w hw => absurd ⟨w, hw⟩ hR_ne⟩
    set γ : ℝ := t₀ + ε
    set z₁ : ℂ := (σ : ℂ) + γ * I
    have hz₁_sub : z₁ - z₀ = (ε : ℂ) * I := by simp [z₁, z₀, γ]; ring
    have hz₁_dist : dist z₁ z₀ = ε := by
      rw [dist_eq_norm, hz₁_sub, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε_pos]
    have hd₁_lt_L : dist ρ z₁ < L := by
      have htri : dist ρ z₁ ≤ dist ρ z₀ + dist z₀ z₁ := dist_triangle ρ z₀ z₁
      rw [hρ_dist, dist_comm z₀ z₁, hz₁_dist] at htri
      have : ε ≤ (L - d₀) / 2 := hε_le1.trans (min_le_left _ _)
      linarith
    have hstrict : ∀ w ∈ F₁.erase ρ, dist ρ z₁ < dist w z₁ := by
      intro w hw
      have hw_ne : w ≠ ρ := (Finset.mem_erase.mp hw).1
      have hw_F₁ : w ∈ F₁ := (Finset.mem_erase.mp hw).2
      have hid : ∀ u : ℂ, ‖u - z₁‖ ^ 2 = ‖u - z₀‖ ^ 2 - 2 * ε * (u.im - t₀) + ε ^ 2 := by
        intro u
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp [z₁, z₀, γ]; ring
      have hdiff_sq : ‖w - z₁‖ ^ 2 - ‖ρ - z₁‖ ^ 2
          = (‖w - z₀‖ ^ 2 - d₀ ^ 2) + 2 * ε * (ρ.im - w.im) := by
        rw [hid w, hid ρ, ← dist_eq_norm ρ z₀, hρ_dist]
        ring
      have hpos_diff : 0 < ‖w - z₁‖ ^ 2 - ‖ρ - z₁‖ ^ 2 := by
        rw [hdiff_sq]
        by_cases hwS : w ∈ S₀
        · have h_eq0 : ‖w - z₀‖ = d₀ := by rw [← dist_eq_norm]; exact (Finset.mem_filter.mp hwS).2
          rw [h_eq0, sub_self, zero_add]
          have him_lt := hS₀_im_lt w hwS hw_ne
          nlinarith
        · have hwR : w ∈ Resto := Finset.mem_filter.mpr ⟨hw, hwS⟩
          have hbd := hε_resto w hwR
          have habs : -(2 * ε * |ρ.im - w.im|) ≤ 2 * ε * (ρ.im - w.im) := by
            nlinarith [neg_abs_le (ρ.im - w.im)]
          linarith
      rw [dist_eq_norm, dist_eq_norm]
      by_contra hnot
      have hle_n : ‖w - z₁‖ ≤ ‖ρ - z₁‖ := not_lt.mp hnot
      have : ‖w - z₁‖ ^ 2 ≤ ‖ρ - z₁‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle_n 2
      linarith
    obtain ⟨w₂, hw₂_mem, hw₂_min⟩ := Finset.exists_min_image (F₁.erase ρ) (fun w => dist w z₁) hrem
    set r : ℝ := min (L + 1 / 2) (dist w₂ z₁)
    have hr_gt : dist ρ z₁ < r := lt_min (by linarith) (hstrict w₂ hw₂_mem)
    refine ⟨γ, ρ, hρ_Z, r, hd₁_lt_L, hr_gt, fun w hw_Z hw_ball => ?_⟩
    have hw_F₁ : w ∈ F₁ := by
      refine (hmem_F₁ w).mpr ⟨Metric.mem_closedBall.mpr ?_, hw_Z⟩
      have h1 : dist w z₁ < L + 1 / 2 := (Metric.mem_ball.mp hw_ball).trans_le (min_le_left _ _)
      have h2 : dist w z₀ ≤ dist w z₁ + dist z₁ z₀ := dist_triangle w z₁ z₀
      have h3 : ε ≤ 1 / 4 := hε_le1.trans (min_le_right _ _)
      rw [hz₁_dist] at h2
      simp only [R₁]; linarith
    by_contra hne
    have hw_er : w ∈ F₁.erase ρ := Finset.mem_erase.mpr ⟨hne, hw_F₁⟩
    have hlt_r : dist w z₁ < dist w₂ z₁ := (Metric.mem_ball.mp hw_ball).trans_le (min_le_right _ _)
    exact lt_irrefl _ (hlt_r.trans_le (hw₂_min w hw_er))
  · refine ⟨t₀, ρ, hρ_Z, R₁, ?_, ?_, fun w hw_Z hw_ball => ?_⟩
    · rwa [hρ_dist]
    · rw [hρ_dist]; simp only [R₁]; linarith
    · have hw_F₁ : w ∈ F₁ := (hmem_F₁ w).mpr ⟨Metric.ball_subset_closedBall hw_ball, hw_Z⟩
      by_contra hne
      exact hrem ⟨w, Finset.mem_erase.mpr ⟨hne, hw_F₁⟩⟩

/-- Teorema geométrico de conductor 1: como `ζ` no se anula en `(0, ∞)`, si existe un cero `ρ₀`
con `Re ρ₀ > θ`, entonces para todo `σ > 2` existen `γ ∈ ℝ`, un cero `ρ ∈ cerosDerecha` y radios
`r, D` tales que `d = ‖(σ + iγ) − ρ‖ < min(r, D, σ − θ)`, `B(σ + iγ, r) ∩ cerosDerecha = {ρ}` y
`B(σ, D) ∩ cerosDerecha = ∅`. -/
theorem geometria_polo_conductor_uno {θ σ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ : 2 < σ)
    {ρ₀ : ℂ} (hρ₀_Z : ρ₀ ∈ cerosDerecha) (hρ₀_gt : θ < ρ₀.re) :
    ∃ γ : ℝ, ∃ ρ ∈ cerosDerecha, ∃ r D : ℝ,
      dist ρ ((σ : ℂ) + γ * I) < σ - θ ∧
      dist ρ ((σ : ℂ) + γ * I) < r ∧
      dist ρ ((σ : ℂ) + γ * I) < D ∧
      D ≤ σ - θ / 2 ∧
      (∀ w ∈ cerosDerecha, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ) ∧
      (∀ w ∈ cerosDerecha, w ∉ Metric.ball (σ : ℂ) D) := by
  set R₀ : ℝ := σ - θ / 2
  let F₀ : Finset ℂ := (finite_closedBall_inter_cerosDerecha (σ : ℂ) R₀).toFinset
  have hmem_F₀ : ∀ w, w ∈ F₀ ↔ w ∈ Metric.closedBall (σ : ℂ) R₀ ∧ w ∈ cerosDerecha := fun w =>
    Set.Finite.mem_toFinset _
  by_cases hnear : ∃ w ∈ F₀, dist w (σ : ℂ) ≤ σ - θ
  · -- Hay ceros a distancia `≤ σ − θ` de `σ`; ninguno es real por `zeta_ofReal_ne_zero`.
    obtain ⟨w_ex, hw_ex_F₀, hw_ex_le⟩ := hnear
    obtain ⟨w₁, hw₁_F₀, hw₁_min⟩ := Finset.exists_min_image F₀ (fun w => dist w (σ : ℂ)) ⟨w_ex, hw_ex_F₀⟩
    set D : ℝ := dist w₁ (σ : ℂ)
    have hD_le : D ≤ σ - θ := (hw₁_min w_ex hw_ex_F₀).trans hw_ex_le
    have hw₁_Z : w₁ ∈ cerosDerecha := ((hmem_F₀ w₁).mp hw₁_F₀).2
    have hw₁_im_ne : w₁.im ≠ 0 := by
      intro him0
      have hw₁_eq : w₁ = (w₁.re : ℂ) := by apply Complex.ext <;> simp [him0]
      exact zeta_ofReal_ne_zero hw₁_Z.1 (hw₁_eq ▸ hw₁_Z.2)
    have hD_pos : 0 < D := dist_pos.mpr fun h => by
      have := congrArg Complex.im h
      simp [hw₁_im_ne] at this
    have hball_free : ∀ w ∈ cerosDerecha, w ∉ Metric.ball (σ : ℂ) D := by
      intro w hw_Z hw_ball
      have hw_cb : w ∈ Metric.closedBall (σ : ℂ) R₀ := by
        rw [Metric.mem_closedBall]
        have := Metric.mem_ball.mp hw_ball
        simp only [R₀]; linarith
      have hw_F₀ : w ∈ F₀ := (hmem_F₀ w).mpr ⟨hw_cb, hw_Z⟩
      exact lt_irrefl _ ((Metric.mem_ball.mp hw_ball).trans_le (hw₁_min w hw_F₀))
    -- Reflejando si hace falta, obtenemos `w₂ ∈ cerosDerecha` con `dist w₂ σ = D` e `Im w₂ > 0`.
    obtain ⟨w₂, hw₂_Z, hw₂_dist, hw₂_im_pos⟩ :
        ∃ w₂ ∈ cerosDerecha, dist w₂ (σ : ℂ) = D ∧ 0 < w₂.im := by
      rcases lt_or_gt_of_ne hw₁_im_ne with hneg | hpos
      · refine ⟨starRingEnd ℂ w₁, cerosDerecha_conj hw₁_Z, ?_, by simp; linarith⟩
        rw [dist_eq_norm, ← show starRingEnd ℂ (σ : ℂ) = (σ : ℂ) by simp, ← map_sub,
          Complex.norm_conj, ← dist_eq_norm]
      · exact ⟨w₁, hw₁_Z, rfl, hpos⟩
    set t₀ : ℝ := w₂.im / 2
    have ht₀_pos : 0 < t₀ := half_pos hw₂_im_pos
    have hd_strict : dist w₂ ((σ : ℂ) + t₀ * I) < D := by
      have hsq1 : dist w₂ ((σ : ℂ) + t₀ * I) ^ 2 = (w₂.re - σ) ^ 2 + (w₂.im - t₀) ^ 2 := by
        rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
        simp; ring
      have hsq2 : D ^ 2 = (w₂.re - σ) ^ 2 + w₂.im ^ 2 := by
        rw [← hw₂_dist, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
        simp; ring
      have hlt_sq : dist w₂ ((σ : ℂ) + t₀ * I) ^ 2 < D ^ 2 := by
        rw [hsq1, hsq2]; simp only [t₀]; nlinarith
      by_contra hge
      have : D ^ 2 ≤ dist w₂ ((σ : ℂ) + t₀ * I) ^ 2 := pow_le_pow_left₀ hD_pos.le (not_lt.mp hge) 2
      linarith
    obtain ⟨γ, ρ, hρ_Z, r, hd_D, hd_r, huniq⟩ := unico_cero_cercano hσ hD_pos hw₂_Z hd_strict
    exact ⟨γ, ρ, hρ_Z, r, D, hd_D.trans_le hD_le, hd_r, hd_D, by simp only [R₀]; linarith,
      huniq, hball_free⟩
  · -- Ningún cero en `closedBall σ (σ − θ)`.
    simp only [not_exists, not_and, not_le] at hnear
    obtain ⟨D, hD_gt, hD_le_R₀, hball_free⟩ :
        ∃ D : ℝ, σ - θ < D ∧ D ≤ R₀ ∧ ∀ w ∈ cerosDerecha, w ∉ Metric.ball (σ : ℂ) D := by
      by_cases hF₀_ne : F₀.Nonempty
      · obtain ⟨w₁, hw₁_F₀, hw₁_min⟩ := Finset.exists_min_image F₀ (fun w => dist w (σ : ℂ)) hF₀_ne
        refine ⟨dist w₁ (σ : ℂ), hnear w₁ hw₁_F₀,
          Metric.mem_closedBall.mp ((hmem_F₀ w₁).mp hw₁_F₀).1, fun w hw_Z hw_ball => ?_⟩
        have hw_cb : w ∈ Metric.closedBall (σ : ℂ) R₀ := by
          rw [Metric.mem_closedBall]
          exact (Metric.mem_ball.mp hw_ball).le.trans (Metric.mem_closedBall.mp ((hmem_F₀ w₁).mp hw₁_F₀).1)
        exact lt_irrefl _ ((Metric.mem_ball.mp hw_ball).trans_le (hw₁_min w ((hmem_F₀ w).mpr ⟨hw_cb, hw_Z⟩)))
      · refine ⟨R₀, by simp only [R₀]; linarith, le_rfl, fun w hw_Z hw_ball => ?_⟩
        exact hF₀_ne ⟨w, (hmem_F₀ w).mpr ⟨Metric.ball_subset_closedBall hw_ball, hw_Z⟩⟩
    have hd₀ : dist ρ₀ ((σ : ℂ) + ρ₀.im * I) < σ - θ := by
      have hre1 : ρ₀.re < 1 := by
        by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hρ₀_Z.2
      have hsub : ρ₀ - ((σ : ℂ) + ρ₀.im * I) = ((ρ₀.re - σ : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    obtain ⟨γ, ρ, hρ_Z, r, hd_st, hd_r, huniq⟩ :=
      unico_cero_cercano hσ (by linarith : 0 < σ - θ) hρ₀_Z hd₀
    exact ⟨γ, ρ, hρ_Z, r, D, hd_st, hd_r, hd_st.trans hD_gt, hD_le_R₀, huniq, hball_free⟩

/-! ### Contradicción de crecimiento exponencial y teoremas principales de ventana -/

theorem contradiccion_crecimiento_exponencial {c d e E M C : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hde : d < e) (heE : e ≤ E)
    (H : ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) : False := by
  have he : 0 < e := lt_trans hd hde
  have hratio : 1 < e / d := (one_lt_div hd).mpr hde
  set η : ℝ := Real.log (e / d) / 2 with hη_def
  have hη : 0 < η := half_pos (Real.log_pos hratio)
  set K_const : ℝ := (|M| + |C| + 1) / c
  have hK_pos : 0 < K_const := div_pos (by positivity) hc
  set U₀ : ℝ := max 1 ((Real.log K_const + 1) / η)
  obtain ⟨U, hU, k, hk, hle⟩ := H η hη U₀
  have hU1 : 1 ≤ U := (le_max_left _ _).trans hU
  have hU_log : Real.log K_const + 1 ≤ η * U := by
    have h1 : (Real.log K_const + 1) / η ≤ U := (le_max_right _ _).trans hU
    rw [div_le_iff₀ hη] at h1
    linarith
  have hek : 0 < e ^ k := pow_pos he k
  have hdk : 0 < d ^ k := pow_pos hd k
  have hexp_ge1 : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have hM_le : M / e ^ k ≤ |M| * Real.exp (η * U) / e ^ k := by
    apply div_le_div_of_nonneg_right _ hek.le
    exact (le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp_ge1)
  have hC_le : C * Real.exp (η * U) / E ^ k ≤ |C| * Real.exp (η * U) / e ^ k := by
    apply div_le_div₀ (by positivity) _ hek (pow_le_pow_left₀ he.le heE k)
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have hcomb : c / d ^ k ≤ (|M| + |C|) * Real.exp (η * U) / e ^ k := by
    have : |M| * Real.exp (η * U) / e ^ k + |C| * Real.exp (η * U) / e ^ k
        = (|M| + |C|) * Real.exp (η * U) / e ^ k := by ring
    linarith
  have hmul : (e / d) ^ k ≤ ((|M| + |C|) / c) * Real.exp (η * U) := by
    rw [div_pow]
    have hm := mul_le_mul_of_nonneg_left hcomb (mul_nonneg hek.le (inv_nonneg.mpr hc.le))
    have hL : e ^ k * c⁻¹ * (c / d ^ k) = e ^ k / d ^ k := by field_simp
    have hR : e ^ k * c⁻¹ * ((|M| + |C|) * Real.exp (η * U) / e ^ k)
        = ((|M| + |C|) / c) * Real.exp (η * U) := by field_simp
    linarith [hm, hL, hR]
  have hstrict_rhs : ((|M| + |C|) / c) * Real.exp (η * U) < K_const * Real.exp (η * U) := by
    apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
    simp only [K_const]
    apply div_lt_div_of_pos_right (by linarith) hc
  have hpow_ge : K_const * Real.exp (η * U) < (e / d) ^ k := by
    have hlog_ed : (e / d) ^ k = Real.exp ((k : ℝ) * Real.log (e / d)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos he hd), mul_comm]
    have hK_exp : K_const * Real.exp (η * U) = Real.exp (Real.log K_const + η * U) := by
      rw [Real.exp_add, Real.exp_log hK_pos]
    rw [hlog_ed, hK_exp]
    apply Real.exp_lt_exp.mpr
    have h2η : Real.log (e / d) = 2 * η := by rw [hη_def]; ring
    rw [h2η]
    nlinarith
  linarith

/-- **Teorema de Landau en ventanas integrales para `ζ(s)`:** bajo `HipotesisVentanaZeta θ δ`,
`ζ` no tiene ceros en `Re s > θ`. -/
theorem sin_ceros_de_ventana_integral {θ δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : HipotesisVentanaZeta θ δ) :
    ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0 := by
  intro ρ₀ hρ₀_gt hζ₀
  obtain ⟨σ, hσ, C, hkey⟩ := cota_derivadas_de_ventana hθ0 hθ1 hδ hW
  have hρ₀_Z : ρ₀ ∈ cerosDerecha := ⟨lt_trans hθ0 hρ₀_gt, hζ₀⟩
  obtain ⟨γ, ρ, hρ_Z, r_raw, D, hd_st, hd_r_raw, hd_D, hD_le, huniq_raw, hfree_D⟩ :=
    geometria_polo_conductor_uno hθ0 hθ1 hσ hρ₀_Z hρ₀_gt
  set z : ℂ := (σ : ℂ) + γ * I
  set d : ℝ := dist ρ z
  set r : ℝ := min r_raw (σ - θ / 2)
  have hr_gt_d : d < r := lt_min hd_r_raw (lt_trans hd_st (by linarith))
  have hne : ρ ≠ z := by
    intro h
    have hre1 : ρ.re < 1 := by
      by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hρ_Z.2
    have hzre : z.re = σ := by simp [z]
    rw [h, hzre] at hre1
    linarith
  have hd_pos : 0 < d := dist_pos.mpr hne
  obtain ⟨c, hc_ne, h_an⟩ := polo_simple_Phi_zeta hρ_Z.2 hρ_Z.1
  -- Holomorfía de `Phi_zeta` en `B(z, r) \ {ρ}` y en `B(σ, D)`.
  have hdiff_z : DifferentiableOn ℂ Phi_zeta (Metric.ball z r \ {ρ}) := by
    intro w ⟨hw_ball, hw_ne⟩
    have hw_re : 0 < w.re := by
      have hn : ‖w - z‖ < σ - θ / 2 := by
        rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hw_ball).trans_le (min_le_right _ _)
      have h1 := (abs_lt.mp ((Complex.abs_re_le_norm (w - z)).trans_lt hn)).1
      simp only [sub_re, z, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero] at h1
      linarith
    have hw0 : w ≠ 0 := by intro h; rw [h, zero_re] at hw_re; exact lt_irrefl 0 hw_re
    have hw_ζ : riemannZeta w ≠ 0 := by
      intro h0
      have hw_r_raw : w ∈ Metric.ball z r_raw :=
        Metric.mem_ball.mpr ((Metric.mem_ball.mp hw_ball).trans_le (min_le_left _ _))
      exact hw_ne (huniq_raw w ⟨hw_re, h0⟩ hw_r_raw)
    exact (analyticAt_Phi_zeta hw0 hw_ζ).differentiableAt.differentiableWithinAt
  have hdiff_σ : DifferentiableOn ℂ Phi_zeta (Metric.ball (σ : ℂ) D) := by
    intro w hw_ball
    have hw_re : 0 < w.re := by
      have hn : ‖w - (σ : ℂ)‖ < σ - θ / 2 := by
        rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hw_ball).trans_le hD_le
      have h1 := (abs_lt.mp ((Complex.abs_re_le_norm (w - (σ : ℂ))).trans_lt hn)).1
      simp only [sub_re, ofReal_re] at h1
      linarith
    have hw0 : w ≠ 0 := by intro h; rw [h, zero_re] at hw_re; exact lt_irrefl 0 hw_re
    have hw_ζ : riemannZeta w ≠ 0 := fun h0 => hfree_D w ⟨hw_re, h0⟩ hw_ball
    exact (analyticAt_Phi_zeta hw0 hw_ζ).differentiableAt.differentiableWithinAt
  set e : ℝ := (d + min (min r D) (σ - θ)) / 2
  have hd_lt_e : d < e := by
    have : d < min (min r D) (σ - θ) := lt_min (lt_min hr_gt_d hd_D) hd_st
    simp only [e]; linarith
  have he_lt_r : e < r := by
    have : min (min r D) (σ - θ) ≤ r := (min_le_left _ _).trans (min_le_left _ _)
    simp only [e]; linarith
  have he_lt_D : e < D := by
    have : min (min r D) (σ - θ) ≤ D := (min_le_left _ _).trans (min_le_right _ _)
    simp only [e]; linarith
  have he_le_st : e ≤ σ - θ := by
    have : min (min r D) (σ - θ) ≤ σ - θ := min_le_right _ _
    simp only [e]; linarith
  have he_pos : 0 < e := lt_trans hd_pos hd_lt_e
  obtain ⟨M₁, hM₁⟩ := asintotica_polo_simple (Metric.mem_ball.mpr hr_gt_d) hne hdiff_z h_an he_pos he_lt_r
  obtain ⟨M₂, hM₂⟩ := cauchy_iteratedDeriv hdiff_σ he_pos he_lt_D
  refine contradiccion_crecimiento_exponencial (c := ‖c‖ / d) (d := d) (e := e) (E := σ - θ)
    (M := M₁ + M₂) (C := C) (div_pos (norm_pos_iff.mpr hc_ne) hd_pos) hd_pos hd_lt_e he_le_st
    fun η hη U₀ => ?_
  obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
  refine ⟨U, hU, k, hk, ?_⟩
  have h1 := hb γ
  have h2 := hM₁ k
  have h3 := hM₂ k
  have hzd : ‖z - ρ‖ = d := by rw [← dist_eq_norm, dist_comm]
  have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = (‖c‖ / d) / d ^ k := by
    rw [norm_div, norm_pow, hzd, pow_succ', div_div]
  have h5 : ‖(-1) ^ k * iteratedDeriv k Phi_zeta (σ : ℂ) / (k.factorial : ℂ)‖
      = ‖iteratedDeriv k Phi_zeta (σ : ℂ) / (k.factorial : ℂ)‖ := by
    rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h6 := (abs_le.mp (Complex.abs_re_le_norm
    ((-1) ^ k * iteratedDeriv k Phi_zeta (σ : ℂ) / (k.factorial : ℂ)))).1
  have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
    ((-1) ^ k * iteratedDeriv k Phi_zeta z / (k.factorial : ℂ))
  rw [norm_sub_rev] at h7
  rw [add_div]
  linarith

/-- De la cota puntual `G_vonMangoldt y ≤ C_v * y^θ` en ventanas `[Y, Y^{1 + δ}]` se sigue la
hipótesis integral `HipotesisVentanaZeta θ δ`. -/
theorem hipotesisVentana_de_puntual {θ δ C_v : ℝ} (hδ : 0 < δ)
    (hV : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (1 + δ)), G_vonMangoldt y ≤ C_v * y ^ θ) :
    HipotesisVentanaZeta θ δ := by
  intro η hη Y₀
  set K : ℝ := max C_v 0
  have hK0 : 0 ≤ K := le_max_right _ _
  set M_umbral : ℝ := max (max Y₀ 2) ((K * δ / (η / 2) + 1) ^ (2 / η))
  obtain ⟨Y, hYM, hY_win⟩ := hV M_umbral
  have hY0 : Y₀ ≤ Y := ((le_max_left _ _).trans (le_max_left _ _)).trans hYM
  have hY2 : 2 ≤ Y := ((le_max_right _ _).trans (le_max_left _ _)).trans hYM
  have hY1 : 1 ≤ Y := by linarith
  have hY_pos : 0 < Y := by linarith
  refine ⟨Y, hY0, hY1, fun y => K * y ^ θ, ?_, ?_, ?_⟩
  · have hcongr : ∀ y ∈ Icc Y (Y ^ (1 + δ)),
        (K * y ^ θ) * y ^ (-θ - 1) = K * y ^ (-1 : ℝ) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hY_pos hy.1
      rw [mul_assoc, ← Real.rpow_add hy0]
      congr 2; ring
    have hcont : ContinuousOn (fun y : ℝ => K * y ^ (-1 : ℝ)) (Icc Y (Y ^ (1 + δ))) :=
      continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun y hy =>
        Or.inl (lt_of_lt_of_le hY_pos hy.1).ne')
    exact hcont.integrableOn_Icc.congr_fun (fun y hy => (hcongr y hy).symm) measurableSet_Icc
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hY_pos.le hy.1
    refine ⟨mul_nonneg hK0 (Real.rpow_nonneg hy0 θ), ?_⟩
    exact (hY_win y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy0 θ))
  · have hY_le_Yδ : Y ≤ Y ^ (1 + δ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : (1 : ℝ) ≤ 1 + δ)
    have hcongr : ∀ y ∈ Icc Y (Y ^ (1 + δ)),
        (K * y ^ θ) * y ^ (-θ - 1) = K * y ^ (-1 : ℝ) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hY_pos hy.1
      rw [mul_assoc, ← Real.rpow_add hy0]
      congr 2; ring
    have hnot0 : (0 : ℝ) ∉ uIcc Y (Y ^ (1 + δ)) := by
      rw [uIcc_of_le hY_le_Yδ]
      intro h; linarith [h.1]
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hY_le_Yδ, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_congr (fun x _ => Real.rpow_neg_one x), integral_inv hnot0,
      Real.log_div (Real.rpow_pos_of_pos hY_pos _).ne' hY_pos.ne',
      Real.log_rpow hY_pos]
    have hlog_eq : K * ((1 + δ) * Real.log Y - Real.log Y) = (K * δ) * Real.log Y := by ring
    rw [hlog_eq]
    have hlog_le : Real.log Y ≤ Y ^ (η / 2) / (η / 2) := Real.log_le_rpow_div hY_pos.le (half_pos hη)
    have hM_le : (K * δ / (η / 2) + 1) ^ (2 / η) ≤ Y := (le_max_right _ _).trans hYM
    have hK_half : K * δ / (η / 2) ≤ Y ^ (η / 2) := by
      have h1 := Real.rpow_le_rpow (by positivity) hM_le (half_pos hη).le
      rw [← Real.rpow_mul (by positivity), show (2 / η) * (η / 2) = 1 by field_simp,
        Real.rpow_one] at h1
      linarith
    calc (K * δ) * Real.log Y
        ≤ (K * δ) * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = (K * δ / (η / 2)) * Y ^ (η / 2) := by ring
      _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
          mul_le_mul_of_nonneg_right hK_half (Real.rpow_nonneg hY_pos.le _)
      _ = Y ^ η := by rw [← Real.rpow_add hY_pos]; congr 1; ring

/-- **Teorema puntual en ventanas (conductor 1):** si `G(y) ≤ C_v y^θ` en ventanas `[Y, Y^{1 + δ}]`
arbitrariamente lejanas, entonces `ζ` no tiene ceros en `Re s > θ`. -/
theorem sin_ceros_de_ventana_puntual {θ δ C_v : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hV : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (1 + δ)), G_vonMangoldt y ≤ C_v * y ^ θ) :
    ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0 :=
  sin_ceros_de_ventana_integral hθ0 hθ1 hδ (hipotesisVentana_de_puntual hδ hV)

/-- **Puente `(V) ⇒ RH` de AMate / Alpöge en conductor 1:** si para cada `1/2 < θ < 1` existen
ventanas arbitrariamente lejanas `[Y, Y^{3/2}]` donde `G_vonMangoldt y ≤ y^θ`, entonces se cumple
`RiemannHypothesis`. -/
theorem rh_de_ventana_vonMangoldt
    (hV : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)), G_vonMangoldt y ≤ y ^ θ) :
    RiemannHypothesis := by
  apply rh_of_no_zero_gt_half
  intro ρ hβ
  set θ : ℝ := (1 / 2 + min ρ.re 1) / 2
  have hθ_gt : 1 / 2 < θ := by
    have : 1 / 2 < min ρ.re 1 := lt_min hβ (by norm_num)
    simp only [θ]; linarith
  have hθ_lt1 : θ < 1 := by
    have : min ρ.re 1 ≤ 1 := min_le_right _ _
    simp only [θ]; linarith
  have hθ_lt_ρ : θ < ρ.re := by
    have : min ρ.re 1 ≤ ρ.re := min_le_left _ _
    simp only [θ]; linarith
  refine sin_ceros_de_ventana_puntual (C_v := 1) (δ := 1 / 2)
    (by linarith) hθ_lt1 (by norm_num) (fun Y₀ => ?_) ρ hθ_lt_ρ
  obtain ⟨Y, hYY₀, hwin⟩ := hV θ hθ_gt hθ_lt1 Y₀
  refine ⟨Y, hYY₀, fun y hy => ?_⟩
  rw [one_mul]
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at hy
  exact hwin y hy

/-- **Puente `(V) ⇒ E_Q ≤ C_ε Q^ε` completo en Lean:** la desigualdad unilateral en ventanas de
`G_vonMangoldt` implica directamente la cota subpolinomial uniforme de la energía de AMate. -/
theorem energia_de_ventana_vonMangoldt
    (hV : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)), G_vonMangoldt y ≤ y ^ θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε :=
  energia_subpolinomial (rh_de_ventana_vonMangoldt hV)

end AMate
