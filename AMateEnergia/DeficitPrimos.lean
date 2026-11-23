import AMateEnergia.VentanaLandau

/-!
# Criterio aritmético sobre sumas de déficits de primos `S_AMate(Y)`

Pieza 3 del puente de conductor 1 entre AMate y las ventanas unilaterales de von Mangoldt:

* `A_primos`, `S_AMate`: las sumas explícitas sobre primos `√x < p ≤ x` y nodos cuárticos
  `Y ≤ m⁴ ≤ Y^{3/2}` introducidas en `APLICACION_A_AMATE.md`:
  `A(x) = ∑_{√x < p ≤ x} (log p) (1 − {x/p})` y
  `S(Y) = ∑_{Y ≤ m⁴ ≤ Y^{3/2}} [γ_E m⁴ − A(m⁴)]_+ / m³`.
* `G_vonMangoldt_le_deficit_primos`: desigualdad global exacta sin constantes asintóticas:
  `G_vonMangoldt x ≤ γ_E x − A_primos x + log x + 1` para todo `x ≥ 1`.
* `G_vonMangoldt_interpolacion`: interpolación por convexidad de `G(x) + x log x` en cualquier
  celda `[a, b] ⊆ (0, ∞)`:
  `max (G_vonMangoldt x) 0 ≤ max (G_vonMangoldt a) 0 + max (G_vonMangoldt b) 0 + (b − a)² / (4 a)`.
* `hipotesisVentana_de_deficit_primos`: si para todo `η > 0` existen escalas arbitrariamente
  grandes `Y` con `S_AMate Y ≤ Y^η`, entonces se cumple `HipotesisVentanaZeta (1 / 2) (1 / 4)`.
* `rh_de_deficit_primos` y `energia_de_deficit_primos`: cierre completo en Lean
  `(∀ η > 0, ∃ᶠ Y, S_AMate Y ≤ Y^η) ⇒ RiemannHypothesis ⇒ (∀ ε > 0, E_Q ≤ C_ε Q^ε)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ArithmeticFunction.vonMangoldt

namespace AMate

/-! ### Definición de `A_primos` y `S_AMate` -/

/-- Suma ponderada sobre primos grandes `√x < p ≤ x`:
`A(x) = ∑_{√x < p ≤ x} (log p) (1 − {x / p})`. -/
noncomputable def A_primos (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => Nat.Prime p ∧ Real.sqrt x < (p : ℝ)),
    Real.log (p : ℝ) * (1 - Int.fract (x / (p : ℝ)))

/-- Suma aritmética de AMate sobre déficits positivos en nodos cuárticos `Y ≤ m⁴ ≤ Y^{3/2}`:
`S(Y) = ∑_{Y ≤ m⁴ ≤ Y^{3/2}} max(γ_E m⁴ − A(m⁴), 0) / m³`. -/
noncomputable def S_AMate (Y : ℝ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊).filter
      (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ)),
    max (Real.eulerMascheroniConstant * (m : ℝ) ^ 4 - A_primos ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3

theorem S_AMate_nonneg (Y : ℝ) : 0 ≤ S_AMate Y := by
  unfold S_AMate
  refine Finset.sum_nonneg fun m _ => ?_
  exact div_nonneg (le_max_right _ _) (by positivity)

/-! ### Identidad combinatoria exacta de la rampa de von Mangoldt -/

theorem natFloor_div_natCast {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ⌊x / (n : ℝ)⌋₊ = ⌊x⌋₊ / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.floor_eq_iff (div_nonneg hx hn_pos.le)]
    constructor
    · rw [le_div_iff₀ hn_pos]
      have h1 : (⌊x⌋₊ / n) * n ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ n
      have h2 : (((⌊x⌋₊ / n) * n : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2.trans (Nat.floor_le hx)
    · rw [div_lt_iff₀ hn_pos]
      have hdiv := Nat.div_add_mod ⌊x⌋₊ n
      have hmod := Nat.mod_lt ⌊x⌋₊ hn
      have h1 : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ / n + 1) * n := by nlinarith
      have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (((⌊x⌋₊ / n + 1) * n : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact (Nat.lt_floor_add_one x).trans_le h2

theorem cast_natFloor_eq_sub_fract {y : ℝ} (hy : 0 ≤ y) :
    (⌊y⌋₊ : ℝ) = y - Int.fract y := by
  let a : ℤ := ⌊y⌋
  let b : ℤ := (⌊y⌋₊ : ℤ)
  have ha1 : (a : ℝ) ≤ y := Int.floor_le y
  have ha2 : y < (a : ℝ) + 1 := Int.lt_floor_add_one y
  have hb1 : (b : ℝ) ≤ y := by simpa [b] using Nat.floor_le hy
  have hb2 : y < (b : ℝ) + 1 := by simpa [b] using Nat.lt_floor_add_one y
  have hlt1 : ((a - b : ℤ) : ℝ) < (1 : ℤ) := by push_cast; linarith
  have hgt1 : ((-1 : ℤ) : ℝ) < ((a - b : ℤ) : ℝ) := by push_cast; linarith
  have hab_lt : a - b < 1 := by exact_mod_cast hlt1
  have hab_gt : -1 < a - b := by exact_mod_cast hgt1
  have hab : a = b := by omega
  have hcast : (⌊y⌋₊ : ℝ) = (⌊y⌋ : ℝ) := by
    simpa [a, b] using congrArg (Int.cast : ℤ → ℝ) hab.symm
  rw [hcast, Int.fract]
  ring

theorem sum_vonMangoldt_div_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ) = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  have hcard : ∀ n ∈ Finset.Icc 1 N,
      ((Finset.Icc 1 N).filter (fun m => n ∣ m)).card = N / n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_pos : 0 < n := hn.1
    have himg : (Finset.Icc 1 N).filter (fun m => n ∣ m)
        = (Finset.Icc 1 (N / n)).image (fun k => n * k) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hm1, hmN⟩, ⟨k, rfl⟩⟩
        refine ⟨k, ⟨?_, ?_⟩, rfl⟩
        · by_contra hk0
          have hk_eq : k = 0 := by omega
          subst hk_eq; simp at hm1
        · exact (Nat.le_div_iff_mul_le hn_pos).mpr (by nlinarith)
      · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
        refine ⟨⟨by nlinarith, (Nat.mul_le_mul_left n hkN).trans (Nat.mul_div_le N n)⟩,
          dvd_mul_right n k⟩
    rw [himg, Finset.card_image_of_injective _ (fun k₁ k₂ h => Nat.eq_of_mul_eq_mul_left hn_pos h),
      Nat.card_Icc]
    simp
  have hdiv : ∀ m ∈ Finset.Icc 1 N,
      (Finset.Icc 1 N).filter (fun n => n ∣ m) = m.divisors := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hm.1, (Nat.le_of_dvd hm.1 hdvd).trans hm.2⟩, hdvd⟩
  calc ∑ n ∈ Finset.Icc 1 N, Λ n * ((N / n : ℕ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, if n ∣ m then Λ n else 0 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard n hn, mul_comm]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, if n ∣ m then Λ n else 0 := Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ m.divisors, Λ n := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [← Finset.sum_filter, hdiv m hm]
    _ = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) :=
          Finset.sum_congr rfl fun m _ => ArithmeticFunction.vonMangoldt_sum

/-! ### Cotas elementales sin análisis asintótico para `∑ log m` y `∑ 1/m` -/

theorem sum_log_Icc_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ)
      ≤ (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 + Real.log (N : ℝ) := by
  have hIco : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco]
  refine Nat.le_induction ?_ ?_ N hN
  · simp
  · intro n hn ih
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn_pos hn1_pos)
    rw [Real.log_div hn_pos.ne' hn1_pos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hn1_pos.le
    have hsimp : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
      field_simp
      ring
    rw [hsimp] at hmul
    push_cast at ih ⊢
    nlinarith

theorem sum_inv_Icc_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
  have hIco : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco]
  refine Nat.le_induction ?_ ?_ N hN
  · simp
  · intro n hn ih
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn_pos hn1_pos)
    rw [Real.log_div hn_pos.ne' hn1_pos.ne'] at hlog
    have hsub : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [hsub] at hlog
    push_cast at ih ⊢
    linarith

/-! ### Comparación global `G_vonMangoldt x ≤ γ_E x − A_primos x + log x + 1` -/

/-- Desigualdad global exacta que vincula `G_vonMangoldt` con el déficit sobre primos grandes:
para todo `x ≥ 1`, `G_vonMangoldt x ≤ γ_E x − A_primos x + log x + 1`. -/
theorem G_vonMangoldt_le_deficit_primos {x : ℝ} (hx : 1 ≤ x) :
    G_vonMangoldt x ≤ Real.eulerMascheroniConstant * x - A_primos x + Real.log x + 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN_le_x : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  -- Paso 1: descomposición exacta de `rampaVonMangoldt x`.
  have hramp_eq : rampaVonMangoldt x
      = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ)
        - ∑ n ∈ Finset.Icc 1 N, Λ n * (1 - Int.fract (x / (n : ℝ))) := by
    unfold rampaVonMangoldt
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        Λ n * (x / (n : ℝ) - 1)
          = Λ n * ((N / n : ℕ) : ℝ) - Λ n * (1 - Int.fract (x / (n : ℝ))) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hdiv_nn : 0 ≤ x / (n : ℝ) := div_nonneg hx0.le hn_pos.le
      have hfl := cast_natFloor_eq_sub_fract hdiv_nn
      rw [natFloor_div_natCast hx0.le n] at hfl
      change Λ n * (x / (n : ℝ) - 1)
        = Λ n * ((⌊x⌋₊ / n : ℕ) : ℝ) - Λ n * (1 - Int.fract (x / (n : ℝ)))
      rw [hfl]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_vonMangoldt_div_floor N]
  -- Paso 2: `A_primos x` es una subsuma de términos no negativos de la suma fraccionaria.
  have hA_le : A_primos x ≤ ∑ n ∈ Finset.Icc 1 N, Λ n * (1 - Int.fract (x / (n : ℝ))) := by
    unfold A_primos
    have hcongr : ∑ p ∈ (Finset.Icc 1 N).filter (fun p : ℕ => Nat.Prime p ∧ Real.sqrt x < (p : ℝ)),
          Real.log (p : ℝ) * (1 - Int.fract (x / (p : ℝ)))
        = ∑ p ∈ (Finset.Icc 1 N).filter (fun p : ℕ => Nat.Prime p ∧ Real.sqrt x < (p : ℝ)),
          Λ p * (1 - Int.fract (x / (p : ℝ))) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
    rw [hcongr]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => ?_
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr (Int.fract_lt_one _).le)
  -- Paso 3: `N log N − N ≤ x log x − x` y `log N ≤ log x`.
  have hNx_mono : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ x * Real.log x - x := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hN_pos hx0)
    rw [Real.log_div hN_pos.ne' hx0.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hx0.le
    have hsimp : x * ((N : ℝ) / x - 1) = (N : ℝ) - x := by field_simp
    rw [hsimp] at h2
    have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    have h3 : (N : ℝ) * Real.log (N : ℝ) ≤ x * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hN_le_x hlogN_nn
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hN_pos hN_le_x
  have hsum_log := sum_log_Icc_le hN1
  unfold G_vonMangoldt
  linarith

theorem max_G_vonMangoldt_le_deficit_primos {x : ℝ} (hx : 1 ≤ x) :
    max (G_vonMangoldt x) 0
      ≤ max (Real.eulerMascheroniConstant * x - A_primos x) 0 + Real.log x + 1 := by
  have hlog_nn : 0 ≤ Real.log x + 1 := by linarith [Real.log_nonneg hx]
  have hrhs_nn : 0 ≤ max (Real.eulerMascheroniConstant * x - A_primos x) 0 + Real.log x + 1 := by
    linarith [le_max_right (Real.eulerMascheroniConstant * x - A_primos x) 0]
  refine max_le ?_ hrhs_nn
  calc G_vonMangoldt x
      ≤ Real.eulerMascheroniConstant * x - A_primos x + Real.log x + 1 :=
        G_vonMangoldt_le_deficit_primos hx
    _ ≤ max (Real.eulerMascheroniConstant * x - A_primos x) 0 + Real.log x + 1 := by
        linarith [le_max_left (Real.eulerMascheroniConstant * x - A_primos x) 0]

/-! ### Continuidad e interpolación por convexidad de `G_vonMangoldt` -/

theorem continuousOn_G_vonMangoldt : ContinuousOn G_vonMangoldt (Ioi 0) := by
  have hramp : ContinuousOn rampaVonMangoldt (Ioi 0) := by
    intro x hx
    have hx_pos : (0 : ℝ) < x := hx
    let M : ℕ := ⌊x + 1⌋₊ + 1
    have hcont_fin : Continuous (fun y : ℝ =>
        ∑ n ∈ Finset.range M, Λ n * max (y / (n : ℝ) - 1) 0) := by fun_prop
    have hev : (fun y : ℝ => ∑ n ∈ Finset.range M, Λ n * max (y / (n : ℝ) - 1) 0)
        =ᶠ[𝓝 x] rampaVonMangoldt := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hx_pos, lt_add_one x⟩] with y hy
      exact (rampaVonMangoldt_eq_range_of_gt y
        ((Nat.floor_mono hy.2.le).trans_lt (Nat.lt_succ_self _))).symm
    exact (hcont_fin.continuousAt.congr hev).continuousWithinAt
  unfold G_vonMangoldt
  exact (hramp.sub (continuousOn_id.mul (Real.continuousOn_log.mono fun y hy => ne_of_gt hy))).add
    (continuousOn_const.mul continuousOn_id)

theorem continuousOn_max_G_vonMangoldt :
    ContinuousOn (fun y : ℝ => max (G_vonMangoldt y) 0) (Ioi 0) :=
  (continuous_id.max continuous_const).comp_continuousOn continuousOn_G_vonMangoldt

/-- Interpolación por convexidad en `[a, b] ⊆ (0, ∞)`:
`max(G(x), 0) ≤ max(G(a), 0) + max(G(b), 0) + (b − a)² / (4 a)`. -/
theorem G_vonMangoldt_interpolacion {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    max (G_vonMangoldt x) 0
      ≤ max (G_vonMangoldt a) 0 + max (G_vonMangoldt b) 0 + (b - a) ^ 2 / (4 * a) := by
  have hx_pos : 0 < x := lt_of_lt_of_le ha hax
  have hb_pos : 0 < b := lt_of_lt_of_le hx_pos hxb
  refine max_le ?_ (by positivity)
  rcases eq_or_lt_of_le (hax.trans hxb) with hab_eq | hab
  · have hxa : x = a := le_antisymm (hxb.trans hab_eq.symm.le) hax
    subst hxa
    have : 0 ≤ max (G_vonMangoldt b) 0 + (b - x) ^ 2 / (4 * x) := by positivity
    linarith [le_max_left (G_vonMangoldt x) 0]
  · set lam : ℝ := (x - a) / (b - a) with hlam_def
    set mu : ℝ := 1 - lam with hmu_def
    have hba : 0 < b - a := sub_pos.mpr hab
    have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hax) hba.le
    have hlam1 : lam ≤ 1 := (div_le_one hba).mpr (sub_le_sub_right hxb a)
    have hmu0 : 0 ≤ mu := sub_nonneg.mpr hlam1
    have hmu1 : mu ≤ 1 := by linarith
    have hcomb_x : mu * a + lam * b = x := by
      rw [hmu_def, hlam_def]
      field_simp
      ring
    let M : ℕ := ⌊b⌋₊ + 1
    have hramp_conv : rampaVonMangoldt x ≤ mu * rampaVonMangoldt a + lam * rampaVonMangoldt b := by
      rw [rampaVonMangoldt_eq_range_of_gt x ((Nat.floor_mono hxb).trans_lt (Nat.lt_succ_self _)),
        rampaVonMangoldt_eq_range_of_gt a ((Nat.floor_mono hab.le).trans_lt (Nat.lt_succ_self _)),
        rampaVonMangoldt_eq_range_of_gt b (Nat.lt_succ_self _),
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      have hmax : max (x / (n : ℝ) - 1) 0
          ≤ mu * max (a / (n : ℝ) - 1) 0 + lam * max (b / (n : ℝ) - 1) 0 := by
        refine max_le ?_ (by positivity)
        have hlin : x / (n : ℝ) - 1 = mu * (a / (n : ℝ) - 1) + lam * (b / (n : ℝ) - 1) := by
          rw [← hcomb_x, hmu_def]
          ring
        rw [hlin]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hmu0)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hlam0)
      calc Λ n * max (x / (n : ℝ) - 1) 0
          ≤ Λ n * (mu * max (a / (n : ℝ) - 1) 0 + lam * max (b / (n : ℝ) - 1) 0) :=
            mul_le_mul_of_nonneg_left hmax ArithmeticFunction.vonMangoldt_nonneg
        _ = mu * (Λ n * max (a / (n : ℝ) - 1) 0) + lam * (Λ n * max (b / (n : ℝ) - 1) 0) := by
            ring
    have hlog_defect : mu * (a * Real.log a) + lam * (b * Real.log b) - x * Real.log x
        ≤ (b - a) ^ 2 / (4 * a) := by
      have hla := Real.log_le_sub_one_of_pos (div_pos ha hx_pos)
      rw [Real.log_div ha.ne' hx_pos.ne'] at hla
      have hlb := Real.log_le_sub_one_of_pos (div_pos hb_pos hx_pos)
      rw [Real.log_div hb_pos.ne' hx_pos.ne'] at hlb
      have hma := mul_le_mul_of_nonneg_left hla (mul_nonneg hmu0 ha.le)
      have hmb := mul_le_mul_of_nonneg_left hlb (mul_nonneg hlam0 hb_pos.le)
      have hsplit : mu * (a * Real.log a) + lam * (b * Real.log b) - x * Real.log x
          = (mu * a) * (Real.log a - Real.log x) + (lam * b) * (Real.log b - Real.log x) := by
        calc mu * (a * Real.log a) + lam * (b * Real.log b) - x * Real.log x
            = mu * (a * Real.log a) + lam * (b * Real.log b) - (mu * a + lam * b) * Real.log x := by
                rw [← hcomb_x]
          _ = (mu * a) * (Real.log a - Real.log x) + (lam * b) * (Real.log b - Real.log x) := by
                ring
      have hnum_id : (mu * a) * (a / x - 1) + (lam * b) * (b / x - 1)
          = lam * (1 - lam) * (b - a) ^ 2 / x := by
        have h1 : (mu * a) * (a / x - 1) + (lam * b) * (b / x - 1)
            = ((mu * a) * (a - x) + (lam * b) * (b - x)) / x := by
          field_simp
        rw [h1]
        congr 1
        rw [← hcomb_x, hmu_def]
        ring
      have hlam_prod : lam * (1 - lam) ≤ 1 / 4 := by
        have : 0 ≤ (lam - 1 / 2) ^ 2 := sq_nonneg _
        nlinarith
      calc mu * (a * Real.log a) + lam * (b * Real.log b) - x * Real.log x
          = (mu * a) * (Real.log a - Real.log x) + (lam * b) * (Real.log b - Real.log x) := hsplit
        _ ≤ (mu * a) * (a / x - 1) + (lam * b) * (b / x - 1) := add_le_add hma hmb
        _ = lam * (1 - lam) * (b - a) ^ 2 / x := hnum_id
        _ ≤ ((1 / 4 : ℝ) * (b - a) ^ 2) / a := by
            apply div_le_div₀ (by positivity) _ ha hax
            exact mul_le_mul_of_nonneg_right hlam_prod (sq_nonneg _)
        _ = (b - a) ^ 2 / (4 * a) := by ring
    have hG_comb : G_vonMangoldt x
        ≤ mu * G_vonMangoldt a + lam * G_vonMangoldt b + (b - a) ^ 2 / (4 * a) := by
      unfold G_vonMangoldt
      have hlin_term : (1 + Real.eulerMascheroniConstant) * x
          = mu * ((1 + Real.eulerMascheroniConstant) * a)
            + lam * ((1 + Real.eulerMascheroniConstant) * b) := by
        rw [← hcomb_x]; ring
      linarith [hramp_conv, hlog_defect, hlin_term]
    have hmu_max : mu * G_vonMangoldt a ≤ max (G_vonMangoldt a) 0 :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hmu0).trans
        (mul_le_of_le_one_left (le_max_right _ _) hmu1)
    have hlam_max : lam * G_vonMangoldt b ≤ max (G_vonMangoldt b) 0 :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hlam0).trans
        (mul_le_of_le_one_left (le_max_right _ _) hlam1)
    linarith

/-! ### Cota en una celda cuártica `[m⁴, (m + 1)⁴]` e integración en ventanas -/

/-- En cada celda `[m⁴, (m + 1)⁴]` con `m ≥ 1`, la integral del perfil positivo con peso `y^{−3/2}`
se controla por los dos extremos y un término armónico `1 / m`. -/
theorem cota_celda_G_vonMangoldt {m : ℕ} (hm1 : 1 ≤ m) :
    ∫ y in ((m : ℝ) ^ 4)..(((m + 1 : ℕ) : ℝ) ^ 4),
        max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
      ≤ 15 * (max (G_vonMangoldt ((m : ℝ) ^ 4)) 0 / (m : ℝ) ^ 3)
        + 120 * (max (G_vonMangoldt (((m + 1 : ℕ) : ℝ) ^ 4)) 0 / ((m + 1 : ℕ) : ℝ) ^ 3)
        + 855 * (1 / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set a : ℝ := (m : ℝ) ^ 4
  set b : ℝ := ((m + 1 : ℕ) : ℝ) ^ 4
  have ha_pos : 0 < a := by positivity
  have hab : a ≤ b := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (Nat.le_succ m)
  have hba_le : b - a ≤ 15 * (m : ℝ) ^ 3 := by
    have hb_eq : b = ((m : ℝ) + 1) ^ 4 := by simp [b, Nat.cast_add]
    rw [hb_eq]
    have : ((m : ℝ) + 1) ^ 4 - (m : ℝ) ^ 4
        = 4 * (m : ℝ) ^ 3 + 6 * (m : ℝ) ^ 2 + 4 * (m : ℝ) + 1 := by ring
    rw [show a = (m : ℝ) ^ 4 from rfl, this]
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hdef_le : (b - a) ^ 2 / (4 * a) ≤ 57 * (m : ℝ) ^ 2 := by
    have hsq : (b - a) ^ 2 ≤ (15 * (m : ℝ) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hab) hba_le 2
    rw [div_le_iff₀ (by positivity : 0 < 4 * a)]
    have ha_eq : a = (m : ℝ) ^ 4 := rfl
    rw [ha_eq] at hsq ⊢
    nlinarith
  let C_top : ℝ := max (G_vonMangoldt a) 0 + max (G_vonMangoldt b) 0 + 57 * (m : ℝ) ^ 2
  let f : ℝ → ℝ := fun y => max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
  have hf_cont : ContinuousOn f (Ioi 0) :=
    continuousOn_max_G_vonMangoldt.mul
      (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (ne_of_gt hy))
  have hpt : ∀ y ∈ Icc a b, f y ≤ C_top / (m : ℝ) ^ 6 := by
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le ha_pos hy.1
    have hG := G_vonMangoldt_interpolacion ha_pos hy.1 hy.2
    have hG' : max (G_vonMangoldt y) 0 ≤ C_top := by
      dsimp only [C_top]; linarith
    have hrpow_a : a ^ (3 / 2 : ℝ) = (m : ℝ) ^ 6 := by
      have ha_rpow : a = (m : ℝ) ^ (4 : ℝ) := by
        change (m : ℝ) ^ 4 = (m : ℝ) ^ (4 : ℝ)
        exact (Real.rpow_natCast (m : ℝ) 4).symm
      rw [ha_rpow, ← Real.rpow_mul hm_pos.le]
      have hexp : (4 : ℝ) * (3 / 2 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_natCast]
    have hrpow_le : y ^ (-(1 / 2 : ℝ) - 1) ≤ 1 / (m : ℝ) ^ 6 := by
      have hexp : -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg hy_pos.le, ← inv_eq_one_div, ← hrpow_a]
      exact inv_anti₀ (Real.rpow_pos_of_pos ha_pos _)
        (Real.rpow_le_rpow ha_pos.le hy.1 (by norm_num))
    calc max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
        ≤ C_top * (1 / (m : ℝ) ^ 6) :=
          mul_le_mul hG' hrpow_le (Real.rpow_nonneg hy_pos.le _) (by positivity)
      _ = C_top / (m : ℝ) ^ 6 := by ring
  have hint_cell : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (hf_cont.mono fun y hy => lt_of_lt_of_le ha_pos hy.1).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hint_le : ∫ y in a..b, f y ≤ (b - a) * (C_top / (m : ℝ) ^ 6) := by
    calc ∫ y in a..b, f y
        ≤ ∫ _y in a..b, C_top / (m : ℝ) ^ 6 :=
          intervalIntegral.integral_mono_on hab hint_cell intervalIntegrable_const hpt
      _ = (b - a) * (C_top / (m : ℝ) ^ 6) := by
          simp [smul_eq_mul]
          ring
  have hm1_cube : 1 / (m : ℝ) ^ 3 ≤ 8 / ((m + 1 : ℕ) : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    calc 1 * ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 3 := one_mul _
      _ ≤ (2 * (m : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      _ = 8 * (m : ℝ) ^ 3 := by ring
  have hmul_cell : (b - a) * (C_top / (m : ℝ) ^ 6) ≤ 15 * (C_top / (m : ℝ) ^ 3) := by
    calc (b - a) * (C_top / (m : ℝ) ^ 6)
        ≤ (15 * (m : ℝ) ^ 3) * (C_top / (m : ℝ) ^ 6) :=
          mul_le_mul_of_nonneg_right hba_le (by positivity)
      _ = 15 * (C_top / (m : ℝ) ^ 3) := by
          have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
          field_simp
  have hsplit_C : 15 * (C_top / (m : ℝ) ^ 3)
      = 15 * (max (G_vonMangoldt a) 0 / (m : ℝ) ^ 3)
        + 15 * (max (G_vonMangoldt b) 0 * (1 / (m : ℝ) ^ 3))
        + 855 * ((m : ℝ) ^ 2 / (m : ℝ) ^ 3) := by
    dsimp only [C_top]
    ring
  have hb_term : 15 * (max (G_vonMangoldt b) 0 * (1 / (m : ℝ) ^ 3))
      ≤ 120 * (max (G_vonMangoldt b) 0 / ((m + 1 : ℕ) : ℝ) ^ 3) := by
    have h1 := mul_le_mul_of_nonneg_left hm1_cube (le_max_right (G_vonMangoldt b) 0)
    calc 15 * (max (G_vonMangoldt b) 0 * (1 / (m : ℝ) ^ 3))
        ≤ 15 * (max (G_vonMangoldt b) 0 * (8 / ((m + 1 : ℕ) : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 120 * (max (G_vonMangoldt b) 0 / ((m + 1 : ℕ) : ℝ) ^ 3) := by ring
  have hinv_m : (m : ℝ) ^ 2 / (m : ℝ) ^ 3 = 1 / (m : ℝ) := by
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    field_simp
  rw [hinv_m] at hsplit_C
  dsimp only [f] at hint_le
  linarith

/-- En toda escala `Y ≥ 5¹⁶`, la integral del perfil positivo en `[16 Y, (16 Y)^{5/4}]` queda
acotada por `135 · S_AMate Y + 1600 · log Y`. -/
theorem integral_ventana_le_S_AMate {Y : ℝ} (hY : (5 : ℝ) ^ 16 ≤ Y) :
    ∫ y in Icc (16 * Y) ((16 * Y) ^ (1 + (1 / 4 : ℝ))),
        max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
      ≤ 135 * S_AMate Y + 1600 * Real.log Y := by
  have hY_pos : 0 < Y := lt_of_lt_of_le (by positivity) hY
  set u : ℝ := Y ^ (1 / 16 : ℝ) with hu_def
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hY_pos _
  have hu5 : 5 ≤ u := by
    have h1 := Real.rpow_le_rpow (by positivity) hY (by norm_num : (0 : ℝ) ≤ 1 / 16)
    have h5_eq : ((5 : ℝ) ^ 16) ^ (1 / 16 : ℝ) = 5 := by
      rw [← Real.rpow_natCast 5 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h5_eq] at h1
  have hu_pow : ∀ k : ℕ, u ^ k = Y ^ ((k : ℝ) / 16) := fun k => by
    rw [← Real.rpow_natCast, hu_def, ← Real.rpow_mul hY_pos.le]
    congr 1; ring
  have hu16 : u ^ 16 = Y := by
    rw [hu_pow 16]
    have hexp : ((16 : ℕ) : ℝ) / 16 = 1 := by norm_num
    rw [hexp, Real.rpow_one]
  have hu24 : u ^ 24 = Y ^ (3 / 2 : ℝ) := by
    rw [hu_pow 24]
    congr 1; norm_num
  have hu6 : u ^ 6 = Y ^ (3 / 8 : ℝ) := by
    rw [hu_pow 6]
    congr 1; norm_num
  set Z : ℝ := 16 * Y with hZ_def
  have hZ_eq : Z = (2 * u ^ 4) ^ 4 := by rw [hZ_def, ← hu16]; ring
  have hZ54 : Z ^ (1 + (1 / 4 : ℝ)) = 32 * u ^ 20 := by
    have h1 : Z = (2 * u ^ 4) ^ (4 : ℝ) := by
      rw [hZ_eq]
      exact (Real.rpow_natCast (2 * u ^ 4) 4).symm
    rw [h1, ← Real.rpow_mul (by positivity)]
    have hexp : (4 : ℝ) * (1 + 1 / 4) = ((5 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
    ring
  set A : ℕ := ⌊2 * u ^ 4⌋₊
  set B : ℕ := ⌊3 * u ^ 5⌋₊
  have hu2_ge : 25 ≤ u ^ 2 := by nlinarith
  have hu4_ge : 625 ≤ u ^ 4 := by
    have hsq : u ^ 4 = (u ^ 2) ^ 2 := by ring
    nlinarith [hsq]
  have hA_gt_u4 : u ^ 4 ≤ (A : ℝ) := by
    have hlt := Nat.lt_floor_add_one (2 * u ^ 4)
    linarith
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast this
  have hA_le_2u4 : (A : ℝ) ≤ 2 * u ^ 4 := Nat.floor_le (by positivity)
  have hA4_ge_Y : Y ≤ (A : ℝ) ^ 4 := by
    rw [← hu16]
    calc u ^ 16 = (u ^ 4) ^ 4 := by ring
      _ ≤ (A : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hA_gt_u4 4
  have hA4_le_Z : (A : ℝ) ^ 4 ≤ Z := by
    rw [hZ_eq]
    exact pow_le_pow_left₀ (by positivity) hA_le_2u4 4
  have hAB : A ≤ B := Nat.floor_mono (by nlinarith)
  have hB1_gt : 3 * u ^ 5 < ((B + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (3 * u ^ 5)
  have hB1_le_u6 : ((B + 1 : ℕ) : ℝ) ≤ u ^ 6 := by
    have hfl : (B : ℝ) ≤ 3 * u ^ 5 := Nat.floor_le (by positivity)
    push_cast
    have hu5_pos : 0 < u ^ 5 := by positivity
    have hu6_eq : u ^ 6 = u * u ^ 5 := by ring
    nlinarith [hu6_eq]
  have hZ54_le_B1 : Z ^ (1 + (1 / 4 : ℝ)) ≤ ((B + 1 : ℕ) : ℝ) ^ 4 := by
    rw [hZ54]
    have h81 : 32 * u ^ 20 ≤ (3 * u ^ 5) ^ 4 := by
      have : 0 ≤ u ^ 20 := by positivity
      linarith [show (3 * u ^ 5) ^ 4 = 81 * u ^ 20 by ring]
    exact h81.trans (pow_le_pow_left₀ (by positivity) hB1_gt.le 4)
  have hB1_le_Y32 : ((B + 1 : ℕ) : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ) := by
    rw [← hu24]
    calc ((B + 1 : ℕ) : ℝ) ^ 4 ≤ (u ^ 6) ^ 4 := pow_le_pow_left₀ (by positivity) hB1_le_u6 4
      _ = u ^ 24 := by ring
  have hB1_le_fl : B + 1 ≤ ⌊Y ^ (3 / 8 : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff (by positivity), ← hu6]
    exact hB1_le_u6
  -- Función integrando y paso de `[Z, Z^{5/4}]` a `[A⁴, (B + 1)⁴]`.
  let f : ℝ → ℝ := fun y => max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
  have hf_cont : ContinuousOn f (Ioi 0) :=
    continuousOn_max_G_vonMangoldt.mul
      (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (ne_of_gt hy))
  have hf_nn : ∀ y : ℝ, 0 ≤ y → 0 ≤ f y := fun y hy =>
    mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hy _)
  have hA4_pos : (0 : ℝ) < (A : ℝ) ^ 4 := by positivity
  have hsub_Icc : Icc Z (Z ^ (1 + (1 / 4 : ℝ))) ⊆ Icc ((A : ℝ) ^ 4) (((B + 1 : ℕ) : ℝ) ^ 4) :=
    Icc_subset_Icc hA4_le_Z hZ54_le_B1
  have hint_big : IntegrableOn f (Icc ((A : ℝ) ^ 4) (((B + 1 : ℕ) : ℝ) ^ 4)) :=
    (hf_cont.mono fun y hy => lt_of_lt_of_le hA4_pos hy.1).integrableOn_Icc
  have hmono_big : ∫ y in Icc Z (Z ^ (1 + (1 / 4 : ℝ))), f y
      ≤ ∫ y in Icc ((A : ℝ) ^ 4) (((B + 1 : ℕ) : ℝ) ^ 4), f y :=
    setIntegral_mono_set hint_big
      ((ae_restrict_iff' measurableSet_Icc).mpr
        (Eventually.of_forall fun y hy => hf_nn y (le_trans hA4_pos.le hy.1)))
      (Eventually.of_forall fun y hy => hsub_Icc hy)
  -- Descomposición en celdas `[m⁴, (m + 1)⁴]`.
  have hA4_le_B14 : (A : ℝ) ^ 4 ≤ ((B + 1 : ℕ) : ℝ) ^ 4 := by
    have : (A : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : A ≤ B + 1)
    exact pow_le_pow_left₀ (by positivity) this 4
  have hsplit_sum : ∫ y in Icc ((A : ℝ) ^ 4) (((B + 1 : ℕ) : ℝ) ^ 4), f y
      = ∑ j ∈ Finset.range (B + 1 - A),
          ∫ y in (((A + j : ℕ) : ℝ) ^ 4)..(((A + (j + 1) : ℕ) : ℝ) ^ 4), f y := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hA4_le_B14]
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun j : ℕ => ((A + j : ℕ) : ℝ) ^ 4) (n := B + 1 - A) (f := f) fun j _ => by
        have hle : ((A + j : ℕ) : ℝ) ^ 4 ≤ ((A + (j + 1) : ℕ) : ℝ) ^ 4 := by
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast (by omega : A + j ≤ A + (j + 1))
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact (hf_cont.mono fun y hy => by
          have hp : (0 : ℝ) < ((A + j : ℕ) : ℝ) ^ 4 := by
            have h1 : 1 ≤ A + j := by omega
            have h2 : (0 : ℝ) < ((A + j : ℕ) : ℝ) := by exact_mod_cast h1
            positivity
          exact lt_of_lt_of_le hp hy.1).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hbot : ((A + 0 : ℕ) : ℝ) ^ 4 = (A : ℝ) ^ 4 := by simp
    have htop : ((A + (B + 1 - A) : ℕ) : ℝ) ^ 4 = ((B + 1 : ℕ) : ℝ) ^ 4 := by
      congr 2; omega
    rw [hbot, htop] at hadj
    exact hadj.symm
  -- Suma sobre las celdas y comparación con `S_AMate Y`.
  let gG : ℕ → ℝ := fun k => max (G_vonMangoldt ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
  have hgG_nn : ∀ k : ℕ, 0 ≤ gG k := fun k => div_nonneg (le_max_right _ _) (by positivity)
  have hsum_left : ∑ j ∈ Finset.range (B + 1 - A), gG (A + j)
      ≤ ∑ k ∈ Finset.Icc A (B + 1), gG k := by
    have himg : (Finset.range (B + 1 - A)).image (fun j : ℕ => A + j) ⊆ Finset.Icc A (B + 1) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]; omega
    rw [← Finset.sum_image (f := gG) (fun j₁ _ j₂ _ h => by omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg fun k _ _ => hgG_nn k
  have hsum_right : ∑ j ∈ Finset.range (B + 1 - A), gG (A + j + 1)
      ≤ ∑ k ∈ Finset.Icc A (B + 1), gG k := by
    have himg : (Finset.range (B + 1 - A)).image (fun j : ℕ => A + j + 1) ⊆ Finset.Icc A (B + 1) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]; omega
    rw [← Finset.sum_image (f := gG) (fun j₁ _ j₂ _ h => by omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg fun k _ _ => hgG_nn k
  have hsum_inv_part : ∑ j ∈ Finset.range (B + 1 - A), (1 / ((A + j : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) := by
    have himg : (Finset.range (B + 1 - A)).image (fun j : ℕ => A + j) ⊆ Finset.Icc 1 (B + 1) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]; omega
    rw [← Finset.sum_image (f := fun k : ℕ => (1 / (k : ℝ))) (fun j₁ _ j₂ _ h => by omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg fun k _ _ => by positivity
  let S_nodos : Finset ℕ := (Finset.Icc 1 ⌊Y ^ (3 / 8 : ℝ)⌋₊).filter
    (fun m : ℕ => Y ≤ (m : ℝ) ^ 4 ∧ (m : ℝ) ^ 4 ≤ Y ^ (3 / 2 : ℝ))
  have hsub_nodos : Finset.Icc A (B + 1) ⊆ S_nodos := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans hA1 hk.1, hk.2.trans hB1_le_fl⟩, ?_, ?_⟩
    · exact hA4_ge_Y.trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hk.1) 4)
    · exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hk.2) 4).trans hB1_le_Y32
  have hgG_le_S : ∑ k ∈ Finset.Icc A (B + 1), gG k
      ≤ S_AMate Y + 5 * ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) := by
    have hpt_k : ∀ k ∈ Finset.Icc A (B + 1),
        gG k ≤ max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
          + 5 * (1 / (k : ℝ)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := le_trans hA1 hk.1
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hk4_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk_ge1
      have hG := max_G_vonMangoldt_le_deficit_primos hk4_ge1
      have hlog_k4 : Real.log ((k : ℝ) ^ 4) + 1 ≤ 5 * (k : ℝ) ^ 2 := by
        rw [Real.log_pow]
        have hlk : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := by
          linarith [Real.log_le_sub_one_of_pos hk_pos]
        push_cast
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
      have hdiv_5 : (5 * (k : ℝ) ^ 2) / (k : ℝ) ^ 3 = 5 * (1 / (k : ℝ)) := by
        have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
        field_simp
      dsimp only [gG]
      calc max (G_vonMangoldt ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
          ≤ (max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0
              + (5 * (k : ℝ) ^ 2)) / (k : ℝ) ^ 3 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            linarith
        _ = max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
              + (5 * (k : ℝ) ^ 2) / (k : ℝ) ^ 3 := add_div _ _ _
        _ = max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
              + 5 * (1 / (k : ℝ)) := by rw [hdiv_5]
    have hsum1 : ∑ k ∈ Finset.Icc A (B + 1), gG k
        ≤ ∑ k ∈ Finset.Icc A (B + 1),
            (max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3)
          + 5 * ∑ k ∈ Finset.Icc A (B + 1), (1 / (k : ℝ)) := by
      calc ∑ k ∈ Finset.Icc A (B + 1), gG k
          ≤ ∑ k ∈ Finset.Icc A (B + 1),
              (max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3
                + 5 * (1 / (k : ℝ))) := Finset.sum_le_sum hpt_k
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hS_sub : ∑ k ∈ Finset.Icc A (B + 1),
          (max (Real.eulerMascheroniConstant * (k : ℝ) ^ 4 - A_primos ((k : ℝ) ^ 4)) 0 / (k : ℝ) ^ 3)
        ≤ S_AMate Y := by
      unfold S_AMate
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub_nodos fun k _ _ =>
        div_nonneg (le_max_right _ _) (by positivity)
    have hinv_sub : ∑ k ∈ Finset.Icc A (B + 1), (1 / (k : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc hA1 le_rfl)
        fun k _ _ => by positivity
    linarith
  have hlogY_ge : 8 ≤ Real.log Y := by
    have hexp8 : Real.exp 8 ≤ Y := by
      have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h8 : Real.exp 8 ≤ 3 ^ 8 := by
        rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos 1).le h3 8
      exact h8.trans (le_trans (by norm_num : (3 : ℝ) ^ 8 ≤ 5 ^ 16) hY)
    have hl := Real.log_le_log (Real.exp_pos 8) hexp8
    rwa [Real.log_exp] at hl
  have hharm_le : ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) ≤ Real.log Y := by
    have h1 := sum_inv_Icc_le (by omega : 1 ≤ B + 1)
    have hB1_pos : (0 : ℝ) < ((B + 1 : ℕ) : ℝ) := by positivity
    have h2 : Real.log ((B + 1 : ℕ) : ℝ) ≤ (3 / 8 : ℝ) * Real.log Y := by
      calc Real.log ((B + 1 : ℕ) : ℝ)
          ≤ Real.log (Y ^ (3 / 8 : ℝ)) := Real.log_le_log hB1_pos (hB1_le_u6.trans_eq hu6)
        _ = (3 / 8 : ℝ) * Real.log Y := Real.log_rpow hY_pos (3 / 8 : ℝ)
    linarith
  have hsum_cells : ∑ j ∈ Finset.range (B + 1 - A),
        ∫ y in (((A + j : ℕ) : ℝ) ^ 4)..(((A + (j + 1) : ℕ) : ℝ) ^ 4), f y
      ≤ 135 * ∑ k ∈ Finset.Icc A (B + 1), gG k
        + 855 * ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) := by
    have hstep : ∀ j ∈ Finset.range (B + 1 - A),
        ∫ y in (((A + j : ℕ) : ℝ) ^ 4)..(((A + (j + 1) : ℕ) : ℝ) ^ 4), f y
          ≤ 15 * gG (A + j) + 120 * gG (A + j + 1) + 855 * (1 / ((A + j : ℕ) : ℝ)) := by
      intro j _
      have hj_eq : A + (j + 1) = (A + j) + 1 := by omega
      rw [hj_eq]
      exact cota_celda_G_vonMangoldt (by omega : 1 ≤ A + j)
    calc ∑ j ∈ Finset.range (B + 1 - A),
          ∫ y in (((A + j : ℕ) : ℝ) ^ 4)..(((A + (j + 1) : ℕ) : ℝ) ^ 4), f y
        ≤ ∑ j ∈ Finset.range (B + 1 - A),
            (15 * gG (A + j) + 120 * gG (A + j + 1) + 855 * (1 / ((A + j : ℕ) : ℝ))) :=
          Finset.sum_le_sum hstep
      _ = 15 * (∑ j ∈ Finset.range (B + 1 - A), gG (A + j))
          + 120 * (∑ j ∈ Finset.range (B + 1 - A), gG (A + j + 1))
          + 855 * (∑ j ∈ Finset.range (B + 1 - A), (1 / ((A + j : ℕ) : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 135 * ∑ k ∈ Finset.Icc A (B + 1), gG k
          + 855 * ∑ k ∈ Finset.Icc 1 (B + 1), (1 / (k : ℝ)) := by
          linarith [hsum_left, hsum_right, hsum_inv_part]
  dsimp only [f] at hmono_big hsplit_sum hsum_cells
  linarith [hmono_big, hsplit_sum, hsum_cells, hgG_le_S, hharm_le, hlogY_ge]

/-- Si para todo `η > 0` existen escalas arbitrariamente grandes `Y` con `S_AMate Y ≤ Y^η`,
entonces se cumple `HipotesisVentanaZeta (1 / 2) (1 / 4)`. -/
theorem hipotesisVentana_de_deficit_primos
    (hS : ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η) :
    HipotesisVentanaZeta (1 / 2) (1 / 4) := by
  intro η hη Z₀
  set K_umbral : ℝ := 135 + 1600 / (η / 2)
  have hK_pos : 0 < K_umbral := by positivity
  set Y_min : ℝ := max (max (Z₀ / 16) ((5 : ℝ) ^ 16)) (K_umbral ^ (2 / η))
  obtain ⟨Y, hYY_min, hSY⟩ := hS (η / 2) (half_pos hη) Y_min
  have hY_Z0 : Z₀ / 16 ≤ Y := ((le_max_left _ _).trans (le_max_left _ _)).trans hYY_min
  have hY_516 : (5 : ℝ) ^ 16 ≤ Y := ((le_max_right _ _).trans (le_max_left _ _)).trans hYY_min
  have hY_K : K_umbral ^ (2 / η) ≤ Y := (le_max_right _ _).trans hYY_min
  have hY_pos : 0 < Y := lt_of_lt_of_le (by positivity) hY_516
  set Z : ℝ := 16 * Y
  have hZ_ge_Z0 : Z₀ ≤ Z := by dsimp only [Z]; linarith
  have hZ_ge1 : 1 ≤ Z := by dsimp only [Z]; linarith [show (1 : ℝ) ≤ (5 : ℝ) ^ 16 by norm_num]
  have hZ_pos : 0 < Z := lt_of_lt_of_le one_pos hZ_ge1
  refine ⟨Z, hZ_ge_Z0, hZ_ge1, fun y => max (G_vonMangoldt y) 0, ?_, ?_, ?_⟩
  · have hf_cont : ContinuousOn
        (fun y : ℝ => max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)) (Ioi 0) :=
      continuousOn_max_G_vonMangoldt.mul
        (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (ne_of_gt hy))
    exact (hf_cont.mono fun y hy => lt_of_lt_of_le hZ_pos hy.1).integrableOn_Icc
  · exact fun y _ => ⟨le_max_right _ _, le_max_left _ _⟩
  · have hint := integral_ventana_le_S_AMate hY_516
    have hlog_le : Real.log Y ≤ Y ^ (η / 2) / (η / 2) :=
      Real.log_le_rpow_div hY_pos.le (half_pos hη)
    have hK_le : K_umbral ≤ Y ^ (η / 2) := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hK_pos.le _) hY_K (half_pos hη).le
      rw [← Real.rpow_mul hK_pos.le, show (2 / η) * (η / 2) = 1 by field_simp,
        Real.rpow_one] at h1
      exact h1
    have hYZ_rpow : Y ^ η ≤ Z ^ η :=
      Real.rpow_le_rpow hY_pos.le (by dsimp only [Z]; linarith) hη.le
    calc ∫ y in Icc Z (Z ^ (1 + (1 / 4 : ℝ))),
          max (G_vonMangoldt y) 0 * y ^ (-(1 / 2 : ℝ) - 1)
        ≤ 135 * S_AMate Y + 1600 * Real.log Y := hint
      _ ≤ 135 * Y ^ (η / 2) + 1600 * (Y ^ (η / 2) / (η / 2)) := by
          linarith [mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ 1600)]
      _ = K_umbral * Y ^ (η / 2) := by simp only [K_umbral]; ring
      _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
          mul_le_mul_of_nonneg_right hK_le (Real.rpow_nonneg hY_pos.le _)
      _ = Y ^ η := by rw [← Real.rpow_add hY_pos]; congr 1; ring
      _ ≤ Z ^ η := hYZ_rpow

/-- Ausencia directa de ceros de `ζ` en `Re s > 1/2` a partir de la suma de déficits `S_AMate`. -/
theorem sin_ceros_de_deficit_primos
    (hS : ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η) :
    ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0 :=
  sin_ceros_de_ventana_integral (by norm_num) (by norm_num) (by norm_num)
    (hipotesisVentana_de_deficit_primos hS)

/-- **Teorema del déficit sobre primos (`S_AMate ≤ Y^η ⇒ RH`):**
si para cada `η > 0` existen escalas arbitrariamente grandes `Y` tales que `S_AMate Y ≤ Y^η`,
entonces se cumple `RiemannHypothesis`. -/
theorem rh_de_deficit_primos
    (hS : ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η) :
    RiemannHypothesis :=
  rh_of_no_zero_gt_half (sin_ceros_de_deficit_primos hS)

/-- **Cota subpolinomial uniforme de `E_Q` desde `S_AMate`:**
si para cada `η > 0` existen escalas arbitrariamente grandes `Y` con `S_AMate Y ≤ Y^η`,
entonces `E_Q ≤ C_ε Q^ε` para todo `ε > 0` y todo `Q ≥ 2`. -/
theorem energia_de_deficit_primos
    (hS : ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ S_AMate Y ≤ Y ^ η) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε :=
  energia_subpolinomial (rh_de_deficit_primos hS)

end AMate
