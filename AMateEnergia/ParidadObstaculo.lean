import AMateEnergia.CalibracionTheta
import AMateEnergia.DeficitPrimos

/-!
# Giros de paridad, fibras radicales y correlaciones de primos grandes `(406)`–`(410)`

Formalización completa en Lean 4 (solo Mathlib, cero `sorry`) del análisis combinatorio y de signo
de las secciones `(406)`–`(410)` de
`HIPOTESIS_DE_RIEMANN_DESDE_VENTANAS_DE_VON_MANGOLDT_2026-11-20.md` y su interacción con la
cancelación de Möbius por columnas:

* **`(408)` Descomposición por radicales impares de primos grandes (`radicalImparGrande z n`):**
  todo entero `n ≥ 1` se factoriza canónicamente como `n = k · s · h²`, donde `k = r_z(n)` es el
  producto de los primos `p > z` con exponente impar `v_p(n)`, `s` es libre de cuadrados soportado
  en primos `p ≤ z`, y `h = ∏ p^{⌊v_p(n)/2⌋}` (`descomposicion_fibra_408`). En consecuencia, cada
  fibra `{n ∈ [1, N] | r_z(n) = k}` tiene cardinal `≤ 2^{π(z)} ⌊√(N/k)⌋₊`
  (`card_fibra_radicalImparGrande_408`).
* **`(406)` Ortogonalidad multiplicativa de Rademacher y media cuadrática `O(N log N)`:**
  promediando sobre signos independientes `ω : P → Bool` en los primos `p ≤ N`, los productos
  cruzados se anulan salvo cuando `r_0(n) = r_0(m)` (`ortogonalidad_rademacher`,
  `media_cuadratica_rademacher_406`), dando una cota media `≤ M_c² N (1 + log N)`
  (`cota_media_rademacher_406`).
* **`(407)` Sesgo cuadrático positivo del giro determinista de Liouville `λ(n)`:**
  como `μ(a) λ(a) = μ(a)²` para todo `a : ℕ` (`mu_mul_liouville`), el giro multiplicativo global
  `λ(ab)` convierte `μ(a) μ(b) λ(ab)` en `μ(a)² μ(b)² ≥ 0` (`moebius_mul_liouville_407`),
  destruyendo toda cancelación entre libres de cuadrados (`sesgo_positivo_liouville_407`).
* **`(409)` Factorización exacta de giros truncados `ξ_z(n)` y obstáculo de Cauchy–Schwarz:**
  el giro de paridad truncado en primos `p > z` depende de `n` únicamente a través de su clase
  radical `k = r_z(n)`: `ξ_z(n) = λ(r_z(n))` (`giroTruncado_eq_liouville_radical`), de modo que
  `(∑_{n=1}^N ξ_z(n) c(n))² ≤ N ∑_{k=1}^N D_z(k)²` (`obstaculo_cauchy_paridad_409`).
* **`(410)` Pares fuera de la diagonal `p ≠ r > z` y cancelación condicional por columnas:**
  dos primos grandes distintos `p ≠ r > z` multiplicados por un mismo primo corto `b ≤ z` caen en
  clases radicales distintas `r_z(pb) = p ≠ r = r_z(rb)` y comparten signo `μ(pb) μ(rb) = +1`
  (`pares_primos_fuera_diagonal_410`, `identidad_fuera_diagonal_410`). Al restituir cofactores
  compuestos `a ∈ [A, B]` bajo `SinCerosDerecha θ` (y en particular bajo `RiemannHypothesis`),
  la suma parcial `|M(n)| ≤ K n^{θ+δ}` (`M_moebius_bound_theta`, Estado 45 `(5.1)`) cancela la
  columna `|∑_{a=A}^B μ(a) w(a)| ≤ K B^{θ+δ} TV(w)` mediante sumación de Abel
  (`cancelacion_columna_moebius_theta`, `cancelacion_columna_moebius_rh`).
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate

/-! ### 1. Factorización por radicales impares y parte cuadrada `(408)` -/

/-- Producto de los primos `p > z` donde `n` tiene valuación `p`-ádica impar (`r_z(n)` en `(408)`). -/
def radicalImparGrande (z n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p : ℕ => z < p ∧ Odd (n.factorization p)), p

/-- Producto de los primos cortos `p ≤ z` donde `n` tiene valuación `p`-ádica impar (`s` en `(408)`). -/
def radicalImparPequeno (z n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p : ℕ => p ≤ z ∧ Odd (n.factorization p)), p

/-- Raíz de la mayor parte cuadrada que divide a `n`: `h = ∏ p^{⌊v_p(n)/2⌋}` (`n = k · s · h²`). -/
def parteCuadradaRaiz (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

theorem factorization_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have ha : Nat.Prime a := hS a (Finset.mem_cons_self a s)
    have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_cons.mpr (Or.inr hp))
    have hs_ne : ∏ p ∈ s, p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hs p hp).ne_zero
    rw [Finset.prod_cons, Nat.factorization_mul ha.ne_zero hs_ne, Finsupp.add_apply,
      ih hs, ha.factorization, Finsupp.single_apply]
    simp only [Finset.mem_cons]
    by_cases hqa : q = a
    · subst hqa; simp [has]
    · have haq : a ≠ q := Ne.symm hqa
      simp [hqa, haq]

theorem factorization_prod_prime_pows {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (e : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ S, p ^ (e p)).factorization q = if q ∈ S then e q else 0 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    have ha : Nat.Prime a := hS a (Finset.mem_cons_self a s)
    have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_cons.mpr (Or.inr hp))
    have ha_ne : a ^ (e a) ≠ 0 := pow_ne_zero _ ha.ne_zero
    have hs_ne : ∏ p ∈ s, p ^ (e p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hs p hp).ne_zero
    rw [Finset.prod_cons, Nat.factorization_mul ha_ne hs_ne, Finsupp.add_apply,
      ih hs, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      ha.factorization, Finsupp.single_apply]
    simp only [Finset.mem_cons]
    by_cases hqa : q = a
    · subst hqa; simp [has]
    · have haq : a ≠ q := Ne.symm hqa
      simp [hqa, haq]

theorem mem_primeFactors_of_factorization_ne_zero {n q : ℕ} (h : n.factorization q ≠ 0) :
    q ∈ n.primeFactors := by
  have hq_prime : Nat.Prime q := by
    by_contra hnp
    exact h (Nat.factorization_eq_zero_of_not_prime n hnp)
  have hq_dvd : q ∣ n := by
    by_contra hnd
    exact h (Nat.factorization_eq_zero_of_not_dvd hnd)
  have hn_ne : n ≠ 0 := by
    rintro rfl
    simp at h
  exact Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, hn_ne⟩

theorem mem_primeFactors_of_odd_factorization {n q : ℕ} (h : Odd (n.factorization q)) :
    q ∈ n.primeFactors := by
  apply mem_primeFactors_of_factorization_ne_zero
  rcases h with ⟨k, hk⟩
  omega

theorem radicalImparGrande_pos (z n : ℕ) : 0 < radicalImparGrande z n :=
  Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem radicalImparPequeno_pos (z n : ℕ) : 0 < radicalImparPequeno z n :=
  Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem parteCuadradaRaiz_pos (n : ℕ) : 0 < parteCuadradaRaiz n :=
  Finset.prod_pos fun _ hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _

theorem factorization_radicalImparGrande (z n q : ℕ) :
    (radicalImparGrande z n).factorization q = if z < q ∧ Odd (n.factorization q) then 1 else 0 := by
  unfold radicalImparGrande
  rw [factorization_prod_primes
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  have hiff : q ∈ n.primeFactors.filter (fun p : ℕ => z < p ∧ Odd (n.factorization p))
      ↔ z < q ∧ Odd (n.factorization q) :=
    ⟨fun h => (Finset.mem_filter.mp h).2,
     fun h => Finset.mem_filter.mpr ⟨mem_primeFactors_of_odd_factorization h.2, h⟩⟩
  by_cases h : z < q ∧ Odd (n.factorization q)
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hm => h (hiff.mp hm))]

theorem factorization_radicalImparPequeno (z n q : ℕ) :
    (radicalImparPequeno z n).factorization q = if q ≤ z ∧ Odd (n.factorization q) then 1 else 0 := by
  unfold radicalImparPequeno
  rw [factorization_prod_primes
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  have hiff : q ∈ n.primeFactors.filter (fun p : ℕ => p ≤ z ∧ Odd (n.factorization p))
      ↔ q ≤ z ∧ Odd (n.factorization q) :=
    ⟨fun h => (Finset.mem_filter.mp h).2,
     fun h => Finset.mem_filter.mpr ⟨mem_primeFactors_of_odd_factorization h.2, h⟩⟩
  by_cases h : q ≤ z ∧ Odd (n.factorization q)
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hm => h (hiff.mp hm))]

theorem factorization_parteCuadradaRaiz (n q : ℕ) :
    (parteCuadradaRaiz n).factorization q = n.factorization q / 2 := by
  unfold parteCuadradaRaiz
  rw [factorization_prod_prime_pows (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  by_cases hq : q ∈ n.primeFactors
  · rw [if_pos hq]
  · rw [if_neg hq]
    have h0 : n.factorization q = 0 := by
      by_contra hne
      exact hq (mem_primeFactors_of_factorization_ne_zero hne)
    rw [h0]

/-- **Descomposición canónica `(408)`:** todo `n ≠ 0` se escribe como `n = r_z(n) · s_z(n) · h(n)²`. -/
theorem descomposicion_fibra_408 (z : ℕ) {n : ℕ} (hn : n ≠ 0) :
    radicalImparGrande z n * radicalImparPequeno z n * (parteCuadradaRaiz n) ^ 2 = n := by
  have hk_ne : radicalImparGrande z n ≠ 0 := (radicalImparGrande_pos z n).ne'
  have hs_ne : radicalImparPequeno z n ≠ 0 := (radicalImparPequeno_pos z n).ne'
  have hh_ne : (parteCuadradaRaiz n) ^ 2 ≠ 0 := pow_ne_zero 2 (parteCuadradaRaiz_pos n).ne'
  apply Nat.eq_of_factorization_eq (mul_ne_zero (mul_ne_zero hk_ne hs_ne) hh_ne) hn
  intro q
  rw [Nat.factorization_mul (mul_ne_zero hk_ne hs_ne) hh_ne,
    Nat.factorization_mul hk_ne hs_ne, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    factorization_radicalImparGrande, factorization_radicalImparPequeno,
    factorization_parteCuadradaRaiz]
  have hpar : (if z < q ∧ Odd (n.factorization q) then 1 else 0)
      + (if q ≤ z ∧ Odd (n.factorization q) then 1 else 0)
      = if Odd (n.factorization q) then 1 else 0 := by
    by_cases hqz : z < q
    · have hnot : ¬ q ≤ z := not_le.mpr hqz
      by_cases ho : Odd (n.factorization q) <;> simp [hqz, hnot, ho]
    · have hle : q ≤ z := not_lt.mp hqz
      by_cases ho : Odd (n.factorization q) <;> simp [hqz, hle, ho]
  rw [hpar]
  by_cases ho : Odd (n.factorization q)
  · rw [if_pos ho]
    rcases ho with ⟨m, hm⟩
    omega
  · rw [if_neg ho]
    rw [Nat.not_odd_iff_even] at ho
    rcases ho with ⟨m, hm⟩
    omega

theorem radicalImparGrande_dvd (z n : ℕ) : radicalImparGrande z n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  · exact ⟨radicalImparPequeno z n * (parteCuadradaRaiz n) ^ 2,
      by rw [← mul_assoc, descomposicion_fibra_408 z hn]⟩

theorem radicalImparGrande_le (z : ℕ) {n : ℕ} (hn : 1 ≤ n) : radicalImparGrande z n ≤ n :=
  Nat.le_of_dvd (by omega) (radicalImparGrande_dvd z n)

/-- **Cota de cardinal de las fibras radicales `(408)`:**
para `k ≥ 1`, el número de enteros `n ∈ [1, N]` con `r_z(n) = k` es a lo sumo
`2^{π(z)} · ⌊√(N / k)⌋₊`. -/
theorem card_fibra_radicalImparGrande_408 (z N k : ℕ) (hk1 : 1 ≤ k) :
    ((Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande z n = k)).card
      ≤ 2 ^ ((Finset.Icc 1 z).filter Nat.Prime).card * ⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊ := by
  let P_z : Finset ℕ := (Finset.Icc 1 z).filter Nat.Prime
  let F : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande z n = k)
  let S_z : ℕ → Finset ℕ := fun n =>
    n.primeFactors.filter (fun p : ℕ => p ≤ z ∧ Odd (n.factorization p))
  let φ : ℕ → Finset ℕ × ℕ := fun n => (S_z n, parteCuadradaRaiz n)
  let G : Finset (Finset ℕ × ℕ) :=
    P_z.powerset ×ˢ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊
  have hinj : Set.InjOn φ F := by
    intro n₁ hn₁ n₂ hn₂ hφ
    have h1_Icc := (Finset.mem_filter.mp hn₁).1
    have h1_k := (Finset.mem_filter.mp hn₁).2
    have h2_Icc := (Finset.mem_filter.mp hn₂).1
    have h2_k := (Finset.mem_filter.mp hn₂).2
    have hn₁_ne : n₁ ≠ 0 := by have := (Finset.mem_Icc.mp h1_Icc).1; omega
    have hn₂_ne : n₂ ≠ 0 := by have := (Finset.mem_Icc.mp h2_Icc).1; omega
    have hS : S_z n₁ = S_z n₂ := congrArg Prod.fst hφ
    have hh : parteCuadradaRaiz n₁ = parteCuadradaRaiz n₂ := congrArg Prod.snd hφ
    have hs_eq : radicalImparPequeno z n₁ = radicalImparPequeno z n₂ :=
      congrArg (fun T : Finset ℕ => ∏ p ∈ T, p) hS
    rw [← descomposicion_fibra_408 z hn₁_ne, ← descomposicion_fibra_408 z hn₂_ne,
      h1_k, h2_k, hs_eq, hh]
  have hsub : F.image φ ⊆ G := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨n, hnF, rfl⟩
    have hn_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hnF).1
    have hn_k : radicalImparGrande z n = k := (Finset.mem_filter.mp hnF).2
    have hn_ne : n ≠ 0 := by omega
    have hS_mem : S_z n ∈ P_z.powerset := by
      rw [Finset.mem_powerset]
      intro p hp
      have hp_pf := (Finset.mem_filter.mp hp).1
      have hp_le := (Finset.mem_filter.mp hp).2.1
      have hp_pr := Nat.prime_of_mem_primeFactors hp_pf
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pr.one_lt.le, hp_le⟩, hp_pr⟩
    have hh_ge1 : 1 ≤ parteCuadradaRaiz n := parteCuadradaRaiz_pos n
    have hh_le : parteCuadradaRaiz n ≤ ⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊ := by
      apply Nat.le_floor
      apply Real.le_sqrt_of_sq_le
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [le_div_iff₀ hk_pos]
      have hmul_nat : k * (parteCuadradaRaiz n) ^ 2 ≤ N := by
        have hs1 : 1 ≤ radicalImparPequeno z n := radicalImparPequeno_pos z n
        calc k * (parteCuadradaRaiz n) ^ 2
            = (k * 1) * (parteCuadradaRaiz n) ^ 2 := by ring
          _ ≤ (k * radicalImparPequeno z n) * (parteCuadradaRaiz n) ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k hs1)
          _ = n := by rw [← hn_k, descomposicion_fibra_408 z hn_ne]
          _ ≤ N := hn_Icc.2
      have hcast : ((k * (parteCuadradaRaiz n) ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hmul_nat
      push_cast at hcast
      linarith
    exact Finset.mem_product.mpr ⟨hS_mem, Finset.mem_Icc.mpr ⟨hh_ge1, hh_le⟩⟩
  calc F.card = (F.image φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ G.card := Finset.card_le_card hsub
    _ = 2 ^ P_z.card * ⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊ := by
        simp [G]

/-! ### 2. Giros aleatorios de Rademacher y media cuadrática `O(N log N)` `(406)` -/

/-- Giro multiplicativo de Rademacher sobre un conjunto finito de primos `P`. -/
def giroRademacher (P : Finset ℕ) (ω : P → Bool) (n : ℕ) : ℝ :=
  ∏ p : P, if ω p then (-1 : ℝ) ^ (n.factorization p.1) else 1

/-- Primos en `[1, N]`. -/
def primosHasta (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime

/-- **Ortogonalidad multiplicativa de Rademacher `(406)`:**
el promedio sobre `ω ∈ {±1}^P` de `ξ_ω(n) ξ_ω(m)` vale `1` si `v_p(n) + v_p(m)` es par para todo
`p ∈ P`, y `0` en caso contrario. -/
theorem ortogonalidad_rademacher (P : Finset ℕ) (n m : ℕ) :
    (1 / (2 : ℝ) ^ P.card) * ∑ ω : P → Bool, giroRademacher P ω n * giroRademacher P ω m
      = if ∀ p ∈ P, Even (n.factorization p + m.factorization p) then 1 else 0 := by
  classical
  let g : P → Bool → ℝ := fun p b =>
    (if b then (-1 : ℝ) ^ (n.factorization p.1) else 1) *
      (if b then (-1 : ℝ) ^ (m.factorization p.1) else 1)
  have hprod_sum : ∑ ω : P → Bool, giroRademacher P ω n * giroRademacher P ω m
      = ∏ p : P, ∑ b : Bool, g p b := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    unfold giroRademacher
    rw [← Finset.prod_mul_distrib]
  have hfactor : ∀ p : P, ∑ b : Bool, g p b
      = if Even (n.factorization p.1 + m.factorization p.1) then 2 else 0 := by
    intro p
    rw [Fintype.sum_bool]
    dsimp only [g]
    simp only [ ↓reduceIte, Bool.false_eq_true, mul_one, ← pow_add]
    by_cases he : Even (n.factorization p.1 + m.factorization p.1)
    · rw [if_pos he, he.neg_one_pow]; norm_num
    · rw [if_neg he, (Nat.not_even_iff_odd.mp he).neg_one_pow]; norm_num
  rw [hprod_sum]
  by_cases hall : ∀ p ∈ P, Even (n.factorization p + m.factorization p)
  · rw [if_pos hall]
    have hp2 : ∏ p : P, ∑ b : Bool, g p b = (2 : ℝ) ^ P.card := by
      calc ∏ p : P, ∑ b : Bool, g p b
          = ∏ _p : P, (2 : ℝ) := Finset.prod_congr rfl fun p _ => by
              rw [hfactor p, if_pos (hall p.1 p.2)]
        _ = (2 : ℝ) ^ (Fintype.card P) := by rw [Finset.prod_const, Finset.card_univ]
        _ = (2 : ℝ) ^ P.card := by rw [Fintype.card_coe]
    rw [hp2]
    field_simp
  · rw [if_neg hall]
    push Not at hall
    rcases hall with ⟨p₀, hp₀, hnot_ev⟩
    have hzero : ∏ p : P, ∑ b : Bool, g p b = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ (⟨p₀, hp₀⟩ : P)) ?_
      rw [hfactor ⟨p₀, hp₀⟩, if_neg hnot_ev]
    rw [hzero, mul_zero]

theorem even_add_iff_odd_iff (a b : ℕ) : Even (a + b) ↔ (Odd a ↔ Odd b) := by
  rw [Nat.even_iff, Nat.odd_iff, Nat.odd_iff]
  omega

theorem condicion_paridad_eq_radical_cero {N n m : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hm : m ∈ Finset.Icc 1 N) :
    (∀ p ∈ primosHasta N, Even (n.factorization p + m.factorization p))
      ↔ radicalImparGrande 0 n = radicalImparGrande 0 m := by
  have hn_le : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hm_le : m ≤ N := (Finset.mem_Icc.mp hm).2
  constructor
  · intro hall
    apply Nat.eq_of_factorization_eq (radicalImparGrande_pos 0 n).ne' (radicalImparGrande_pos 0 m).ne'
    intro q
    rw [factorization_radicalImparGrande, factorization_radicalImparGrande]
    by_cases hq_pr : Nat.Prime q
    · by_cases hq_le : q ≤ N
      · have hqP : q ∈ primosHasta N :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_pr.one_lt.le, hq_le⟩, hq_pr⟩
        have hodd_iff := (even_add_iff_odd_iff _ _).mp (hall q hqP)
        simp only [hq_pr.pos, true_and, hodd_iff]
      · have hgt_n : n < q := by omega
        have hgt_m : m < q := by omega
        rw [Nat.factorization_eq_zero_of_lt hgt_n, Nat.factorization_eq_zero_of_lt hgt_m]
    · rw [Nat.factorization_eq_zero_of_not_prime n hq_pr,
        Nat.factorization_eq_zero_of_not_prime m hq_pr]
  · intro hrad p hp
    rw [even_add_iff_odd_iff]
    have hp_pos : 0 < p := (Finset.mem_filter.mp hp).2.pos
    have hfq := congrArg (fun k : ℕ => k.factorization p) hrad
    simp only [factorization_radicalImparGrande, hp_pos, true_and] at hfq
    by_cases ho1 : Odd (n.factorization p) <;> by_cases ho2 : Odd (m.factorization p) <;>
      simp [ho1, ho2] at hfq ⊢

/-- **Identidad exacta de segundo momento de Rademacher `(406)`:**
la esperanza cuadrática sobre signos aleatorios en los primos `p ≤ N` diagonaliza exactamente
según los núcleos libres de cuadrados `k = r_0(n)`. -/
theorem media_cuadratica_rademacher_406 (N : ℕ) (c : ℕ → ℝ) :
    (1 / (2 : ℝ) ^ (primosHasta N).card) *
        ∑ ω : primosHasta N → Bool,
          (∑ n ∈ Finset.Icc 1 N, giroRademacher (primosHasta N) ω n * c n) ^ 2
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k), c n) ^ 2 := by
  have hexpand : ∀ ω : primosHasta N → Bool,
      (∑ n ∈ Finset.Icc 1 N, giroRademacher (primosHasta N) ω n * c n) ^ 2
        = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (giroRademacher (primosHasta N) ω n * giroRademacher (primosHasta N) ω m) * (c n * c m) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  have hlhs_eq : (1 / (2 : ℝ) ^ (primosHasta N).card) *
      ∑ ω : primosHasta N → Bool,
        (∑ n ∈ Finset.Icc 1 N, giroRademacher (primosHasta N) ω n * c n) ^ 2
      = ∑ n ∈ Finset.Icc 1 N,
          (1 / (2 : ℝ) ^ (primosHasta N).card) *
            ∑ ω : primosHasta N → Bool,
              ∑ m ∈ Finset.Icc 1 N,
                (giroRademacher (primosHasta N) ω n * giroRademacher (primosHasta N) ω m) * (c n * c m) := by
    simp_rw [hexpand]
    rw [Finset.sum_comm, Finset.mul_sum]
  have hinner : ∀ n ∈ Finset.Icc 1 N,
      (1 / (2 : ℝ) ^ (primosHasta N).card) *
        ∑ ω : primosHasta N → Bool,
          ∑ m ∈ Finset.Icc 1 N,
            (giroRademacher (primosHasta N) ω n * giroRademacher (primosHasta N) ω m) * (c n * c m)
      = ∑ m ∈ Finset.Icc 1 N,
          if radicalImparGrande 0 n = radicalImparGrande 0 m then c n * c m else 0 := by
    intro n hn
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_mul, ← mul_assoc, ortogonalidad_rademacher]
    simp only [condicion_paridad_eq_radical_cero hn hm]
    by_cases h : radicalImparGrande 0 n = radicalImparGrande 0 m <;> simp [h]
  rw [hlhs_eq, Finset.sum_congr rfl hinner]
  -- Agrupación por fibras `k = r_0(n) ∈ [1, N]`.
  have hmaps : ∀ n ∈ Finset.Icc 1 N, radicalImparGrande 0 n ∈ Finset.Icc 1 N := fun n hn => by
    have hn_Icc := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨radicalImparGrande_pos 0 n,
      (radicalImparGrande_le 0 hn_Icc.1).trans hn_Icc.2⟩
  symm
  calc ∑ k ∈ Finset.Icc 1 N,
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k), c n) ^ 2
      = ∑ k ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k),
            c n * ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => radicalImparGrande 0 m = k), c m := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul]
    _ = ∑ k ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k),
            ∑ m ∈ Finset.Icc 1 N,
              if radicalImparGrande 0 n = radicalImparGrande 0 m then c n * c m else 0 := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n hn => ?_
          have hnk : radicalImparGrande 0 n = k := (Finset.mem_filter.mp hn).2
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hnk]
          by_cases hmk : radicalImparGrande 0 m = k
          · simp [hmk]
          · have hkm : ¬ k = radicalImparGrande 0 m := fun h => hmk h.symm
            simp [hmk, hkm]
    _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 N,
            if radicalImparGrande 0 n = radicalImparGrande 0 m then c n * c m else 0 :=
        Finset.sum_fiberwise_of_maps_to hmaps _

/-- **Cota `O(N log N)` de `(406)`:** si `|c(n)| ≤ M_c` en `[1, N]` (`N ≥ 1`), la media cuadrática
bajo giros de Rademacher está acotada por `M_c² · N · (1 + log N)`. -/
theorem cota_media_rademacher_406 {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℝ} {M_c : ℝ}
    (hMc0 : 0 ≤ M_c) (hc : ∀ n ∈ Finset.Icc 1 N, |c n| ≤ M_c) :
    (1 / (2 : ℝ) ^ (primosHasta N).card) *
        ∑ ω : primosHasta N → Bool,
          (∑ n ∈ Finset.Icc 1 N, giroRademacher (primosHasta N) ω n * c n) ^ 2
      ≤ M_c ^ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  rw [media_cuadratica_rademacher_406]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k), c n) ^ 2
        ≤ (M_c ^ 2 * (N : ℝ)) * (1 / (k : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    let F_k := (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k)
    have hcard0 : F_k.card ≤ ⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊ := by
      have hc0 := card_fibra_radicalImparGrande_408 0 N k hk1
      have hemp : (Finset.Icc 1 0).filter Nat.Prime = ∅ := by simp
      simpa [F_k, hemp] using hc0
    have hcard_real : (F_k.card : ℝ) ≤ Real.sqrt ((N : ℝ) / (k : ℝ)) :=
      (show (F_k.card : ℝ) ≤ (⌊Real.sqrt ((N : ℝ) / (k : ℝ))⌋₊ : ℝ) by exact_mod_cast hcard0).trans
        (Nat.floor_le (Real.sqrt_nonneg _))
    have habs_sum : |∑ n ∈ F_k, c n| ≤ M_c * Real.sqrt ((N : ℝ) / (k : ℝ)) := by
      calc |∑ n ∈ F_k, c n|
          ≤ ∑ n ∈ F_k, |c n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ F_k, M_c :=
            Finset.sum_le_sum fun n hn => hc n (Finset.mem_filter.mp hn).1
        _ = (F_k.card : ℝ) * M_c := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Real.sqrt ((N : ℝ) / (k : ℝ)) * M_c :=
            mul_le_mul_of_nonneg_right hcard_real hMc0
        _ = M_c * Real.sqrt ((N : ℝ) / (k : ℝ)) := by ring
    calc (∑ n ∈ F_k, c n) ^ 2
        = |∑ n ∈ F_k, c n| ^ 2 := (sq_abs _).symm
      _ ≤ (M_c * Real.sqrt ((N : ℝ) / (k : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs_sum 2
      _ = M_c ^ 2 * (Real.sqrt ((N : ℝ) / (k : ℝ))) ^ 2 := mul_pow _ _ 2
      _ = M_c ^ 2 * ((N : ℝ) / (k : ℝ)) := by
          rw [Real.sq_sqrt (div_nonneg (Nat.cast_nonneg N) hk_pos.le)]
      _ = (M_c ^ 2 * (N : ℝ)) * (1 / (k : ℝ)) := by ring
  calc ∑ k ∈ Finset.Icc 1 N,
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande 0 n = k), c n) ^ 2
      ≤ ∑ k ∈ Finset.Icc 1 N, (M_c ^ 2 * (N : ℝ)) * (1 / (k : ℝ)) :=
          Finset.sum_le_sum hterm
    _ = (M_c ^ 2 * (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) :=
          (Finset.mul_sum _ _ _).symm
    _ ≤ (M_c ^ 2 * (N : ℝ)) * (1 + Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le hN) (by positivity)
    _ = M_c ^ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) := by ring

/-! ### 3. Giro determinista de Liouville y sesgo cuadrático positivo `(407)` -/

/-- Función de Liouville `λ(n) = (−1)^{Ω(n)}` (con `λ(0) = 1` por convención `0.factorization = 0`). -/
def liouville (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n.factorization.sum fun _ e => e)

theorem liouville_sq (n : ℕ) : (liouville n) ^ 2 = 1 := by
  unfold liouville
  rw [← pow_mul, mul_comm]
  exact (even_two_mul _).neg_one_pow

theorem liouville_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    liouville (a * b) = liouville a * liouville b := by
  unfold liouville
  rw [Nat.factorization_mul ha hb, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), pow_add]

/-- Identidad puntual `μ(a) · λ(a) = μ(a)²` para todo `a : ℕ`. -/
theorem mu_mul_liouville (a : ℕ) : mu a * liouville a = (mu a) ^ 2 := by
  induction a using Nat.recOnPrimeCoprime with
  | zero => simp [mu]
  | prime_pow p k hp =>
    rcases k with _ | _ | k
    · simp only [pow_zero]
      have hli1 : liouville 1 = 1 := by
        unfold liouville
        rw [Nat.factorization_one, Finsupp.sum_zero_index, pow_zero]
      rw [hli1, mul_one]
      unfold mu
      rw [ArithmeticFunction.moebius_apply_one]
      norm_num
    · rw [Nat.zero_add, pow_one]
      have hmu : mu p = -1 := by
        unfold mu
        rw [ArithmeticFunction.moebius_apply_prime hp]
        norm_num
      have hli : liouville p = -1 := by
        unfold liouville
        rw [hp.factorization, Finsupp.sum_single_index rfl]
        norm_num
      rw [hmu, hli]
      norm_num
    · have hmu0 : mu (p ^ (k + 2)) = 0 := by
        unfold mu
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k + 2 ≠ 0),
          if_neg (by omega : k + 2 ≠ 1)]
        norm_num
      rw [hmu0]
      ring
  | coprime a b ha1 hb1 hab ha_ih hb_ih =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hmu_mul : mu (a * b) = mu a * mu b := by
      unfold mu
      rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hab]
      push_cast; rfl
    rw [hmu_mul, liouville_mul ha0 hb0]
    calc (mu a * mu b) * (liouville a * liouville b)
        = (mu a * liouville a) * (mu b * liouville b) := by ring
      _ = (mu a) ^ 2 * (mu b) ^ 2 := by rw [ha_ih, hb_ih]
      _ = (mu a * mu b) ^ 2 := by ring

/-- **Identidad `(407)`:** `μ(a) μ(b) λ(ab) = μ(a)² μ(b)² ≥ 0` para todo `a, b ≠ 0`. -/
theorem moebius_mul_liouville_407 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    mu a * mu b * liouville (a * b) = (mu a) ^ 2 * (mu b) ^ 2 := by
  rw [liouville_mul ha hb]
  calc mu a * mu b * (liouville a * liouville b)
      = (mu a * liouville a) * (mu b * liouville b) := by ring
    _ = (mu a) ^ 2 * (mu b) ^ 2 := by rw [mu_mul_liouville, mu_mul_liouville]

theorem mu_sq_eq_ite_squarefree (a : ℕ) : (mu a) ^ 2 = if Squarefree a then 1 else 0 := by
  classical
  by_cases ha : Squarefree a
  · rw [if_pos ha]
    unfold mu
    rw [ArithmeticFunction.moebius_apply_of_squarefree ha]
    push_cast
    rw [← pow_mul, mul_comm]
    exact (even_two_mul _).neg_one_pow
  · rw [if_neg ha]
    unfold mu
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree ha]
    norm_num

/-- **Sesgo positivo de Liouville `(407)`:** para pesos no negativos `W(a, b) ≥ 0` sobre conjuntos
finitos de enteros positivos `A, B`, insertar el giro `λ(ab)` elimina toda cancelación de Möbius
y deja exactamente la suma positiva sobre pares libres de cuadrados. -/
theorem sesgo_positivo_liouville_407 {A B : Finset ℕ} (hA : 0 ∉ A) (hB : 0 ∉ B)
    (W : ℕ → ℕ → ℝ) (hW : ∀ a ∈ A, ∀ b ∈ B, 0 ≤ W a b) :
    (∑ a ∈ A, ∑ b ∈ B, mu a * mu b * liouville (a * b) * W a b
        = ∑ a ∈ A.filter Squarefree, ∑ b ∈ B.filter Squarefree, W a b) ∧
      0 ≤ ∑ a ∈ A, ∑ b ∈ B, mu a * mu b * liouville (a * b) * W a b := by
  classical
  have heq : ∑ a ∈ A, ∑ b ∈ B, mu a * mu b * liouville (a * b) * W a b
      = ∑ a ∈ A.filter Squarefree, ∑ b ∈ B.filter Squarefree, W a b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := fun h => hA (h ▸ ha)
    rw [Finset.sum_filter]
    by_cases hasf : Squarefree a
    · rw [if_pos hasf]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb0 : b ≠ 0 := fun h => hB (h ▸ hb)
      rw [moebius_mul_liouville_407 ha0 hb0, mu_sq_eq_ite_squarefree a,
        mu_sq_eq_ite_squarefree b, if_pos hasf]
      by_cases hbsf : Squarefree b <;> simp [hbsf]
    · rw [if_neg hasf]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb0 : b ≠ 0 := fun h => hB (h ▸ hb)
      rw [moebius_mul_liouville_407 ha0 hb0, mu_sq_eq_ite_squarefree a, if_neg hasf]
      ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb =>
    hW a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1

/-! ### 4. Giros truncados `ξ_z(n)` y obstáculo de Cauchy–Schwarz `(409)` -/

/-- Giro de paridad truncado en primos grandes `p > z`: `ξ_z(n) = (−1)^{∑_{p > z} v_p(n)}`. -/
def giroTruncado (z n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (∑ p ∈ n.primeFactors.filter (fun p : ℕ => z < p), n.factorization p)

/-- Suma de coeficientes sobre la clase radical `r_z(n) = k` en `[1, N]` (`D_z(k)` en `(409)`). -/
def D_clase (z N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande z n = k), c n

/-- **Factorización exacta `(409)`:** el giro truncado `ξ_z(n)` depende de `n` únicamente a través
de la clase radical `k = r_z(n)`: `ξ_z(n) = λ(r_z(n))`. -/
theorem giroTruncado_eq_liouville_radical (z n : ℕ) :
    giroTruncado z n = liouville (radicalImparGrande z n) := by
  unfold giroTruncado liouville
  let T : Finset ℕ := n.primeFactors.filter (fun p : ℕ => z < p)
  let S : Finset ℕ := n.primeFactors.filter (fun p : ℕ => z < p ∧ Odd (n.factorization p))
  have hsum_rad : ((radicalImparGrande z n).factorization.sum fun _ e => e) = S.card := by
    unfold Finsupp.sum
    have hsupp : (radicalImparGrande z n).factorization.support = S := by
      ext q
      rw [Finsupp.mem_support_iff, factorization_radicalImparGrande]
      have hiff : q ∈ S ↔ z < q ∧ Odd (n.factorization q) :=
        ⟨fun h => (Finset.mem_filter.mp h).2,
         fun h => Finset.mem_filter.mpr ⟨mem_primeFactors_of_odd_factorization h.2, h⟩⟩
      by_cases h : z < q ∧ Odd (n.factorization q)
      · simp [h, hiff.mpr h]
      · simp [h, show q ∉ S from fun hm => h (hiff.mp hm)]
    rw [hsupp]
    have h1 : ∀ q ∈ S, (radicalImparGrande z n).factorization q = 1 := fun q hq => by
      rw [factorization_radicalImparGrande, if_pos (Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hsum_rad]
  have hS_eq : S = T.filter (fun p : ℕ => Odd (n.factorization p)) := by
    ext p; simp only [S, T, Finset.mem_filter, and_assoc]
  rw [hS_eq, Finset.card_filter]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases ho : Odd (n.factorization p)
  · rw [if_pos ho, ho.neg_one_pow]; norm_num
  · rw [if_neg ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]; norm_num

/-- Descomposición por clases radicales `k = r_z(n)` de la suma girada por `ξ_z`. -/
theorem suma_giroTruncado_eq_clases (z N : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, giroTruncado z n * c n
      = ∑ k ∈ Finset.Icc 1 N, liouville k * D_clase z N c k := by
  have hmaps : ∀ n ∈ Finset.Icc 1 N, radicalImparGrande z n ∈ Finset.Icc 1 N := fun n hn => by
    have hn_Icc := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨radicalImparGrande_pos z n,
      (radicalImparGrande_le z hn_Icc.1).trans hn_Icc.2⟩
  symm
  unfold D_clase
  calc ∑ k ∈ Finset.Icc 1 N,
        liouville k * ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande z n = k), c n
      = ∑ k ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => radicalImparGrande z n = k),
            giroTruncado z n * c n := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [giroTruncado_eq_liouville_radical, (Finset.mem_filter.mp hn).2]
    _ = ∑ n ∈ Finset.Icc 1 N, giroTruncado z n * c n :=
          Finset.sum_fiberwise_of_maps_to hmaps _

/-- **Obstáculo de Cauchy–Schwarz `(409)`:**
como `|λ(k)| = 1`, agrupar por clases `k = r_z(n)` fuerza la cota
`(∑_{n=1}^N ξ_z(n) c(n))² ≤ N · ∑_{k=1}^N D_z(k)²`. -/
theorem obstaculo_cauchy_paridad_409 (z N : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, giroTruncado z n * c n) ^ 2
      ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, (D_clase z N c k) ^ 2 := by
  rw [suma_giroTruncado_eq_clases]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) liouville (D_clase z N c)
  have hones : ∑ k ∈ Finset.Icc 1 N, (liouville k) ^ 2 = (N : ℝ) := by
    simp_rw [liouville_sq]
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rwa [hones] at hcs

/-! ### 5. Pares de primos grandes distintos `p ≠ r > z` y cancelación por columnas `(410)` -/

theorem radicalImparGrande_mul_primo_corto {z p b : ℕ} (hp : Nat.Prime p) (hb : Nat.Prime b)
    (hbz : b ≤ z) (hzp : z < p) :
    radicalImparGrande z (p * b) = p := by
  apply Nat.eq_of_factorization_eq (radicalImparGrande_pos z (p * b)).ne' hp.ne_zero
  intro q
  rw [factorization_radicalImparGrande, hp.factorization, Finsupp.single_apply,
    Nat.factorization_mul hp.ne_zero hb.ne_zero, Finsupp.add_apply,
    hp.factorization, hb.factorization, Finsupp.single_apply, Finsupp.single_apply]
  have hpb : p ≠ b := by omega
  by_cases hqp : p = q
  · subst hqp
    have hbp : b ≠ p := Ne.symm hpb
    simp [hzp, hbp]
  · simp only [hqp, ↓reduceIte, zero_add]
    by_cases hbq : b = q
    · subst hbq
      have hnot : ¬ z < b := not_lt.mpr hbz
      simp [hnot]
    · simp [hbq]

/-- **Estructura fuera de la diagonal `(410)`:**
para dos primos grandes distintos `p ≠ r > z` y un primo corto común `b ≤ z`:
1. `p b ≠ r b`;
2. `r_z(p b) = p` y `r_z(r b) = r`, luego `r_z(p b) ≠ r_z(r b)` (caen fuera de las fibras de `(408)`);
3. `μ(p b) · μ(r b) = +1` (los cofactores puramente primos no se cancelan entre sí). -/
theorem pares_primos_fuera_diagonal_410 {z b p r : ℕ} (hb : Nat.Prime b) (hp : Nat.Prime p)
    (hr : Nat.Prime r) (hbz : b ≤ z) (hzp : z < p) (hzr : z < r) (hpr : p ≠ r) :
    p * b ≠ r * b ∧
      radicalImparGrande z (p * b) = p ∧
      radicalImparGrande z (r * b) = r ∧
      radicalImparGrande z (p * b) ≠ radicalImparGrande z (r * b) ∧
      mu (p * b) * mu (r * b) = 1 := by
  have hne_mul : p * b ≠ r * b := fun h => hpr (Nat.mul_right_cancel hb.pos h)
  have hrad_p : radicalImparGrande z (p * b) = p :=
    radicalImparGrande_mul_primo_corto hp hb hbz hzp
  have hrad_r : radicalImparGrande z (r * b) = r :=
    radicalImparGrande_mul_primo_corto hr hb hbz hzr
  have hmu_pb : mu (p * b) = 1 := by
    have hcop : Nat.Coprime p b := (hp.coprime_iff_not_dvd).mpr fun h => by
      have := Nat.le_of_dvd hb.pos h; omega
    unfold mu
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hcop,
      ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime hb]
    norm_num
  have hmu_rb : mu (r * b) = 1 := by
    have hcop : Nat.Coprime r b := (hr.coprime_iff_not_dvd).mpr fun h => by
      have := Nat.le_of_dvd hb.pos h; omega
    unfold mu
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hcop,
      ArithmeticFunction.moebius_apply_prime hr,
      ArithmeticFunction.moebius_apply_prime hb]
    norm_num
  refine ⟨hne_mul, hrad_p, hrad_r, ?_, ?_⟩
  · rw [hrad_p, hrad_r]; exact hpr
  · rw [hmu_pb, hmu_rb]; norm_num

/-- **Identidad fuera de la diagonal `(410)`:**
la suma de productos sobre pares de primos distintos `p ≠ r` en `I_p` es exactamente
`(∑_{p ∈ I_p} w(p))² − ∑_{p ∈ I_p} w(p)²`. -/
theorem identidad_fuera_diagonal_410 (I_p : Finset ℕ) (w : ℕ → ℝ) :
    ∑ p ∈ I_p, ∑ r ∈ I_p.erase p, w p * w r
      = (∑ p ∈ I_p, w p) ^ 2 - ∑ p ∈ I_p, (w p) ^ 2 := by
  classical
  have hadd : ∀ p ∈ I_p,
      (∑ r ∈ I_p.erase p, w p * w r) + (w p) ^ 2 = ∑ r ∈ I_p, w p * w r := fun p hp => by
    have h := Finset.sum_erase_add I_p (fun r => w p * w r) hp
    rwa [← sq] at h
  have hsum := Finset.sum_congr rfl hadd
  rw [Finset.sum_add_distrib] at hsum
  have htot : ∑ p ∈ I_p, ∑ r ∈ I_p, w p * w r = (∑ p ∈ I_p, w p) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  linarith

/-- Función sumatoria de Möbius `M(n) = ∑_{d=1}^n μ(d)` (`M(0) = 0`). -/
noncomputable def M_moebius (n : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 n, mu d

theorem M_moebius_zero : M_moebius 0 = 0 := by simp [M_moebius]

theorem M_moebius_succ_sub (a : ℕ) : M_moebius (a + 1) - M_moebius a = mu (a + 1) := by
  unfold M_moebius
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ a + 1)]
  ring

/-- **Cota de Mertens general (Estado 45, `(5.1)`):**
bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`), para todo `δ > 0` con `θ + δ < 1` existe `K ≥ 0` tal que
`|M(n)| = |∑_{d=1}^n μ(d)| ≤ K n^{θ+δ}` para todo `n : ℕ`. -/
theorem M_moebius_bound_theta {θ δ : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ < 1)
    (hZ : SinCerosDerecha θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |M_moebius n| ≤ K * (n : ℝ) ^ (θ + δ) := by
  obtain ⟨C, hC⟩ := balazard_saias_theta hθ hδ hθδ one_pos hZ
  obtain ⟨CZ, hCZ0, hCZ⟩ := Zinv_bound_theta hθ hδ hθδ one_pos hZ
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl 2 (by norm_num; linarith)
    simp at h1; exact le_trans (norm_nonneg _) (by linarith)
  refine ⟨4 * (CZ + C), by positivity, fun n => ?_⟩
  set v : ℝ := θ + δ
  have hv0 : 0 < v := by simp only [v]; linarith
  have hv1 : v ≤ 1 := by simp only [v]; linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [M_moebius, Real.zero_rpow hv0.ne']
  set s₀ : ℂ := (v : ℂ)
  have hs₀re : s₀.re = θ + δ := by simp [s₀, v]
  have hs₀im : s₀.im = 0 := by simp [s₀]
  set M_bd : ℝ := CZ + C
  have hM0 : 0 ≤ M_bd := by positivity
  have hA : ∀ d : ℕ, ‖Dsum d s₀‖ ≤ M_bd := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Dsum, hM0]
    have h1 := hC d hd s₀ (by rw [hs₀re])
    rw [hs₀im] at h1; simp at h1
    change ‖Dsum d s₀ - Zinv s₀‖ ≤ _ at h1
    have h2 := hCZ s₀ (by rw [hs₀re])
    rw [hs₀im] at h2; simp at h2
    have h3 : (d : ℝ) ^ (-(δ / 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    have h3' : (d : ℝ) ^ (-δ / 3) ≤ 1 := by rwa [neg_div]
    calc ‖Dsum d s₀‖ ≤ ‖Dsum d s₀ - Zinv s₀‖ + ‖Zinv s₀‖ := norm_le_norm_sub_add _ _
      _ ≤ C * (d : ℝ) ^ (-δ / 3) + CZ := add_le_add h1 h2
      _ ≤ C * 1 + CZ := by gcongr
      _ = M_bd := by simp only [M_bd]; ring
  set g : ℕ → ℝ := fun d => (d : ℝ) ^ v
  have hginc : ∀ d : ℕ, g d ≤ g (d + 1) := fun d =>
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by push_cast; linarith) hv0.le
  have hM_eq_Dsum0 : ((M_moebius n : ℝ) : ℂ) = Dsum n 0 := by
    unfold M_moebius Dsum
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    simp
  have hterm : ∀ d ∈ Finset.Icc 1 n, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-(0 : ℂ))
      = (((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s₀)) * (g d : ℂ) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    simp only [g, s₀]
    rw [ofReal_cpow hd0.le, ofReal_natCast, mul_assoc, ← cpow_add _ _ (by exact_mod_cast hd0.ne')]
    congr 2; ring
  have hab : Dsum n 0
      = Dsum n s₀ * (g (n + 1) : ℂ)
        + ∑ d ∈ Finset.Icc 1 n, Dsum d s₀ * ((g d : ℂ) - g (d + 1)) := by
    unfold Dsum; rw [Finset.sum_congr rfl hterm, abel_Icc]
  have htel : ∑ d ∈ Finset.Icc 1 n, (g (d + 1) - g d) = g (n + 1) - 1 := by
    have := telescopio_Ioc (fun d => -g d) (n := 0) n
    rw [show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_add_one_left_eq_Ioc 0 n]
    simp only [zero_add] at this
    have hg1 : g 1 = 1 := by simp [g]
    rw [hg1] at this
    linarith [this, show ∑ d ∈ Finset.Ioc 0 n, (g (d + 1) - g d)
      = ∑ d ∈ Finset.Ioc 0 n, (-g d - -g (d + 1)) from Finset.sum_congr rfl fun d _ => by ring]
  have hgn : g (n + 1) ≤ 2 * (n : ℝ) ^ v := by
    simp only [g]
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith
    calc ((n + 1 : ℕ) : ℝ) ^ v ≤ (2 * (n : ℝ)) ^ v :=
          Real.rpow_le_rpow (by positivity) h2 hv0.le
      _ = 2 ^ v * (n : ℝ) ^ v := Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
      _ ≤ 2 ^ (1 : ℝ) * (n : ℝ) ^ v :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hv1) (by positivity)
      _ = 2 * (n : ℝ) ^ v := by rw [Real.rpow_one]
  have habs_eq : |M_moebius n| = ‖Dsum n 0‖ := by
    rw [← hM_eq_Dsum0, Complex.norm_real, Real.norm_eq_abs]
  rw [habs_eq, hab]
  calc ‖Dsum n s₀ * (g (n + 1) : ℂ)
        + ∑ d ∈ Finset.Icc 1 n, Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖
      ≤ ‖Dsum n s₀ * (g (n + 1) : ℂ)‖
        + ∑ d ∈ Finset.Icc 1 n, ‖Dsum d s₀ * ((g d : ℂ) - g (d + 1))‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ M_bd * g (n + 1) + ∑ d ∈ Finset.Icc 1 n, M_bd * (g (d + 1) - g d) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun d _ => ?_)
        · have hg0 : 0 ≤ g (n + 1) := by simp only [g]; positivity
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
          exact mul_le_mul_of_nonneg_right (hA n) hg0
        · have hgd : 0 ≤ g (d + 1) - g d := sub_nonneg.mpr (hginc d)
          have en : ‖(g d : ℂ) - g (d + 1)‖ = g (d + 1) - g d := by
            rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hgd]
          rw [norm_mul, en]
          exact mul_le_mul_of_nonneg_right (hA d) hgd
    _ = M_bd * g (n + 1) + M_bd * (g (n + 1) - 1) := by rw [← Finset.mul_sum, htel]
    _ ≤ 2 * M_bd * g (n + 1) := by linarith
    _ ≤ 2 * M_bd * (2 * (n : ℝ) ^ v) := by gcongr
    _ = 4 * (CZ + C) * (n : ℝ) ^ (θ + δ) := by simp only [M_bd, v]; ring

/-- Sumación de Abel por intervalos para `∑_{a=A}^B μ(a) w(a)` (`1 ≤ A ≤ B`). -/
theorem abel_intervalo_moebius (w : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ∀ k : ℕ, ∑ a ∈ Finset.Icc A (A + k), mu a * w a
      = M_moebius (A + k) * w (A + k + 1) - M_moebius (A - 1) * w A
        + ∑ a ∈ Finset.Icc A (A + k), M_moebius a * (w a - w (a + 1)) := by
  intro k
  induction k with
  | zero =>
    simp only [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton]
    have hA_eq : A - 1 + 1 = A := by omega
    have hstep := M_moebius_succ_sub (A - 1)
    rw [hA_eq] at hstep
    linarith [show M_moebius A * w (A + 1) - M_moebius (A - 1) * w A + M_moebius A * (w A - w (A + 1))
      = (M_moebius A - M_moebius (A - 1)) * w A by ring,
      congrArg (· * w A) hstep]
  | succ k ih =>
    have hle : A ≤ (A + k) + 1 := by omega
    rw [show A + (k + 1) = (A + k) + 1 by omega, Finset.sum_Icc_succ_top hle, ih,
      Finset.sum_Icc_succ_top hle]
    have hstep := M_moebius_succ_sub (A + k)
    have hring : M_moebius (A + k + 1) * w (A + k + 1 + 1) - M_moebius (A - 1) * w A
        + (∑ a ∈ Finset.Icc A (A + k), M_moebius a * (w a - w (a + 1))
            + M_moebius (A + k + 1) * (w (A + k + 1) - w (A + k + 1 + 1)))
        = (M_moebius (A + k) * w (A + k + 1) - M_moebius (A - 1) * w A
            + ∑ a ∈ Finset.Icc A (A + k), M_moebius a * (w a - w (a + 1)))
          + (M_moebius (A + k + 1) - M_moebius (A + k)) * w (A + k + 1) := by ring
    rw [hring, hstep]

/-- **Cancelación condicional por columnas al restituir cofactores compuestos (sección `(410)`):**
bajo `SinCerosDerecha θ` (`1/2 ≤ θ < 1`), al restituir todos los cofactores libres de cuadrados
`a ∈ [A, B]` (`1 ≤ A ≤ B`) contra un perfil suave `w(a)` en lugar de aislar únicamente primos
grandes `p ≠ r` del mismo signo, la columna completa `∑_{a=A}^B μ(a) w(a)` se cancela a orden
`B^{θ+δ}` multiplicado por la variación total de `w`. -/
theorem cancelacion_columna_moebius_theta {θ δ : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ)
    (hθδ : θ + δ < 1) (hZ : SinCerosDerecha θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : ℕ) (w : ℕ → ℝ), 1 ≤ A → A ≤ B →
      |∑ a ∈ Finset.Icc A B, mu a * w a|
        ≤ K * (B : ℝ) ^ (θ + δ)
          * (|w A| + |w (B + 1)| + ∑ a ∈ Finset.Icc A B, |w a - w (a + 1)|) := by
  obtain ⟨K, hK0, hK⟩ := M_moebius_bound_theta hθ hδ hθδ hZ
  refine ⟨K, hK0, fun A B w hA hAB => ?_⟩
  have hBk : B = A + (B - A) := by omega
  have hab := abel_intervalo_moebius w hA (B - A)
  rw [← hBk] at hab
  have hM_le : ∀ a : ℕ, a ≤ B → |M_moebius a| ≤ K * (B : ℝ) ^ (θ + δ) := fun a ha => by
    calc |M_moebius a| ≤ K * (a : ℝ) ^ (θ + δ) := hK a
      _ ≤ K * (B : ℝ) ^ (θ + δ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast ha) (by linarith)) hK0
  rw [hab]
  have htri1 := abs_add_le (M_moebius B * w (B + 1) - M_moebius (A - 1) * w A)
    (∑ a ∈ Finset.Icc A B, M_moebius a * (w a - w (a + 1)))
  have htri2 := abs_sub (M_moebius B * w (B + 1)) (M_moebius (A - 1) * w A)
  have hB_term : |M_moebius B * w (B + 1)| ≤ K * (B : ℝ) ^ (θ + δ) * |w (B + 1)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM_le B le_rfl) (abs_nonneg _)
  have hA_term : |M_moebius (A - 1) * w A| ≤ K * (B : ℝ) ^ (θ + δ) * |w A| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM_le (A - 1) (by omega)) (abs_nonneg _)
  have hsum_term : |∑ a ∈ Finset.Icc A B, M_moebius a * (w a - w (a + 1))|
      ≤ K * (B : ℝ) ^ (θ + δ) * ∑ a ∈ Finset.Icc A B, |w a - w (a + 1)| := by
    calc |∑ a ∈ Finset.Icc A B, M_moebius a * (w a - w (a + 1))|
        ≤ ∑ a ∈ Finset.Icc A B, |M_moebius a * (w a - w (a + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc A B, K * (B : ℝ) ^ (θ + δ) * |w a - w (a + 1)| := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hM_le a (Finset.mem_Icc.mp ha).2) (abs_nonneg _)
      _ = K * (B : ℝ) ^ (θ + δ) * ∑ a ∈ Finset.Icc A B, |w a - w (a + 1)| :=
          (Finset.mul_sum _ _ _).symm
  linarith

/-- Especialización a `RiemannHypothesis` (`θ = 1/2`): cancelación por columnas `O(B^{1/2+δ})`. -/
theorem cancelacion_columna_moebius_rh (hRH : RiemannHypothesis) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : ℕ) (w : ℕ → ℝ), 1 ≤ A → A ≤ B →
      |∑ a ∈ Finset.Icc A B, mu a * w a|
        ≤ K * (B : ℝ) ^ (1 / 2 + δ)
          * (|w A| + |w (B + 1)| + ∑ a ∈ Finset.Icc A B, |w a - w (a + 1)|) :=
  cancelacion_columna_moebius_theta le_rfl hδ (by linarith)
    (sinCerosDerecha_half_iff_rh.mpr hRH)

end AMate
