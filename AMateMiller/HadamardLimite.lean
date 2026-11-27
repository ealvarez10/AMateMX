import AMateMiller.HadamardVertical

/-!
# La cota de Hadamard para la suma sobre ceros

Para `χ` primitivo módulo `N > 1`, con GRH y `1 < σ < 3/2`:

  `∑_{|Im ρ| < T} m_ρ · 2(σ − 1/2)/((σ − 1/2)² + (Im ρ)²) ≤ Re (Λd(σ, χ) + Λd(σ, χ⁻¹))`

(`cota_hadamard`). Se pasa al límite en la identidad del rectángulo (`identidad_rect`) a lo largo
de alturas buenas `T'_k → ∞`: los lados horizontales tienden a `0` (`LogDerivHoriz` y las cotas de
`ψ`), el izquierdo se refleja sobre `Re s = 3/2` y allí la integral es `0`
(`integral_Λd_G_eq_zero`).
-/

open Complex MeasureTheory Filter Topology Set
open AMate.Miller.PI AMate.Miller.PI.EF AMate.Miller.PI.Digamma

noncomputable section

namespace AMate.Miller.Hadamard

set_option linter.unusedSectionVars false

/-- Las hipótesis analíticas de Alpöge que usa la cota de Hadamard. -/
structure HipHadamard : Prop where
  rc : RectCauchy
  zl : ZeroLocus
  zf : ZerosFinite
  rp : RegularPart
  refl : ReflexionLogDeriv
  dd : DigammaDerecha
  di : DigammaIzquierda
  alt : ∃ κ C : ℝ, 0 < κ ∧ GoodHeightExists κ ∧ LogDerivHoriz κ C

variable {N : ℕ} [NeZero N]

/-- Una altura buena no es ordenada de ningún cero. -/
theorem noOrdinate_of_good {χ : DirichletCharacter ℂ N} {κ T' : ℝ} (hκ : 0 < κ) (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') : NoOrdinate χ T' := by
  intro ρ h0 h1 hL heq
  have h := hg ρ h0 h1 hL
  rw [heq, sub_self, abs_zero] at h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hlog : 0 < Real.log (N * T') := Real.log_pos (by nlinarith)
  have : 0 < 1 / (κ * Real.log (N * T')) := by positivity
  linarith

/-- `|ψ(w)| ≤ (C₁ + C₂) log(|w| + 3) + 1` si `−1/4 ≤ Re w ≤ 5/4` y `|Im w| ≥ 1`. -/
theorem norm_digamma_tira {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hD : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C₁ * Real.log (‖z‖ + 2))
    (hI : ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C₂ * Real.log (‖w‖ + 2))
    {w : ℂ} (hw1 : -1 / 4 ≤ w.re) (him : 1 ≤ |w.im|) :
    ‖Complex.digamma w‖ ≤ (C₁ + C₂) * Real.log (‖w‖ + 3) + 1 := by
  have hl2 : Real.log (‖w‖ + 2) ≤ Real.log (‖w‖ + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg w])
  have hnw : 1 ≤ ‖w‖ := him.trans (Complex.abs_im_le_norm w)
  rcases le_or_gt w.re (1 / 4) with h | h
  · have := hI w h (Or.inl (by linarith))
    nlinarith
  rcases le_or_gt (1 / 2) w.re with h' | h'
  · have := hD w h'
    nlinarith
  · have hw0 : w ≠ 0 := by intro e; rw [e] at hnw; norm_num at hnw
    have e := digamma_add_inv (w := w) (by linarith) hw0
    have h1 := hD (w + 1) (by simp; linarith)
    have hn1 : ‖w + 1‖ ≤ ‖w‖ + 1 := by
      have := norm_add_le w 1; simpa using this
    have hl : Real.log (‖w + 1‖ + 2) ≤ Real.log (‖w‖ + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hinv : ‖1 / w‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by linarith)).mpr hnw
    have : Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by rw [← e]; ring
    rw [this]
    calc ‖Complex.digamma (w + 1) - 1 / w‖ ≤ ‖Complex.digamma (w + 1)‖ + ‖1 / w‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.log (‖w‖ + 3) + 1 := by
          have := mul_le_mul_of_nonneg_left hl hC₁.le
          linarith
      _ ≤ (C₁ + C₂) * Real.log (‖w‖ + 3) + 1 := by
          have : 0 ≤ C₂ * Real.log (‖w‖ + 3) :=
            mul_nonneg hC₂.le (Real.log_nonneg (by linarith [norm_nonneg w]))
          nlinarith

/-- `|G(x ± iT')| ≤ (2σ − 1)/T'²`. -/
theorem norm_G_horiz {σ : ℝ} (hσ1 : 1 < σ) {x y : ℝ} (hy : 0 < |y|) :
    ‖G σ ((x : ℂ) + y * I)‖ ≤ (2 * σ - 1) / |y| ^ 2 := by
  set s : ℂ := (x : ℂ) + y * I with hs
  have ha : |y| ≤ ‖s - ((1 - σ : ℝ) : ℂ)‖ := by
    have := Complex.abs_im_le_norm (s - ((1 - σ : ℝ) : ℂ)); simpa [hs] using this
  have hb : |y| ≤ ‖s - (σ : ℂ)‖ := by
    have := Complex.abs_im_le_norm (s - (σ : ℂ)); simpa [hs] using this
  have hpa : 0 < ‖s - ((1 - σ : ℝ) : ℂ)‖ := lt_of_lt_of_le hy ha
  have hpb : 0 < ‖s - (σ : ℂ)‖ := lt_of_lt_of_le hy hb
  have hG : G σ s = (((1 - σ : ℝ) : ℂ) - σ) / ((s - ((1 - σ : ℝ) : ℂ)) * (s - σ)) := by
    unfold G
    have a : s - ((1 - σ : ℝ) : ℂ) ≠ 0 := norm_pos_iff.mp hpa
    have b : s - (σ : ℂ) ≠ 0 := norm_pos_iff.mp hpb
    field_simp
    ring
  rw [hG, norm_div, norm_mul]
  have hnum : ‖((1 - σ : ℝ) : ℂ) - σ‖ = 2 * σ - 1 := by
    rw [show ((1 - σ : ℝ) : ℂ) - σ = ((1 - 2 * σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  rw [hnum]
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  rw [sq]
  exact mul_le_mul ha hb hy.le hpa.le

/-- Cota de `Λd·G` en los lados horizontales de una altura buena. -/
theorem norm_F_horiz {C₁ C₂ κ Ch : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hD : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C₁ * Real.log (‖z‖ + 2))
    (hI : ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C₂ * Real.log (‖w‖ + 2))
    (hLD : LogDerivHoriz κ Ch) {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {σ : ℝ}
    (hσ1 : 1 < σ) {T' : ℝ} (hT' : 2 ≤ T') (hg : GoodHeight χ κ T') {x : ℝ}
    (hx : x ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2)) {y : ℝ} (hy : y = T' ∨ y = -T') :
    ‖Λd χ ((x : ℂ) + y * I) * G σ ((x : ℂ) + y * I)‖ ≤
      (|Real.log (N / Real.pi)| / 2 + ((C₁ + C₂) * Real.log (T' + 5) + 1) / 2 +
        Ch * Real.log (N * T') ^ 2) * ((2 * σ - 1) / T' ^ 2) := by
  have hyabs : |y| = T' := by
    rcases hy with rfl | rfl
    · exact abs_of_pos (by linarith)
    · rw [abs_neg]; exact abs_of_pos (by linarith)
  have hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I)‖ ≤
      Ch * Real.log (N * T') ^ 2 := by
    obtain ⟨h1, h2⟩ := hLD N χ hp T' hT' hg x hx.1 (by linarith [hx.2])
    rcases hy with rfl | rfl
    · exact h1
    · exact h2
  have hpar := par_re_nonneg χ
  set w : ℂ := ((x : ℂ) + y * I + par χ) / 2 with hw
  have hwre : -1 / 4 ≤ w.re := by
    simp only [hw, Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith [hx.1]
  have hwim : 1 ≤ |w.im| := by
    have : w.im = y / 2 := by
      simp [hw, hpar.2.2]
    rw [this, abs_div, hyabs, abs_two]
    linarith
  have hpsi := norm_digamma_tira hC₁ hC₂ hD hI hwre hwim
  have hnw : ‖w‖ ≤ T' + 2 := by
    have hp1 : ‖par χ‖ ≤ 1 := by
      rcases par_spec χ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
    have h1 : ‖(x : ℂ) + y * I‖ ≤ |x| + |y| := by
      have := norm_add_le (x : ℂ) (y * I)
      simpa [Complex.norm_real] using this
    have hxabs : |x| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    rw [hw, norm_div, Complex.norm_ofNat]
    have := norm_add_le ((x : ℂ) + y * I) (par χ)
    linarith
  have hlw : Real.log (‖w‖ + 3) ≤ Real.log (T' + 5) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpsi' : ‖Complex.digamma w‖ ≤ (C₁ + C₂) * Real.log (T' + 5) + 1 := by
    have := mul_le_mul_of_nonneg_left hlw (by linarith : (0 : ℝ) ≤ C₁ + C₂)
    linarith
  have hΛ : ‖Λd χ ((x : ℂ) + y * I)‖ ≤ |Real.log (N / Real.pi)| / 2 +
      ((C₁ + C₂) * Real.log (T' + 5) + 1) / 2 + Ch * Real.log (N * T') ^ 2 := by
    unfold Λd
    calc _ ≤ ‖((Real.log (N / Real.pi) / 2 : ℝ) : ℂ)‖ + ‖Complex.digamma w / 2‖ +
          ‖logDeriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I)‖ := norm_add₃_le
      _ ≤ _ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two, norm_div, Complex.norm_ofNat]
          linarith
  have hGb := norm_G_horiz (x := x) (y := y) hσ1 (by rw [hyabs]; linarith)
  rw [hyabs] at hGb
  rw [norm_mul]
  exact mul_le_mul hΛ hGb (norm_nonneg _) (by
    have : 0 ≤ Ch * Real.log (N * T') ^ 2 := le_trans (norm_nonneg _) hL
    have : 0 ≤ (C₁ + C₂) * Real.log (T' + 5) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ T' + 5 by linarith)
      nlinarith
    positivity)

/-- `G(1 − s) = G(s)`. -/
theorem G_uno_menos (σ : ℝ) (s : ℂ) : G σ (1 - s) = G σ s := by
  unfold G
  have h1 : 1 - s - ((1 - σ : ℝ) : ℂ) = -(s - σ) := by push_cast; ring
  have h2 : 1 - s - (σ : ℂ) = -(s - ((1 - σ : ℝ) : ℂ)) := by push_cast; ring
  rw [h1, h2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

/-- **Lado izquierdo reflejado**: `F(−1/2 + iy) = −F⁻(3/2 − iy)` con `F = Λd·G`. -/
theorem lado_izquierdo (hR : ReflexionLogDeriv) (hZL : ZeroLocus)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (σ y : ℝ) :
    Λd χ (((-1 / 2 : ℝ) : ℂ) + y * I) * G σ (((-1 / 2 : ℝ) : ℂ) + y * I) =
      -(Λd χ⁻¹ (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) *
        G σ (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
  have hpar := par_re_nonneg χ
  have e1 : 1 - s = ((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hsre : s.re = -1 / 2 := by simp [hs]
  have c1 : ∀ n : ℕ, (s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.add_re, hsre, Complex.neg_re,
      Complex.natCast_re] at hre
    rcases par_spec χ with ⟨-, h0⟩ | ⟨-, h1⟩
    · rw [h0] at hre; simp at hre
      rcases n with _ | n
      · norm_num at hre
      · push_cast at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rw [h1] at hre; simp at hre; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have c2 : ∀ n : ℕ, (1 - s + par χ) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.sub_re, Complex.one_re, hsre,
      Complex.neg_re, Complex.natCast_re] at hre
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hpar.1]
  have c3 : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro hL
    have hne1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
    rcases hZL N χ hp s (by rw [hsre]; norm_num) hne1 hL with h | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hsre] at h; linarith [h.1]
    · have := congrArg Complex.re h; rw [hsre] at this; simp at this
    · have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have c4 : DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 :=
    L_sigma_ne' χ⁻¹ (by rw [e1]; simp; norm_num)
  rw [reflexion_gen hR hp c1 c2 c3 c4, ← G_uno_menos σ s, e1]
  ring

/-- Descomposición de `∮ Λd·G` con el lado izquierdo reflejado. -/
theorem rectInt_descomp (hR : ReflexionLogDeriv) (hZL : ZeroLocus) (hD : DigammaDerecha)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {σ : ℝ} (hσ1 : 1 < σ)
    (hσ2 : σ < 3 / 2) (T : ℝ) :
    rectInt (fun s => Λd χ s * G σ s) (-1 / 2) (3 / 2) (-T) T =
      (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), Λd χ (x + (-T : ℝ) * I) * G σ (x + (-T : ℝ) * I)) -
        (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), Λd χ (x + T * I) * G σ (x + T * I)) +
        I • ∫ y : ℝ in (-T)..T, (Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) +
          Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I)) := by
  have hi1 := (integrable_Λd_G hD (χ := χ) hσ1 hσ2).intervalIntegrable (a := -T) (b := T)
  have hi2 := (integrable_Λd_G hD (χ := χ⁻¹) hσ1 hσ2).intervalIntegrable (a := -T) (b := T)
  have hleft : ∫ y : ℝ in (-T)..T, Λd χ (((-1 / 2 : ℝ) : ℂ) + y * I) * G σ (((-1 / 2 : ℝ) : ℂ) + y * I) =
      -∫ y : ℝ in (-T)..T, Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) := by
    simp_rw [lado_izquierdo hR hZL hp σ]
    rw [intervalIntegral.integral_neg]
    congr 1
    have := intervalIntegral.integral_comp_neg (a := -T) (b := T)
      (fun y : ℝ => Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I))
    simp only [neg_neg] at this
    rw [← this]
  unfold rectInt
  rw [hleft, intervalIntegral.integral_add hi1 hi2]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- `log(N T)² ≤ 4 N T`. -/
theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := log_le_two_sqrt (show (0 : ℝ) ≤ x by linarith)
  have h0 := Real.log_nonneg hx
  have : Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (by linarith)] at this
  linarith

/-- **Cota de Hadamard.** -/
theorem cota_hadamard (h : HipHadamard) (hG : GRHPrimitivo)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3 / 2)
    {T : ℝ} (hfin : (ZerosBelow χ T).Finite) :
    ∑ ρ ∈ hfin.toFinset, (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) ≤
      (Λd χ σ + Λd χ⁻¹ σ + del1 χ * (2 / σ + 2 / (σ - 1))).re := by
  obtain ⟨κ, Ch, hκ, hGHE, hLDH⟩ := h.alt
  obtain ⟨C₁, hC₁, hD⟩ := id h.dd
  obtain ⟨C₂, hC₂, hI⟩ := id h.di
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  -- alturas buenas
  have hgood : ∀ k : ℕ, ∃ T' : ℝ, (k : ℝ) + 2 ≤ T' ∧ T' ≤ (k : ℝ) + 2 + 1 ∧ GoodHeight χ κ T' :=
    fun k => hGHE N χ hp ((k : ℝ) + 2) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  choose Tk hTk1 hTk2 hTkg using hgood
  have hTk2' : ∀ k, 2 ≤ Tk k := fun k => by linarith [hTk1 k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hTk0 : ∀ k, 0 < Tk k := fun k => by linarith [hTk2' k]
  have hno : ∀ k, NoOrdinate χ (Tk k) := fun k => noOrdinate_of_good hκ (hTk2' k) (hTkg k)
  have hreg : ∀ k, ∃ H₀ : ℂ → ℂ, IsRegPart χ (3 / 2) (Tk k) H₀ := fun k =>
    h.rp N χ hp (3 / 2) (Tk k) (by norm_num) (hTk0 k) (hno k)
  choose H₀ hH₀ using hreg
  have hfk : ∀ k, (ZerosBelow χ (Tk k)).Finite := fun k => h.zf N χ hp (Tk k)
  set V : ℂ := Λd χ σ + Λd χ⁻¹ σ + del1 χ * (2 / σ + 2 / (σ - 1)) with hV
  set R : ℕ → ℂ := fun k => rectInt (fun s => Λd χ s * G σ s) (-1 / 2) (3 / 2) (-Tk k) (Tk k)
    with hRdef
  have hid : ∀ k, ∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ)) =
      V + R k / (2 * Real.pi * I) := fun k => by
    rw [identidad_rect h.rc h.zl h.refl hp (hTk0 k) (hno k) (hH₀ k) (hfk k) hσ1 hσ2, hV]
    ring
  -- `R k → 0`
  have hTk_top : Tendsto Tk atTop atTop :=
    tendsto_atTop_mono (fun k => hTk1 k)
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set A : ℝ := |Real.log (N / Real.pi)| / 2 + (4 * (C₁ + C₂) + 1) / 2 with hA
  set B : ℝ := (C₁ + C₂) / 2 + 4 * N * max Ch 0 with hB
  have hM : ∀ T' : ℝ, 2 ≤ T' →
      |Real.log (N / Real.pi)| / 2 + ((C₁ + C₂) * Real.log (T' + 5) + 1) / 2 +
        Ch * Real.log (N * T') ^ 2 ≤ A + B * T' := by
    intro T' hT'
    have h1 : Real.log (T' + 5) ≤ T' + 4 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < T' + 5 by linarith); linarith
    have h2 : Real.log (N * T') ^ 2 ≤ 4 * (N * T') := log_sq_le (by nlinarith)
    have h3 : Ch * Real.log (N * T') ^ 2 ≤ max Ch 0 * (4 * (N * T')) := by
      calc Ch * Real.log (N * T') ^ 2 ≤ max Ch 0 * Real.log (N * T') ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
        _ ≤ max Ch 0 * (4 * (N * T')) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have h4 : (C₁ + C₂) * Real.log (T' + 5) ≤ (C₁ + C₂) * (T' + 4) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [hA, hB]
    nlinarith
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; have := le_max_right Ch 0; positivity
  have hhor : ∀ k : ℕ, ∀ y : ℝ, (y = Tk k ∨ y = -Tk k) →
      ‖∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), Λd χ (x + y * I) * G σ (x + y * I)‖ ≤
        2 * ((A + B) * (2 * σ - 1)) / Tk k := by
    intro k y hy
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1 / 2) (b := 3 / 2)
      (C := (A + B * Tk k) * ((2 * σ - 1) / Tk k ^ 2)) (f := fun x : ℝ =>
        Λd χ (x + y * I) * G σ (x + y * I)) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        refine (norm_F_horiz hC₁ hC₂ hD hI hLDH hp hσ1 (hTk2' k) (hTkg k)
          ⟨hx.1.le, hx.2⟩ hy).trans ?_
        exact mul_le_mul_of_nonneg_right (hM (Tk k) (hTk2' k)) (by
          have : 0 < 2 * σ - 1 := by linarith
          positivity))
    rw [show |(3 / 2 : ℝ) - -1 / 2| = 2 by norm_num] at hb
    have hT := hTk2' k
    have hT0 := hTk0 k
    have h2σ : 0 < 2 * σ - 1 := by linarith
    have : (A + B * Tk k) * ((2 * σ - 1) / Tk k ^ 2) ≤ (A + B) * (2 * σ - 1) / Tk k := by
      have hle : A + B * Tk k ≤ (A + B) * Tk k := by nlinarith
      calc (A + B * Tk k) * ((2 * σ - 1) / Tk k ^ 2)
          ≤ ((A + B) * Tk k) * ((2 * σ - 1) / Tk k ^ 2) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (A + B) * (2 * σ - 1) / Tk k := by field_simp
    have e : 2 * ((A + B) * (2 * σ - 1)) / Tk k = (A + B) * (2 * σ - 1) / Tk k * 2 := by ring
    rw [e]
    linarith
  have hdec : Tendsto (fun k => 2 * ((A + B) * (2 * σ - 1)) / Tk k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hTk_top
  have hbot : Tendsto (fun k => ∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
      Λd χ (x + ((-Tk k : ℝ) : ℂ) * I) * G σ (x + ((-Tk k : ℝ) : ℂ) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hhor k (-Tk k) (Or.inr rfl)) hdec
  have htop : Tendsto (fun k => ∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
      Λd χ (x + (Tk k : ℂ) * I) * G σ (x + (Tk k : ℂ) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hhor k (Tk k) (Or.inl rfl)) hdec
  have hvert : Tendsto (fun k => ∫ y : ℝ in (-Tk k)..(Tk k),
      (Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) +
        Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I))) atTop (𝓝 0) := by
    have hi1 := integrable_Λd_G h.dd (χ := χ) hσ1 hσ2
    have hi2 := integrable_Λd_G h.dd (χ := χ⁻¹) hσ1 hσ2
    have h0 : ∫ y : ℝ, (Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) +
        Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I)) = 0 := by
      rw [integral_add hi1 hi2, integral_Λd_G_eq_zero h.dd (χ := χ) hσ1 hσ2,
        integral_Λd_G_eq_zero h.dd (χ := χ⁻¹) hσ1 hσ2, add_zero]
    have := intervalIntegral_tendsto_integral (hi1.add hi2) (tendsto_neg_atTop_atBot.comp hTk_top)
      hTk_top
    simp only [Pi.add_apply, Function.comp_apply] at this
    rw [h0] at this
    exact this
  have hR0 : Tendsto R atTop (𝓝 0) := by
    have e : R = fun k => (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
        Λd χ (x + ((-Tk k : ℝ) : ℂ) * I) * G σ (x + ((-Tk k : ℝ) : ℂ) * I)) -
        (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), Λd χ (x + (Tk k : ℂ) * I) * G σ (x + (Tk k : ℂ) * I)) +
        I • ∫ y : ℝ in (-Tk k)..(Tk k), (Λd χ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I) +
          Λd χ⁻¹ ((3 / 2 : ℝ) + y * I) * G σ ((3 / 2 : ℝ) + y * I)) := by
      funext k
      exact rectInt_descomp h.refl h.zl h.dd hp hσ1 hσ2 (Tk k)
    rw [e]
    have := (hbot.sub htop).add (hvert.const_smul I)
    simpa using this
  -- la suma converge a `V`
  have hS : Tendsto (fun k => ∑ ρ ∈ (hfk k).toFinset,
      (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ))) atTop (𝓝 V) := by
    have := (hR0.div_const (2 * Real.pi * I)).const_add V
    simp only [zero_div, add_zero] at this
    exact this.congr fun k => (hid k).symm
  have hSre := (Complex.continuous_re.tendsto V).comp hS
  -- los términos son reales y no negativos
  have hterm : ∀ (T' : ℝ) (ρ : ℂ), ρ ∈ ZerosBelow χ T' →
      ((mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ))).re =
        (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
    intro T' ρ hρ
    have hre := re_eq_half_de_mem hG hp hρ
    set a : ℝ := σ - 1 / 2 with ha
    set γ : ℝ := ρ.im with hγ
    have hρ' : ρ = (1 / 2 : ℂ) + (γ : ℂ) * I := by
      rw [← Complex.re_add_im ρ, hre]; push_cast; ring
    have hpos : 0 < a ^ 2 + γ ^ 2 := by
      have : 0 < a := by rw [ha]; linarith
      positivity
    have key : (1 / ((σ : ℂ) - ρ) - 1 / (((1 - σ : ℝ) : ℂ) - ρ)) =
        ((2 * a / (a ^ 2 + γ ^ 2) : ℝ) : ℂ) := by
      have z1 : (σ : ℂ) - ρ = (a : ℂ) - (γ : ℂ) * I := by rw [hρ', ha]; push_cast; ring
      have z2 : ((1 - σ : ℝ) : ℂ) - ρ = -((a : ℂ) + (γ : ℂ) * I) := by rw [hρ', ha]; push_cast; ring
      have hz1 : (a : ℂ) - (γ : ℂ) * I ≠ 0 := by
        intro e; have := congrArg Complex.re e; simp at this; rw [ha] at this; linarith
      have hz2 : (a : ℂ) + (γ : ℂ) * I ≠ 0 := by
        intro e; have := congrArg Complex.re e; simp at this; rw [ha] at this; linarith
      have hprod : ((a : ℂ) - (γ : ℂ) * I) * ((a : ℂ) + (γ : ℂ) * I) = ((a ^ 2 + γ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [z1, z2, one_div_neg_eq_neg_one_div, sub_neg_eq_add, div_add_div _ _ hz1 hz2, hprod]
      rw [show (1 : ℂ) * ((a : ℂ) + (γ : ℂ) * I) + ((a : ℂ) - (γ : ℂ) * I) * 1 = ((2 * a : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_div]
    rw [key, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hre_sum : ∀ k, (∑ ρ ∈ (hfk k).toFinset,
      (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ))).re =
      ∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
    intro k
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [Set.Finite.mem_toFinset] at hρ
    exact hterm (Tk k) ρ hρ
  have hnn : ∀ ρ : ℂ, 0 ≤ (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
    intro ρ
    have : 0 < σ - 1 / 2 := by linarith
    positivity
  -- comparación con `ZerosBelow χ T`
  have hev : ∀ᶠ k in atTop, ∑ ρ ∈ hfin.toFinset,
      (mult χ ρ : ℝ) * (2 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) ≤
      (∑ ρ ∈ (hfk k).toFinset, (mult χ ρ : ℂ) * (1 / (σ - ρ) - 1 / ((1 - σ : ℝ) - ρ))).re := by
    filter_upwards [hTk_top.eventually_ge_atTop T] with k hk
    rw [hre_sum k]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ _ _ => hnn ρ
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, lt_of_lt_of_le hρ.2.2.1 hk, hρ.2.2.2⟩
  exact ge_of_tendsto hSre hev

end AMate.Miller.Hadamard
