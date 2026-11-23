import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import AMateEnergia.EquivalenciaVentanas

/-!
# Ruta A: motor algebraico y de proyección en anfitriones finitos para conductor 1

Formalización original en Lean 4 (solo Mathlib, cero `sorry`) de la espina dorsal algebraica y de
escalas con la que el método de anfitriones / levantamientos theta de Alpöge (2026), especializado
al carácter trivial (`N = 1, χ = 1`, función `ζ(s)` de Riemann), esquiva la barrera de paridad
`(407)`–`(410)` sin elevar al cuadrado la suma sobre primos:

1. **Ortogonalidad lineal en subgrupos de `GrupoBaseDos × H` (`ortogonalidad_subgrupo_anfitrion`,
   `proyeccion_lineal_anfitrion`):**
   promediando el funcional explícito torcido sobre el subgrupo `(0, A₀) ≤ (ℤ/2ℤ × ℤ/2ℤ) × H` se
   anulan todos los caracteres aditivos no triviales sobre `A₀` mediante cancelación exacta de
   grupo abeliano finito (`AddChar.sum_eq_zero_iff_ne_zero`), conservando intacto el signo
   unilateral de la desigualdad superior.
2. **Dicotomía multiplicativa trivial / cuadrático auxiliar (`dicotomia_cuadratica_anfitrion`) y
   aislamiento limpio en conductor 1 (`aislamiento_unilateral_conductor_uno`):**
   sobre `(ℤˣ × ℤˣ) × M`, fijar la paridad arquimediana impar y anular el núcleo `M` deja
   exactamente dos caracteres: el trivial `1` (que lee `G_vonMangoldt y`) y el carácter cuadrático
   auxiliar `caracterCuadraticoAux`. Como en conductor 1 no existe carácter cuadrático retenido en
   el nivel (`psK = none`), toda contribución con `ψ ≠ 0` pasa al término complementario acotado
   `B_sig`, entregando punto a punto la desigualdad unilateral
   `G_vonMangoldt y ≤ B_top / b + B_sig`.
3. **Interfaz exacta de los 4 pilares en exponente `λ = 3/2` (`MotorArithConductorUno`) y cierre
   bilateral (`rh_de_motor_conductor_uno`, `energia_de_motor_conductor_uno`,
   `rh_iff_motor_conductor_uno`):**
   encapsula exactamente el suministro de ventanas conectadas producido por
   `RowSrc` + `RecTExists` + `VwinOfRow` + `EveryCharacterOfLiteratureOfVWin` para `ζ(s)` y
   demuestra en Lean que implica `(V)`, `RiemannHypothesis` y `E_Q ≤ C_ε Q^ε`, siendo además
   lógicamente equivalente a `RiemannHypothesis`.
-/

open Complex MeasureTheory Set Filter Metric Topology

namespace AMate

/-! ### 1. Grupo anfitrión `(ℤ/2ℤ × ℤ/2ℤ) × H` y proyección lineal por ortogonalidad -/

/-- Factor de paridad base `E₀ = (ℤ/2ℤ) × (ℤ/2ℤ)` de los grupos anfitriones `E₀ × H`. -/
abbrev GrupoBaseDos : Type := ZMod 2 × ZMod 2

/-- Incrustación desplazada en la componente impar `((1, 0), h) ∈ E₀ × H`. -/
def traslacionImpar {H : Type*} (h : H) : GrupoBaseDos × H := ((1, 0), h)

theorem neg_uno_zmod_dos : -(1 : ZMod 2) = (1 : ZMod 2) := by decide

theorem descomposicion_neg_traslacionImpar {H : Type*} [AddCommGroup H] (s u t : H) :
    -(traslacionImpar (s + u - t)) = traslacionImpar t + (0, -s) + (0, -u) := by
  ext
  ·change -(1 : ZMod 2) = (1 : ZMod 2) + 0 + 0
   decide
  ·change -(0 : ZMod 2) = (0 : ZMod 2) + 0 + 0
   decide
  ·change -(s + u - t) = t + -s + -u
   abel

/-- Subconjunto de caracteres en `Ψ` que se anulan (valen `1`) sobre el subgrupo `(0, A₀)`. -/
noncomputable def subconjuntoAnulador {H : Type*} [AddCommGroup H]
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ)) (A0 : AddSubgroup H) :
    Finset (AddChar (GrupoBaseDos × H) ℂ) := by
  classical
  exact Ψ.filter fun ψ => ∀ v ∈ A0, ψ (0, v) = 1

@[simp]
theorem mem_subconjuntoAnulador {H : Type*} [AddCommGroup H]
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ)) (A0 : AddSubgroup H)
    (ψ : AddChar (GrupoBaseDos × H) ℂ) :
    ψ ∈ subconjuntoAnulador Ψ A0 ↔ ψ ∈ Ψ ∧ ∀ v ∈ A0, ψ (0, v) = 1 := by
  classical
  simp [subconjuntoAnulador]

open Classical in
/-- **Ortogonalidad en el subgrupo `A₀ ≤ H`:**
promediar `ψ(−traslacionImpar(s + u − t))` sobre `u ∈ A₀` conserva `|A₀| · ψ(traslacionImpar t)`
si `ψ` es trivial en `(0, A₀)` y anula exactamente todos los demás caracteres. -/
theorem ortogonalidad_subgrupo_anfitrion {H : Type*} [AddCommGroup H]
    (A0 : AddSubgroup H) [Fintype A0] (ψ : AddChar (GrupoBaseDos × H) ℂ)
    (s t : H) (hs : s ∈ A0) :
    (∑ u : A0, ψ (-(traslacionImpar (s + (u : H) - t))))
      = if ∀ v ∈ A0, ψ (0, v) = 1 then (Fintype.card A0 : ℂ) * ψ (traslacionImpar t) else 0 := by
  classical
  simp_rw [descomposicion_neg_traslacionImpar, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  by_cases htriv : ∀ v ∈ A0, ψ (0, v) = 1
  · rw [if_pos htriv, htriv (-s) (A0.neg_mem hs), mul_one]
    have hones : ∑ u : A0, ψ (0, -(u : H)) = (Fintype.card A0 : ℂ) := by
      have hcongr : ∀ u : A0, ψ (0, -(u : H)) = 1 := fun u => htriv _ (A0.neg_mem u.2)
      rw [Finset.sum_congr rfl fun u _ => hcongr u, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    rw [hones, mul_comm]
  · rw [if_neg htriv]
    let φ : AddChar A0 ℂ := ψ.compAddMonoidHom ((AddMonoidHom.inr GrupoBaseDos H).comp A0.subtype)
    have hφ_apply : ∀ u : A0, φ u = ψ (0, (u : H)) := fun _ => rfl
    have hφ_ne : φ ≠ 0 := by
      rw [AddChar.ne_zero_iff]
      push Not at htriv
      rcases htriv with ⟨v, hv, hne1⟩
      exact ⟨⟨v, hv⟩, hne1⟩
    have hsum_neg : ∑ u : A0, ψ (0, -(u : H)) = ∑ u : A0, φ u := by
      rw [← Equiv.sum_comp (Equiv.neg A0) φ]
      rfl
    rw [hsum_neg, AddChar.sum_eq_zero_iff_ne_zero.mpr hφ_ne, mul_zero]

/-- Funcional explícito torcido sobre un conjunto finito `Ψ` de caracteres de `E₀ × H` y una
ventana fina de clases `T₂ ⊆ A₀`. -/
noncomputable def funcionalExplicitoTorcido {H : Type*} [AddCommGroup H]
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ)) (T2 : Finset H) (b : ℝ)
    (perfil : AddChar (GrupoBaseDos × H) ℂ → ℝ → ℂ) (y : ℝ) (u0 t : H) : ℂ :=
  ∑ s ∈ T2, ∑ ψ ∈ Ψ,
    ψ (-(traslacionImpar (s + u0 - t))) * ((b : ℂ) * perfil ψ y)

/-- **Proyección lineal sin elevar al cuadrado (`sum_Th` abstracto):**
al sumar `funcionalExplicitoTorcido` sobre `u₀ ∈ A₀`, desaparecen todos los caracteres de `Ψ` no
triviales en `(0, A₀)` y sobrevive únicamente `subconjuntoAnulador Ψ A₀`. -/
theorem proyeccion_lineal_anfitrion {H : Type*} [AddCommGroup H]
    (A0 : AddSubgroup H) [Fintype A0]
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ)) (T2 : Finset H)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (b : ℝ)
    (perfil : AddChar (GrupoBaseDos × H) ℂ → ℝ → ℂ) (y : ℝ) (t : H) :
    (∑ u0 : A0, funcionalExplicitoTorcido Ψ T2 b perfil y (u0 : H) t)
      = ((Fintype.card A0 * T2.card : ℕ) : ℂ) * (b : ℂ) *
          ∑ ψ ∈ subconjuntoAnulador Ψ A0, ψ (traslacionImpar t) * perfil ψ y := by
  classical
  unfold funcionalExplicitoTorcido
  rw [Finset.sum_comm]
  have hinner : ∀ s ∈ T2,
      (∑ u0 : A0, ∑ ψ ∈ Ψ, ψ (-(traslacionImpar (s + (u0 : H) - t))) * ((b : ℂ) * perfil ψ y))
        = (Fintype.card A0 : ℂ) * (b : ℂ) *
            ∑ ψ ∈ subconjuntoAnulador Ψ A0, ψ (traslacionImpar t) * perfil ψ y := by
    intro s hs
    rw [Finset.sum_comm]
    have hψ_eq : ∀ ψ ∈ Ψ,
        (∑ u0 : A0, ψ (-(traslacionImpar (s + (u0 : H) - t))) * ((b : ℂ) * perfil ψ y))
          = if ∀ v ∈ A0, ψ (0, v) = 1 then
              (Fintype.card A0 : ℂ) * (b : ℂ) * (ψ (traslacionImpar t) * perfil ψ y)
            else 0 := by
      intro ψ _
      rw [← Finset.sum_mul, ortogonalidad_subgrupo_anfitrion A0 ψ s t (hT2 s hs)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hψ_eq, ← Finset.sum_filter, Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-! ### 2. Dicotomía trivial / cuadrático auxiliar y aislamiento en conductor 1 -/

/-- Grupo multiplicativo abstracto del marco anfitrión: `(ℤˣ × ℤˣ) × M`. -/
abbrev GrupoMarco (M : Type*) := (ℤˣ × ℤˣ) × M

def elementoSigno {M : Type*} [One M] : GrupoMarco M := ((-1, 1), 1)

def elementoImparArquimediano {M : Type*} [One M] : GrupoMarco M := ((1, -1), 1)

def incrustacionNucleo {M : Type*} (m : M) : GrupoMarco M := ((1, 1), m)

/-- Carácter cuadrático auxiliar que lee el signo de la primera componente `a ∈ ℤˣ`. -/
def caracterCuadraticoAux {M : Type*} [Monoid M] : GrupoMarco M →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp
    ((MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst (ℤˣ × ℤˣ) M))

@[simp]
theorem val_caracterCuadraticoAux {M : Type*} [Monoid M] (a b : ℤˣ) (m : M) :
    ((caracterCuadraticoAux ((a, b), m) : ℂˣ) : ℂ) = ((a : ℤ) : ℂ) := rfl

/-- **Dicotomía trivial / cuadrático auxiliar (`gmA_eq_triv` abstracto):**
en `(ℤˣ × ℤˣ) × M`, entre los caracteres multiplicativos con paridad arquimediana
`θ(elementoImparArquimediano) = 1`, los que se anulan en todo `incrustacionNucleo m` son
exactamente `1` y `caracterCuadraticoAux`. -/
theorem dicotomia_cuadratica_anfitrion {M : Type*} [Monoid M] (θ : GrupoMarco M →* ℂˣ)
    (h_impar : θ elementoImparArquimediano = 1) :
    (∀ m : M, θ (incrustacionNucleo m) = 1) ↔ (θ = 1 ∨ θ = caracterCuadraticoAux) := by
  constructor
  · intro hM
    have hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1 := by
      intro b
      rcases Int.units_eq_one_or b with rfl | rfl
      · exact map_one θ
      · exact h_impar
    have hfact : ∀ (a b : ℤˣ) (m : M), θ ((a, b), m) = θ ((a, 1), 1) := by
      intro a b m
      have heq : (((a, b), m) : GrupoMarco M)
          = ((a, 1), 1) * ((1, b), 1) * incrustacionNucleo m := by
        simp [incrustacionNucleo]
      rw [heq, map_mul, map_mul, hB b, hM m, mul_one, mul_one]
    have hsq : ((θ elementoSigno : ℂˣ) : ℂ) * ((θ elementoSigno : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have heq : (elementoSigno : GrupoMarco M) * elementoSigno = 1 := by
        simp [elementoSigno]
      rw [heq, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with hpos | hneg
    · left
      ext ⟨⟨a, b⟩, m⟩
      rw [hfact a b m]
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]; simp
      · simpa [elementoSigno] using hpos
    · right
      ext ⟨⟨a, b⟩, m⟩
      rw [hfact a b m]
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]; simp
      · simpa [elementoSigno] using hneg
  · rintro (rfl | rfl) m
    · simp
    · apply Units.ext
      simp [incrustacionNucleo]

/-- **Aislamiento unilateral de `G_vonMangoldt` en conductor 1:**
como en conductor 1 no hay carácter cuadrático retenido en el nivel (`psK = none`), el carácter
trivial `0 ∈ Ψ` aporta `G_vonMangoldt y` y todos los demás caracteres de `subconjuntoAnulador Ψ A₀`
quedan acotados por `B_sig`, produciendo la desigualdad unilateral
`G_vonMangoldt y ≤ B_top / b + B_sig` sin elevar al cuadrado la suma de primos. -/
theorem aislamiento_unilateral_conductor_uno {H : Type*} [AddCommGroup H]
    (A0 : AddSubgroup H) [Fintype A0]
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ))
    (h0_mem : (0 : AddChar (GrupoBaseDos × H) ℂ) ∈ Ψ)
    (T2 : Finset H) (hT2_sub : ∀ s ∈ T2, s ∈ A0) (hT2_ne : T2.Nonempty)
    (t : H) {b y B_top B_sig : ℝ} (hb : 0 < b)
    (perfil : AddChar (GrupoBaseDos × H) ℂ → ℝ → ℂ)
    (h_lectura_uno : (perfil 0 y).re = G_vonMangoldt y)
    (h_cota_top : ∀ u0 : A0,
      (funcionalExplicitoTorcido Ψ T2 b perfil y (u0 : H) t).re ≤ (T2.card : ℝ) * B_top)
    (h_cota_sig :
      |(∑ ψ ∈ (by classical exact (subconjuntoAnulador Ψ A0).erase 0),
          ψ (traslacionImpar t) * perfil ψ y).re| ≤ B_sig) :
    G_vonMangoldt y ≤ B_top / b + B_sig := by
  classical
  have hproy := congrArg Complex.re (proyeccion_lineal_anfitrion A0 Ψ T2 hT2_sub b perfil y t)
  rw [Complex.re_sum] at hproy
  have hre_rhs : (((Fintype.card A0 * T2.card : ℕ) : ℂ) * (b : ℂ) *
      ∑ ψ ∈ subconjuntoAnulador Ψ A0, ψ (traslacionImpar t) * perfil ψ y).re
      = (Fintype.card A0 : ℝ) * (T2.card : ℝ) * b *
          (∑ ψ ∈ subconjuntoAnulador Ψ A0, ψ (traslacionImpar t) * perfil ψ y).re := by
    have hcast : ((Fintype.card A0 * T2.card : ℕ) : ℂ) * (b : ℂ)
        = (((Fintype.card A0 : ℝ) * (T2.card : ℝ) * b : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.re_ofReal_mul]
  rw [hre_rhs] at hproy
  have hlhs_le : (∑ u0 : A0, (funcionalExplicitoTorcido Ψ T2 b perfil y (u0 : H) t).re)
      ≤ (Fintype.card A0 : ℝ) * (T2.card : ℝ) * B_top := by
    calc (∑ u0 : A0, (funcionalExplicitoTorcido Ψ T2 b perfil y (u0 : H) t).re)
        ≤ ∑ _u0 : A0, (T2.card : ℝ) * B_top := Finset.sum_le_sum fun u0 _ => h_cota_top u0
      _ = (Fintype.card A0 : ℝ) * ((T2.card : ℝ) * B_top) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card A0 : ℝ) * (T2.card : ℝ) * B_top := by ring
  have h0_an : (0 : AddChar (GrupoBaseDos × H) ℂ) ∈ subconjuntoAnulador Ψ A0 := by
    rw [mem_subconjuntoAnulador]
    exact ⟨h0_mem, fun _ _ => AddChar.zero_apply _⟩
  have hsplit_an : (∑ ψ ∈ subconjuntoAnulador Ψ A0, ψ (traslacionImpar t) * perfil ψ y).re
      = G_vonMangoldt y +
          (∑ ψ ∈ (subconjuntoAnulador Ψ A0).erase 0, ψ (traslacionImpar t) * perfil ψ y).re := by
    rw [← Finset.add_sum_erase _ _ h0_an, Complex.add_re, AddChar.zero_apply, one_mul, h_lectura_uno]
  have hA0_pos : (0 : ℝ) < Fintype.card A0 := by exact_mod_cast Fintype.card_pos
  have hT2_pos : (0 : ℝ) < T2.card := by exact_mod_cast Finset.card_pos.mpr hT2_ne
  have hfac_pos : 0 < (Fintype.card A0 : ℝ) * (T2.card : ℝ) := mul_pos hA0_pos hT2_pos
  have hineq1 : (Fintype.card A0 : ℝ) * (T2.card : ℝ) *
      (b * (G_vonMangoldt y +
        (∑ ψ ∈ (subconjuntoAnulador Ψ A0).erase 0, ψ (traslacionImpar t) * perfil ψ y).re))
      ≤ (Fintype.card A0 : ℝ) * (T2.card : ℝ) * B_top := by
    rw [← hsplit_an]
    linarith
  have hineq2 : b * (G_vonMangoldt y +
      (∑ ψ ∈ (subconjuntoAnulador Ψ A0).erase 0, ψ (traslacionImpar t) * perfil ψ y).re) ≤ B_top :=
    le_of_mul_le_mul_left hineq1 hfac_pos
  have hdiv : G_vonMangoldt y +
      (∑ ψ ∈ (subconjuntoAnulador Ψ A0).erase 0, ψ (traslacionImpar t) * perfil ψ y).re ≤ B_top / b := by
    rwa [le_div_iff₀ hb, mul_comm]
  have hsig_lo : -B_sig ≤
      (∑ ψ ∈ (subconjuntoAnulador Ψ A0).erase 0, ψ (traslacionImpar t) * perfil ψ y).re :=
    (abs_le.mp h_cota_sig).1
  linarith

/-! ### 3. Interfaz de los 4 pilares de Alpöge en conductor 1 (`λ = 3/2`) y equivalencia con RH -/

/-- **Dato anfitrión en una ventana `[Y, Y^{3/2}]`:**
existencia de un grupo finito `H`, subgrupo `A₀`, conjunto fino `T₂ ⊆ A₀` y perfil torcido cuyas
cotas de Arakelov–Stepanov–theta (`B_top`) y de caracteres complementarios (`B_sig`) suman a lo
sumo `y^{1/2 + c_motor · ε}` en toda la ventana `[Y, Y^{3/2}]`. -/
def VentanaAnfitrionConductorUno (Y c_motor ε : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (A0 : AddSubgroup H) (_ : Fintype A0)
    (Ψ : Finset (AddChar (GrupoBaseDos × H) ℂ)) (T2 : Finset H) (t : H) (b : ℝ)
    (perfil : AddChar (GrupoBaseDos × H) ℂ → ℝ → ℂ)
    (B_top B_sig : ℝ → ℝ),
    (0 : AddChar (GrupoBaseDos × H) ℂ) ∈ Ψ ∧
    (∀ s ∈ T2, s ∈ A0) ∧ T2.Nonempty ∧ 0 < b ∧
    ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)),
      (perfil 0 y).re = G_vonMangoldt y ∧
      (∀ u0 : A0,
        (funcionalExplicitoTorcido Ψ T2 b perfil y (u0 : H) t).re ≤ (T2.card : ℝ) * B_top y) ∧
      |(∑ ψ ∈ (by classical exact (subconjuntoAnulador Ψ A0).erase 0),
          ψ (traslacionImpar t) * perfil ψ y).re| ≤ B_sig y ∧
      B_top y / b + B_sig y ≤ y ^ (1 / 2 + c_motor * ε)

/-- **Interfaz exacta del motor aritmético de 4 pilares para `ζ(s)` (conductor 1):**
existen constantes `c_motor ≥ 0` (`e_D + e_L + 7` en `CoreGm`) y `ε₁ > 0` tales que para cada
`ε ∈ (0, ε₁)` y cada umbral `Y₀`, existe una ventana `[Y, Y^{3/2}]` con `Y ≥ Y₀` equipada con
`VentanaAnfitrionConductorUno Y c_motor ε`. -/
def MotorArithConductorUno : Prop :=
  ∃ (c_motor ε₁ : ℝ), 0 ≤ c_motor ∧ 0 < ε₁ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ VentanaAnfitrionConductorUno Y c_motor ε

/-- Del motor de anfitriones en conductor 1 se deduce la condición unilateral `(V)` en ventanas
`[Y, Y^{3/2}]`. -/
theorem ventana_de_motor_conductor_uno (hM : MotorArithConductorUno) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ Y₀ : ℝ, ∃ Y : ℝ,
      Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y ^ (3 / 2 : ℝ)), G_vonMangoldt y ≤ y ^ θ := by
  obtain ⟨c_motor, ε₁, hc0, hε₁, hfam⟩ := hM
  intro θ hθ12 _ Y₀
  set ε : ℝ := min (ε₁ / 2) ((θ - 1 / 2) / (c_motor + 1))
  have hε_pos : 0 < ε := lt_min (half_pos hε₁) (div_pos (by linarith) (by positivity))
  have hε_lt : ε < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcε_le : c_motor * ε ≤ θ - 1 / 2 := by
    have h1 : ε ≤ (θ - 1 / 2) / (c_motor + 1) := min_le_right _ _
    have h2 : c_motor * ε ≤ (c_motor + 1) * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hε_pos.le
    have h3 : (c_motor + 1) * ((θ - 1 / 2) / (c_motor + 1)) = θ - 1 / 2 :=
      mul_div_cancel₀ _ (by positivity)
    linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ c_motor + 1)]
  obtain ⟨Y, hY_ge, H, iG, iF, A0, iFA0, Ψ, T2, t, b, perfil, B_top, B_sig,
    h0_mem, hT2_sub, hT2_ne, hb, hy_win⟩ := hfam ε hε_pos hε_lt (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY_ge, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := ((le_max_right Y₀ 1).trans hY_ge).trans hy.1
  obtain ⟨h_lec, h_top, h_sig, h_sum⟩ := hy_win y hy
  have hG_le : G_vonMangoldt y ≤ B_top y / b + B_sig y :=
    @aislamiento_unilateral_conductor_uno H iG A0 iFA0 Ψ h0_mem T2 hT2_sub hT2_ne t
      b y (B_top y) (B_sig y) hb perfil h_lec h_top h_sig
  exact hG_le.trans (h_sum.trans (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)))

/-- **Cierre Ruta A → RH:** `MotorArithConductorUno` implica `RiemannHypothesis`. -/
theorem rh_de_motor_conductor_uno (hM : MotorArithConductorUno) : RiemannHypothesis :=
  rh_de_ventana_vonMangoldt (ventana_de_motor_conductor_uno hM)

/-- **Cierre Ruta A → Energía de AMate:** `MotorArithConductorUno` implica `E_Q ≤ C_ε Q^ε` para
todo `Q ≥ 2`. -/
theorem energia_de_motor_conductor_uno (hM : MotorArithConductorUno) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → E Q ≤ C * (Q : ℝ) ^ ε :=
  energia_subpolinomial (rh_de_motor_conductor_uno hM)

/-- Recíprocamente, `RiemannHypothesis` implica `MotorArithConductorUno` (instanciando el anfitrión
trivial `H = ZMod 1`). -/
theorem motor_conductor_uno_de_rh (hRH : RiemannHypothesis) : MotorArithConductorUno := by
  refine ⟨1, 1 / 2, zero_le_one, by norm_num, fun ε hε0 hε_lt Y₀ => ?_⟩
  have hZ : SinCerosDerecha (1 / 2) := sinCerosDerecha_half_iff_rh.mpr hRH
  have hσ_gt : (1 / 2 : ℝ) < 1 / 2 + ε / 2 := by linarith
  have hσ_lt : 1 / 2 + ε / 2 < 1 := by linarith
  obtain ⟨C, hC0, hC⟩ := cota_G_vonMangoldt_de_sin_ceros le_rfl hσ_gt hσ_lt hZ
  set Y : ℝ := max Y₀ (max 1 ((C + 1) ^ (2 / ε)))
  have hY_ge_Y0 : Y₀ ≤ Y := le_max_left _ _
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYC : (C + 1) ^ (2 / ε) ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  have iTopF : Fintype (⊤ : AddSubgroup (ZMod 1)) := by classical infer_instance
  refine ⟨Y, hY_ge_Y0, ZMod 1, inferInstance, inferInstance, ⊤, iTopF,
    {(0 : AddChar (GrupoBaseDos × ZMod 1) ℂ)}, {(0 : ZMod 1)}, (0 : ZMod 1), 1,
    (fun _ y => (G_vonMangoldt y : ℂ)), (fun y => y ^ (1 / 2 + 1 * ε)), (fun _ => 0),
    Finset.mem_singleton_self _, (fun _ _ => AddSubgroup.mem_top _), Finset.singleton_nonempty _,
    one_pos, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := hY1.trans hy.1
  have hy_pos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hC_le_y : C ≤ y ^ (ε / 2) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
      (hYC.trans hy.1) (half_pos hε0).le
    rw [← Real.rpow_mul (by positivity), show (2 / ε) * (ε / 2) = 1 by field_simp,
      Real.rpow_one] at h1
    linarith
  have hG_bd : G_vonMangoldt y ≤ y ^ (1 / 2 + 1 * ε) := by
    calc G_vonMangoldt y
        ≤ |G_vonMangoldt y| := le_abs_self _
      _ ≤ C * y ^ (1 / 2 + ε / 2) := hC y hy1
      _ ≤ y ^ (ε / 2) * y ^ (1 / 2 + ε / 2) :=
          mul_le_mul_of_nonneg_right hC_le_y (Real.rpow_nonneg hy_pos.le _)
      _ = y ^ (1 / 2 + 1 * ε) := by
          rw [← Real.rpow_add hy_pos]
          congr 1; ring
  refine ⟨by simp, fun u0 => ?_, ?_, by simp⟩
  · unfold funcionalExplicitoTorcido
    simp only [Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton,
      AddChar.zero_apply, ofReal_one]
    simpa using hG_bd
  · classical
    have hemp : (subconjuntoAnulador {(0 : AddChar (GrupoBaseDos × ZMod 1) ℂ)} ⊤).erase 0 = ∅ := by
      ext ψ
      simp only [Finset.mem_erase, mem_subconjuntoAnulador, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      tauto
    rw [hemp]
    simp

/-- **Equivalencia bilateral completa `MotorArithConductorUno ↔ RiemannHypothesis`:**
la existencia de anfitriones con cota `y^{1/2 + c · ε}` en ventanas `[Y, Y^{3/2}]` es exacta (ni más
fuerte ni más débil que `RiemannHypothesis`). -/
theorem rh_iff_motor_conductor_uno :
    RiemannHypothesis ↔ MotorArithConductorUno :=
  ⟨motor_conductor_uno_de_rh, rh_de_motor_conductor_uno⟩

end AMate
