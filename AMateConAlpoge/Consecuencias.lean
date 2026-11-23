import AMateEnergia
import Main

/-!
# Consecuencias sin hipótesis de la composición con Alpöge

AMate demostró, solo con Mathlib, cotas aritméticas bajo la hipótesis `SinCerosDerecha θ`
(ζ no se anula en `Re s > θ`). Con `riemannHypothesis` del módulo `Main` de Alpöge
(`θ = 1/2`) pasan a ser teoremas sin hipótesis:

* `mertens_raiz_alpoge`: cota de Littlewood para la función de Mertens,
  `|∑_{d ≤ n} μ(d)| ≤ K_δ n^{1/2+δ}`.
* `vonMangoldt_suavizada_alpoge`: suma suavizada de von Mangoldt con error de raíz,
  `|∑_{n ≤ y} Λ(n)(y/n − 1) − y log y + (1 + γ) y| ≤ C y^{σ₀}` para todo `σ₀ > 1/2`.

Como `Composicion.lean`, este archivo no se compila por defecto: necesita la biblioteca
completa de Alpöge.
-/

namespace AMate

/-- RH en la forma `SinCerosDerecha (1/2)`, a partir del teorema de Alpöge. -/
theorem sinCeros_half_alpoge : SinCerosDerecha (1 / 2) :=
  sinCerosDerecha_half_iff_rh.mpr riemannHypothesis

/-- Cota de Littlewood sin hipótesis: para todo `0 < δ < 1/2` hay `K` con
`|∑_{d ≤ n} μ(d)| ≤ K n^{1/2+δ}` para todo `n`. -/
theorem mertens_raiz_alpoge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      |∑ d ∈ Finset.Icc 1 n, mu d| ≤ K * (n : ℝ) ^ (1 / 2 + δ) :=
  M_moebius_bound_theta le_rfl hδ (by linarith) sinCeros_half_alpoge

/-- Suma suavizada de von Mangoldt con error de raíz, sin hipótesis: para todo
`1/2 < σ₀ < 1` hay `C` con
`|∑_{n ≤ y} Λ(n)(y/n − 1) − y log y + (1 + γ) y| ≤ C y^{σ₀}` para todo `y ≥ 1`. -/
theorem vonMangoldt_suavizada_alpoge {σ₀ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      |(∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1))
          - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y| ≤ C * y ^ σ₀ :=
  cota_G_vonMangoldt_de_sin_ceros le_rfl h1 h2 sinCeros_half_alpoge

end AMate

#print axioms AMate.mertens_raiz_alpoge
#print axioms AMate.vonMangoldt_suavizada_alpoge
