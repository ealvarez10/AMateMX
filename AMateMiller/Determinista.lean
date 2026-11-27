import AMateMiller.Ejecutable
import AMateMiller.CotaBach
import AMateMiller.CotaBachCuadrada

/-!
# Test de Miller determinista con `O((log n)^4)` bases

Une el puente algebraico (`Puente.lean`), el test ejecutable (`Ejecutable.lean`) y la cota para
caracteres que se deduce de GRH, la fórmula explícita truncada y el conteo de ceros en ventanas
(`CotaBach.lean`):

* `basesBach K n = ⌊K (1 + log n)^4⌋`;
* `esPrimoMiller_de_grh`: bajo esas tres hipótesis existe `K > 0` tal que
  `esPrimoMiller (basesBach K) n = true ↔ n.Prime` para todo `n`.
* `basesBach2 K n = ⌊K (1 + log n)^2⌋` y `esPrimoMiller_de_grh_cuad`: lo mismo con
  `O((log n)^2)` bases (`CotaBachCuadrada.lean`).

La constante `K` no es explícita (depende de las constantes de las hipótesis). La versión con
constante explícita, `a ≤ 2 (log n)²`, y el test ejecutable certificado que se deduce de ella están
en `BachExplicito.lean` y `DeterministaExplicito.lean`.
-/

namespace AMate.Miller

/-- Número de bases `⌊K (1 + log n)^4⌋`. -/
noncomputable def basesBach (K : ℝ) (n : ℕ) : ℕ := ⌊K * (1 + Real.log n) ^ 4⌋₊

theorem cotaCaracteres_basesBach {K : ℝ}
    (h : ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 4 ∧ Nat.Coprime a n ∧ χ a ≠ 1) :
    CotaCaracteres (basesBach K) := by
  intro n hn χ hχ
  obtain ⟨a, ha, hcop, hχa⟩ := h n hn χ hχ
  exact ⟨a, Nat.le_floor ha, hcop, hχa⟩

/-- Bajo GRH (caracteres primitivos), la fórmula explícita truncada y el conteo de ceros en
ventanas, el test de Miller con `⌊K (1 + log n)^4⌋` bases decide la primalidad. -/
theorem esPrimoMiller_de_grh (hEF : PI.ExplicitFormula) (hZW : PI.ZerosWindow)
    (hGRH : GRHPrimitivo) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, esPrimoMiller (basesBach K) n = true ↔ n.Prime := by
  obtain ⟨K, hK, h⟩ := cota_caracteres_de_grh' hEF hZW hGRH
  exact ⟨K, hK, esPrimoMiller_correcto_de_caracteres (cotaCaracteres_basesBach h)⟩

/-- Número de bases `⌊K (1 + log n)^2⌋`. -/
noncomputable def basesBach2 (K : ℝ) (n : ℕ) : ℕ := ⌊K * (1 + Real.log n) ^ 2⌋₊

theorem cotaCaracteres_basesBach2 {K : ℝ}
    (h : ∀ n : ℕ, 3 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ K * (1 + Real.log n) ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1) :
    CotaCaracteres (basesBach2 K) := by
  intro n hn χ hχ
  obtain ⟨a, ha, hcop, hχa⟩ := h n hn χ hχ
  exact ⟨a, Nat.le_floor ha, hcop, hχa⟩

/-- Bajo GRH (caracteres primitivos), la fórmula explícita truncada y el conteo de ceros en
ventanas, el test de Miller con `⌊K (1 + log n)^2⌋` bases decide la primalidad. -/
theorem esPrimoMiller_de_grh_cuad (hEF : PI.ExplicitFormula) (hZW : PI.ZerosWindow)
    (hGRH : GRHPrimitivo) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, esPrimoMiller (basesBach2 K) n = true ↔ n.Prime := by
  obtain ⟨K, hK, h⟩ := cota_caracteres_de_grh_cuad' hEF hZW hGRH
  exact ⟨K, hK, esPrimoMiller_correcto_de_caracteres (cotaCaracteres_basesBach2 h)⟩

end AMate.Miller
