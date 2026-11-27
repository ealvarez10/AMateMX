import AMateMiller.DeterministaExplicito
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectProofs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlaneStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundLeftRegionStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DirichletLogDerivReflectionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaTendstoLogSubHarmonic

/-!
# Las hipótesis analíticas de la cota explícita, demostradas por Alpöge

`HipHadamard` y `SerieDigamma` (`AMateMiller/HipotesisAnaliticas.lean`) son copias literales de
enunciados de la biblioteca de Alpöge; aquí se instancian con sus teoremas, que encajan por
igualdad definicional:

* `PI.EF.rectCauchy`, `PI.EF.zeroLocus`, `PI.EF.zerosFinite`, `PI.EF.regularPart`;
* `GlobalTheory.T.dirichlet_logDeriv_reflection_formula`,
  `GlobalTheory.T.digamma_log_bound_right_half_plane`,
  `GlobalTheory.T.digamma_log_bound_left_region`;
* las alturas buenas y la cota de `L'/L` en ellas, a partir de `zerosWindow_closed` y
  `PI.EF.localLemma_of_helpers`;
* `GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma`.

Este archivo no importa `Main` (solo unos pocos módulos de Alpöge), así que se comprueba en una
máquina normal. Queda solo GRH como hipótesis: `esPrimoMiller_explicito_de_grh`. La versión sin
hipótesis está en `MillerAlpoge.lean`.
-/

namespace AMate.Miller

/-- Las hipótesis analíticas de la cota de Hadamard, demostradas por Alpöge. -/
theorem hipHadamard_alpoge : Hadamard.HipHadamard where
  rc := _root_.PI.EF.rectCauchy
  zl := _root_.PI.EF.zeroLocus
  zf := _root_.PI.EF.zerosFinite
  rp := _root_.PI.EF.regularPart
  refl := GlobalTheory.T.dirichlet_logDeriv_reflection_formula
  dd := GlobalTheory.T.digamma_log_bound_right_half_plane
  di := GlobalTheory.T.digamma_log_bound_left_region
  alt := by
    obtain ⟨Cw, hCw, hW⟩ := zerosWindow_closed
    obtain ⟨Cl, hCl, hL⟩ := _root_.PI.EF.localLemma_of_helpers zerosWindow_closed chk_discFactor
      chk_discLog chk_lBoundRight chk_zetaBoundRight chk_lInvRight
    have hκ0 : (0 : ℝ) < 12 * Cw + 4 := by linarith
    exact ⟨12 * Cw + 4, _, hκ0, _root_.PI.EF.goodHeightExists_of hCw.le hW,
      _root_.PI.EF.logDerivHoriz_of hCw.le hCl.le hκ0 hW hL _root_.PI.EF.zeroLocus⟩

/-- La serie de la digamma, demostrada por Alpöge. -/
theorem serieDigamma_alpoge : PI.Digamma.SerieDigamma :=
  GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma

/-- **Cota de Bach explícita bajo GRH**: si `log n ≥ 64`, todo carácter `χ ≠ 1` módulo `n` toma
un valor `≠ 1` en algún `a ≤ 2 (log n)²` coprimo con `n`. -/
theorem cota_bach_explicita_de_grh (hG : GRHPrimitivo) :
    ∀ n : ℕ, 64 ≤ Real.log n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, (a : ℝ) ≤ 2 * Real.log n ^ 2 ∧ Nat.Coprime a n ∧ χ a ≠ 1 :=
  Explicito.cota_bach_explicita hipHadamard_alpoge serieDigamma_alpoge hG

/-- **Test de Miller certificado bajo GRH** con `basesExplicitas`. -/
theorem esPrimoMiller_explicito_de_grh (hG : GRHPrimitivo) (n : ℕ) :
    esPrimoMiller basesExplicitas n = true ↔ n.Prime :=
  esPrimoMiller_explicito hipHadamard_alpoge serieDigamma_alpoge hG n

end AMate.Miller

#print axioms AMate.Miller.hipHadamard_alpoge
#print axioms AMate.Miller.serieDigamma_alpoge
#print axioms AMate.Miller.cota_bach_explicita_de_grh
#print axioms AMate.Miller.esPrimoMiller_explicito_de_grh
