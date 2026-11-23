import Mathlib

/-!
# Definiciones: testigo canónico y energía de AMate

Testigo de los estados 37–45 de AMate, sin cambios hasta el estado 82. Para `Q ≥ 2` y `k ≥ 1`:

* `w k = 1/(k(k+1))` y `u d k = {k/d}`;
* `m Q = ∑_{d ≤ Q} μ(d)/d` y `t Q = 1 − ∑_{d ≤ Q} μ(d) log(Q/d)/d`;
* `gam Q = Q t_Q / log 2` y `h Q = 2 u_{2Q} − u_Q`;
* `phi Q = 1 + ∑_{d ≤ Q} μ(d) u_d − Q m_Q u_Q` y `sigma Q = phi Q − gam Q · h Q`;
* `E Q = ∑_{k ≥ 1} σ_Q(k)² w_k`;
* `P Q s`, el polinomio de Dirichlet de (2.3), con `σ̂_Q(s) = (1 − ζ(s) P_Q(s))/s`.
-/

open Finset

namespace AMate

/-- La función de Möbius con valores reales. -/
noncomputable def mu (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- Peso `w_k = 1/(k(k+1))`. -/
noncomputable def w (k : ℕ) : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1))

/-- Parte fraccionaria `u_d(k) = {k/d}`. Para `d = 0` vale cero. -/
noncomputable def u (d k : ℕ) : ℝ := Int.fract ((k : ℝ) / (d : ℝ))

/-- `m_Q = ∑_{d ≤ Q} μ(d)/d`. -/
noncomputable def m (Q : ℕ) : ℝ := ∑ d ∈ Icc 1 Q, mu d / (d : ℝ)

/-- `t_Q = 1 − ∑_{d ≤ Q} μ(d) log(Q/d)/d`. -/
noncomputable def t (Q : ℕ) : ℝ :=
  1 - ∑ d ∈ Icc 1 Q, mu d / (d : ℝ) * Real.log ((Q : ℝ) / (d : ℝ))

/-- Coeficiente del corrector, `γ_Q = Q t_Q / log 2`. -/
noncomputable def gam (Q : ℕ) : ℝ := (Q : ℝ) * t Q / Real.log 2

/-- Corrector `h_Q = 2 u_{2Q} − u_Q`. -/
noncomputable def h (Q k : ℕ) : ℝ := 2 * u (2 * Q) k - u Q k

/-- `φ_Q = 1 + ∑_{d ≤ Q} μ(d) u_d − Q m_Q u_Q`. -/
noncomputable def phi (Q k : ℕ) : ℝ :=
  1 + ∑ d ∈ Icc 1 Q, mu d * u d k - (Q : ℝ) * m Q * u Q k

/-- Testigo canónico `σ_Q = φ_Q − γ_Q h_Q`. -/
noncomputable def sigma (Q k : ℕ) : ℝ := phi Q k - gam Q * h Q k

/-- Energía `E_Q = ∑_{k ≥ 1} σ_Q(k)² w_k`. -/
noncomputable def E (Q : ℕ) : ℝ := ∑' k : ℕ, sigma Q (k + 1) ^ 2 * w (k + 1)

/-- Polinomio de Dirichlet del estado 45, (2.3):
`P_Q(s) = ∑_{d ≤ Q} μ(d) d^{-s} − Q m_Q Q^{-s} − γ_Q (2 (2Q)^{-s} − Q^{-s})`. -/
noncomputable def P (Q : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 Q, ((mu d : ℝ) : ℂ) * (d : ℂ) ^ (-s)
    - (Q : ℂ) * ((m Q : ℝ) : ℂ) * (Q : ℂ) ^ (-s)
    - ((gam Q : ℝ) : ℂ) * (2 * ((2 * Q : ℕ) : ℂ) ^ (-s) - (Q : ℂ) ^ (-s))

end AMate
