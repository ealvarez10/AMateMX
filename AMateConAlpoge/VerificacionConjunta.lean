import AMateEnergia
import AMateConAlpoge.Composicion

/-!
Esta verificación carga la biblioteca completa de AMate y la composición con Main
en un mismo entorno. Se inspecciona una declaración de cada módulo añadido
después del paquete enviado al servidor.
-/

example : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 2 ≤ Q → AMate.E Q ≤ C * (Q : ℝ) ^ ε :=
  AMate.energia_subpolinomial_alpoge

#print axioms AMate.rh_de_energia_acotada_cofinal
#print axioms AMate.polo_simple_Phi_zeta
#print axioms AMate.energia_de_ventana_vonMangoldt
#print axioms AMate.energia_de_deficit_primos
#print axioms AMate.tendsto_log_energia_div_log
#print axioms AMate.rh_iff_deficit_primos
#print axioms AMate.cancelacion_columna_moebius_rh
#print axioms AMate.rh_iff_motor_conductor_uno
#print axioms AMate.rh_iff_S_hiperbolica
#print axioms AMate.S_hiperbolica_uniforme_de_rh
#print axioms riemannHypothesis
#print axioms AMate.energia_subpolinomial_alpoge
