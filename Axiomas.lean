import AMateEnergia
import AMateDirichlet
import AMateMiller

/-!
# Axiom check for the main theorems

Run with `lake env lean Axiomas.lean` after `lake build`. Every line must list only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- Energy criterion for ζ
#print axioms AMate.rh_iff_energia_subpolinomial
#print axioms AMate.rh_iff_energia_cofinal
#print axioms AMate.sin_ceros_iff_energia_theta
#print axioms AMate.tendsto_log_energia_div_log
#print axioms AMate.cota_inferior_energia_cero

-- Equivalent arithmetic formulations and barrier theorem
#print axioms AMate.rh_iff_ventana_vonMangoldt
#print axioms AMate.rh_iff_deficit_primos
#print axioms AMate.rh_iff_motor_conductor_uno
#print axioms AMate.rh_iff_S_hiperbolica
#print axioms AMate.explosion_ventana_ondaPrueba

-- Dirichlet L-functions
#print axioms AMate.Dirichlet.LFunction_eq_integral
#print axioms AMate.Dirichlet.integral_sigma_floor
#print axioms AMate.Dirichlet.cota_inferior_energia_cero
#print axioms AMate.Dirichlet.LFunction_ne_zero_de_energia_cofinal
#print axioms AMate.Dirichlet.L_recta_critica
#print axioms AMate.Dirichlet.P_recta_critica_L
#print axioms AMate.Dirichlet.sin_ceros_iff_energia_theta_L
#print axioms AMate.Dirichlet.grh_iff_energia_subpolinomial
#print axioms AMate.Dirichlet.tendsto_log_energia_div_log_L

-- Miller test
#print axioms AMate.Miller.primo_todos_mentirosos
#print axioms AMate.Miller.mentirosos_en_subgrupo_propio
#print axioms AMate.Miller.test_miller_correcto
#print axioms AMate.Miller.cotaSubgruposPropios_of_cotaCaracteres
#print axioms AMate.Miller.esPrimoMiller_correcto
#print axioms AMate.Miller.esPrimoMiller_id_correcto
#print axioms AMate.Miller.cota_caracteres_de_grh'
#print axioms AMate.Miller.esPrimoMiller_de_grh
#print axioms AMate.Miller.cota_caracteres_de_grh_cuad'
#print axioms AMate.Miller.esPrimoMiller_de_grh_cuad
#print axioms AMate.Miller.Hadamard.cota_hadamard
#print axioms AMate.Miller.Ponderada.cota_S
#print axioms AMate.Miller.Explicito.cota_bach_explicita
#print axioms AMate.Miller.cotaCaracteres_basesExplicitas
#print axioms AMate.Miller.esPrimoMiller_explicito
