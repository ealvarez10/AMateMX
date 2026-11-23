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

-- Miller test
#print axioms AMate.Miller.primo_todos_mentirosos
#print axioms AMate.Miller.mentirosos_en_subgrupo_propio
#print axioms AMate.Miller.test_miller_correcto
