#!/usr/bin/env bash
# Recheck the main theorems with the independent kernel nanoda.
#
# Requirements (not included in this repository):
#   - lean4export, tag v4.33.0, built with Lean 4.33.1:
#       https://github.com/leanprover/lean4export
#   - nanoda_lib (nanoda_bin), built with `cargo build --release`:
#       https://github.com/ammkrn/nanoda_lib
#
# Usage, from the repository root, after `lake build`:
#   LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin scripts/verificar_con_nanoda.sh
#
# The export is about 540 MB. nanoda used 8 threads and took about 11 s on 2026-11-23.
set -euo pipefail
: "${LEAN4EXPORT:?set LEAN4EXPORT to the lean4export binary}"
: "${NANODA:?set NANODA to the nanoda_bin binary}"
OUT=${OUT:-verificacion/nanoda/salida}
mkdir -p "$OUT"

DECL="AMate.energia_subpolinomial AMate.rh_iff_energia_subpolinomial AMate.rh_iff_energia_cofinal
AMate.sin_ceros_iff_energia_theta AMate.tendsto_log_energia_div_log AMate.rh_iff_ventana_vonMangoldt
AMate.rh_iff_deficit_primos AMate.cancelacion_columna_moebius_rh AMate.rh_iff_motor_conductor_uno
AMate.rh_iff_S_hiperbolica AMate.S_hiperbolica_uniforme_de_rh AMate.explosion_ventana_ondaPrueba
AMate.cota_incondicional_S_hiperbolica AMate.M_moebius_bound_theta AMate.cota_G_vonMangoldt_de_sin_ceros
AMate.E_le_lineal AMate.zeta_ofReal_ne_zero AMate.obstaculo_cauchy_paridad_409 AMate.cota_inferior_energia_cero
AMate.Dirichlet.cota_inferior_energia_cero AMate.Dirichlet.LFunction_ne_zero_de_energia_cofinal
AMate.Dirichlet.integral_sigma_floor AMate.Dirichlet.LFunction_eq_integral
AMate.Miller.test_miller_correcto AMate.Miller.mentirosos_en_subgrupo_propio AMate.Miller.primo_todos_mentirosos"

# shellcheck disable=SC2086
lake env "$LEAN4EXPORT" AMateEnergia AMateDirichlet AMateMiller -- $DECL > "$OUT/amate.ndjson"
sha256sum "$OUT/amate.ndjson"

touch "$OUT/enunciados_nanoda.txt"
cat > "$OUT/nanoda_config.json" <<EOF
{
    "export_file_path": "$OUT/amate.ndjson",
    "use_stdin": false,
    "num_threads": 8,
    "stack_size_bytes": 1073741824,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "pp_declars": [
        "AMate.tendsto_log_energia_div_log",
        "AMate.rh_iff_energia_cofinal",
        "AMate.energia_subpolinomial",
        "AMate.Dirichlet.LFunction_ne_zero_de_energia_cofinal",
        "AMate.Miller.test_miller_correcto"
    ],
    "pp_output_path": "$OUT/enunciados_nanoda.txt",
    "pp_to_stdout": false,
    "pp_options": {"all": false, "explicit": false, "universes": false, "notation": true,
                   "proofs": false, "indent": 2, "width": 100},
    "declar_sep": "\n\n",
    "print_success_message": true
}
EOF
"$NANODA" "$OUT/nanoda_config.json"
