#!/usr/bin/env bash
# Corridas de la numérica de energía. Salida CSV en resultados/.
set -euo pipefail
B="$1"
cd "$(dirname "$0")"
malla() { python3 -I -c "
import math,sys
qmax=int(sys.argv[1]); paso=1/40
qs=sorted({max(2,round(math.exp(i*paso))) for i in range(int(math.log(qmax)/paso)+1)})
print(' '.join(map(str,qs)))" "$1"; }
"$B" zeta x2000:10_000_000 $(malla 1000000) > resultados/zeta_malla_log.csv
"$B" zeta x2000:10_000_000 $(seq 2 5000) > resultados/zeta_todos_Q_hasta_5000.csv
for m in chi3 chi4 chi5; do "$B" $m x2000:10_000_000 $(malla 300000) > resultados/${m}_malla_log.csv; done
for m in chi3 chi4 chi5; do "$B" $m x2000:10_000_000 $(seq 1 5000) > resultados/${m}_todos_Q_hasta_5000.csv; done
"$B" zeta x2000 1500000 2000000 3000000 5000000 7000000 10000000 > resultados/zeta_hasta_1e7.csv
echo LISTO
