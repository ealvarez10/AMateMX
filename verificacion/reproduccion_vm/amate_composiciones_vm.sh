#!/usr/bin/env bash
# =====================================================================================================
# Composiciones nuevas de AMate con la biblioteca de Alpöge (26 nov 2026)
# =====================================================================================================
# Se ejecuta DESPUÉS de amate_alpoge_vm.sh, en la misma máquina: reutiliza la biblioteca de Alpöge ya
# compilada en /home/ubuntu/grh/src/lean y el usuario sin privilegios "constructor".
#
# Compila y comprueba:
#   AMateConAlpoge/Composicion.lean           E_Q ≤ C_ε Q^ε sin hipótesis (ya comprobada el 23 nov)
#   AMateConAlpoge/ComposicionDirichlet.lean  E_{Q,χ} ≤ C_ε Q^ε y Θ_χ = 1/2 para todo χ ≠ 1
#   AMateConAlpoge/HipotesisAlpoge.lean       hipótesis analíticas de la cota de Bach explícita
#   AMateConAlpoge/MillerAlpoge.lean          test de Miller determinista con O((log n)^4) y O((log n)^2)
#                                             bases, y test certificado con la cota explícita 2(log n)^2
#   AMateConAlpoge/CertificadoAlpoge.lean     test certificado para todo n y menor no-residuo cuadrático
#
# Uso, con la versión de AMate subida a la máquina como tar.gz de publicacion/amate-lean:
#     sudo AMATE_TAR=/ruta/amate-lean.tar.gz AMATE_SHA256=<huella> nohup bash amate_composiciones_vm.sh \
#         > composiciones.log 2>&1 &
# o tomándola de GitHub:
#     sudo AMATE_COMMIT=<commit de AMateMX> nohup bash amate_composiciones_vm.sh > composiciones.log 2>&1 &
# Resultado: /root/amate_composiciones/resultado.txt (y todo en /root/amate_composiciones.tar.gz).
# Cada proceso que importa Main usa unos 25 GB de RAM y tarda más de 10 min solo en cargarlo.
# =====================================================================================================
set -uo pipefail

MATHLIB_REV=0df444a360eaa60ab8c11dca51a86af692955474
USUARIO=constructor
HOME_U=/home/$USUARIO
DIR_RH=/home/ubuntu/grh/src/lean
DIR_PROY=/opt/amate2/amate-lean
SALIDA=/root/amate_composiciones
REPO_AMATE=https://github.com/ealvarez10/AMateMX.git

[ "$(id -u)" = 0 ] || { echo "Ejecútalo con sudo."; exit 1; }
mkdir -p "$SALIDA"
log() { echo "[$(date -u '+%F %T') UTC] $*" | tee -a "$SALIDA/registro.txt"; }
die() { log "ERROR: $*"; echo "FALLÓ: $*" > "$SALIDA/estado.txt"; exit 1; }
como() {
    runuser -u "$USUARIO" -- env HOME="$HOME_U" PATH="$HOME_U/.elan/bin:/usr/local/bin:/usr/bin:/bin" \
        bash -c "$1"
}

# ---------- 1. Requisitos: la biblioteca de Alpöge ya compilada ----------
id "$USUARIO" >/dev/null 2>&1 || die "falta el usuario $USUARIO: ejecuta antes amate_alpoge_vm.sh"
[ -f "$DIR_RH/.lake/build/lib/lean/Main.olean" ] || die "falta $DIR_RH/.lake/build/lib/lean/Main.olean"
UID_U=$(id -u "$USUARIO")
log "Biblioteca de Alpöge encontrada en $DIR_RH"

# ---------- 2. Versión de AMate ----------
rm -rf /opt/amate2
mkdir -p /opt/amate2
if [ -n "${AMATE_TAR:-}" ]; then
    [ -f "$AMATE_TAR" ] || die "no existe $AMATE_TAR"
    if [ -n "${AMATE_SHA256:-}" ]; then
        echo "$AMATE_SHA256  $AMATE_TAR" | sha256sum -c - >> "$SALIDA/registro.txt" 2>&1 \
            || die "la huella de $AMATE_TAR no coincide"
    fi
    tar xzf "$AMATE_TAR" -C /opt/amate2 || die "no se pudo extraer $AMATE_TAR"
    [ -d "$DIR_PROY" ] || DIR_PROY=$(dirname "$(find /opt/amate2 -maxdepth 3 -name lakefile.toml | head -1)")
elif [ -n "${AMATE_COMMIT:-}" ]; then
    git clone -q "$REPO_AMATE" "$DIR_PROY" || die "no se pudo clonar $REPO_AMATE"
    git -C "$DIR_PROY" checkout -q "$AMATE_COMMIT" || die "no existe el commit $AMATE_COMMIT"
else
    die "indica AMATE_TAR o AMATE_COMMIT"
fi
for f in AMateConAlpoge/Composicion.lean AMateConAlpoge/ComposicionDirichlet.lean AMateConAlpoge/HipotesisAlpoge.lean \
    AMateConAlpoge/MillerAlpoge.lean AMateConAlpoge/CertificadoAlpoge.lean; do
    [ -f "$DIR_PROY/$f" ] || die "falta $f en la versión de AMate"
done
(cd "$DIR_PROY" && sha256sum AMateConAlpoge/*.lean AMateDirichlet/*.lean AMateMiller/*.lean) > "$SALIDA/huellas_fuentes.txt"
log "AMate en $DIR_PROY ($(wc -l < "$SALIDA/huellas_fuentes.txt") archivos con huella)"

# ---------- 3. lakefile con la biblioteca de Alpöge ----------
cat > "$DIR_PROY/lakefile.toml" <<TOML
name = "AMateEnergia"
defaultTargets = ["AMateEnergia", "AMateDirichlet", "AMateMiller"]

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "$MATHLIB_REV"

[[require]]
name = "tree"
path = "$DIR_RH"

[[lean_lib]]
name = "AMateEnergia"

[[lean_lib]]
name = "AMateDirichlet"

[[lean_lib]]
name = "AMateMiller"

[[lean_lib]]
name = "AMateConAlpoge"
roots = ["AMateConAlpoge.Composicion", "AMateConAlpoge.ComposicionDirichlet",
  "AMateConAlpoge.HipotesisAlpoge", "AMateConAlpoge.MillerAlpoge", "AMateConAlpoge.CertificadoAlpoge"]
TOML
chown -R "$USUARIO:" /opt/amate2
como "cd $DIR_PROY && (lake update tree || lake update)" >> "$SALIDA/registro.txt" 2>&1 || die "falló lake update"
ok=0
for i in 1 2 3; do
    como "cd $DIR_PROY && lake exe cache get" >> "$SALIDA/registro.txt" 2>&1 && { ok=1; break; }
    log "lake exe cache get falló (intento $i)"
done
[ "$ok" = 1 ] || die "no se pudo descargar la caché de Mathlib"

# ---------- 4. Sin red para el usuario que compila ----------
iptables -I OUTPUT -m owner --uid-owner "$UID_U" -j REJECT || die "no se pudo cortar la red"
ip6tables -I OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
como "curl -s -m 5 https://example.com >/dev/null" && die "el usuario sin privilegios todavía tiene red"

# ---------- 5. Compilación ----------
log "Compilando AMateEnergia, AMateDirichlet y AMateMiller"
como "cd $DIR_PROY && lake build AMateEnergia AMateDirichlet AMateMiller" >> "$SALIDA/build.log" 2>&1 \
    || die "falló la compilación de las bibliotecas de AMate (mira build.log)"
log "Compilando AMateConAlpoge (importa Main)"
como "cd $DIR_PROY && lake build AMateConAlpoge" >> "$SALIDA/build.log" 2>&1 \
    || die "falló la compilación de AMateConAlpoge (mira build.log)"

# ---------- 6. Axiomas ----------
cat > "$DIR_PROY/VerificacionComposiciones.lean" <<'LEAN'
import AMateConAlpoge.Composicion
import AMateConAlpoge.ComposicionDirichlet
import AMateConAlpoge.MillerAlpoge
import AMateConAlpoge.CertificadoAlpoge
#print axioms AMate.energia_subpolinomial_alpoge
#print axioms AMate.Dirichlet.energia_dirichlet_subpolinomial_alpoge
#print axioms AMate.Dirichlet.tendsto_log_energia_dirichlet_alpoge
#print axioms AMate.Miller.cota_bach_alpoge
#print axioms AMate.Miller.esPrimoMiller_alpoge
#print axioms AMate.Miller.cota_bach_cuad_alpoge
#print axioms AMate.Miller.esPrimoMiller_cuad_alpoge
#print axioms AMate.Miller.hipHadamard_alpoge
#print axioms AMate.Miller.cota_bach_explicita_alpoge
#print axioms AMate.Miller.esPrimoMiller_explicito_alpoge
#print axioms AMate.Miller.esPrimoMiller_certificado_alpoge
#print axioms AMate.Miller.noResiduo_16_alpoge
#print axioms AMate.Miller.noResiduo_explicito_alpoge
#print axioms AMate.Miller.esPrimo_alpoge
LEAN
chown "$USUARIO:" "$DIR_PROY/VerificacionComposiciones.lean"
como "cd $DIR_PROY && lake env lean VerificacionComposiciones.lean" > "$SALIDA/axiomas.txt" 2>&1 \
    || die "falló VerificacionComposiciones.lean (mira axiomas.txt)"
iptables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
ip6tables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
grep -q sorryAx "$SALIDA/axiomas.txt" && die "alguna composición usa sorryAx (mira axiomas.txt)"
# Cada teorema debe depender solo de los tres axiomas estándar.
python3 -I - "$SALIDA/axiomas.txt" <<'PY' || die "aparecen axiomas no estándar (mira axiomas.txt)"
import re, sys
texto = open(sys.argv[1]).read()
bloques = re.findall(r"depends on axioms: \[([^\]]*)\]", texto, re.S)
assert len(bloques) == 14, f"se esperaban 14 listas de axiomas y hay {len(bloques)}"
for b in bloques:
    ax = {a.strip() for a in b.split(",") if a.strip()}
    assert ax <= {"propext", "Classical.choice", "Quot.sound"}, ax
PY

# ---------- 7. Resultado ----------
{
    echo "TERMINADO: composiciones compiladas y comprobadas ($(date -u '+%F %H:%M') UTC)"
    echo
    echo "--- Axiomas ---"
    cat "$SALIDA/axiomas.txt"
    echo
    echo "--- Huellas de las fuentes ---"
    cat "$SALIDA/huellas_fuentes.txt"
} > "$SALIDA/resultado.txt"
gzip -f "$SALIDA/build.log" 2>/dev/null
tar czf /root/amate_composiciones.tar.gz -C /root amate_composiciones
echo "TERMINADO $(date -u '+%F %H:%M') UTC: mira $SALIDA/resultado.txt" > "$SALIDA/estado.txt"
cat "$SALIDA/resultado.txt"
