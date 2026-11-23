#!/usr/bin/env bash
# =====================================================================================================
# AMate + Alpöge en una máquina virtual propia (Ubuntu 22.04 o 24.04, con sudo)
# =====================================================================================================
# Compila la biblioteca de Alpöge (prueba de la hipótesis de Riemann en Lean, 175.187 módulos) y la
# composición con AMate, comprueba los axiomas de
#     AMate.energia_subpolinomial_alpoge : ∀ ε > 0, ∃ C, ∀ Q ≥ 2, E Q ≤ C * Q ^ ε
# y compara la huella de cada .olean con la lista que publicó el MIT.
#
# Máquina recomendada: 64 núcleos, 256 GB de RAM (mínimo ~128), 300 GB de disco, Ubuntu LTS, y SIN
# cuenta de servicio ni rol IAM: compilar ejecuta código de la biblioteca, que no tiene licencia.
# Por eso compila un usuario sin privilegios ("constructor") y sin red durante la compilación.
#
# Uso:
#     sudo nohup bash amate_alpoge_vm.sh > amate_vm.log 2>&1 &
#     cat /root/amate_resultado/estado.txt       # resumen, cada 10 minutos
#     tail -f amate_vm.log                        # detalle
# Tarda unas 11-13 h con 64 núcleos. Si se corta (reinicio, error, cierre de sesión), vuelve a
# ejecutarlo igual: retoma donde se quedó, porque lake solo compila lo que falta.
# Al final deja el resultado en /root/amate_resultado/resultado.txt y todo junto en
# /root/amate_resultado.tar.gz (unos 30 MB) para descargarlo.
#
# Diferencias con Colab: aquí sí se puede subir vm.max_map_count (el límite de mapas de memoria por
# proceso que hizo fallar la compilación en Colab), así que no hace falta el parche. Y la biblioteca
# se compila en la misma ruta que usó el MIT (/home/ubuntu/grh/src/lean), así que las huellas se
# pueden comparar byte a byte: en Lean 4.33.1 los .olean con avisos del linter guardan esa ruta.
# El proyecto de AMate es el mismo zip que usó el cuaderno de Colab (21 nov 2026).
# =====================================================================================================
set -uo pipefail

REPO=https://github.com/leanprover-community/riemann-hypothesis.git
COMMIT=40e56bab026552e089d7afcfeff08d2defb9c005
TOOLCHAIN=leanprover/lean4:v4.33.1
MATHLIB_REV=0df444a360eaa60ab8c11dca51a86af692955474
USUARIO=constructor
HOME_U=/home/$USUARIO
DIR_RH=/home/ubuntu/grh/src/lean
DIR_AMATE=/opt/amate
DIR_PROY=$DIR_AMATE/lean_energia
SALIDA=/root/amate_resultado
LOG=$SALIDA/build.log
N_MODULOS=175187
SHA_MAIN_OLEAN_MIT=9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad
INICIO=$(date +%s)

[ "$(id -u)" = 0 ] || { echo "Ejecútalo con sudo."; exit 1; }
mkdir -p "$SALIDA/py"
log() { echo "[$(date -u '+%F %T') UTC] $*" | tee -a "$SALIDA/registro_script.txt"; }
die() { log "ERROR: $*"; echo "FALLÓ: $*" > "$SALIDA/estado.txt"; exit 1; }
hecho() { [ -f "$SALIDA/.hecho_$1" ]; }
marcar() { touch "$SALIDA/.hecho_$1"; }
ulimit -n 1048576 2>/dev/null || ulimit -n 65536
NUCLEOS=$(nproc)
RAM_GB=$(awk '/MemTotal/ {printf "%d", $2/1024/1024}' /proc/meminfo)
HILOS=$(( NUCLEOS < 64 ? NUCLEOS : 64 ))   # más de 64 hace que lake pierda tiempo en un bloqueo interno (MIT)

como() {   # ejecuta una orden de bash como el usuario sin privilegios
    runuser -u "$USUARIO" -- env HOME="$HOME_U" PATH="$HOME_U/.elan/bin:/usr/local/bin:/usr/bin:/bin" \
        LEAN_NUM_THREADS="$HILOS" bash -c "$1"
}
contar() { find "$DIR_RH/.lake/build/lib/lean" -name '*.olean' 2>/dev/null | wc -l; }
estado() {
    local n libre mem ult
    n=$(contar)
    libre=$(df --output=avail -BG "$DIR_RH" 2>/dev/null | tail -1 | tr -dc 0-9)
    mem=$(awk '/MemAvailable/ {printf "%d", $2/1024/1024}' /proc/meminfo)
    ult=$(tail -n 1 "$LOG" 2>/dev/null | cut -c1-200)
    printf '%s UTC  %s módulos %s/%s (%s %%)  %s h  disco libre %s GB  memoria disponible %s GB\n    %s\n' \
        "$(date -u '+%F %H:%M')" "$1" "$n" "$N_MODULOS" "$((100 * n / N_MODULOS))" \
        "$(( ($(date +%s) - INICIO) / 3600 ))" "$libre" "$mem" "$ult" | tee "$SALIDA/estado.txt"
}

# ---------- Programas auxiliares en Python ----------
cat > "$SALIDA/py/amate.py" <<'PY'
import sys, os, hashlib, zipfile
zip_ruta, destino = sys.argv[1:3]
ZIP_SHA256 = 'fcf0fdf449f166aa8bc95f318560255ccb2a8b36a72ef855fca741853a02b25c'
HUELLAS = {
    "lean_energia/lakefile.toml": "955bd9b6a0e1599a925c2234eab066dee4ec14e7d6bd9fe58bbf37594199ad90",
    "lean_energia/lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lean_energia/lake-manifest.json": "e130d921a4549a9867e6d71fd7e9b05a64070e2ebe60fc0334eab7cd6c638280",
    "lean_energia/AMateEnergia.lean": "3b5a09fef4edf69ac024d671951508440a09302e6f7f581666b6f62326f74cdd",
    "lean_energia/AMateConAlpoge/Composicion.lean": "95360762862bb37df8b8c1dad58753e1884cb9416b4b63e71594ca77410b16ed",
    "lean_energia/AMateEnergia/Analitica.lean": "ea792c4a6b8262fefda24192e858c3cfad1573d561ec409ae63a11bd8855a5d8",
    "lean_energia/AMateEnergia/Definiciones.lean": "50a46ae12b25d32e08b779abecce41d2105b9bc1326342a7dc98f2da8bea34be",
    "lean_energia/AMateEnergia/Elementales.lean": "93a43c334442781b992933d8133bd7b2817fee0e148de28a30127993cde62676",
    "lean_energia/AMateEnergia/EnergiaFourier.lean": "3fb95a1debe4a5b385bd041a270f428ec4a7f4abea9b9c22e06a4e1dd1fb9246",
    "lean_energia/AMateEnergia/InversaZeta.lean": "60218cb970713a8af6b4f159c283fefaf568dcf7bb07a8511acf0e1a99cd8c05",
    "lean_energia/AMateEnergia/MellinTestigo.lean": "6c67c66415ab25a200fe65c95ee9e18649f60e3e6c82a3944eae1ce1a65cff8d",
    "lean_energia/AMateEnergia/PerronContorno.lean": "c5324ca9d0bc81eb5cda4481dd80a84d20a077da4133f2d26a2314450240de86",
    "lean_energia/AMateEnergia/PerronPeso.lean": "8e49c8824ca394bed886420dccc249e782579fb937d0587a7a99c4f9b9d2b93a",
    "lean_energia/AMateEnergia/PerronZ.lean": "1000c36d301e140804de9d9d8e6f163a17b01af81ac214b63f289b2ff2b64717",
    "lean_energia/AMateEnergia/Plancherel.lean": "88f394d97220a0d30850873b0be0d5805ecb2253be3f0c7110253e802f0419ea",
    "lean_energia/AMateEnergia/PolinomioCritica.lean": "18ae41e8cbd654a1b1ef8ace0c1d3fec828143a4ce99c14e3b019292e135a6e4",
    "lean_energia/AMateEnergia/Teorema.lean": "4deb6d6043c7606c2e1d9223737b9a94ff07a2f7e640d8dfe2a7177f7a5d0d3d",
    "lean_energia/AMateEnergia/ZetaBanda.lean": "03c318cb61fc6ff5dafb7675acbf7d4bba1bfcc292d6f87bb1f61ae607660e3e",
    "lean_energia/AMateEnergia/ZetaCotas.lean": "004279fc606fc62bf26160db87e7e0cab37c5a1f0f967a9b528cc6855c0a7308",
    "lean_energia/AMateEnergia/ZetaIntegral.lean": "480a38bbc83aa903fffefba4e74a25b48103ed5fd8112e97095143be655370f2",
    "lean_energia/AMateEnergia/ZetaRectaCero.lean": "d5fed05317c4e3bc9d77771f1b3d27f27eb8b0308edc4b4a8bd0df7210b5870a"
}
assert hashlib.sha256(open(zip_ruta, 'rb').read()).hexdigest() == ZIP_SHA256, 'la huella del zip de AMate no coincide'
zipfile.ZipFile(zip_ruta).extractall(destino)
for rel, h in HUELLAS.items():
    assert hashlib.sha256(open(os.path.join(destino, rel), 'rb').read()).hexdigest() == h, f'huella distinta: {rel}'
print(f'{len(HUELLAS)} archivos de AMate, huellas correctas')
PY
cat > "$SALIDA/py/errores.py" <<'PY'
# Extrae del registro de lake los bloques de los módulos que fallaron ("✖ ...") y los clasifica.
import sys, re, collections
ruta, titulo = sys.argv[1:3]
FIN = ('✔', '⚠', '✖', 'ℹ', 'Some required', 'Build completed', 'error: build failed', 'CODIGO_SALIDA=', '===== PASADA')
bloques, actual = [], None
for linea in open(ruta, encoding='utf-8', errors='replace'):
    linea = linea.rstrip('\n')
    if linea.startswith('✖'):
        if actual:
            bloques.append(actual)
        actual = [linea[:2000]]
    elif actual is not None:
        if linea.startswith(FIN):
            bloques.append(actual)
            actual = None
        else:
            actual.append(linea[:2000])
if actual:
    bloques.append(actual)
CLASES = [
    ('no pudo cargar un .olean, pedir memoria o crear un hilo (límite de mapas de memoria)',
     r"failed to read file '[^']*\.olean|failed to map|failed to create thread|bad_alloc|INTERNAL PANIC: out of memory"),
    ('proceso matado por el sistema (código 137: falta de memoria)', r'code 137|signal 9|SIGKILL|\bKilled\b'),
    ('desbordamiento de pila', r'[Ss]tack overflow'),
    ('tiempo determinista agotado', r'deterministic\) timeout|maxHeartbeats|maximum recursion depth'),
    ('sin espacio en disco', r'No space left'),
    ('demasiados archivos abiertos', r'Too many open files|EMFILE'),
]
def clase(b):
    t = '\n'.join(b)
    return next((n for n, p in CLASES if re.search(p, t)), 'otro (ver el texto del error)')
c = collections.Counter(clase(b) for b in bloques)
print(f'===== {titulo}: {len(bloques)} módulos con error')
for k, v in c.most_common():
    print(f'  {v:5d}  {k}')
print()
for b in bloques:
    print('\n'.join(b[:60] + ([f'... ({len(b) - 60} líneas más)'] if len(b) > 60 else [])))
    print()
PY
cat > "$SALIDA/py/comparar.py" <<'PY'
# Huella de cada .olean compilado, si guarda la ruta de compilación, y comparación con la lista del MIT.
import sys, os, hashlib, urllib.request, pathlib
from concurrent.futures import ThreadPoolExecutor
dir_rh, salida = sys.argv[1:3]
URL_MIT = 'https://math.mit.edu/~drew/grh/project-oleans.sha256'
SHA_LISTA_MIT = '375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25'
DIR_RH_MIT = '/home/ubuntu/grh/src/lean'
CON_RUTA_MIT = 98219
LOCMODEL = './Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LocModel.olean'
SHA_LOCMODEL_VALIDAS = {'b55278e22939409c55d8085f8b9d26431b3bef5132a5b07166ec8fd4c4092ae4',
                        '612ca2f7fae47c832214d298427ec1fcdf7f35861402f7b9de200042801afda7'}
base = pathlib.Path(dir_rh, '.lake/build/lib/lean')
marca = (dir_rh + '/src/').encode()

def huella_y_ruta(ruta):
    h, tiene, cola = hashlib.sha256(), False, b''
    with open(ruta, 'rb') as f:
        for bloque in iter(lambda: f.read(1 << 20), b''):
            h.update(bloque)
            if not tiene:
                tiene = marca in cola + bloque
                cola = bloque[-len(marca):]
    return h.hexdigest(), tiene

rutas = sorted(str(p) for p in base.rglob('*.olean'))
with ThreadPoolExecutor(os.cpu_count()) as ex:
    res = list(ex.map(huella_y_ruta, rutas))
nuestras = {'./' + os.path.relpath(r, base): h for r, (h, _) in zip(rutas, res)}
con_ruta = {'./' + os.path.relpath(r, base) for r, (_, t) in zip(rutas, res) if t}
pathlib.Path(salida, 'huellas_oleans.sha256').write_text(''.join(f'{h}  {r}\n' for r, h in sorted(nuestras.items())))

lineas = []
try:
    datos = urllib.request.urlopen(URL_MIT, timeout=300).read()
    ok = hashlib.sha256(datos).hexdigest() == SHA_LISTA_MIT
except Exception as e:
    datos, ok = None, False
    lineas.append(f'No se pudo descargar la lista del MIT ({e}).')
lineas += [f'Lista del MIT: {"descargada y verificada" if ok else "NO verificada"}',
           f'Ruta de compilación: {dir_rh}' + ('' if dir_rh == DIR_RH_MIT else f' (el MIT usó {DIR_RH_MIT})'),
           f'Archivos compilados aquí: {len(nuestras)}',
           f'Archivos que guardan la ruta de compilación: {len(con_ruta)} (en el MIT: {CON_RUTA_MIT} de 175.187)']
if ok:
    mit = {}
    for l in datos.decode().splitlines():
        if l.strip():
            h, r = l.split(None, 1)
            mit[r.strip()] = h
    iguales = sum(1 for r, h in nuestras.items() if mit.get(r) == h)
    distintos = sorted(r for r, h in nuestras.items() if r in mit and mit[r] != h)
    otra = LOCMODEL in distintos and nuestras[LOCMODEL] in SHA_LOCMODEL_VALIDAS
    if otra:
        distintos.remove(LOCMODEL)
        iguales += 1
    faltan = sorted(set(mit) - set(nuestras))
    sobran = sorted(set(nuestras) - set(mit))
    dist_sin = [r for r in distintos if r not in con_ruta]
    dist_con = [r for r in distintos if r in con_ruta]
    lineas += [f'Archivos en la lista del MIT: {len(mit)}',
               f'Idénticos byte a byte: {iguales}' + (' (LocModel.olean coincide con la otra salida que documenta el MIT)' if otra else ''),
               f'Distintos: {len(distintos)} ({len(dist_con)} guardan la ruta de compilación, {len(dist_sin)} no)',
               f'En la lista del MIT pero no compilados aquí: {len(faltan)}',
               f'Compilados aquí pero no en la lista del MIT: {len(sobran)}',
               'CONCLUSIÓN: ' + ('todos idénticos' if iguales == len(mit) == len(nuestras) else 'hay diferencias; ver las listas')]
    if LOCMODEL in distintos:
        lineas.append('Nota: LocModel.olean es el módulo no determinista que documenta el MIT (nombre de una variable ligada).')
    for nombre, lst in (('Distintos que no guardan la ruta', dist_sin), ('Distintos que guardan la ruta', dist_con),
                        ('Faltan', faltan), ('Sobran', sobran)):
        if lst:
            lineas += ['', f'{nombre} (primeros 200):'] + lst[:200]
pathlib.Path(salida, 'comparacion_mit.txt').write_text('\n'.join(lineas) + '\n')
print('\n'.join(lineas[:12]))
PY

# ---------- 0. Máquina, límites y paquetes ----------
log "Máquina: $NUCLEOS núcleos, $RAM_GB GB de RAM. Procesos de Lean a la vez: $HILOS"
command -v apt-get >/dev/null || die "este script es para Ubuntu (usa apt-get)"
[ "$NUCLEOS" -ge 16 ] || die "solo $NUCLEOS núcleos: tardaría días"
[ "$RAM_GB" -ge 120 ] || [ "${FORZAR:-0}" = 1 ] || die "solo $RAM_GB GB de RAM (mínimo ~128; FORZAR=1 para seguir igualmente)"
mkdir -p /home/ubuntu/grh/src
if ! hecho clon; then
    LIBRE=$(df --output=avail -BG /home/ubuntu/grh/src | tail -1 | tr -dc 0-9)
    [ "$LIBRE" -ge 220 ] || die "solo $LIBRE GB libres en /home: hacen falta unos 250 GB"
fi
# Cada .olean importado ocupa un mapa de memoria; los módulos de arriba importan ~230.000 archivos.
sysctl -w vm.max_map_count=1048576 >/dev/null
echo 'vm.max_map_count = 1048576' > /etc/sysctl.d/99-amate-lean.conf
[ "$(cat /proc/sys/vm/max_map_count)" -ge 1048576 ] || die "no se pudo subir vm.max_map_count"
log "vm.max_map_count = $(cat /proc/sys/vm/max_map_count)"
if ! hecho paquetes; then
    export DEBIAN_FRONTEND=noninteractive
    apt-get update -qq && apt-get install -y -qq git curl python3 iptables ca-certificates >/dev/null \
        || die "no se pudieron instalar los paquetes"
    marcar paquetes
fi

# ---------- 1. Usuario sin privilegios y Lean 4.33.1 ----------
id -u "$USUARIO" >/dev/null 2>&1 || useradd -m -s /bin/bash "$USUARIO"
UID_U=$(id -u "$USUARIO")
# por si una ejecución anterior le cortó la red y no llegó al final
iptables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
ip6tables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
if [ ! -x "$HOME_U/.elan/bin/lake" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
        || die "no se pudo descargar elan"
    chmod 644 /tmp/elan-init.sh
    como "bash /tmp/elan-init.sh -y --default-toolchain none" >/dev/null || die "no se pudo instalar elan"
fi
VERSION=$(como "elan toolchain install $TOOLCHAIN >/dev/null 2>&1; elan run $TOOLCHAIN lean --version" 2>&1)
log "$VERSION"
[[ "$VERSION" == *"version 4.33.1"* ]] || die "no se pudo instalar Lean 4.33.1"

# ---------- 2. Biblioteca de Alpöge en la ruta del MIT ----------
# constructor tiene que poder atravesar /home/ubuntu (solo atravesar, no listar)
chmod o+x /home/ubuntu /home/ubuntu/grh /home/ubuntu/grh/src
if ! hecho clon; then
    mkdir -p "$DIR_RH" && chown "$USUARIO:" "$DIR_RH"
    [ -d "$DIR_RH/.git" ] || como "git clone --quiet $REPO $DIR_RH" || die "no se pudo clonar la biblioteca"
    como "git -C $DIR_RH checkout --quiet --detach $COMMIT" || die "no se pudo fijar el commit"
    [ "$(git -c safe.directory='*' -C "$DIR_RH" rev-parse HEAD)" = "$COMMIT" ] || die "commit inesperado"
    while read -r h f; do
        echo "$h  $DIR_RH/$f" | sha256sum -c --quiet - || die "huella distinta: $f"
    done <<'HUELLAS'
b831ad8cac0babb7bf713433259bdfe5163e58c90734e86d71536d4e30ddec4c  lakefile.toml
fee57ee9ed399d0a638ca955e5ad40a37a36eeb9b6dfd9f5964114fa7bbe4774  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
017645ca448f2fd1f6fd5c4c2cb2c6e96e472725be13f6e180ca6e1574360939  src/Main.lean
HUELLAS
    N=$(find "$DIR_RH/src" -name '*.lean' | wc -l)
    [ "$N" = "$N_MODULOS" ] || die "$N módulos; se esperaban $N_MODULOS"
    log "Biblioteca: commit $COMMIT, $N módulos, huellas correctas"
    marcar clon
fi

# ---------- 3. Proyecto de AMate, caché de Mathlib y parte de AMate ----------
if ! hecho amate; then
    mkdir -p "$DIR_AMATE"
    base64 -d > "$SALIDA/amate_lean_energia.zip" <<'ZIP'
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
sBPPVqoK3HAuNeH4ymgeSNQ0a9bqWtCd5OakJ+RPuoB3xyL4x4hHNN8ly4Jd5EBfz8iBVh+lussbcsoMDdJcihgfNWqMesUlSQsl
3AJK6SItig0rLHfZKmahujyvQu2wnQOmH9YMlmVkULqOwTkS4G4joFZZDeWgxztCAh2xUCDB/uXdH1pER+Ua5rjp3wH7TXqMzpPh
J+ddpLQNp4eEkpA+X+4H+AqtdDAvsjXEj7Xhe7sQb5Vjw0jjiky6Dlvim3iRDljy14wy9LxPlLIRTZYYq8WwipaK3NIkM5beCC0U
g13Mr9liMYThToK7agpocl4tTJNM7WLhFUN7D972KWHA/jq/Xp8Fm7CEh9FpRA106bm/jDi1wwlrs8khziWuJ1KKOUHH4ODqaPuT
xVS4b6o8FttA1SEcddqVa+dI+ZGhyNce3+WFSTIHebRnFtl/mVB5g6JJK9NuGALNnM/UxesYhesFIoaBoO1r6vhs2Ijvv8Eb9EIr
6mmxVOQi396FYN5mFIgVunFkws2xa3KEHFb8/TcUPjv4gyl6mJxezrarsn20YxWSVDkcqItdVpj7g12kloroOO2OAmtHLg2LwyPX
UNVXUtYfQ12ZURHr4RuluynsXv6GMnvU/BIPB0EYsv0nTdNQ8sooXfQpssUUkFm1m5pNu9lhiLvM8KS9HGbWRYZPu9qk24okO/MR
ps6NNK8jB3F10eGq/GpFE70fQbbw+o2GhIleS9ATLJRFxaVbO3SlI9X5/1QlEMopZYT2ktqpY1YB2uoILHfgNQRePzB6HFRvNIIc
tNYWZMeRc7mvYHaBLT6rUztB5VWGW9j7Rv00LLHh9YJRoyTKmuVxIwmb/LHZ7zRIiw3fXIp9a3upZt3jRuP7sL1qW3NpMvucaSM/
DHkLsNHvbJcTWRXtSm2gZhcz31RYp0l1+bYCnnJQbxRtb5gbHNbOAHZr4IJYowbW9CH21B4HlvR57yYr2iNWSpdmVpN22/xseWax
ckfDdjeIlpd+/Ibt4m+iYbuLmo303NzhKSvRsbcJWXNHXiJa0QnrpOD90BNrSdIDkm56E2uqrubpbk52NzC3j9H42tmLjJM7Bl1s
1l2lF1kUmLXqnwcZHSbiqxNdWp7o0kLv6lnlPY96lrJdmw12Q7acYIe22zaCWG93gnh6Oby+1IJ4slbY8p6OpEODyI/v3rr0dm5d
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
U+O8B68r1SyHMOfRXjfZRRs7q2rxyg+XXJ5gaUJhyJp4v2kqqcGloGTqmxNipLHSJB+76LTD+j9EAdWibKZ/WvZ/UEsBAhQDFAAA
AAgAAAAhAEx/Er72AQAAPwMAABoAAAAAAAAAAAAAAKQBAAAAAGxlYW5fZW5lcmdpYS9sYWtlZmlsZS50b21sUEsBAhQDFAAAAAgA
AAAhAE2DPRQbAAAAGQAAABsAAAAAAAAAAAAAAKQBLgIAAGxlYW5fZW5lcmdpYS9sZWFuLXRvb2xjaGFpblBLAQIUAxQAAAAIAAAA
IQDHlstgpQIAAFcMAAAfAAAAAAAAAAAAAACkAYICAABsZWFuX2VuZXJnaWEvbGFrZS1tYW5pZmVzdC5qc29uUEsBAhQDFAAAAAgA
AAAhAMOD2/HbBQAAOw4AAB4AAAAAAAAAAAAAAKQBZAUAAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEubGVhblBLAQIUAxQAAAAI
AAAAIQAumSHacwEAAEMCAAAsAAAAAAAAAAAAAACkAXsLAABsZWFuX2VuZXJnaWEvQU1hdGVDb25BbHBvZ2UvQ29tcG9zaWNpb24u
bGVhblBLAQIUAxQAAAAIAAAAIQC5pelMeAUAANULAAAoAAAAAAAAAAAAAACkATgNAABsZWFuX2VuZXJnaWEvQU1hdGVFbmVyZ2lh
L0FuYWxpdGljYS5sZWFuUEsBAhQDFAAAAAgAAAAhAPmVkqiWAwAAKgkAACsAAAAAAAAAAAAAAKQB9hIAAGxlYW5fZW5lcmdpYS9B
TWF0ZUVuZXJnaWEvRGVmaW5pY2lvbmVzLmxlYW5QSwECFAMUAAAACAAAACEAG9vlK2kXAADZWwAAKgAAAAAAAAAAAAAApAHVFgAA
bGVhbl9lbmVyZ2lhL0FNYXRlRW5lcmdpYS9FbGVtZW50YWxlcy5sZWFuUEsBAhQDFAAAAAgAAAAhALCBQgQpDwAApTEAAC0AAAAA
AAAAAAAAAKQBhi4AAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvRW5lcmdpYUZvdXJpZXIubGVhblBLAQIUAxQAAAAIAAAAIQD0
M6a75hoAANVbAAAqAAAAAAAAAAAAAACkAfo9AABsZWFuX2VuZXJnaWEvQU1hdGVFbmVyZ2lhL0ludmVyc2FaZXRhLmxlYW5QSwEC
FAMUAAAACAAAACEA3GrxhQcOAAAzNgAALAAAAAAAAAAAAAAApAEoWQAAbGVhbl9lbmVyZ2lhL0FNYXRlRW5lcmdpYS9NZWxsaW5U
ZXN0aWdvLmxlYW5QSwECFAMUAAAACAAAACEAlzlPlW8iAAATiQAALQAAAAAAAAAAAAAApAF5ZwAAbGVhbl9lbmVyZ2lhL0FNYXRl
RW5lcmdpYS9QZXJyb25Db250b3Juby5sZWFuUEsBAhQDFAAAAAgAAAAhAN/TarQREAAAIUQAACkAAAAAAAAAAAAAAKQBM4oAAGxl
YW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvUGVycm9uUGVzby5sZWFuUEsBAhQDFAAAAAgAAAAhAFlai35DDgAAbysAACYAAAAAAAAA
AAAAAKQBi5oAAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvUGVycm9uWi5sZWFuUEsBAhQDFAAAAAgAAAAhAFOs7mVxBQAA6g0A
ACkAAAAAAAAAAAAAAKQBEqkAAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvUGxhbmNoZXJlbC5sZWFuUEsBAhQDFAAAAAgAAAAh
AO8+3wP7HQAAo4IAAC8AAAAAAAAAAAAAAKQByq4AAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvUG9saW5vbWlvQ3JpdGljYS5s
ZWFuUEsBAhQDFAAAAAgAAAAhAAct/F6xCAAA0xsAACYAAAAAAAAAAAAAAKQBEs0AAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEv
VGVvcmVtYS5sZWFuUEsBAhQDFAAAAAgAAAAhAPx7scEMGQAAuGwAACgAAAAAAAAAAAAAAKQBB9YAAGxlYW5fZW5lcmdpYS9BTWF0
ZUVuZXJnaWEvWmV0YUJhbmRhLmxlYW5QSwECFAMUAAAACAAAACEApJZMsG0JAABVGwAAKAAAAAAAAAAAAAAApAFZ7wAAbGVhbl9l
bmVyZ2lhL0FNYXRlRW5lcmdpYS9aZXRhQ290YXMubGVhblBLAQIUAxQAAAAIAAAAIQCOO2apfxEAAPE8AAArAAAAAAAAAAAAAACk
AQz5AABsZWFuX2VuZXJnaWEvQU1hdGVFbmVyZ2lhL1pldGFJbnRlZ3JhbC5sZWFuUEsBAhQDFAAAAAgAAAAhAEvYtzHgCgAAjigA
ACwAAAAAAAAAAAAAAKQB1AoBAGxlYW5fZW5lcmdpYS9BTWF0ZUVuZXJnaWEvWmV0YVJlY3RhQ2Vyby5sZWFuUEsFBgAAAAAVABUA
BQcAAP4VAQAAAA==
ZIP
    python3 -I "$SALIDA/py/amate.py" "$SALIDA/amate_lean_energia.zip" "$DIR_AMATE" | tee -a "$SALIDA/registro_script.txt" \
        || die "el proyecto de AMate no coincide con sus huellas"
    cat > "$DIR_PROY/lakefile.toml" <<TOML
name = "AMateEnergia"
defaultTargets = ["AMateEnergia"]

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
name = "AMateConAlpoge"
roots = ["AMateConAlpoge.Composicion"]
TOML
    chown -R "$USUARIO:" "$DIR_AMATE"
    como "cd $DIR_PROY && (lake update tree || lake update)" >> "$SALIDA/registro_script.txt" 2>&1 \
        || die "falló lake update"
    python3 -I - "$DIR_PROY/lake-manifest.json" "$MATHLIB_REV" <<'PY' || die "el manifiesto no tiene la Mathlib esperada o falta tree"
import json, sys
m = json.load(open(sys.argv[1]))
revs = {p['name']: p.get('rev') for p in m['packages']}
assert revs.get('mathlib') == sys.argv[2], revs.get('mathlib')
assert 'tree' in revs
PY
    ok=0
    for i in 1 2 3; do
        como "cd $DIR_PROY && lake exe cache get" >> "$SALIDA/registro_script.txt" 2>&1 && { ok=1; break; }
        log "lake exe cache get falló (intento $i); reintento"
    done
    [ "$ok" = 1 ] || die "no se pudo descargar la caché de Mathlib"
    como "cd $DIR_PROY && lake build AMateEnergia" >> "$SALIDA/registro_script.txt" 2>&1 || die "falló lake build AMateEnergia"
    printf 'import AMateEnergia\n#print axioms AMate.energia_subpolinomial\n' > "$DIR_PROY/VerificaAMate.lean"
    chown "$USUARIO:" "$DIR_PROY/VerificaAMate.lean"
    como "cd $DIR_PROY && lake env lean VerificaAMate.lean" > "$SALIDA/axiomas_amate.txt" 2>&1 || die "falló VerificaAMate.lean"
    grep -q sorryAx "$SALIDA/axiomas_amate.txt" && die "AMate.energia_subpolinomial usa sorryAx"
    log "Parte de AMate compilada: $(tr '\n' ' ' < "$SALIDA/axiomas_amate.txt" | cut -c1-200)"
    marcar amate
fi

# ---------- 4. Sin red para el usuario que compila ----------
iptables -I OUTPUT -m owner --uid-owner "$UID_U" -j REJECT || die "no se pudo cortar la red del usuario sin privilegios"
ip6tables -I OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
if como "curl -s -m 5 https://example.com >/dev/null"; then
    die "el usuario sin privilegios todavía tiene red"
fi
log "Red cortada para $USUARIO durante la compilación"

# ---------- 5. Compilación, con reintentos ----------
limpiador() {   # borra el setup.json (~6 MB) de cada módulo ya compilado (regla del MIT)
    while [ ! -f "$SALIDA/.fin_compilacion" ]; do
        sleep 120
        find "$DIR_RH/.lake/build/ir" -name '*.setup.json' 2>/dev/null | while IFS= read -r f; do
            t="$DIR_RH/.lake/build/lib/lean/${f#"$DIR_RH"/.lake/build/ir/}"
            [ "${t%.setup.json}.trace" -nt "$f" ] && rm -f "$f"
        done
    done
}
if ! hecho compilacion; then
    rm -f "$SALIDA/.fin_compilacion"
    limpiador &
    PID_LIMP=$!
    for pasada in 1 2 3 4; do
        antes=$(contar)
        echo "===== PASADA $pasada con LEAN_NUM_THREADS=$HILOS ($(date -u)) =====" >> "$LOG"
        desde=$(stat -c %s "$LOG")
        ( como "cd $DIR_PROY && lake build AMateConAlpoge"; echo "CODIGO_SALIDA=$?" ) >> "$LOG" 2>&1 &
        pid=$!
        t=0
        while kill -0 "$pid" 2>/dev/null; do
            [ $((t % 600)) -eq 0 ] && estado "[pasada $pasada, $HILOS procesos]"
            sleep 30
            t=$((t + 30))
        done
        wait "$pid"
        tail -c +"$((desde + 1))" "$LOG" > "$SALIDA/pasada_$pasada.log"
        python3 -I "$SALIDA/py/errores.py" "$SALIDA/pasada_$pasada.log" "Pasada $pasada (LEAN_NUM_THREADS=$HILOS)" \
            >> "$SALIDA/errores_compilacion.txt"
        if grep -q '^CODIGO_SALIDA=0$' "$SALIDA/pasada_$pasada.log"; then
            log "Pasada $pasada: compilación terminada"
            marcar compilacion
            break
        fi
        ahora=$(contar)
        log "Pasada $pasada falló: $((ahora - antes)) módulos nuevos. Errores en $SALIDA/errores_compilacion.txt"
        if [ "$ahora" -le "$antes" ] && [ "$HILOS" -le 2 ]; then break; fi
        HILOS=$(( HILOS / 2 > 1 ? HILOS / 2 : 1 ))
    done
    touch "$SALIDA/.fin_compilacion"
    kill "$PID_LIMP" 2>/dev/null
    estado "[compilación]" > /dev/null
    hecho compilacion || die "la compilación no terminó; mira $SALIDA/errores_compilacion.txt"
fi

# ---------- 6. Comprobación final ----------
if ! hecho verificacion; then
    cat > "$DIR_PROY/Verificacion.lean" <<'LEAN'
import AMateConAlpoge.Composicion
#check @AMate.energia_subpolinomial_alpoge
#print axioms AMate.energia_subpolinomial_alpoge
#print axioms riemannHypothesis
LEAN
    chown "$USUARIO:" "$DIR_PROY/Verificacion.lean"
    como "cd $DIR_PROY && lake env lean Verificacion.lean" > "$SALIDA/verificacion.txt" 2>&1 \
        || die "falló la comprobación final (mira $SALIDA/verificacion.txt)"
    grep -q sorryAx "$SALIDA/verificacion.txt" && die "la composición usa sorryAx (mira verificacion.txt)"
    marcar verificacion
fi
iptables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null
ip6tables -D OUTPUT -m owner --uid-owner "$UID_U" -j REJECT 2>/dev/null

# ---------- 7. Huellas y comparación con el MIT ----------
log "Calculando las huellas de los .olean y comparando con el MIT"
python3 -I "$SALIDA/py/comparar.py" "$DIR_RH" "$SALIDA" | tee -a "$SALIDA/registro_script.txt"
H_MAIN=$(sha256sum "$DIR_RH/.lake/build/lib/lean/Main.olean" | cut -c1-64)

# ---------- 8. Resultado ----------
{
    echo "TERMINADO: composición compilada y comprobada"
    echo
    echo "Commit de la biblioteca: $COMMIT"
    echo "Toolchain: $TOOLCHAIN; Mathlib $MATHLIB_REV"
    echo "Máquina: $NUCLEOS núcleos, $RAM_GB GB de RAM; vm.max_map_count $(cat /proc/sys/vm/max_map_count)"
    echo "Duración total: $(( ($(date +%s) - INICIO) / 3600 )) h (de esta ejecución del script)"
    echo "Módulos compilados: $(contar)"
    echo
    echo "--- Comprobación final (lake env lean Verificacion.lean) ---"
    cat "$SALIDA/verificacion.txt"
    echo
    echo "Main.olean sha256 $H_MAIN"
    if [ "$H_MAIN" = "$SHA_MAIN_OLEAN_MIT" ]; then echo "Coincide con el del MIT."; else echo "No coincide con el del MIT."; fi
    echo
    echo "--- Comparación con el MIT ---"
    head -n 12 "$SALIDA/comparacion_mit.txt"
} > "$SALIDA/resultado.txt"
gzip -f "$LOG" "$SALIDA"/pasada_*.log 2>/dev/null
tar czf /root/amate_resultado.tar.gz -C /root amate_resultado
echo "TERMINADO $(date -u '+%F %H:%M') UTC: mira $SALIDA/resultado.txt" > "$SALIDA/estado.txt"
cat "$SALIDA/resultado.txt"
log "Todo junto en /root/amate_resultado.tar.gz"
