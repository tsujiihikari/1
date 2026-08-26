#!/usr/bin/env bash
set -Eeuo pipefail

# ============================================================
# IkoRsyncTool.sh
#
# 10.206.40.35:/IKO/Master 配下の指定ディレクトリから
# *.jar ファイルだけをディレクトリ構造を維持して取得する。
#
# 実行ユーザー想定: aiuser
# ローカル格納先:
#   /home/aiuser/nkSec/tools/iko-rsync-main/IKO/Master
# ============================================================

# ---------- 設定 ----------
BASE_DIR="/home/aiuser/nkSec/tools/iko-rsync-main"
LOCAL_MASTER="${BASE_DIR}/IKO/Master"

REMOTE_USER="appadm"
REMOTE_HOST="10.206.40.35"
REMOTE_MASTER="/IKO/Master"

# cronでパスワード入力できないため、別ファイルから読み込む。
# 初回だけ以下を実行:
#   printf '%s\n' 'appadm' > /home/aiuser/.iko_rsync_pass
#   chmod 600 /home/aiuser/.iko_rsync_pass
PASS_FILE="/home/aiuser/.iko_rsync_pass"
SSH_DIR="/home/aiuser/.ssh"
KNOWN_HOSTS="${SSH_DIR}/known_hosts"

LOG_DIR="${BASE_DIR}/log"
LOG_FILE="${LOG_DIR}/IkoRsyncTool.log"
LOCK_FILE="/tmp/IkoRsyncTool.lock"

# ---------- 共通処理 ----------
mkdir -p "${LOCAL_MASTER}" "${LOG_DIR}" "${SSH_DIR}"
chmod 700 "${SSH_DIR}"

# 同じ処理の二重起動を防止
exec 9>"${LOCK_FILE}"
if ! flock -n 9; then
    printf '%s %s\n' "$(date '+%Y-%m-%d %H:%M:%S')" \
        "[INFO] IkoRsyncTool is already running. Exit." >> "${LOG_FILE}"
    exit 0
fi

# 手動実行時は画面＋ログ、cron時はログのみ
if [[ -t 1 ]]; then
    exec > >(tee -a "${LOG_FILE}") 2>&1
else
    exec >> "${LOG_FILE}" 2>&1
fi

log() {
    printf '%s %s\n' "$(date '+%Y-%m-%d %H:%M:%S')" "$*"
}

trap 'rc=$?; log "[ERROR] line=${LINENO} rc=${rc} command=${BASH_COMMAND}"; exit "${rc}"' ERR

# ---------- 前提コマンド確認 ----------
for cmd in rsync ssh sshpass flock find; do
    if ! command -v "${cmd}" >/dev/null 2>&1; then
        log "[ERROR] command not found: ${cmd}"
        log "[ERROR] Ubuntu例: sudo apt-get install -y rsync sshpass"
        exit 1
    fi
done

if [[ ! -r "${PASS_FILE}" ]]; then
    log "[ERROR] password file not found/readable: ${PASS_FILE}"
    log "[ERROR] create it once:"
    log "        printf '%s\\n' 'appadm' > ${PASS_FILE}"
    log "        chmod 600 ${PASS_FILE}"
    exit 1
fi

# パスワードファイルの権限が緩すぎる場合は警告
PASS_MODE="$(stat -c '%a' "${PASS_FILE}" 2>/dev/null || true)"
if [[ -n "${PASS_MODE}" && "${PASS_MODE}" != "600" ]]; then
    log "[WARN] ${PASS_FILE} permission is ${PASS_MODE}; chmod 600 is recommended."
fi

# ---------- 取得対象 ----------
REMOTE_SOURCES=()

add_targets() {
    local project="$1"
    shift

    local target
    for target in "$@"; do
        # /./ 以降を -R(--relative) でローカル側に維持する。
        # 例:
        #   /IKO/Master/./nikkoEZ/ez.web.online/
        #     -> LOCAL_MASTER/nikkoEZ/ez.web.online/
        REMOTE_SOURCES+=(
            "${REMOTE_USER}@${REMOTE_HOST}:${REMOTE_MASTER}/./${project}/${target}/"
        )
    done
}

# nikkoEZ
add_targets "nikkoEZ" \
    "ez.hostif.online" \
    "ez.hostif.online.night" \
    "ez.web.online" \
    "gyak.web.online" \
    "mcez.web.online" \
    "mcsmbc.web.online" \
    "msg.online" \
    "rb.hostif.online" \
    "rb.web.online" \
    "smbc.web.online"

# nkCCIS
add_targets "nkCCIS" \
    "compl.online.jar" \
    "efront.online.jar" \
    "gaidb.online.jar" \
    "h2front.online.jar" \
    "hfront.online.jar" \
    "hons.online.jar" \
    "kyak.online.jar" \
    "odryak.online.jar" \
    "pdfweb.online.jar" \
    "pless.online.jar" \
    "plessweb.online.jar" \
    "sknhons.online.jar" \
    "sknodryak.online.jar" \
    "tosj.online.jar" \
    "tsnhons.online.jar" \
    "tsnodryak.online.jar" \
    "wfront.online.jar" \
    "ws.online.jar"

# ifaCCIS
add_targets "ifaCCIS" \
    "icompl.online.jar" \
    "ifap.online.jar" \
    "ikyak.online.jar" \
    "iodryak.online.jar" \
    "isknodryak.online.jar" \
    "itsnodryak.online.jar" \
    "mfront.online.jar" \
    "sfront.online.jar"

# mbc
add_targets "mbc" \
    "apbfw.online" \
    "app.online" \
    "dfw.online" \
    "web.online"

# mobile
add_targets "mobile" \
    "apbfw.online" \
    "app.online" \
    "dfw.online" \
    "web.online"

# ---------- rsync ----------
#
# --relative / -R
#   /./ 以降の nikkoEZ/... 等をそのままローカルに保持
#
# --include='*/'
#   .jar に到達するため途中ディレクトリは通す
#
# --include='*.jar'
#   jarファイルのみ取得
#
# --exclude='*'
#   jar以外のファイルを除外
#
# --prune-empty-dirs
#   jarを含まない空ディレクトリをローカルに作らない
#
# --partial
#   転送中断時の再実行を効率化
#
# -rlt
#   recursive / symlink / timestamp を維持
#
SSH_CMD="ssh \
    -o StrictHostKeyChecking=accept-new \
    -o UserKnownHostsFile=${KNOWN_HOSTS} \
    -o ConnectTimeout=20 \
    -o ServerAliveInterval=30 \
    -o ServerAliveCountMax=3"

log "============================================================"
log "[START] IkoRsyncTool"
log "[INFO] remote=${REMOTE_USER}@${REMOTE_HOST}:${REMOTE_MASTER}"
log "[INFO] local=${LOCAL_MASTER}"
log "[INFO] target directories=${#REMOTE_SOURCES[@]}"

START_EPOCH="$(date +%s)"

set +e
sshpass -f "${PASS_FILE}" \
rsync \
    -rltR \
    --prune-empty-dirs \
    --partial \
    --human-readable \
    --itemize-changes \
    --include='*/' \
    --include='*.jar' \
    --exclude='*' \
    -e "${SSH_CMD}" \
    "${REMOTE_SOURCES[@]}" \
    "${LOCAL_MASTER}/"
RSYNC_RC=$?
set -e

END_EPOCH="$(date +%s)"
ELAPSED=$((END_EPOCH - START_EPOCH))

if [[ "${RSYNC_RC}" -ne 0 ]]; then
    log "[ERROR] rsync failed. rc=${RSYNC_RC}, elapsed=${ELAPSED}s"
    exit "${RSYNC_RC}"
fi

JAR_COUNT="$(find "${LOCAL_MASTER}" -type f -name '*.jar' | wc -l | tr -d ' ')"
TOTAL_SIZE="$(du -sh "${LOCAL_MASTER}" 2>/dev/null | awk '{print $1}')"

log "[INFO] local jar count=${JAR_COUNT}"
log "[INFO] local size=${TOTAL_SIZE}"
log "[SUCCESS] rsync completed. elapsed=${ELAPSED}s"
log "[END] IkoRsyncTool"
log "============================================================"
