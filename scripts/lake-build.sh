#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="$ROOT/lean"
LOCKFILE="${LOCKFILE:-$LEAN_ROOT/.lake/lake-build.lock}"
MEMORY_MB="${MEMORY_MB:-16384}"
THREADS="${THREADS:-1}"
LEAN_LOCKFILE="${LEAN_LOCKFILE:-$LEAN_ROOT/.lake/lean-serial.lock}"

REAL_LAKE="${REAL_LAKE:-$(command -v lake)}"
REAL_LEAN="${REAL_LEAN:-$(command -v lean)}"

mkdir -p "$(dirname "$LOCKFILE")"
mkdir -p "$(dirname "$LEAN_LOCKFILE")"

acquire_lock() {
  while true; do
    if (set -o noclobber; printf '%s\n' "$$" >"$LOCKFILE") 2>/dev/null; then
      return 0
    fi

    if IFS= read -r lock_pid <"$LOCKFILE" && [[ "$lock_pid" =~ ^[0-9]+$ ]] &&
        kill -0 "$lock_pid" 2>/dev/null; then
      echo "another lake build is already running (pid $lock_pid): $LOCKFILE" >&2
      exit 1
    fi

    rm -f "$LOCKFILE"
  done
}

WRAP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/schur-lake-wrap.XXXXXX")"
child_pid=""

cleanup() {
  if [[ -n "$child_pid" ]] && kill -0 "$child_pid" 2>/dev/null; then
    kill "$child_pid" 2>/dev/null || true
    wait "$child_pid" 2>/dev/null || true
  fi
  rm -rf "$WRAP_DIR"
  rm -f "$LOCKFILE"
}
trap cleanup EXIT INT TERM HUP

acquire_lock

cat >"$WRAP_DIR/lean" <<EOF
#!/usr/bin/env bash
set -euo pipefail

LEAN_LOCKFILE="$LEAN_LOCKFILE"
THREADS="$THREADS"
MEMORY_MB="$MEMORY_MB"
REAL_LEAN="$REAL_LEAN"
have_lock=0

cleanup() {
  if [[ "\$have_lock" == "1" ]]; then
    rm -f "\$LEAN_LOCKFILE"
  fi
}
trap cleanup EXIT INT TERM HUP

acquire_lean_lock() {
  while true; do
    if (set -o noclobber; printf '%s\n' "\$\$" >"\$LEAN_LOCKFILE") 2>/dev/null; then
      have_lock=1
      return 0
    fi

    if IFS= read -r lock_pid <"\$LEAN_LOCKFILE" && [[ "\$lock_pid" =~ ^[0-9]+$ ]] &&
        kill -0 "\$lock_pid" 2>/dev/null; then
      sleep 0.1
      continue
    fi

    rm -f "\$LEAN_LOCKFILE"
  done
}

acquire_lean_lock
"\$REAL_LEAN" -j "\$THREADS" -M "\$MEMORY_MB" "\$@"
EOF
chmod 755 "$WRAP_DIR/lean"

cd "$LEAN_ROOT"
PATH="$WRAP_DIR:$PATH" "$REAL_LAKE" build "$@" &
child_pid=$!
wait "$child_pid"
child_pid=""
