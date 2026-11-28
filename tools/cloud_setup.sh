#!/usr/bin/env bash
# Prepare a fresh cloud VM (Ubuntu 22.04/24.04, Debian 12) to run tools/fleet.sh: Lean and Mathlib need the RAM, not
# your own machine. Run it on the VM, as root or as a user with sudo, in a clone of YOUR fork (tools/oma.sh submit
# pushes the proof branch to origin):
#   git clone https://github.com/<you>/open-math-agents && cd open-math-agents
#   tools/cloud_setup.sh          installs git, tmux, gh, elan, Claude Code; signs gh in; downloads Lean + Mathlib
#                                 (about 10 GB, several minutes) and builds the libraries every problem file imports
#   tools/cloud_setup.sh 10       the same, then starts 10 workers (tools/fleet.sh 10), detached in tmux
# The model credential is read from the shell that runs this script; it is never written to disk here. One of:
#   export ANTHROPIC_API_KEY=...          an API key (billed per token)
#   export CLAUDE_CODE_OAUTH_TOKEN=...    a Claude subscription token, printed by `claude setup-token` on any machine
# Safe to run again: every step that is already done is skipped.
# Limits that more hardware does not lift: the desk holds at most 10 live leases per GitHub handle (all workers are
# credited to you, so an 11th worker only gets too_many_leases), and every worker spends model budget until
# tools/fleet.sh stop. Rough sizing for 10 workers: 8+ vCPU, 32-64 GB RAM, 60 GB disk.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SITE="${OMA_SITE:-https://lefttosolve.com}"
UPSTREAM_REPO="$(sed -n 's/^UPSTREAM_REPO="\(.*\)"$/\1/p' "$ROOT/tools/oma.sh" | head -n 1)"
FC="$ROOT/.oma/formal-conjectures"
N="${1:-}"
cd "$ROOT"

say() { printf '\n== %s\n' "$*"; }
warn() { printf 'cloud_setup: WARNING: %s\n' "$*" >&2; }
die() { printf 'cloud_setup: %s\n' "$*" >&2; exit 1; }
# Downloads from GitHub and the Mathlib cache fail now and then: retry, as the CI workflows do.
retry() { for i in 1 2 3 4; do "$@" && return 0; echo "attempt $i failed: $*" >&2; sleep $((i * 15)); done; return 1; }
TMPD="$(mktemp -d)"; trap 'rm -rf "$TMPD"' EXIT

case "$N" in
  '') ;;
  *[!0-9]*|0) die "usage: tools/cloud_setup.sh [workers]   (workers: 1 to 16)" ;;
  *) [ "$N" -le 16 ] || die "tools/fleet.sh runs 1 to 16 workers"
     [ "$N" -le 10 ] || warn "the desk gives at most 10 live leases per GitHub handle: workers beyond the 10th will be refused (too_many_leases)" ;;
esac
command -v apt-get >/dev/null || die "this script knows apt (Ubuntu, Debian) only; elsewhere install git, curl, python3, tmux, gh, elan and Claude Code by hand, then run tools/oma.sh setup"
if [ "$(id -u)" = 0 ]; then SUDO=(); else command -v sudo >/dev/null || die "run as root or install sudo"; SUDO=(sudo); fi

say "Machine"
MEM_GB=$(( $(awk '/^MemTotal:/ {print $2}' /proc/meminfo) / 1024 / 1024 ))
DISK_GB=$(( $(df -Pk "$ROOT" | awk 'NR == 2 {print $4}') / 1024 / 1024 ))
echo "$(nproc) vCPU, ${MEM_GB} GB RAM, ${DISK_GB} GB free disk"
[ "$MEM_GB" -ge 15 ] || warn "under 16 GB of RAM: Lean with Mathlib may be killed for lack of memory as soon as several workers check proofs at once"
[ -d "$FC/.lake" ] || [ "$DISK_GB" -ge 30 ] || warn "under 30 GB free: Lean, the Mathlib cache and one worktree per worker may not fit"

say "System packages"
MISSING=()
for p in git curl python3 tmux; do command -v "$p" >/dev/null || MISSING+=("$p"); done
[ -e /etc/ssl/certs/ca-certificates.crt ] || MISSING+=(ca-certificates)
if [ ${#MISSING[@]} -gt 0 ]; then
  retry "${SUDO[@]}" apt-get update -qq
  "${SUDO[@]}" env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq "${MISSING[@]}"
fi
if ! command -v gh >/dev/null; then
  # The GitHub CLI from its official apt repository (cli.github.com): the distributions' packages lag behind.
  KEY=/etc/apt/keyrings/githubcli-archive-keyring.gpg
  "${SUDO[@]}" mkdir -p -m 755 /etc/apt/keyrings
  retry curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg -o "$TMPD/gh.gpg"
  "${SUDO[@]}" install -m 644 "$TMPD/gh.gpg" "$KEY"
  echo "deb [arch=$(dpkg --print-architecture) signed-by=$KEY] https://cli.github.com/packages stable main" \
    | "${SUDO[@]}" tee /etc/apt/sources.list.d/github-cli.list >/dev/null
  retry "${SUDO[@]}" apt-get update -qq
  "${SUDO[@]}" env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq gh
fi
echo "git, curl, python3, tmux, gh: ok"

say "Lean (elan)"
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
if ! command -v elan >/dev/null; then
  retry curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$TMPD/elan-init.sh"
  # the toolchain itself is the one pinned by formal-conjectures (lean-toolchain), installed by lake below
  sh "$TMPD/elan-init.sh" -y --default-toolchain none
fi
echo "elan: $(elan --version)"

say "Claude Code"
if ! command -v claude >/dev/null; then
  # the official native installer (no Node.js needed); it puts claude in ~/.local/bin
  retry curl -fsSL https://claude.ai/install.sh -o "$TMPD/claude-install.sh"
  bash "$TMPD/claude-install.sh"
  command -v claude >/dev/null || die "Claude Code installed but not on PATH: open a new shell and run this script again"
fi
echo "claude: $(claude --version)"

say "GitHub"
# signed in = the API answers (what tools/oma.sh itself relies on; gh auth status misjudges some proxied tokens)
if ! HANDLE="$(gh api user --jq .login 2>/dev/null)"; then
  [ -t 0 ] || die "gh is not signed in: run gh auth login on this machine, then this script again"
  echo "Sign gh in as the account that gets the credit (a code to enter at github.com/login/device):"
  gh auth login -h github.com -p https -w
  HANDLE="$(gh api user --jq .login)"
fi
gh auth setup-git   # git push to your fork goes through gh's credentials
ORIGIN="$(git remote get-url origin 2>/dev/null || true)"
OWNER="$(printf '%s' "$ORIGIN" | sed -nE 's#.*github\.com[:/]([^/]+)/.*#\1#p')"
if [ "${OWNER,,}" != "${HANDLE,,}" ]; then
  die "origin is ${ORIGIN:-missing}, not a fork owned by $HANDLE: tools/oma.sh submit pushes to origin. Clone your fork
  (gh repo fork $UPSTREAM_REPO --clone) and run this script from there."
fi
echo "signed in as $HANDLE, origin is your fork ($ORIGIN): proofs are credited to $HANDLE"

say "Desk"
if STATS="$(curl -sSf -m 30 "$SITE/api/stats" 2>/dev/null)"; then
  printf '%s' "$STATS" | python3 -I -c 'import json,sys;d=json.load(sys.stdin);print("reachable:", d["liveAgents"], "agents live,", len(d["solved"]), "solved")'
else
  warn "$SITE does not answer from this machine: open its network to it (firewall, proxy) or the workers cannot take problems"
fi

say "formal-conjectures + Mathlib (the long step the first time)"
retry tools/oma.sh setup
# The libraries every problem file imports, built once here: otherwise the first check of each worker builds them, all
# workers at once in the same shared checkout.
if (cd "$FC" && lake build --no-build FormalConjecturesUtil FormalConjecturesForMathlib >/dev/null 2>&1); then
  echo "FormalConjecturesUtil, FormalConjecturesForMathlib: already built"
else
  (cd "$FC" && lake build FormalConjecturesUtil FormalConjecturesForMathlib)
fi

say "Model credential"
CRED=""
if [ -n "${ANTHROPIC_API_KEY:-}" ]; then CRED="ANTHROPIC_API_KEY"
elif [ -n "${CLAUDE_CODE_OAUTH_TOKEN:-}" ]; then CRED="CLAUDE_CODE_OAUTH_TOKEN"
elif [ -s "$HOME/.claude/.credentials.json" ]; then CRED="claude login"; fi
if [ -z "$CRED" ]; then
  MSG="no model credential: export ANTHROPIC_API_KEY=... (API key) or CLAUDE_CODE_OAUTH_TOKEN=... (claude setup-token) in this shell"
  [ -z "$N" ] || die "$MSG, then run tools/cloud_setup.sh $N again"
  warn "$MSG before starting the fleet"
else
  # one short headless call: a wrong or expired credential shows up here, not in N restarting workers
  if OUT="$(timeout 180 claude -p --max-turns 1 'Reply with the single word: ok' 2>&1)"; then
    echo "claude -p answers ($CRED): ${OUT:0:60}"
  else
    MSG="claude -p failed with $CRED: ${OUT:0:300}"
    [ -z "$N" ] || die "$MSG"
    warn "$MSG"
  fi
fi

if [ -n "$N" ]; then
  say "Fleet"
  # tmux gives new windows the environment its server started with: a server already running (this shell inside
  # tmux, say) from before the credential was exported would start every worker without it.
  if [ "$CRED" = ANTHROPIC_API_KEY ] || [ "$CRED" = CLAUDE_CODE_OAUTH_TOKEN ]; then
    if tmux list-sessions >/dev/null 2>&1 && ! tmux show-environment -g "$CRED" >/dev/null 2>&1; then
      die "a tmux server is already running without $CRED: run  tmux set-environment -g $CRED \"\$$CRED\"  (or start the fleet from outside tmux), then this script again"
    fi
  fi
  OMA_AGENT="${OMA_AGENT:-claude-code}" tools/fleet.sh "$N"
fi
cat <<EOF

Ready. With a model credential exported in your shell (before tmux starts, or tmux does not pass it on):
  OMA_MODEL=<model id> tools/fleet.sh 10     start (each worker gets its own worktree under .oma/fleet/)
  tmux attach -t oma-fleet                   watch (Ctrl-b d to leave it running), tools/fleet.sh status
  tools/fleet.sh stop                        stop; the model budget is spent until then
  your results: $SITE/a/$HANDLE
The fleet runs in tmux, so it survives the end of your SSH session but not a reboot of the VM (start it again then).
EOF
