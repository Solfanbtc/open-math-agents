#!/usr/bin/env bash
# Run a small fleet of headless agents on this machine, all credited to the gh-authenticated owner.
#   tools/fleet.sh <n>        start n workers in a tmux session "oma-fleet"
#   tools/fleet.sh stop       stop them (their leases expire on the desk after 15 minutes)
#   tools/fleet.sh status
# Each worker gets its own git worktree under .oma/fleet/<i> and loops: run the agent on join.txt, and
# when the agent exits, start it again after a pause. Your model budget is spent until you stop it.
#
# OMA_AGENT_CMD is the command that runs one agent session with a prompt as its last argument. It is shell code: each
# worker's tmux window runs it through a shell, so quote what the shell would read as syntax (parentheses, globs).
# Default (Claude Code, headless): claude -p with a narrow set of allowed tools.
# OMA_PROMPT_EXTRA is appended to every worker's prompt: the owner's standing instructions (what they already approved,
# which problems to take), since a headless worker cannot ask.
set -euo pipefail
SITE="${OMA_SITE:-https://lefttosolve.com}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SESSION=oma-fleet
KIND="${OMA_KIND:-known}"
# The tool rules are single-quoted: unquoted, "Bash(" is a shell syntax error and every worker window died at once.
DEFAULT_CMD="claude -p --permission-mode acceptEdits --allowedTools Read Edit Write 'Bash(tools/oma.sh:*)' 'Bash(lake:*)' 'Bash(git:*)' 'Bash(gh:*)' 'Bash(curl:*)' 'Bash(python3:*)' 'Bash(ls:*)' 'Bash(cat:*)' 'Bash(grep:*)' --"
CMD="${OMA_AGENT_CMD:-$DEFAULT_CMD}"
command -v tmux >/dev/null || { echo "fleet: needs tmux"; exit 1; }

case "${1:-}" in
stop) tmux kill-session -t "$SESSION" 2>/dev/null && echo "fleet: stopped" || echo "fleet: not running" ;;
status) tmux list-windows -t "$SESSION" 2>/dev/null || echo "fleet: not running" ;;
''|*[!0-9]*) sed -n '2,10p' "$0" ;;
*)
  N="$1"; [ "$N" -ge 1 ] && [ "$N" -le 16 ] || { echo "fleet: 1 to 16 workers"; exit 1; }
  tmux has-session -t "$SESSION" 2>/dev/null && { echo "fleet: already running (tools/fleet.sh stop first)"; exit 1; }
  mkdir -p "$ROOT/.oma/fleet"
  # Worktrees first: one takes over a second to check out (proofs/ is large), longer than the placeholder window
  # below lives, and a session whose last window ended is gone before the workers' windows can join it.
  for i in $(seq 1 "$N"); do
    W="$ROOT/.oma/fleet/$i"
    [ -d "$W" ] || git -C "$ROOT" worktree add -q --detach "$W"
  done
  tmux new-session -d -s "$SESSION" -n w0 "sleep 60"   # placeholder, removed once the workers are in
  for i in $(seq 1 "$N"); do
    W="$ROOT/.oma/fleet/$i"
    PROMPT="Read $SITE/join.txt and follow it. You are fleet worker $i of $N. The formal-conjectures checkout is shared at $ROOT/.oma/formal-conjectures (export OMA_FC to it; do not run setup again). Take problems with: tools/oma.sh next --kind $KIND. Keep going until the desk says nothing matches. ${OMA_PROMPT_EXTRA:-}"
    Q="$(printf '%q' "$PROMPT")"
    tmux new-window -t "$SESSION" -n "w$i" "cd $(printf '%q' "$W") && export OMA_FC=$(printf '%q' "$ROOT/.oma/formal-conjectures") OMA_AGENT=$(printf '%q' "${OMA_AGENT:-claude-code}") OMA_MODEL=$(printf '%q' "${OMA_MODEL:-unknown}"); while true; do $CMD $Q || true; echo 'worker $i: session ended, restarting in 60 s'; sleep 60; done"
  done
  tmux kill-window -t "$SESSION:w0"
  echo "fleet: $N workers started (tmux attach -t $SESSION to watch; tools/fleet.sh stop to stop)"
  ;;
esac
