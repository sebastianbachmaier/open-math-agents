#!/usr/bin/env bash
# submit.sh <id>: prep.sh (official check, lease beat, push branch oma/<id> to the fork), then ask the fork's
# oma-open-pr workflow to open the upstream pull request by pushing a request file to branch pr-requests,
# wait for the PR to appear, and release the lease.
set -euo pipefail
cd /home/user/open-math-agents
ID="$1"; LID="$ID"; REASON=submitted
if [[ "$ID" =~ \.R[0-9]+$ ]] && [ -f "reductions/$ID.lean" ]; then LID="${ID%.R*}"; REASON=reduced; fi
if ! .oma/prep.sh "$ID" > "/tmp/prep-$$.log" 2>&1; then tail -5 "/tmp/prep-$$.log"; echo "PREP FAILED for $ID: nothing submitted"; exit 3; fi
tail -4 "/tmp/prep-$$.log" | grep -v '^https' || true
L=$(cat ".oma/leases/$LID")
OK=""
for a in 1 2 3 4 5; do
  WT=$(mktemp -d /tmp/claude-0/-home-user-open-math-agents/fe762f43-9f16-52e7-8a0c-449996367afb/scratchpad/req-XXXX)
  git fetch -q --depth 5 origin pr-requests
  git worktree add -q --detach "$WT" FETCH_HEAD
  printf 'ID=%s\nLEASE=%s\nPROBLEM=%s\nAGENT=%s\nMODEL=%s\n' "$ID" "$L" "$LID" "${OMA_AGENT:-claude-code}" "${OMA_MODEL:-unknown}" > "$WT/pr-requests/$ID.env"
  git -C "$WT" add pr-requests
  git -C "$WT" commit -q -m "request: open PR for $ID"
  if git -C "$WT" push -q origin HEAD:refs/heads/pr-requests 2>/dev/null; then OK=1; fi
  git worktree remove --force "$WT"
  [ -n "$OK" ] && break
  sleep $((a*3))
done
if [ -z "$OK" ]; then echo "REQUEST PUSH FAILED for $ID"; exit 7; fi
SHA=$(git rev-parse "oma/$ID"); PR=""
for t in $(seq 1 18); do
  sleep 10
  PR=$(git ls-remote upstream 'refs/pull/*/head' | grep "$SHA" | sed 's#.*pull/\([0-9]*\)/head#\1#' | head -1 || true)
  [ -n "$PR" ] && break
done
if [ -z "$PR" ]; then echo "NO PR YET for $ID after 3 minutes: check the fork's Actions tab"; exit 5; fi
echo "PR opened: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/$PR"
curl -sS -m 30 -X POST "https://lefttosolve.com/api/desk/release?lease=$L&reason=$REASON" || true; echo
rm -f ".oma/leases/$LID"
