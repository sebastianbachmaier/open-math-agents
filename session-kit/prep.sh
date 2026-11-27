#!/usr/bin/env bash
# prep.sh <id>: re-check, confirm lease, put the single proof file on branch oma/<id> cut from upstream/main, push to the fork, print the PR link
set -euo pipefail
cd /home/user/open-math-agents
ID="$1"; F=proofs/$ID.lean; [[ "$ID" =~ \.R[0-9]+$ ]] && [ -f "reductions/$ID.lean" ] && F=reductions/$ID.lean
tools/oma.sh check "$ID" 2>&1 | tail -2
LID="$ID"; [[ "$F" == reductions/* ]] && LID="${ID%.R*}"
L=$(cat .oma/leases/$LID)
C=$(curl -sS -m 30 -o /dev/null -w '%{http_code}' -X POST "https://lefttosolve.com/api/desk/beat?lease=$L"); echo "beat $C"; [ "$C" = 200 ]
git fetch -q --depth 50 upstream main
if git cat-file -e "upstream/main:$F" 2>/dev/null; then echo "ALREADY ON MAIN: $F"; exit 4; fi
WT=/tmp/claude-0/-home-user-open-math-agents/fe762f43-9f16-52e7-8a0c-449996367afb/scratchpad/wt-$$
git worktree add -q -B "oma/$ID" "$WT" upstream/main
cp "$F" "$WT/$F"; git -C "$WT" add "$F"
git -C "$WT" commit -q -m "proof: $ID

Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PFXeZHwoF1GJ9YxkFJBC9K"
# guard: the branch must differ from upstream main by exactly the one proof file (no workflow or other files)
CHANGED=$(git -C "$WT" diff --name-only upstream/main HEAD)
if [ "$CHANGED" != "$F" ]; then echo "REFUSING TO PUSH: branch would change: $CHANGED"; git worktree remove --force "$WT"; exit 6; fi
git -C "$WT" -c push.negotiate=true push -q -f -u origin "oma/$ID" 2>&1 | tail -1
git -C "$WT" show --stat --oneline HEAD | tail -1
git worktree remove --force "$WT"
python3 -I -c '
import urllib.parse,sys,os
i,l,t=sys.argv[1],sys.argv[2],sys.argv[3]
body="Lease: %s\nAgent: %s\nModel: %s\n\nProblem: https://lefttosolve.com/p/%s\nChecked locally with tools/oma.sh check."%(l,os.environ.get("OMA_AGENT","claude-code"),os.environ.get("OMA_MODEL","unknown"),t)
print("https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...sebastianbachmaier:"+urllib.parse.quote("oma/"+i)+"?expand=1&title="+urllib.parse.quote(i)+"&body="+urllib.parse.quote(body))' "$ID" "$L" "$LID"
