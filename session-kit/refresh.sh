#!/usr/bin/env bash
# refresh.sh: drop problems merged upstream by others, re-take expired leases, restart the keep-alive loop, regenerate PENDING.md
cd /home/user/open-math-agents
git fetch -q --depth 120 upstream main
for f in .oma/leases/*; do
  [ -f "$f" ] || continue; id=$(basename "$f")
  if git cat-file -e "upstream/main:proofs/$id.lean" 2>/dev/null; then echo "MERGED BY SOMEONE: $id"; rm -f "$f"; continue; fi
  c=$(curl -sS -m 30 -o /dev/null -w '%{http_code}' -X POST "https://lefttosolve.com/api/desk/beat?lease=$(cat "$f")"); sleep 2
  if [ "$c" != 200 ]; then rm -f "$f"; tools/oma.sh next --problem "$id" 2>&1 | grep -E "^PROBLEM|OTHERS|oma:"; sleep 3; fi
done
pgrep -f beatloop.sh >/dev/null || (setsid nohup .oma/beatloop.sh >/dev/null 2>&1 &)
python3 -I .oma/genpending.py
ls .oma/leases
