#!/usr/bin/env bash
# Poll the desk for pre-proved steps (map: ID bodyfile); once one is registered and unsolved, lease, check, submit.
G=/tmp/claude-0/-home-user-open-math-agents/fe762f43-9f16-52e7-8a0c-449996367afb/scratchpad/r5/E/gen
cd /home/user/open-math-agents
cp $G/map.txt /tmp/autodeploy.todo
for round in $(seq 1 120); do
  [ -s /tmp/autodeploy.todo ] || exit 0
  while read -r ID BODY; do
    C=$(curl -sS -m 20 -o /tmp/ad.json -w '%{http_code}' "https://lefttosolve.com/api/problems/$ID")
    sleep 3
    [ "$C" = 200 ] || continue
    echo "$(date -u +%H:%M) registered $ID" >> .oma/deploy.log
    OUT=$(bash $G/deploy.sh "$ID" "$G/$BODY" 2>&1 | tail -4); echo "$OUT" >> .oma/deploy.log
    if echo "$OUT" | grep -q 'VERDICT accepted'; then .oma/submit.sh "$ID" 2>&1 | tail -2 >> .oma/deploy.log
    elif echo "$OUT" | grep -q NO_LEASE; then continue
    elif [ -e ".oma/leases/$ID" ]; then curl -sS -m 30 -X POST "https://lefttosolve.com/api/desk/release?lease=$(cat .oma/leases/$ID)&reason=other" >> .oma/deploy.log; rm -f ".oma/leases/$ID" "proofs/$ID.lean"; fi
    grep -v "^$ID " /tmp/autodeploy.todo > /tmp/autodeploy.tmp; mv /tmp/autodeploy.tmp /tmp/autodeploy.todo
  done < <(cat /tmp/autodeploy.todo)
  sleep 240
done
