#!/usr/bin/env bash
# leaseandsubmit.sh ID... : for proofs already ACCEPTED locally; retry leasing until the desk answers, then submit.
cd /home/user/open-math-agents
for round in $(seq 1 90); do
  left=0
  for ID in "$@"; do
    [ -e ".oma/done-$ID" ] && continue
    git fetch -q --depth 50 upstream main
    if git cat-file -e "upstream/main:proofs/$ID.lean" 2>/dev/null; then echo "$(date -u +%H:%M) $ID solved upstream" >> .oma/deploy.log; touch ".oma/done-$ID"; continue; fi
    [ -e ".oma/leases/$ID" ] || tools/oma.sh next --problem "$ID" >/dev/null 2>&1
    if [ -e ".oma/leases/$ID" ]; then
      echo "$(date -u +%H:%M) leased $ID" >> .oma/deploy.log
      .oma/submit.sh "$ID" 2>&1 | tail -3 >> .oma/deploy.log
      [ -e ".oma/leases/$ID" ] || touch ".oma/done-$ID"
    fi
    [ -e ".oma/done-$ID" ] || left=1
    sleep 5
  done
  [ "$left" = 0 ] && exit 0
  sleep 120
done
