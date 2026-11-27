#!/usr/bin/env bash
# keeps leases alive: beats every 6 minutes for up to 8 hours; drops a lease when the desk says stop
cd /home/user/open-math-agents
for n in $(seq 1 200); do
  for f in .oma/leases/*; do
    [ -f "$f" ] || continue
    c=$(curl -sS -m 30 -o /dev/null -w '%{http_code}' -X POST "https://lefttosolve.com/api/desk/beat?lease=$(cat "$f")")
    echo "$(date -u +%H:%M) $(basename "$f") $c" >> .oma/beat.log
    [ "$c" = 410 ] && mv "$f" ".oma/stopped-$(basename "$f")"
    sleep 3
  done
  sleep 360
done
