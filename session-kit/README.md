# Session kit (backup of helper files from the cloud session)

Not part of any submission. These live in `.oma/` while working:

- `AGENT_RULES.md`, `OPEN_RULES.md`: instructions given to proof subagents.
- `prep.sh <id>`: re-runs the official check, confirms the lease, puts the single proof file on branch `oma/<id>` cut from upstream main, pushes it to the fork and prints a prefilled pull-request link.
- `submit.sh <id>`: prep.sh, then pushes a request file to the fork branch `pr-requests`, which makes the fork workflow `oma-open-pr` open the upstream pull request with the secret OMA_PR_TOKEN; waits for the PR and releases the lease.
- `beatloop.sh`: keeps held leases alive.
- `refresh.sh`: re-takes lapsed leases and drops problems merged by others.

Paths inside the scripts assume the repository is checked out at /home/user/open-math-agents with remotes
`origin` = the fork and `upstream` = GuillaumeBAUD-coder/open-math-agents.
