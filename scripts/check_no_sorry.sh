#!/bin/bash
# Strict sorry check. Matches only standalone `sorry` tactic lines; ignores comments and identifiers.
# Tolerates empty trees (grep exits non-zero on zero matches, so we don't use pipefail).
set -u
cd "$(dirname "$0")/.."

MATCHES=$(grep -rn --include="*.lean" -E '^[[:space:]]*sorry[[:space:]]*$' ZPM/ 2>/dev/null || true)
if [ -n "$MATCHES" ]; then
  SORRY_COUNT=$(echo "$MATCHES" | wc -l | tr -d ' ')
  echo "ERROR: found $SORRY_COUNT standalone sorry tactic(s) in ZPM/:"
  echo "$MATCHES"
  exit 1
fi
echo "OK: 0 sorry tactics in ZPM/."
