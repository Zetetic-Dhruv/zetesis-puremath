#!/bin/bash
# Strict sorry check. Matches only standalone `sorry` tactic lines; ignores comments and identifiers.
set -euo pipefail
cd "$(dirname "$0")/.."

SORRY_COUNT=$(grep -rn --include="*.lean" -E '^[[:space:]]*sorry[[:space:]]*$' ZPM/ 2>/dev/null | wc -l | tr -d ' ')
if [ "$SORRY_COUNT" -gt 0 ]; then
  echo "ERROR: found $SORRY_COUNT standalone sorry tactic(s) in ZPM/:"
  grep -rn --include="*.lean" -E '^[[:space:]]*sorry[[:space:]]*$' ZPM/
  exit 1
fi
echo "OK: 0 sorry tactics in ZPM/."
