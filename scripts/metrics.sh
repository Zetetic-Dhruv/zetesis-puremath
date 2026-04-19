#!/bin/bash
# Canonical metrics for zetesis-puremath.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "{"
echo "  \"generated\": \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\","

if [ -d "ZPM" ] && [ -n "$(find ZPM -name '*.lean' -type f 2>/dev/null | head -1)" ]; then
  LINES=$(find ZPM -name "*.lean" | xargs wc -l | tail -1 | awk '{print $1}')
else
  LINES=0
fi
echo "  \"total_lines\": $LINES,"

FILES=$(find ZPM -name "*.lean" -type f 2>/dev/null | wc -l | tr -d ' ')
echo "  \"total_files\": $FILES,"

PUB_THM=$(grep -rn --include="*.lean" -E '^(theorem|lemma) ' ZPM/ 2>/dev/null | wc -l | tr -d ' ')
PRIV_THM=$(grep -rn --include="*.lean" -E '^private (theorem|lemma) ' ZPM/ 2>/dev/null | wc -l | tr -d ' ')
TOTAL_THM=$((PUB_THM + PRIV_THM))
echo "  \"public_theorems\": $PUB_THM,"
echo "  \"private_theorems\": $PRIV_THM,"
echo "  \"total_theorems\": $TOTAL_THM,"

DEFS=$(grep -rn --include="*.lean" -E '^(def |noncomputable def |private def |abbrev )' ZPM/ 2>/dev/null | wc -l | tr -d ' ')
echo "  \"definitions\": $DEFS,"

STRUCTS=$(grep -rn --include="*.lean" -E '^structure ' ZPM/ 2>/dev/null | wc -l | tr -d ' ')
echo "  \"structures\": $STRUCTS,"

SORRY_LINES=$(grep -rn --include="*.lean" -E '^[[:space:]]*sorry[[:space:]]*$' ZPM/ 2>/dev/null || true)
if [ -z "$SORRY_LINES" ]; then SORRY=0; else SORRY=$(echo "$SORRY_LINES" | wc -l | tr -d ' '); fi
echo "  \"sorry_tactics\": $SORRY"

echo "}"
