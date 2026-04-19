#!/bin/bash
# Canonical metrics for zetesis-puremath. Tolerates empty or single-file trees.
set -u
cd "$(dirname "$0")/.."

# Enumerate all .lean files under the ZPM library.
ZPM_FILES=()
if [ -f "ZPM.lean" ]; then
  ZPM_FILES+=("ZPM.lean")
fi
if [ -d "ZPM" ]; then
  while IFS= read -r f; do
    [ -n "$f" ] && ZPM_FILES+=("$f")
  done < <(find ZPM -name "*.lean" -type f 2>/dev/null)
fi

FILES=${#ZPM_FILES[@]}

count_lines() {
  if [ "$FILES" -eq 0 ]; then echo 0; return; fi
  wc -l "${ZPM_FILES[@]}" 2>/dev/null | tail -1 | awk '{print $1}' || echo 0
}

count_matches() {
  local pattern="$1"
  if [ "$FILES" -eq 0 ]; then echo 0; return; fi
  local n
  n=$(grep -hE "$pattern" "${ZPM_FILES[@]}" 2>/dev/null | wc -l | tr -d ' ')
  echo "${n:-0}"
}

LINES=$(count_lines)
PUB_THM=$(count_matches '^(theorem|lemma) ')
PRIV_THM=$(count_matches '^private (theorem|lemma) ')
DEFS=$(count_matches '^(def |noncomputable def |private def |abbrev )')
STRUCTS=$(count_matches '^structure ')
SORRY=$(count_matches '^[[:space:]]*sorry[[:space:]]*$')

cat <<JSON
{
  "generated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "total_lines": $LINES,
  "total_files": $FILES,
  "public_theorems": $PUB_THM,
  "private_theorems": $PRIV_THM,
  "total_theorems": $((PUB_THM + PRIV_THM)),
  "definitions": $DEFS,
  "structures": $STRUCTS,
  "sorry_tactics": $SORRY
}
JSON
