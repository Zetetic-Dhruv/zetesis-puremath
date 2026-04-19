#!/bin/bash
# Regenerates Verification/ChallengeCrown.lean, Verification/SolutionCrown.lean,
# and premise/final.json from Verification/Headlines.lean using the
# verification_extract lean_exe.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build verification_extract
BIN=".lake/build/bin/verification_extract"
if [ ! -x "$BIN" ]; then
  echo "ERROR: verification_extract binary not found at $BIN"
  exit 1
fi

# lake env sets LEAN_PATH so the exe can find ZPM.olean at runtime.
lake env "$BIN" challenge > Verification/ChallengeCrown.lean
lake env "$BIN" solution  > Verification/SolutionCrown.lean
lake env "$BIN" premise   > premise/final.json

echo "Regenerated:"
echo "  Verification/ChallengeCrown.lean"
echo "  Verification/SolutionCrown.lean"
echo "  premise/final.json"
