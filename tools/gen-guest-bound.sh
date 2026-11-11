#!/usr/bin/env bash
# Regenerate submission/InitECandidate/Solver/GuestBound/Fns/ from the guest AST,
# the loop checks and GuestBound/manual-loops.txt. The generator runs while
# Tools/GenGuestBound.lean is elaborated, so a fresh stamp forces Lake to rerun it.
set -euo pipefail
cd "$(dirname "$0")/.."
printf '/-! Written by tools/gen-guest-bound.sh to force a rerun of the generator. -/\ndef Tools.GenGuestBound.stamp : String := "%s"\n' "$(date -u +%Y%m%dT%H%M%S%N)" > Tools/GenGuestBoundStamp.lean
rm -rf submission/InitECandidate/Solver/GuestBound/Fns
lake build Tools.GenGuestBound 2>&1 | grep -v '^✔\|^trace' | grep -v '^$'
