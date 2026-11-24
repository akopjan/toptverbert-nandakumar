#!/usr/bin/env bash
# Exact selection used for the final model certificate; requires the pinned
# toolchain on PATH. The export is a large temporary artifact outside the ZIP.
set -euo pipefail
project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$project_dir"
if (( $# != 1 )); then
  echo 'Usage: run-selected-models.sh /absolute/fresh-export.ndjson' >&2
  exit 2
fi
cp scripts/verify-selected-kernels.py verification/model-kernels/verifier-used.py
python3 scripts/verify-selected-kernels.py Audit \
  AkopyanResearch.PairOrbit.card_labelsOverPair \
  AkopyanResearch.PairL2Deformation.strong_deformation_retraction \
  --definition-target AkopyanResearch.TargetFiberModel.homotopyFiberHomeomorph \
  --definition-target AkopyanResearch.PairNormalModel.jointQuotientContinuousEquiv \
  --definition-target AkopyanResearch.SingleCoordinateModel.coordinatesHomeomorph \
  --definition-target AkopyanResearch.PairPathCoordinates.homeomorph \
  --definition-target AkopyanResearch.TargetCollapseModel.pairTargetSphereHomeomorph \
  --proof-module AkopyanResearch.Completion.PairOrbit \
  --proof-module AkopyanResearch.Completion.PairL2Deformation \
  --proof-module AkopyanResearch.Completion.TargetFiberModel \
  --proof-module AkopyanResearch.Completion.PairNormalModel \
  --proof-module AkopyanResearch.Completion.SingleCoordinateModel \
  --proof-module AkopyanResearch.Completion.PairPathCoordinates \
  --proof-module AkopyanResearch.Completion.TargetCollapseModel \
  --definition AkopyanResearch.TargetFiberModel.HomotopyFiber \
  --definition AkopyanResearch.PairNormalModel.commonEquality \
  --definition AkopyanResearch.PairL2Deformation.Balanced2 \
  --output-dir verification/model-kernels \
  --export-file "$1"
