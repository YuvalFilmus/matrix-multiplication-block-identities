#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
python3 scripts/check-frozen.py
python3 review/rectangular/guard-regression.py
python3 scripts/check-imports.py
python3 scripts/build-project.py
python3 scripts/check-abi.py
python3 scripts/check-statements.py
python3 scripts/check-rectangular.py
python3 scripts/check-helper-axioms.py
python3 scripts/check-rectangular-frontier.py
python3 scripts/check-imports.py
