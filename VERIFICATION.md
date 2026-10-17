# Release verification

The public export preserves all 266 owned Lean files byte for byte from the
completed square and rectangular development. All 35 approved theorem types,
their ABI hashes, and seven frozen semantic modules are unchanged.

Independent static release review by a separate agent passed: mathematical byte fidelity,
proof status, dependency paths, release hygiene, manuscript/bibliography
identity, and licensing/attribution scope. Two packaging findings were resolved:
the retained upstream provenance is marked historical, and the unavailable
ComparatorAudit target is omitted. These changes affect no mathematical source.

The source inventory and SHA256 hashes are in
[review/release-source-hashes.json](review/release-source-hashes.json).
The included PDF is the canonical companion of the exact worked LaTeX file;
its title, 35 pages, rectangular section and first-page rendering were checked.
The bibliography is unchanged.

## Fresh-checkout verification: PASS (2026-10-17)

A separate Git clone of the proposed release began with empty owned-project
and vendored-dependency build directories. Only third-party package caches were
reused; all nine cached package Git revisions were checked against the lockfile.
No project or Navot build artifacts were copied.

`LEAN_NUM_THREADS=1 bash scripts/check.sh` completed successfully:

- Complete build: 9366 jobs, including both public import modules.
- All 35 original elaborated theorem ABI hashes unchanged.
- All 17 square headers and 18 rectangular approved types checked.
- All sealed export axiom checks passed, plus 44 square helper and 321
  rectangular frontier closures; only `propext`, `Classical.choice`, `Quot.sound`.
- Zero drafts, unregistered proof holes, or draft-import violations.
- All eight isolated guard regression cases passed.
- Import boundary: 306 modules; no existing final exponent or character proof.
- Module checks: all 400 shipped Lean files passed.

The final release's Lean source, Lake configurations and pins were compared
byte for byte with this checked clone. Later release edits are documentation,
provenance, line-ending attributes and verification evidence only.

[Complete checker output](review/release-check.txt),
[exact ABI output](review/elaborated-abi.txt),
[square header/axiom output](review/statement-elaboration.txt),
[rectangular interface/axiom output](review/rectangular/current-interface-check.txt),
[rectangular frontier axioms](review/rectangular/frontier-axioms.txt).
Checker diagnostics retain existing linter/deprecation warnings. Published text
logs normalize trailing whitespace and replace the absolute checkout prefix
in diagnostic locations with a relative path; theorem and axiom output is unchanged.

The source LaTeX retains its approved bytes, including inherited whitespace;
it and the bibliography are unchanged. All 61 manuscript citation keys resolve
in the included bibliography. Publication is authorized by the author.
