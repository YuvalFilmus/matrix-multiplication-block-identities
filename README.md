# Matrix multiplication from block identities

[![Build and verify](https://github.com/YuvalFilmus/matrix-multiplication-block-identities/actions/workflows/verify.yml/badge.svg)](https://github.com/YuvalFilmus/matrix-multiplication-block-identities/actions/workflows/verify.yml)

Lean formalization of **Matrix multiplication from block identities**, proving
square and rectangular matrix multiplication bounds over **every field**,
including finite fields. The manuscript is included as [LaTeX](source/manuscript.tex)
and [PDF](source/manuscript.pdf), with its [bibliography](source/matrix-multiplication.bib).

For the formal polynomial exponent, the results include

```math
\omega_F \leq \frac{9}{4},
\qquad \alpha_F \geq \frac{1}{2}.
```

```math
\omega_F(1,k,1) \leq
\begin{cases}
2, & 0 \leq k \leq \frac{1}{2}, \\
1+k+\frac{1}{4k}, & k > \frac{1}{2}.
\end{cases}
```

The cost theorems produce division-free algorithms with formal polynomial
correctness and cost at most $C n^{b+\varepsilon}$ for every $\varepsilon>0$,
with one $C>0$ valid for all $n\geq1$. The same upper bounds are established
for Navot's original functional exponents; equality of formal and functional
exponents is not assumed over finite fields.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3; Git and internet
access are needed for the first dependency/cache download. From this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build BlockIdentities
bash scripts/check.sh
```

The toolchain is **Lean 4.35.0**. Mathlib is pinned to
`ccbef15ebdb41c2addfac682131f83c75904c3c1`; the lockfile pins transitive dependencies.
Navot's adapted source is vendored as a relative path dependency, so there are
no private repositories or machine-specific paths. Do not run `lake update` to
reproduce this snapshot. Run one Lake build at a time.

The full checker also builds all owned helper modules, compares all 35 exact
elaborated theorem types and approved source headers, checks the 35 sealed
exports plus 44 square and 321 rectangular helper axiom closures, tests the
import-quarantine guard, and checks the 306-module import boundary. Generated
probe files go in ignored `work/`; check outputs go in `review/`.

GitHub Actions runs the full build and verification on every push and pull
request, and supports manual runs. It uses the pinned toolchain, caches build
artifacts, and uploads the verification log, including when checks fail.

The manuscript can be rebuilt with a TeX installation containing its packages:

```sh
cd source
latexmk -pdf manuscript.tex
```

See [release verification](VERIFICATION.md) for the source inventory, review
and isolated-build evidence.

## Lean API

```lean
import BlockIdentities -- both phases
-- or: import BlockIdentities.Rectangular
```

Square endpoints in namespace `BlockIdentities.Square`:

- `formalOmega_le_nine_quarters`
- `formal_matrix_multiplication_cost_le`
- `omega_le_nine_quarters`

Rectangular endpoints in namespace `BlockIdentities.Rectangular`:

- `formalShapeOmega_general_bound`
- `formalRectangularOmega_curve`
- `formal_rectangular_cost_le`
- `rectangularOmega_curve`
- `formalAlpha_ge_half`
- `rectangular_alpha_ge_half`

All 17 square and 18 rectangular targets are proved. No owned Lean declarations
contain `sorry`, `admit`, or custom axioms. Audited axiom closures use only
`propext`, `Classical.choice`, and `Quot.sound`. The [manifest](review/frozen-manifest.json)
binds the approved statements, semantic definitions and exact ABI hashes.
Review-only `.lean.txt` headers and isolated guard fixtures are not library proofs.

The proof develops finite polynomial identities, cancellation, extraction,
entropy and convolution profiles, and scalar descent. It reuses Navot/OpenAI
arithmetic programs, finite constructions, rank and interpolation APIs. The
new proof's import closure excludes their existing final 9/4, spectral,
Character, AllFields and RankBound proofs. Unused vendored results belong to
upstream, rather than being new claims of this project.

The finite square bound uses the direct row telescope; a generic finite-graph
criterion is also proved. The continuous rectangular profiles and laws needed
for the angular argument are proved. A separate ceiling-limit characterization
of those profiles is outside the claimed API. This is a formalization of the
listed targets, not a claim that every statement in the manuscript or cited
papers has been formalized.

## Sources, attribution and licenses

Code: [Apache 2.0](LICENSE). Manuscript copyright remains with the author; no
manuscript license is inferred from the code license. See [NOTICE](NOTICE).

This development builds on [Navot's all-fields extension](https://github.com/selanavot/matrix-multiplication-all-fields)
of OpenAI's formalization. Its baseline revision is
`08481ef22bca7dc9ffba091083b7c1e81e537220`; original licenses and notices are retained.
The auxiliary rectangular source by Przemysław Uznański is included under its
CC BY 4.0 license, with [version and provenance](source/rectangular/uznanski-v2/provenance.json).

This public repository starts with a clean source export. Private development
history, scratch files, generated caches, and campaign correspondence are excluded.
Subsequent public revisions use normal forward commits.
