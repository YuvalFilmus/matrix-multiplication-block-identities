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

## Main results in the manuscript

The PDF uses formal polynomial correctness, including over finite fields.
The links below lead to the corresponding **proved Lean statements**; the PDF
page numbers refer to the included manuscript. Square statements are in
`BlockIdentities.Square`, and rectangular statements in `BlockIdentities.Rectangular`.

| Manuscript result | PDF page | Lean statement |
| --- | --- | --- |
| Theorem 1.1: identities-to-exponent criterion | [2](source/manuscript.pdf#page=2) | [identities_to_exponent](BlockIdentities/Frozen/identities_to_exponent_v2.lean#L16) |
| Theorem 1.2: square bound | [5](source/manuscript.pdf#page=5) | [formalOmega_le_nine_quarters](BlockIdentities/Frozen/formalOmega_le_nine_quarters_v2.lean#L16), [omega_le_nine_quarters](BlockIdentities/Frozen/omega_le_nine_quarters_v2.lean#L16) |
| Proposition 2.4: general extraction | [9](source/manuscript.pdf#page=9) | [general_extraction](BlockIdentities/Frozen/general_extraction_v3.lean#L16) |
| Proposition 2.7: shared-leg value inequality | [11](source/manuscript.pdf#page=11) | [shared_leg_value_inequality](BlockIdentities/Frozen/shared_leg_value_inequality_v2.lean#L16) |
| Proposition 3.1: convolution degenerations | [15](source/manuscript.pdf#page=15) | [convolution_neighbor_degeneration](BlockIdentities/Frozen/convolution_neighbor_degeneration_v2.lean#L16), [convolution_tripling_degeneration](BlockIdentities/Frozen/convolution_tripling_degeneration_v2.lean#L16) |
| Theorem 5.1: oriented value bounded by asymptotic rank | [20](source/manuscript.pdf#page=20) | [oriented_value_rank](BlockIdentities/Rectangular/Frozen/oriented_value_rank.lean#L16) |
| Proposition 5.2: oriented-value properties | [21](source/manuscript.pdf#page=21) | [oriented_value_properties](BlockIdentities/Rectangular/Frozen/oriented_value_properties.lean#L16) |
| Proposition 5.3: oriented shared-leg inequality | [22](source/manuscript.pdf#page=22) | [oriented_shared_leg_entropy](BlockIdentities/Rectangular/Frozen/oriented_shared_leg_entropy.lean#L16) |
| Theorem 5.4: rectangular curve and dual exponent | [23](source/manuscript.pdf#page=23) | [formalRectangularOmega_curve](BlockIdentities/Rectangular/Frozen/formalRectangularOmega_curve.lean#L16), [formalAlpha_ge_half](BlockIdentities/Rectangular/Frozen/formalAlpha_ge_half.lean#L16) |
| Equation (5.15): angular constraint | [23](source/manuscript.pdf#page=23) | [support_angular_constraint](BlockIdentities/Rectangular/Frozen/support_angular_constraint.lean#L16) |
| Equation (5.16): general rectangular shape bound | [23](source/manuscript.pdf#page=23) | [formalShapeOmega_general_bound](BlockIdentities/Rectangular/Frozen/formalShapeOmega_general_bound.lean#L16) |
| Lemma A.1: fixed-overhead scalar descent | [27](source/manuscript.pdf#page=27) | [scalar_descent](BlockIdentities/Frozen/scalar_descent_v2.lean#L16) |

The explicit algorithmic cost versions are [formal_matrix_multiplication_cost_le](BlockIdentities/Frozen/formal_matrix_multiplication_cost_le_v2.lean#L16)
for square multiplication and [formal_rectangular_cost_le](BlockIdentities/Rectangular/Frozen/formal_rectangular_cost_le.lean#L16)
for rectangular multiplication. Each includes every positive exponent allowance.
The corresponding original functional rectangular results are
[rectangularOmega_curve](BlockIdentities/Rectangular/Frozen/rectangularOmega_curve.lean#L16) and [rectangular_alpha_ge_half](BlockIdentities/Rectangular/Frozen/rectangular_alpha_ge_half.lean#L16).

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
