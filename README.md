# Chen–Dalang moments and growth indices in Lean

Selected results for the nonlinear stochastic heat equation with rough initial
conditions: explicit resolvents, full nonnegative-data p = 2 existence and
uniqueness, exact quasilinear second moments, and growth indices.

## What is proved

The selected entry contains 16 Challenge statements. It includes full random-field
solution existence, L2 continuity of the actual integral, almost-sure uniqueness
separately at each positive-time space point, proved second-moment inputs, the
adopted p = 2 growth bounds and exact transition, and lower-growth conclusions
for every real p at least 2. Diffusivity remains general and positive.

All 216 declared claims remain in the native audit; 200 are supporting
declarations rather than separately compared entry claims. The actual noise,
integral and nonzero-Dirac solution fixture establishes nonvacuity.

[What is proved](docs/what-is-proved.md) gives a plain-language account and the
exact Lean header of every selected statement. Committed source-bound receipts
identify the verified snapshot; this repository is a substantive proof
development, not a thin wrapper around private proof code.

> [!IMPORTANT]
> Signed-data existence, higher-p upper bounds, two-point stochastic formulas,
> pathwise continuity and complete verification of the paper are not claimed.

## Paper and source

Le Chen and Robert C. Dalang, *Moments and growth indices for the nonlinear
stochastic heat equation with rough initial conditions*, Ann. Probab. 43(6)
(2015), 3006–3051, [doi:10.1214/14-AOP954](https://doi.org/10.1214/14-AOP954),
[arXiv:1307.0600v3](https://arxiv.org/abs/1307.0600v3).

The public production source is not byte-identical to the author manuscript
used during development. The selected statements were cross-checked in both;
[exact hashes and scope](docs/PAPER_SOURCE.md) record that relationship and the
Appendix A.1 sign correction. Manuscript files retain their separate rights and
are linked rather than redistributed under this code's Apache-2.0 license.

## Build and verify

Lean v4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 are pinned.
RoughHeatKernel and WalshIntegral are public Git dependencies at exact commits
in lake-manifest.json. No private dependency is needed to rebuild this source.

See [verification instructions](docs/verification.md) for cache setup, a manual
check, the receipt-backed lean-pkg route, expected terminal markers and limits.
The Palomar Comparator configuration is comparator/config-chen-dalang-2015.json.

## Trust and axioms

Proofs must use only propext, Classical.choice and Quot.sound. The intentional
Challenge placeholders are independently checked against the proved Solution;
no sorry is permitted in the proof development. A native audit and an exact
statement comparison have distinct scopes. See the committed receipts and
[statement boundary](docs/what-is-proved.md).

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)), Lean,
Mathlib, [RoughHeatKernel](https://github.com/chenle02/rough-heat-kernel-lean)
and [WalshIntegral](https://github.com/chenle02/walsh-integral-lean).

## Authors and AI disclosure

Le Chen is the author and responsible maintainer of this formalization. Both
Chen and Dalang are credited as authors of the source paper. Claude Code and
OpenAI Codex agents assisted with implementation, API search, debugging,
documentation and fidelity reviews under Le Chen's direction. No independent
human review of the Lean formalization is claimed.

<!-- lean-pkg:page:begin -->
<!-- lean-pkg generates the source-bound verification record after gating. -->
<!-- lean-pkg:page:end -->
