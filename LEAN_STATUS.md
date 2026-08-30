<!--
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-->

# Lean theorem inventory

This file records the Lean content distributed in the public repository as of
2026-08-29. It separates the twelve externally comparator-gated declarations
from the larger project-only theorem layer. The exact module allowlist is
[`lean/PUBLIC_MODULES.txt`](lean/PUBLIC_MODULES.txt).

## Status terms

- **Comparator-gated**: the mathlib-only statement and project-backed proof
  pass statement comparison, the Lean kernel, the `nanoda` kernel, and the
  configured axiom policy.
- **Independently audited Lean proof**: a separate reviewer checked statement
  fidelity, import reachability, a fresh build, and the named theorem's
  transitive axiom closure.
- **Kernel-checked project theorem**: the declaration builds without a proof
  placeholder. Its package is public, but it is not one of the twelve
  comparator declarations.
- **Adapter only**: the displayed implication is proved, while a producer for
  one of its hypotheses remains open.

## Comparator-gated declarations

The current gate contains twelve declarations under `Headline`:

1. `schurMod_eq`
2. `schurMod_is_greatest`
3. `no_valid_partition_of_ge_m`
4. `schurMod_eq_schurModResidue`
5. `schurModResidue_eq`
6. `schurModResidue_le`
7. `le_schurModResidue`
8. `singleton_sumFree_iff`
9. `unsafe_witness_residue`
10. `not_sumFree_of_mem_zero`
11. `schurModResidue_k1`
12. `sigmaInfty_le`

Their project import closure is the ten-module structural package from
`Basic.lean` through `SigmaInfty.lean`. The gate permits only `propext`,
`Classical.choice`, and `Quot.sound`; the independent kernel replay is part of
CI. `lean/comparator/README.md` gives the exact statement-to-project mapping.

## Independently audited project-only packages

These packages are now distributed but remain outside the twelve-declaration
comparator configuration.

| Package | Main modules | Named capstones |
| --- | --- | --- |
| Labelled support-one deletion | `AxisLabelledCover` | `axis_cover_extensionalImage_eq_privateLabels_add_residual` |
| Arithmetic canonical blocks | `CanonicalBlocks` | `canonicalPrivateLabels_eq_supportOneSeedLabels`; `axisCover_canonicalExtensionalFamily_eq_private_add_residual` |
| Closed seed count | `CanonicalSeedCount` | `card_supportOneSeedLabels_eq_seedCountFormula`; `axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual` |
| Stable-prime point transport | `CanonicalSeedTransport` | `canonicalSeedCoveredPoints_mul_eq_nondvd_union_image`; `canonicalSeedResidualPoints_mul_eq_image` |
| Residual-neighborhood and cover transport | `CanonicalResidualCoverTransport` | `canonicalSeedResidualNeighbourhood_activePrimeLabelMap_eq_image`; `axisCover_canonicalSeedResidual_mul_prime_eq`; `axisCover_canonicalExtensionalFamily_mul_prime_eq` |
| Prime powers and critical core | `CanonicalCriticalCore` | `axisCover_canonicalExtensionalFamily_primePow_mul_prime_eq`; `axisCover_canonicalExtensionalFamily_eq_exponentTruncatedCore_add_excess_unrestricted` |

Mathematically, these capstones establish:

- the exact support-one seed count `K_seed(n,a)` and the decomposition of the
  canonical cover into that closed term plus a residual cover;
- under the sharp condition `a_p ≤ v_p(n)`, transport of the residual point
  set and every nonempty residual neighborhood under `n → pn`, invariance of
  the residual cover number, and
  `κ(pn,a) = κ(n,a) + (p−1)p^(a_p)`;
- the fresh-prime specialization, where `a_p = 0` and the contribution is
  `p−1`;
- prime-power iteration and the unrestricted reduction to
  `n_crit = ∏_{p∣n} p^min(v_p(n),a_p)`, with the exact contribution of every
  removed exponent layer.

The independent audits cover the seed-count capstones and the final point,
neighborhood, recurrence, fresh-prime, prime-power, and unrestricted
critical-core consumers. General helper declarations compile and feed those
consumers; they did not each receive a separate statement-fidelity review.

## Other public kernel-checked theory

The public allowlist also carries the hand-written, generated-independent
modules needed to state and check the broader cover theory:

- `TauClosure`: atomization, exact set-cover dynamic programming, executable
  recurrence, cost-only compression, and the scoped `n=220` package. The named
  DP capstones are audited by `PublicAxiomAudit.lean`.
- `CoordinateUnion` and `SameSupportFiber`: coordinate-clique descriptions of
  same-support fibers under their explicit hypotheses.
- `AnchoredExactTransversal`: an explicit anchored transversal yields equality
  of axis cover and maximum packing.
- `WholeAxisPID`: the corrected all-axis separation theorem and the valid
  singleton-pattern specialization. One-axis injectivity by itself does not
  prove the former.
- `TwoAxisStructural` and `TwoAxisAnchoredExactTransversal`: coverage and
  certificate-to-transversal adapters. These do **not** construct the matching
  certificate from the assumption that the support has cardinality two.
- `DeficitGrowthInvariant`, `DeficitGrowthRestrictedAET`, and
  `DeficitGrowthCertificateShape`: implication and certificate-shape lemmas
  surviving the refuted universal AET route. They do not revive that route.

The exact statements live in the Lean sources. Descriptions here do not add
hypotheses or conclusions to them.

## Trust boundary

The public formalization consists of 27 hand-written modules plus
`PublicAxiomAudit.lean`. The static assembly checker enforces:

- no `ModularSchur/Generated/` directory or generated-dependent module;
- no proof-placeholder use in the 27 project modules;
- no project `axiom`, `native_decide`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `Lean.trustCompiler`, `unsafe`, `partial`, `extern`, or
  `implemented_by` boundary in those modules;
- a complete project-import closure matching `lean/PUBLIC_MODULES.txt`.

The release runbook separately requires fresh builds of the public aggregate
and both comparator modules, plus inspection of transitive `#print axioms`
output for the named project-only capstones. Those build gates must pass before
the staged public candidate is committed.

`Challenge.lean` intentionally contains twelve `sorry` statement stubs. They
are not proofs. `Solution.lean` supplies the proofs, and the comparator checks
the two exported statement sets.

The private working repository retains thousands of generated computational
modules from an older scan route. Those files are not distributed and support
no claim made by this public Lean release.

## Results not closed in Lean

The following must not be inferred from the public module count:

- the stable prime-block normal form and full stable-prefix formula;
- the O6--O9 prime-power prefix and at-most-one-active formulas;
- construction of the two-axis matching certificate from support cardinality
  two;
- a universal closed form for the residual cover number on the truncated
  critical domain.

## Reproduce the Lean checks

From the public repository:

```bash
cd lean
lake build
lake build Challenge Solution
lake env lean ModularSchur/PublicAxiomAudit.lean
comparator/check-conformance.sh
```

Project maintainers use the global `lake-build` wrapper in place of direct
`lake build` so concurrent top-level builds are serialized and each Lean
worker receives the repository memory ceiling.
