<!--
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-->

# Lean theorem inventory

This file records the Lean content selected for the next public repository
release as of 2026-09-14. It separates the thirteen declarations configured
for the Comparator gate from the larger project-only theorem layer. The most
recent successful public Comparator run, run `33447037510` at commit
`315337d6a318a4465cf272073bf54d9f0ed233bb`, covered the preceding 12-declaration
configuration. The renamed thirteen-declaration Comparator job passed in run
`33534800665` at commit `5ca1063ec835e7f65d937395e7c227833f0a89ce`, but
the companion conformance job failed while building
`ModularSchur.PublicAxiomAudit`. That failure must be repaired and the complete
workflow rerun before release. Those runs used leanprover/comparator built from
a pinned tag on Lean 4.33. The Lean tree is now on
`leanprover/lean4:v4.35.0-rc3` with Mathlib `v4.35.0-rc3`, and the Comparator
job runs that toolchain's `lake comparator` with the Lean, `nanoda` and
`con-ron` kernels; no run of it is recorded here yet. The exact module
allowlist is [`lean/PUBLIC_MODULES.txt`](lean/PUBLIC_MODULES.txt).

## Status terms

- **Comparator-gated**: the mathlib-only statement and project-backed proof
  pass statement comparison, the Lean kernel, the `nanoda` kernel, and the
  configured axiom policy.
- **Independently audited Lean proof**: a separate reviewer checked statement
  fidelity, import reachability, a fresh build, and the named theorem's
  transitive axiom closure.
- **Kernel-checked project theorem**: the declaration builds without a proof
placeholder. Its package is public, but it is not one of the thirteen
  comparator declarations.
- **Adapter only**: the displayed implication is proved, while a producer for
  one of its hypotheses remains open.

## Comparator-gated declarations

The current gate contains thirteen declarations under `ComparatorClaims`:

1. `schurMod_integerClosedForm`
2. `schurMod_integerCap_isGreatest`
3. `noValidIntegerPartition_of_ge_modulus`
4. `schurMod_integer_eq_residue`
5. `schurModResidue_closedForm`
6. `schurModResidue_upperBound`
7. `schurModResidue_lowerBound`
8. `singleton_sumFree_iff_nonzeroMultiple`
9. `criticalResidue_isUnsafe`
10. `zeroMem_notSumFree`
11. `schurModResidue_oneColorClosedForm_of_le_modulus`
12. `schurModResidue_oneColorClosedForm`
13. `sigmaInfty_card_le_minFacQuotient`

Their project import closure is the ten-module structural package from
`Basic.lean` through `SigmaInfty.lean`. The gate permits only `propext`,
`Classical.choice`, and `Quot.sound`; the independent kernel replay is part of
CI. `lean/comparator/README.md` gives the exact statement-to-project mapping.

## Independently audited project-only packages

These packages are now distributed but remain outside the thirteen-declaration
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
modules needed to state and check the integer-level one-colour value and the
broader cover theory:

- `K1IntegerTheorem`: the integer-level one-colour value `schurMod m 1 ℓ` for
  every `m ≥ 2` and `ℓ ≥ 2`, obtained from the residue-level formula through
  the reduction bridge. Its single capstone `schurMod_k1_all` is audited by
  `PublicAxiomAudit.lean`. It covers the regime `m < ℓ`, which the paper does
  not treat.
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
- `PairSupportGraph`: the pair-support conflict graph, with
  `maxPacking_eq_indepNum` identifying maximum axis packing with the graph's
  independence number.
- `CanonicalBlockMonotonicity`: monotonicity and congruence of the canonical
  restricted, prefix, and factorization extensional cover families under
  label coarsening.
- `AllButOneAxisCover`: the all-but-one-axis residual label cover
  (`allButOneAxis_isLabelCover`) and the resulting bound of the canonical
  extensional axis cover by the seed count plus the off-axis residual labels.
- `AxisBlockCount`: closed counts on one axis -- the per-layer label count
  `card_axisLayerLabels_eq_min`, the axis total as a sum over layers, the
  on-axis seed count, and the residual axis count as their difference.
- `AllButOneAxisCount`: the off-axis residual labels summed over axes in closed
  form, and the two resulting bounds on the canonical extensional axis cover.
- `DeficitGrowthInvariant`, `DeficitGrowthRestrictedAET`, and
  `DeficitGrowthCertificateShape`: implication and certificate-shape lemmas
  surviving the refuted universal AET route. They do not revive that route.

The exact statements live in the Lean sources. Descriptions here do not add
hypotheses or conclusions to them.

The working research tree has also closed and independently audited the shared
AS/FD-6 window layer W0 (`SemiprimeWindow.lean`) and support layer W1
(`SemiprimeSupport.lean`). Those modules are not in this release's public
allowlist and are not Comparator targets. W2 is the next working-tree
obligation; W3 is the highest-risk bridge, and W4/A1--A3/F1--F3 remain open.

## Trust boundary

The public formalization consists of 33 hand-written modules plus
`PublicAxiomAudit.lean`. The static assembly checker enforces:

- no `ModularSchur/Generated/` directory or generated-dependent module;
- no proof-placeholder use in the 33 project modules;
- no project `axiom`, `native_decide`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `Lean.trustCompiler`, `unsafe`, `partial`, `extern`, or
  `implemented_by` boundary in those modules;
- a complete project-import closure matching `lean/PUBLIC_MODULES.txt`.

The release runbook separately requires fresh builds of the public aggregate
and both comparator modules, plus inspection of transitive `#print axioms`
output for the named project-only capstones. The conformance workflow now also
runs `lake build ModularSchur.PublicAxiomAudit`: its `#print axioms` commands elaborate
the named declarations and surface their transitive closures in the CI log for
review. This target does not automatically whitelist-fail on custom axioms.
It is independent of the Comparator/`nanoda` gate, which still checks exactly
the thirteen `ComparatorClaims` declarations. Those build gates must pass before the
staged public candidate is committed.

`Challenge.lean` intentionally contains thirteen `sorry` statement stubs. They
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
lake build ModularSchur.PublicAxiomAudit
comparator/check-conformance.sh
```

Project maintainers use the global `lake-build` wrapper in place of direct
`lake build` so concurrent top-level builds are serialized and each Lean
worker receives the repository memory ceiling.
