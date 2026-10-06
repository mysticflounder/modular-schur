# comparator/ — Zulip auditability gate

This directory packages the **modular Schur number** project for the Lean
community's **auditability gate for AI-authored formalizations** (leanprover
Zulip, "AI authored projects"). The gate answers *"is this claim real, and is it
exactly what you say it is?"* — it is **not** the bar for mathlib inclusion (that
is a separate PR review).

Proposed Paper I: *Endpoint formulas for modular Schur numbers, with a
correction to a prime-power formula* (A. McKenna, 2026). Its high-color
headline result is:

> For every `m ≥ 2`, `ℓ ≥ 2`, and `k ≥ n-1` where `n := m / gcd(m, ℓ-1)`,
> `S_m(k,ℓ) = n - 1 = m / gcd(m, ℓ-1) - 1`.

## The four required artifacts

| # | Requirement | Here |
|---|-------------|------|
| 1 | `Challenge.lean` — **mathlib-only**, currently gated claims as `sorry` stubs | [`Challenge.lean`](Challenge.lean) (module `Challenge`, `import Mathlib`) |
| 2 | `Solution.lean` — imports the project, discharges the stubs | [`Solution.lean`](Solution.lean) (module `Solution`, `import ModularSchur.*`) |
| 3 | Comparator run in CI + comparator axiom audit | [`config.json`](config.json) + [`../../.github/workflows/comparator.yml`](../../.github/workflows/comparator.yml) + [`axiom-audit.lean`](axiom-audit.lean) |
| 4 | `formalization.yaml` (mathlib-initiative spec) | [`../../formalization.yaml`](../../formalization.yaml) |

Challenge and Solution declare the current 13 gated results in a shared
`ComparatorClaims` namespace (so `config.json` lists
`ComparatorClaims.schurMod_integerClosedForm`, …). The
comparator looks up each name in *both* exports, so they must agree on the
fully-qualified name; the namespace also keeps Solution's restatements from
colliding with the project's own top-level theorem names.

## Paper II comparator sections — SKETCH — NOT PROMOTABLE

Paper I is the current 13-declaration gate. The structural programme belongs
to a later Paper II only after its interfaces are ready.  Its five section
boundaries are recorded in the mathlib-only, declaration-free
[`StrategySketch.lean`](StrategySketch.lean): stable semantics and canonical
blocks; labelled seeds; tail elimination and the critical core; two-active-prime
matching; and the separate prefix-boundary formulas.

The project-wide headline list has grown beyond the live gate. The rows below
are planning-only declaration slots for that Paper II expansion. They are not
Lean declarations and are absent from `ComparatorClaims`, `Challenge.lean`,
`Solution.lean`, `config.json`, and both axiom audits. Thus they make no
Comparator, kernel-proof, or publication claim.

Every row has comparator status **SKETCH — NOT PROMOTABLE**. That label applies
to the missing comparator package, not to the underlying prose or project-Lean
result. Proposed names are working names until the exact mathlib-only statements
and matching project-backed declarations are reviewed.

| Paper II section | Project-wide package | Proposed `ComparatorClaims` declaration slots | Underlying result | Work required before gate entry |
|---|---|---|---|---|
| A | Stable prime-block normal form and exact stable prefix cover | `stablePrimeBlockNormalForm`; `stablePrefixBlockCover` | **PROVEN** in prose and independently audited; full prefix statements retain stable-length, `n ≥ 2`, and `0 ≤ N ≤ n−1` hypotheses | Formalize the project-side Lean producers; then write complete mathlib-only statements and matching `Solution` proofs. |
| B | Labelled/arithmetic support-one seed decomposition and closed count | `axisCoverExtensionalImageEqPrivateLabelsAddResidual`; `canonicalPrivateLabelsEqSupportOneSeedLabels`; `cardSupportOneSeedLabelsEqSeedCountFormula`; `axisCoverCanonicalExtensionalFamilyEqSeedCountFormulaAddResidual` | **PROVEN IN LEAN** and independently audited | Inline the project definitions using mathlib-only objects and add statement-matched `Solution` wrappers. |
| C | Certified inactive-prime stripping | `inactivePrimeStripping`; `axisCoverCanonicalExtensionalFamilyMulEqOfPrimeNotMem` | **PROVEN IN LEAN** for the terminal O2--O5 package and independently audited | Add exact mathlib-only `Challenge` statements and matching project-backed `Solution` proofs. No mathlib-only comparator proofs exist yet. |
| C | One-step stable-prime residual-cover transport | `canonicalSeedResidualNeighbourhoodPrimeMultiplicationLabelMapEqImage`; `axisCoverCanonicalSeedResidualMulPrimeEq`; `seedCountFormulaMulPrime`; `axisCoverCanonicalExtensionalFamilyMulPrimeEq` | **PROVEN IN LEAN** and independently audited | Inline the arithmetic label, residual-neighborhood, and cover definitions using mathlib-only objects, then add statement-matched `Solution` wrappers. Do not require a global label bijection. |
| C | Unrestricted exponent truncation | `axisCoverCanonicalExtensionalFamilyPrimePowMulPrimeEq`; `axisCoverCanonicalExtensionalFamilyEqExponentTruncatedCoreAddExcessUnrestricted` | **PROVEN IN LEAN** and independently audited | Inline the unrestricted truncated-core, exponent-excess, and canonical-cover definitions using mathlib-only objects, then add statement-matched `Solution` wrappers. No positive-depth hypothesis is required by the unrestricted project identity; no mathlib-only comparator proof exists yet. |
| D | Exact two-active-prime matching boundary | `twoActivePrimeMatchingBoundary` | **PROVEN** in prose and independently audited; project Lean currently has coverage and certificate-to-AET adapters | Supply the finite Kőnig certificate producer and final project consumer, then translate the complete statement. |
| E | Prime-power and at-most-one-active prefix boundaries | `primePowerStableBoundary`; `atMostOneActivePrimeBoundary` | **PROVEN** in prose; Lean producers remain open | Formalize the stable prefix/layer-count formulas before translating them. |

Sources for these slots are the
[stable normal-form proof](../../docs/proofs/stable-prime-block-normal-form-2026-08-24.md),
[inactive-prime proof](../../docs/proofs/inactive-prime-stripping-and-prime-power-boundary-2026-08-24.md),
[inactive-prime Lean audit](../../docs/skeptic-inactive-prime-stripping-lean-2026-08-26.md),
[two-active-prime proof](../../docs/proofs/two-active-prime-matching-boundary-2026-08-24.md),
and [labelled seed decomposition](../../docs/proofs/axis-labelled-cover-seed-decomposition-2026-08-25.md).

Promotion is atomic: only after an exact statement, a project proof with a
reachable final consumer, and the required trust audit exist should one add the
`Challenge` theorem, the matching proved `Solution` theorem, the `config.json`
name, and the corresponding `axiom-audit.lean` entry in the same change. Until
then, the live gate remains the current 13-theorem set.

The universal residual-cover quantity `tau` and the three-or-more-active-axis
case are **OPEN**. They are intentionally absent from Sections A--E and have no
proposed `ComparatorClaims` slot.

## Run it

The Lean package lives in `lean/` (its `lakefile.toml` registers the `Challenge`,
`Solution`, and declaration-free `StrategySketch` libraries with
`srcDir = comparator`). Cheap offline pre-flight (build + axiom audit; no
comparator toolchain needed):

```bash
# from the repo root
lean/comparator/check-conformance.sh
```

The authoritative check is the `lake comparator` run (requirement 3): the
comparator that ships with the Lean toolchain since v4.35.0-rc2 (earlier runs
of this gate used the standalone
[leanprover/comparator](https://github.com/leanprover/comparator) built from a
pinned tag). The comparator, the exporter (`leanexport`) and the kernels all
come from `lean/lean-toolchain` (currently `leanprover/lean4:v4.35.0-rc3`).
It builds and exports `Challenge` and `Solution` inside a `bwrap`
(bubblewrap) sandbox, checks statement identity and axiom compliance, then
replays the solution through Lean's kernel and every configured external
kernel. It exits 0 and ends with `Your solution is okay!` on acceptance. It is
wired in CI
([`../../.github/workflows/comparator.yml`](../../.github/workflows/comparator.yml)).

The committed [`config.json`](config.json) names no `external_kernels`: the
Palomar Registry rejects that field in a submitted configuration and registers
the toolchain's bundled kernels itself. The CI step does the same. It writes a
copy of `config.json` without `enable_nanoda` (which `lake comparator` refuses
together with `external_kernels`) and with the toolchain's `nanoda_bin` and
`con-ron` registered as external kernels, then runs `lake comparator` on that
copy. To run it the same way on Linux with `bubblewrap` installed:

```bash
cd lean
lake exe cache get
prefix="$(lean --print-prefix)"
jq --arg prefix "$prefix" \
  'del(.enable_nanoda)
   | .external_kernels = {
       "nanoda": [($prefix + "/bin/nanoda_bin")],
       "con-ron": [($prefix + "/bin/con-ron")]
     }' \
  comparator/config.json > /tmp/comparator-config.json
lake comparator --config /tmp/comparator-config.json
# Exit 0 is acceptance; the log ends with "Your solution is okay!".
```

`bubblewrap` is Linux-only, so the comparator runs in Linux CI.
`lake comparator --inadvisably-no-sandbox` disables the sandbox; this
repository does not use it.

The conformance workflow has a separate project-layer step that runs
`lake build ModularSchur.PublicAxiomAudit`:

```bash
lake build ModularSchur.PublicAxiomAudit
```

`PublicAxiomAudit` consists of `#print axioms` commands. Building it elaborates
the named project-only declarations and emits their transitive axiom closures
in the log for review; the build does not automatically enforce a whitelist or
fail on a custom axiom. This audit is independent of the Comparator/`nanoda`
gate, whose configured scope remains exactly the current 13 `ComparatorClaims`
statements.

## What is in the gate: the current 13 mathlib-only structural claims

These are the currently configured structural closed-form results whose
statements have already been expressed with mathlib definitions alone, so a
reviewer can read `Challenge.lean` without trusting any project definition.
They are not an exhaustive project-wide ranking. All 13 are axiom-clean: their
`#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no custom axioms, **no `native_decide`**).

| Name (under `ComparatorClaims`) | Project theorem | Paper / role |
|---|---|---|
| `schurMod_integerClosedForm` | `ModularSchur.schurMod_eq` | **Theorem 1.2** — main closed form (integer, Definition 1.1) |
| `schurMod_integerCap_isGreatest` | `ModularSchur.schurMod_is_greatest` | Definition correctness: the `N ≤ m-1` cap in `Nat.findGreatest` is lossless, so `schurMod` is the unbounded "greatest `N`" of Definition 1.1 |
| `noValidIntegerPartition_of_ge_modulus` | `ModularSchur.no_valid_partition_of_ge_m` | **Lemma 2.2** — universal upper bound (no valid partition once `N ≥ m`) |
| `schurMod_integer_eq_residue` | `ModularSchur.schurMod_eq_schurModResidue` | **Lemma 2.1** — residue reduction (integer def = residue def) |
| `schurModResidue_closedForm` | `ModularSchur.schurModResidue_eq` | **Theorem 1.2**, residue form (= Theorem 3.1 ∧ Theorem 4.1) |
| `schurModResidue_upperBound` | `ModularSchur.schurModResidue_le` | **Theorem 3.1** — upper bound |
| `schurModResidue_lowerBound` | `ModularSchur.le_schurModResidue` | **Theorem 4.1** — lower bound |
| `singleton_sumFree_iff_nonzeroMultiple` | `ModularSchur.singleton_sumFree_iff` | **Lemma 2.3** — singleton safety |
| `criticalResidue_isUnsafe` | `ModularSchur.unsafe_witness_residue` | §3 arithmetic crux: `(ℓ-1)·n ≡ 0 (mod m)` |
| `zeroMem_notSumFree` | `ModularSchur.not_sumFree_of_mem_zero` | §2 — any class containing `0` is not `ℓ`-sum-free |
| `schurModResidue_oneColorClosedForm_of_le_modulus` | `ModularSchur.schurModResidue_k1` | repo result: D'orville–Sim–Wong–Ho **Problem 1.3** (`k=1` closed form `min(ℓ-1, ⌊m/ℓ⌋)`) |
| `schurModResidue_oneColorClosedForm` | `ModularSchur.schurModResidue_k1_all` | complete one-color formula for every `m ≥ 2`, `ℓ ≥ 2`, including the `0/1` branches when `m < ℓ` |
| `sigmaInfty_card_le_minFacQuotient` | `ModularSchur.sigmaInfty_le` | repo result: σ∞ coset cardinality bound (`|C| ≤ m/minFac m`) |

### How the gate is satisfied: the bridge

`schurMod` / `schurModResidue` are `Nat.findGreatest` over a predicate that
quantifies over the one-constructor `Prop` structures `IsValidPartitionNat` /
`IsValidPartition`. `Challenge.lean` unbundles those structures into an explicit
four-way conjunction (the `covers ∧ disjoint ∧ subset ∧ sumFree` fields), so the
statement uses mathlib constants only. `Solution.lean` carries two `private`
bridge lemmas proving `schurMod = <inlined>` and `schurModResidue = <inlined>`
(the two existentials are propositionally equal because a structure is equivalent
to its fields), then discharges each headline from the project theorem. The
comparator verifies the inlined statements in the two exports are identical.

## The audit boundary: what is NOT in the comparator gate

The project's private working tree contains a large **`native_decide`-backed
computational scan tree** (`ModularSchur/Generated/` and generated-dependent
concrete residue-axis, deficit-growth, and scanner bridges — thousands of
generated lemmas verifying per-modulus tables). That line is an earlier
*computational* route, subsumed by the structural closed-form proof above. It
is not distributed in the public repository and is **deliberately excluded**
from this comparator gate:

- Its `#print axioms` closure includes a generated per-computation
  native-evaluation axiom named like
  `declaration._native.native_decide.ax_*`, so it is **not** kernel-axiom-clean in the
  `{propext, Classical.choice, Quot.sound}` sense this gate enforces.
- The headline closed form does not depend on it.

This boundary is deliberate and honest: the comparator gate covers the
mathlib-statable, kernel-axiom-clean **structural** surface that the paper
machine-verifies; the computational scan tree is retained only in the private
working tree — not distributed here, not part of this gate, and not part of
the public verification claim.

The public repository separately carries a hand-written,
generated-independent project layer, including `ResidueAxis`, the canonical
seed/transport/critical-core package, and several structural adapters. Those
modules contain no `native_decide` and have their own capstone axiom audit in
`ModularSchur/PublicAxiomAudit.lean`. Its build surfaces the transitive
`#print axioms` closures but does not itself whitelist-fail on custom axioms.
They remain outside the thirteen configured `ComparatorClaims` declarations until
complete mathlib-only statements and matching `Solution` wrappers are reviewed
atomically.
