# comparator/ — Zulip auditability gate

This directory packages the **modular Schur number** project for the Lean
community's **auditability gate for AI-authored formalizations** (leanprover
Zulip, "AI authored projects"). The gate answers *"is this claim real, and is it
exactly what you say it is?"* — it is **not** the bar for mathlib inclusion (that
is a separate PR review).

Paper: *A uniform closed form for modular Schur numbers `S_m(k,ℓ)`* (A. McKenna,
2026). Headline result, Theorem 1.2:

> For every `m ≥ 2`, `ℓ ≥ 2`, and `k ≥ n-1` where `n := m / gcd(m, ℓ-1)`,
> `S_m(k,ℓ) = n - 1 = m / gcd(m, ℓ-1) - 1`.

## The four required artifacts

| # | Requirement | Here |
|---|-------------|------|
| 1 | `Challenge.lean` — **mathlib-only**, headline claims as `sorry` stubs | [`Challenge.lean`](Challenge.lean) (module `Challenge`, `import Mathlib`) |
| 2 | `Solution.lean` — imports the project, discharges the stubs | [`Solution.lean`](Solution.lean) (module `Solution`, `import ModularSchur.*`) |
| 3 | Comparator run in CI + axiom audit | [`config.json`](config.json) + [`../../.github/workflows/comparator.yml`](../../.github/workflows/comparator.yml) + [`axiom-audit.lean`](axiom-audit.lean) |
| 4 | `formalization.yaml` (mathlib-initiative spec) | [`../../formalization.yaml`](../../formalization.yaml) |

Challenge and Solution declare the 12 results in a **shared `Headline`
namespace** (so `config.json` lists `Headline.schurMod_eq`, …). The comparator
looks up each name in *both* exports, so they must agree on the fully-qualified
name; the namespace also keeps Solution's restatements from colliding with the
project's own top-level theorem names.

## Run it

The Lean package lives in `lean/` (its `lakefile.toml` registers the `Challenge`
and `Solution` libraries with `srcDir = comparator`). Cheap offline pre-flight
(build + axiom audit; no comparator toolchain needed):

```bash
# from the repo root
lean/comparator/check-conformance.sh
```

The authoritative check is the real
[leanprover/comparator](https://github.com/leanprover/comparator) run
(requirement 3): it re-exports both modules through `lean4export`, checks
statement identity and axiom compliance, then re-runs **both** the `nanoda`
kernel and the Lean default kernel, ending in `Your solution is okay!`. It is
wired in CI; to run it locally:

```bash
cd lean
# Build the comparator at the tag matching this repo's lean-toolchain, so its
# bundled lean4export is built against the SAME Lean as the project.
TC="$(cut -d: -f2 lean-toolchain)"           # v4.28.0
git clone --branch "$TC" https://github.com/leanprover/comparator /tmp/cmp
( cd /tmp/cmp && lake build && lake build lean4export )   # comparator + matched lean4export

# Build the project's Challenge/Solution first. A pre-built .lake means the
# comparator does not rebuild Solution, so its guarantee no longer rests on the
# sandbox (comparator README assumption: "obtained a fully pre-built .lake").
../scripts/lake-build.sh Challenge Solution

# This comparator tag invokes `landrun` and `lean4export` by name from PATH —
# there are no COMPARATOR_LANDRUN / COMPARATOR_LEAN4EXPORT overrides. landrun is
# Linux-only (Landlock LSM); on macOS expose the in-repo no-sandbox shim
# (comparator/fake-landrun.sh) as `landrun`:
mkdir -p /tmp/shim && ln -sf "$PWD/comparator/fake-landrun.sh" /tmp/shim/landrun
LE=/tmp/cmp/.lake/packages/lean4export/.lake/build/bin

PATH="/tmp/shim:$LE:$PATH" \
  lake env /tmp/cmp/.lake/build/bin/comparator comparator/config.json
# Success ends with "Your solution is okay!".
```

[`fake-landrun.sh`](fake-landrun.sh) strips the landrun sandbox flags and execs
the command unsandboxed; it drops only the sandbox (which contains a *malicious*
Solution author — not the point for a self-audit of our own Solution), not any
verification leg. Linux CI uses the real `landrun` sandbox.

The committed [`config.json`](config.json) sets `enable_nanoda: true`; the nanoda
leg invokes `nanoda_bin` from PATH and runs in Linux CI. To run locally without
it, pass a config with nanoda off
(`jq '.enable_nanoda=false' comparator/config.json > /tmp/cfg.json` then point the
comparator at `/tmp/cfg.json`), or build
[`ammkrn/nanoda_lib`](https://github.com/ammkrn/nanoda_lib) and put `nanoda_bin`
on PATH. The statement-identity + Lean default-kernel legs run either way.

## What is in the gate: the 12 mathlib-only headline claims

These are exactly the project's **structural closed-form** results whose
**statement** is expressible with mathlib definitions alone, so a reviewer can
read `Challenge.lean` without trusting any project definition. All 12 are
axiom-clean: their `#print axioms` closure ⊆ `{propext, Classical.choice,
Quot.sound}` (no `sorryAx`, no custom axioms, **no `native_decide`**).

| Name (under `Headline`) | Project theorem | Paper / role |
|---|---|---|
| `schurMod_eq` | `ModularSchur.schurMod_eq` | **Theorem 1.2** — main closed form (integer, Definition 1.1) |
| `schurMod_is_greatest` | `ModularSchur.schurMod_is_greatest` | Definition correctness: the `N ≤ m-1` cap in `Nat.findGreatest` is lossless, so `schurMod` is the unbounded "greatest `N`" of Definition 1.1 |
| `no_valid_partition_of_ge_m` | `ModularSchur.no_valid_partition_of_ge_m` | **Lemma 2.2** — universal upper bound (no valid partition once `N ≥ m`) |
| `schurMod_eq_schurModResidue` | `ModularSchur.schurMod_eq_schurModResidue` | **Lemma 2.1** — residue reduction (integer def = residue def) |
| `schurModResidue_eq` | `ModularSchur.schurModResidue_eq` | **Theorem 1.2**, residue form (= Theorem 3.1 ∧ Theorem 4.1) |
| `schurModResidue_le` | `ModularSchur.schurModResidue_le` | **Theorem 3.1** — upper bound |
| `le_schurModResidue` | `ModularSchur.le_schurModResidue` | **Theorem 4.1** — lower bound |
| `singleton_sumFree_iff` | `ModularSchur.singleton_sumFree_iff` | **Lemma 2.3** — singleton safety |
| `unsafe_witness_residue` | `ModularSchur.unsafe_witness_residue` | §3 arithmetic crux: `(ℓ-1)·n ≡ 0 (mod m)` |
| `not_sumFree_of_mem_zero` | `ModularSchur.not_sumFree_of_mem_zero` | §2 — any class containing `0` is not `ℓ`-sum-free |
| `schurModResidue_k1` | `ModularSchur.schurModResidue_k1` | repo result: D'orville–Sim–Wong–Ho **Problem 1.3** (`k=1` closed form `min(ℓ-1, ⌊m/ℓ⌋)`) |
| `sigmaInfty_le` | `ModularSchur.sigmaInfty_le` | repo result: σ∞ coset cardinality bound (`|C| ≤ m/minFac m`) |

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

The repository contains a large **`native_decide`-backed computational scan
tree** (`ModularSchur/Generated/` and the residue-axis / deficit-growth /
scanner-bridge machinery — thousands of generated lemmas verifying per-modulus
tables). That line is an earlier *computational* route, subsumed by the
structural closed-form proof above. It is **deliberately excluded** from this
comparator gate:

- Its `#print axioms` closure includes `Lean.ofReduceBool` (the `native_decide`
  compiler-trust axiom), so it is **not** kernel-axiom-clean in the
  `{propext, Classical.choice, Quot.sound}` sense this gate enforces.
- The headline closed form does not depend on it.

This boundary is deliberate and honest: the comparator gate covers the
mathlib-statable, kernel-axiom-clean **structural** surface that the paper
machine-verifies; the computational scan tree is auditable by reading the
repository and running its own builds, but is not part of this gate.
