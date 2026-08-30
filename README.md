<!--
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam McKenna <adam@mysticflounder.ai>
-->

# modular-schur

Modular Schur numbers $S_m(k,\ell)$: a uniform closed form, its Lean 4
formalization, an independently audited exponent-tail reduction, and the
computational program around them.

**The paper**: <https://mysticflounder.github.io/modular-schur/>

**The research status record**:
<https://mysticflounder.github.io/modular-schur/status.html>

The status record states what is proven, what is machine-verified, what has
been computed, what has been refuted, and what is open. It is updated as the
research state changes, so a claim's status there supersedes the PDF.

## Main theorem

For all $m \ge 2$, $\ell \ge 2$, and $k \ge m/\gcd(m,\ell-1) - 1$,

$$S_m(k,\ell) = \frac{m}{\gcd(m,\ell-1)} - 1.$$

## What is here

| Path | Contents |
| --- | --- |
| `docs/` | the site GitHub Pages serves: the paper, and the status record |
| `paper/` | the published paper snapshot; Lean-only releases leave it byte-for-byte unchanged |
| `lean/ModularSchur/` | 27 hand-written formalization modules plus the project-only axiom audit |
| `lean/comparator/` | the auditability gate: `Challenge.lean`, `Solution.lean`, config, audit |
| `LEAN_STATUS.md` | package-by-package theorem, trust, and open-boundary inventory |
| `RELEASING.md` | the source-to-public release process and paper guards |
| `formalization.yaml` | project metadata |

## The comparator gate

Twelve structural results are machine-checked. Each is stated twice. The
statement in `lean/comparator/Challenge.lean` uses Mathlib definitions only and
leaves the proof as `sorry`. The proof in `lean/comparator/Solution.lean`
discharges it from this project's development. The comparator checks that the two elaborated declarations carry the same statement,
so a proof cannot quietly weaken the statement it claims.

CI runs the `leanprover/comparator` gate on every push. The build fails if any
of these occur:

- a proof depends on `sorryAx`
- a proof depends on an axiom outside `propext`, `Classical.choice`, `Quot.sound`
- a proof depends on a generated native-evaluation axiom such as
  `declaration._native.native_decide.ax_*`
- a Challenge statement and its Solution statement differ

A second job replays the proofs through the independent `nanoda` kernel.

## Project-only Lean packages

The repository now also distributes the hand-written, generated-independent
formalization behind the newer project results. These declarations are **not**
silently added to the twelve-theorem comparator configuration.

The independently reviewed capstones establish:

- the exact support-one seed count and the decomposition of the canonical
  cover into that closed count plus a residual cover;
- exact residual-point and residual-neighborhood transport under `n → pn` at
  stable prime depth;
- invariance of the residual cover number and
  `κ(pn,a) = κ(n,a) + (p−1)p^(a_p)`;
- the fresh-prime specialization, prime-power iteration, and the unrestricted
  reduction to the exponent-truncated critical core.

The same curated tree includes the generic exact-cover dynamic program,
coordinate-union and corrected whole-axis structural theorems, anchored
transversal implications, and the current two-axis and deficit-growth
adapters. Adapter modules prove only their stated implications; in particular,
the Lean development does not yet construct the two-axis matching certificate
from support cardinality two.

[`LEAN_STATUS.md`](LEAN_STATUS.md) names every package, capstone, audit class,
and remaining Lean-open statement. `lean/PUBLIC_MODULES.txt` is the exact module
allowlist used by the publisher.

## Audit boundary

The Lean tree is curated in two explicit layers:

1. the ten-module import closure of `comparator/Solution.lean`, checked by the
   twelve-declaration comparator gate; and
2. the project-only hand-written closure recorded in
   `lean/PUBLIC_MODULES.txt`, built and axiom-audited separately.

An earlier computational route to some of these results used `native_decide`
over a generated tree of about 7,500 files. That route is **not** in this
repository and is **not** part of the verification claim. `native_decide`
trusts the compiler instead of the kernel, so its axiom closure carries
a generated per-computation native-evaluation axiom named like
`declaration._native.native_decide.ax_*`. The structural proof replaces it.

The public project-only modules contain no `native_decide`; finite checks
retained in `TauClosure.lean` use kernel `decide`. That file includes scoped
concrete sections for `d₀ = 110, 220, 440, 880, 1760, 4400, 8800`, alongside
its abstract dynamic-programming theory. The release checker also rejects
`Generated/`, unlisted project imports, proof placeholders, custom axioms, and
unsafe or external implementation boundaries in the public project modules.

## Build

**Lean.** Toolchain `leanprover/lean4:v4.33.0`. Mathlib is pinned at
`db584cd6` in `lean/lake-manifest.json`.

```
cd lean && lake build
```

To build the gate modules, which are not default targets:

```
cd lean && lake build Challenge Solution
```

The named project-only capstones have a reproducible transitive axiom audit:

```
cd lean && lake env lean ModularSchur/PublicAxiomAudit.lean
```

Maintainers use the global `lake-build` wrapper for top-level builds. Plain
`lake build` remains the portable command for a clean external checkout.

**Paper snapshot.** The source-of-truth repository builds the PDF and web page
from Markdown and publishes them together only during an explicit full release.
The files in this checkout are a synchronized snapshot. To rebuild the PDF from
that snapshot with pandoc:

```
pandoc paper/modular-schur.md -o paper/modular-schur.pdf
```

The web version is built in the source repository, which renders the same file
to HTML, compiles its TikZ figures to SVG without the print card frames, and
inlines them into the page so they follow the site's light and dark palettes.

## Reproduction of the scans

The paper's main theorem is elementary and does not depend on SAT. The
computational tables were produced with a SAT encoder driving CaDiCaL, with
DRAT certificates replayed by `drat-trim`. The full certificate tree is about
121 GB and is not distributed. The encoder regenerates it deterministically
(`--certified` makes every UNSAT fail closed unless its DRAT proof replays).

The headline computational claims map to these invocations (require `uv` and
CaDiCaL; `drat-trim` for certificate checking):

```
uv run scripts/schur_mod.py validate
    # 168 literature cases + 540+ brute-force checks
uv run scripts/phase9_stable_tables.py --scan-residual-frontier 5500 --jobs 1
    # m <= 5500 residual-frontier closure
uv run scripts/phase9_stable_tables.py --help
    # lists the 56 --scan-n<N>-fixed-quotient-family flags and the grid driver
```

No checksums for the original certificate tree are published, so a re-run is a
re-computation, not a verification of the original artifacts.

## Citing

A. McKenna, *A uniform closed form for modular Schur numbers $S_m(k,\ell)$*
(2026). The Lean development was written by Claude (Anthropic) through Claude
Code, which produced the definitions, the statements, the `IntegerBridge` and
`K1Theorem` modules and the comparator layer; [Aristotle](https://harmonic.fun)
(Achim et al., 2025, [arXiv:2510.01346](https://arxiv.org/abs/2510.01346))
filled the proof bodies of 10 lemmas in the residue-side modules. See the
`Provenance` section of the [status page](https://mysticflounder.github.io/modular-schur/)
for the per-theorem split.

## Licence

Apache License 2.0. See `LICENSE`.
