# modular-schur

Modular Schur numbers $S_m(k,\ell)$: a uniform closed form, its Lean 4
formalization, and the computational program around it.

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
| `paper/` | the paper's canonical Markdown source, and the PDF built from it |
| `lean/ModularSchur/` | the structural formalization, 10 modules |
| `lean/comparator/` | the auditability gate: `Challenge.lean`, `Solution.lean`, config, audit |
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
- a proof depends on `Lean.ofReduceBool`
- a Challenge statement and its Solution statement differ

A second job replays the proofs through the independent `nanoda` kernel.

## Audit boundary

The Lean tree here is curated. It carries the import closure of
`comparator/Solution.lean` and nothing more.

An earlier computational route to some of these results used `native_decide`
over a generated tree of about 7,500 files. That route is **not** in this
repository and is **not** part of the verification claim. `native_decide`
trusts the compiler instead of the kernel, so its axiom closure carries
`Lean.ofReduceBool`. The structural proof replaces it.

## Build

**Lean.** Toolchain `leanprover/lean4:v4.28.0`. Mathlib is pinned in
`lean/lake-manifest.json`.

```
cd lean && lake build
```

To build the gate modules, which are not default targets:

```
cd lean && lake build Challenge Solution
```

**Paper.** The source is Markdown, not LaTeX, and it is the canonical form: the
PDF and the web page are both built from it. Build the PDF with pandoc:

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
