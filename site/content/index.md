---
updated: 2026-08-06
---

This page is the primary record of the modular Schur project: what is proven,
what is machine-verified, what has been computed, what has been refuted, and
what is open. It is updated as the research state changes rather than frozen at
publication, so a claim's status here supersedes any statement in the PDF.

Every claim below carries a status label. **Proven** means a complete proof
exists and has been audited. **Verified** means the Lean kernel checks it and
the axiom closure has been inspected. **Empirical** means a solver established
it for specific parameters and nothing more. **Conjecture** means it is
believed but unproven. **Refuted** means it was believed and is now disproven —
those are kept on the page deliberately.

## The main theorem

For a modulus $m$, write $S_m(k,\ell)$ for the largest $N$ such that
$\{1,\ldots,N\}$ admits a $k$-partition into sets containing no solution to
$x_1 + \cdots + x_{\ell-1} \equiv x_\ell \pmod m$.

**Proven.** For all $m \ge 2$, $\ell \ge 2$, and $k \ge m/\gcd(m,\ell-1) - 1$,

$$S_m(k,\ell) = \frac{m}{\gcd(m,\ell-1)} - 1.$$

**Verified.** The Lean statement is `schurModResidue_eq` in
`lean/ModularSchur/Partition.lean`. The `ModularSchur` tree contains no `sorry`.

## Formalization status

Twelve structural results are machine-checked in Lean 4, on toolchain
`leanprover/lean4:v4.28.0` with Mathlib pinned at `8f9d9cff`.

They are checked through a **comparator gate**, which exists to stop a
formalization from proving something weaker than it appears to. Each theorem is
stated twice: once in `comparator/Challenge.lean` using only Mathlib
definitions, with the proof left as `sorry`, and once in
`comparator/Solution.lean` where it is proved from this project's development.
The two signatures are byte-identical, so the Lean statement cannot quietly
drift toward the project's own convenient definitions. The `sorry`s in
`Challenge.lean` are the design — they are the twelve holes the gate fills.

**Verified.** The gate passes on the current commit. It fails the build on any
of: a `sorryAx` in the closure, an axiom outside
`{propext, Classical.choice, Quot.sound}`, a `Lean.ofReduceBool`, or a
Challenge/Solution statement mismatch. A second job replays the proofs through
the independent `nanoda` kernel.

| Theorem | Content | Source |
| --- | --- | --- |
| `schurMod_eq` | the main theorem, over $\mathbb{N}$ | `IntegerBridge.lean` |
| `schurModResidue_eq` | the main theorem, residue form | `Partition.lean` |
| `schurMod_eq_schurModResidue` | the two forms agree | `IntegerBridge.lean` |
| `schurModResidue_le` | upper bound | `Partition.lean` |
| `le_schurModResidue` | lower bound | `Partition.lean` |
| `schurMod_is_greatest` | maximality of the witness | `IntegerBridge.lean` |
| `no_valid_partition_of_ge_m` | nothing survives at $N \ge m$ | `IntegerBridge.lean` |
| `singleton_sumFree_iff` | singleton safety criterion | `SingletonSafety.lean` |
| `not_sumFree_of_mem_zero` | the zero residue is never safe | `UniversalBound.lean` |
| `unsafe_witness_residue` | the witness an unsafe set must contain | `UnifiedValue.lean` |
| `schurModResidue_k1` | $k=1$: $\min(\ell-1,\ m/\ell)$ | `K1Theorem.lean` |
| `sigmaInfty_le` | $\lvert C\rvert \le m/\operatorname{minFac}(m)$ | `SigmaInfty.lean` |

The main theorem as Lean sees it, with no project-specific definitions in the
statement:

```lean
theorem schurMod_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
      (m - 1) = m / Nat.gcd m (ℓ - 1) - 1
```

### The audit boundary

An earlier computational route to some of these results lives in a generated
tree of 7,478 Lean files (35 MB), of which 1,737 use `native_decide`. That route
is **excluded from the gate** and is not part of the verification claim above:
`native_decide` trusts the compiler rather than the kernel, so its closure
carries `Lean.ofReduceBool`.

**Verified.** The twelve theorems do not depend on that tree. `Solution.lean`
imports only `IntegerBridge`, `K1Theorem`, and `SigmaInfty`; the resulting
import cone reaches `Basic`, `Partition`, `SingletonSafety`, `UniversalBound`,
`UnifiedValue`, `UnifiedTheorem`, and `StableRange`, and contains zero
occurrences of `native_decide`. The structural proof subsumes the computational
one; the generated tree is retained as history, not as evidence.

## Computational coverage

### Direct SAT tables

`scripts/schur_mod.py` encodes $S_m(k,\ell)$ as SAT and drives CaDiCaL, emitting
a DRAT proof for each UNSAT boundary that `drat-trim` replays.

**Empirical.** Full grids computed for $m = 8, 9, 10, 11, 12, 13$ over
$k \le 12$ and $\ell \le 12$, with probes out to $\ell = 25$. The encoder was
validated first against the published values of D'orville et al. for
$m \in \{4,5,6,7\}$, $k \le 6$, $\ell \le 8$ — 168 cases, zero mismatches — and
against brute force on 540+ small instances.

The full run produced 10,712 CNF/proof/solution triples spanning
$m \le 18$, $k \le 17$, $\ell \le 54$. **These artifacts are not distributed**:
they are local and gitignored. Only the boundary rows recorded in the phase
tables carry an explicit `proof_verified` replay result. Treat the grids as
reproducible rather than as shipped certificates.

### The residual frontier program

Beyond the stabilized law, the project computes the exact threshold
$k_0^\infty(m,c)$ in the stable regime. The method caps each prime exponent of
$d$, collapsing infinitely many moduli onto finitely many normalized cells, so
an infinite family closes by a finite check.

**Proven, by finite normalized-cell reduction.** 56 fixed-quotient lines
($n = 36$ through $n = 345$), each with per-cell certificates, governed by three
capstone theorems. Stable laws for the families $m = 36t$ ($d=6$), $72t$
($d=12$), $72t$ ($d=6t$), $100t$ ($d=10$), $144t$, $196t$, $216t$, $252t$,
$360t$, computationally reproduced to $t \le 500$.

**Proven, by explicit certificate.** The rows those families do not cover are
handled individually — 40 packing-gap rows for $8 \le m \le 60$, then residual
covers at successive frontiers.

> **The $m \le 5500$ frontier is closed**: after the Phase 19–95 filters, zero
> residual rows remain.

This is a statement about the stable regime $\ell \ge m-1$ and about
$k_0^\infty$, not about the main theorem, which is unconditional and needs no
computation.

### Verification debt

Not everything computed is machine-checked to the standard of the twelve gated
theorems. The certificate-theorem sweep over the $m \le 5500$ frontier has not
been run through the axiom audit, and `tauDPRec_characterization` has no
recorded axiom closure. Those results rest on their solver certificates, not on
a kernel-checked Lean proof.

## Open questions

### The threshold $k_0(m,\ell)$

The main theorem says what $S_m(k,\ell)$ equals once $k$ is large enough. The
threshold — the least $k$ at which the stable value is reached — is the open
half of the problem.

Write $n = m/\gcd(m,\ell-1)$ and let $\sigma(m,\ell)$ be the largest size of a
safe subset. **Proven:** $k_0 \le n-1$ when $d < m$, and
$k_0 \ge \lceil (n-1)/\sigma \rceil$. For prime modulus the threshold is settled
exactly: $\sigma(p,\ell) = 1$ and $k_0 = p-1$.

**The natural conjecture is false at composite moduli.** One might expect that
for each $m$ there is an $L(m)$ beyond which $k_0(m,\ell) = n-1$ whenever
$d < m$. Take $m = 12$ and any $\ell \equiv 11 \pmod{12}$, so $d = 2$ and
$n = 6$. The pair $C = \{1,5\}$ is $\ell$-safe: $H_C = \langle 4\rangle$ has
order 3, $g_C = 4$, and safety needs $4 \nmid 10$. Directly,
$11 \cdot \{1,5\} = \{3,7,11\}$, disjoint from $\{1,5\}$. So $\sigma \ge 2$ and
$k_0(12,\ell) \le 3 < 5 = n-1$. Such $\ell$ are arbitrarily large, so no $L(12)$
exists. The argument generalizes to any composite $m$ with a suitable proper
divisor; the correct replacement is coset-theoretic rather than singleton-based.

A second natural guess, $k_0^\infty = \lceil (n-1)/\sigma^\infty \rceil$ for
$d > 1$, is also **refuted** — first at $m = 16$, where $\sigma^\infty = 2$ gives
a bound of 4 but the true value is 5.

**Open.** The general $d > 1$ law that replaces it. The frontier program above
establishes it row by row out to $m \le 5500$ without yielding a closed form.

### Also open

- A closed form for $\sigma^\infty(m,c)$ as a function of $(m,c)$, rather than a
  maximum over subsets.
- The boundary regime $1 \le k < n-1$. No unified formula; per-row eventual
  periodicity in $\ell$ is **conjectured**, supported by the tables for
  $8 \le m \le 13$.
- $\sigma(m,\ell) = \max\{\lvert H\rvert : H < \mathbb{Z}/m$ proper,
  $\ell H \cap H = \varnothing\}$ — **conjecture**.
- A universal closed form for $\tau$, the residual minimum set cover — **open**,
  and the anchored-transversal route to it is the one refuted above.

### Erdős problem 483

**This project does not address Erdős problem 483.** The problem asks for the
growth rate of the Schur numbers — whether $f(k) < c^k$ — which no finite
computation resolves. It is not the determination of $S(6)$.

$S(6)$ itself is unknown, with $536 \le S(6) \le 1836$; the lower bound has
stood since 2000. A recon pass on it concluded it was not a productive target
for this project and it was **abandoned**. One lead was noted and not pursued:
since $h(r) \le f(r)$ and $f(6) = S(6)$, any modular sum-free 6-colouring of
$[N]$ modulo $N+1$ certifies $S(6) \ge N$.

A planned Rado-number thread was **never executed**; the material that exists is
a landscape memo, not a result.

### D'orville et al. problems

Of the three problems posed in the originating paper, **problem 3** — the values
of $S_m(1,\ell)$ for $2 < \ell < (m+1)/2$, $m \ge 8$ — is **closed** by this
work as $S_m(1,\ell) = \min(\ell-1, \lfloor m/\ell \rfloor)$, formalized as
`schurModResidue_k1`. Problems 1 and 2 remain open.

## Refuted and retracted

These were working hypotheses in this project and are now known false. They stay
on the page with their refuting evidence, because the cost of a dead end is paid
twice if it is not recorded.

### The anchored exact transversal route

Write $\nu$ for the maximum packing and $\theta$ for the axis cover of a fiber's
conflict structure. The **anchored exact transversal** hypothesis (AET) asserted
$\theta = \nu$ — that the cover is always tight.

**Refuted** (2026-04-26, independently re-certified 2026-06-20) in its universal
form, by eight non-dyadic counterexamples. The cornerstone cases are $n = 330$
and $n = 660$, where $\nu = 13$ and $\theta = 14$.

The hypothesis was then narrowed to dyadic fibers, where it held across every
case scanned. That restriction is also **refuted** (2026-06-21), by a single
certified fiber:

$$n = 880,\quad d_0 = 35200,\quad P = (121,\,125,\,256) = (11^2,\,5^3,\,2^8)$$

with $\nu = 48$ and $\theta = 50$. The fiber is dyadic ($880 = 55\cdot 2^4$, no
power of three anywhere), singleton-atom, PID-failing, and sub-saturating. The
bounds are certified by cvc5 — maximum packing $\ge 49$ UNSAT, cover $\le 49$
UNSAT, cover of size 50 SAT — cross-checked against Z3 and CaDiCaL, with the
encoding smoke-tested against the known $n = 1716$ and $n = 330$ results first.

**What survives.** The implication *certificate shape $\Rightarrow$ exactness*
is untouched and remains fully proved in Lean. What the counterexample removes
is the claim that the shape disjunction is universal — that every PID-failing
fiber has one of those shapes. Each individual shape still forces
$\theta = \nu$. These are different statements and the second is not in
question.

### Other closed routes

| Route | How it failed |
| --- | --- |
| Perfectness of the conflict graph via odd-hole classification | 11 explicit induced $C_5$ subgraphs in dyadic $\lvert P\rvert = 3$ conflict graphs |
| Bounded atom treewidth as a universal method | treewidth grows: 15 at $n=220$, 21 at $n=440$, 36 at $n=880$ |
| An arithmetic invariant on $(n, d_0, P)$ separating AET-holds from AET-fails | no such invariant exists at that granularity — the same $(d_0, P)$ holds at $n = 1760$ and fails at $n = 880$ |
| Whole-fiber packing law for the deficit | false: the gap-0 fiber $n = 660$ contains 222 vertex-critical gap-1 cores, so deficit $<$ packing |
| Six pre-declared LP optimal-face activity selectors | none reproduces the integer deficit across a 12-fiber, 6,969-vertex census |
| Universal incidence-width bound $\le 26$ | replayed certificates give $27 \le \mathrm{tw} \le 89$ at the $n = 7040$ probe |
| Growing-minor lower bound along the $(121,125,256)$ family | an artifact of labeling — the four incidence graphs at $n = 7040, 14080, 28160, 56320$ are isomorphic under $x \mapsto 2x$ |

### Retracted for solver error

Two reported dyadic AET failures — at $n = 1760$ and $n = 3520$ — were **false
positives**, caused by a maximum-independent-set routine that under-counted.
AET in fact holds at both ($\nu = \theta = 16$). Six of fourteen reported
non-dyadic failures came from the same defect and were withdrawn. The
counterexamples that survive, including $n = 880$ above, were re-certified with
the corrected procedure and by an independent audit path.

This is why the $n = 880$ result carries a cvc5 certificate and a
second-solver cross-check rather than a scan report.

## Reproduction

**Lean.** Toolchain `leanprover/lean4:v4.28.0`, Mathlib pinned in
`lean/lake-manifest.json`.

```
cd lean && lake build
```

**Scans.** Require `uv` and CaDiCaL; `drat-trim` for certificate checking.

```
uv run scripts/phase9_stable_tables.py --help
```

The full certificate tree is roughly 121 GB and is not distributed;
`scripts/schur_mod.py` regenerates it deterministically.

## Provenance

The quantity $S_m(k,\ell)$ was introduced by Chappelon et al. (2013). The three
problems this work engages with are posed by D'orville, Sim, Wong, and Ho,
*Integers* 25 #A62.

The Lean formalization was produced with
[Aristotle](https://harmonic.fun) (Achim et al., 2025,
[arXiv:2510.01346](https://arxiv.org/abs/2510.01346)) and checked as described
under [Formalization status](#formalization-status).

Author: A. McKenna, 2026.
