# Phase 7: The Unified Stabilized Law for $S_m(k,\ell)$

**Status labels.** PROVEN = complete, gap-free argument. CONJECTURED = open. EMPIRICALLY VERIFIED = SAT-checked on a finite grid only. HEURISTIC = informal.

## 0. Summary of what this document proves

Let $m\ge 2$ and $\ell\ge 2$ be integers, and set $d:=\gcd(m,\ell-1)$ and $n:=m/d$. The main theorem establishes, in closed form and with no finite-grid hypothesis, the stabilized value of $S_m(k,\ell)$:

- **Theorem 7.1 (Unified Stabilized Law).** For all $m\ge 2$, all $\ell\ge 2$, and all $k\ge m/d-1$,
  $$S_m(k,\ell)\;=\;\tfrac{m}{\gcd(m,\ell-1)}-1.$$
  PROVEN (this document).

- **Theorem 7.2 (Uniform $k_0$ upper bound).** The threshold at which the stabilized value is first attained satisfies $k_0(m,\ell)\le m/d-1$ whenever $d<m$, and $k_0(m,\ell)=1$ when $d=m$. PROVEN (this document).

- **Theorem 7.3 (Uniform $k_0$ lower bound).** For every $m\ge 2$ and every $\ell\ge 2$ with $d=\gcd(m,\ell-1)<m$,
  $k_0(m,\ell)\ge \lceil (m/d-1)/\sigma(m,\ell)\rceil$,
  where $\sigma(m,\ell)$ is the maximum size of a single $\ell$-safe subset of $\{1,\ldots,m/d-1\}\subseteq\mathbb{Z}/m$. PROVEN (this document).

- **Corollary 7.4 (Prime modulus).** If $m=p$ is prime, then for $k\ge p-1$:
  $S_p(k,\ell)=0$ if $\ell\equiv 1\pmod p$, and $S_p(k,\ell)=p-1$ otherwise. PROVEN.

- Theorems 7.1–7.2 recover the stabilized portions of the phase-4/5 theorems for $m=8,9,11$ as corollaries; the tight $k_0$ values at fixed modulus require extra case analysis and are not settled by the unified theorem alone.

Throughout, the argument depends on nothing beyond arithmetic in $\mathbb{Z}/m$ and the base lemmas of `phase4-m8-proof.md` §2 (restated below for self-containment). No finiteness of a search is used.

## 1. Preliminaries

### 1.1. Definition

Fix $m\ge 2$. For $N\in\mathbb{Z}_{\ge 0}$ and $k\in\mathbb{Z}_{\ge 1}$, a *valid $k$-partition* of $[1,N]$ modulo $m$ with parameter $\ell$ is a partition $[1,N]=C_1\sqcup\cdots\sqcup C_k$ (empty classes allowed) such that every class $C_i$ is *$\ell$-sum-free mod $m$*: there is no tuple $(x_1,\ldots,x_\ell,y)\in C_i^{\ell+1}$ (repetitions allowed) with $x_1+\cdots+x_\ell\equiv y\pmod m$. Set
$$S_m(k,\ell)\;:=\;\sup\{N\ge 0: [1,N]\text{ has a valid $k$-partition}\}\in\mathbb{Z}_{\ge 0}\cup\{\infty\}.$$
By convention the empty partition of $[1,0]$ is vacuously valid, so $S_m(k,\ell)\ge 0$ always. Lemma 1.2 below shows $S_m(k,\ell)\le m-1$ is finite.

### 1.2. Base lemmas (generic $m$)

The three lemmas below are stated and proved for generic $m$ in `phase4-m8-proof.md` §2 for $m=8$; the proofs use only modular arithmetic and are valid for every $m\ge 2$.

**Lemma 1.1 (Residue reduction).** *If $N\le m-1$, the elements $1,2,\ldots,N$ have pairwise distinct nonzero residues mod $m$, all in $\{1,\ldots,m-1\}$. A partition of $[1,N]$ into classes is valid iff each class, viewed as a subset of $\{1,\ldots,m-1\}\subseteq\mathbb{Z}/m$, is $\ell$-safe (i.e. satisfies $\ell C\cap C=\emptyset$ in $\mathbb{Z}/m$, where $\ell C$ is the set of residues of $\ell$-term sums with repetition from $C$).* PROVEN.

**Lemma 1.2 (Universal upper bound $N\le m-1$).** *For every $\ell\ge 1$ and every $k\ge 1$, $S_m(k,\ell)\le m-1$.*

*Proof.* If $N\ge m$, the element $m\in[1,N]$ lies in some class $C$. Taking $x_1=\cdots=x_\ell=m$ gives sum $m\ell\equiv 0\equiv m\pmod m$, and $m\in C$, so the tuple $(m,\ldots,m,m)$ is a relation inside $C$. $\square$ PROVEN.

**Lemma 1.3 (Singleton safety).** *For $r\in\{1,\ldots,m-1\}$, the singleton $\{r\}\subseteq\mathbb{Z}/m$ is $\ell$-safe iff $(\ell-1)r\not\equiv 0\pmod m$. Equivalently, $\{r\}$ is unsafe iff $r$ is a nonzero multiple of $m/\gcd(m,\ell-1)$.*

*Proof.* $\ell\{r\}=\{\ell r\bmod m\}$, so $\ell\{r\}\cap\{r\}\ne\emptyset$ iff $\ell r\equiv r$, i.e. $(\ell-1)r\equiv 0\pmod m$. Setting $d=\gcd(m,\ell-1)$ and writing $\ell-1=d\cdot u$, $m=d\cdot n$ (with $\gcd(u,n)=1$), $(\ell-1)r\equiv 0\pmod m$ iff $du\cdot r\equiv 0\pmod{dn}$ iff $ur\equiv 0\pmod n$ iff $n\mid r$ (using $\gcd(u,n)=1$). $\square$ PROVEN.

**Lemma 1.4 (Monotonicity in $k$).** *If $[1,N]$ admits a valid $k_0$-partition, then for every $k\ge k_0$ it admits a valid $k$-partition.*

*Proof.* Pad with $k-k_0$ empty classes; the empty set is vacuously $\ell$-safe. $\square$ PROVEN.

## 2. Notation for the unified theorem

Fix $m\ge 2$ and $\ell\ge 2$. Define:

- $d:=\gcd(m,\ell-1)\in\{1,2,\ldots,m\}$.
- $n:=m/d\in\{1,2,\ldots,m\}$.

Note $dn=m$ exactly, and $d\mid(\ell-1)$ by definition. In particular $(\ell-1)\cdot n = du\cdot n = u\cdot m\equiv 0\pmod m$ for some integer $u$.

The "boundary" cases:
- $d=1\iff\gcd(m,\ell-1)=1$: then $n=m$, and the unsafe-residue set of Lemma 1.3 is empty.
- $d=m\iff\ell\equiv 1\pmod m$: then $n=1$ and every residue in $\{1,\ldots,m-1\}$ is unsafe (Lemma 1.3 with $r=1$ already fails).

## 3. Upper bound: $S_m(k,\ell)\le m/d-1$

**Proposition 3.1.** *For every $m\ge 2$, every $\ell\ge 2$, and every $k\ge 1$,*
$$S_m(k,\ell)\;\le\;\frac{m}{\gcd(m,\ell-1)}-1\;=\;n-1.$$

*Proof.* We must show: no $N\ge n$ admits a valid $k$-partition.

Assume $N\ge n$ and let $C$ be the (nonempty) class containing the element $n\in[1,N]$ — this element exists because $1\le n\le m\le\ldots$; if $n=m$ (the $d=1$ case), $n=m\le N$ and $m\in[1,N]$; if $n\le m-1$ (the $d\ge 2$ case), $n\in\{1,\ldots,m-1\}\subseteq[1,N]$. Either way $n\in[1,N]$.

Form the tuple $(x_1,\ldots,x_\ell,y):=(n,n,\ldots,n,n)\in C^{\ell+1}$. Its "sum side" is
$$x_1+\cdots+x_\ell \;=\;\ell\,n\;=\;(\ell-1)\,n+n.$$
By definition of $d$, $d\mid\ell-1$; write $\ell-1=d\cdot u$. Then
$$(\ell-1)\,n\;=\;(du)\cdot n\;=\;u\cdot(dn)\;=\;u\cdot m\;\equiv\;0\pmod m.$$
Hence $\ell n\equiv n\pmod m$, so $x_1+\cdots+x_\ell\equiv y\pmod m$ with all entries equal to $n\in C$. This is a forbidden relation inside $C$; $C$ is not $\ell$-sum-free. Contradiction. $\square$ PROVEN.

*Remark.* The argument unifies the classical "element-$m$ is unsafe" proof (Lemma 1.2, the $d=1$ case) and the "$r=m/d$ is unsafe singleton" proof (Lemma 1.3 applied to $r=n$). In the language of Lemma 1.3, Proposition 3.1 is the single observation: **the element $n\in[1,N]$ is itself unsafe as a singleton** (Lemma 1.3 with $r=n$: $(\ell-1)n\equiv 0\pmod m$), *and the unsafety propagates upward*: any class containing $n$ is unsafe, because the $\ell$-tuple witnessing failure for $\{n\}$ still lies in any superset. This is the sketch's "Claim" step, now stated correctly: the contradiction comes from $r=n=y=n$, i.e. $\ell$ copies of $n$ giving sum $\equiv n$ with $n\in C$.

## 4. Lower bound: $S_m(k,\ell)\ge m/d-1$ for $k\ge m/d-1$

**Proposition 4.1.** *For every $m\ge 2$, every $\ell\ge 2$, and every $k\ge n-1 = m/d - 1$,*
$$S_m(k,\ell)\;\ge\;n-1.$$

*(When $n=1$, i.e. $d=m$, the statement reads $S_m(k,\ell)\ge 0$, which is vacuous.)*

*Proof.* If $n=1$ the lower bound is $0$, automatically true. Assume $n\ge 2$. Consider the $(n-1)$-partition of $[1,n-1]$ into singletons:
$$D_r:=\{r\}\qquad (r=1,2,\ldots,n-1).$$
We verify each $D_r$ is $\ell$-safe. By Lemma 1.3, $\{r\}$ is unsafe iff $n\mid r$. For $r\in\{1,\ldots,n-1\}$, $0<r<n$, so $n\nmid r$. Hence every $D_r$ is $\ell$-safe, and $\{D_1,\ldots,D_{n-1}\}$ is a valid $(n-1)$-partition of $[1,n-1]$. By Lemma 1.4, for every $k\ge n-1$ we obtain a valid $k$-partition by padding with empty classes. $\square$ PROVEN.

## 5. Main theorem

**Theorem 7.1 (Unified Stabilized Law).** *For every $m\ge 2$, every $\ell\ge 2$, and every $k\ge m/\gcd(m,\ell-1)-1$,*
$$S_m(k,\ell)\;=\;\frac{m}{\gcd(m,\ell-1)}-1.$$

*Proof.* Combine Proposition 3.1 (upper bound, all $k\ge 1$) and Proposition 4.1 (lower bound, $k\ge n-1$). $\square$ PROVEN.

**Corollary 5.1 (Degenerate case).** *If $\ell\equiv 1\pmod m$, then $S_m(k,\ell)=0$ for every $k\ge 1$.*

*Proof.* $d=m$, $n=1$, Theorem 7.1 gives $S_m(k,\ell)=0$ for $k\ge 0$, i.e. always. $\square$ PROVEN.

## 6. Tight threshold analysis ($k_0$)

Define $k_0(m,\ell)$ to be the least integer $k_0\ge 1$ such that $S_m(k,\ell)=m/d-1$ for every $k\ge k_0$.

**Theorem 7.2 (Uniform $k_0$ upper bound).** *For every $m\ge 2$ and every $\ell\ge 2$,*
$$k_0(m,\ell)\;\le\;\max\!\bigl(1,\;m/\gcd(m,\ell-1)-1\bigr).$$

*Proof.* If $d=m$, Corollary 5.1 gives $k_0=1$. Otherwise $n\ge 2$ and $n-1\ge 1$; Proposition 4.1 exhibits a valid $(n-1)$-partition achieving $N=n-1$, so $k_0\le n-1$. Monotonicity (Lemma 1.4) carries the value upward. Matching the upper bound Proposition 3.1 gives equality. $\square$ PROVEN.

**Theorem 7.3 (Uniform $k_0$ lower bound via covering).** *For every $m\ge 2$ and every $\ell\ge 2$ with $d<m$,*
$$k_0(m,\ell)\;\ge\;\left\lceil\frac{n-1}{\sigma(m,\ell)}\right\rceil,$$
*where*
$$\sigma(m,\ell)\;:=\;\max\bigl\{|C|:C\subseteq\{1,\ldots,n-1\},\;C\text{ is $\ell$-safe mod }m\bigr\}.$$
*(If no class has any $\ell$-safe superset in $\{1,\ldots,n-1\}$, interpret the RHS as $n-1$.)*

*Proof.* Suppose $[1,n-1]$ admits a valid $k$-partition $C_1\sqcup\cdots\sqcup C_k$ achieving $S_m(k,\ell)=n-1$. Each $C_i$ is a subset of $\{1,\ldots,n-1\}$ (since all elements of $[1,n-1]$ have residues in $\{1,\ldots,n-1\}$; moreover $[1,n-1]\subseteq\{1,\ldots,m-1\}$ because $n-1<n\le m$), and each $C_i$ is $\ell$-safe, so $|C_i|\le\sigma(m,\ell)$. Then $n-1=\sum|C_i|\le k\sigma(m,\ell)$, giving $k\ge\lceil(n-1)/\sigma(m,\ell)\rceil$. $\square$ PROVEN.

**Remark (sharpness of $\sigma$).** $\sigma(m,\ell)\in\{1,2,\ldots,n-1\}$. The two extremes:

- *$\sigma=n-1$* (one class suffices): $k_0(m,\ell)=1$. Happens when $\{1,\ldots,n-1\}$ itself is $\ell$-safe mod $m$.
- *$\sigma=1$* (only singletons are safe): $k_0(m,\ell)=n-1$. This is the maximal threshold and matches the sketch's observation that $m=11$, large $\ell$, has $k_0=m-1=10$.

**Corollary 6.1 (Asymptotic $k_0$ for large $\ell$, prime $m$).** *Let $p$ be prime and $\ell\ge p$ with $\ell\not\equiv 1\pmod p$. Then $\sigma(p,\ell)=1$ for $\ell$ sufficiently large, and hence $k_0(p,\ell)=p-1$.*

*Proof sketch (referring to phase5-m11-proof.md §4).* For prime $m=p$ and $\ell\ge p-1$, the $\ell$-sumset of any $2$-element set $C\subseteq\mathbb{Z}/p$ equals all of $\mathbb{Z}/p$ (see phase5 Lemma 4.1, Corollary 4.2, which generalize verbatim from $p=11$ to any prime $p$: for $|C|=2$, $\ell C$ is an arithmetic progression in $\mathbb{Z}/p$ of length $\min(\ell+1,p)$, which equals $\mathbb{Z}/p$ when $\ell+1\ge p$). Hence no $2$-element class is $\ell$-safe, so $\sigma(p,\ell)=1$, so $k_0(p,\ell)\ge p-1$. Combined with Theorem 7.2, $k_0(p,\ell)=p-1$. $\square$ PROVEN (modulo citing phase5-m11-proof.md §4; the proof there is written for $p=11$ but is purely a fact about $\mathbb{Z}/p$ for prime $p$).

**Remark.** The general problem of computing $\sigma(m,\ell)$ and hence tight $k_0(m,\ell)$ for composite $m$ is subtle and residue-dependent. This is why the phase-4 theorem for $m=8$ has $k_0=3$ (the even-$\ell$ witness $\{C_1,C_2,C_3\}$ of §6 uses classes of sizes $4,2,1$, achieving $\sigma=4$), whereas for $m=11$ at large $\ell$, $\sigma=1$ forces $k_0=10$. **CONJECTURED:** for every fixed $m$, $k_0(m,\ell)$ is eventually constant in $\ell$ (periodic in $\ell\bmod m$, once $\ell$ exceeds some threshold depending on $m$); this is supported by the tables in phase2/phase3/phase6 for $m\in\{8,9,10,11,12,13\}$ but is not proven here.

## 7. Corollaries: recovering phase-4/5 stabilized theorems

### 7.1. $m=8$ (phase 4)

Theorem 7.1 with $m=8$ gives: for $k\ge 8/d-1$,
- $\ell\equiv 1\pmod 8\Rightarrow d=8\Rightarrow S_8(k,\ell)=0$; $k_0\le 1$.
- $\ell\equiv 5\pmod 8\Rightarrow d=4\Rightarrow S_8(k,\ell)=1$; $k_0\le 1$.
- $\ell\equiv 3,7\pmod 8\Rightarrow d=2\Rightarrow S_8(k,\ell)=3$; $k_0\le 3$.
- $\ell$ even $\Rightarrow d=1\Rightarrow S_8(k,\ell)=7$; $k_0\le 7$.

The first three rows match the phase-4 theorem exactly. The fourth row gives $k_0\le 7$, whereas phase-4 proves the tight $k_0=3$ (via the explicit three-class witness $C_1=\{1,3,5,7\}, C_2=\{2,6\}, C_3=\{4\}$). Thus Theorem 7.1 *recovers the stabilized value* for $m=8$ but only gives a loose $k_0$ bound for the even-$\ell$ row; the phase-4 witness gives $\sigma(8,\ell)=4$ for $\ell$ even, which via Theorem 7.3 gives only $k_0\ge\lceil 7/4\rceil=2$, so the tight $k_0=3$ requires the explicit SAT-verified impossibility at $k=2$ (phase-4 §9, deferred).

### 7.2. $m=9$ (phase 5)

Theorem 7.1 with $m=9$:
- $\ell\equiv 1\pmod 9\Rightarrow d=9\Rightarrow S_9=0$; $k_0\le 1$.
- $\ell\equiv 4,7\pmod 9\Rightarrow d=3\Rightarrow S_9=2$; $k_0\le 2$.
- $\ell\equiv 0,2,3,5,6,8\pmod 9\Rightarrow d=1\Rightarrow S_9=8$; $k_0\le 8$.

Matches the phase-5 stabilized theorem values exactly. Phase-5 proves a uniform threshold $k_0=4$ for the third row (via the mod-$3$-coset witness $\{1,4,7\},\{2,5,8\},\{3\},\{6\}$ for $\ell\equiv 3\pmod 9$ and variants for other residues). Theorem 7.1's uniform $k_0\le 8$ is weaker but recovers the value.

### 7.3. $m=11$ (phase 5)

Theorem 7.1 with $m=11$:
- $\ell\equiv 1\pmod{11}\Rightarrow d=11\Rightarrow S_{11}=0$; $k_0\le 1$.
- $\ell\not\equiv 1\pmod{11}\Rightarrow d=1\Rightarrow S_{11}=10$; $k_0\le 10$.

Matches phase-5 Theorem 1 exactly, including the uniform $k_0=10$ bound. Corollary 6.1 furthermore shows $k_0\ge 10$ for $\ell\ge p-1=10$ with $\ell\not\equiv 1\pmod{11}$, recovering phase-5's tight-threshold statement in those residues.

### 7.4. Prime modulus ($m=p$ prime)

**Corollary 7.4.** *Let $p$ be prime. Then for every $\ell\ge 2$ and every $k\ge p-1$,*
$$S_p(k,\ell)=\begin{cases}0,&\ell\equiv 1\pmod p,\\ p-1,&\ell\not\equiv 1\pmod p.\end{cases}$$
*Furthermore, for $\ell\ge p-1$ with $\ell\not\equiv 1\pmod p$, $k_0(p,\ell)=p-1$ (tight).*

*Proof.* $\gcd(p,\ell-1)\in\{1,p\}$. If $\ell\equiv 1\pmod p$, $d=p$, apply Corollary 5.1. Otherwise $d=1$, $n=p$, Theorem 7.1 gives $S_p(k,\ell)=p-1$ for $k\ge p-1$. The tight $k_0$ follows from Corollary 6.1. $\square$ PROVEN.

### 7.5. Prime-power modulus ($m=p^e$)

**Corollary 7.5.** *Let $m=p^e$ with $p$ prime and $e\ge 1$. For every $\ell\ge 2$, write $v:=\min(v_p(\ell-1),e)$ where $v_p$ is $p$-adic valuation, so $\gcd(m,\ell-1)=p^v$. Then for $k\ge p^{e-v}-1$,*
$$S_{p^e}(k,\ell)\;=\;p^{e-v}-1.$$

*Proof.* Direct specialization of Theorem 7.1: $d=p^v$, $n=p^{e-v}$. $\square$ PROVEN.

In particular, $m=8=2^3$ recovers the phase-4 list; $m=9=3^2$ recovers the phase-5 list.

## 8. Boundary cases and scope

The unified theorem covers:
- All $m\ge 2$.
- All $\ell\ge 2$.
- All $k\ge m/\gcd(m,\ell-1)-1$, including the degenerate $k\ge 0$ when $\ell\equiv 1\pmod m$.

Excluded (deliberately):
- The boundary regime $1\le k < m/\gcd(m,\ell-1)-1$. This is the "not-yet-stabilized" region, where $S_m(k,\ell)$ can take smaller values depending on $k$; the phase-4 document handles $m=8, k\in\{1,2\}$ explicitly, and the general $k$-row problem is posed but not solved here. Current empirical data for $m\le 13$ suggests these boundary rows are still residue-and-$k$-dependent in a way that resists a single closed form; **CONJECTURED:** the per-row values are eventually periodic in $\ell\bmod m$ for each fixed $k$, but no unified formula is claimed.
- $\ell=1$: excluded by hypothesis $\ell\ge 2$. If $\ell=1$, the defining relation is $x_1\equiv y\pmod m$, and a class is $1$-safe iff it consists of elements whose residues form no solutions, i.e. at most one residue — this reduces to a trivial sum-free condition and is not of interest here.
- $m=1$: trivial; $\mathbb{Z}/1$ is a point, everything is unsafe, $S_1(k,\ell)=0$. Excluded by $m\ge 2$.

No FLAG FOR IMPLEMENTER is needed for the headline Theorem 7.1, Theorem 7.2, Corollary 5.1, Corollary 7.4, or Corollary 7.5: each step is an elementary modular-arithmetic computation.

The tight $k_0$ for composite $m$ at small $\ell$ (e.g. $m=8, \ell$ even, $k_0=3$ vs. our bound $k_0\le 7$) remains **CONJECTURED / EMPIRICALLY VERIFIED only** beyond what the case-specific phase-4/5 documents prove.

## 9. "What next"

Ranked directions for extending the unified theorem:

1. **Tight $k_0$ for composite $m$, small $\ell$** *(highest value)*. Need a structural understanding of $\sigma(m,\ell)$ — the maximum $\ell$-safe subset of $\{1,\ldots,n-1\}\subseteq\mathbb{Z}/m$. The phase-4 even-$\ell$ witness uses $C_1=\{1,3,5,7\}$ (all odd residues, which form a mod-$2$ coset avoiding the even $\ell$-sumset), suggesting: for $d=1$, $\sigma(m,\ell)$ is controlled by the largest coset of a proper subgroup of $\mathbb{Z}/m$ that is $\ell$-safe. CONJECTURE: $\sigma(m,\ell)=\max\{|H|: H<\mathbb{Z}/m \text{ proper subgroup, }\ell H\cap H=\emptyset\}$ (plus possibly off-coset witnesses). Verifying or refuting this on the phase-6 grids for $m\in\{10,12,13\}$ is the natural next SAT probe.

2. **Boundary rows $k\in\{1,2,\ldots,n-2\}$**. Phase-4 solved $m=8,k\in\{1,2\}$ by brute modular checks. The structure is: $S_m(k,\ell)=\max\{N\le m-1: [1,N]$ has a valid $k$-partition$\}$; for small $k$, the classes must be large, so the problem becomes one of covering $\{1,\ldots,N\}$ by few large $\ell$-safe sets. CONJECTURE: for each fixed $k\ge 1$, $S_m(k,\ell)$ is a closed-form function of $(m,\ell\bmod m, d)$ for $\ell\ge\ell_0(m,k)$. Evidence: phase-6 tables.

3. **Generalize Corollary 6.1 to composite $m$**. For composite $m$, what is the smallest $\ell_1(m)$ such that $\sigma(m,\ell)=1$ for all $\ell\ge\ell_1(m)$ with $\gcd(m,\ell-1)=1$? Phase-5 for $m=11$ shows $\ell_1(11)=10=m-1$. CONJECTURE: $\ell_1(m)=m-1$ for all $m\ge 3$, and the large-$\ell$ $2$-element sumset argument of phase5 §4.1 generalizes via: $\ell C$ for $|C|=2, C\subseteq\mathbb{Z}/m$ is an arithmetic progression that covers all of $\mathbb{Z}/m$ once $\ell\ge m-1$, provided the step $a-b\in(\mathbb{Z}/m)^\times$. For composite $m$ the step need not be a unit, so this needs more care.

4. **Formalize in Lean 4**. Theorem 7.1, Proposition 3.1, and Proposition 4.1 are all short and purely combinatorial; each should be tractable for Aristotle or direct Lean formalization. The base lemmas 1.1–1.4 are the prerequisites.

## 10. Appendix: summary table of what the Unified Law predicts

| $(m,\ell\bmod m)$ | $d=\gcd(m,\ell-1)$ | Stabilized value $n-1$ | $k_0$ upper bound |
|---|---|---|---|
| $(m,1)$ | $m$ | $0$ | $1$ |
| $(p,\ne 1)$, $p$ prime | $1$ | $p-1$ | $p-1$ |
| $(8,5)$ | $4$ | $1$ | $1$ |
| $(8,3),(8,7)$ | $2$ | $3$ | $3$ |
| $(8,\text{even})$ | $1$ | $7$ | $7$ |
| $(9,4),(9,7)$ | $3$ | $2$ | $2$ |
| $(9,\text{other}\ne 1)$ | $1$ | $8$ | $8$ |
| $(10,6)$ | $5$ | $1$ | $1$ |
| $(10,3),(10,5),(10,7),(10,9)$ | $2$ | $4$ | $4$ |
| $(10,\text{even}\ne 6,\ne 0)$ and $(10,0)$ | $1$ | $9$ | $9$ |
| $(12,4),(12,10)$ | $3$ | $3$ | $3$ |
| $(12,5),(12,9)$ | $4$ | $2$ | $2$ |
| $(12,3),(12,11)$ | $2$ | $5$ | $5$ |
| $(12,6),(12,8),(12,0)$ | $1$ or $2$ | varies | varies |
| $(12,7)$ | $6$ | $1$ | $1$ |

All values in the "Stabilized value" column are **PROVEN by Theorem 7.1**. The $k_0$ upper bounds are PROVEN by Theorem 7.2 but are not tight in general.
