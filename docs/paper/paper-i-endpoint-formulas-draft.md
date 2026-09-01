---
title: "Endpoint formulas for modular Schur numbers, with a correction to a prime-power formula"
author: Adam McKenna
date: "September 2026 — draft"
abstract: |
  Fix a modulus $m\ge2$, a sum length $\ell\ge2$, and a number of colors
  $k\ge1$. The modular Schur number $S_m(k,\ell)$ is the largest $N$ for
  which $1,\ldots,N$ can be colored with $k$ colors without a monochromatic
  congruence $x_1+\cdots+x_\ell\equiv y\pmod m$. Writing
  $n=m/\gcd(m,\ell-1)$, we prove the uniform high-color formula
  $$S_m(k,\ell)=n-1\qquad(k\ge n-1).$$
  We also determine the one-color value for every $\ell\ge2$, prove the
  exact high-color threshold for prime moduli when $\ell\ge p-1$ and
  $\ell\not\equiv1\pmod p$, and show
  why the analogous singleton argument fails for composite moduli. Finally,
  we correct a published prime-power formula: a three-coloring proves
  $S_8(3,8)=7$, whereas the printed formula gives $5$. The endpoint formulas,
  residue bridge, universal cap, and singleton criterion
  have Lean 4 formalizations; the prime-threshold and coset arguments remain
  prose proofs. The precise verification boundary is recorded at the end.
---

# 1. Introduction

Schur's theorem says that, however the positive integers are colored with
finitely many colors, one color eventually contains numbers satisfying
$x+y=z$ \cite{LR2014}. Modular Schur numbers ask a finite, cyclic version of this question.
Instead of equality, we use congruence modulo a fixed integer $m$, and instead
of two summands we allow a fixed number $\ell$ of summands.

This paper studies two endpoints of the coloring problem: what happens when
many colors are available, and what happens when only one color is available.
Both endpoints admit short exact formulas. The proofs use only elementary
modular arithmetic, greatest common divisors, and one standard sumset theorem
for the prime-modulus threshold.

The main high-color result is especially simple. Put

$$
d=\gcd(m,\ell-1),\qquad n=\frac m d.
$$

The integer $n$ is the first positive number that defeats every coloring:
$\ell$ copies of $n$ add to $n$ modulo $m$. Every smaller integer, by
contrast, is safe as a singleton. Consequently

$$
S_m(k,\ell)=n-1\qquad\text{whenever }k\ge n-1.
$$

At the other endpoint, when $k=1$, the complete answer is

$$
S_m(1,\ell)=
\begin{cases}
\min\!\left(\ell-1,\left\lfloor m/\ell\right\rfloor\right),&2\le\ell\le m,\\
0,&m<\ell\text{ and }\ell\equiv1\pmod m,\\
1,&m<\ell\text{ and }\ell\not\equiv1\pmod m.
\end{cases}
$$

Modular Schur numbers were introduced by Chappelon, Revuelta Marchena, and
Sanz Domínguez \cite[Sections 1.1--2]{CMD2013}. D'orville, Sim, Wong, and Ho subsequently
developed additional formulas, tables, and open problems \cite{DSWH2025}.
Section 7 corrects one of their prime-power formulas by proving the exact
value $S_8(3,8)=7$.

The paper is written for a reader with roughly one or two years of college
mathematics; no prior number theory is assumed. Section 2 reviews every piece
of modular arithmetic used later. Sections 3--6 give
the endpoint and threshold arguments. Section 8 states exactly which results
have been checked in Lean and what that claim does not include.

# 2. Definitions and elementary tools

For an integer $m\ge2$, two integers $a$ and $b$ are **congruent modulo
$m$**, written $a\equiv b\pmod m$, when $m$ divides $a-b$. Thus congruent
integers have the same remainder after division by $m$. We write
$\mathbb Z/m\mathbb Z$ for the set of the $m$ possible remainders.

Let $C$ be a set of integers. We call $C$ **$\ell$-sum-free modulo $m$** if
there are no $x_1,\ldots,x_\ell,y\in C$ such that

$$x_1+\cdots+x_\ell\equiv y\pmod m.$$

Repetition is allowed: the same member of $C$ may be used several times.

For $N\ge0$, write $[1,N]=\{1,2,\ldots,N\}$, with $[1,0]$ empty. A
**valid $k$-coloring** of $[1,N]$ is a partition of this interval into $k$
$\ell$-sum-free color classes. Empty color classes are harmless. The modular
Schur number is

$$
S_m(k,\ell)=\max\{N:[1,N]\text{ has a valid }k\text{-coloring}\}.
$$

For $N\le m-1$, replacing every integer by its remainder modulo $m$ is
injective on $[1,N]$ and preserves every forbidden congruence. Thus the integer
and residue formulations agree in this range. The universal cap below shows
that no larger value of $N$ can occur.

## 2.1 The universal cap

No valid coloring reaches the integer $m$.

**Lemma 2.1 (universal cap).** For every $m\ge2$, $\ell\ge2$, and $k\ge1$,

$$S_m(k,\ell)\le m-1.$$

**Proof.** If $m$ lies in a color class, then $m\equiv0\pmod m$. Taking all
$\ell$ summands and the target equal to $m$ gives
$\ell m\equiv m\equiv0\pmod m$. That color class is not sum-free. Hence
$[1,m]$ cannot be valid. $\square$

## 2.2 Exactly when a singleton is safe

The following test drives the high-color formula.

**Lemma 2.2 (singleton criterion).** A singleton $\{r\}$ is
$\ell$-sum-free modulo $m$ precisely when

$$m\nmid(\ell-1)r.$$

**Proof.** The only possible choice has all summands and the target equal to
$r$. It is forbidden precisely when $\ell r\equiv r\pmod m$, which says
$m\mid(\ell-1)r$. $\square$

We will repeatedly use Euclid's lemma: if $\gcd(a,b)=1$ and $a\mid bc$, then
$a\mid c$. It follows from the Euclidean algorithm and is standard in a first
course in number theory.

# 3. The uniform high-color formula

Set

$$d=\gcd(m,\ell-1),\qquad n=m/d.$$

Write $\ell-1=du$. Dividing the greatest common divisor by $d$ shows that
$\gcd(u,n)=1$.

**Theorem 3.1 (uniform high-color formula).** Let $m\ge2$, $\ell\ge2$, and
$k\ge1$. If $k\ge n-1$, then

$$
\boxed{S_m(k,\ell)=n-1.}
$$

**Proof. Upper bound.** Since $m=dn$ and $\ell-1=du$,

$$m=dn\mid dun=(\ell-1)n.$$

Lemma 2.2 therefore says that the singleton $\{n\}$ is already unsafe. Any
color class containing $n$ is unsafe as well, because it contains the same
forbidden choice. Thus no coloring of $[1,n]$ can be valid, and
$S_m(k,\ell)\le n-1$.

**Lower bound.** For each $r$ with $1\le r<n$, suppose that
$m\mid(\ell-1)r$. After substituting $m=dn$ and $\ell-1=du$ and cancelling
$d$, we obtain $n\mid ur$. Since $\gcd(u,n)=1$, Euclid's lemma gives
$n\mid r$, impossible for $1\le r<n$. Hence every singleton $\{r\}$ with
$r<n$ is safe. Color the $n-1$ integers separately and leave any extra color
classes empty. This is valid whenever $k\ge n-1$, so
$S_m(k,\ell)\ge n-1$. $\square$

The formula includes the case $n=1$: then the claimed value is $0$, and the
upper-bound argument says that even $1$ is unsafe.

The proof also identifies the obstruction rather than merely counting colors.
The number $n=m/\gcd(m,\ell-1)$ is the first positive integer $r$ for which
$\ell r\equiv r\pmod m$.

# 4. When does the high-color value begin?

Define the **high-color threshold**

$$
k_0(m,\ell)=\min\{k\ge1:S_m(k,\ell)=n-1\}.
$$

Theorem 3.1 gives $k_0(m,\ell)\le n-1$ whenever $n\ge2$. This upper bound is
sometimes sharp and sometimes very far from sharp.

For a finite set $C\subseteq\mathbb Z/m\mathbb Z$, write
$tC=\{c_1+\cdots+c_t:c_i\in C\}$ for its $t$-fold sumset.

## 4.1 Prime moduli

We use the Cauchy--Davenport theorem \cite{Cauchy1813,Davenport1935}:
if $A,B\subseteq\mathbb Z/p\mathbb Z$ and $p$ is prime, then

$$|A+B|\ge\min(p,|A|+|B|-1).$$

Repeated application gives

$$|tC|\ge\min\bigl(p,t(|C|-1)+1\bigr).$$

**Theorem 4.1 (prime threshold).** Let $p$ be prime, let $\ell\ge p-1$, and
assume $\ell\not\equiv1\pmod p$. Then

$$\boxed{k_0(p,\ell)=p-1.}$$

**Proof.** Here $\gcd(p,\ell-1)=1$, so $n=p$ and the high-color value is
$p-1$. Consider a color class $C$ containing at least two residues. The
sumset bound gives

$$|\ell C|\ge\min(p,\ell+1)=p,$$

so $\ell C$ is the whole residue group. In particular, for any $y\in C$
there are $x_1,\ldots,x_\ell\in C$ whose sum is $y$ modulo $p$. Thus no
safe class can contain two elements.

Any valid coloring of $[1,p-1]$ therefore needs at least $p-1$ colors.
Theorem 3.1 supplies a valid coloring with $p-1$ singleton classes. Hence the
threshold is $p-1$. $\square$

## 4.2 Why composite moduli behave differently

Composite residue groups have proper subgroups. Sums can remain trapped in a
coset of such a subgroup, allowing safe classes with more than one element.
The next elementary lemma makes that mechanism explicit.

For $C\subseteq\mathbb Z/m\mathbb Z$, let $\langle C-C\rangle$ denote the
smallest subgroup containing every difference $c-c'$. Every subgroup of
$\mathbb Z/m\mathbb Z$ has the form $g\mathbb Z/m\mathbb Z$ for a divisor
$g$ of $m$.

**Lemma 4.2 (coset saturation).** Let $C$ contain at least two elements,
choose $a\in C$, and write, for a divisor $g\mid m$,

$$H=\langle C-C\rangle=g\mathbb Z/m\mathbb Z.$$

If $t\ge |H|-1$, then $tC=ta+H$. Consequently $C$ is $t$-sum-free precisely
when $g\nmid(t-1)a$.

**Proof.** Put $D=C-a$. Then $0\in D$, $D\subseteq H$, and $D$ generates
$H$. The sets $D,2D,3D,\ldots$ form an increasing chain. If
$jD+D=jD$, then translation by every member of $D$ preserves $jD$.
Translations are bijections, so $jD$ is preserved by the subgroup generated
by $D$, namely all of $H$. Since $jD$ is nonempty, this forces $jD=H$.

Before reaching $H$, the chain grows by at least one element at each step.
It begins with at least two elements, so it reaches $H$ no later than step
$|H|-1$. Thus $tD=H$ and $tC=ta+H$.

The set $C$ lies in the coset $a+H$. A forbidden solution exists precisely
when $a+H$ meets $ta+H$. Two cosets of a subgroup either are disjoint or are
the same, and these two are the same precisely when $(t-1)a\in H$, or
$g\mid(t-1)a$. $\square$

**Proposition 4.3 (a composite counterexample).** If
$\ell\equiv11\pmod{12}$, then

$$k_0(12,\ell)\le3<5=n-1.$$

**Proof.** Here $\gcd(12,\ell-1)=2$, so $n=6$. Use

$$[1,5]=\{1,4\}\sqcup\{2,5\}\sqcup\{3\}.$$

For either pair, the differences generate
$3\mathbb Z/12\mathbb Z=\{0,3,6,9\}$, which has four elements. Since
$\ell\ge11$, Lemma 4.2 applies. For $a=1$ and $a=2$, the safety test is
$3\nmid(\ell-1)a$. The congruence assumption gives
$\ell-1\equiv10\pmod{12}$, so both tests pass. For $\{3\}$, Lemma 2.2 gives
$12\nmid3(\ell-1)$, because $3(\ell-1)\equiv6\pmod{12}$. Thus the displayed
three-coloring is valid. $\square$

# 5. The one-color endpoint

When $k=1$, the entire interval $[1,N]$ is one color class. Two different
obstructions compete when $2\le\ell\le m$: the interval may reach $\ell$,
or an $\ell$-term sum may wrap once around the modulus.

**Theorem 5.1 (one color, $\ell\le m$).** For $m\ge2$ and
$2\le\ell\le m$,

$$
\boxed{S_m(1,\ell)=
\min\!\left(\ell-1,\left\lfloor\frac m\ell\right\rfloor\right).}
$$

**Proof.** Write
$N^*=\min(\ell-1,\lfloor m/\ell\rfloor)$.

First suppose $N\ge\ell$. Then $\ell$ copies of $1$ sum to the target
$\ell$, all inside $[1,N]$. Hence $N$ is invalid and
$S_m(1,\ell)\le\ell-1$.

Next suppose $N\ge\lfloor m/\ell\rfloor+1$. Divide $m+1$ by $\ell$:

$$m+1=q\ell+r,\qquad0\le r<\ell.$$

Take $r$ summands equal to $q+1$ and the remaining $\ell-r$ summands equal
to $q$. Their sum is $m+1\equiv1\pmod m$. The summands and target $1$ all
belong to $[1,N]$: if $r=0$ only $q$ is used, while if $r>0$ the elementary
division bounds give $q+1\le\lfloor m/\ell\rfloor+1\le N$. Therefore
$S_m(1,\ell)\le\lfloor m/\ell\rfloor$.

It remains to show that $[1,N^*]$ is safe. Every ordinary sum of $\ell$
members lies between $\ell$ and $\ell N^*\le m$. Its residue is therefore
one of $\ell,\ell+1,\ldots,m-1,0$. Every possible target lies between $1$
and $N^*\le\ell-1$. These two lists of residues are disjoint. $\square$

The Lean development also closes the range $m<\ell$.

**Theorem 5.2 (complete one-color formula).** For $m\ge2$ and $\ell\ge2$,

$$
S_m(1,\ell)=
\begin{cases}
\min(\ell-1,\lfloor m/\ell\rfloor),&\ell\le m,\\
0,&m<\ell\text{ and }\ell\equiv1\pmod m,\\
1,&m<\ell\text{ and }\ell\not\equiv1\pmod m.
\end{cases}
$$

**Proof.** The first branch is Theorem 5.1. Assume $m<\ell$.

If $\ell\equiv1\pmod m$, then $\ell$ copies of $1$ sum to $1$ modulo $m$,
so even $[1,1]$ is invalid and the value is $0$.

Now assume $\ell\not\equiv1\pmod m$. Lemma 2.2 says that $\{1\}$ is safe,
so the value is at least $1$. We show that $[1,2]$ is unsafe. Let
$a$ be the remainder of $\ell$ modulo $m$. If $a=0$, put $r=1$; otherwise
put $r=m+1-a$. Since $a\ne1$, in either case $1\le r<m<\ell$ and
$\ell+r\equiv1\pmod m$. Choose $r$ of the $\ell$ summands to be $2$ and
the other $\ell-r$ summands to be $1$. Their sum is $\ell+r$, congruent to
the target $1$. Thus $[1,2]$ is invalid and the value is $1$. $\square$

# 6. Immediate consequences

Theorem 3.1 turns every greatest-common-divisor computation into a high-color
value. Two useful specializations are the following.

**Corollary 6.1 (coprime case).** If $\gcd(m,\ell-1)=1$ and $k\ge m-1$,
then $S_m(k,\ell)=m-1$.

**Corollary 6.2 (prime powers).** Let $m=p^a$ with $p$ prime. If
$v_p(\ell-1)=j<a$, then for every $k\ge p^{a-j}-1$,

$$S_{p^a}(k,\ell)=p^{a-j}-1.$$

If $p^a\mid\ell-1$, then $S_{p^a}(k,\ell)=0$ for every $k\ge1$.

Here $v_p(r)$ is the exponent of $p$ in the prime factorization of $r$; for
example, $v_2(40)=3$ because $40=2^3\cdot5$.

# 7. Correction to a published prime-power formula

D'orville, Sim, Wong, and Ho state a prime-power formula in their Theorem 8
\cite[Theorem 8]{DSWH2025}. At $p=2$, exponent $3$, $\ell=8$, and $k=3$, that formula
predicts $S_8(3,8)=5$. The exact value is instead $7$.

**Theorem 7.1.**

$$\boxed{S_8(3,8)=7.}$$

**Proof.** Lemma 2.1 gives the upper bound $S_8(3,8)\le7$. For the lower
bound, color $[1,7]$ as

$$
\{1,3,5,7\}\sqcup\{2,6\}\sqcup\{4\}.
$$

The first class is safe because a sum of eight odd numbers is even, whereas
every possible target in the class is odd. In the second class, suppose that
$r$ of the eight summands are $6$ and the other $8-r$ are $2$. Their sum is

$$6r+2(8-r)=16+4r,$$

whose residue modulo $8$ is $0$ or $4$, never $2$ or $6$. The singleton
$\{4\}$ is safe because eight copies of $4$ sum to $32\equiv0\pmod8$, not
$4$. Thus the coloring is valid and the lower bound is $7$. $\square$

The relevant step in Lemma 2(2) of the printed proof
\cite[Lemma 2(2)]{DSWH2025} treats a congruence with a divisible
coefficient as though it were always solvable. In this instance it becomes

$$2t\equiv1\pmod4,$$

which has no solution: the left side is even and the right side is odd. The
counterexample therefore identifies the failed case directly, rather than
only showing that the final formula is numerically inaccurate.

# 8. Formal verification and trust boundary

The high-color theorem, the integer-to-residue bridge, the universal cap, the
singleton criterion, and both one-color theorems have Lean 4 formalizations in
the accompanying repository. The comparator package restates thirteen public
claims using Mathlib-only definitions. For those configured statements, the
reported transitive axiom closures are contained in

$$\{\texttt{propext},\ \texttt{Classical.choice},\ \texttt{Quot.sound}\},$$

and contain no `native_decide` axiom.

This statement-comparison gate has a deliberately narrow scope. The prime
threshold, coset-saturation lemma, composite example, and literature
correction are proved in ordinary mathematics in this paper but do not yet
have dedicated comparator statements. Additional structural Lean modules in
the project have their own transitive-axiom audit; they are not silently
included in the thirteen-statement comparison.

Thus “formalized in Lean” and “inside the Comparator gate” are separate
claims. The repository records both statuses explicitly.

# 9. Outlook

The endpoint formulas do not determine the smallest number of colors needed
for a composite modulus. Prime moduli are rigid because every nonzero
difference generates the whole residue group. Composite moduli contain proper
subgroups, and Lemma 4.2 shows how a color class can hide inside one of their
cosets.

The natural next question is therefore:

> For fixed composite $m$, and for large $\ell$, determine the exact threshold
> $k_0(m,\ell)$ from the prime-power structure of $m$ and
> $\gcd(m,\ell-1)$.

The companion draft,
[*Prime-power structure of the stable regime for modular Schur numbers*](paper-ii-stable-prime-power-structure-draft.md),
develops a canonical prime-block covering problem for this stable regime. The
present paper does not depend on that structural theory.

# References

\begin{thebibliography}{DSWH25}

\bibitem[Cau1813]{Cauchy1813}
A. L. Cauchy,
\emph{Recherches sur les nombres},
J. École Polytech. \textbf{9} (1813), 99--116.

\bibitem[CMD13]{CMD2013}
J. Chappelon, M. P. Revuelta Marchena, and M. I. Sanz Domínguez,
\emph{Modular Schur numbers},
Electron. J. Combin. \textbf{20}(2) (2013), \#P61. arXiv:1306.5635.

\bibitem[Dav35]{Davenport1935}
H. Davenport,
\emph{On the addition of residue classes},
J. London Math. Soc. \textbf{10} (1935), 30--32.

\bibitem[DSWH25]{DSWH2025}
J. D'orville, K. A. Sim, K. B. Wong, and C. K. Ho,
\emph{Modular generalizations of Schur numbers},
Integers \textbf{25} (2025), \#A62. Theorem 8 and Lemma 2(2), pp. 11--12;
official PDF: \texttt{https://math.colgate.edu/~integers/z62/z62.pdf};
DOI: 10.5281/zenodo.15756071.

\bibitem[LR14]{LR2014}
B. M. Landman and A. Robertson,
\emph{Ramsey Theory on the Integers}, 2nd ed.,
Student Mathematical Library \textbf{73}, American Mathematical Society, 2014.

\end{thebibliography}
