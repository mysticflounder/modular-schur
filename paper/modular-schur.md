---
title: "A uniform closed form for modular Schur numbers $S_m(k,\\ell)$"
author: Adam McKenna
date: April 2026
abstract: |
  The modular Schur number $S_m(k,\ell)$ of Chappelon--Marchena--Domínguez
  is the greatest $N$ such that $[1,N]$ admits a $k$-partition into classes
  that are $\ell$-sum-free modulo $m$. We record the uniform closed form
  $S_m(k,\ell) = m/\gcd(m,\ell-1) - 1$ for every $m \geq 2$, $\ell \geq 2$,
  and $k \geq m/\gcd(m,\ell-1) - 1$. The formula is a two-paragraph
  corollary of the singleton criterion (Theorem 4) and Corollary 3 of
  D'orville--Sim--Wong--Ho (2025); it extends their Corollary 5 (the
  coprime case $\gcd(m,\ell-1)=1$) to all values of the gcd, and settles
  the stable-$k$ regime of their Problem 1, part 5 for all $m$.
  The main theorem is formalized in Lean 4 with axiom dependencies only
  `propext`, `Classical.choice`, `Quot.sound`. Beyond the closed form, we
  give a sharp $k_0$ for prime moduli via an iterated-sumset saturation
  lemma, and record a small composite counterexample
  ($C = \{1,5\} \subseteq \mathbb{Z}/12$) that refutes the natural
  "only singletons are safe" extrapolation.
header-includes:
  - \usepackage{amsmath,amssymb,amsthm}
  - \usepackage{hyperref}
  - \usepackage{enumitem}
  - \DeclareMathOperator{\Zm}{\mathbb{Z}/m}
  - \newcommand{\Sm}{S_m(k,\ell)}
  - \newtheorem{theorem}{Theorem}[section]
  - \newtheorem{proposition}[theorem]{Proposition}
  - \newtheorem{lemma}[theorem]{Lemma}
  - \newtheorem{corollary}[theorem]{Corollary}
  - \theoremstyle{definition}
  - \newtheorem{definition}[theorem]{Definition}
  - \newtheorem{remark}[theorem]{Remark}
---

# Introduction

The classical Schur number $S(k)$ is the largest $N$ such that $\{1,\ldots,N\}$ admits a $k$-partition into sum-free sets. Values are known only through $S(5) = 160$ \cite{Heule2017}; $S(6)$ is the content of Erdős problem 483 and remains open. Generalizations to longer equations were studied by Beutelspacher and Brestovansky \cite{BB1982} and are now textbook material \cite{LR2014}.

Chappelon, Marchena, and Domínguez \cite{CMD2013} introduced the modular version of the generalized Schur number.

\begin{definition}\label{def:schur}
A set $S \subseteq \mathbb{Z}$ is *$\ell$-sum-free modulo $m$* if no $x_1, \ldots, x_\ell \in S$ (repetitions allowed) and $y \in S$ satisfy $x_1 + \cdots + x_\ell \equiv y \pmod m$. The *modular Schur number* $S_m(k,\ell)$ is the greatest $N \geq 0$ such that $[1,N]$ admits a $k$-partition into $\ell$-sum-free sets modulo $m$.
\end{definition}

Chappelon et al. \cite{CMD2013} closed $m \in \{1,2,3\}$ and observed that the determination of $S_m(k,\ell)$ "seems to be much more difficult for moduli $m \geq 4$" \cite[§6]{CMD2013}. D'orville, Sim, Wong, and Ho \cite{DSWH2025} subsequently closed $m \in \{4,5,6,7\}$ via residue-by-residue case analysis on $\ell \bmod m$, leaving $m \geq 8$ as Problem 1, part 5 of their open problems. The pattern visible across all ten tables (once $k$ is large enough, $S_m(k,\ell)$ is a function of $\gcd(m,\ell-1)$ alone) was not formulated as a unified statement.

Writing $d := \gcd(m, \ell-1)$ and $n := m/d$, the following theorem makes that pattern explicit, with no hypothesis on $m$ and no case split on $\ell \bmod m$.

\begin{theorem}\label{thm:main}
For every $m \geq 2$, $\ell \geq 2$, and $k \geq n - 1$,
$$S_m(k, \ell) = n - 1 = \frac{m}{\gcd(m, \ell - 1)} - 1.$$
\end{theorem}

The proof is elementary: both bounds reduce to the observation that $n$ itself is a singleton that fails $\ell$-sum-freeness. We give it in the next two sections. Theorem \ref{thm:main} settles the stable-$k$ regime ($k \geq n-1$) of \cite[Problem 1, part 5]{DSWH2025} for all $m \geq 2$.

The formula follows from \cite[Theorem 4 + Corollary 3]{DSWH2025} by choosing the optimal singleton: the smallest $a \in [1, m-1]$ for which Corollary 3's hypothesis $\ell \equiv 1 \pmod{m/\gcd(a,m)}$ holds is $a = n$, giving the upper bound $S_m(k,\ell) < n$. \cite{DSWH2025} used Corollary 3 only through Corollary 5 (the coprime case $\gcd(m,\ell-1)=1$, where the hypothesis holds for no $a \leq m-1$); they did not record the optimization for general $\gcd$. The genuinely new content of the present note is the threshold $k_0$ analysis in Section \ref{sec:threshold}: a cyclic-group iterated-sumset saturation lemma (Theorem \ref{thm:coset}), a sharp $k_0$ for prime moduli, and the explicit witness $\{1,5\} \subseteq \mathbb{Z}/12$ showing the prime case does not generalize naively.

## Formalization

The proof is short but has a form that is easy to misstate (we previously confused the role of $n$ versus $m$ in the forbidden tuple). Theorem \ref{thm:main} has been formalized in Lean 4 to remove any doubt; the core closed-form proof was completed by Aristotle \cite{aristotle}. The Lean development defines $S_m(k,\ell)$ both in its original integer form (Definition \ref{def:schur}) as `schurMod` and in its residue-level form as `schurModResidue`; Lemma \ref{lem:residues} below is formalized as the equivalence `schurMod_eq_schurModResidue`, so the machine-verified theorem

```lean
theorem schurMod_eq (m k l : N) (hm : 2 <= m) (hl : 2 <= l)
    (hk : m / Nat.gcd m (l - 1) - 1 <= k) :
    schurMod m k l = m / Nat.gcd m (l - 1) - 1
```

states Theorem \ref{thm:main} verbatim and compiles with axiom dependencies only `propext`, `Classical.choice`, `Quot.sound`. Source is at <https://github.com/mysticflounder/modular-schur>.

## Organization

Section \ref{sec:prelim} establishes base lemmas. Section \ref{sec:upper} proves the upper bound $S_m(k,\ell) \leq n - 1$. Section \ref{sec:lower} proves the matching lower bound. Section \ref{sec:threshold} analyzes the threshold $k_0(m, \ell)$ and records a tight prime-modulus result. Section \ref{sec:corollaries} lists corollaries for specific $m$. Section \ref{sec:open} poses open questions on tight $k_0$ for composite $m$.

# Preliminaries {#sec:prelim}

Throughout, $m \geq 2$ and $\ell \geq 2$ are fixed integers, $d := \gcd(m, \ell-1)$, and $n := m/d$. Note $dn = m$ exactly, and $d \mid (\ell - 1)$ by definition.

\begin{lemma}[Residue reduction]\label{lem:residues}
Let $N \leq m - 1$. The integers $1, 2, \ldots, N$ have pairwise distinct nonzero residues modulo $m$, and a $k$-partition of $[1,N] \subseteq \mathbb{Z}$ into classes $C_1 \sqcup \cdots \sqcup C_k$ is valid (each $C_i$ is $\ell$-sum-free modulo $m$ in the sense of Definition \ref{def:schur}) if and only if the corresponding $k$-partition of the residue set $\{1, \ldots, N\} \subseteq \mathbb{Z}/m$ into $\bar C_1 \sqcup \cdots \sqcup \bar C_k$ has each $\bar C_i$ $\ell$-sum-free modulo $m$. Consequently $S_m(k,\ell)$, as defined on integers in Definition \ref{def:schur}, equals its residue-level counterpart.
\end{lemma}

\begin{proof}
All elements of $[1,N]$ lie in $[1, m-1]$, and $[1, m-1] \hookrightarrow \mathbb{Z}/m$ is injective (if $a \equiv b \pmod m$ with $1 \leq a, b \leq m-1$ then $|a-b| < m$ forces $a = b$). Under this injection each $C_i$ corresponds bijectively to a subset $\bar C_i \subseteq \{1, \ldots, m-1\} \subseteq \mathbb{Z}/m$. For any $(x_1, \ldots, x_\ell; y) \in C_i^\ell \times C_i$, the congruence $x_1 + \cdots + x_\ell \equiv y \pmod m$ in $\mathbb{Z}$ is equivalent to $\bar x_1 + \cdots + \bar x_\ell = \bar y$ in $\mathbb{Z}/m$; conversely every $\ell$-tuple in $\bar C_i$ lifts uniquely to $C_i$. Thus $\ell$-sum-freeness transfers in both directions, and the two definitions of $S_m(k,\ell)$ agree. (This equivalence is formalized in Lean as \texttt{schurMod\_eq\_schurModResidue}.)
\end{proof}

\begin{lemma}[Universal upper bound, Chappelon et al.~2013]\label{lem:univ-upper}
For every $\ell \geq 1$ and every $k \geq 1$, $S_m(k,\ell) \leq m - 1$.
\end{lemma}

\begin{proof}
If $N \geq m$, then $m \in [1,N]$ lies in some class $C$. The tuple $(m, \ldots, m; m) \in C^{\ell+1}$ satisfies $m \cdot \ell \equiv 0 \equiv m \pmod m$, violating $\ell$-sum-freeness. (This is \cite[Eq. (2)]{CMD2013}; formalized in Lean as \texttt{no\_valid\_partition\_of\_ge\_m}, and together with Lemma \ref{lem:residues} justifies the $N \leq m-1$ search cap used in the Lean definition via \texttt{schurMod\_is\_greatest}.)
\end{proof}

\begin{lemma}[Singleton safety]\label{lem:singleton}
For $r \in \{1, \ldots, m-1\}$, the singleton $\{r\} \subseteq \mathbb{Z}/m$ is $\ell$-sum-free modulo $m$ if and only if $(\ell - 1)r \not\equiv 0 \pmod m$; equivalently, if and only if $n \nmid r$.
\end{lemma}

This is \cite[Theorem 4]{DSWH2025} rewritten in the variables natural for our application; we include the derivation for self-containment.

\begin{proof}
$\ell\{r\} \cap \{r\} \neq \emptyset$ iff $\ell r \equiv r \pmod m$ iff $(\ell-1)r \equiv 0 \pmod m$. Write $\ell - 1 = du$ so $\gcd(u, n) = 1$; then $(\ell-1)r \equiv 0 \pmod{dn}$ iff $ur \equiv 0 \pmod n$ iff $n \mid r$.
\end{proof}

\begin{lemma}[Monotonicity in $k$]\label{lem:monotone}
If $[1,N]$ admits a valid $k_0$-partition, then for every $k \geq k_0$ it admits a valid $k$-partition.
\end{lemma}

\begin{proof}
Pad with $k - k_0$ empty classes; the empty set is vacuously $\ell$-sum-free.
\end{proof}

# Upper bound {#sec:upper}

\begin{theorem}\label{thm:unified-upper}
For all $m \geq 2$, $\ell \geq 2$, and $k \geq 1$,
$$S_m(k,\ell) \leq n - 1.$$
\end{theorem}

\begin{proof}
Suppose $N \geq n$. Since $1 \leq n \leq m$, we have $n \in [1, N]$; let $C$ be the class of a valid $k$-partition containing $n$. Write $\ell - 1 = du$ with $u \in \mathbb{Z}$, so
$$(\ell - 1) \cdot n = du \cdot n = u \cdot (dn) = u \cdot m \equiv 0 \pmod m.$$
Hence $\ell n \equiv n \pmod m$. The tuple $(n, \ldots, n; n) \in C^{\ell+1}$ thus witnesses $\ell$-sum-freeness failure in $C$, a contradiction.
\end{proof}

\begin{remark}
Equivalently, this is \cite[Corollary 3]{DSWH2025} applied at $a = n$. That corollary states $S_m(k,\ell) < a$ whenever $\ell \equiv 1 \pmod{m/\gcd(a,m)}$, and the smallest $a \leq m-1$ satisfying the hypothesis is $a = n$: any smaller $a$ has $\gcd(a,m) < n$, so $m/\gcd(a,m) > \gcd(m,\ell-1)$, and the hypothesis $m/\gcd(a,m) \mid (\ell-1)$ would contradict $\gcd(m,\ell-1)$ being maximal.
\end{remark}

\begin{remark}
The two obstructions in prior arguments are the same: "$N \geq m$ is blocked by $m$" (Lemma \ref{lem:univ-upper}, the $d=1$ case $n = m$) and "$r = m/d$ is an unsafe singleton" (Lemma \ref{lem:singleton} at $r = n$). Both reduce to: the single element $n$ is unsafe as a singleton, so any class containing it is unsafe. Once $N \geq n$, some class contains $n$.
\end{remark}

# Lower bound {#sec:lower}

\begin{theorem}\label{thm:unified-lower}
For all $m \geq 2$, $\ell \geq 2$, and $k \geq n - 1$,
$$S_m(k, \ell) \geq n - 1.$$
\end{theorem}

\begin{proof}
If $n = 1$ the conclusion reads $S_m(k,\ell) \geq 0$, vacuously true. Assume $n \geq 2$. Partition $[1, n-1]$ into singletons $D_r := \{r\}$ for $r = 1, \ldots, n-1$. By Lemma \ref{lem:singleton} each $D_r$ is $\ell$-sum-free (since $1 \leq r < n$ forces $n \nmid r$). This is a valid $(n-1)$-partition; for $k \geq n-1$ pad with empty classes by Lemma \ref{lem:monotone}.
\end{proof}

\begin{proof}[Proof of Theorem \ref{thm:main}]
Combine Theorems \ref{thm:unified-upper} and \ref{thm:unified-lower}.
\end{proof}

# The threshold $k_0(m,\ell)$ {#sec:threshold}

Let $k_0(m, \ell)$ denote the least $k$ such that $S_m(k', \ell) = n - 1$ for every $k' \geq k$.

\begin{theorem}\label{thm:k0-upper}
$k_0(m, \ell) \leq \max(1, n - 1)$.
\end{theorem}

\begin{proof}
Theorem \ref{thm:unified-lower} exhibits a valid $(n-1)$-partition achieving $N = n - 1$ when $n \geq 2$. When $n = 1$ the value is zero, achieved trivially at $k = 1$.
\end{proof}

\begin{theorem}[Covering lower bound]\label{thm:k0-lower-cov}
Let $\sigma(m, \ell) := \max\{|C| : C \subseteq \{1, \ldots, n-1\}, C \text{ is } \ell\text{-sum-free mod } m\}$. Then $k_0(m, \ell) \geq \lceil (n-1)/\sigma(m, \ell) \rceil$.
\end{theorem}

\begin{proof}
If $[1, n-1]$ admits a valid $k$-partition, summing class sizes gives $n - 1 \leq k \cdot \sigma(m, \ell)$.
\end{proof}

## Tight threshold for prime modulus

\begin{theorem}[Large-$\ell$ coset criterion]\label{thm:coset}
Let $C \subseteq \mathbb{Z}/m$ with $|C| \geq 2$, pick $a_0 \in C$, and let $H := \langle C - C \rangle = g\mathbb{Z}/m$ with $g := m/|H|$. For every $\ell \geq |H| - 1$,
$$\ell C = \ell a_0 + H,$$
and consequently $C$ is $\ell$-sum-free modulo $m$ if and only if $g \nmid (\ell - 1) a_0$.
\end{theorem}

\begin{proof}[Proof sketch]
$(\subseteq)$ Every $\ell$-sum $\sum c_i = \ell a_0 + \sum (c_i - a_0)$ lies in $\ell a_0 + H$ since $c_i - a_0 \in H$.

$(\supseteq)$ Let $D := C - a_0 \subseteq H$; then $0 \in D$ and $\langle D \rangle = \langle D - D \rangle = \langle C - C \rangle = H$. Since $0 \in D$, the iterated sumsets form an increasing chain $D \subseteq 2D \subseteq 3D \subseteq \cdots \subseteq H$, in which strict inclusions can occur at most $|H| - |D| \leq |H| - 1$ times; hence $kD = (k+1)D$ for some $k \leq |H| - 1$. Once $kD = kD + D$, the set $kD$ is closed under adding any element of $D$, hence under adding any element of $\langle D \rangle = H$, so $kD$ is a union of $H$-cosets; since $0 \in kD \subseteq H$, we get $kD = H$. For every $\ell \geq k$ (in particular $\ell \geq |H| - 1$), $\ell D = kD + (\ell - k)D = H + (\ell - k)D = H$. Therefore $\ell C = \ell a_0 + \ell D = \ell a_0 + H$.

The safety criterion follows: since $C \subseteq a_0 + H$, we have $\ell C \cap C \neq \emptyset$ iff $\ell a_0 + H = a_0 + H$ iff $(\ell - 1) a_0 \in H$ iff $g \mid (\ell - 1) a_0$.
\end{proof}

\begin{remark}
The $(\supseteq)$ direction is a cyclic-group version of the Cauchy--Davenport theorem \cite{Cauchy1813,Davenport1935}: over $\mathbb{Z}/p$ prime, iterating $|A+B| \geq \min(p, |A| + |B| - 1)$ yields $|\ell C| \geq \min(p, \ell(|C|-1) + 1)$, so any non-degenerate $C$ ($|C| \geq 2$) has $\ell C = \mathbb{Z}/p$ once $\ell \geq p - 1$. Theorem \ref{thm:coset} is the saturation statement inside an arbitrary cyclic subgroup $H \leq \mathbb{Z}/m$, with the explicit $\ell \geq |H| - 1$ threshold.
\end{remark}

\begin{corollary}[Sharp $k_0$ for prime moduli]\label{cor:prime-sharp}
Let $p$ be prime. For every $\ell \geq p - 1$ with $\ell \not\equiv 1 \pmod p$,
$$k_0(p, \ell) = p - 1.$$
\end{corollary}

\begin{proof}
For any $|C| \geq 2$ in $\mathbb{Z}/p$, the subgroup $\langle C - C \rangle$ is either $0$ (ruled out) or $\mathbb{Z}/p$ (since $\mathbb{Z}/p$ has no nontrivial subgroups). By Theorem \ref{thm:coset} with $g = 1$, $\ell C = \mathbb{Z}/p$, so $C$ is not $\ell$-sum-free. Hence $\sigma(p, \ell) = 1$, and Theorem \ref{thm:k0-lower-cov} gives $k_0 \geq n - 1 = p - 1$; Theorem \ref{thm:k0-upper} supplies the match.
\end{proof}

## Composite moduli: a counterexample to the natural conjecture

Corollary \ref{cor:prime-sharp} might suggest: for every $m$ and every large $\ell$ with $\gcd(m, \ell - 1) < m$, only singletons are $\ell$-sum-free, so $k_0(m, \ell) = n - 1$. This is false once $m$ is composite.

\begin{proposition}\label{prop:refute-A}
For $m = 12$ and every $\ell \equiv 11 \pmod{12}$ (so $d = 2$, $n = 6$), the set $C = \{1, 5\} \subseteq \{1, \ldots, 5\}$ is $\ell$-sum-free modulo $12$. Consequently $\sigma(12, \ell) \geq 2$ and $k_0(12, \ell) \leq 3 < n - 1$.
\end{proposition}

\begin{proof}
$C - C = \{0, \pm 4\}$, so $\langle C - C \rangle = 4\mathbb{Z}/12 = \{0, 4, 8\}$, $|H| = 3$, $g = 4$. Theorem \ref{thm:coset} applies once $\ell \geq 2$. With $a_0 = 1$, the criterion $4 \nmid (\ell - 1) \cdot 1$ reads $4 \nmid \ell - 1$, i.e. $\ell \not\equiv 1 \pmod 4$. For $\ell \equiv 11 \pmod{12}$ we have $\ell \equiv 3 \pmod 4$, so $4 \nmid \ell - 1$, and $C$ is $\ell$-sum-free, giving $\sigma(12, \ell) \geq 2$.

For the $k_0$ bound, consider the $3$-partition $[1, 5] = \{1, 4\} \sqcup \{2, 5\} \sqcup \{3\}$. Each pair-class has $C - C = \{0, \pm 3\}$, hence $H = \langle 3 \rangle = \{0, 3, 6, 9\}$, $|H| = 4$, $g = 3$; Theorem \ref{thm:coset} applies for $\ell \geq 3$ with safety criterion $3 \nmid (\ell - 1) a_0$. For $\ell \equiv 11 \pmod{12}$ we have $\ell - 1 \equiv 10 \pmod{12}$, and $3 \nmid 10 \cdot 1$ as well as $3 \nmid 10 \cdot 2$, so both $\{1, 4\}$ (with $a_0 = 1$) and $\{2, 5\}$ (with $a_0 = 2$) are $\ell$-sum-free. The singleton $\{3\}$ is safe by Lemma \ref{lem:singleton}: $(\ell - 1) \cdot 3 \equiv 30 \equiv 6 \not\equiv 0 \pmod{12}$. Hence $k_0(12, \ell) \leq 3$.
\end{proof}

# Corollaries: recovered and extended formulas {#sec:corollaries}

Specializing Theorem \ref{thm:main}:

- **$m = 8$:** for $k \geq 7$, $S_8(k, \ell)$ equals $0, 1, 3, 7$ according to $\gcd(8, \ell - 1) \in \{8, 4, 2, 1\}$ (residue pattern $\ell \bmod 8$).
- **$m = 9$:** for $k \geq 8$, $S_9(k, \ell)$ equals $0, 2, 8$ according to $\gcd(9, \ell - 1) \in \{9, 3, 1\}$.
- **$m = 11$:** for $k \geq 10$, $S_{11}(k, \ell) = 0$ if $\ell \equiv 1 \pmod{11}$, else $10$.
- **Prime-power $m = p^e$:** writing $v := \min(v_p(\ell - 1), e)$ where $v_p$ denotes the $p$-adic valuation, for $k \geq p^{e-v} - 1$,
  $$S_{p^e}(k, \ell) = p^{e-v} - 1.$$

All of these stabilized rows are consistent with (and for $m = 4, 5, 6, 7$ recover) the tables of \cite[§2--3]{DSWH2025} and for $m = 1, 2, 3$ the theorems of \cite[§1--2]{CMD2013}.

# What stays open {#sec:open}

1. *Tight $k_0$ for composite $m$.* The covering bound (Theorem \ref{thm:k0-lower-cov}) matches the easy upper bound $n - 1$ for primes but not in general. For $m = 8$, $\ell$ even: $\sigma(8, \ell) = 4$ (witness $\{1, 3, 5, 7\}$), so the covering bound gives only $k_0 \geq 2$, while the true value is $k_0 = 3$. A closed form for $k_0(m, \ell)$ at composite $m$ is open.
2. *Boundary $k < n - 1$.* Theorem \ref{thm:main} only governs $k \geq n - 1$. The smaller-$k$ regime---where classes must be large and $\ell$-sum-free---is empirically eventually periodic in $\ell \bmod m$ for fixed $k$ (verified through $m \leq 13$), but I have no formula.
3. *Optimizing over $\ell$.* For fixed $k$ and $m \to \infty$, what is $\max_\ell S_m(k, \ell)$? The pointwise value is Theorem \ref{thm:main}; the sup over $\ell$ becomes a divisor-counting problem on $m$.

## Acknowledgments

This paper was written collaboratively with Claude (Anthropic), and the Lean 4 proofs were machine-verified by Aristotle (Harmonic) \cite{aristotle}. The informal proofs, formalization, and draft were iterated together over the course of several sessions.

# References

\begin{thebibliography}{9}

\bibitem[Achim et al.~2025]{aristotle}
T. Achim et al.,
\emph{Aristotle: IMO-level Automated Theorem Proving},
2025. arXiv:2510.01346.

\bibitem[Beutelspacher--Brestovansky 1982]{BB1982}
A. Beutelspacher and W. Brestovansky,
\emph{Generalized Schur numbers},
in \emph{Combinatorial Theory} (Schloß Rauischholzhausen, 1982),
Lecture Notes in Mathematics \textbf{969}, Springer, 1982, pp. 30--38.

\bibitem[Cauchy 1813]{Cauchy1813}
A. L. Cauchy,
\emph{Recherches sur les nombres},
J. École Polytech. \textbf{9} (1813), 99--116.

\bibitem[Chappelon et al.~2013]{CMD2013}
J. Chappelon, M. P. Revuelta Marchena, and M. I. Sanz Domínguez,
\emph{Modular Schur numbers},
Electron. J. Combin. \textbf{20}(2) (2013), \#P61. arXiv:1306.5635.

\bibitem[Davenport 1935]{Davenport1935}
H. Davenport,
\emph{On the addition of residue classes},
J. London Math. Soc. \textbf{10} (1935), 30--32.

\bibitem[D'orville et al.~2025]{DSWH2025}
J. D'orville, K. A. Sim, K. B. Wong, and C. K. Ho,
\emph{Modular generalizations of Schur numbers},
Integers \textbf{25} (2025), \#A62.

\bibitem[Heule 2017]{Heule2017}
M. J. H. Heule,
\emph{Schur number five},
Proceedings of AAAI 2018, 6598--6606. arXiv:1711.08076.

\bibitem[Landman--Robertson 2014]{LR2014}
B. M. Landman and A. Robertson,
\emph{Ramsey Theory on the Integers}, 2nd ed.,
Student Mathematical Library \textbf{73}, American Mathematical Society, 2014.

\end{thebibliography}
