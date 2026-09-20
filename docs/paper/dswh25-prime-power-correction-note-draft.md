---
title: "A correction to a prime-power formula for modular Schur numbers"
author: Adam McKenna
date: "September 2026 — draft"
abstract: |
  Theorem 8 of D'orville, Sim, Wong, and Ho, *Integers* 25 (2025), #A62,
  gives a formula for modular Schur numbers at prime-power moduli. We show
  that its middle branch is false. At the smallest counterexample produced
  by the present analysis, the printed formula gives $S_8(3,8)=5$, while
  the exact value is $S_8(3,8)=7$. We reconstruct the proof, identify the
  failed inference in Lemma 2(2), and verify the counterexample without
  computer search. We then prove a broader replacement result:
  if $p$ is prime, $i\ge1$, and $p\nmid(\ell-1)$, then
  $$S_{p^i}(k,\ell)=p^i-1\qquad\text{for every }k\ge i(p-1).$$
  This gives an infinite family of contradictions to the printed middle
  branch. We finish with a claim-by-claim account of which parts of the
  2025 paper are affected and which are not.
---

# Exact target and status

This note establishes the following four claims.

1. The printed middle branch of Theorem 8 in D'orville--Sim--Wong--Ho
   (2025, pp. 11--12) gives
   $S_8(3,8)=5$.
2. Its supporting Lemma 2(2) is false. The pair $a=2$, $b=6$ satisfies all
   hypotheses of that lemma at $p=2$, $i=3$, and $\ell=8$, but
   $\{2,6\}$ is $8$-sum-free modulo $8$.
3. The correct value is
   $$\boxed{S_8(3,8)=7}.$$
4. More generally, if $p\nmid(\ell-1)$, then
   $$\boxed{S_{p^i}(k,\ell)=p^i-1\quad(k\ge i(p-1)).}$$

Claims 1 and 2 identify the source and logical form of the error. Claims 3
and 4 give corrections. Every mathematical argument needed for these claims
appears below. No SAT calculation is used as a proof, and the general
replacement theorem is not presented as a complete formula for the
lower-color range $k<i(p-1)$.

# 1. The coloring problem

Fix integers $m\ge2$, $k\ge1$, and $\ell\ge2$. A set $C$ of integers is
**$\ell$-sum-free modulo $m$** when there are no
$x_1,\ldots,x_\ell,y\in C$ satisfying

$$x_1+\cdots+x_\ell\equiv y\pmod m.$$

The summands may repeat. This matters throughout the subject: a single
element can make its entire color class unsafe.

The modular Schur number $S_m(k,\ell)$ is the largest $N\ge0$ for which
$[1,N]=\{1,2,\ldots,N\}$ can be partitioned into at most $k$ sets, each
$\ell$-sum-free modulo $m$. Allowing empty colors makes “at most $k$” and
“exactly $k$” interchangeable once a coloring exists.

There is an elementary upper bound that will close both corrected results.

**Lemma 1.1 (universal modulus cap).** For every $m\ge2$, $k\ge1$, and
$\ell\ge2$,

$$S_m(k,\ell)\le m-1.$$

**Proof.** Any coloring of $[1,m]$ assigns a color to $m$. Taking $m$ as
each of the $\ell$ summands gives

$$\underbrace{m+\cdots+m}_{\ell\text{ terms}}\equiv0\equiv m\pmod m.$$

The color containing $m$ is therefore unsafe. Hence $[1,m]$ has no valid
coloring, regardless of the number of colors. $\square$

# 2. What the published theorem says

Let $p$ be prime and let $i$ and $\ell$ be positive integers. Under the
hypotheses

$$\ell\ge p^i-1,\qquad \ell\not\equiv1\pmod p,$$

Theorem 8 of D'orville--Sim--Wong--Ho gives the following three branches

$$
S_{p^i}(k,\ell)=
\begin{cases}
k,
  &1\le k\le p-1,\quad i\ge1,\\[3pt]
up-1,
  &k=p+(u-2),\quad i\ge2,\quad 2\le u\le p^{i-1},\\[3pt]
p^i-1,
  &k\ge p+(p^{i-1}-2),\quad i\ge1.
\end{cases}
\tag{2.1}
$$

The middle branch is the one at issue.

Take

$$p=2,\qquad i=3,\qquad \ell=8,\qquad k=3.$$

The theorem's hypotheses hold because $8\ge2^3-1=7$ and
$8\not\equiv1\pmod2$. In the middle branch,

$$3=2+(u-2),$$

so $u=3$. The printed value is therefore

$$up-1=3\cdot2-1=5.$$

Thus (2.1) asserts

$$S_8(3,8)=5.\tag{2.2}$$

The discrepancy is not a notational issue or an endpoint convention. Section
5 gives a valid coloring of all seven nonzero residues modulo $8$, so the
correct value exceeds $5$ by two.

# 3. The congruence criterion used in the proof

The failed step becomes easier to see after proving the elementary
congruence criterion on which the source relies.

**Lemma 3.1 (linear congruence criterion).** Let $A,B$ be integers and let
$M\ge1$. Put $g=\gcd(A,M)$. The congruence

$$At\equiv B\pmod M\tag{3.1}$$

has an integer solution precisely when $g$ divides $B$.

**Proof.** First suppose that $t$ solves (3.1). Then $M$ divides $At-B$, so
there is an integer $q$ with

$$At-B=qM.$$

Rearranging gives $B=At-qM$. Since $g$ divides both $A$ and $M$, it divides
the right side and hence divides $B$.

For the reverse direction, suppose $g$ divides $B$. Write
$A=gA'$, $M=gM'$, and $B=gB'$. The integers $A'$ and $M'$ are coprime.
Bézout's identity supplies integers $r,s$ with

$$rA'+sM'=1.$$

Multiplying by $B'$ gives

$$A'(rB')+M'(sB')=B'.$$

Reducing modulo $M'$ shows $A'(rB')\equiv B'\pmod{M'}$. Multiplying by
$g$ shows $A(rB')\equiv B\pmod M$, so $t=rB'$ is a solution. $\square$

Two cases deserve emphasis.

- If $\gcd(A,M)=1$, then (3.1) has a solution for every $B$.
- If a prime $p$ divides $A$ and $M$ but does not divide $B$, then (3.1)
  has no solution.

The second case is the obstruction that the published argument discards.
Divisibility of $B$ is a consequence of an already existing solution; it
cannot be used to declare that the divisible-coefficient case itself is
impossible.

# 4. Reconstruction of Lemma 2(2) and its failure

## 4.1 The published setup

Lemma 2(2) of the 2025 paper considers two distinct integers

$$a=k_1p^{j_1},\qquad b=k_2p^{j_2},$$

where

$$gcd(k_1,p)=\gcd(k_2,p)=1,qquad j_1,j_2\ge1,$$

and $1\le a<b\le p^i$. Under the same assumptions on $\ell$ used in
Theorem 8, the lemma claims that $a$ and $b$ cannot belong to one
$\ell$-sum-free set modulo $p^i$.

To force a forbidden relation with target $a$, take $t$ copies of $b$ and
$\ell-t$ copies of $a$. Their sum is

$$(\ell-t)a+tb=\ell a+t(b-a).$$

Requiring this sum to be congruent to $a$ modulo $p^i$ gives

$$
(b-a)t\equiv a(1-\ell)\pmod {p^i}.
\tag{4.1}
$$

The conclusion about whether two elements may share a safe set is symmetric
in the two elements. We may therefore exchange their names, independently of
their ordinary order, so that $j_1\le j_2$. This relabeling is necessary:
$a<b$ alone does not order their $p$-adic valuations. It also gives $j_1<i$.
Indeed, an integer in $[1,p^i]$ with valuation $i$ must be $p^i$, leaving no
distinct larger-valuation element in that interval.

After substituting the factorizations and dividing by $p^{j_1}$, the source's
congruence becomes

$$
\bigl(k_2p^{j_2-j_1}-k_1\bigr)t
  \equiv k_1(1-\ell)\pmod {p^{i-j_1}}.
\tag{4.2}
$$

The modulus $p^{i-j_1}$ is divisible by $p$ because $j_1<i$.

## 4.2 The exact logical error

Set

$$
A=k_2p^{j_2-j_1}-k_1,qquad
B=k_1(1-\ell),qquad
M=p^{i-j_1}.
$$

Because $k_1$ is not divisible by $p$ and
$\ell\not\equiv1\pmod p$, the right side $B$ is not divisible by $p$.
The printed proof considers the possibility $p\mid A$. It observes that a
solution would then force $p\mid B$, and says that this case “cannot occur.”

What cannot occur is a **solution of (4.2)** in that case. The coefficient
itself can certainly be divisible by $p$. Lemma 3.1 then proves that (4.2)
is insoluble. But the purpose of (4.2) was to construct a forbidden sum.
Insolubility removes that proposed forbidden sum; it does not remove the
pair $a,b$.

The inference has the following form:

$$
\begin{array}{c}
p\mid A,\ p\mid M,\ p\nmid B\\
\Downarrow\\
At\equiv B\pmod M\text{ has no solution.}
\end{array}
$$

The printed argument needs the opposite conclusion—existence of a suitable
$t$—to prove that the two elements cannot share a color. This is why the
mistake is substantive rather than a missing sentence.

## 4.3 The surviving and failed subcases

Formula (4.2) also pinpoints the boundary of this particular proof method.

If $j_2>j_1$, then

$$A=k_2p^{j_2-j_1}-k_1\equiv-k_1\not\equiv0\pmod p.$$

Thus $A$ is relatively prime to $p^{i-j_1}$, and Lemma 3.1 supplies a
solution of (4.2). Choose its representative in
$0\le t<p^{i-j_1}$. The source's hypothesis $\ell\ge p^i-1$ gives
$t\le\ell$, so it is a legitimate number of copies of $b$ among the
$\ell$ summands.

If $j_2=j_1$, then $A=k_2-k_1$. There are two possibilities.

- When $k_2\not\equiv k_1\pmod p$, the coefficient is a unit modulo the
  power of $p$, so the same bounded-representative argument makes the
  proposed construction work.
- When $k_2\equiv k_1\pmod p$, the coefficient is divisible by $p$ while
  $B$ is not. The congruence has no solution.

Consequently the source's mixing argument works for distinct valuations and
for different normalized residues modulo $p$. It fails exactly where two
numbers have the same valuation and the same normalized nonzero residue
modulo $p$. Those failed classes become the color classes in the general
correction proved in Section 6.

## 4.4 A concrete counterexample to the lemma

Choose

$$p=2,\quad i=3,\quad \ell=8,\quad a=2,\quad b=6.$$

Every hypothesis of the printed Lemma 2(2) is satisfied:

$$
a=1\cdot2^1,\qquad b=3\cdot2^1,qquad
\gcd(1,2)=\gcd(3,2)=1,qquad 1\le2<6\le8.
$$

Also $8\ge7$ and $8\not\equiv1\pmod2$. Equation (4.1) becomes

$$4t\equiv2(1-8)=-14\equiv2\pmod8.$$

Dividing all terms and the modulus by $2$ gives

$$2t\equiv1\pmod4.\tag{4.3}$$

No integer satisfies (4.3), because $2t$ is even modulo $4$ and $1$ is
odd. In the language of Lemma 3.1,

$$\gcd(2,4)=2\nmid1.$$

This verifies the failed congruence directly. It remains possible that some
other mixture of $2$ and $6$, or the other choice of target, could still
make the set unsafe. The next subsection rules that out completely.

## 4.5 Direct verification that $\{2,6\}$ is safe

Take any eight summands from $\{2,6\}$. If exactly $r$ of them are $6$,
then the other $8-r$ are $2$, where $0\le r\le8$. Their sum is

$$6r+2(8-r)=16+4r.$$

When $r$ is even, this is congruent to $0$ modulo $8$. When $r$ is odd, it
is congruent to $4$ modulo $8$. Therefore the entire eight-fold sumset has
residue set

$$8\{2,6\}=\{0,4\}\pmod8.$$

Neither possible target, $2$ or $6$, belongs to $\{0,4\}$ modulo $8$.
Thus $\{2,6\}$ is $8$-sum-free modulo $8$. This single set disproves the
published Lemma 2(2).

# 5. The exact correction at modulus eight

**Theorem 5.1.**

$$\boxed{S_8(3,8)=7.}$$

**Proof.** Lemma 1.1 with $m=8$ gives $S_8(3,8)\le7$.

For the lower bound, partition $[1,7]$ into

$$
C_1=\{1,3,5,7\},\qquad
C_2=\{2,6\},\qquad
C_3=\{4\}.
\tag{5.1}
$$

We check all three classes.

Every member of $C_1$ is odd. A sum of eight odd integers is even. Reduction
modulo $8$ preserves parity, so such a sum cannot be congruent to any member
of $C_1$.

Section 4.5 computed the full eight-fold sumset of $C_2$: its possible
residues are $0$ and $4$, whereas the possible targets have residues $2$
and $6$. Hence $C_2$ is safe.

The only eight-term sum from $C_3$ is

$$8\cdot4=32\equiv0\pmod8,$$

which is not congruent to its target $4$. Hence $C_3$ is safe.

The partition (5.1) proves $S_8(3,8)\ge7$. Together with the upper bound,
this proves the stated equality. $\square$

The proof is exhaustive despite its short length. Repetition is handled in
$C_1$ by parity, in $C_2$ by the count $r$, and in $C_3$ by the unique
possible repeated sum. No assumption is made that the eight summands are
distinct.

# 6. A general prime-power correction

The counterexample is one member of a natural coloring family. We now prove
the family without relying on Theorem 8 or its Lemma 2.

For a nonzero integer $x$ with $1\le x<p^i$, let $v_p(x)$ be the largest
integer $j$ such that $p^j$ divides $x$. Since $x$ is not divisible by
$p^i$, its valuation satisfies $0\le j\le i-1$. After removing $p^j$, the
integer $x/p^j$ is not divisible by $p$, so it has a unique nonzero residue
$r\in\{1,\ldots,p-1\}$ modulo $p$.

For $0\le j\le i-1$ and $1\le r\le p-1$, define

$$
C_{j,r}=
\left\{x\in[1,p^i-1]:
v_p(x)=j\text{ and }\frac{x}{p^j}\equiv r\pmod p\right\}.
\tag{6.1}
$$

These are the **valuation-and-leading-residue classes**. Every integer in
$[1,p^i-1]$ belongs to exactly one of them, and there are $i(p-1)$ classes.

**Theorem 6.1 (valuation-layer coloring).** Let $p$ be prime, $i\ge1$, and
$\ell\ge2$. If $p\nmid(\ell-1)$, every class $C_{j,r}$ in (6.1) is
$\ell$-sum-free modulo $p^i$.

**Proof.** Fix $j,r$ and choose any
$x_1,\ldots,x_\ell,y\in C_{j,r}$. From the definition of the class, each
of these integers has the form

$$
x_s=p^j(r+pq_s),\qquad y=p^j(r+pq)
$$

for suitable integers $q_s,q$. Reducing modulo $p^{j+1}$ gives

$$x_s\equiv p^jr\pmod {p^{j+1}},\qquad
y\equiv p^jr\pmod {p^{j+1}}.$$

Therefore

$$
x_1+\cdots+x_\ell-y
\equiv(\ell-1)p^jr\pmod {p^{j+1}}.
\tag{6.2}
$$

Neither $r$ nor $\ell-1$ is divisible by $p$. Their product is not divisible
by $p$, so $(\ell-1)p^jr$ is divisible by $p^j$ but not by $p^{j+1}$.
The right side of (6.2) is therefore nonzero modulo $p^{j+1}$.

If the sum were congruent to $y$ modulo $p^i$, their difference would be
divisible by $p^i$. Since $j+1\le i$, it would also be divisible by
$p^{j+1}$, contradicting (6.2). Thus no forbidden relation exists in
$C_{j,r}$. $\square$

**Corollary 6.2 (corrected high-color prime-power range).** Under the
hypotheses of Theorem 6.1,

$$
\boxed{S_{p^i}(k,\ell)=p^i-1
       \qquad\text{for every }k\ge i(p-1).}
\tag{6.3}
$$

**Proof.** The $i(p-1)$ classes in (6.1) give a valid coloring of
$[1,p^i-1]$, so $S_{p^i}(k,\ell)\ge p^i-1$ whenever
$k\ge i(p-1)$. Lemma 1.1 gives the reverse inequality. $\square$

Notice that Theorem 6.1 needs only $p\nmid(\ell-1)$. It does not require the
additional published hypothesis $\ell\ge p^i-1$.

## 6.1 The modulus-eight coloring recovered

For $p=2$ there is only one nonzero residue modulo $2$, so the classes are
just the exact $2$-adic valuation layers. At $i=3$ they are

$$
\begin{array}{c|c|c}
j&\text{condition}&C_{j,1}\\ \hline
0&x\text{ odd}&\{1,3,5,7\}\\
1&2\mid x,\ 4\nmid x&\{2,6\}\\
2&4\mid x,\ 8\nmid x&\{4\}.
\end{array}
$$

Thus (5.1) was not an isolated trick; it was the complete valuation-layer
coloring. Corollary 6.2 yields

$$S_{2^i}(k,\ell)=2^i-1$$

for every even $\ell$ and every $k\ge i$.

## 6.2 An infinite family contradicting the printed middle branch

Let $i\ge3$, take $p=2$, choose any even $\ell\ge2^i-1$, and put $k=i$.
Corollary 6.2 gives

$$S_{2^i}(i,\ell)=2^i-1.\tag{6.4}$$

In the middle branch of (2.1), $p=2$ makes
$k=2+(u-2)=u$, so $u=i$. The condition $2\le i\le2^{i-1}$ holds for every
$i\ge3$. The printed branch therefore gives

$$S_{2^i}(i,\ell)=2i-1.\tag{6.5}$$

For $i\ge3$, $2^i-1>2i-1$. Hence (6.4) and (6.5) disagree for every such
$i$ and $\ell$. Theorem 8 is therefore false as a general statement, not
only at one exceptional parameter tuple.

# 7. What the correction does and does not establish

## 7.1 A corrected local form of the mixing argument

The reconstruction in Section 4 supports the following narrower statement.
Suppose $a=k_1p^{j_1}$ and $b=k_2p^{j_2}$ satisfy the source's unit and range
conditions, with $j_1\le j_2$. The particular mixture targeting $a$ is
produced by (4.2) in either of these cases:

1. $j_1<j_2$;
2. $j_1=j_2$ and $k_1\not\equiv k_2\pmod p$.

When $j_1=j_2$ and $k_1\equiv k_2\pmod p$, that congruence has no solution.
This statement repairs the congruence analysis. It is not a classification of
all two-element safe sets, because some different choice of target or mixture
could still create a forbidden relation in other parameter ranges.

The valuation classes $C_{j,r}$ collect precisely the elements for which the
published mixture can fail under $p\nmid(\ell-1)$. Theorem 6.1 proves more:
the whole class is safe, not merely one selected pair.

## 7.2 The unresolved lower-color range

Corollary 6.2 determines the value once $k\ge i(p-1)$. It does not determine
$S_{p^i}(k,\ell)$ for every smaller $k$. In particular, this note does not
offer a replacement for every value in the printed middle branch. Finding
the exact lower-color thresholds may require understanding which valuation
classes can be merged without creating a forbidden sum.

The distinction is important:

- **proved here:** an exact formula in the range $k\ge i(p-1)$;
- **disproved here:** the published middle branch as a universal formula;
- **not claimed here:** a complete prime-power formula for all $k$.

# 8. Downstream scope in the 2025 paper

The correction should be applied according to proof dependency, not by
withdrawing every result near Theorem 8.

| Item in D'orville--Sim--Wong--Ho | Status after this correction | Reason |
|---|---|---|
| Lemma 2(2) | False as printed | $\{2,6\}$ at $(p,i,\ell)=(2,3,8)$ satisfies its hypotheses and is safe. |
| Theorem 8, middle branch (Case 2) | False as printed | Its upper-bound argument invokes Lemma 2(2), and $S_8(3,8)$ directly contradicts its value. |
| Theorem 8 as one complete piecewise theorem | False as printed | One branch of a piecewise equality is false. |
| Theorem 8, first branch (Case 1) | Not affected by this error | The written proof uses Lemma 2(1), not Lemma 2(2). |
| Theorem 8, final branch (Case 3) | Numerical conclusion remains valid | Its construction reaches $p^i-1$, and the universal modulus cap supplies the matching upper bound. This does not assert that its stated color threshold is minimal. |
| Corollary 8 for prime moduli | Its statement is recoverable, but its dependency should be repaired | It specializes to $i=1$, where the disputed middle branch is absent. Because the printed derivation cites Theorem 8 as a whole, it should instead cite the unaffected Case 1 and Case 3 arguments directly. |
| Example 1: $S_8(4,8)=7$ | Value remains correct; one upper-bound explanation is invalid | The displayed lower coloring is valid, and Lemma 1.1 gives the upper bound. The claim that all of $2,4,6,8$ must be singletons uses the false Lemma 2(2). |
| Theorems 6 and 7 | No dependency on this error found in the written proofs | Their case arguments do not invoke Lemma 2(2). |
| Theorems 9 and 10 | Numerical conclusions are recoverable; citation chain needs repair | They invoke Corollary 8. Replacing that citation by the unaffected $i=1$ Case 1 and Case 3 arguments removes the path through Theorem 8 as a whole. |
| Open Problem 1 | Unaffected | Correcting a claimed formula does not alter the questions as posed. |

“Not affected” in this table has a limited meaning: the identified error in
Lemma 2(2) is not a dependency of the stated item. It is not a new independent
verification of every line of that item. Likewise, the surviving value in
Example 1 does not rescue its unnecessary singleton argument.

# 9. Verification record and trust boundary

The proof of $S_8(3,8)=7$ in Section 5 is elementary and independent of
software. The project also contains a SAT-produced coloring that agrees with
(5.1), but no SAT output is needed for the theorem. In particular, the upper
bound is Lemma 1.1, not a recorded unsatisfiability certificate.

The generic universal cap has a Lean 4 proof in the accompanying repository.
The valuation-layer theorem, the source reconstruction, and the correction
to Theorem 8 are presently prose mathematics. They do not have dedicated
Mathlib-only Comparator statements. This note therefore does not label the
full correction “Lean-verified.”

The archived source PDF used for the source audit is the journal version of
DSWH25. Its SHA-256 digest is

```
d76426b767d55d6f567d8a238137f90a70d4ca6f251a4fda084f142457813388
```

This digest identifies the document examined; it is not evidence for any
mathematical claim by itself.

# 10. Completion matrix

| Obligation | Status | Evidence in this note | Load-bearing? |
|---|---|---|---|
| State the published formula and its hypotheses | Proven by source audit | Section 2; DSWH25, Theorem 8 | Yes |
| Derive the printed value $S_8(3,8)=5$ | Proven | Section 2 arithmetic | Yes |
| Prove the linear congruence criterion | Proven | Lemma 3.1 | Yes |
| Locate the failed inference in Lemma 2(2) | Proven by source reconstruction and Lemma 3.1 | Section 4.2 | Yes |
| Check every hypothesis of the counterexample | Proven | Section 4.4 | Yes |
| Prove $\{2,6\}$ is safe, including all repetitions | Proven | Section 4.5 | Yes |
| Construct a valid three-coloring of $[1,7]$ | Proven | Theorem 5.1 | Yes |
| Prove that $[1,8]$ cannot be colored | Proven | Lemma 1.1 | Yes |
| Establish $S_8(3,8)=7$ | Proven | Theorem 5.1 | Yes |
| Prove the valuation-layer coloring | Proven | Theorem 6.1 | Yes for the general correction |
| Prove the corrected high-color prime-power formula | Proven | Corollary 6.2 | Yes for the general correction |
| Show infinitely many disagreements with the printed branch | Proven | Section 6.2 | No for the smallest counterexample |
| Determine all lower-color prime-power values | Open; not claimed | Section 7.2 | No |
| Formalize the full correction in Lean | Not yet done; not claimed | Section 9 | No |

# 11. Conclusion

The error in the 2025 prime-power formula comes from a reversed use of the
linear congruence solvability criterion. When the reduced coefficient is
divisible by $p$ but the right side is not, the desired congruence has no
solution. The published proof treats that outcome as excluding the
coefficient case, even though the coefficient case occurs for numbers with
the same $p$-adic valuation and the same normalized residue modulo $p$.

At modulus $8$, those numbers form the safe class $\{2,6\}$. Together with
the odd residues and $\{4\}$, it yields a three-coloring of $[1,7]$ and the
exact correction $S_8(3,8)=7$.

The same structure extends to every prime power. Partitioning by valuation
and normalized nonzero residue produces $i(p-1)$ safe classes whenever
$p\nmid(\ell-1)$. This proves the exact value $p^i-1$ in that color range and
generates infinitely many counterexamples to the printed middle branch. The
remaining lower-color values are a separate problem and are left open here.

# References

1. S. Chappelon, M. Revuelta Marchena, and M. Sanz Domínguez,
   “Modular Schur numbers,” *Graphs and Combinatorics* **29** (2013),
   1055--1070.

2. J. D'orville, K. A. Sim, K. B. Wong, and C. K. Ho,
   “Modular generalizations of Schur numbers,” *Integers* **25** (2025),
   Paper A62, <https://math.colgate.edu/~integers/z62/z62.pdf>.
