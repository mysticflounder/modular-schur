---
title: "Prime-power structure of the stable regime for modular Schur numbers"
author: Adam McKenna
date: "June 2026, revised 30 August 2026"
abstract: |
  Choose a modulus $m$ and a length $\ell$. The *modular Schur number*
  $S_m(k,\ell)$, introduced by Chappelon, Revuelta Marchena, and Sanz
  Domínguez, is the largest $N$ for which $1, 2, \ldots, N$ can be colored
  with $k$ colors so that no color class contains a solution of
  $x_1 + \cdots + x_\ell \equiv y \pmod m$.

  Our main result is a single closed form valid for every modulus. Writing
  $n := m/\gcd(m,\ell-1)$, we show that once $k \geq n-1$,
  $$S_m(k,\ell) = n - 1 = \frac{m}{\gcd(m,\ell-1)} - 1.$$
  The mechanism is one *self-defeating* value: $\ell$ copies of $n$ sum to
  $n$ modulo $m$, so even the lone class $\{n\}$ already breaks the rule,
  while every smaller value is safe. The identity is a short corollary of
  the singleton criterion and Corollary 3 of D'orville, Sim, Wong, and Ho
  (2025), extending their coprime case (Corollary 5) to every gcd and
  settling the large-$k$ regime of their Problem 1, part 5.

  We then ask how many colors are actually needed before the formula takes
  hold, the threshold $k_0(m,\ell)$. For a prime modulus $p$, when
  $\ell \geq p - 1$ and $\ell \not\equiv 1 \pmod p$, the threshold is
  exactly $k_0(p,\ell) = p - 1$; the value is already implicit in
  Corollary 8 of D'orville et al., and we recover it by a saturation lemma
  of Cauchy--Davenport type. This breaks for composite moduli: in
  $\mathbb{Z}/12$ the pair $\{1,5\}$ is a safe two-element class for suitable
  $\ell$, refuting the natural guess that only singletons are safe. We also
  settle the single-color case,
  $S_m(1,\ell) = \min(\ell-1, \lfloor m/\ell \rfloor)$ for
  $2 \leq \ell \leq m$ (their Problem 1, part 3).

  The composite threshold stays open, but we reduce it to one finite
  question. In the stable regime $\ell \geq m - 1$ the threshold depends
  only on $\ell \bmod m$; for that stable threshold $k_0^\infty$, a uniform
  "$K + \tau$" schema collapses each family of pairs sharing the same $n$
  to finitely many *cells*. On them we prove a
  *Coordinate-Union Edge Rule* (each cell's conflict graph is a union of
  coordinate cliques) and a *separated-fiber* criterion
  (whenever every axis separates a fiber's atoms, the fiber pins down its
  exact cover). Separation is automatic for single-axis fibers and holds
  computationally for $60$--$74\%$ of fibers on the family
  $n = 55 \cdot 2^a$. The remaining fibers we leave open: a
  uniform closed form for the residual-cover number $\tau$ would require
  that each still admits a matching cover-and-packing witness, which holds
  on almost every case we computed but fails on certified fibers both
  dyadic ($n = 880$: packing $48$, cover $50$) and not (a $3^3$ axis
  forces counterexamples at $n \in \{330, 660\}$), so $\tau$ at
  composite $m$ stays conjectural.
header-includes:
  - \usepackage{amsmath,amssymb,amsthm}
  - \usepackage{hyperref}
  - \usepackage{enumitem}
  - \clubpenalty=10000
  - \widowpenalty=10000
  - \displaywidowpenalty=10000
  - \usepackage{caption}
  - \captionsetup{font=small,labelfont=bf,labelsep=period,justification=justified}
  - \newsavebox{\figbox}
  - \usepackage{tikz}
  - \usetikzlibrary{arrows.meta,backgrounds}
  - \definecolor{figbg}{HTML}{FBF6EC}
  - \definecolor{figbd}{HTML}{E6D6BE}
  - \definecolor{clsH}{HTML}{3A5A78}
  - \definecolor{clsP}{HTML}{FBF6EC}
  - \definecolor{clsB}{HTML}{E6D6BE}
  - \definecolor{modH}{HTML}{C0563E}
  - \definecolor{modP}{HTML}{FCF3E9}
  - \definecolor{modB}{HTML}{ECD8C2}
  - \definecolor{addX}{HTML}{3A5A78}
  - \definecolor{addF}{HTML}{DBE5F0}
  - \definecolor{sumX}{HTML}{C0563E}
  - \definecolor{sumF}{HTML}{F5DCD1}
  - \definecolor{sumD}{HTML}{9A3B2A}
  - \definecolor{accY}{HTML}{D9A441}
  - \definecolor{accF}{HTML}{F2E2BD}
  - \definecolor{accD}{HTML}{8A6A1F}
  - \definecolor{brX}{HTML}{7A6A55}
  - \definecolor{ink}{HTML}{3D405B}
  - \definecolor{mut}{HTML}{8A7E6B}
  - \definecolor{lin}{HTML}{B9AC97}
  - \definecolor{lin2}{HTML}{CBBDA2}
  - \definecolor{bnP}{HTML}{FBEFD3}
  - \definecolor{bnB}{HTML}{EBD7A8}
  - \definecolor{bnT}{HTML}{5A5022}
  - \tikzset{figcard/.style={show background rectangle, background rectangle/.style={fill=figbg, draw=figbd, line width=1pt, rounded corners=6pt}, inner frame sep=8pt}}
  - \tikzset{callout/.style={draw=figbd, fill=figbg, line width=1.1pt, rounded corners=6pt, inner sep=11pt}}
  - \tikzset{fighd/.style={font=\small\bfseries, text=white, fill=ink, rounded corners=3pt, inner xsep=8pt, inner ysep=3pt, align=center}}
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

The classical Schur number $S(k)$ is the largest $N$ such that $\{1,\ldots,N\}$ can be split into $k$ groups, each containing no solution to $x + y = z$ with $x, y, z$ in the same group. Think of it as a coloring game: color the integers $1$ through $N$ with $k$ colors, and call each color's *class* the set of integers that receive that color (so the $k$ classes are exactly the $k$ groups above). The coloring wins when no class contains two numbers that add up to a third number of that same class (Figure \ref{fig:schur-game}). Values are known only through $S(5) = 160$ \cite{Heule2017}; $S(6)$ is unknown, and the growth rate of $S(k)$ is Erdős problem 483. Generalizations to longer equations ($x_1 + \cdots + x_\ell = y$) were studied by Beutelspacher and Brestovansky \cite{BB1982} and are now textbook material \cite{LR2014}.

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, x=1cm, y=1cm,
   rtile/.style={rounded corners=2pt, draw=sumX, fill=sumF, minimum size=8mm, inner sep=0pt, font=\small},
   btile/.style={rounded corners=2pt, draw=addX, fill=addF, minimum size=8mm, inner sep=0pt, font=\small},
   op/.style={font=\large, text=ink},
   capt/.style={font=\scriptsize, align=center, text width=3.8cm}
]
  % ---- left: the solution 1+2=3, all in one class (forbidden) ----
  \node[font=\small\bfseries, sumX] at (1.3,2.45) {forbidden};
  \node[rtile] (x1) at (0,1.5)    {$1$};
  \node[op]         at (0.65,1.5) {$+$};
  \node[rtile] (x2) at (1.3,1.5)  {$2$};
  \node[op]         at (1.95,1.5) {$=$};
  \node[rtile] (x3) at (2.6,1.5)  {$3$};
  \node[capt, sumD] at (1.3,0.5)
    {$1,2,3$ in one class:\\ $1{+}2=3$ is monochromatic};
  % divider
  \draw[lin2] (3.5,0.0) -- (3.5,2.6);
  % ---- right: the same solution, split across two colors (allowed) ----
  \node[font=\small\bfseries, addX] at (5.7,2.45) {allowed};
  \node[rtile] (y1) at (4.4,1.5)  {$1$};
  \node[op]         at (5.05,1.5) {$+$};
  \node[btile] (y2) at (5.7,1.5)  {$2$};
  \node[op]         at (6.35,1.5) {$=$};
  \node[btile] (y3) at (7.0,1.5)  {$3$};
  \node[capt] at (5.7,0.5)
    {$1$ and $2{,}3$ in different classes:\\ $1{+}2=3$ is split across classes};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{The Schur coloring game: a coloring of $1,\dots,N$ is valid when no class contains a solution of $x+y=z$, here $1+2=3$. The valid $2$-coloring $\{1,4\},\{2,3\}$ of $\{1,\dots,4\}$ gives $S(2)=4$. This paper forbids instead the longer congruence $x_1+\cdots+x_\ell\equiv y \pmod m$.}
\label{fig:schur-game}
\end{minipage}
\end{figure}

Why study such numbers? Schur's theorem, that every finite coloring of the positive integers leaves some color class with a solution of $x + y = z$, is a founding result of Ramsey theory; Schur proved it in 1916 as a step toward Fermat's Last Theorem modulo a prime, showing that $x^n + y^n \equiv z^n \pmod p$ has a nonzero solution for all sufficiently large $p$ \cite{LR2014}. The relation $x + y = z$ is the simplest partition-regular equation, the prototype for Rado's theory of which linear systems force a monochromatic solution, and $S(k)$ records the exact threshold at which that force takes hold. The numbers are notoriously hard to compute, the value $S(5) = 160$ above being both the current frontier and a landmark of computer-generated proof \cite{Heule2017}. The modular variant studied here keeps the same coloring game but turns each color class into an $\ell$-sum-free set in the cyclic group $\mathbb{Z}/m$; this brings additive combinatorics to bear, for instance the Cauchy--Davenport inequality of Section \ref{sec:threshold}, and, as the results below show, makes exact closed forms attainable where the classical numbers resist them.

Chappelon, Revuelta Marchena, and Sanz Domínguez \cite{CMD2013} introduced a modular twist: instead of requiring $x_1 + \cdots + x_\ell = y$ exactly, they only forbid $x_1 + \cdots + x_\ell \equiv y \pmod{m}$. This is the modular Schur number $S_m(k, \ell)$.

\begin{definition}\label{def:schur}
A set $S \subseteq \mathbb{Z}$ is \emph{$\ell$-sum-free modulo $m$} if no $x_1, \ldots, x_\ell \in S$ (repetitions allowed) and $y \in S$ satisfy $x_1 + \cdots + x_\ell \equiv y \pmod m$. The \emph{modular Schur number} $S_m(k,\ell)$ is the greatest $N \geq 0$ such that $[1,N]$ admits a $k$-partition into $\ell$-sum-free sets modulo $m$.
\end{definition}

In other words: $S_m(k,\ell)$ is the largest list of positive integers that can be colored with $k$ colors so that no color class contains the forbidden modular equation. Figure \ref{fig:classical-modular} contrasts the two notions side by side.

\begin{figure}[!t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[x=1cm, y=1cm, font=\small,
   panelC/.style={rounded corners=6pt, draw=clsB, fill=clsP, line width=1pt},
   panelM/.style={rounded corners=6pt, draw=modB, fill=modP, line width=1pt},
   hdrC/.style={rounded corners=4pt, fill=clsH, text=white, font=\bfseries\small, minimum height=7.5mm, minimum width=56mm},
   hdrM/.style={rounded corners=4pt, fill=modH, text=white, font=\bfseries\small, minimum height=7.5mm, minimum width=56mm},
   eqbox/.style={rounded corners=5pt, draw=bnB, fill=white, line width=0.8pt, minimum height=10mm, inner xsep=7pt},
   note/.style={font=\scriptsize, align=center, text=mut},
   genarr/.style={-{Stealth[length=3.2mm]}, line width=1.2pt, brX},
   tk/.style={lin}
]
\def\clockR{1.5}
% ===== background panels =====
\filldraw[panelC] (0.05,0.15) rectangle (6.35,9.95);
\filldraw[panelM] (9.05,0.15) rectangle (15.35,9.95);

% ===== top banner: the shared coloring game =====
\filldraw[rounded corners=6pt, fill=bnP, draw=bnB, line width=1pt] (0.05,10.1) rectangle (15.35,11.6);
\node[font=\small, align=center, text=bnT, text width=14.4cm] at (7.7,10.85)
   {Both are the \emph{same} coloring game: split $1,2,\dots,N$ into $k$ color classes so that \textcolor{ink}{\textbf{no class contains a solution of the boxed equation}}; the Schur number is the largest $N$ that works. The two notions differ only in \emph{which} equation is banned.};

% ===== headers =====
\node[hdrC] at (3.2,9.35) {CLASSICAL\quad $S(k)$};
\node[hdrM] at (12.2,9.35) {MODULAR\quad $S_m(k,\ell)$};

% ===== equations =====
\node[eqbox] at (3.2,8.05) {$\textcolor{addX}{x} + \textcolor{addX}{y} = \textcolor{sumX}{z}$};
\node[note] at (3.2,7.25) {banned: two terms, exact equality};
\node[eqbox] at (12.2,8.05) {$\textcolor{addX}{x_1}+\cdots+\textcolor{addX}{x_\ell} \equiv \textcolor{sumX}{y} \pmod m$};
\node[note] at (12.2,7.25) {banned: $\ell$ terms, equality mod $m$};

% ===== left visual: number line, exact landing =====
\draw[tk, -{Stealth[length=2.2mm]}] (0.65,4.9) -- (5.95,4.9);
\node[font=\scriptsize, tk, anchor=west] at (5.7,5.18) {$\mathbb{Z}$};
\foreach \i/\x in {1/1.0, 2/1.8, 3/2.6, 4/3.4, 5/4.2, 6/5.0} {
   \draw[tk] (\x,4.9) -- (\x,4.7);
}
% neutral integers
\foreach \i/\x in {4/3.4, 5/4.2, 6/5.0} {
   \node[font=\scriptsize, anchor=north, text=lin] at (\x,4.68) {$\i$};
   \fill[lin] (\x,4.9) circle (1.1pt);
}
% addends 1,2 (blue) and forbidden sum 3 (rose)
\foreach \i/\x in {1/1.0, 2/1.8} {
   \node[font=\scriptsize, anchor=north, text=addX] at (\x,4.68) {$\i$};
   \fill[addX] (\x,4.9) circle (2.2pt);
}
\node[font=\scriptsize, anchor=north, text=sumX] at (2.6,4.68) {$3$};
\fill[sumX] (2.6,4.9) circle (2.2pt);
\draw[-{Stealth[length=2.2mm]}, sumX, line width=1pt] (1.0,5.02) to[bend left=58] (2.6,5.02);
\node[sumX, font=\scriptsize] at (1.8,5.95) {$+2$};
\node[note, text=mut] at (3.2,3.55) {a banned triple: $\textcolor{addX}{1}{+}\textcolor{addX}{2}=\textcolor{sumX}{3}$\\ (so $\textcolor{addX}{1},\textcolor{addX}{2},\textcolor{sumX}{3}$ can't share a color)};

% ===== right visual: clock Z/12, wraparound =====
\begin{scope}[shift={(12.2,5.0)}]
   \draw[tk] (0,0) circle (\clockR);
   \node[font=\scriptsize, text=lin] at (0,0) {$\mathbb{Z}/12$};
   \foreach \i in {0,...,11} {
     \node[circle, draw=lin2, fill=white, minimum size=4.8mm, inner sep=0pt, font=\scriptsize, text=mut]
        (r\i) at ({90-\i*30}:\clockR) {\i};
   }
   % running partial sums 0,5,10 (blue); landing residue 3 (rose)
   \foreach \i in {0,5,10} {
     \node[circle, draw=addX, fill=addF, minimum size=4.8mm, inner sep=0pt, font=\scriptsize, text=ink]
        at ({90-\i*30}:\clockR) {\i};
   }
   \node[circle, draw=sumX, fill=sumF, minimum size=4.8mm, inner sep=0pt, font=\scriptsize\bfseries, text=sumD]
        at ({90-3*30}:\clockR) {3};
\end{scope}
\draw[-{Stealth[length=2mm]}, addX, line width=1pt] (r0) to[bend left=55] (r5);
\draw[-{Stealth[length=2mm]}, addX, line width=1pt] (r5) to[bend left=55] (r10);
\draw[-{Stealth[length=2mm]}, sumX, line width=1.1pt] (r10) to[bend left=58] (r3);
\node[note, text=mut] at (12.2,3.0) {a banned relation: $\textcolor{addX}{5}{+}\textcolor{addX}{5}{+}\textcolor{addX}{5}\equiv \textcolor{sumX}{3}$\\ (the sum wraps: $\textcolor{addX}{15}\equiv \textcolor{sumX}{3} \bmod 12$)};

% ===== center: the two generalizations =====
\node[font=\scriptsize\bfseries, text=bnT, align=center] at (7.7,8.6) {two\\generalizations};
\draw[genarr] (6.55,6.55) -- (8.85,6.55);
\node[note] at (7.7,6.95) {\textbf{1.} sum of $\ell$ terms};
\draw[genarr] (6.55,4.85) -- (8.85,4.85);
\node[note] at (7.7,5.25) {\textbf{2.} equality $\to$ mod $m$};

% ===== color key =====
\node[note, align=center, text width=2.6cm] at (7.7,2.7)
   {\textbf{color key}\\ \textcolor{addX}{\textbf{addends}} land on the\\ \textcolor{sumX}{\textbf{forbidden}} third value};

% ===== status lines =====
\node[note, text=mut] at (3.2,1.3) {known only through $S(5)=160$;\\ $S(6)$ open; growth is Erdős 483};
\node[note, text=mut] at (12.2,1.25) {closed form (\textcolor{modH}{\textbf{our contribution}}):\\[1pt] $\textcolor{ink}{S_m(k,\ell)=\dfrac{m}{\gcd(m,\ell-1)}-1}$};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{Two notions of Schur number, one game. In both, one splits $1,2,\dots,N$ into $k$ color classes so that no class contains a solution of the boxed equation, and the Schur number is the largest $N$ for which a valid coloring exists. The notions differ only in which equation is banned. \emph{Classical} (left): $x+y=z$, two terms and exact, so a banned triple is something like $1+2=3$; the values are known only through $S(5)=160$, with $S(6)$ unknown and the growth rate of $S(k)$ the subject of Erdős problem 483. \emph{Modular} (right): the equation has $\ell$ terms and is read modulo $m$, so like macaroni in a pot, a banned relation can wrap around the clock $\mathbb{Z}/m$, as in $5+5+5=15\equiv 3 \bmod 12$. Modular Schur thus generalizes classical Schur in two ways, more terms and reduction mod $m$; our contribution is the closed form $S_m(k,\ell)=m/\gcd(m,\ell-1)-1$ in the stable-$k$ regime.}
\label{fig:classical-modular}
\end{minipage}
\end{figure}

Chappelon et al. \cite{CMD2013} settled the small cases $m \in \{1,2,3\}$ and noted that the determination of $S_m(k,\ell)$ "seems to be much more difficult for moduli $m \geq 4$" \cite[§6]{CMD2013}. D'orville, Sim, Wong, and Ho \cite{DSWH2025} subsequently settled $m \in \{4,5,6,7\}$ by working through every possible value of $\ell \bmod m$ case by case, leaving $m \geq 8$ as Problem 1, part 5 of their open problems. Looking across all ten of their tables, a pattern emerges: once $k$ is large enough, $S_m(k,\ell)$ depends only on $\gcd(m,\ell-1)$, not on the full details of $m$ and $\ell$ separately. That pattern was not written down as a single unified statement.

Writing $d := \gcd(m, \ell-1)$ (the greatest common divisor of $m$ and $\ell-1$) and $n := m/d$, the following theorem makes that pattern explicit, with no hypothesis on $m$ and no case split on $\ell \bmod m$.

\begin{theorem}\label{thm:main}
For every $m \geq 2$, $\ell \geq 2$, and $k \geq n - 1$,
$$S_m(k, \ell) = n - 1 = \frac{m}{\gcd(m, \ell - 1)} - 1.$$
\end{theorem}

\begin{center}
\vspace{-9pt}
\begin{tikzpicture}
\node[callout, text width=0.9\linewidth, align=justify] {\textbf{What does `closed form' mean?}\\[5pt] Here, \emph{closed form} means exactly: a single explicit expression that produces $S_m(k,\ell)$ directly from $m$ and $\ell$ in a fixed number of elementary steps (one gcd, a division, a subtraction), with no search over colorings, no recursion, and no case split on $\ell \bmod m$. This is what replaces the modulus-by-modulus tables of \cite{DSWH2025} with a single rule.};
\end{tikzpicture}
\vspace{-9pt}
\end{center}

In other words: when you have enough color classes (at least $n - 1$ of them), the longest colorable list has exactly $n - 1$ entries, where $n$ is $m$ divided by $\gcd(m, \ell - 1)$ (Figure \ref{fig:closed-form}).

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, x=1cm, y=1cm,
   lt/.style={rounded corners=2pt, draw=mut, fill=lin2!25, minimum width=10mm, minimum height=6.5mm, inner sep=1pt, font=\small},
   dt/.style={rounded corners=2pt, draw=accY, fill=accF, minimum width=9mm, minimum height=6.5mm, inner sep=1pt, font=\small},
   st/.style={rounded corners=2pt, draw=addX, fill=addF, minimum width=8mm, minimum height=6.5mm, inner sep=1pt, font=\small},
   to/.style={-{Stealth[length=2mm]}, mut},
   hd/.style={rounded corners=3pt, text=white, font=\scriptsize\bfseries, align=center, minimum height=6mm, inner xsep=5pt},
   hdL/.style={hd, fill=ink},
   hdD/.style={hd, fill=accD},
   hdS/.style={hd, fill=addX}
]
  % column headers (color-coded to each column)
  \node[hdL] at (0,4.0)   {$\ell$};
  \node[hdD] at (3,4.0)   {$d=\gcd(12,\,\ell-1)$};
  \node[hdS] at (6.7,4.0) {$S_{12}(k,\ell)=\tfrac{12}{d}-1$};
  % ell tiles
  \node[lt] (l2) at (0,3) {$\ell=2$};
  \node[lt] (l8) at (0,2) {$\ell=8$};
  \node[lt] (l4) at (0,1) {$\ell=4$};
  \node[lt] (l5) at (0,0) {$\ell=5$};
  % d tiles
  \node[dt] (d1) at (3,2.5) {$d=1$};
  \node[dt] (d3) at (3,1)   {$d=3$};
  \node[dt] (d4) at (3,0)   {$d=4$};
  % S tiles
  \node[st] (s11) at (6.7,2.5) {$11$};
  \node[st] (s3)  at (6.7,1)   {$3$};
  \node[st] (s2)  at (6.7,0)   {$2$};
  % arrows ell -> d (2 and 8 collapse onto d=1)
  \draw[to] (l2) -- (d1);
  \draw[to] (l8) -- (d1);
  \draw[to] (l4) -- (d3);
  \draw[to] (l5) -- (d4);
  % arrows d -> S
  \draw[to] (d1) -- (s11);
  \draw[to] (d3) -- (s3);
  \draw[to] (d4) -- (s2);
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{What the closed form says (Theorem \ref{thm:main}, in the regime $k \ge n-1$). The value $S_m(k,\ell)=m/\gcd(m,\ell-1)-1$ depends on $\ell$ only through $d=\gcd(m,\ell-1)$: the pair $(m,\ell)$ collapses to the single quantity $n=m/d$, and the longest colorable list is $n-1$, one short of the self-defeating value $n$. With $m=12$ fixed, $\ell=2$ and $\ell=8$ share $d=1$ (both $\ell-1$ coprime to $12$), so both give $S_{12}=11$; $\ell=4,5$ give $3,2$.}
\label{fig:closed-form}
\end{minipage}
\end{figure}

The proof is elementary: both bounds reduce to the observation that $n$ itself is a singleton that fails $\ell$-sum-freeness. We give it in the next two sections. Theorem \ref{thm:main} settles the stable-$k$ regime ($k \geq n-1$) of \cite[Problem 1, part 5]{DSWH2025} for all $m \geq 2$.

The formula follows from \cite[Theorem 4 + Corollary 3]{DSWH2025} by choosing the optimal singleton: the smallest $a \in [1, m-1]$ for which Corollary 3's hypothesis $\ell \equiv 1 \pmod{m/\gcd(a,m)}$ holds is $a = n$, giving the upper bound $S_m(k,\ell) < n$. \cite{DSWH2025} used Corollary 3 only through Corollary 5 (the coprime case $\gcd(m,\ell-1)=1$, where the hypothesis holds for no $a \leq m-1$); they did not record the optimization for general $\gcd$. The principal new content of the present note is the threshold $k_0$ analysis in Section \ref{sec:threshold}: a cyclic-group iterated-sumset saturation lemma (Theorem \ref{thm:coset}), a sharp $k_0$ for prime moduli, and the explicit witness $\{1,5\} \subseteq \mathbb{Z}/12$ showing the prime case does not generalize naively. The note also resolves their Problem 1, part 3 in closed form (the single-class case, Section \ref{sec:k1}) and develops structural machinery toward the composite-modulus threshold (Section \ref{sec:structural}).

Theorem \ref{thm:main} and the $k = 1$ case (Theorem \ref{thm:k1}) are formalized in Lean 4 and checked through a comparator gate in the public repository at <https://github.com/mysticflounder/modular-schur>, which carries exactly the ten modules in the import cone of those statements; the core closed-form proof was produced with the Aristotle automated theorem prover \cite{aristotle}. The Lean modules named in Section \ref{sec:structural} for the structural reductions live in the author's private working tree: they are not distributed with the public repository and are not part of its gated verification claim.

## Organization

The paper is organized as follows. Section \ref{sec:prelim} collects four short lemmas that the proofs of the main theorem will use. Section \ref{sec:upper} proves the upper bound $S_m(k,\ell) \leq n - 1$, the heart of the argument. Section \ref{sec:lower} proves the matching lower bound, showing the upper bound is always achieved. Section \ref{sec:threshold} asks a finer question: how large must $k$ be before the formula kicks in? It records a tight answer for prime moduli and a counterexample showing composite moduli behave differently. Section \ref{sec:k1} handles the single-class case $k = 1$ in a separate closed form. Section \ref{sec:corollaries} spells out the formula for several specific moduli. Section \ref{sec:structural} records the structural machinery developed toward the composite-modulus threshold: the $K+\tau$ schema, the Coordinate-Union Edge Rule, and the separated-fiber and anchored exact transversal (AET) criteria, together with the computational frontier. Section \ref{sec:open} states what remains open.

# Preliminaries {#sec:prelim}

Throughout, $m \geq 2$ and $\ell \geq 2$ are fixed integers. Set
$$d := \gcd(m, \ell-1), \qquad n := m/d.$$
Then $dn = m$ exactly, and $d \mid (\ell - 1)$ by definition. The number $n$ is the key quantity: the main theorem says the answer is $n - 1$.

This section records four lemmas that the proofs in later sections will call on. Three of them are quick sanity checks (working modulo $m$ is harmless; the list can never exceed $m - 1$; adding empty classes is free). The fourth, the singleton safety criterion, is the engine of the whole paper.

\begin{lemma}[Residue reduction]\label{lem:residues}
Let $N \leq m - 1$. Then the integers $1, 2, \ldots, N$ have pairwise distinct nonzero residues modulo $m$. Moreover, a $k$-partition
$$[1,N] = C_1 \sqcup \cdots \sqcup C_k \subseteq \mathbb{Z}$$
is valid, meaning each $C_i$ is $\ell$-sum-free modulo $m$ in the sense of Definition \ref{def:schur}, if and only if the corresponding partition of the residues,
$$\{1, \ldots, N\} = \bar C_1 \sqcup \cdots \sqcup \bar C_k \subseteq \mathbb{Z}/m,$$
has each $\bar C_i$ $\ell$-sum-free. Consequently $S_m(k,\ell)$, defined on the integers in Definition \ref{def:schur}, equals its residue-level counterpart.
\end{lemma}

In other words: when $N < m$, the integers $1, \ldots, N$ are all distinct modulo $m$, so thinking of them as residues loses no information. A coloring is valid on the integers exactly when it is valid on the residues.

\begin{proof}
All elements of $[1,N]$ lie in $[1, m-1]$, and the reduction $[1, m-1] \hookrightarrow \mathbb{Z}/m$ is injective: if $a \equiv b \pmod m$ with $1 \leq a, b \leq m-1$, then $|a-b| < m$ forces $a = b$. Under this injection each class $C_i$ corresponds bijectively to a subset $\bar C_i \subseteq \{1, \ldots, m-1\}$ of $\mathbb{Z}/m$. For any tuple $(x_1, \ldots, x_\ell; y) \in C_i^\ell \times C_i$, the integer congruence
$$x_1 + \cdots + x_\ell \equiv y \pmod m$$
holds if and only if $\bar x_1 + \cdots + \bar x_\ell = \bar y$ in $\mathbb{Z}/m$, and every $\ell$-tuple in $\bar C_i$ lifts uniquely to $C_i$. So $\ell$-sum-freeness transfers in both directions, and the two definitions of $S_m(k,\ell)$ agree. (This equivalence is formalized as \texttt{schurMod\_eq\_schurModResidue}.)
\end{proof}

\begin{lemma}[Universal upper bound, \cite{CMD2013}]\label{lem:univ-upper}
For every $\ell \geq 1$ and every $k \geq 1$, $S_m(k,\ell) \leq m - 1$.
\end{lemma}

In other words: the element $m$ is always self-defeating, so no valid coloring can include it. The list can never reach length $m$.

\begin{proof}
If $N \geq m$, then $m \in [1,N]$ lies in some class $C$. The tuple $(m, \ldots, m; m) \in C^{\ell+1}$ satisfies
$$\ell m \equiv 0 \equiv m \pmod m,$$
violating $\ell$-sum-freeness. (This is \cite[Eq. (2)]{CMD2013}; formalized as \texttt{no\_valid\_partition\_of\_ge\_m}, and together with Lemma \ref{lem:residues} justifies the $N \leq m-1$ search cap used in the Lean definition via \texttt{schurMod\_is\_greatest}.)
\end{proof}

\begin{lemma}[Singleton safety]\label{lem:singleton}
For $r \in \{1, \ldots, m-1\}$, the singleton $\{r\} \subseteq \mathbb{Z}/m$ is $\ell$-sum-free modulo $m$ if and only if $(\ell - 1)r \not\equiv 0 \pmod m$; equivalently, if and only if $n \nmid r$.
\end{lemma}

In other words: a single element $r$ placed alone in a class is safe precisely when adding $r$ to itself $\ell$ times does not wrap around to $r$ modulo $m$. The smallest unsafe singleton turns out to be exactly $r = n$.

This is \cite[Theorem 4]{DSWH2025} rewritten in the variables natural for our application; we include the derivation for self-containment.

\begin{proof}
The singleton $\{r\}$ fails to be $\ell$-sum-free exactly when $\ell\{r\} \cap \{r\} \neq \emptyset$, that is, when $\ell r \equiv r \pmod m$, equivalently $(\ell-1)r \equiv 0 \pmod m$. Write $\ell - 1 = du$, so that $\gcd(u, n) = 1$. Since $m = dn$,
$$(\ell-1)r \equiv 0 \pmod{m} \;\iff\; ur \equiv 0 \pmod n \;\iff\; n \mid r.$$
So $\{r\}$ is $\ell$-sum-free if and only if $(\ell-1)r \not\equiv 0 \pmod m$, if and only if $n \nmid r$.
\end{proof}

\begin{lemma}[Monotonicity in $k$]\label{lem:monotone}
If $[1,N]$ admits a valid $k_0$-partition, then for every $k \geq k_0$ it admits a valid $k$-partition.
\end{lemma}

In other words: more color classes can never hurt. If $k_0$ colors work, any larger number of colors works too.

\begin{proof}
Pad with $k - k_0$ empty classes; the empty set is vacuously $\ell$-sum-free.
\end{proof}

# Upper bound {#sec:upper}

The entire upper bound rests on a single self-defeating number. Recall $d = \gcd(m, \ell-1)$ and $n = m/d$, so $dn = m$. The value $n$ is exactly the smallest positive integer $r$ for which $(\ell-1)\,r$ is a multiple of $m$, since $m \mid (\ell-1)r$ if and only if $n \mid r$ (Lemma \ref{lem:singleton}). Saying "$(\ell-1)\,n$ is a multiple of $m$" is the same as
$$\ell\,n \equiv n \pmod{m},$$
that is, adding $n$ to itself $\ell$ times returns to $n$ modulo $m$ (Figure \ref{fig:self-defeating}). So $n$ is unsafe even as a singleton, and no $\ell$-sum-free class can contain it.

\begin{theorem}\label{thm:unified-upper}
For all $m \geq 2$, $\ell \geq 2$, and $k \geq 1$,
$$S_m(k,\ell) \leq n - 1.$$
\end{theorem}

In other words: once the list grows to include $n$, it can no longer be partitioned into $\ell$-sum-free classes, no matter how many classes are allowed.

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, scale=1]
  % header
  \node[fighd] at (0,3.5) {The self-defeating value $n$};
  % the 12 residues on a clock, 0 at top, going clockwise
  \foreach \i in {0,...,11} {
    \node[circle, draw=mut, minimum size=6.5mm, inner sep=0pt]
      (c\i) at ({90-\i*30}:2.6) {\small \i};
  }
  % highlight the multiples of n=4 (the cyclic subgroup they generate)
  \foreach \i in {0,4,8} {
    \node[circle, draw=sumX, fill=sumF, minimum size=6.5mm, inner sep=0pt]
      at ({90-\i*30}:2.6) {\small \i};
  }
  % three +4 steps close one full lap: 0 -> 4 -> 8 -> 0
  \draw[-{Stealth[length=2.6mm]}, thick, sumX] (c0) to[bend left=10] (c4);
  \draw[-{Stealth[length=2.6mm]}, thick, sumX] (c4) to[bend left=10] (c8);
  \draw[-{Stealth[length=2.6mm]}, thick, sumX] (c8) to[bend left=10] (c0);
  \node[sumX] at (0,0) {\small $+4$ steps};
  \node[sumX] at (0,-0.5) {\scriptsize (size $n$)};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{On the clock $\mathbb{Z}/12$, three steps of size $n=4$ (here $\ell-1=3$)
close exactly one full lap back to $0$, because $(\ell-1)\,n = 3\cdot 4 = 12 \equiv 0$.
Equivalently $\ell n = 4\cdot 4 = 16 \equiv 4 = n$: adding $n$ to itself $\ell$ times
returns to $n$. So the single number $n$ already solves the forbidden equation
$x_1+\cdots+x_\ell \equiv y$ with every entry equal to $n$, so no class can contain it.}
\label{fig:self-defeating}
\end{minipage}
\end{figure}

\begin{proof}
Suppose $N \geq n$. Since $1 \leq n \leq m$, we have $n \in [1, N]$; let $C$ be the class of a valid $k$-partition containing $n$. Write $\ell - 1 = du$ with $u \in \mathbb{Z}$, so
$$(\ell - 1) \cdot n = du \cdot n = u \cdot (dn) = u \cdot m \equiv 0 \pmod m.$$
Hence $\ell n \equiv n \pmod m$. The tuple $(n, \ldots, n; n) \in C^{\ell+1}$ thus witnesses $\ell$-sum-freeness failure in $C$, a contradiction.
\end{proof}

\begin{figure}[t]
\centering
\begin{minipage}[t]{0.47\textwidth}
\vspace{0pt}
\centering
\resizebox{\linewidth}{!}{%
\begin{tikzpicture}[figcard, x=1cm, y=1cm,
   safe/.style={rounded corners, draw=addX, fill=addF,
                minimum height=8.5mm, minimum width=11mm, inner xsep=2pt},
   bad/.style={rounded corners, draw=sumX, fill=sumF,
                minimum height=8.5mm, minimum width=11mm, inner xsep=2pt},
   ll/.style={font=\scriptsize, anchor=east, text=ink}
]
  \node[fighd] at (2.0,1.9) {Why the list caps at $n-1$};
  % top row: reaching N = n-1 = 3 with singletons
  \node[ll] at (-0.1,0.85) {reach $n{-}1{=}3$:};
  \node[safe] (a) at (0.5,0.85)  {$\{1\}$};
  \node[safe] (b) at (1.8,0.85)  {$\{2\}$};
  \node[safe] (c) at (3.1,0.85)  {$\{3\}$};
  \node[font=\scriptsize, anchor=west, addX] at (3.9,0.85) {each is $\ell$-sum-free};
  % bottom row: adding n=4 forces some class to fail
  \node[ll] at (-0.1,-0.85) {add $n{=}4$:};
  \node[bad]  (d) at (0.5,-0.85)  {$\{1,4\}$};
  \node[safe] (e) at (1.8,-0.85)  {$\{2\}$};
  \node[safe] (f) at (3.1,-0.85)  {$\{3\}$};
  \node[font=\scriptsize, anchor=west, sumD] at (3.9,-0.85) {$4{+}4{+}4{+}4\equiv 4$};
  \draw[-{Stealth[length=2.2mm]}, thick, ink] (a.south) -- (d.north);
\end{tikzpicture}}
\par\smallskip
\caption{For $m=12,\ \ell=4$ we have $n=4$, so $S_{12}(k,4)\le 3$.
The list $1,2,3$ splits into $\ell$-sum-free singletons, reaching $N=n-1=3$
(attained once $k\ge n-1$). But the moment $n=4$ joins the list it must land in
\emph{some} class, and that class then contains the forbidden $\ell$-sum
$4+4+4+4\equiv 4$. Hence the list cannot grow past $n-1$.}
\label{fig:cap}
\end{minipage}\hfill
\begin{minipage}[t]{0.50\textwidth}
\vspace{0pt}
\centering
\resizebox{\linewidth}{!}{%
\begin{tikzpicture}[figcard, x=1.0cm, y=0.4cm]
  % header
  \node[fighd] at (3.4,14.8) {Two ceilings on $S_m(k,\ell)$};
  % axes
  \draw[-{Stealth[length=2mm]}, mut] (0,0) -- (7.1,0) node[right, font=\scriptsize, ink] {$k$};
  \draw[-{Stealth[length=2mm]}, mut] (0,0) -- (0,13.2) node[above, font=\scriptsize, ink] {$N$};
  % guaranteed-exact column k >= n-1 = 5, up to the new ceiling
  \fill[addF] (5,0) rectangle (6.8,5);
  % sharpened-away band between new ceiling n-1=5 and old ceiling m-1=11
  \fill[accF] (0,5) rectangle (6.8,11);
  % old ceiling m-1 = 11
  \draw[dashed, sumX] (0,11) -- (6.8,11);
  \node[font=\scriptsize, sumD, anchor=east] at (6.8,12.1) {old ceiling $m-1=11$};
  % new ceiling n-1 = 5
  \draw[dashed, thick, addX] (0,5) -- (6.8,5);
  \node[font=\scriptsize, addX, anchor=west] at (0.1,5.9) {new ceiling $n-1=5$ \;(Thm \ref{thm:unified-upper})};
  % sharpening label
  \node[font=\scriptsize, accD, align=center] at (2.5,8.4) {sharpened away\\[-1pt] {\scriptsize old bound allowed, $n{-}1$ forbids}};
  % exact-region label
  \node[font=\scriptsize, addX, align=center] at (5.9,2.5) {exact\\[-1pt] $S=n{-}1$\\[-1pt] {\scriptsize (Thm \ref{thm:main})}};
  % loose-region label
  \node[font=\scriptsize, mut, align=center] at (2.4,2.5) {ceiling may be loose\\[-1pt] {\scriptsize exact $k_0$ in \S\ref{sec:threshold}}};
  % known anchor S_12(1,11)=1
  \fill[ink] (1,1) circle (1.6pt);
  \node[font=\scriptsize, anchor=west, ink] at (1.2,1) {$S_{12}(1,11)=1$};
  % plateau dots at k=5,6
  \fill[addX] (5,5) circle (1.8pt);
  \fill[addX] (6,5) circle (1.8pt);
  % x ticks
  \foreach \k in {1,2,3,4,5,6} \draw[lin] (\k,0) -- (\k,-0.4);
  \foreach \k in {1,2,3,4,5,6} \node[font=\scriptsize, mut] at (\k,-1.1) {\k};
\end{tikzpicture}}
\par\smallskip
\caption{The two ceilings for $m=12$, $\ell=11$ (so $d=2$, $n=6$). The old universal
bound $S_m(k,\ell)\le m-1=11$ (Lemma \ref{lem:univ-upper}) is sharpened to
$S_m(k,\ell)\le n-1=5$ (Theorem \ref{thm:unified-upper}); the mustard band between
the two dashed lines is forbidden by the new bound but was permitted by the old one.
The bound is attained with equality, $S=n-1$, once $k\ge n-1$ (teal column, Theorem
\ref{thm:main}); for fewer classes it can be strictly loose, e.g.\ $S_{12}(1,11)=1$,
and the exact threshold $k_0$ is the subject of \S\ref{sec:threshold}.}
\label{fig:two-ceilings}
\end{minipage}
\end{figure}

**How to read this bound: is it the exact answer?** Theorem \ref{thm:unified-upper} is a *ceiling*, and three points are worth separating.

- **It sharpens the older ceiling.** The previously known general bound was $S_m(k,\ell) \leq m-1$ (Lemma \ref{lem:univ-upper}). Since $n = m/d \leq m$, the new ceiling $n-1$ is never worse, and is strictly lower whenever $d = \gcd(m,\ell-1) > 1$.
- **The ceiling is hit exactly when there are enough classes.** If $k \geq n-1$, placing each of $1, 2, \ldots, n-1$ in its own one-element class makes every singleton $\{r\}$ with $r < n$ $\ell$-sum-free (the self-defeating identity needs the value $n$, and $r \neq n$). This reaches $N = n-1$, so the bound is met with equality: $S_m(k,\ell) = n-1$. This matching lower bound is Theorem \ref{thm:unified-lower}; together they give the main formula, Theorem \ref{thm:main}. Figure \ref{fig:cap} shows both halves for $m = 12$, $\ell = 4$.
- **With few classes it can be loose.** When $k < n-1$ there may be too few classes to reach $n-1$, and the true value can be smaller; then $n-1$ is only an over-estimate. For a single class, $S_m(1,\ell) = \min(\ell-1, \lfloor m/\ell \rfloor)$ (Theorem \ref{thm:k1}), usually well below $n-1$.

In short, Theorem \ref{thm:unified-upper} gives the *exact* value precisely in the "many classes" regime $k \geq n-1$, and an *improved-but-not-tight* ceiling below it. Figure \ref{fig:two-ceilings} plots both regimes.

\begin{remark}
Equivalently, this is \cite[Corollary 3]{DSWH2025} applied at $a = n$. That corollary states $S_m(k,\ell) < a$ whenever $\ell \equiv 1 \pmod{m/\gcd(a,m)}$, and the smallest $a \leq m-1$ satisfying the hypothesis is $a = n$: any smaller $a$ has $\gcd(a,m) < n$, so $m/\gcd(a,m) > \gcd(m,\ell-1)$, and the hypothesis $m/\gcd(a,m) \mid (\ell-1)$ would contradict $\gcd(m,\ell-1)$ being maximal.
\end{remark}

\begin{remark}
The two obstructions in prior arguments are the same: "$N \geq m$ is blocked by $m$" (Lemma \ref{lem:univ-upper}, the $d=1$ case $n = m$) and "$r = m/d$ is an unsafe singleton" (Lemma \ref{lem:singleton} at $r = n$). Both reduce to: the single element $n$ is unsafe as a singleton, so any class containing it is unsafe. Once $N \geq n$, some class contains $n$.
\end{remark}

# Lower bound {#sec:lower}

The upper bound in Section \ref{sec:upper} showed the list can never reach length $n$. Here we show it can always reach length $n - 1$: just put each of $1, 2, \ldots, n-1$ in its own singleton class. By the singleton safety criterion (Lemma \ref{lem:singleton}), every one of those singletons is safe, because none of them is a multiple of $n$. This matching lower bound, together with the upper bound, pins down the exact value. Figure \ref{fig:singleton-ladder} shows the construction for $m = 12$, $\ell = 4$.

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard,
   safe/.style={rounded corners, draw=addX, fill=addF,
                minimum size=9mm, inner sep=2pt, font=\small},
   wall/.style={rounded corners, draw=sumX, fill=sumF,
                minimum size=9mm, inner sep=2pt, font=\small},
   gone/.style={rounded corners, draw=lin, fill=lin2!20,
                minimum size=9mm, inner sep=2pt, font=\small, text=mut}]
  % header
  \node[fighd] at (3.2,2.15) {Reaching $n-1$ with singletons};
  % the n-1 singleton classes covering [1, n-1]
  \node[safe] (s1) at (0,0)   {$\{1\}$};
  \node[safe] (s2) at (1.5,0) {$\{2\}$};
  \node[safe] (s3) at (3.0,0) {$\{3\}$};
  \node[wall] (w)  at (4.5,0) {$4$};
  \node[gone] (g5) at (6.0,0) {$5$};
  \node[gone] (g6) at (7.1,0) {$\cdots$};
  % singleton-safety arithmetic: (l-1) r mod 12, with l-1 = 3
  \node[font=\scriptsize, addX] at (0,-0.95)   {$3{\cdot}1\equiv 3$};
  \node[font=\scriptsize, addX] at (1.5,-0.95) {$3{\cdot}2\equiv 6$};
  \node[font=\scriptsize, addX] at (3.0,-0.95) {$3{\cdot}3\equiv 9$};
  \node[font=\scriptsize, sumD]   at (4.5,-0.95) {$3{\cdot}4\equiv 0$};
  \node[font=\scriptsize, addX] at (1.5,-1.55) {$(\ell-1)r\not\equiv 0$: safe};
  \node[font=\scriptsize, sumD]   at (4.6,-1.55) {$\equiv 0$ at $r=n$};
  % reachable span and the wall
  \draw[{Stealth[length=2mm]}-{Stealth[length=2mm]}, mut] (-0.5,0.85) -- (3.5,0.85);
  \node[font=\scriptsize, ink] at (1.5,1.2) {reachable list $[1,n{-}1]$, length $N=3$};
  \node[font=\scriptsize, sumD] at (4.5,1.05) {$n=4$};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{The matching lower bound for $m=12$, $\ell=4$ (so $n=4$). Each of
$1,2,\dots,n-1$ goes in its own singleton class; by Lemma \ref{lem:singleton} the
class $\{r\}$ is $\ell$-sum-free exactly when $(\ell-1)r\not\equiv 0\pmod m$, that is
when $n\nmid r$, which holds for every $r<n$. The construction therefore colors all
of $[1,n-1]$ and reaches $N=n-1=3$. It stops there because the list must be an
initial segment $[1,N]$, and the next value $n=4$ is the self-defeating singleton
$(\ell-1)\,n\equiv 0$, which caps the list (compare Figure \ref{fig:cap}).}
\label{fig:singleton-ladder}
\end{minipage}
\end{figure}

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

Theorem \ref{thm:main} says that $S_m(k,\ell) = n - 1$ once $k$ is large enough. But exactly how large is "large enough"? Define $k_0(m, \ell)$ to be the least $k$ such that $S_m(k', \ell) = n - 1$ for every $k' \geq k$. This section pins down $k_0$ for prime moduli exactly and shows, via a counterexample, that composite moduli can require fewer classes than the prime case suggests.

\begin{theorem}\label{thm:k0-upper}
$k_0(m, \ell) \leq \max(1, n - 1)$.
\end{theorem}

In other words: for $n \geq 2$ you never need more than $n - 1$ classes before the formula $S_m(k,\ell) = n - 1$ kicks in; for $n = 1$ the threshold is $1$.

\begin{proof}
Theorem \ref{thm:unified-lower} exhibits a valid $(n-1)$-partition achieving $N = n - 1$ when $n \geq 2$. When $n = 1$ the value is zero, achieved trivially at $k = 1$.
\end{proof}

\begin{theorem}[Covering lower bound]\label{thm:k0-lower-cov}
Assume $n \geq 2$, that is, $\ell \not\equiv 1 \pmod m$. Let $\sigma(m, \ell) := \max\{|C| : C \subseteq \{1, \ldots, n-1\}, C \text{ is } \ell\text{-sum-free mod } m\}$. Then $k_0(m, \ell) \geq \lceil (n-1)/\sigma(m, \ell) \rceil$.
\end{theorem}

In other words: $\sigma(m, \ell)$ is the maximum number of elements that can share a single safe class. To cover all $n - 1$ elements, you need at least $\lceil (n-1)/\sigma \rceil$ classes.

\begin{proof}
If $[1, n-1]$ admits a valid $k$-partition, summing class sizes gives $n - 1 \leq k \cdot \sigma(m, \ell)$.
\end{proof}

## Tight threshold for prime modulus

For prime moduli, every non-singleton class eventually becomes unsafe once $\ell$ is large, which forces every class to be a singleton and, for $\ell \not\equiv 1 \pmod p$ (so that $n = p$), pins $k_0$ exactly at $n - 1 = p - 1$. The following lemma is the key tool: it describes what the set of all $\ell$-fold sums from a multi-element class looks like, once $\ell$ is large relative to the size of the subgroup that class generates.

\begin{theorem}[Large-$\ell$ coset criterion]\label{thm:coset}
Let $C \subseteq \mathbb{Z}/m$ with $|C| \geq 2$, pick $a_0 \in C$, and let $H := \langle C - C \rangle = g\mathbb{Z}/m$ with $g := m/|H|$. For every $\ell \geq |H| - 1$,
$$\ell C = \ell a_0 + H,$$
and consequently $C$ is $\ell$-sum-free modulo $m$ if and only if $g \nmid (\ell - 1) a_0$.
\end{theorem}

In other words: once $\ell$ is large enough (at least $|H| - 1$), the collection of all $\ell$-fold sums from $C$ fills out the entire coset $\ell a_0 + H$. The class $C$ is safe precisely when that filled coset does not overlap with $C$ itself. Figure \ref{fig:coset-fill} traces the saturation for a prime modulus.

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard,
   res/.style={circle, draw=mut, minimum size=5.5mm, inner sep=0pt, font=\scriptsize},
   inS/.style={circle, draw=addX, fill=addF, minimum size=5.5mm, inner sep=0pt, font=\scriptsize},
   cmem/.style={circle, draw=accY, line width=1pt, fill=addF, minimum size=5.5mm, inner sep=0pt, font=\scriptsize}]
  % header
  \node[fighd] at (3.9,1.95) {Sumset saturation over a prime};
  % Panel 1: 1C = C = {1,3}
  \begin{scope}[shift={(0,0)}]
    \foreach \i in {0,...,4} \node[res] at ({90-\i*72}:0.9) {\i};
    \foreach \i in {1,3} \node[cmem] at ({90-\i*72}:0.9) {\i};
    \node[font=\scriptsize] at (0,-1.5) {$1C=C=\{1,3\}$};
  \end{scope}
  \node at (1.95,0) {$\xrightarrow{\,+C\,}$};
  % Panel 2: 2C = {1,2,4}
  \begin{scope}[shift={(3.9,0)}]
    \foreach \i in {0,...,4} \node[res] at ({90-\i*72}:0.9) {\i};
    \foreach \i in {1,2,4} \node[inS] at ({90-\i*72}:0.9) {\i};
    \node[font=\scriptsize] at (0,-1.5) {$2C=\{1,2,4\}$};
  \end{scope}
  \node at (5.85,0) {$\xrightarrow{\ \cdots\ }$};
  % Panel 3: ell C = Z/5, contains C
  \begin{scope}[shift={(7.8,0)}]
    \foreach \i in {0,...,4} \node[inS] at ({90-\i*72}:0.9) {\i};
    \foreach \i in {1,3} \node[cmem] at ({90-\i*72}:0.9) {\i};
    \node[font=\scriptsize] at (0,-1.5) {$\ell C=\mathbb{Z}/5\supseteq C$};
  \end{scope}
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{Saturation over a prime modulus (Theorem \ref{thm:coset}), for
$C=\{1,3\}\subseteq\mathbb{Z}/5$. Since $\langle C-C\rangle=\mathbb{Z}/5$ (a prime has
no proper nontrivial subgroup), the $\ell$-fold sumsets grow in size,
$|1C|<|2C|<\cdots$ (Cauchy--Davenport; the sets themselves are nested only
after the shift $D=C-a_0$ used in the proof), and fill the whole group after
at most $|H|-1=4$ steps.
The filled set $\ell C=\mathbb{Z}/5$ then contains $C$ itself (mustard ring), so some
$\ell$-sum of elements of $C$ equals an element of $C$, and the class is not
$\ell$-sum-free. The same collapse hits every class of size $\ge 2$ over a prime, so
only singletons survive and, for $\ell\ge p-1$ with $\ell\not\equiv 1\pmod p$,
$k_0(p,\ell)=p-1$ (Corollary \ref{cor:prime-sharp}).}
\label{fig:coset-fill}
\end{minipage}
\end{figure}

\begin{proof}[Proof sketch]
\emph{The inclusion $\ell C \subseteq \ell a_0 + H$.} Write any $\ell$-fold sum as
$$c_1 + \cdots + c_\ell = \ell a_0 + \sum_{i=1}^{\ell} (c_i - a_0).$$
Each difference $c_i - a_0$ lies in $H = \langle C - C \rangle$, so the whole sum lies in the coset $\ell a_0 + H$.

\emph{The reverse inclusion $\ell a_0 + H \subseteq \ell C$.} Shift $C$ to the origin by setting $D := C - a_0$. Then $0 \in D \subseteq H$, and $D$ generates $H$, since $\langle D \rangle = \langle D - D \rangle = \langle C - C \rangle = H$ (the first equality uses $0 \in D$). Because $0 \in D$, adjoining another copy of $D$ can only enlarge a sumset, so the iterated sumsets form a non-decreasing chain inside $H$,
$$D \subseteq 2D \subseteq 3D \subseteq \cdots \subseteq H.$$
This chain starts at $|D| = |C| \geq 2$ elements and is capped by $|H|$, so it can strictly grow at most $|H| - 2$ times; hence it stabilizes, $tD = (t+1)D$, at some step $t \leq |H| - 1$. A stabilized sumset satisfies $tD + D = tD$, so $tD$ is closed under adding any element of $D$, and therefore under adding any element of the subgroup $\langle D \rangle = H$ that $D$ generates. Thus $tD$ is a union of cosets of $H$, and since it contains $0$ it must be all of $H$. So $\ell D = H$ for every $\ell \geq t$, in particular for every $\ell \geq |H| - 1$, and undoing the shift gives $\ell C = \ell a_0 + \ell D = \ell a_0 + H$.

\emph{The safety criterion.} Fix $\ell \geq |H| - 1$, so that $\ell C = \ell a_0 + H$ by the two inclusions above. Since $C \subseteq a_0 + H$, the sumset $\ell C$ meets $C$ exactly when the cosets $\ell a_0 + H$ and $a_0 + H$ coincide, that is when $(\ell - 1) a_0 \in H$, equivalently $g \mid (\ell - 1) a_0$ (recall $H = g\,\mathbb{Z}/m$). Hence $C$ is $\ell$-sum-free if and only if $g \nmid (\ell - 1) a_0$.
\end{proof}

\begin{remark}
The $(\supseteq)$ direction is a cyclic-group version of the Cauchy--Davenport theorem \cite{Cauchy1813,Davenport1935}: over $\mathbb{Z}/p$ prime, iterating $|A+B| \geq \min(p, |A| + |B| - 1)$ yields $|\ell C| \geq \min(p, \ell(|C|-1) + 1)$, so any non-degenerate $C$ ($|C| \geq 2$) has $\ell C = \mathbb{Z}/p$ once $\ell \geq p - 1$. Theorem \ref{thm:coset} is the saturation statement inside an arbitrary cyclic subgroup $H \leq \mathbb{Z}/m$, with the explicit $\ell \geq |H| - 1$ threshold.
\end{remark}

\begin{corollary}[Sharp $k_0$ for prime moduli]\label{cor:prime-sharp}
Let $p$ be prime. For every $\ell \geq p - 1$ with $\ell \not\equiv 1 \pmod p$,
$$k_0(p, \ell) = p - 1.$$
\end{corollary}

In other words: for a prime modulus, you need exactly $p - 1$ classes before the formula stabilizes, and no fewer will do. The reason is that any class with two or more elements eventually becomes unsafe (its $\ell$-fold sums fill all of $\mathbb{Z}/p$), so every safe partition must consist entirely of singletons.

\begin{proof}
For any $|C| \geq 2$ in $\mathbb{Z}/p$, the subgroup $\langle C - C \rangle$ is either $0$ (ruled out) or $\mathbb{Z}/p$ (since $\mathbb{Z}/p$ has no nontrivial subgroups). By Theorem \ref{thm:coset} with $g = 1$, $\ell C = \mathbb{Z}/p$, so $C$ is not $\ell$-sum-free. Hence $\sigma(p, \ell) = 1$, and Theorem \ref{thm:k0-lower-cov} gives $k_0 \geq n - 1 = p - 1$; Theorem \ref{thm:k0-upper} supplies the match.
\end{proof}

## Composite moduli: a counterexample to the natural conjecture

Corollary \ref{cor:prime-sharp} might suggest a general rule: for every $m$ and every large $\ell$ with $\gcd(m, \ell - 1) < m$, only singletons are $\ell$-sum-free, so $k_0(m, \ell) = n - 1$. This is false once $m$ is composite. The composite case has more subgroup structure, and a two-element class can hide inside a proper subgroup and remain safe. The proposition below gives a concrete instance.

\begin{proposition}\label{prop:refute-A}
For $m = 12$ and every $\ell \equiv 11 \pmod{12}$ (so $d = 2$, $n = 6$), the set $C = \{1, 5\} \subseteq \{1, \ldots, 5\}$ is $\ell$-sum-free modulo $12$. Consequently $\sigma(12, \ell) \geq 2$ and $k_0(12, \ell) \leq 3 < n - 1$.
\end{proposition}

In other words: the pair $\{1, 5\}$ generates differences $\{0, \pm 4\}$, so its differences lie in the subgroup $\{0, 4, 8\} \subset \mathbb{Z}/12$ (Figure \ref{fig:subgroup-hide}). That subgroup is small enough that $\{1, 5\}$ stays safe. This lets us cover $[1, 5]$ with only three classes rather than five, showing $k_0 < n - 1$ here.

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, scale=1]
  % header
  \node[fighd] at (0,3.5) {A subgroup hides a safe pair};
  \foreach \i in {0,...,11} {
    \node[circle, draw=mut, minimum size=6.5mm, inner sep=0pt]
      (c\i) at ({90-\i*30}:2.6) {\small \i};
  }
  % the proper subgroup H = {0,4,8} = 4Z/12 (the "trap")
  \foreach \i in {0,4,8} {
    \node[circle, draw=accY, fill=accF, minimum size=6.5mm, inner sep=0pt]
      at ({90-\i*30}:2.6) {\small \i};
  }
  % the pair C = {1,5}
  \foreach \i in {1,5} {
    \node[circle, draw=addX, fill=addF, minimum size=6.5mm, inner sep=0pt]
      at ({90-\i*30}:2.6) {\small \i};
  }
  % the difference 5-1 = 4 lands in H
  \draw[-{Stealth[length=2.6mm]}, thick, addX] (c1) to[bend right=14] (c5);
  \node[addX] at (0,0.25) {\small $5-1=4$};
  \node[accD] at (0,-0.35) {\scriptsize $\in\{0,4,8\}$};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{Why composite moduli differ from primes. The pair $C=\{1,5\}$ (teal)
has difference $5-1=4$, which lands inside the proper subgroup
$H=\{0,4,8\}=4\mathbb{Z}/12$ (mustard). All differences of $C$ stay trapped in this
size-$3$ subgroup, so $C$ can remain $\ell$-sum-free even with two elements. Over
a prime modulus no such trap exists: any two distinct residues have a difference
that generates the whole group, forcing every safe class to be a singleton
(Corollary \ref{cor:prime-sharp}).}
\label{fig:subgroup-hide}
\end{minipage}
\end{figure}

\begin{proof}
$C - C = \{0, \pm 4\}$, so $\langle C - C \rangle = 4\mathbb{Z}/12 = \{0, 4, 8\}$, $|H| = 3$, $g = 4$. Theorem \ref{thm:coset} applies once $\ell \geq 2$. With $a_0 = 1$, the criterion $4 \nmid (\ell - 1) \cdot 1$ reads $4 \nmid \ell - 1$, i.e. $\ell \not\equiv 1 \pmod 4$. For $\ell \equiv 11 \pmod{12}$ we have $\ell \equiv 3 \pmod 4$, so $4 \nmid \ell - 1$, and $C$ is $\ell$-sum-free, giving $\sigma(12, \ell) \geq 2$.

For the $k_0$ bound, consider the $3$-partition $[1, 5] = \{1, 4\} \sqcup \{2, 5\} \sqcup \{3\}$. Each pair-class has $C - C = \{0, \pm 3\}$, hence $H = \langle 3 \rangle = \{0, 3, 6, 9\}$, $|H| = 4$, $g = 3$; Theorem \ref{thm:coset} applies for $\ell \geq 3$ with safety criterion $3 \nmid (\ell - 1) a_0$. For $\ell \equiv 11 \pmod{12}$ we have $\ell - 1 \equiv 10 \pmod{12}$, and $3 \nmid 10 \cdot 1$ as well as $3 \nmid 10 \cdot 2$, so both $\{1, 4\}$ (with $a_0 = 1$) and $\{2, 5\}$ (with $a_0 = 2$) are $\ell$-sum-free. The singleton $\{3\}$ is safe by Lemma \ref{lem:singleton}: $(\ell - 1) \cdot 3 \equiv 30 \equiv 6 \not\equiv 0 \pmod{12}$. Hence $k_0(12, \ell) \leq 3$.
\end{proof}

# The $k = 1$ case {#sec:k1}

When $k = 1$ there is only a single class, which must contain all of $[1,N]$. The whole list is one set, and it must itself be $\ell$-sum-free. So $S_m(1,\ell)$ is asking: how long can a list be if we are not allowed to split it at all? The answer turns out to be the minimum of two simple quantities, each capturing one way the list can become too long.

\begin{theorem}\label{thm:k1}
For every $m \geq 2$ and $2 \leq \ell \leq m$,
$$S_m(1, \ell) = \min\!\left(\ell - 1,\ \left\lfloor \frac{m}{\ell} \right\rfloor\right).$$
\end{theorem}

In other words: the single-class limit is whichever is smaller, either $\ell - 1$ (imposed by the element $1$ appearing $\ell$ times) or $\lfloor m/\ell \rfloor$ (imposed by the list growing long enough that some $\ell$-fold sum wraps around to $1$ modulo $m$).

This resolves \cite[Problem 1, part 3]{DSWH2025}.

\begin{proof}
Write $N^* := \min(\ell - 1, \lfloor m/\ell \rfloor)$.

\textbf{Upper bound $S_m(1,\ell) \leq \ell - 1$.} For $\ell = m$ this follows from Lemma \ref{lem:univ-upper}. For $\ell < m$: if $N \geq \ell$, then $1 \in [1,N]$ and the $\ell$-fold sum $\underbrace{1 + \cdots + 1}_{\ell} = \ell$ satisfies $\ell \in [1,N]$ (since $\ell < m$, so $\ell$ is a nonzero residue in $[1,m-1]$, and $\ell \leq N$). This gives a violation.

\textbf{Upper bound $S_m(1,\ell) \leq \lfloor m/\ell \rfloor$.} Suppose $N \geq \lfloor m/\ell \rfloor + 1$. Write $m + 1 = q\ell + r$ with $q = \lfloor(m+1)/\ell\rfloor$ and $r = (m+1) \bmod \ell$. Then $q \geq 1$ (since $m \geq \ell$) and $q \leq \lfloor m/\ell \rfloor + 1 \leq N$; also $q + 1 \leq \lfloor m/\ell \rfloor + 1 \leq N$ when $r > 0$. The $\ell$-tuple with $r$ entries equal to $q+1$ and $\ell - r$ entries equal to $q$ consists entirely of elements in $[1, N]$ and sums (as integers) to $q\ell + r = m + 1 \equiv 1 \pmod m$. Since $1 \in [1,N]$, this is a violation.

\textbf{Lower bound $S_m(1,\ell) \geq N^*$.} Every $\ell$-fold integer sum of elements from $[1, N^*]$ lies in $[\ell, \ell N^*]$. Since $N^* \leq \lfloor m/\ell \rfloor$, we have $\ell N^* \leq m$, so all such sums lie in $[\ell, m]$. Their residues modulo $m$ belong to $\{\ell, \ldots, m-1, 0\}$. But elements of $[1, N^*]$ have residues in $\{1, \ldots, N^*\} \subseteq \{1, \ldots, \ell - 1\}$, which is disjoint from $\{\ell, \ldots, m-1, 0\}$. No violation is possible.
\end{proof}

\begin{remark}
The formula $\min(\ell - 1, \lfloor m/\ell \rfloor)$ interpolates naturally between two regimes. In the \emph{no-wrap} regime $\ell(\ell-1) < m$, one has $\ell - 1 < m/\ell$, so the minimum equals $\ell - 1$: the list is bottlenecked by the element $1$ summing up to $\ell$, not by any wraparound (consistent with the observation in \cite{DSWH2025} for small $\ell$). In the \emph{wrap} regime $\ell(\ell-1) \geq m$ (D'orville's Problem 1, part 3), the minimum is $\lfloor m/\ell \rfloor$: the list is bottlenecked by $\ell$-fold sums wrapping around modulo $m$; Figure \ref{fig:k1-regimes} plots both bounds and their minimum for $m = 30$. The formula was empirically verified for $m \in [2,30]$, $\ell \in [2, m]$ (435 cases) before the proof was written.
\end{remark}

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, x=0.8cm, y=0.30cm, reg/.style={font=\scriptsize}]
  % header
  \node[fighd] at (5.2,18.0) {The two regimes of $S_m(1,\ell)$};
  \draw[-{Stealth[length=2mm]}, mut] (-0.3,0) -- (11,0) node[right,font=\scriptsize,text=ink] {$\ell$};
  \draw[-{Stealth[length=2mm]}, mut] (0,-0.3) -- (0,16.5) node[above,font=\scriptsize,text=ink] {value};
  \foreach \x/\lab in {0/2, 2/4, 4/6, 6/8, 8/10, 10/12} {
    \draw[lin] (\x,0) -- (\x,-0.4); \node[below,font=\scriptsize,text=mut] at (\x,-0.4) {$\lab$};
  }
  \foreach \y in {5,10,15} {
    \draw[lin] (0,\y) -- (-0.2,\y); \node[left,font=\scriptsize,text=mut] at (-0.2,\y) {$\y$};
  }
  % crossover marker (ell = 6, where ell(ell-1) = m = 30)
  \draw[lin2, dashed] (4,0) -- (4,11.5);
  % floor(m/ell), m=30
  \draw[sumX, thick]
    (0,15) -- (1,10) -- (2,7) -- (3,6) -- (4,5) -- (5,4) -- (6,3) -- (7,3) -- (8,3) -- (9,2) -- (10,2);
  \node[sumX, font=\scriptsize, anchor=west] at (10.1,2) {$\lfloor m/\ell\rfloor$};
  % ell-1 (rising line)
  \draw[addX, thick] (0,1) -- (10,11);
  \node[addX, font=\scriptsize, anchor=south west] at (10.1,11) {$\ell-1$};
  % S_m(1,ell) = min (lower envelope)
  \draw[accY, line width=1.3pt]
    (0,1) -- (1,2) -- (2,3) -- (3,4) -- (4,5) -- (5,4) -- (6,3) -- (7,3) -- (8,3) -- (9,2) -- (10,2);
  \fill[ink] (4,5) circle (2.2pt);
  \node[font=\scriptsize, anchor=south, accD] at (4,5.4) {$S_m(1,\ell)$};
  % regime labels
  \node[reg, addX, align=center] at (2.3,13.5) {no-wrap\\$\ell(\ell-1)<m$};
  \node[reg, sumX, align=center] at (7.7,13.5) {wrap\\$\ell(\ell-1)\ge m$};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{The single-class value $S_m(1,\ell)=\min(\ell-1,\lfloor m/\ell\rfloor)$
for $m=30$ (Theorem \ref{thm:k1}). The rising line $\ell-1$ (teal) governs the
\emph{no-wrap} regime; the falling curve $\lfloor m/\ell\rfloor$ (terracotta) governs the
\emph{wrap} regime. The value $S_m(1,\ell)$ (mustard) is the lower of the two: it
climbs along $\ell-1$, peaks where the curves cross, here at $\ell=6$, exactly
where $\ell(\ell-1)=m$ (dashed), then descends along $\lfloor m/\ell\rfloor$.}
\label{fig:k1-regimes}
\end{minipage}
\end{figure}

# Corollaries: recovered and extended formulas {#sec:corollaries}

The main formula $S_m(k,\ell) = m/\gcd(m,\ell-1) - 1$ (Theorem \ref{thm:main}) immediately yields explicit tables for any fixed modulus by plugging in the possible values of $\gcd(m, \ell-1)$. We list a few cases to show how the formula recovers and extends the prior literature, then state the prime-power family.

Specializing Theorem \ref{thm:main}:

- **$m = 8$:** for $k \geq 7$, $S_8(k, \ell)$ equals $0, 1, 3, 7$ according to $\gcd(8, \ell - 1) \in \{8, 4, 2, 1\}$ (residue pattern $\ell \bmod 8$).
- **$m = 9$:** for $k \geq 8$, $S_9(k, \ell)$ equals $0, 2, 8$ according to $\gcd(9, \ell - 1) \in \{9, 3, 1\}$.
- **$m = 11$:** for $k \geq 10$, $S_{11}(k, \ell) = 0$ if $\ell \equiv 1 \pmod{11}$, else $10$.
- **Prime-power $m = p^e$:** writing $v := \min(v_p(\ell - 1), e)$ where $v_p$ denotes the $p$-adic valuation, for $k \geq p^{e-v} - 1$,
  $$S_{p^e}(k, \ell) = p^{e-v} - 1.$$

All of these stabilized values are consistent with (and for $m = 4, 5, 6, 7$ recover) the tables of \cite[§2--3]{DSWH2025} and for $m = 1, 2, 3$ the theorems of \cite[§1--2]{CMD2013}.

# Structural reductions toward composite $k_0(m,\ell)$ {#sec:structural}

For composite $m$, the threshold $k_0(m,\ell)$ is not pinned by Theorem \ref{thm:k0-upper} alone: the covering bound (Theorem \ref{thm:k0-lower-cov}) matches $n - 1$ for primes but falls short in general. For $m = 8$ and $\ell$ even, $\sigma(8, \ell) = 4$ (the witness set $\{1, 3, 5, 7\}$ is $\ell$-sum-free), so the covering bound gives only $k_0 \geq 2$ while the true value is $k_0 = 3$. A closed form for $k_0(m,\ell)$ at composite $m$ remains open (Section \ref{sec:open}), but the reductions below reduce the problem to a single well-defined existence question on a finite and structurally organized collection of cells.

## The $K + \tau$ schema

Throughout this section the threshold is taken in the *stable regime* $\ell \geq m - 1$. There, by Theorem \ref{thm:coset} (every class $C$ with $|C| \geq 2$ has $|\langle C - C \rangle| \leq m$, so the theorem applies) together with the singleton criterion (Lemma \ref{lem:singleton}), whether a class is $\ell$-sum-free depends only on $c := \ell \bmod m$; hence $k_0(m,\ell)$ is a function of $(m, c)$ there, and we write $k_0^\infty(m, c)$ for this common value. The reduction below is a statement about $k_0^\infty$, not about the ordinary threshold at small $\ell$: the pairs $(m,\ell) = (5,2)$ and $(5,3)$ share $n = 5$ and the normalized cell $d_0 = 1$ defined next, yet $k_0(5,2) = 2$ (the partition $\{1,4\} \sqcup \{2,3\}$ is safe) while $k_0(5,3) = 4$.

The key insight is that all pairs $(m, \ell)$ in the stable regime sharing the same quotient $n = m/\gcd(m, \ell-1)$ produce the same covering problem, and that problem depends only on a *normalized cell* $d_0$ derived from $\gcd(m, \ell-1)$.

Fix a quotient $n \geq 2$, write $n = \prod_i p_i^{f_i}$, and set $\mathrm{cap}_i := \lfloor \log_{p_i}(n - 1) \rfloor$. For any $\ell$ with $m/\gcd(m, \ell-1) = n$, write $d := \gcd(m, \ell - 1)$ and define the *normalized cell*
$$d_0 := \prod_i p_i^{\min(v_{p_i}(d),\ \mathrm{cap}_i)}.$$
The maximal $\ell$-sum-free fragments on $\{1, \ldots, n-1\} \subseteq \mathbb{Z}/m$ depend only on $d_0$: prime factors of $d$ outside the support of $n$ are absorbed by $g \mapsto g/\gcd(g, d)$ in the singleton criterion (Lemma \ref{lem:singleton}), and exponents above $\mathrm{cap}_i$ produce divisors $> n - 1$. Splitting any optimal cover into *private* fragments (those containing a witness point in no other fragment) and the *residual* cover yields
$$k_0^\infty(m, c) = K(d_0) + \tau(d_0),$$
where $K(d_0)$ counts the private fragments and $\tau(d_0)$ is the minimum number of non-private fragments needed to cover the points left over once the private (forced) fragments are removed. Each fixed-quotient family thus reduces to a finite collection of $\prod_i (\mathrm{cap}_i + 1)$ normalized cells, and per-cell $\tau$ is an exact (NP-hard but tractable in practice) set-cover computation on the *atom graph* $G_{\mathrm{atom}}(d_0)$: its vertices are the *atoms* of the residual universe $R(d_0)$ (maximal sets of points lying in exactly the same maximal residual fragments), and two atoms are adjacent when some fragment contains both.

## The Coordinate-Union Edge Rule

The atom graph has hidden product structure that makes the set-cover problem more tractable. Each atom $A$ carries a set of *coordinates*, one per axis label $g$ in its support pattern (the labels are not necessarily primes; the axes in the examples below are prime powers such as $121$, $125$, and $256$), that record which residue class modulo $g$ the atom lies in. The edge rule says: two atoms are adjacent exactly when they share a coordinate.

Write the maximal residual fragments of a cell as $F_1, \ldots, F_s$ with *labels* $g_i \mid m$ and *anchors* $r_i$. For an atom $A$, its *support pattern* is $P(A) := \{g_i : A \subseteq F_i\} \setminus \{1\}$, and for $g \in P(A)$ its *coordinate* is $\rho_g(A) := r_i \bmod g$ for any $i$ with $g_i = g$ and $A \subseteq F_i$. The *same-support fiber* is $X_P := \{A : P(A) = P\}$.

\begin{theorem}[Coordinate-Union Edge Rule]\label{thm:edge-rule}
Let $P$ be a nonempty support pattern. Two distinct atoms $A, B \in X_P$ are adjacent in $G_{\mathrm{atom}}[X_P]$ if and only if $\rho_g(A) = \rho_g(B)$ for some $g \in P$. Equivalently, $G_{\mathrm{atom}}[X_P]$ is the union over $g \in P$ and $r \in \mathbb{Z}/g$ of the cliques $C_{g,r} := \{A \in X_P : \rho_g(A) = r\}$.
\end{theorem}

In other words: adjacency in the atom graph is determined by coordinate-matching. Atoms that share a residue coordinate along any axis are adjacent; atoms that differ in every coordinate are non-adjacent. This turns the atom graph into a union of coordinate-cliques, a structured form that the next two reductions exploit (Figure \ref{fig:edge-rule}).

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard,
   atom/.style={circle, draw=ink, fill=lin2!20, minimum size=7mm, inner sep=0pt, font=\small},
   coledge/.style={addX, thick},
   rowedge/.style={sumX, thick}
]
  % faint grid: columns rho_{g1} in {1,2,3}, rows rho_{g2} in {1,2}
  \foreach \c in {1,2,3} { \draw[lin2!55] (\c*2,0.9) -- (\c*2,3.7); }
  \foreach \r in {1,2}   { \draw[lin2!55] (1.4,\r*1.3+0.6) -- (6.6,\r*1.3+0.6); }
  % axis labels
  \node[font=\scriptsize, addX] at (4,0.45) {$\rho_{g_1}$ (columns)};
  \node[font=\scriptsize, sumX, rotate=90] at (0.75,2.55) {$\rho_{g_2}$ (rows)};
  \node[font=\scriptsize, text=mut] at (2,3.95) {$1$};
  \node[font=\scriptsize, text=mut] at (4,3.95) {$2$};
  \node[font=\scriptsize, text=mut] at (6,3.95) {$3$};
  \node[font=\scriptsize, text=mut] at (1.2,1.9) {$1$};
  \node[font=\scriptsize, text=mut] at (1.2,3.2) {$2$};
  % atoms at (col,row): A=(1,1) B=(1,2) C=(2,1) D=(3,2)
  \coordinate (A) at (2,1.9);
  \coordinate (B) at (2,3.2);
  \coordinate (C) at (4,1.9);
  \coordinate (D) at (6,3.2);
  % column clique (shared rho_{g1}=1): A-B
  \draw[coledge] (A) -- (B);
  % row cliques (shared rho_{g2}): A-C on row 1, B-D on row 2
  \draw[rowedge] (A) -- (C);
  \draw[rowedge] (B) -- (D);
  \node[atom] at (A) {$A$};
  \node[atom] at (B) {$B$};
  \node[atom] at (C) {$C$};
  \node[atom] at (D) {$D$};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{The Coordinate-Union Edge Rule (Theorem \ref{thm:edge-rule}) for a
two-axis fiber. Each atom is placed by its coordinates
$(\rho_{g_1},\rho_{g_2})$, and two atoms are adjacent exactly when they share a
column (same $\rho_{g_1}$, teal) or a row (same $\rho_{g_2}$, terracotta), ``rook
adjacency.'' Here $A,B$ share column $1$, $A,C$ share row $1$, and $B,D$ share
row $2$; the other three pairs differ in both coordinates and are non-adjacent.
A fiber is whole-axis projection-injective (WAP) exactly when its atoms
occupy distinct lines along one axis, e.g.\ distinct columns, so that axis
alone separates every atom.}
\label{fig:edge-rule}
\end{minipage}
\end{figure}

\begin{proof}
We use the maximal-fragment normal form: \textup{(NF1)} each $F_i = \{x \in R(d_0) : x \equiv r_i \pmod{g_i}\}$; \textup{(NF2)} two fragments of the same label $g \neq 1$ that meet on $R(d_0)$ are equal; \textup{(NF3)} distinct labels impose independent congruences. NF1 is the definition of the fragment generators and NF3 is immediate; NF2 (anchor uniqueness per label) is the anchor-uniqueness sublemma, formalized together with the fiber machinery in `SameSupportFiber.lean`. In particular $\rho_g$ is well defined, since by NF2 at most one label-$g$ fragment contains a given atom.

If $A, B \subseteq F_i$ for one fragment $F_i$, then its label is not $1$ (a label-$1$ fragment is a singleton residual mask, which cannot contain two distinct atoms), so $g_i \in P(A) = P(B) = P$; by NF1 every point of $A$ and of $B$ is congruent to $r_i$ modulo $g_i$, whence $\rho_{g_i}(A) = \rho_{g_i}(B) = r_i \bmod g_i$. Conversely, suppose $\rho_g(A) = \rho_g(B) = r$ for some $g \in P$. Let $F_i$ be the unique label-$g$ fragment with $A \subseteq F_i$, so $r_i \equiv r \pmod g$. Every $y \in B$ satisfies $y \equiv \rho_g(B) = r \equiv r_i \pmod{g_i}$ and $y \in R(d_0)$, so $y \in F_i$ by NF1; hence $B \subseteq F_i$ and $A, B$ share a fragment. Both directions use only that every point of an atom carries the atom's $\rho_g$-coordinate, so the argument holds verbatim for atoms of any size.
\end{proof}

The edge rule turns each per-cell cover problem into set cover by the coordinate-cliques $C_{g,r}$, a structured instance on which the next two reductions act. It is formalized in `CoordinateUnion.lean` and `SameSupportFiber.lean`.

## Exact duality and whole-axis projection-injectivity

To certify the exact value of $\tau$ for a given cell, we need to show that a particular covering is not just valid but *minimum*. The following duality proposition does that: a cover and a packing (independent set) of equal size pin $\tau$ between them, since from the top, the cover can drop no further and from below the packing can rise no higher.

\begin{proposition}[Cover--packing exact duality]\label{prop:duality}
If a cell admits a residue-axis cover of $G_{\mathrm{atom}}[X_P]$ and an independent set (packing) of the same cardinality, then that cover is minimum: $\mathrm{axis\_cover}(X_P) = \mathrm{maxPacking}(X_P)$.
\end{proposition}

This is the engine behind every certified cell below (formalized in `ResidueAxis.lean`): it reduces "compute $\tau$" to "exhibit a matching cover/packing pair," and it yields a clean structural sufficient condition.

\begin{definition}\label{def:wap}
A fiber $X_P$ is \emph{whole-axis projection-injective} (WAP) if $\rho_g$ is injective on $X_P$ for some $g \in P$; such an $X_P$ is a \emph{whole-axis projection-injective fiber}.
\end{definition}

In other words: a fiber is WAP when its atoms all have distinct coordinates along some single axis $g$. The coordinate-cliques along that axis are then singletons, but that alone does not certify the cover number: a cover may draw cliques from every axis of $P$, and two atoms that differ on $g$ can still share a coordinate on another axis. Call a fiber \emph{separated} when $\rho_g$ is injective on $X_P$ for *every* $g \in P$; by the edge rule this says exactly that $G_{\mathrm{atom}}[X_P]$ has no edges (Figure \ref{fig:wap}).

\begin{figure}[t]
\centering
\begin{lrbox}{\figbox}%
\begin{tikzpicture}[figcard, x=1.05cm, y=0.95cm,
   atom/.style={circle, draw=ink, line width=0.8pt, fill=white,
                minimum size=6.5mm, inner sep=0pt, font=\small, text=ink},
   proj/.style={-{Stealth[length=1.9mm]}, addX, line width=0.8pt},
   ax/.style={mut, line width=0.6pt},
   band/.style={rounded corners=3.5pt},
   ttl/.style={font=\small\bfseries, text=white, rounded corners=3pt,
               inner xsep=8pt, inner ysep=3.5pt}
]
  % ---- left: separated (every axis injective) ----
  \node[ttl, fill=addX] at (2,4.05) {separated};
  \foreach \r in {1,2,3} {
    \fill[band, addF!45] (0.5,\r-0.42) rectangle (3.62,\r+0.42);
    \node[font=\scriptsize, anchor=east, text=mut] at (0.34,\r) {$r_{\r}$};
  }
  \draw[ax] (0.5,0) -- (3.62,0);
  \foreach \c in {1,2,3} {
    \draw[ax] (\c,0) -- (\c,-0.12);
    \node[font=\scriptsize, anchor=north, text=mut] at (\c,-0.16) {$c_{\c}$};
  }
  \node[font=\scriptsize, anchor=west, text=mut] at (3.72,0) {$\rho_{g_1}$};
  \node[atom] (LA) at (1,1) {$A$};
  \node[atom] (LB) at (2,3) {$B$};
  \node[atom] (LC) at (3,2) {$C$};
  \draw[proj] (LA) -- (1,0.15);
  \draw[proj] (LB) -- (2,0.15);
  \draw[proj] (LC) -- (3,0.15);
  \foreach \c in {1,2,3} { \fill[addX] (\c,0) circle (1.7pt); }
  \node[font=\scriptsize, addX, align=center] at (2,-1.12)
    {3 distinct columns, 3 distinct rows:\\ every $\rho_g$ injective, no edges};
  % ---- right: WAP but not separated ----
  \node[ttl, fill=sumX] at (7.6,4.05) {WAP but not separated};
  \fill[band, addF!45] (6.1,2-0.42) rectangle (9.22,2+0.42);
  \fill[band, sumF!70] (6.1,1-0.42) rectangle (9.22,1+0.42);
  \node[font=\scriptsize, anchor=east, text=mut]  at (5.94,2) {$r_2$};
  \node[font=\scriptsize, anchor=east, text=sumX] at (5.94,1) {$r_1$};
  \draw[ax] (6.1,0) -- (9.22,0);
  \foreach \c/\lab in {6.6/1, 7.6/2, 8.6/3} {
    \draw[ax] (\c,0) -- (\c,-0.12);
    \node[font=\scriptsize, anchor=north, text=mut] at (\c,-0.16) {$c_{\lab}$};
  }
  \node[font=\scriptsize, anchor=west, text=mut] at (9.32,0) {$\rho_{g_1}$};
  \draw[proj] (7.6,1.66) -- (7.6,0.15);
  \draw[sumF!70, line width=4pt] (6.6,1) -- (8.6,1);
  \draw[sumX, line width=1.1pt] (6.6,1) -- (8.6,1);
  \node[atom] (RA) at (6.6,1) {$A$};
  \node[atom] (RB) at (7.6,2) {$B$};
  \node[atom] (RC) at (8.6,1) {$C$};
  \draw[proj] (RA) -- (6.6,0.15);
  \draw[proj] (RC) -- (8.6,0.15);
  \foreach \c in {6.6,7.6,8.6} { \fill[addX] (\c,0) circle (1.7pt); }
  \node[font=\scriptsize, sumX, align=center] at (7.6,-1.12)
    {columns all distinct, but $A,C$ share $r_1$:\\ the edge $A$--$C$ survives};
\end{tikzpicture}
\end{lrbox}%
\usebox{\figbox}\par\smallskip
\begin{minipage}{\wd\figbox}%
\caption{Separation versus whole-axis projection-injectivity
(Definition \ref{def:wap}). The shaded bands are the residue classes along the row axis $g_2$: each band is one coordinate-clique. \emph{Left:} a separated fiber: the three atoms
occupy three distinct columns and three distinct rows, so $\rho_{g_1}$ and
$\rho_{g_2}$ are both injective and, by the Coordinate-Union Edge Rule,
$G_{\mathrm{atom}}[X_P]$ has no edges. The singleton coordinate-cliques along
either axis are a minimum cover and the whole fiber is a maximum packing, so
the residual-cover number is exact (Theorem \ref{thm:pid}). \emph{Right:} a
fiber that is WAP via the column axis but not separated: the columns are all
distinct, yet $A$ and $C$ share the row residue $r_1$, so the edge $A$--$C$
survives and the fiber is not a packing. One injective axis therefore does
not certify the cover number; here the cover may use the row clique
$\{A, C\}$ and beat the column count. Non-separated fibers are where the
cover/packing deficit can appear (Section \ref{sec:open}).}
\label{fig:wap}
\end{minipage}
\end{figure}

\begin{theorem}[Separated-fiber sufficiency]\label{thm:pid}
If $X_P$ is separated, then for any $g \in P$ the singleton coordinate-cliques along $g$ form a cover and the whole fiber is a packing, so $\mathrm{axis\_cover}(X_P) = |X_P|$ is exact. Moreover every $|P| = 1$ fiber is separated.
\end{theorem}

Both parts are proved per cell (the $|P| = 1$ case routed through NF2) and formalized in `WholeAxisPID.lean`. An earlier version of this theorem drew the same conclusion from WAP alone. That is false for $|P| \geq 2$: two atoms can differ on the injective axis and still share a coordinate on another axis of $P$, so the fiber need not be a packing. The failure is not rare. At $n = 220$, $d_0 = 110$, $P = (8, 25)$ the fiber has $12$ atoms with $\rho_{25}$ injective, yet all $12$ share their $\rho_8$ coordinate, so a single $8$-axis clique covers everything and the true cover number is $1$, not $12$. Computationally, separation holds for $100\%$ of $|P| = 1$ fibers and for $74.1\%, 60.2\%, 61.3\%$ of all fibers at the levels $n = 220, 440, 880$ of the dyadic family $n = 55 \cdot 2^a$; WAP alone, which certifies only the single-axis subfamily, holds for $93.8\%, 89.5\%, 89.1\%$. The non-separated fibers are the cases in which the cover--packing gap (the *deficit*) can appear: separation does not eliminate the obstruction, it locates the cells in which the obstruction can live.

For those cells, where no axis sorts the atoms one per bucket, the duality engine still mops up, through a weaker witness.

\begin{proposition}[AET exactness]\label{prop:aet}
An \textbf{anchored exact transversal} (AET) of $X_P$ is a family of coordinate-cliques covering $X_P$ together with a system of distinct representatives that is independent in $G_{\mathrm{atom}}[X_P]$. If $X_P$ admits an AET, then $\mathrm{axis\_cover}(X_P) = \mathrm{maxPacking}(X_P)$.
\end{proposition}

In other words: an AET is a cover-and-packing witness that does not require the atoms to be pairwise separated on every axis, but instead allows different parts of the fiber to be handled by different axes, provided the chosen representatives are independent. A separated fiber admits the trivial single-axis AET, in which every clique of the cover is a singleton and the fiber represents itself; a fiber that is merely WAP does not, since its atoms need not be independent. The proposition is formalized in `AnchoredExactTransversal.lean`. Whether every non-separated fiber admits an AET is the residual obstruction taken up in Section \ref{sec:open}.

## Computational frontier and verification basis

Using the schema and the duality engine, every remaining pair $(m,\ell)$ with $m \leq 5500$ has been certified to an explicit value of $k_0^\infty$: fixed-quotient family closures for $n \leq 345$, plus direct single-pair certificates for the six remaining pairs $5184 \leq m \leq 5472$. Every per-cell fact is machine-checked in Lean by `native_decide`. On the current toolchain (`leanprover/lean4:v4.33.0`), the tactic compiles and runs the closed Boolean decision procedure and then records its result as a generated per-computation axiom named like `declaration._native.native_decide.ax_*` ([Lean PR #12217](https://github.com/leanprover/lean4/pull/12217)). The Lean kernel checks the surrounding proof from that explicit assumption; it does not re-run the compiled computation. The `bv_decide` LRAT path uses the same native-evaluation mechanism for its verified checker's final Boolean result, but receives its own generated axiom. Thus the certificate trusts the Lean compiler and local CPU for the stated Boolean computation. That delegation is sound provided no project-level compiler redirection (`@[extern]`, `@[implemented_by]`, `unsafe`) shadows a verified definition in the evaluated closure, of which the development has none (the only externs it reaches are Lean-core and Mathlib primitives). No external solver output, network service, or manual step takes part in these `native_decide` certificates.

\begin{remark}\label{rem:tw}
An earlier approach bounded $\tau(d_0)$ by a nice-tree-decomposition DP on $G_{\mathrm{atom}}(d_0)$ with a three-term frontier-bag bound. On the $n = 220$ family ($d = 110t$, cap profile $(\mathrm{cap}_2, \mathrm{cap}_5, \mathrm{cap}_{11}) = (7, 3, 2)$, a collection of $96$ cells) an exhaustive scan gives a maximum treewidth $\max_{d_0} \mathrm{tw}(G_{\mathrm{atom}}(d_0)) = 15$, attained at $d_0 = 440$ and matching the bag-size bound $16$. The bound is $n$-specific, however: the treewidth already exceeds $15$ at $n = 440$ (the same prime support $\{2,5,11\}$), so the tree-decomposition route does not give a uniform DP across quotients. The Coordinate-Union Edge Rule and the cover/packing duality above superseded it as the per-cell tool.
\end{remark}

# The remaining open frontier {#sec:open}

The paper closes three questions from the prior literature and opens several new ones. This section states clearly what the current techniques do not yet resolve.

1. *AET existence and a closed form for $\tau(d_0)$.* The reductions of Section \ref{sec:structural} reduce the composite-$m$ threshold problem to a single obstruction: does every non-separated fiber admit an anchored exact transversal (Proposition \ref{prop:aet})? The answer is no, and not only for other moduli: beyond the $27 = 3^3$ coordinate axis that produces AET-failing fibers at $n \in \{330, 660\}$ (cover $14$, packing $13$), a certified failure exists on the dyadic family itself, at $n = 880$, $d_0 = 35200$, $P = (121, 125, 256)$, with packing $48$ and cover $50$. Empirically the failures are isolated: an AET exists on every other dyadic fiber tested, which covers around $30$ WAP-failing fibers, including difficult cases with large prime-power components ($11^2$ and $5^3$; $5^4$ and $11^3$), for $n$ up to $14080$, and all $75$ fibers at $n \in \{220, 440\}$ that are WAP but not separated, where the exact minimum cover equals the exact maximum packing throughout. A certified prose proof now covers every two-axis fiber: finite bipartite matching gives an AET even with parallel atoms and extensionally duplicate coordinate cliques. This construction has no Lean companion. No comparable structural argument is known for fibers with three or more axes. A closed form for $\tau(d_0)$ therefore cannot lean on AET alone; it must either characterize where AET fails or bound the cover--packing deficit there directly. The deficit across four dyadic levels grew $5 \to 7 \to 11 \to 14$ with no convergent trajectory, and every simple scalar predictor of $\tau$ (dyadic level, support exponent, maximal class size, class counts, projection size) has been ruled out by the data, leaving the shape of the covering certificate as the only surviving predictor. A uniform closed form for $\tau(d_0)$ at composite $m$ thus remains conjectural.
2. *Boundary $1 < k < n - 1$.* Theorem \ref{thm:main} governs the "many classes" regime $k \geq n - 1$, and Theorem \ref{thm:k1} settles the single-class case $k = 1$. The intermediate regime $1 < k < n - 1$, where classes must be simultaneously large and $\ell$-sum-free, is empirically eventually periodic in $\ell \bmod m$ for fixed $k$ (verified through $m \leq 13$), but there is no formula.
3. *Optimizing over $\ell$.* For fixed $k$ and $m \to \infty$, what is $\max_\ell S_m(k, \ell)$? Theorem \ref{thm:main} supplies the pointwise value only when $k \geq n - 1$, a condition that depends on $\ell$, so for fixed $k$ the maximum can come from the boundary regime of the previous item: at $m = 100$, $k = 1$, Theorem \ref{thm:k1} gives $S_{100}(1, 10) = 9$, while Theorem \ref{thm:main} at $k = 1$ covers only the $\ell$ with $n \leq 2$. Within the range where Theorem \ref{thm:main} applies the question is a divisor-counting problem on $m$; outside it, it is open.

# Revision history {#sec:revisions}

- *June 2026.* First version.
- *2026-08-23.* Theorem \ref{thm:pid} restated with separation on every axis of $P$; the earlier statement, which assumed weak axis projection on a single axis, is false for $|P| \geq 2$ (at $(n, d_0, P) = (220, 110, (8, 25))$ the true cover is $1$ where $12$ was claimed). The abstract and open problem 1 now record the certified dyadic AET failure at $n = 880$.
- *2026-08-24.* Section \ref{sec:structural} restated for the stable-regime threshold $k_0^\infty$, which is now defined there; the earlier display $k_0(m,\ell) = K(d_0) + \tau(d_0)$ for the ordinary threshold is false ($(5,2)$ and $(5,3)$ share a cell with $k_0 = 2$ and $4$). The hypotheses $\ell \geq p - 1$ and $\ell \not\equiv 1 \pmod p$ added to the prime-threshold statements in the abstract and in the caption of Figure \ref{fig:coset-fill}, with the value attributed to D'orville et al., Corollary 8. Open problem 3 corrected. $n \geq 2$ added to Theorem \ref{thm:k0-lower-cov}; the gloss after Theorem \ref{thm:k0-upper} corrected at $n = 1$; the caption of Figure \ref{fig:coset-fill} no longer asserts $1C \subset 2C$; the one-color check count corrected from $414$ to $435$; "axis label" replaces "prime" for the atom coordinates; the Lean formalization sentence in the introduction narrowed to the public modules.
- *2026-08-24, two-axis closure.* Open problem 1 now records the independently certified prose proof that every two-axis fiber admits an AET by finite bipartite matching, including parallel atoms and extensional duplicate cliques. Lean formalization remains open.
- *2026-08-30.* Retitled *Prime-adic structure of the stable regime for modular Schur numbers*. No mathematical claim changed in this revision.
- *2026-08-30 (title correction).* Retitled *Prime-power structure of the stable regime for modular Schur numbers* for terminological clarity. No mathematical claim changed in this revision.

# References

\begin{thebibliography}{DSWH25}

\bibitem[ABB+25]{aristotle}
T. Achim, A. Best, A. Bietti, K. Der, M. Fédérico, S. Gukov, D. Halpern-Leistner, K. Henningsgard, Y. Kudryashov, A. Meiburg, M. Michelsen, R. Patterson, E. Rodriguez, L. Scharff, V. Shanker, V. Sicca, H. Sowrirajan, A. Swope, M. Tamas, V. Tenev, J. Thomm, H. Williams, and L. Wu,
\emph{Aristotle: IMO-level Automated Theorem Proving},
2025. arXiv:2510.01346.

\bibitem[BB82]{BB1982}
A. Beutelspacher and W. Brestovansky,
\emph{Generalized Schur numbers},
in \emph{Combinatorial Theory} (Schloß Rauischholzhausen, 1982),
Lecture Notes in Mathematics \textbf{969}, Springer, 1982, pp. 30--38.

\bibitem[Cau13]{Cauchy1813}
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
Integers \textbf{25} (2025), \#A62.

\bibitem[Heu17]{Heule2017}
M. J. H. Heule,
\emph{Schur number five},
Proceedings of AAAI 2018, 6598--6606. arXiv:1711.08076.

\bibitem[LR14]{LR2014}
B. M. Landman and A. Robertson,
\emph{Ramsey Theory on the Integers}, 2nd ed.,
Student Mathematical Library \textbf{73}, American Mathematical Society, 2014.

\end{thebibliography}
