import Solution

/-
Comparator axiom audit. Prints the `#print axioms` closure for every theorem in
`Solution.lean` that the comparator config lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer (or CI) see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} — no `sorryAx`, no custom axioms, and
no generated native-evaluation axiom such as
`declaration._native.native_decide.ax_*` — the structural comparator set uses
no `native_decide`, so it is absent here. The private development checkout's
historical native-backed scan tree is omitted from the public snapshot and is
outside this gate; see comparator/README.md "audit boundary".

The current 12 theorems live in the shared `Headline` namespace in
`Solution.lean`, so the comparator finds them under the same qualified names
listed in `config.json`.

Run (from the `lean/` directory): lake env lean comparator/axiom-audit.lean
-/

#print axioms Headline.schurMod_eq
#print axioms Headline.schurMod_is_greatest
#print axioms Headline.no_valid_partition_of_ge_m
#print axioms Headline.schurMod_eq_schurModResidue
#print axioms Headline.schurModResidue_eq
#print axioms Headline.schurModResidue_le
#print axioms Headline.le_schurModResidue
#print axioms Headline.singleton_sumFree_iff
#print axioms Headline.unsafe_witness_residue
#print axioms Headline.not_sumFree_of_mem_zero
#print axioms Headline.schurModResidue_k1
#print axioms Headline.sigmaInfty_le
