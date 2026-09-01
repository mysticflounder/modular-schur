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

The current 13 theorems live in the shared `ComparatorClaims` namespace in
`Solution.lean`, so the comparator finds them under the same qualified names
listed in `config.json`.

Run (from the `lean/` directory): lake env lean comparator/axiom-audit.lean
-/

#print axioms ComparatorClaims.schurMod_integerClosedForm
#print axioms ComparatorClaims.schurMod_integerCap_isGreatest
#print axioms ComparatorClaims.noValidIntegerPartition_of_ge_modulus
#print axioms ComparatorClaims.schurMod_integer_eq_residue
#print axioms ComparatorClaims.schurModResidue_closedForm
#print axioms ComparatorClaims.schurModResidue_upperBound
#print axioms ComparatorClaims.schurModResidue_lowerBound
#print axioms ComparatorClaims.singleton_sumFree_iff_nonzeroMultiple
#print axioms ComparatorClaims.criticalResidue_isUnsafe
#print axioms ComparatorClaims.zeroMem_notSumFree
#print axioms ComparatorClaims.schurModResidue_oneColorClosedForm_of_le_modulus
#print axioms ComparatorClaims.schurModResidue_oneColorClosedForm
#print axioms ComparatorClaims.sigmaInfty_card_le_minFacQuotient
