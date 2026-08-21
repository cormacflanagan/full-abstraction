/-
# Audit

Every numbered result of the paper, with its Lean name.  Uncommenting the
`#print axioms` lines below reports, for each, whether its proof is complete
(`propext, Classical.choice, Quot.sound` only) or still rests on `sorryAx`.

Run `lake env lean FullAbstraction/Audit.lean` to check.
-/
import FullAbstraction

namespace FA

section Complete
-- Results whose proofs are complete.
#print axioms theorem_4_4_directed_lub
#print axioms theorem_4_4_bounded_lub
#print axioms theorem_4_4_bot
#print axioms theorem_4_4_algebraic
#print axioms theorem_4_4_finite_elements
#print axioms theorem_4_4_countably_many_finite
#print axioms lemma_4_3_partial_order
#print axioms dsub_lub_of_finite_bounded
#print axioms finiteApprox_directed
#print axioms Tree.join_spec
#print axioms TreeOk_join
#print axioms lemma_4_3
#print axioms lemma_4_7
#print axioms apply0_sub1_zero
#print axioms apply0_mono_left
#print axioms apply0_mono_right
#print axioms at'_mono
#print axioms theorem_4_11
#print axioms corollary_4_18
#print axioms Kn_mono
#print axioms In_mono
#print axioms T_base_flat
#print axioms Model.extensional_of_orderExtensional
#print axioms SemDef.seqIndex_of_propagates
#print axioms SemDef.theorem_6_5
#print axioms theorem_5_1_separating
#print axioms theorem_5_1
#print axioms theorem_5_1_fullyAbstract
#print axioms theorem_6_2
#print axioms theorem_6_4
#print axioms theorem_6_7
#print axioms theorem_4_22
#print axioms lemma_A_6
end Complete

section DerivedOrDependent
-- Results with real proofs whose *statement* or *ingredients* still mention a
-- `sorry`; `#print axioms` therefore reports `sorryAx` for them.  In
-- particular anything mentioning `Tmodel` inherits it from `Y_chain_directed`
-- and `claim_A_5`, and anything mentioning `SPCFSem` from `Tmeaning_mono`.
#print axioms lemma_4_3_omega_algebraic
#print axioms meaning_omegaTerm
#print axioms meaning_errTerm
end DerivedOrDependent

section Outstanding
-- Results still resting on `sorryAx` because their own proof is `sorry`.
#print axioms dsub_countable
#print axioms apply0_ok
#print axioms claim_4_8
#print axioms lemma_4_14
#print axioms corollary_4_15
#print axioms lemma_4_16
#print axioms orderExtensional_T
#print axioms claim_A_5
#print axioms lemma_A_1
#print axioms claim_A_2
#print axioms lemma_A_7
#print axioms theorem_4_22_I
#print axioms corollary_4_23
#print axioms corollary_4_24
#print axioms Y_chain_directed
#print axioms lemma_B_1
#print axioms theorem_4_27
#print axioms lemma_5_2
#print axioms lemma_5_2_subtrees
#print axioms soundness
#print axioms separation
#print axioms meaning_apps
#print axioms Tmeaning_mono
#print axioms probe_index
#print axioms catch_returns_index
end Outstanding

end FA
