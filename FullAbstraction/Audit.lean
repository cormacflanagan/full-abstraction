/-
# Audit

Every numbered result of the paper, with its Lean name.  The `#print axioms`
lines below report, for each, whether its proof is complete (`propext`,
`Classical.choice`, `Quot.sound` only) or still rests on `sorryAx`.

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
#print axioms Tree.join_spec
#print axioms TreeOk_join
#print axioms dsub_lub_of_finite_bounded
#print axioms lemma_4_3
#print axioms finiteApprox_directed
#print axioms Finitary_of_TreeOk
#print axioms lemma_4_7
#print axioms claim_4_8
#print axioms apply0_mono_left
#print axioms apply0_mono_right
#print axioms at'_mono
#print axioms at'_resp
#print axioms apply0_first
#print axioms apply0_ok
#print axioms lemma_4_14
#print axioms applyArgs_at_query
#print axioms corollary_4_15
#print axioms corollary_4_15_path
#print axioms T_base_flat
#print axioms Comb.tyOf_of_hasTy
#print axioms Comb.lamStar_hasTy
#print axioms Term.toComb_hasTy
#print axioms Kn_mono
#print axioms In_mono
#print axioms claim_A_2
#print axioms claim_A_2_le
#print axioms claim_A_2_ge
#print axioms claim_I_le
#print axioms claim_I_ge
#print axioms Comb.subst_hasTy
#print axioms Comb.weaken
#print axioms Term.weaken
#print axioms Term.hasTy_unique
#print axioms Model.combMeaning_congr_env
#print axioms plant_step_self
#print axioms at'_plant_self
#print axioms le_plant
#print axioms at'_plant_other
#print axioms substTree_le_plant
#print axioms TreeOk_congr_ctx
#print axioms Resp.toTree_substAns
#print axioms chain_directed
#print axioms applyT_mono_left
#print axioms applyT_mono_right
#print axioms Model.extensional_of_orderExtensional
#print axioms SemDef.seqIndex_of_propagates
#print axioms SemDef.theorem_6_5
#print axioms TreeOk_at'
#print axioms legalQuery_join_snoc
#print axioms Query.ctxFrom_snoc
#print axioms KnP_ok
#print axioms KnP_le_Kn
#print axioms apply0_KnP_ge
#print axioms Kn_legal_cofinal
#print axioms InP_ok
#print axioms InP_le_In
#print axioms apply0_InP_ge
#print axioms In_legal_cofinal
#print axioms lemma_A_1
#print axioms theorem_4_22_I
end Complete

section DerivedOrDependent
-- Results with real proofs whose statement or ingredients still mention a
-- `sorry`; `#print axioms` therefore reports `sorryAx`.  Anything mentioning
-- `Tmodel` inherits it from `Y_chain_directed` and `claim_A_5`, and anything
-- mentioning `SPCFSem` from `Tmeaning_mono`.
#print axioms theorem_4_11
#print axioms corollary_4_18
#print axioms theorem_4_22
#print axioms lemma_A_6
#print axioms lemma_4_3_omega_algebraic
#print axioms meaning_omegaTerm
#print axioms meaning_errTerm
#print axioms meaning_apps
#print axioms applyT_eq_of_principal
#print axioms eq_of_principal_applyIdeals
#print axioms separation
#print axioms beta_law
#print axioms lamStar_apply
#print axioms corollary_4_23
#print axioms soundness_aux
#print axioms soundness
#print axioms Tmeaning_mono
#print axioms meaning_mono_aux
#print axioms meaning_Omega
#print axioms Y_chain_directed
#print axioms applyT_interpY_fix
#print axioms corollary_4_24
#print axioms theorem_5_1_separating
#print axioms theorem_5_1
#print axioms theorem_5_1_fullyAbstract
#print axioms theorem_6_2
#print axioms theorem_6_4
#print axioms theorem_6_7
end DerivedOrDependent

section Outstanding
-- Results still resting on `sorryAx` because their own proof is `sorry`.
#print axioms dsub_countable
#print axioms lemma_4_16
#print axioms orderExtensional_T
#print axioms claim_A_5
#print axioms lemma_A_7
#print axioms lemma_B_1
#print axioms theorem_4_27
#print axioms lemma_5_2
#print axioms lemma_5_2_subtrees
#print axioms probe_index
#print axioms catch_returns_index
end Outstanding

end FA
