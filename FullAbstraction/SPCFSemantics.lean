/-
# The semantic definition of SPCF (Definition 6.1)

"The semantic definition of SPCF is the meaning function `T` determined by the
model `T` restricted to programs."

To instantiate the generic framework of `Semantics.lean` we must check that the
ground domain `T_o` really is the *flat* domain of ground answers that
Definitions 6.3 and 2.9 presuppose.  That is proved here.
-/
import FullAbstraction.Combinators

namespace FA

open Po

/-! ## The ground domain `T_o` is flat -/

/-- A tree of ground type is a leaf: `o` has no arguments, so there is no index
`i` for a node `⟨i, q, f⟩`. -/
theorem tree_base_leaf (t : Tree 𝕆) : ∃ v, t = .leaf v := by
  cases t with
  | leaf v => exact ⟨v, rfl⟩
  | node i _ _ => exact absurd i.isLt (by simp)

/-- `d ⊑ ⊥` forces `d = ⊥`. -/
theorem DSub.eq_bot_of_le_bot {σ : Ty} {γ : Ctx σ} {d : DSub σ γ} (h : d ⊑ DSub.bot) :
    d = DSub.bot := Po.le_antisymm h (DSub.bot_le d)

/-- `D_o` is flat: a proper element is maximal. -/
theorem D_base_flat (a b : D 𝕆) (ha : a ≠ DSub.bot) (hab : a ⊑ b) : a = b := by
  obtain ⟨v, hv⟩ := tree_base_leaf a.1
  obtain ⟨w, hw⟩ := tree_base_leaf b.1
  apply Subtype.ext
  have h : Tree.Le a.1 b.1 := hab
  rw [hv, hw] at h ⊢
  cases h with
  | bot d => exact absurd (Subtype.ext (by rw [hv]; rfl) : a = DSub.bot) ha
  | leaf v => rfl

/-- An ideal all of whose elements are `⊥` is the principal ideal of `⊥`. -/
theorem T_eq_bot {σ : Ty} (A : T σ) (h : ∀ a, a ∈ A → a = DSub.bot) :
    A = Ideal.principal (DSub.bot : D σ) := by
  apply Ideal.ext
  intro a
  constructor
  · intro ha; rw [h a ha]; exact Po.le_refl (DSub.bot : D σ)
  · intro ha
    obtain ⟨b, hb⟩ := A.nonempty'
    have hle : a ⊑ (DSub.bot : DSub σ []) := ha
    have hEq : a = DSub.bot := Po.le_antisymm hle (DSub.bot_le a)
    rw [hEq, ← h b hb]; exact hb

/-- **`T_o` is a flat domain.**  This is what Definitions 2.9 and 6.3 mean by
"a flat domain for the ground type". -/
theorem T_base_flat (A B : T 𝕆) (hA : A ≠ Ideal.principal (DSub.bot : D 𝕆))
    (hAB : A ⊑ B) : A = B := by
  -- `A` contains a proper element `a`
  have hex : ∃ a, a ∈ A ∧ a ≠ DSub.bot := by
    refine Classical.byContradiction fun h => hA (T_eq_bot A fun a ha => ?_)
    exact Classical.byContradiction fun hne => h ⟨a, ha, hne⟩
  obtain ⟨a, haA, hane⟩ := hex
  have haB : a ∈ B := hAB a haA
  refine Po.le_antisymm hAB ?_
  intro b hb
  obtain ⟨c, hc, hac, hbc⟩ := B.directed' a b haB hb
  have : a = c := D_base_flat a c hane hac
  exact A.downward b a (this ▸ hbc) haA

/-! ## Definition 6.1: the semantic definition of SPCF -/

/-- `⌜n⌝` as an element of `T_o`. -/
noncomputable def natAns (n : Nat) : T 𝕆 :=
  Ideal.principal ⟨.leaf (.num n), TreeOk.leaf _ _⟩

theorem natAns_inj (m n : Nat) (h : natAns m = natAns n) : m = n := by
  have := Ideal.principal_inj h
  have h2 : (Tree.leaf (.num m) : Tree 𝕆) = .leaf (.num n) := congrArg Subtype.val this
  cases h2; rfl

theorem natAns_ne_bot (n : Nat) : natAns n ≠ Ideal.principal (DSub.bot : D 𝕆) := by
  intro h
  have := Ideal.principal_inj h
  have h2 : (Tree.leaf (.num n) : Tree 𝕆) = Tree.bot := congrArg Subtype.val this
  exact absurd h2 (by simp [Tree.bot])

/-- `Ω`, a canonical divergent SPCF program: `sub1 ⌜0⌝`. -/
def omegaTerm : Term SPCF := .app (.const .sub1) (.const (.num 0))

theorem meaning_omegaTerm (E : Tmodel.Env) :
    Tmodel.meaning E omegaTerm 𝕆 = Ideal.principal (DSub.bot : D 𝕆) := by
  sorry

/-- The meaning function `T` restricted to closed phrases uses the everywhere-`⊥`
environment; closed phrases do not consult it. -/
noncomputable def botEnv : Tmodel.Env := fun _ σ => ScottDomain.bot (α := T σ)

/-- The meaning function is monotone in every hole of a context.  This is the
monotonicity that Theorem 6.5 uses; it follows from the monotonicity of
`apply` and of the abstraction algorithm. -/
theorem Tmeaning_mono {k : Nat} (C : MCtx SPCF k) (M : Fin k → Term SPCF) (j : Fin k)
    (N : Term SPCF) :
    Tmodel.meaning botEnv (C.fill (repl M j omegaTerm)) 𝕆
      ⊑ Tmodel.meaning botEnv (C.fill (repl M j N)) 𝕆 := by
  sorry

/-- **Definition 6.1** (*Semantic Definition of SPCF*).

"The semantic definition of SPCF is the meaning function `T` determined by the
model `T` restricted to programs."  Programs are the closed phrases of ground
type. -/
noncomputable def SPCFSem : SemDef SPCF where
  Ans := T 𝕆
  po := inferInstance
  bot := Ideal.principal (DSub.bot : D 𝕆)
  bot_le A := by
    intro a ha
    obtain ⟨b, hb⟩ := A.nonempty'
    have hle : a ⊑ (DSub.bot : D 𝕆) := ha
    exact A.downward a b (Po.le_trans hle (DSub.bot_le b)) hb
  flat := T_base_flat
  nat := natAns
  nat_inj := natAns_inj
  nat_ne_bot := natAns_ne_bot
  Program M := Term.Closed M ∧ Term.HasTy [] M 𝕆
  meaning M := Tmodel.meaning botEnv M 𝕆
  omega := omegaTerm
  meaning_omega := meaning_omegaTerm botEnv
  mono := Tmeaning_mono

end FA
