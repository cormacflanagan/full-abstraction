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
    have hle : a ⊑ (DSub.bot : DSub σ Ctx.empty) := ha
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

/-- `sub1 ⌜0⌝` denotes `⊥`: `sub1` probes its argument with the initial query,
receives the answer `0`, and its branching function sends `0` to `⊥`
(Definition 4.19). -/
theorem apply0_sub1_zero : apply0 treeSub1 (.leaf (.num 0)) = (Tree.bot : Tree 𝕆) := rfl

theorem meaning_omegaTerm (E : Tmodel.Env) :
    Tmodel.meaning E omegaTerm 𝕆 = Ideal.principal (DSub.bot : D 𝕆) := by
  apply Ideal.ext
  intro a
  constructor
  · -- every finite approximation of `apply (sub1, ⌜0⌝)` is below `⊥`
    rintro ⟨f, hf, d, hd, ha⟩
    have hfle : f.1 ⊑ treeSub1 := hf
    have hdle : d.1 ⊑ (Tree.leaf (.num 0) : Tree 𝕆) := hd
    have : apply0 f.1 d.1 ⊑ (Tree.bot : Tree 𝕆) := by
      rw [← apply0_sub1_zero]
      exact Po.le_trans (apply0_mono_left hfle d.1) (apply0_mono_right treeSub1 hdle)
    exact Po.le_trans (show a.1 ⊑ apply0 f.1 d.1 from ha) this
  · intro ha
    have hle : a ⊑ (DSub.bot : D 𝕆) := ha
    have hEq : a = DSub.bot := Po.le_antisymm hle (DSub.bot_le a)
    subst hEq
    exact ⟨DSub.bot, Tree.Le.bot _, DSub.bot, Tree.Le.bot _, Tree.Le.bot _⟩

/-- The meaning function `T` restricted to closed phrases uses the everywhere-`⊥`
environment; closed phrases do not consult it. -/
noncomputable def botEnv : Tmodel.Env := fun _ σ => ScottDomain.bot (α := T σ)

theorem hasTy_omegaTerm : Term.HasTy [] omegaTerm 𝕆 :=
  Term.HasTy.app Term.HasTy.const Term.HasTy.const

/-- Filling a multi-hole context with type-compatible replacements preserves
typing. -/
theorem MCtx.fill_hasTy_mono {k : Nat} (Ms Ms' : Fin k → Term SPCF)
    (hMs : ∀ (i : Fin k) (ν : Ty) (Γ : List (Nat × Ty)),
      Term.HasTy Γ (Ms i) ν → Term.HasTy Γ (Ms' i) ν) :
    ∀ (C : MCtx SPCF k) (Γ : List (Nat × Ty)) (ρ : Ty),
      Term.HasTy Γ (C.fill Ms) ρ → Term.HasTy Γ (C.fill Ms') ρ := by
  intro C
  induction C with
  | hole i => intro Γ ρ h; exact hMs i ρ Γ h
  | var x ν => intro Γ ρ h; exact h
  | const c => intro Γ ρ h; exact h
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ h
    cases h with | app h₁ h₂ => exact Term.HasTy.app (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | lam x ν C ih =>
    intro Γ ρ h
    cases h with | lam hC => exact Term.HasTy.lam (ih _ _ hC)

/-- Monotonicity of the meaning function in every hole, in the form the
induction needs. -/
theorem meaning_mono_aux {k : Nat} (Ms Ms' : Fin k → Term SPCF)
    (hMs : ∀ (i : Fin k) (ν : Ty) (Γ : List (Nat × Ty)),
      Term.HasTy Γ (Ms i) ν → Term.HasTy Γ (Ms' i) ν)
    (hle : ∀ (i : Fin k) (E' : Tmodel.Env) (ν : Ty),
      Tmodel.combMeaning E' (Term.toComb (Ms i)) ν
        ⊑ Tmodel.combMeaning E' (Term.toComb (Ms' i)) ν) :
    ∀ (C : MCtx SPCF k) (Γ : List (Nat × Ty)) (ρ : Ty) (E : Tmodel.Env),
      Term.HasTy Γ (C.fill Ms) ρ →
      Tmodel.combMeaning E (Term.toComb (C.fill Ms)) ρ
        ⊑ Tmodel.combMeaning E (Term.toComb (C.fill Ms')) ρ := by
  intro C
  induction C with
  | hole i => intro Γ ρ E _; exact hle i E ρ
  | var x ν => intro Γ ρ E _; exact Po.le_refl _
  | const c => intro Γ ρ E _; exact Po.le_refl _
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ E h
    cases h with
    | app h₁ h₂ =>
      rename_i α
      have e₂ : Comb.tyOf (Term.toComb (C₂.fill Ms)) = α := Term.tyOf_toComb h₂
      have e₂' : Comb.tyOf (Term.toComb (C₂.fill Ms')) = α :=
        Term.tyOf_toComb (MCtx.fill_hasTy_mono Ms Ms' hMs C₂ Γ α h₂)
      show Tmodel.combMeaning E (.app (Term.toComb (C₁.fill Ms))
        (Term.toComb (C₂.fill Ms))) ρ ⊑ _
      rw [Model.combMeaning_app, e₂]
      show _ ⊑ Tmodel.combMeaning E (.app (Term.toComb (C₁.fill Ms'))
        (Term.toComb (C₂.fill Ms'))) ρ
      rw [Model.combMeaning_app, e₂']
      exact Po.le_trans (applyT_mono_left (ih₁ Γ (α ⇒ ρ) E h₁) _)
        (applyT_mono_right _ (ih₂ Γ α E h₂))
  | lam x ν C ih =>
    intro Γ ρ E h
    cases h with
    | lam hC =>
      rename_i τ
      show Tmodel.combMeaning E (Comb.lamStar x ν (Term.toComb (C.fill Ms))) (ν ⇒ τ)
        ⊑ Tmodel.combMeaning E (Comb.lamStar x ν (Term.toComb (C.fill Ms'))) (ν ⇒ τ)
      refine orderExtensional_T _ _ fun z => ?_
      rw [lamStar_apply E x ν z _ τ Γ (Term.toComb_hasTy hC),
        lamStar_apply E x ν z _ τ Γ
          (Term.toComb_hasTy (MCtx.fill_hasTy_mono Ms Ms' hMs C ((x, ν) :: Γ) τ hC))]
      exact ih ((x, ν) :: Γ) τ (Model.envUpdate E x ν z) hC

/-- The meaning function is monotone in every hole of a context.  This is the
monotonicity that Theorem 6.5 uses; it follows from the monotonicity of `apply`
in both arguments (`apply0_mono_left`, `apply0_mono_right`), the abstraction
lemma `lamStar_apply`, and order-extensionality for the `λ` case.

The two `Program` hypotheses are needed: with an ill-typed replacement the
filled context has an unconstrained meaning. -/
theorem Tmeaning_mono {k : Nat} (C : MCtx SPCF k) (M : Fin k → Term SPCF) (j : Fin k)
    (N : Term SPCF) (hN : Term.HasTy [] N 𝕆)
    (h1 : Term.Closed (C.fill (repl M j omegaTerm))
      ∧ Term.HasTy [] (C.fill (repl M j omegaTerm)) 𝕆)
    (_ : Term.Closed (C.fill (repl M j N)) ∧ Term.HasTy [] (C.fill (repl M j N)) 𝕆) :
    Tmodel.meaning botEnv (C.fill (repl M j omegaTerm)) 𝕆
      ⊑ Tmodel.meaning botEnv (C.fill (repl M j N)) 𝕆 := by
  refine meaning_mono_aux (repl M j omegaTerm) (repl M j N) ?_ ?_ C [] 𝕆 botEnv h1.2
  · intro i ν Γ hi
    by_cases hij : i = j
    · subst hij
      rw [repl_self] at hi ⊢
      have hν : ν = 𝕆 := Term.hasTy_unique hi hasTy_omegaTerm
      subst hν
      exact Term.weaken (fun _ hp => absurd hp (by simp)) hN
    · simp only [repl, if_neg hij] at hi ⊢
      exact hi
  · intro i E' ν
    by_cases hij : i = j
    · subst hij
      rw [repl_self, repl_self,
        show Tmodel.combMeaning E' (Term.toComb omegaTerm) ν
          = Tmodel.meaning E' omegaTerm ν from rfl]
      by_cases hν : ν = 𝕆
      · subst hν
        rw [meaning_omegaTerm E']
        exact principal_bot_le _
      · show Tmodel.combMeaning E' (.app (.const .sub1) (.const (.num 0))) ν ⊑ _
        rw [Model.combMeaning_app,
          show Comb.tyOf (Comb.const (SConst.num 0) : Comb SPCF) = 𝕆 from rfl,
          show Tmodel.combMeaning E' (Comb.const SConst.sub1) (𝕆 ⇒ ν)
            = ScottDomain.bot from by
              show (if h : (𝕆 ⇒ 𝕆) = (𝕆 ⇒ ν) then _ else ScottDomain.bot) = _
              rw [dif_neg (fun h => hν (by injection h with _ h2; exact h2.symm))]]
        exact Po.le_trans (show Tmodel.apply (ScottDomain.bot : T (𝕆 ⇒ ν)) _
            ⊑ Ideal.principal (DSub.bot : D ν) from
          (applyT_bot 𝕆 ν _).symm ▸ Po.le_refl _) (principal_bot_le _)
    · simp only [repl, if_neg hij]
      exact Po.le_refl _

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
  OmegaLike N := Term.HasTy [] N 𝕆
  omega_omegaLike := hasTy_omegaTerm
  mono := Tmeaning_mono

end FA
