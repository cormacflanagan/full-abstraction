/-
# Equations for `catch` and `error` (§4.4, Appendix B)

States **Lemma 4.26**, **Theorem 4.27** and **Lemma B.1**.

"If we place an `error` value or `⊥` in the hole of an evaluation context, the
entire term denotes the value placed in the hole.  In addition, `catch` can
determine which variable occurs in the hole of an evaluation context in its
procedure argument." (§4.4)
-/
import FullAbstraction.SPCFSemantics

namespace FA

open Po

/-- The variables `x₁, …, xₙ` of a type list, named by their position. -/
def varsOf (l : List Ty) : List (Nat × Ty) :=
  (List.finRange l.length).map fun i => (i.val, l[i.val]'i.isLt)

/-! ## Leaf-valued ideals and their propagation

The `(error)` and `(bottom)` clauses of Theorem 4.27 are both instances of one
computation: a leaf value in a strict position propagates through `apply`. -/

/-- The principal ideal of a leaf, at any type: `⊥`, `errorᵢ` or (at ground
type, morally) a numeral. -/
noncomputable def leafT (σ : Ty) (v : Val) : T σ :=
  Ideal.principal ⟨.leaf v, TreeOk.leaf _ _⟩

/-- Membership in a leaf ideal. -/
theorem mem_leafT {σ : Ty} {v : Val} {d : D σ} :
    d ∈ leafT σ v ↔ Tree.Le d.1 (.leaf v) := Iff.rfl

/-- A leaf denotes the constant function: application ignores the argument. -/
theorem applyT_leafT {σ τ : Ty} (v : Val) (X : T σ) :
    applyT (leafT (σ ⇒ τ) v) X = leafT τ v := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨f, hf, d, hd, hc⟩
    have h1 : Tree.Le c.1 (apply0 f.1 d.1) := hc
    have h2 : Tree.Le (apply0 f.1 d.1) (apply0 (.leaf v) d.1) :=
      apply0_mono_left (hf : Tree.Le f.1 (.leaf v)) d.1
    exact mem_leafT.mpr (Tree.Le.trans h1 h2)
  · intro hc
    obtain ⟨d, hd⟩ := X.nonempty'
    exact ⟨⟨.leaf v, TreeOk.leaf _ _⟩, mem_leafT.mpr (Tree.Le.refl _), d, hd,
      (mem_leafT.mp hc : Tree.Le c.1 (.leaf v))⟩

/-- The root query of a legal closed tree is `?`. -/
theorem root_query_hole {σ : Ty} {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f : Resp (σ.arg i) → Tree σ} (h : TreeOk Ctx.empty (Tree.node i q f)) :
    q = Query.hole := by
  obtain ⟨hlq, _, _, _⟩ := TreeOk_node_inv h
  cases q with
  | hole => rfl
  | step i' p r rest =>
    exact absurd hlq.1 (by simp [Ctx.empty, Tree.bot, Tree.at', Tree.stepAt])

/-- A root probe consuming `⊥` produces `⊥`. -/
theorem apply0_rootProbe_bot {σ τ : Ty} (h0 : 0 < (σ ⇒ τ).arity)
    (f : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)) :
    apply0 (Tree.node ⟨0, h0⟩ .hole f) Tree.bot = Tree.bot := by
  rw [apply0]
  rfl

/-- A root probe consuming `errorᵢ` produces `errorᵢ`. -/
theorem apply0_rootProbe_err {σ τ : Ty} (h0 : 0 < (σ ⇒ τ).arity)
    (f : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)) (b : Bool) :
    apply0 (Tree.node ⟨0, h0⟩ .hole f) (.leaf (.err b)) = .leaf (.err b) := by
  rw [apply0]
  rfl

/-- A root probe applied to `⊥` yields `⊥`: the strict half of the `(bottom)`
clause. -/
theorem applyT_rootProbe_bot {σ τ : Ty} (h0 : 0 < (σ ⇒ τ).arity)
    (g : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)) :
    applyT (idealOf (Tree.node ⟨0, h0⟩ .hole g)) (leafT σ .bot) = leafT τ .bot := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨f, hf, d, hd, hc⟩
    have hdb : d.1 = Tree.bot :=
      Tree.eq_bot_of_le_bot (mem_leafT.mp hd)
    have h1 : Tree.Le c.1 (apply0 f.1 d.1) := hc
    refine mem_leafT.mpr (Tree.Le.trans h1 ?_)
    cases hfv : f.1 with
    | leaf v =>
      have hle : Tree.Le (Tree.leaf v) (Tree.node ⟨0, h0⟩ .hole g) :=
        hfv ▸ (hf : Tree.Le f.1 _)
      cases hle with
      | bot => exact Tree.Le.refl _
    | node i2 q2 f2 =>
      have hle : Tree.Le (Tree.node i2 q2 f2) (Tree.node ⟨0, h0⟩ .hole g) :=
        hfv ▸ (hf : Tree.Le f.1 _)
      cases hle with
      | node _ _ _ _ _ =>
        rw [hdb, apply0_rootProbe_bot h0 f2]
        exact Tree.Le.refl _
  · intro hc
    refine ⟨DSub.bot, Tree.Le.bot _, ⟨.leaf .bot, TreeOk.leaf _ _⟩,
      mem_leafT.mpr (Tree.Le.refl _), ?_⟩
    show Tree.Le c.1 (apply0 (Tree.bot : Tree (σ ⇒ τ)) (Tree.leaf Val.bot : Tree σ))
    exact mem_leafT.mp hc

/-- A root probe applied to `errorᵢ` yields `errorᵢ`: the strict half of the
`(error)` clause. -/
theorem applyT_rootProbe_err {σ τ : Ty} (h0 : 0 < (σ ⇒ τ).arity)
    (g : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)) (b : Bool) :
    applyT (idealOf (Tree.node ⟨0, h0⟩ .hole g)) (leafT σ (.err b))
      = leafT τ (.err b) := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨f, hf, d, hd, hc⟩
    have h1 : Tree.Le c.1 (apply0 f.1 d.1) := hc
    refine mem_leafT.mpr (Tree.Le.trans h1 ?_)
    cases hfv : f.1 with
    | leaf v =>
      have hle : Tree.Le (Tree.leaf v) (Tree.node ⟨0, h0⟩ .hole g) :=
        hfv ▸ (hf : Tree.Le f.1 _)
      cases hle with
      | bot => exact Tree.Le.bot _
    | node i2 q2 f2 =>
      have hle : Tree.Le (Tree.node i2 q2 f2) (Tree.node ⟨0, h0⟩ .hole g) :=
        hfv ▸ (hf : Tree.Le f.1 _)
      cases hle with
      | node _ _ _ _ _ =>
        have hdc : d.1 = Tree.bot ∨ d.1 = .leaf (.err b) := by
          cases hdv : d.1 with
          | leaf w =>
            have hle2 : Tree.Le (Tree.leaf w) (.leaf (.err b)) :=
              hdv ▸ (mem_leafT.mp hd)
            cases hle2 with
            | bot => exact Or.inl rfl
            | leaf => exact Or.inr rfl
          | node i3 q3 f3 =>
            have hle2 : Tree.Le (Tree.node i3 q3 f3) (.leaf (.err b)) :=
              hdv ▸ (mem_leafT.mp hd)
            cases hle2
        rcases hdc with hdb | hde
        · rw [hdb, apply0_rootProbe_bot h0 f2]
          exact Tree.Le.bot _
        · rw [hde, apply0_rootProbe_err h0 f2 b]
          exact Tree.Le.refl _
  · intro hc
    refine ⟨⟨Tree.node ⟨0, h0⟩ .hole (fun _ => Tree.bot),
        TreeOk.node _ _ _ _ LegalQuery.root ⟨[], fun r hr => absurd rfl hr⟩
          (fun r _ => TreeOk.leaf _ _) (fun r _ => rfl)⟩,
      ?_, ⟨.leaf (.err b), TreeOk.leaf _ _⟩, mem_leafT.mpr (Tree.Le.refl _), ?_⟩
    · exact Tree.Le.node _ _ _ _ fun r => Tree.Le.bot _
    · show Tree.Le c.1 (apply0 (Tree.node ⟨0, h0⟩ .hole
        (fun _ => Tree.bot)) (.leaf (.err b)))
      rw [apply0_rootProbe_err h0 _ b]
      exact mem_leafT.mp hc

/-! ## Abstraction of a leaf-valued body -/

/-- The abstraction algorithm produces well-typed terms (moved here from the
§6 development). -/
theorem Comb.lamStars_hasTy {L : Lang} : ∀ (l : List (Nat × Ty)) (Γ : List (Nat × Ty))
    (P : Comb L) (ρ : Ty), Comb.HasTy (l ++ Γ) P ρ →
    Comb.HasTy Γ (Comb.lamStars l P) (l.foldr (fun p τ => p.2 ⇒ τ) ρ)
  | [], _, _, _, h => h
  | (x, σ) :: l, Γ, P, ρ, h => by
      show Comb.HasTy Γ (Comb.lamStar x σ (Comb.lamStars l P)) _
      refine Comb.lamStar_hasTy (Comb.lamStars_hasTy l ((x, σ) :: Γ) P ρ ?_)
      refine Comb.weaken (fun p hp => ?_) h
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with (hp | hp) | hp
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)

/-- **Typing inversion for the abstraction algorithm**: `λ*y.P` has only types
of the form `σ ⇒ ρ`, with the body typed in the extended context. -/
theorem Comb.lamStar_hasTy_inv {L : Lang} (y : Nat) (σ : Ty) :
    ∀ (P : Comb L) (Γ : List (Nat × Ty)) (μ : Ty),
    Comb.HasTy Γ (Comb.lamStar y σ P) μ →
    ∃ ρ, μ = (σ ⇒ ρ) ∧ Comb.HasTy ((y, σ) :: Γ) P ρ
  | .var z ν, Γ, μ, h => by
      by_cases hz : z = y ∧ ν = σ
      · obtain ⟨rfl, rfl⟩ := hz
        rw [show Comb.lamStar z ν (Comb.var z ν : Comb L) = .I ν by
          simp [Comb.lamStar]] at h
        cases h with
        | I => exact ⟨ν, rfl, Comb.HasTy.var (List.mem_cons_self ..)⟩
      · rw [show Comb.lamStar y σ (Comb.var z ν : Comb L)
            = .app (.K ν σ) (.var z ν) by
          simp only [Comb.lamStar, if_neg hz]] at h
        cases h with
        | app hK hv =>
          cases hv with
          | var hmem =>
            cases hK with
            | K => exact ⟨ν, rfl, Comb.HasTy.var (List.mem_cons_of_mem _ hmem)⟩
  | .const c, Γ, μ, h => by
      cases h with
      | app hK hv =>
        cases hv with
        | const =>
          cases hK with
          | K => exact ⟨L.constTy c, rfl, Comb.HasTy.const⟩
  | .S a b c, Γ, μ, h => by
      cases h with
      | app hK hv =>
        cases hv with
        | S =>
          cases hK with
          | K => exact ⟨_, rfl, Comb.HasTy.S⟩
  | .K a b, Γ, μ, h => by
      cases h with
      | app hK hv =>
        cases hv with
        | K =>
          cases hK with
          | K => exact ⟨_, rfl, Comb.HasTy.K⟩
  | .I a, Γ, μ, h => by
      cases h with
      | app hK hv =>
        cases hv with
        | I =>
          cases hK with
          | K => exact ⟨_, rfl, Comb.HasTy.I⟩
  | .app M N, Γ, μ, h => by
      cases h with
      | app h1 h2 =>
        cases h1 with
        | app hS hM =>
          cases hS with
          | S =>
            obtain ⟨ρM, hρM, hM'⟩ := Comb.lamStar_hasTy_inv y σ M Γ _ hM
            obtain ⟨ρN, hρN, hN'⟩ := Comb.lamStar_hasTy_inv y σ N Γ _ h2
            have h1' : ρM = (Comb.tyOf N ⇒ Comb.tyOf (Comb.app M N)) := by
              injection hρM with _ h
              exact h.symm
            have h2' : ρN = Comb.tyOf N := by
              injection hρN with _ h
              exact h.symm
            subst h1' h2'
            exact ⟨_, rfl, Comb.HasTy.app hM' hN'⟩

/-- Iterated typing inversion for `λ*`. -/
theorem Comb.lamStars_hasTy_inv {L : Lang} :
    ∀ (xs : List (Nat × Ty)) (Γ : List (Nat × Ty)) (P : Comb L) (μ : Ty),
    Comb.HasTy Γ (Comb.lamStars xs P) μ →
    ∃ ρ, μ = xs.foldr (fun p τ => p.2 ⇒ τ) ρ ∧ Comb.HasTy (xs ++ Γ) P ρ
  | [], Γ, P, μ, h => ⟨μ, rfl, h⟩
  | (x, σ) :: xs, Γ, P, μ, h => by
      obtain ⟨ρ₁, rfl, h₁⟩ :=
        Comb.lamStar_hasTy_inv x σ (Comb.lamStars xs P) Γ μ h
      obtain ⟨ρ, rfl, h₂⟩ := Comb.lamStars_hasTy_inv xs ((x, σ) :: Γ) P ρ₁ h₁
      refine ⟨ρ, rfl, Comb.weaken (fun p hp => ?_) h₂⟩
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with hp | hp | hp
      · exact Or.inl (Or.inr hp)
      · exact Or.inl (Or.inl hp)
      · exact Or.inr hp

/-- Abstracting a body that denotes a leaf denotes that leaf: the constant
function `λ*y.v` is `v` itself. -/
theorem lamStar_meaning_leaf (Env : Tmodel.Env) (y : Nat) (σ : Ty) (P : Comb SPCF)
    (ρ : Ty) (Γ : List (Nat × Ty)) (hty : Comb.HasTy ((y, σ) :: Γ) P ρ) (v : Val)
    (h : ∀ x : T σ, Tmodel.combMeaning (Model.envUpdate Env y σ x) P ρ = leafT ρ v) :
    Tmodel.combMeaning Env (Comb.lamStar y σ P) (σ ⇒ ρ) = leafT (σ ⇒ ρ) v := by
  refine Po.le_antisymm (orderExtensional_T _ _ fun x => ?_)
    (orderExtensional_T _ _ fun x => ?_)
  · rw [lamStar_apply Env y σ x P ρ Γ hty, h x, applyT_leafT]
    exact Po.le_refl _
  · rw [lamStar_apply Env y σ x P ρ Γ hty, h x, applyT_leafT]
    exact Po.le_refl _

/-- Iterated leaf abstraction: if the body denotes the leaf `v` under every
environment that reassigns only the abstracted variables, so does the whole
procedure. -/
theorem lamStars_meaning_leaf : ∀ (xs : List (Nat × Ty)) (Env : Tmodel.Env)
    (P : Comb SPCF) (ρ : Ty) (Γ : List (Nat × Ty)),
    Comb.HasTy (xs ++ Γ) P ρ → ∀ (v : Val),
    (∀ Env' : Tmodel.Env,
      (∀ p : Nat × Ty, ¬ p ∈ xs → Env' p.1 p.2 = Env p.1 p.2) →
      Tmodel.combMeaning Env' P ρ = leafT ρ v) →
    Tmodel.combMeaning Env (Comb.lamStars xs P)
      (xs.foldr (fun p τ => p.2 ⇒ τ) ρ) = leafT _ v
  | [], Env, P, ρ, Γ, hty, v, h => h Env (fun _ _ => rfl)
  | (x, σ) :: xs, Env, P, ρ, Γ, hty, v, h => by
      show Tmodel.combMeaning Env (Comb.lamStar x σ (Comb.lamStars xs P)) _ = _
      have htyIn : Comb.HasTy (xs ++ (x, σ) :: Γ) P ρ := by
        refine Comb.weaken (fun p hp => ?_) hty
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        rcases hp with (hp | hp) | hp
        · exact Or.inr (Or.inl hp)
        · exact Or.inl hp
        · exact Or.inr (Or.inr hp)
      refine lamStar_meaning_leaf Env x σ (Comb.lamStars xs P) _ Γ
        (Comb.lamStars_hasTy xs ((x, σ) :: Γ) P ρ htyIn) v (fun d => ?_)
      refine lamStars_meaning_leaf xs (Model.envUpdate Env x σ d) P ρ
        ((x, σ) :: Γ) htyIn v (fun Env' hEnv' => ?_)
      refine h Env' (fun p hp => ?_)
      simp only [List.mem_cons] at hp
      have hp1 : ¬ p = (x, σ) := fun he => hp (Or.inl he)
      have hp2 : ¬ p ∈ xs := fun he => hp (Or.inr he)
      rw [hEnv' p hp2, Model.envUpdate_other]
      intro ⟨he1, he2⟩
      exact hp1 (by cases p; simp_all)

/-! ## Evaluation contexts propagate a leaf-valued hole -/

/-- The binders an evaluation context wraps around its hole. -/
def EvalCtx.Binds : EvalCtx → (Nat × Ty) → Prop
  | .hole, _ => False
  | .primApp _ E, p => E.Binds p
  | .appL E _, p => E.Binds p
  | .catchLam _ xs E, p => p ∈ xs ∨ E.Binds p

/-- **Evaluation contexts propagate a leaf-valued hole** — the master lemma
behind the `(error)` and `(bottom)` clauses of Theorem 4.27.  The hole's
meaning is assumed to be the leaf under every environment that reassigns only
variables bound by the context around its hole. -/
theorem EvalCtx.fill_leaf (v : Val) (hv : v = Val.bot ∨ ∃ b, v = Val.err b) :
    ∀ (E : EvalCtx) (Γ : List (Nat × Ty)) (Env : Tmodel.Env) (M : Comb SPCF)
      (ν ρ : Ty),
    Comb.HasTy Γ (E.fill M) ρ → Comb.HasTy Γ M ν →
    (∀ Env' : Tmodel.Env,
      (∀ p : Nat × Ty, ¬ E.Binds p → Env' p.1 p.2 = Env p.1 p.2) →
      Tmodel.combMeaning Env' M ν = leafT ν v) →
    Tmodel.combMeaning Env (E.fill M) ρ = leafT ρ v
  | .hole, Γ, Env, M, ν, ρ, h, hM, hleaf => by
      have h1 : Comb.tyOf M = ρ := Comb.tyOf_of_hasTy h
      have h2 : Comb.tyOf M = ν := Comb.tyOf_of_hasTy hM
      have hνρ : ν = ρ := h2 ▸ h1
      subst hνρ
      exact hleaf Env (fun _ _ => rfl)
  | .primApp f E', Γ, Env, M, ν, ρ, h, hM, hleaf => by
      cases h with
      | app hf hi =>
        rename_i α
        have hα : Comb.tyOf (E'.fill M) = α := Comb.tyOf_of_hasTy hi
        rw [show (EvalCtx.primApp f E').fill M = .app f.toComb (E'.fill M) from rfl,
          Model.combMeaning_app, hα]
        have hIH : Tmodel.combMeaning Env (E'.fill M) α = leafT α v :=
          EvalCtx.fill_leaf v hv E' Γ Env M ν α hi hM hleaf
        rw [hIH]
        cases f with
        | add1 =>
          have hty : (𝕆 ⇒ 𝕆 : Ty) = (α ⇒ ρ) := Comb.tyOf_of_hasTy hf
          injection hty with hty1 hty2
          subst hty1 hty2
          have hm : Tmodel.combMeaning Env (Comb.const SConst.add1 : Comb SPCF)
              (𝕆 ⇒ 𝕆) = Tmodel.interpConst SConst.add1 :=
            Model.combMeaning_const Tmodel Env SConst.add1
          rw [show PrimF.toComb .add1 = (Comb.const SConst.add1 : Comb SPCF)
            from rfl, hm,
            show Tmodel.interpConst SConst.add1 = idealOf treeAdd1 from rfl]
          rcases hv with rfl | ⟨b, rfl⟩
          · exact applyT_rootProbe_bot (Nat.succ_pos _) _
          · exact applyT_rootProbe_err (Nat.succ_pos _) _ b
        | sub1 =>
          have hty : (𝕆 ⇒ 𝕆 : Ty) = (α ⇒ ρ) := Comb.tyOf_of_hasTy hf
          injection hty with hty1 hty2
          subst hty1 hty2
          have hm : Tmodel.combMeaning Env (Comb.const SConst.sub1 : Comb SPCF)
              (𝕆 ⇒ 𝕆) = Tmodel.interpConst SConst.sub1 :=
            Model.combMeaning_const Tmodel Env SConst.sub1
          rw [show PrimF.toComb .sub1 = (Comb.const SConst.sub1 : Comb SPCF)
            from rfl, hm,
            show Tmodel.interpConst SConst.sub1 = idealOf treeSub1 from rfl]
          rcases hv with rfl | ⟨b, rfl⟩
          · exact applyT_rootProbe_bot (Nat.succ_pos _) _
          · exact applyT_rootProbe_err (Nat.succ_pos _) _ b
        | if0 =>
          have hty : (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆 : Ty) = (α ⇒ ρ) := Comb.tyOf_of_hasTy hf
          injection hty with hty1 hty2
          subst hty1 hty2
          have hm : Tmodel.combMeaning Env (Comb.const SConst.if0 : Comb SPCF)
              (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆) = Tmodel.interpConst SConst.if0 :=
            Model.combMeaning_const Tmodel Env SConst.if0
          rw [show PrimF.toComb .if0 = (Comb.const SConst.if0 : Comb SPCF)
            from rfl, hm,
            show Tmodel.interpConst SConst.if0 = idealOf treeIf0 from rfl]
          rcases hv with rfl | ⟨b, rfl⟩
          · exact applyT_rootProbe_bot (Nat.succ_pos _) _
          · exact applyT_rootProbe_err (Nat.succ_pos _) _ b
        | catchF σ' =>
          have hty : (σ' ⇒ 𝕆 : Ty) = (α ⇒ ρ) := Comb.tyOf_of_hasTy hf
          injection hty with hty1 hty2
          subst hty1 hty2
          have hm : Tmodel.combMeaning Env
              (Comb.const (SConst.catchC σ') : Comb SPCF)
              (σ' ⇒ 𝕆) = Tmodel.interpConst (SConst.catchC σ') :=
            Model.combMeaning_const Tmodel Env (SConst.catchC σ')
          rw [show PrimF.toComb (.catchF σ')
              = (Comb.const (SConst.catchC σ') : Comb SPCF) from rfl, hm,
            show Tmodel.interpConst (SConst.catchC σ') = idealOf (treeCatch σ')
              from rfl]
          rcases hv with rfl | ⟨b, rfl⟩
          · exact applyT_rootProbe_bot (Nat.succ_pos _) _
          · exact applyT_rootProbe_err (Nat.succ_pos _) _ b
  | .appL E' N, Γ, Env, M, ν, ρ, h, hM, hleaf => by
      cases h with
      | app hi hN =>
        rename_i α
        have hα : Comb.tyOf N = α := Comb.tyOf_of_hasTy hN
        rw [show (EvalCtx.appL E' N).fill M = .app (E'.fill M) N from rfl,
          Model.combMeaning_app, hα]
        have hIH : Tmodel.combMeaning Env (E'.fill M) (α ⇒ ρ) = leafT (α ⇒ ρ) v :=
          EvalCtx.fill_leaf v hv E' Γ Env M ν (α ⇒ ρ) hi hM hleaf
        rw [hIH]
        exact applyT_leafT v _
  | .catchLam σ' xs' E', Γ, Env, M, ν, ρ, h, hM, hleaf => by
      cases h with
      | app hc hl =>
        rename_i α
        have hty : (σ' ⇒ 𝕆 : Ty) = (α ⇒ ρ) := Comb.tyOf_of_hasTy hc
        injection hty with hty1 hty2
        subst hty1 hty2
        obtain ⟨ρ', rfl, hinner⟩ := Comb.lamStars_hasTy_inv xs' Γ (E'.fill M) _ hl
        have hα : Comb.tyOf (Comb.lamStars xs' (E'.fill M))
            = xs'.foldr (fun p τ => p.2 ⇒ τ) ρ' := Comb.tyOf_of_hasTy hl
        rw [show (EvalCtx.catchLam (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ') xs' E').fill M
            = .app (.const (.catchC (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ')))
                (Comb.lamStars xs' (E'.fill M)) from rfl,
          Model.combMeaning_app, hα]
        have hm : Tmodel.combMeaning Env
            (Comb.const (SConst.catchC (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ'))
              : Comb SPCF)
            ((xs'.foldr (fun p τ => p.2 ⇒ τ) ρ') ⇒ 𝕆)
            = Tmodel.interpConst
                (SConst.catchC (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ')) :=
          Model.combMeaning_const Tmodel Env _
        rw [hm, show Tmodel.interpConst
            (SConst.catchC (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ'))
            = idealOf (treeCatch (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ')) from rfl]
        have hΛ : Tmodel.combMeaning Env (Comb.lamStars xs' (E'.fill M))
            (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ')
            = leafT (xs'.foldr (fun p τ => p.2 ⇒ τ) ρ') v := by
          refine lamStars_meaning_leaf xs' Env (E'.fill M) ρ' Γ hinner v
            (fun Env'' hEnv'' => ?_)
          refine EvalCtx.fill_leaf v hv E' (xs' ++ Γ) Env'' M ν ρ' hinner
            (Comb.weaken (fun p hp => List.mem_append.mpr (Or.inr hp)) hM)
            (fun Env''' hEnv''' => ?_)
          refine hleaf Env''' (fun p hp => ?_)
          have hp1 : ¬ p ∈ xs' := fun he =>
            hp (show (EvalCtx.catchLam _ xs' E').Binds p from Or.inl he)
          have hp2 : ¬ E'.Binds p := fun he =>
            hp (show (EvalCtx.catchLam _ xs' E').Binds p from Or.inr he)
          rw [hEnv''' p hp2, hEnv'' p hp1]
        rw [hΛ]
        rcases hv with rfl | ⟨b, rfl⟩
        · exact applyT_rootProbe_bot (Nat.succ_pos _) _
        · exact applyT_rootProbe_err (Nat.succ_pos _) _ b

/-- **Lemma B.1.**  *For all variables `x₁, …, xₙ`, for all evaluation contexts
`E`, and for all `1 ≤ j ≤ n`,*
`T[[λ* x₁ … xₙ . E[xⱼ]]] = ⟨j, ?, f⟩` *for an appropriate branching function
`f`.*

That is: a procedure whose body places the variable `xⱼ` in the hole of an
evaluation context probes its `j`-th argument first, with the initial query
`?`. -/
theorem lemma_B_1 (l : List Ty) (E : EvalCtx) (j : Fin l.length)
    (Env : Tmodel.Env) :
    ∃ (f : Resp ((l.foldr Ty.arrow 𝕆).arg (finOf l j)) → Tree (l.foldr Ty.arrow 𝕆))
      (d : D (l.foldr Ty.arrow 𝕆)),
      d.1 = .node (finOf l j) .hole f ∧
      Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (l.foldr Ty.arrow 𝕆) = Ideal.principal d := by
  sorry

/-- **Lemma 4.26.**  *For all variables `x₁, …, xₙ`, for all evaluation contexts
`E`, and for all `j`, `1 ≤ j ≤ n`, `T[[λ* x₁ … xₙ . E[xⱼ]]] = ⟨j, ?, f⟩` for
some appropriate branching function `f`.*

"Proof.  See Appendix B." -/
theorem lemma_4_26 (l : List Ty) (E : EvalCtx) (j : Fin l.length) (Env : Tmodel.Env) :
    ∃ (f : Resp ((l.foldr Ty.arrow 𝕆).arg (finOf l j)) → Tree (l.foldr Ty.arrow 𝕆))
      (d : D (l.foldr Ty.arrow 𝕆)),
      d.1 = .node (finOf l j) .hole f ∧
      Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (l.foldr Ty.arrow 𝕆) = Ideal.principal d :=
  lemma_B_1 l E j Env

/-- `errorᵢ` as an element of `T_o`. -/
noncomputable def errAns (b : Bool) : T 𝕆 :=
  Ideal.principal ⟨.leaf (.err b), TreeOk.leaf _ _⟩

/-- **Theorem 4.27.**  *For all evaluation contexts `E`, types
`σ = σ₁ → … → σₙ`, and variables `x₁, …, xₙ`:*

```
T[[E[errorⱼ]]]                            = errorⱼ           (error)
T[[E[⊥]]]                                 = ⊥                (bottom)
T[[apply (catch_σ, λ* x₁ … xₙ . E[xⱼ])]]  = ⌜j−1⌝            (catch), 1 ≤ j ≤ n
T[[apply (catch_σ, λ* x₁ … xₙ . ⌜k⌝)]]    = ⌜k+n⌝            (return)
```
-/
theorem theorem_4_27 :
    -- (error)
    (∀ (E : EvalCtx) (b : Bool) (Env : Tmodel.Env),
      Tmodel.combMeaning Env (E.fill (.const (.err b))) 𝕆 = errAns b) ∧
    -- (bottom)
    (∀ (E : EvalCtx) (Env : Tmodel.Env),
      Tmodel.combMeaning Env (E.fill (Omega 𝕆)) 𝕆
        = Ideal.principal (DSub.bot : D 𝕆)) ∧
    -- (catch)
    (∀ (l : List Ty) (E : EvalCtx) (j : Fin l.length) (Env : Tmodel.Env),
      Tmodel.combMeaning Env
        (.app (.const (.catchC (l.foldr Ty.arrow 𝕆)))
          (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))) 𝕆
        = natAns j.val) ∧
    -- (return)
    (∀ (l : List Ty) (k : Nat) (Env : Tmodel.Env),
      Tmodel.combMeaning Env
        (.app (.const (.catchC (l.foldr Ty.arrow 𝕆)))
          (Comb.lamStars (varsOf l) (.const (.num k)))) 𝕆
        = natAns (k + l.length)) := by
  sorry

end FA
