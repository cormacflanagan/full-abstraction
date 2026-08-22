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

/-- Every index is listed by `finRange`. -/
theorem finRange_mem : ∀ (n : Nat) (i : Fin n), i ∈ List.finRange n
  | 0, i => absurd i.isLt (by omega)
  | n + 1, i => by
      rw [List.finRange_succ]
      refine Fin.cases ?_ (fun i' => ?_) i
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨i', finRange_mem n i', rfl⟩)

/-- Membership of the `j`-th variable in `varsOf l`. -/
theorem mem_varsOf (l : List Ty) (j : Fin l.length) :
    (j.val, l[j.val]'j.isLt) ∈ varsOf l := by
  simp only [varsOf, List.mem_map]
  exact ⟨j, finRange_mem _ j, rfl⟩

/-! ## Name-indexed application chains

The analysis of `T[[λ* x₁ … xₙ . E[xⱼ]]]` applies the abstraction to one
argument per abstracted variable.  The chains are indexed by the variable
list itself. -/

/-- `(varsOf l).length = l.length`. -/
theorem varsOf_length (l : List Ty) : (varsOf l).length = l.length := by
  simp [varsOf]

/-- The `i`-th entry of `varsOf l`. -/
theorem varsOf_getElem (l : List Ty) (i : Nat) (h : i < (varsOf l).length) :
    (varsOf l)[i] = (i, l[i]'(by rw [varsOf_length] at h; exact h)) := by
  simp only [varsOf, List.getElem_map, List.getElem_finRange]
  rfl

/-- The uncurried type of a variable list, versus its type list. -/
theorem foldr_pair (xs : List (Nat × Ty)) :
    xs.foldr (fun p τ => p.2 ⇒ τ) 𝕆 = (xs.map Prod.snd).foldr Ty.arrow 𝕆 := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simp [List.foldr_cons, ih]

/-- The types listed by `varsOf l` are `l`. -/
theorem varsOf_snd (l : List Ty) : (varsOf l).map Prod.snd = l := by
  have h : ∀ (n : Nat) (l' : List Ty) (hn : n = l'.length),
      (List.finRange n).map (fun i => l'[i.val]'(hn ▸ i.isLt)) = l' := by
    intro n
    induction n with
    | zero =>
      intro l' hn
      cases l' with
      | nil => rfl
      | cons a l' => exact absurd hn (by simp)
    | succ n ih =>
      intro l' hn
      cases l' with
      | nil => exact absurd hn (by simp)
      | cons a l' =>
        rw [List.finRange_succ, List.map_cons, List.map_map]
        exact congrArg (a :: ·) (ih l' (by simpa using hn))
  simp only [varsOf, List.map_map]
  exact h l.length l rfl

/-- `foldr` over `varsOf l` is `foldr` over `l`. -/
theorem varsOf_foldr (l : List Ty) :
    (varsOf l).foldr (fun p τ => p.2 ⇒ τ) 𝕆 = l.foldr Ty.arrow 𝕆 := by
  rw [foldr_pair, varsOf_snd]

/-- The uncurried type of a variable list. -/
abbrev foldX (xs : List (Nat × Ty)) : Ty := xs.foldr (fun p τ => p.2 ⇒ τ) 𝕆

/-- The arity of the uncurried type of a variable list. -/
theorem arity_foldrX : ∀ xs : List (Nat × Ty), (foldX xs).arity = xs.length
  | [] => rfl
  | p :: xs => by
      show (foldX xs).arity + 1 = xs.length + 1
      rw [arity_foldrX xs]

/-- `apply (t, d₁, …, dₙ)` on finite trees, indexed by a variable list. -/
noncomputable def apply0ChainF : ∀ (xs : List (Nat × Ty)),
    Tree (foldX xs) →
    ((i : Fin xs.length) → Tree ((xs[i.1]'i.isLt).2)) → Tree 𝕆
  | [], t, _ => t
  | _ :: xs, t, ds =>
      apply0ChainF xs (apply0 t (ds ⟨0, Nat.succ_pos _⟩)) (fun i => ds i.succ)

/-- `apply (Λ, D₁, …, Dₙ)` on ideals, with name-indexed argument families. -/
noncomputable def applyTChainX : ∀ (xs : List (Nat × Ty)),
    T (foldX xs) → (∀ p : Nat × Ty, T p.2) → T 𝕆
  | [], t, _ => t
  | p :: xs, t, vs => applyTChainX xs (applyT t (vs p)) vs

/-- A leaf passes through the chain unchanged. -/
theorem apply0ChainF_leaf : ∀ (xs : List (Nat × Ty)) (v : Val)
    (ds : (i : Fin xs.length) → Tree ((xs[i]).2)),
    apply0ChainF xs (.leaf v) ds = .leaf v
  | [], _, _ => rfl
  | p :: xs, v, ds => by
      show apply0ChainF xs (apply0 (.leaf v) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      exact apply0ChainF_leaf xs v _

/-- The chain is monotone in the tree. -/
theorem apply0ChainF_mono : ∀ (xs : List (Nat × Ty))
    {t t' : Tree (foldX xs)}, Tree.Le t t' →
    ∀ (ds : (i : Fin xs.length) → Tree ((xs[i]).2)),
    Tree.Le (apply0ChainF xs t ds) (apply0ChainF xs t' ds)
  | [], t, t', h, _ => h
  | p :: xs, t, t', h, ds =>
      apply0ChainF_mono xs (apply0_mono_left h _) (fun i => ds i.succ)

/-- A root probe of an argument that is `⊥` collapses the chain to `⊥`. -/
theorem apply0ChainF_bot : ∀ (xs : List (Nat × Ty)) (n : Nat)
    (hn : n < xs.length)
    (hn' : n < (foldX xs).arity)
    (f : Resp ((foldX xs).arg ⟨n, hn'⟩) → Tree (foldX xs))
    (ds : (i : Fin xs.length) → Tree ((xs[i]).2)),
    ds ⟨n, hn⟩ = Tree.bot →
    apply0ChainF xs (Tree.node ⟨n, hn'⟩ .hole f) ds = Tree.bot
  | [], n, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | p :: xs, 0, hn, hn', f, ds, hds => by
      show apply0ChainF xs
        (apply0 (Tree.node ⟨0, hn'⟩ .hole f) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      rw [hds, apply0_rootProbe_bot hn' f]
      exact apply0ChainF_leaf xs .bot _
  | p :: xs, n + 1, hn, hn', f, ds, hds => by
      show apply0ChainF xs
        (apply0 (Tree.node ⟨n + 1, hn'⟩ .hole f) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      rw [show apply0 (Tree.node ⟨n + 1, hn'⟩ .hole f) (ds ⟨0, Nat.succ_pos _⟩)
          = Tree.node ⟨n, Nat.lt_of_succ_lt_succ hn'⟩ .hole
              (fun r => apply0 (f r) (ds ⟨0, Nat.succ_pos _⟩)) from by
        rw [apply0]]
      exact apply0ChainF_bot xs n (Nat.lt_of_succ_lt_succ hn) _ _
        (fun i => ds i.succ) hds

/-- Extraction of a chain member: it is bounded by one finite computation. -/
theorem applyTChainX_mem : ∀ (xs : List (Nat × Ty))
    (Λ : T (foldX xs)) (vs : ∀ p : Nat × Ty, T p.2)
    (c : D 𝕆), c ∈ applyTChainX xs Λ vs →
    ∃ s : D (foldX xs), s ∈ Λ ∧
      ∃ ds : (i : Fin xs.length) → D ((xs[i.1]'i.isLt).2),
        (∀ i, ds i ∈ vs (xs[i.1]'i.isLt)) ∧
        Tree.Le c.1 (apply0ChainF xs s.1 (fun i => (ds i).1))
  | [], Λ, vs, c, hc => ⟨c, hc, fun i => absurd i.isLt (Nat.not_lt_zero _),
      fun i => absurd i.isLt (Nat.not_lt_zero _), Tree.Le.refl _⟩
  | p :: xs, Λ, vs, c, hc => by
      obtain ⟨s', hs', ds', hds', hle'⟩ := applyTChainX_mem xs _ vs c hc
      obtain ⟨s, hs, d0, hd0, hsd⟩ := hs'
      refine ⟨s, hs, Fin.cases d0 ds', fun i => ?_, ?_⟩
      · refine Fin.cases ?_ (fun i' => ?_) i
        · exact hd0
        · exact hds' i'
      · show Tree.Le c.1 (apply0ChainF xs (apply0 s.1 d0.1) _)
        refine Tree.Le.trans hle' (apply0ChainF_mono xs ?_ _)
        exact (hsd : Tree.Le s'.1 (apply0 s.1 d0.1))

/-- Introduction of a chain member from one finite computation. -/
theorem applyTChainX_intro : ∀ (xs : List (Nat × Ty))
    (Λ : T (foldX xs)) (vs : ∀ p : Nat × Ty, T p.2)
    (s : D (foldX xs)), s ∈ Λ →
    ∀ ds : (i : Fin xs.length) → D ((xs[i.1]'i.isLt).2), (∀ i, ds i ∈ vs (xs[i.1]'i.isLt)) →
    ∀ c : D 𝕆, Tree.Le c.1 (apply0ChainF xs s.1 (fun i => (ds i).1)) →
    c ∈ applyTChainX xs Λ vs
  | [], Λ, vs, s, hs, ds, hds, c, hc => Λ.downward c s hc hs
  | p :: xs, Λ, vs, s, hs, ds, hds, c, hc => by
      refine applyTChainX_intro xs (applyT Λ (vs p)) vs (applyD s (ds ⟨0, Nat.succ_pos _⟩))
        ⟨s, hs, ds ⟨0, Nat.succ_pos _⟩, hds ⟨0, Nat.succ_pos _⟩, Po.le_refl _⟩
        (fun i => ds i.succ) (fun i => hds i.succ) c hc

/-- Iterated environment update along a variable list. -/
noncomputable def updEnvX : List (Nat × Ty) → Tmodel.Env → (∀ p : Nat × Ty, T p.2)
    → Tmodel.Env
  | [], Env, _ => Env
  | p :: xs, Env, vs => updEnvX xs (Model.envUpdate Env p.1 p.2 (vs p)) vs

/-- The updated environment agrees with the original off the listed keys. -/
theorem updEnvX_other : ∀ (xs : List (Nat × Ty)) (Env : Tmodel.Env)
    (vs : ∀ p : Nat × Ty, T p.2) (x : Nat) (ν : Ty),
    (∀ q ∈ xs, ¬ (x = q.1 ∧ ν = q.2)) → updEnvX xs Env vs x ν = Env x ν
  | [], _, _, _, _, _ => rfl
  | q :: xs, Env, vs, x, ν, h => by
      show updEnvX xs (Model.envUpdate Env q.1 q.2 (vs q)) vs x ν = _
      rw [updEnvX_other xs _ vs x ν (fun r hr => h r (List.mem_cons_of_mem _ hr)),
        Model.envUpdate_other _ _ _ _ _ _ (h q (List.mem_cons_self ..))]

/-- The updated environment assigns each listed variable its value. -/
theorem updEnvX_lookup : ∀ (xs : List (Nat × Ty)) (Env : Tmodel.Env)
    (vs : ∀ p : Nat × Ty, T p.2) (p : Nat × Ty), p ∈ xs →
    updEnvX xs Env vs p.1 p.2 = vs p
  | [], _, _, p, hp => absurd hp (by simp)
  | q :: xs, Env, vs, p, hp => by
      show updEnvX xs (Model.envUpdate Env q.1 q.2 (vs q)) vs p.1 p.2 = _
      by_cases hpx : p ∈ xs
      · exact updEnvX_lookup xs _ vs p hpx
      · have hpq : p = q := by
          rcases List.mem_cons.mp hp with h | h
          · exact h
          · exact absurd h hpx
        subst hpq
        rw [updEnvX_other xs _ vs p.1 p.2 (fun r hr hcon => ?_),
          Model.envUpdate_self]
        exact hpx (show p ∈ xs from by
          have : p = r := Prod.ext hcon.1 hcon.2
          rw [this]; exact hr)

/-- Peeling the abstraction: applying `λ* xs . P` to one argument per
variable computes `P` in the updated environment. -/
theorem lamStars_peel : ∀ (xs : List (Nat × Ty)) (Env : Tmodel.Env)
    (P : Comb SPCF) (Γ : List (Nat × Ty)), Comb.HasTy (xs ++ Γ) P 𝕆 →
    ∀ vs : (∀ p : Nat × Ty, T p.2),
    applyTChainX xs (Tmodel.combMeaning Env (Comb.lamStars xs P)
      (foldX xs)) vs
      = Tmodel.combMeaning (updEnvX xs Env vs) P 𝕆
  | [], Env, P, Γ, hty, vs => rfl
  | (x, σ) :: xs, Env, P, Γ, hty, vs => by
      have htyIn : Comb.HasTy (xs ++ (x, σ) :: Γ) P 𝕆 := by
        refine Comb.weaken (fun p hp => ?_) hty
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        rcases hp with (hp | hp) | hp
        · exact Or.inr (Or.inl hp)
        · exact Or.inl hp
        · exact Or.inr (Or.inr hp)
      show applyTChainX xs (applyT (Tmodel.combMeaning Env
        (Comb.lamStar x σ (Comb.lamStars xs P)) _) (vs (x, σ))) vs = _
      rw [lamStar_apply Env x σ (vs (x, σ)) (Comb.lamStars xs P) _ Γ
        (Comb.lamStars_hasTy xs ((x, σ) :: Γ) P 𝕆 htyIn)]
      exact lamStars_peel xs (Model.envUpdate Env x σ (vs (x, σ))) P
        ((x, σ) :: Γ) htyIn vs

/-- The all-`⊥` argument family. -/
noncomputable def vsBot : ∀ p : Nat × Ty, T p.2 := fun p => leafT p.2 .bot

/-- The argument family that is `error₁` at one variable and `⊥` elsewhere. -/
noncomputable def vsErr (x : Nat) (ν : Ty) : ∀ p : Nat × Ty, T p.2 := fun p =>
  if p = (x, ν) then leafT p.2 (.err true) else leafT p.2 .bot

/-- The abstraction `T[[λ* x₁ … xₙ . E[xⱼ]]]`, as an ideal. -/
noncomputable def ctxAbs (l : List Ty) (E : EvalCtx) (j : Fin l.length)
    (Env : Tmodel.Env) : T (foldX (varsOf l)) :=
  Tmodel.combMeaning Env
    (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
    (foldX (varsOf l))

/-- **Lemma B.1.**  *For all variables `x₁, …, xₙ`, for all evaluation contexts
`E`, and for all `1 ≤ j ≤ n`,*
`T[[λ* x₁ … xₙ . E[xⱼ]]] = ⟨j, ?, f⟩` *for an appropriate branching function
`f`.*

The tree `⟨j, ?, f⟩` is infinite (its continuation copies whatever computation
follows), so in the ideal completion the statement reads: the meaning has a
member with root `⟨j, ?⟩`, and every member is `⊥` or has that root.  The
hypotheses are the paper's conventions: the filled context is well typed, and
the context does not capture the variable in its hole. -/
theorem lemma_B_1 (l : List Ty) (E : EvalCtx) (j : Fin l.length)
    (Env : Tmodel.Env)
    (hty : Comb.HasTy (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))) 𝕆)
    (hfresh : ¬ E.Binds (j.val, l[j.val]'j.isLt)) :
    (∃ s : D (foldX (varsOf l)), s ∈ ctxAbs l E j Env ∧
      ∃ f, s.1 = Tree.node
        ⟨j.val, by rw [arity_foldrX, varsOf_length]; exact j.isLt⟩
        Query.hole f) ∧
    (∀ s : D (foldX (varsOf l)), s ∈ ctxAbs l E j Env →
      s.1 = Tree.bot ∨
      ∃ f, s.1 = Tree.node
        ⟨j.val, by rw [arity_foldrX, varsOf_length]; exact j.isLt⟩
        Query.hole f) := by
  classical
  have hj : j.val < (foldX (varsOf l)).arity := by
    rw [arity_foldrX, varsOf_length]; exact j.isLt
  have htyApp : Comb.HasTy (varsOf l ++ [])
      (E.fill (.var j.val (l[j.val]'j.isLt))) 𝕆 := by
    simpa using hty
  have hvar : Comb.HasTy (varsOf l)
      (Comb.var j.val (l[j.val]'j.isLt) : Comb SPCF) (l[j.val]'j.isLt) :=
    Comb.HasTy.var (mem_varsOf l j)
  have hrunB : applyTChainX (varsOf l) (ctxAbs l E j Env) vsBot
      = leafT 𝕆 .bot := by
    rw [show ctxAbs l E j Env = Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (foldX (varsOf l)) from rfl,
      lamStars_peel (varsOf l) Env _ [] htyApp vsBot]
    refine EvalCtx.fill_leaf Val.bot (Or.inl rfl) E (varsOf l) _ _
      (l[j.val]'j.isLt) 𝕆 hty hvar (fun Env' hEnv' => ?_)
    rw [Model.combMeaning_var,
      hEnv' (j.val, l[j.val]'j.isLt) hfresh,
      updEnvX_lookup (varsOf l) Env vsBot _ (mem_varsOf l j)]
    rfl
  have hrunE : applyTChainX (varsOf l) (ctxAbs l E j Env)
      (vsErr j.val (l[j.val]'j.isLt)) = leafT 𝕆 (.err true) := by
    rw [show ctxAbs l E j Env = Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (foldX (varsOf l)) from rfl,
      lamStars_peel (varsOf l) Env _ [] htyApp _]
    refine EvalCtx.fill_leaf (Val.err true) (Or.inr ⟨true, rfl⟩) E (varsOf l) _ _
      (l[j.val]'j.isLt) 𝕆 hty hvar (fun Env' hEnv' => ?_)
    rw [Model.combMeaning_var,
      hEnv' (j.val, l[j.val]'j.isLt) hfresh,
      updEnvX_lookup (varsOf l) Env _ _ (mem_varsOf l j)]
    show vsErr j.val (l[j.val]'j.isLt) (j.val, l[j.val]'j.isLt) = _
    rw [vsErr, if_pos rfl]
  have hnoleaf : ∀ (s : D (foldX (varsOf l))) (v : Val),
      s ∈ ctxAbs l E j Env → s.1 = .leaf v → v = Val.bot := by
    intro s v hs hsv
    refine Classical.byContradiction fun hv => ?_
    have hmem : (⟨.leaf v, TreeOk.leaf _ _⟩ : D 𝕆)
        ∈ applyTChainX (varsOf l) (ctxAbs l E j Env) vsBot := by
      refine applyTChainX_intro (varsOf l) _ vsBot s hs
        (fun i => DSub.bot) (fun i => mem_leafT.mpr (Tree.Le.bot _)) _ ?_
      rw [hsv, apply0ChainF_leaf]
      exact Tree.Le.refl _
    rw [hrunB] at hmem
    have hle : Tree.Le (.leaf v) (.leaf .bot) := mem_leafT.mp hmem
    cases hle with
    | bot => exact hv rfl
    | leaf => exact hv rfl
  have hmemE : (⟨.leaf (.err true), TreeOk.leaf _ _⟩ : D 𝕆)
      ∈ applyTChainX (varsOf l) (ctxAbs l E j Env)
        (vsErr j.val (l[j.val]'j.isLt)) := by
    rw [hrunE]
    exact mem_leafT.mpr (Tree.Le.refl _)
  obtain ⟨s₀, hs₀, ds₀, hds₀, hle₀⟩ := applyTChainX_mem (varsOf l) _ _ _ hmemE
  have hs₀node : ∃ f, s₀.1 = Tree.node ⟨j.val, hj⟩ Query.hole f := by
    cases hsv : s₀.1 with
    | leaf v =>
      rw [hsv, apply0ChainF_leaf] at hle₀
      cases hle₀ with
      | leaf => exact Val.noConfusion (hnoleaf s₀ _ hs₀ hsv)
    | node jt q f =>
      obtain ⟨jtv, hjtlt⟩ := jt
      have hq : q = Query.hole := root_query_hole (hsv ▸ s₀.2)
      subst hq
      by_cases hjt : jtv = j.val
      · subst hjt
        exact ⟨f, rfl⟩
      · have hjtlen : jtv < (varsOf l).length := by
          rw [← arity_foldrX (varsOf l)]
          exact hjtlt
        have hdsb : (ds₀ ⟨jtv, hjtlen⟩).1 = Tree.bot := by
          have hmem := hds₀ ⟨jtv, hjtlen⟩
          have hq1 : ((varsOf l)[jtv]'hjtlen).1 = jtv :=
            congrArg Prod.fst (varsOf_getElem l jtv hjtlen)
          have hvs : vsErr j.val (l[j.val]'j.isLt) ((varsOf l)[jtv]'hjtlen)
              = leafT ((varsOf l)[jtv]'hjtlen).2 .bot := by
            rw [vsErr, if_neg (fun he => hjt (hq1 ▸ congrArg Prod.fst he))]
          rw [hvs] at hmem
          exact Tree.eq_bot_of_le_bot (mem_leafT.mp hmem)
        rw [hsv, apply0ChainF_bot (varsOf l) jtv hjtlen hjtlt f _ hdsb] at hle₀
        cases hle₀
  refine ⟨⟨s₀, hs₀, hs₀node⟩, ?_⟩
  intro s hs
  cases hsv : s.1 with
  | leaf v =>
    have hvb := hnoleaf s v hs hsv
    subst hvb
    exact Or.inl rfl
  | node jt q f =>
    have hq : q = Query.hole := root_query_hole (hsv ▸ s.2)
    subst hq
    obtain ⟨f₀, hs₀v⟩ := hs₀node
    obtain ⟨u, hu, hsu, hs₀u⟩ := (ctxAbs l E j Env).directed' s s₀ hs hs₀
    have h1 : Tree.Le (Tree.node jt Query.hole f) u.1 :=
      hsv ▸ (hsu : Tree.Le s.1 u.1)
    have h2 : Tree.Le (Tree.node ⟨j.val, hj⟩ Query.hole f₀) u.1 :=
      hs₀v ▸ (hs₀u : Tree.Le s₀.1 u.1)
    obtain ⟨g, hg⟩ := Tree.eq_node_of_le h1
    obtain ⟨g₀, hg₀⟩ := Tree.eq_node_of_le h2
    rw [hg] at hg₀
    injection hg₀ with hjj _ _
    subst hjj
    exact Or.inr ⟨f, rfl⟩

/-- **Lemma 4.26** is Lemma B.1: "Proof.  See Appendix B." -/
theorem lemma_4_26 (l : List Ty) (E : EvalCtx) (j : Fin l.length)
    (Env : Tmodel.Env)
    (hty : Comb.HasTy (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))) 𝕆)
    (hfresh : ¬ E.Binds (j.val, l[j.val]'j.isLt)) :
    (∃ s : D (foldX (varsOf l)), s ∈ ctxAbs l E j Env ∧
      ∃ f, s.1 = Tree.node
        ⟨j.val, by rw [arity_foldrX, varsOf_length]; exact j.isLt⟩
        Query.hole f) ∧
    (∀ s : D (foldX (varsOf l)), s ∈ ctxAbs l E j Env →
      s.1 = Tree.bot ∨
      ∃ f, s.1 = Tree.node
        ⟨j.val, by rw [arity_foldrX, varsOf_length]; exact j.isLt⟩
        Query.hole f) :=
  lemma_B_1 l E j Env hty hfresh

/-- `errorᵢ` as an element of `T_o`. -/
noncomputable def errAns (b : Bool) : T 𝕆 :=
  Ideal.principal ⟨.leaf (.err b), TreeOk.leaf _ _⟩

/-- The `(error)` clause of Theorem 4.27. -/
theorem theorem_4_27_error (E : EvalCtx) (b : Bool) (Env : Tmodel.Env)
    (hty : Comb.HasTy [] (E.fill (.const (.err b))) 𝕆) :
    Tmodel.combMeaning Env (E.fill (.const (.err b))) 𝕆 = errAns b := by
  refine EvalCtx.fill_leaf (Val.err b) (Or.inr ⟨b, rfl⟩) E [] Env _ 𝕆 𝕆 hty
    Comb.HasTy.const (fun Env' _ => ?_)
  exact Model.combMeaning_const Tmodel Env' (SConst.err b)

/-- The `(bottom)` clause of Theorem 4.27. -/
theorem theorem_4_27_bottom (E : EvalCtx) (Env : Tmodel.Env)
    (hty : Comb.HasTy [] (E.fill (Omega 𝕆)) 𝕆) :
    Tmodel.combMeaning Env (E.fill (Omega 𝕆)) 𝕆
      = Ideal.principal (DSub.bot : D 𝕆) := by
  refine EvalCtx.fill_leaf Val.bot (Or.inl rfl) E [] Env _ 𝕆 𝕆 hty
    (hasTy_Omega 𝕆 []) (fun Env' _ => ?_)
  exact meaning_Omega _ rfl rfl 𝕆 Env'

/-- **Theorem 4.27.**  *For all evaluation contexts `E`, types
`σ = σ₁ → … → σₙ`, and variables `x₁, …, xₙ`:*

```
T[[E[errorⱼ]]]                            = errorⱼ           (error)
T[[E[⊥]]]                                 = ⊥                (bottom)
T[[apply (catch_σ, λ* x₁ … xₙ . E[xⱼ])]]  = ⌜j−1⌝            (catch), 1 ≤ j ≤ n
T[[apply (catch_σ, λ* x₁ … xₙ . ⌜k⌝)]]    = ⌜k+n⌝            (return)
```

Each clause assumes its term is well typed, and the `(catch)` clause assumes
the context does not capture the variable in its hole — the paper's standing
conventions. -/
theorem theorem_4_27 :
    -- (error)
    (∀ (E : EvalCtx) (b : Bool) (Env : Tmodel.Env),
      Comb.HasTy [] (E.fill (.const (.err b))) 𝕆 →
      Tmodel.combMeaning Env (E.fill (.const (.err b))) 𝕆 = errAns b) ∧
    -- (bottom)
    (∀ (E : EvalCtx) (Env : Tmodel.Env),
      Comb.HasTy [] (E.fill (Omega 𝕆)) 𝕆 →
      Tmodel.combMeaning Env (E.fill (Omega 𝕆)) 𝕆
        = Ideal.principal (DSub.bot : D 𝕆)) ∧
    -- (catch)
    (∀ (l : List Ty) (E : EvalCtx) (j : Fin l.length) (Env : Tmodel.Env),
      Comb.HasTy (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))) 𝕆 →
      ¬ E.Binds (j.val, l[j.val]'j.isLt) →
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
