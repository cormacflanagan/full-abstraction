/-
# Machinery for Lemma 5.2 (Definability of finite elements)

The tools of the §5 representability construction: `k`-ary application in the
ideal completion, subtree representability (Definition 5.3), the leaf case of
the induction, and the computation lemmas for the primitive constants that the
`catch`-based node case consumes.
-/
import FullAbstraction.Control

namespace FA

open Po

/-! ## `k`-ary application in the ideal completion -/

/-- `apply (F, D₁, …, Dₖ)` in the tree domains. -/
noncomputable def applyIdeals : ∀ σ : Ty, T σ → ((i : Fin σ.arity) → T (σ.arg i)) → T 𝕆
  | .base, t, _ => t
  | .arrow _ b, t, ds =>
      applyIdeals b (applyT t (ds ⟨0, Nat.succ_pos _⟩))
        (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-! ## Definition 5.3 -/

/-- Ground trees are always legal: `𝕆` has no argument positions. -/
theorem TreeOk_ground (γ : Ctx 𝕆) : ∀ t : Tree 𝕆, TreeOk γ t
  | .leaf v => TreeOk.leaf γ v
  | .node i _ _ => absurd i.isLt (by simp [Ty.arity])

/-- A ground tree, packed as a finite element. -/
noncomputable def groundD (t : Tree 𝕆) : D 𝕆 := ⟨t, TreeOk_ground Ctx.empty t⟩

/-- Application of principal ideals is the principal ideal of the
application. -/
theorem applyT_principal {σ τ : Ty} (f : D (σ ⇒ τ)) (d : D σ) :
    applyT (Ideal.principal f) (Ideal.principal d) = Ideal.principal (applyD f d) := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨f', hf', d', hd', hc⟩
    show Tree.Le c.1 (apply0 f.1 d.1)
    refine Tree.Le.trans (hc : Tree.Le c.1 (apply0 f'.1 d'.1)) ?_
    exact Tree.Le.trans
      (apply0_mono_left (hf' : Tree.Le f'.1 f.1) d'.1)
      (apply0_mono_right f.1 (hd' : Tree.Le d'.1 d.1))
  · intro hc
    exact ⟨f, Po.le_refl f, d, Po.le_refl d, hc⟩

/-- Iterated application of principal ideals computes `applyArgs`. -/
theorem applyIdeals_principal : ∀ (σ : Ty) (d : D σ)
    (ds : (i : Fin σ.arity) → D (σ.arg i)),
    applyIdeals σ (Ideal.principal d) (fun i => Ideal.principal (ds i))
      = Ideal.principal (groundD (applyArgs σ d.1 (fun i => (ds i).1)))
  | .base, d, ds => by
      show Ideal.principal d = _
      exact congrArg Ideal.principal (Subtype.ext rfl)
  | .arrow a τ, d, ds => by
      show applyIdeals τ (applyT (Ideal.principal d)
        (Ideal.principal (ds ⟨0, Nat.succ_pos _⟩))) _ = _
      rw [applyT_principal d (ds ⟨0, Nat.succ_pos _⟩)]
      exact applyIdeals_principal τ (applyD d (ds ⟨0, Nat.succ_pos _⟩))
        (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- **Definition 5.3** (*Subtree representability*).

"Let `γ` be a context in `C_σ`.  A subtree `e ∈ D_σ(γ)` is representable iff
there exists a closed expression `M` such that
`apply (T[[M]], d₁, …, dₖ) = apply (e, d₁, …, dₖ)` for all arguments
`d₁, …, dₖ` in `D_σ₁, …, D_σₖ`, such that `dᵢ ⊒ ⊔ γ(i)`.

When `γ = ∅`, `e` is a complete tree and subtree representability reduces to
tree representability by extensionality." -/
def Representable (σ : Ty) (γ : Ctx σ) (e : Tree σ) : Prop :=
  ∃ M : Term SPCF, Term.Closed M ∧ Term.HasTy [] M σ ∧
    ∀ ds : (i : Fin σ.arity) → D (σ.arg i),
      (∀ i, Ctx.Above γ i (ds i).1) →
      applyIdeals σ (Tmodel.meaning botEnv M σ) (fun i => Ideal.principal (ds i))
        = Ideal.principal (groundD (applyArgs σ e (fun i => (ds i).1)))

/-- Abstraction over a variable list, at the term level. -/
theorem Term.lams_closed : ∀ (xs : List (Nat × Ty)) (B : Term SPCF),
    Term.Closed B → Term.Closed (Term.lams xs B)
  | [], _, h => h
  | p :: xs, B, h => by
      intro q hq
      exact Term.lams_closed xs B h q hq.1

/-- Typing for iterated `λ`. -/
theorem Term.lams_hasTy : ∀ (xs : List (Nat × Ty)) (Γ : List (Nat × Ty))
    (B : Term SPCF) (ρ : Ty), Term.HasTy (xs ++ Γ) B ρ →
    Term.HasTy Γ (Term.lams xs B) (xs.foldr (fun p τ => p.2 ⇒ τ) ρ)
  | [], _, _, _, h => h
  | (x, σ) :: xs, Γ, B, ρ, h => by
      show Term.HasTy Γ (Term.lam x σ (Term.lams xs B)) _
      refine Term.HasTy.lam (Term.lams_hasTy xs ((x, σ) :: Γ) B ρ ?_)
      refine Term.weaken (fun p hp => ?_) h
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with (hp | hp) | hp
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)

/-- A leaf applies to anything as itself. -/
theorem applyArgs_leaf : ∀ (σ : Ty) (v : Val)
    (ds : (i : Fin σ.arity) → Tree (σ.arg i)),
    applyArgs σ (.leaf v) ds = .leaf v
  | .base, _, _ => rfl
  | .arrow a τ, v, ds => by
      show applyArgs τ (apply0 (.leaf v) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      exact applyArgs_leaf τ v _

/-- A leaf-valued ideal applies to anything as itself. -/
theorem applyIdeals_leafT : ∀ (σ : Ty) (v : Val)
    (ds : (i : Fin σ.arity) → D (σ.arg i)),
    applyIdeals σ (leafT σ v) (fun i => Ideal.principal (ds i))
      = Ideal.principal (groundD (.leaf v))
  | .base, v, _ => congrArg Ideal.principal (Subtype.ext rfl)
  | .arrow a τ, v, ds => by
      show applyIdeals τ (applyT (leafT (a ⇒ τ) v)
        (Ideal.principal (ds ⟨0, Nat.succ_pos _⟩))) _ = _
      rw [applyT_leafT]
      exact applyIdeals_leafT τ v _

/-- The leaf case of the induction of Lemma 5.2: `λ*x̄.⌜a⌝`, `λ*x̄.errorⱼ` and
`λ*x̄.Ω` represent the leaves. -/
theorem representable_leaf (σ : Ty) (γ : Ctx σ) (v : Val) :
    Representable σ γ (.leaf v) := by
  obtain ⟨xs, rfl⟩ : ∃ xs : List (Nat × Ty), σ = foldX xs :=
    ⟨varsOf σ.args, by
      show σ = (varsOf σ.args).foldr (fun p τ => p.2 ⇒ τ) 𝕆
      rw [varsOf_foldr, Ty.foldr_args]⟩
  have key : ∀ B : Term SPCF, Term.Closed B → Term.HasTy (xs ++ []) B 𝕆 →
      (∀ Env' : Tmodel.Env, Tmodel.combMeaning Env' (Term.toComb B) 𝕆 = leafT 𝕆 v) →
      Representable (foldX xs) γ (.leaf v) := by
    intro B hBcl hBty hBmean
    refine ⟨Term.lams xs B, Term.lams_closed xs B hBcl,
      Term.lams_hasTy xs [] B 𝕆 hBty, fun ds hds => ?_⟩
    have hmean : Tmodel.meaning botEnv (Term.lams xs B) (foldX xs)
        = leafT (foldX xs) v := by
      show Tmodel.combMeaning botEnv (Term.toComb (Term.lams xs B)) (foldX xs) = _
      rw [Term.toComb_lams]
      exact lamStars_meaning_leaf xs botEnv (Term.toComb B) 𝕆 []
        (Term.toComb_hasTy hBty) v (fun Env' _ => hBmean Env')
    rw [hmean, applyIdeals_leafT, applyArgs_leaf]
  cases v with
  | num a =>
    refine key (.const (.num a)) (fun p hp => hp) Term.HasTy.const (fun Env' => ?_)
    exact Model.combMeaning_const Tmodel Env' (SConst.num a)
  | err b =>
    refine key (.const (.err b)) (fun p hp => hp) Term.HasTy.const (fun Env' => ?_)
    exact Model.combMeaning_const Tmodel Env' (SConst.err b)
  | bot =>
    refine key omegaTerm (by rintro p (hp | hp) <;> exact hp)
      (Term.weaken (fun p hp => absurd hp (by simp)) hasTy_omegaTerm)
      (fun Env' => ?_)
    exact meaning_omegaTerm Env'

/-! ## Computation lemmas for the primitive constants -/

/-- Every ground tree is a leaf. -/
theorem ground_leaf : ∀ t : Tree 𝕆, ∃ v : Val, t = .leaf v
  | .leaf v => ⟨v, rfl⟩
  | .node i _ _ => absurd i.isLt (by simp [Ty.arity])

/-- `sub1` on a positive numeral, on trees. -/
theorem apply0_sub1_succ (n : Nat) :
    apply0 treeSub1 (.leaf (.num (n + 1))) = .leaf (.num n) := rfl

/-- `sub1` on a positive numeral. -/
theorem applyT_sub1_succ (n : Nat) :
    applyT (idealOf treeSub1) (natAns (n + 1)) = natAns n := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨g, hg, d, hd, hc⟩
    show Tree.Le c.1 (.leaf (.num n))
    refine Tree.Le.trans (hc : Tree.Le c.1 (apply0 g.1 d.1)) ?_
    refine Tree.Le.trans
      (apply0_mono_left (hg : Tree.Le g.1 treeSub1) d.1) ?_
    refine Tree.Le.trans (apply0_mono_right treeSub1
      (hd : Tree.Le d.1 (.leaf (.num (n + 1))))) ?_
    rw [apply0_sub1_succ]
    exact Tree.Le.refl _
  · intro hc
    have hlegal : LegalResp (Query.hole : Query 𝕆) (Resp.ans (n + 1)) :=
      LegalResp.num Query.hole (n + 1)
    have gok : TreeOk Ctx.empty
        ((Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          fun r => if r = Resp.ans (n + 1)
            then Tree.leaf (.num n) else Tree.bot) : Tree (𝕆 ⇒ 𝕆)) := by
      refine TreeOk.node _ _ _ _ LegalQuery.root
        ⟨[Resp.ans (n + 1)], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
      · by_cases hr2 : r = Resp.ans (n + 1)
        · rw [hr2]; exact List.mem_cons_self ..
        · exact absurd (if_neg hr2) hr
      · by_cases hr2 : r = Resp.ans (n + 1)
        · rw [if_pos hr2]; exact TreeOk.leaf _ _
        · rw [if_neg hr2]; exact TreeOk.leaf _ _
      · by_cases hr2 : r = Resp.ans (n + 1)
        · exact absurd (hr2 ▸ hlegal) hr
        · exact if_neg hr2
    refine ⟨⟨_, gok⟩, ?_, ⟨.leaf (.num (n + 1)), TreeOk.leaf _ _⟩,
      Tree.Le.refl _, ?_⟩
    · rw [treeSub1]
      refine Tree.Le.node _ _ _ _ fun r => ?_
      by_cases hr : r = Resp.ans (n + 1)
      · subst hr
        rw [if_pos rfl]
        exact Tree.Le.refl _
      · rw [if_neg hr]
        exact Tree.Le.bot _
    · show Tree.Le c.1 (apply0 _ (Tree.leaf (.num (n + 1)) : Tree 𝕆))
      rw [show apply0 (Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          fun r => if r = Resp.ans (n + 1)
            then Tree.leaf (.num n) else Tree.bot)
          (Tree.leaf (.num (n + 1)) : Tree 𝕆) = Tree.leaf (.num n) from by
        rw [apply0]
        simp only [Tree.at'_hole]
        show apply0 (if Query.hole.substAns (RAns.num (n + 1)) = Resp.ans (n + 1)
          then Tree.leaf (Val.num n) else Tree.bot) _ = _
        rw [show (Query.hole.substAns (RAns.num (n + 1)) : Resp 𝕆)
            = Resp.ans (n + 1) from rfl, if_pos rfl]
        rfl]
      exact (hc : Tree.Le c.1 (.leaf (.num n)))

/-- `sub1` on `⌜0⌝` diverges. -/
theorem applyT_sub1_zero' :
    applyT (idealOf treeSub1) (natAns 0) = leafT 𝕆 .bot := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨g, hg, d, hd, hc⟩
    show Tree.Le c.1 (.leaf .bot)
    refine Tree.Le.trans (hc : Tree.Le c.1 (apply0 g.1 d.1)) ?_
    refine Tree.Le.trans
      (apply0_mono_left (hg : Tree.Le g.1 treeSub1) d.1) ?_
    refine Tree.Le.trans (apply0_mono_right treeSub1
      (hd : Tree.Le d.1 (.leaf (.num 0)))) ?_
    rw [apply0_sub1_zero]
    exact Tree.Le.refl _
  · intro hc
    refine ⟨DSub.bot, Tree.Le.bot _, ⟨.leaf (.num 0), TreeOk.leaf _ _⟩,
      Tree.Le.refl _, ?_⟩
    show Tree.Le c.1 (apply0 (Tree.bot : Tree (𝕆 ⇒ 𝕆)) (Tree.leaf (.num 0)))
    exact mem_leafT.mp hc

/-- `sub1` propagates an error. -/
theorem applyT_sub1_err (b : Bool) :
    applyT (idealOf treeSub1) (leafT 𝕆 (.err b)) = leafT 𝕆 (.err b) := by
  rw [treeSub1]
  exact applyT_rootProbe_err (Nat.succ_pos _) _ b

/-- `sub1` on `⊥` diverges. -/
theorem applyT_sub1_bot :
    applyT (idealOf treeSub1) (leafT 𝕆 .bot) = leafT 𝕆 .bot := by
  rw [treeSub1]
  exact applyT_rootProbe_bot (Nat.succ_pos _) _

/-- The three-argument `if0` computation, on trees. -/
theorem apply0_if0 (v : Nat) (at' bt : Tree 𝕆) :
    apply0 (apply0 (apply0 treeIf0 (.leaf (.num v))) at') bt
      = if v = 0 then at' else bt := by
  obtain ⟨va, rfl⟩ := ground_leaf at'
  obtain ⟨vb, rfl⟩ := ground_leaf bt
  cases v with
  | zero =>
    rw [if_pos rfl]
    cases va <;> rfl
  | succ v =>
    rw [if_neg (by omega)]
    cases vb <;> rfl

/-- `⊥` belongs to every ideal. -/
theorem bot_mem {σ : Ty} (I : T σ) : DSub.bot ∈ I := by
  obtain ⟨d, hd⟩ := I.nonempty'
  exact I.downward DSub.bot d (Tree.Le.bot _) hd

/-- The `if0` computation on a numeral scrutinee and finite ground arms. -/
theorem applyT_if0_chain (v : Nat) (a b : D 𝕆) :
    applyT (applyT (applyT (idealOf treeIf0) (natAns v)) (Ideal.principal a))
      (Ideal.principal b)
      = Ideal.principal (if v = 0 then a else b) := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨g₂, ⟨g₁, ⟨g₀, hg₀, cv, hcv, hle₁⟩, a', ha', hle₂⟩, b', hb', hle₃⟩
    show Tree.Le c.1 (if v = 0 then a else b).1
    have s1 : Tree.Le (apply0 g₀.1 cv.1)
        (apply0 treeIf0 (.leaf (.num v))) :=
      Tree.Le.trans (apply0_mono_left (hg₀ : Tree.Le g₀.1 treeIf0) cv.1)
        (apply0_mono_right treeIf0 (hcv : Tree.Le cv.1 (.leaf (.num v))))
    have s2 : Tree.Le (apply0 g₁.1 a'.1)
        (apply0 (apply0 treeIf0 (.leaf (.num v))) a.1) :=
      Tree.Le.trans (apply0_mono_left
          (Tree.Le.trans (hle₁ : Tree.Le g₁.1 (apply0 g₀.1 cv.1)) s1) a'.1)
        (apply0_mono_right _ (ha' : Tree.Le a'.1 a.1))
    have s3 : Tree.Le (apply0 g₂.1 b'.1)
        (apply0 (apply0 (apply0 treeIf0 (.leaf (.num v))) a.1) b.1) :=
      Tree.Le.trans (apply0_mono_left
          (Tree.Le.trans (hle₂ : Tree.Le g₂.1 (apply0 g₁.1 a'.1)) s2) b'.1)
        (apply0_mono_right _ (hb' : Tree.Le b'.1 b.1))
    refine Tree.Le.trans (hle₃ : Tree.Le c.1 (apply0 g₂.1 b'.1))
      (Tree.Le.trans s3 ?_)
    rw [apply0_if0]
    by_cases hv : v = 0
    · rw [if_pos hv, if_pos hv]
      exact Tree.Le.refl _
    · rw [if_neg hv, if_neg hv]
      exact Tree.Le.refl _
  · intro hc
    have hcle : Tree.Le c.1 (if v = 0 then a else b).1 := hc
    -- it suffices to exhibit one finite legal pruning of `if0` computing the arm
    suffices h : ∃ P : D (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆), Tree.Le P.1 treeIf0 ∧
        Tree.Le c.1 (apply0 (apply0 (apply0 P.1 (.leaf (.num v))) a.1) b.1) by
      obtain ⟨P, hPle, hPval⟩ := h
      exact ⟨applyD (applyD P ⟨.leaf (.num v), TreeOk.leaf _ _⟩) a,
        ⟨applyD P ⟨.leaf (.num v), TreeOk.leaf _ _⟩,
          ⟨P, hPle, ⟨.leaf (.num v), TreeOk.leaf _ _⟩, Tree.Le.refl _,
            Po.le_refl _⟩,
          a, Ideal.mem_principal.mpr (Po.le_refl a), Po.le_refl _⟩,
        b, Ideal.mem_principal.mpr (Po.le_refl b), hPval⟩
    by_cases hv : v = 0
    · subst hv
      rw [if_pos rfl] at hcle
      obtain ⟨w, hw⟩ := ground_leaf a.1
      rw [hw] at hcle
      cases w with
      | bot =>
        have hcb : c.1 = Tree.bot := Tree.eq_bot_of_le_bot hcle
        refine ⟨DSub.bot, Tree.Le.bot _, ?_⟩
        rw [hcb]
        exact Tree.Le.bot _
      | err e =>
        refine ⟨⟨Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          (fun r => if r = Resp.ans 0 then
            Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆) (fun _ => Tree.bot)
            else Tree.bot), ?_⟩, ?_, ?_⟩
        · refine TreeOk.node _ _ _ _ LegalQuery.root
            ⟨[Resp.ans 0], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hr2 : r = Resp.ans 0
            · rw [hr2]; exact List.mem_cons_self ..
            · exact absurd (if_neg hr2) hr
          · by_cases hr2 : r = Resp.ans 0
            · rw [if_pos hr2]
              exact TreeOk.node _ _ _ _ LegalQuery.root
                ⟨[], fun r' hr' => absurd rfl hr'⟩
                (fun r' _ => TreeOk.leaf _ _) (fun r' _ => rfl)
            · rw [if_neg hr2]; exact TreeOk.leaf _ _
          · by_cases hr2 : r = Resp.ans 0
            · exact absurd (hr2 ▸ LegalResp.num Query.hole 0) hr
            · exact if_neg hr2
        · rw [treeIf0]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = Resp.ans 0
          · subst hr
            rw [if_pos rfl]
            show Tree.Le _ (groundBranch _ (Resp.ans 0))
            exact Tree.Le.node _ _ _ _ fun r' => Tree.Le.bot _
          · rw [if_neg hr]
            exact Tree.Le.bot _
        · have h1 : apply0 ((Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
              (fun r => if r = Resp.ans 0 then
                Tree.node ⟨1, by decide⟩ Query.hole (fun _ => Tree.bot)
                else Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num 0))
              = apply0 ((Tree.node ⟨1, by decide⟩ Query.hole
                  (fun _ => Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num 0)) := by
            rw [apply0]
            simp only [Tree.at'_hole]
            show apply0 (if Query.hole.substAns (RAns.num 0) = Resp.ans 0
              then _ else _) _ = _
            rw [show (Query.hole.substAns (RAns.num 0) : Resp 𝕆) = Resp.ans 0
              from rfl, if_pos rfl]
          have h2 : apply0 ((Tree.node ⟨1, by decide⟩ Query.hole
              (fun _ => Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num 0))
              = (Tree.node ⟨0, by decide⟩ Query.hole
                  (fun _ => Tree.bot) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) := by
            rw [apply0]
            rfl
          have h3 : apply0 ((Tree.node ⟨0, by decide⟩ Query.hole
              (fun _ => Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) a.1
              = Tree.leaf (Val.err e) := by
            rw [hw, apply0]
            rfl
          rw [h1, h2, h3]
          show Tree.Le c.1 (apply0 (Tree.leaf (Val.err e) : Tree (𝕆 ⇒ 𝕆)) b.1)
          exact hcle
      | num u =>
        refine ⟨⟨Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          (fun r => if r = Resp.ans 0 then
            Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆)
              (fun r' => if r' = Resp.ans u then .leaf (.num u) else Tree.bot)
            else Tree.bot), ?_⟩, ?_, ?_⟩
        · refine TreeOk.node _ _ _ _ LegalQuery.root
            ⟨[Resp.ans 0], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hr2 : r = Resp.ans 0
            · rw [hr2]; exact List.mem_cons_self ..
            · exact absurd (if_neg hr2) hr
          · by_cases hr2 : r = Resp.ans 0
            · rw [if_pos hr2]
              refine TreeOk.node _ _ _ _ LegalQuery.root
                ⟨[Resp.ans u], fun r' hr' => ?_⟩ (fun r' _ => ?_) (fun r' hr' => ?_)
              · by_cases hr3 : r' = Resp.ans u
                · rw [hr3]; exact List.mem_cons_self ..
                · exact absurd (if_neg hr3) hr'
              · by_cases hr3 : r' = Resp.ans u
                · rw [if_pos hr3]; exact TreeOk.leaf _ _
                · rw [if_neg hr3]; exact TreeOk.leaf _ _
              · by_cases hr3 : r' = Resp.ans u
                · exact absurd (hr3 ▸ LegalResp.num Query.hole u) hr'
                · exact if_neg hr3
            · rw [if_neg hr2]; exact TreeOk.leaf _ _
          · by_cases hr2 : r = Resp.ans 0
            · exact absurd (hr2 ▸ LegalResp.num Query.hole 0) hr
            · exact if_neg hr2
        · rw [treeIf0]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = Resp.ans 0
          · subst hr
            rw [if_pos rfl]
            show Tree.Le _ (groundBranch _ (Resp.ans 0))
            refine Tree.Le.node _ _ _ _ fun r' => ?_
            by_cases hr3 : r' = Resp.ans u
            · subst hr3
              rw [if_pos rfl]
              show Tree.Le _ (groundBranch _ (Resp.ans u))
              exact Tree.Le.refl _
            · rw [if_neg hr3]
              exact Tree.Le.bot _
          · rw [if_neg hr]
            exact Tree.Le.bot _
        · have h1 : apply0 ((Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
              (fun r => if r = Resp.ans 0 then
                Tree.node ⟨1, by decide⟩ Query.hole
                  (fun r' => if r' = Resp.ans u then .leaf (.num u) else Tree.bot)
                else Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num 0))
              = (Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
                  (fun r' => apply0 (if r' = Resp.ans u
                    then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                    (.leaf (.num 0))) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) := by
            rw [apply0]
            simp only [Tree.at'_hole]
            show apply0 (if Query.hole.substAns (RAns.num 0) = Resp.ans 0
              then _ else _) _ = _
            rw [show (Query.hole.substAns (RAns.num 0) : Resp 𝕆) = Resp.ans 0
              from rfl, if_pos rfl, apply0]
          have h2 : apply0 ((Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
              (fun r' => apply0 (if r' = Resp.ans u
                then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                (.leaf (.num 0))) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆))) a.1
              = Tree.leaf (.num u) := by
            rw [hw, apply0]
            simp only [Tree.at'_hole]
            show apply0 (apply0 (if Query.hole.substAns (RAns.num u) = Resp.ans u
              then _ else _) _) _ = _
            rw [show (Query.hole.substAns (RAns.num u) : Resp 𝕆) = Resp.ans u
              from rfl, if_pos rfl]
            rfl
          rw [h1, h2]
          show Tree.Le c.1 (apply0 (Tree.leaf (Val.num u) : Tree (𝕆 ⇒ 𝕆)) b.1)
          exact hcle
    · rw [if_neg hv] at hcle
      obtain ⟨s', rfl⟩ : ∃ s', v = s' + 1 := ⟨v - 1, by omega⟩
      obtain ⟨w, hw⟩ := ground_leaf b.1
      rw [hw] at hcle
      cases w with
      | bot =>
        have hcb : c.1 = Tree.bot := Tree.eq_bot_of_le_bot hcle
        refine ⟨DSub.bot, Tree.Le.bot _, ?_⟩
        rw [hcb]
        exact Tree.Le.bot _
      | err e =>
        refine ⟨⟨Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          (fun r => if r = Resp.ans (s' + 1) then
            Tree.node ⟨2, by decide⟩ (Query.hole : Query 𝕆) (fun _ => Tree.bot)
            else Tree.bot), ?_⟩, ?_, ?_⟩
        · refine TreeOk.node _ _ _ _ LegalQuery.root
            ⟨[Resp.ans (s' + 1)], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · rw [hr2]; exact List.mem_cons_self ..
            · exact absurd (if_neg hr2) hr
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · rw [if_pos hr2]
              exact TreeOk.node _ _ _ _ LegalQuery.root
                ⟨[], fun r' hr' => absurd rfl hr'⟩
                (fun r' _ => TreeOk.leaf _ _) (fun r' _ => rfl)
            · rw [if_neg hr2]; exact TreeOk.leaf _ _
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · exact absurd (hr2 ▸ LegalResp.num Query.hole (s' + 1)) hr
            · exact if_neg hr2
        · rw [treeIf0]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = Resp.ans (s' + 1)
          · subst hr
            rw [if_pos rfl]
            show Tree.Le _ (groundBranch _ (Resp.ans (s' + 1)))
            exact Tree.Le.node _ _ _ _ fun r' => Tree.Le.bot _
          · rw [if_neg hr]
            exact Tree.Le.bot _
        · have h1 : apply0 ((Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
              (fun r => if r = Resp.ans (s' + 1) then
                Tree.node ⟨2, by decide⟩ Query.hole (fun _ => Tree.bot)
                else Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num (s' + 1)))
              = (Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆)
                  (fun _ => Tree.bot) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) := by
            rw [apply0]
            simp only [Tree.at'_hole]
            show apply0 (if Query.hole.substAns (RAns.num (s' + 1))
              = Resp.ans (s' + 1) then _ else _) _ = _
            rw [show (Query.hole.substAns (RAns.num (s' + 1)) : Resp 𝕆)
              = Resp.ans (s' + 1) from rfl, if_pos rfl, apply0]
            rfl
          have h2 : apply0 ((Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆)
              (fun _ => Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) a.1
              = (Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
                  (fun _ => Tree.bot) : Tree (𝕆 ⇒ 𝕆)) := by
            rw [apply0]
            rfl
          have h3 : apply0 ((Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
              (fun _ => Tree.bot)) : Tree (𝕆 ⇒ 𝕆)) b.1
              = Tree.leaf (Val.err e) := by
            rw [hw, apply0]
            rfl
          rw [h1, h2, h3]
          exact hcle
      | num u =>
        refine ⟨⟨Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
          (fun r => if r = Resp.ans (s' + 1) then
            Tree.node ⟨2, by decide⟩ (Query.hole : Query 𝕆)
              (fun r' => if r' = Resp.ans u then .leaf (.num u) else Tree.bot)
            else Tree.bot), ?_⟩, ?_, ?_⟩
        · refine TreeOk.node _ _ _ _ LegalQuery.root
            ⟨[Resp.ans (s' + 1)], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · rw [hr2]; exact List.mem_cons_self ..
            · exact absurd (if_neg hr2) hr
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · rw [if_pos hr2]
              refine TreeOk.node _ _ _ _ LegalQuery.root
                ⟨[Resp.ans u], fun r' hr' => ?_⟩ (fun r' _ => ?_) (fun r' hr' => ?_)
              · by_cases hr3 : r' = Resp.ans u
                · rw [hr3]; exact List.mem_cons_self ..
                · exact absurd (if_neg hr3) hr'
              · by_cases hr3 : r' = Resp.ans u
                · rw [if_pos hr3]; exact TreeOk.leaf _ _
                · rw [if_neg hr3]; exact TreeOk.leaf _ _
              · by_cases hr3 : r' = Resp.ans u
                · exact absurd (hr3 ▸ LegalResp.num Query.hole u) hr'
                · exact if_neg hr3
            · rw [if_neg hr2]; exact TreeOk.leaf _ _
          · by_cases hr2 : r = Resp.ans (s' + 1)
            · exact absurd (hr2 ▸ LegalResp.num Query.hole (s' + 1)) hr
            · exact if_neg hr2
        · rw [treeIf0]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = Resp.ans (s' + 1)
          · subst hr
            rw [if_pos rfl]
            show Tree.Le _ (groundBranch _ (Resp.ans (s' + 1)))
            refine Tree.Le.node _ _ _ _ fun r' => ?_
            by_cases hr3 : r' = Resp.ans u
            · subst hr3
              rw [if_pos rfl]
              show Tree.Le _ (groundBranch _ (Resp.ans u))
              exact Tree.Le.refl _
            · rw [if_neg hr3]
              exact Tree.Le.bot _
          · rw [if_neg hr]
            exact Tree.Le.bot _
        · have h1 : apply0 ((Tree.node ⟨0, Nat.succ_pos _⟩ (Query.hole : Query 𝕆)
              (fun r => if r = Resp.ans (s' + 1) then
                Tree.node ⟨2, by decide⟩ Query.hole
                  (fun r' => if r' = Resp.ans u then .leaf (.num u) else Tree.bot)
                else Tree.bot)) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) (.leaf (.num (s' + 1)))
              = (Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆)
                  (fun r' => apply0 (if r' = Resp.ans u
                    then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                    (.leaf (.num (s' + 1)))) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) := by
            rw [apply0]
            simp only [Tree.at'_hole]
            show apply0 (if Query.hole.substAns (RAns.num (s' + 1))
              = Resp.ans (s' + 1) then _ else _) _ = _
            rw [show (Query.hole.substAns (RAns.num (s' + 1)) : Resp 𝕆)
              = Resp.ans (s' + 1) from rfl, if_pos rfl, apply0]
          have h2 : apply0 ((Tree.node ⟨1, by decide⟩ (Query.hole : Query 𝕆)
              (fun r' => apply0 (if r' = Resp.ans u
                then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                (.leaf (.num (s' + 1))))) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆)) a.1
              = (Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
                  (fun r' => apply0 (apply0 (if r' = Resp.ans u
                    then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                    (.leaf (.num (s' + 1)))) a.1) : Tree (𝕆 ⇒ 𝕆)) := by
            rw [apply0]
          have h3 : apply0 ((Tree.node ⟨0, by decide⟩ (Query.hole : Query 𝕆)
              (fun r' => apply0 (apply0 (if r' = Resp.ans u
                then (.leaf (.num u) : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)) else Tree.bot)
                (.leaf (.num (s' + 1)))) a.1)) : Tree (𝕆 ⇒ 𝕆)) b.1
              = Tree.leaf (.num u) := by
            rw [hw, apply0]
            simp only [Tree.at'_hole]
            show apply0 (apply0 (apply0 (if Query.hole.substAns (RAns.num u)
              = Resp.ans u then _ else _) _) _) _ = _
            rw [show (Query.hole.substAns (RAns.num u) : Resp 𝕆) = Resp.ans u
              from rfl, if_pos rfl]
            rfl
          rw [h1, h2, h3]
          exact hcle


/-- The meaning of an application, in terms of `apply`. -/
theorem meaning_app {L : Lang} (M : Model L) (E : M.Env) (t u : Comb L) (a ρ : Ty)
    (hu : Comb.tyOf u = a) :
    M.combMeaning E (.app t u) ρ = M.apply (M.combMeaning E t (a ⇒ ρ)) (M.combMeaning E u a) := by
  subst hu; rfl

/-- The meaning of `(M E₁ … Eₖ)` is `apply (T[[M]], T[[E₁]], …, T[[Eₖ]])`.

This is what makes the applicative context `C[·] = ([·] E₁ … Eₖ)` of the proof
of Theorem 5.1 compute the `k`-ary application of the meanings. -/
theorem meaning_apps : ∀ (σ : Ty) (M : Term SPCF) (E : (i : Fin σ.arity) → Term SPCF)
    (ds : (i : Fin σ.arity) → T (σ.arg i)),
    (∀ i, Term.HasTy [] (E i) (σ.arg i)) →
    (∀ i, Tmodel.meaning botEnv (E i) (σ.arg i) = ds i) →
    Tmodel.meaning botEnv (Term.apps M (List.ofFn E)) 𝕆
      = applyIdeals σ (Tmodel.meaning botEnv M σ) ds
  | .base, M, E, ds, _, _ => by
      show Tmodel.meaning botEnv (Term.apps M (List.ofFn E)) 𝕆 = _
      rw [show (List.ofFn E : List (Term SPCF)) = [] from List.ofFn_zero]
      rfl
  | .arrow a τ, M, E, ds, hty, hE => by
      have hsucc : (List.ofFn E : List (Term SPCF))
          = E ⟨0, Nat.succ_pos _⟩ :: List.ofFn fun i : Fin τ.arity =>
              E ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
        rw [List.ofFn_succ]
        rfl
      have hstep : Term.apps M (List.ofFn E)
          = Term.apps (.app M (E ⟨0, Nat.succ_pos _⟩)) (List.ofFn fun i : Fin τ.arity =>
              E ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by
        rw [hsucc]; rfl
      rw [hstep,
        meaning_apps τ (.app M (E ⟨0, Nat.succ_pos _⟩))
          (fun i => E ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => hty ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => hE ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)]
      show applyIdeals τ (Tmodel.combMeaning botEnv
        (.app (Term.toComb M) (Term.toComb (E ⟨0, Nat.succ_pos _⟩))) τ) _ = _
      rw [meaning_app Tmodel botEnv _ _ a τ (Term.tyOf_toComb (hty ⟨0, Nat.succ_pos _⟩))]
      have h0 : Tmodel.combMeaning botEnv (Term.toComb (E ⟨0, Nat.succ_pos _⟩)) a
          = ds ⟨0, Nat.succ_pos _⟩ := hE ⟨0, Nat.succ_pos _⟩
      rw [h0]
      rfl


/-! ## The dispatch behaviour of a node under `k`-ary application -/

/-- Applying a node `⟨i,q,f⟩` to a full argument tuple consults `dᵢ @ q` and
dispatches: an unanswered or `⊥` position diverges, an error propagates, a
numeral or an inner node selects the corresponding branch of `f` — which is
then applied to the *same* argument tuple. -/
theorem applyArgs_node : ∀ (σ : Ty) (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (ds : (j : Fin σ.arity) → Tree (σ.arg j)),
    applyArgs σ (.node i q f) ds =
      match (ds i).at' q with
      | none => Tree.bot
      | some (.leaf .bot) => Tree.bot
      | some (.leaf (.err b)) => .leaf (.err b)
      | some (.leaf (.num n)) => applyArgs σ (f (q.substAns (.num n))) ds
      | some (.node j p _) => applyArgs σ (f (q.substAns (.node j p))) ds
  | .base, i, _, _, _ => absurd i.isLt (by simp [Ty.arity])
  | .arrow a τ, ⟨0, h0⟩, q, f, ds => by
      show applyArgs τ (apply0 (.node ⟨0, h0⟩ q f) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      rw [apply0]
      cases h : (ds ⟨0, Nat.succ_pos _⟩).at' q with
      | none =>
        rw [show (Tree.bot : Tree τ) = Tree.leaf Val.bot from rfl, applyArgs_leaf]
        rfl
      | some t =>
        cases t with
        | leaf v =>
          cases v with
          | bot =>
            rw [show (Tree.bot : Tree τ) = Tree.leaf Val.bot from rfl, applyArgs_leaf]
            rfl
          | err b =>
            show applyArgs τ (.leaf (.err b)) _ = _
            rw [applyArgs_leaf]
          | num n => rfl
        | node j p g => rfl
  | .arrow a τ, ⟨i' + 1, hi⟩, q, f, ds => by
      show applyArgs τ (apply0 (.node ⟨i' + 1, hi⟩ q f) (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      rw [apply0]
      rw [applyArgs_node τ ⟨i', Nat.lt_of_succ_lt_succ hi⟩ q
        (fun r => apply0 (f r) (ds ⟨0, Nat.succ_pos _⟩))
        (fun j => ds ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)]
      cases h : (ds ⟨i' + 1, hi⟩).at' q with
      | none => rfl
      | some t =>
        cases t with
        | leaf v => cases v <;> rfl
        | node j p g => rfl

/-! ## The semantic root-shape lemma

The purely semantic content of Lemma B.1: an ideal at an iterated procedure
type whose full application to the all-`⊥` family is `⊥`, and whose full
application to the family that is `error₁` at position `j` and `⊥` elsewhere is
`error₁`, has a member probing argument `j` first — and every member is `⊥` or
probes argument `j` first. -/
theorem root_shape_of_runs (xs : List (Nat × Ty)) (Λ : T (foldX xs))
    (j : Fin xs.length)
    (hnodup : ∀ j' : Fin xs.length, j'.val ≠ j.val →
      (xs[j'.1]'j'.isLt) ≠ (xs[j.1]'j.isLt))
    (hrunB : applyTChainX xs Λ vsBot = leafT 𝕆 .bot)
    (hrunE : applyTChainX xs Λ
      (vsErr (xs[j.1]'j.isLt).1 (xs[j.1]'j.isLt).2) = leafT 𝕆 (.err true)) :
    (∃ s : D (foldX xs), s ∈ Λ ∧
      ∃ f, s.1 = Tree.node ⟨j.val, by rw [arity_foldrX]; exact j.isLt⟩
        Query.hole f) ∧
    (∀ s : D (foldX xs), s ∈ Λ →
      s.1 = Tree.bot ∨
      ∃ f, s.1 = Tree.node ⟨j.val, by rw [arity_foldrX]; exact j.isLt⟩
        Query.hole f) := by
  classical
  have hj : j.val < (foldX xs).arity := by
    rw [arity_foldrX]; exact j.isLt
  have hnoleaf : ∀ (s : D (foldX xs)) (v : Val),
      s ∈ Λ → s.1 = .leaf v → v = Val.bot := by
    intro s v hs hsv
    refine Classical.byContradiction fun hv => ?_
    have hmem : (⟨.leaf v, TreeOk.leaf _ _⟩ : D 𝕆)
        ∈ applyTChainX xs Λ vsBot := by
      refine applyTChainX_intro xs _ vsBot s hs
        (fun i => DSub.bot) (fun i => mem_leafT.mpr (Tree.Le.bot _)) _ ?_
      rw [hsv, apply0ChainF_leaf]
      exact Tree.Le.refl _
    rw [hrunB] at hmem
    have hle : Tree.Le (.leaf v) (.leaf .bot) := mem_leafT.mp hmem
    cases hle with
    | bot => exact hv rfl
    | leaf => exact hv rfl
  have hmemE : (⟨.leaf (.err true), TreeOk.leaf _ _⟩ : D 𝕆)
      ∈ applyTChainX xs Λ (vsErr (xs[j.1]'j.isLt).1 (xs[j.1]'j.isLt).2) := by
    rw [hrunE]
    exact mem_leafT.mpr (Tree.Le.refl _)
  obtain ⟨s₀, hs₀, ds₀, hds₀, hle₀⟩ := applyTChainX_mem xs _ _ _ hmemE
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
      · have hjtlen : jtv < xs.length := by
          rw [← arity_foldrX xs]
          exact hjtlt
        have hdsb : (ds₀ ⟨jtv, hjtlen⟩).1 = Tree.bot := by
          have hmem := hds₀ ⟨jtv, hjtlen⟩
          have hvs : vsErr (xs[j.1]'j.isLt).1 (xs[j.1]'j.isLt).2
              (xs[jtv]'hjtlen)
              = leafT (xs[jtv]'hjtlen).2 .bot := by
            rw [vsErr, if_neg]
            intro he
            exact hnodup ⟨jtv, hjtlen⟩ hjt he
          rw [hvs] at hmem
          exact Tree.eq_bot_of_le_bot (mem_leafT.mp hmem)
        rw [hsv, apply0ChainF_bot xs jtv hjtlen hjtlt f _ hdsb] at hle₀
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
    obtain ⟨u, hu, hsu, hs₀u⟩ := Λ.directed' s s₀ hs hs₀
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

/-! ## Padding a tree with an extra leading ground argument

The §5 construction interprets the tree `q̂(h)` "as a tree of type `σ'ₕ`" with
extra ground arguments.  Here the extra arguments are added at the *front*:
a padded tree never probes the new argument `0`, so applying it to anything
recovers the original tree (`apply0_pad`).  Grafting the probes of §5 into a
padded tree is what makes the argument expressions `Bₕ` report back to the
body of `M'`. -/

/-- Argument `i` of `σ`, as argument `i+1` of `𝕆 ⇒ σ`. -/
def Fin.padI {σ : Ty} (i : Fin σ.arity) : Fin (𝕆 ⇒ σ).arity :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

theorem Fin.padI_inj {σ : Ty} {i j : Fin σ.arity} (h : Fin.padI i = Fin.padI j) :
    i = j := by
  have hv := congrArg Fin.val h
  exact Fin.ext (by simp only [Fin.padI] at hv; omega)

theorem Fin.padI_ne_zero {σ : Ty} (i : Fin σ.arity)
    (h0 : 0 < (𝕆 ⇒ σ).arity) : Fin.padI i ≠ ⟨0, h0⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.padI] at hv
  exact Nat.succ_ne_zero _ hv

/-- Reinterpret a tree at `σ` as a tree at `𝕆 ⇒ σ` that ignores argument 0. -/
noncomputable def Tree.pad {σ : Ty} : Tree σ → Tree (𝕆 ⇒ σ)
  | .leaf v => .leaf v
  | .node i q f => .node (Fin.padI i) q (fun r => Tree.pad (f r))

/-- Reinterpret a position in `t` as a position in `Tree.pad t`. -/
def Query.padQ {σ : Ty} : Query σ → Query (𝕆 ⇒ σ)
  | .hole => .hole
  | .step i q r rest => .step (Fin.padI i) q r (Query.padQ rest)

/-- The padded context: nothing is known about the new argument. -/
noncomputable def Ctx.padC {σ : Ty} (γ : Ctx σ) : Ctx (𝕆 ⇒ σ) := fun j =>
  match j with
  | ⟨0, _⟩ => Tree.bot
  | ⟨i + 1, h⟩ => γ ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem Ctx.padC_padI {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity) :
    (Ctx.padC γ) (Fin.padI i) = γ i := rfl

theorem Ctx.padC_empty {σ : Ty} :
    Ctx.padC (Ctx.empty : Ctx σ) = (Ctx.empty : Ctx (𝕆 ⇒ σ)) := by
  funext j
  obtain ⟨jv, hj⟩ := j
  cases jv <;> rfl

theorem Ctx.padC_cons {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity)
    (r : Resp (σ.arg i)) :
    (Ctx.padC γ).cons (Fin.padI i) r = Ctx.padC (γ.cons i r) := by
  funext j
  obtain ⟨jv, hj⟩ := j
  cases jv with
  | zero =>
    rw [Ctx.cons_other _ _ (Fin.padI_ne_zero i hj)]
    rfl
  | succ k =>
    have hk : k < σ.arity := Nat.lt_of_succ_lt_succ hj
    have hjk : (⟨k + 1, hj⟩ : Fin (𝕆 ⇒ σ).arity) = Fin.padI ⟨k, hk⟩ := rfl
    rw [hjk]
    by_cases hik : i = (⟨k, hk⟩ : Fin σ.arity)
    · cases hik
      rw [Ctx.cons_self, Ctx.padC_padI, Ctx.padC_padI, Ctx.cons_self]
    · rw [Ctx.cons_other _ _ (fun he => hik (Fin.padI_inj he)),
        Ctx.padC_padI, Ctx.padC_padI, Ctx.cons_other γ r hik]

/-- A padded tree is `⊥` exactly when the original is. -/
theorem Tree.pad_eq_bot_iff {σ : Ty} (t : Tree σ) :
    Tree.pad t = Tree.bot ↔ t = Tree.bot := by
  cases t with
  | leaf v =>
    show (Tree.leaf v : Tree (𝕆 ⇒ σ)) = Tree.leaf Val.bot ↔ _
    exact Iff.intro (fun h => by injection h with hv; rw [hv]; rfl)
      (fun h => by injection h with hv; rw [hv])
  | node i q f =>
    constructor
    · intro h
      rw [Tree.pad] at h
      exact Tree.noConfusion h
    · intro h
      exact Tree.noConfusion h

/-- Applying a padded tree consumes the new argument and gives the original
tree back. -/
theorem apply0_pad {σ : Ty} : ∀ (t : Tree σ) (d : Tree 𝕆),
    apply0 (Tree.pad t) d = t
  | .leaf v, d => by rw [Tree.pad, apply0]
  | .node i q f, d => by
      rw [Tree.pad]
      simp only [Fin.padI]
      rw [apply0]
      show (Tree.node i q fun r => apply0 (Tree.pad (f r)) d) = _
      exact congrArg (fun g => (Tree.node i q g : Tree σ))
        (funext fun r => apply0_pad (f r) d)

/-- The equality of padded node values reduces to that of the originals. -/
theorem padNodeVal_eq_iff {σ : Ty} (i j : Fin σ.arity) (q : Query (σ.arg i))
    (p : Query (σ.arg j)) :
    ((⟨Fin.padI i, q⟩ : NodeVal (𝕆 ⇒ σ)) = ⟨Fin.padI j, p⟩)
      ↔ ((⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩) := by
  constructor
  · intro h
    injection h with h1 h2
    cases Fin.padI_inj h1
    cases (eq_of_heq h2 : q = p)
    rfl
  · intro h
    injection h with h1 h2
    cases h1
    cases (eq_of_heq h2 : q = p)
    rfl

/-- Navigation commutes with padding. -/
theorem at'_pad {σ : Ty} : ∀ (P : Query σ) (t : Tree σ),
    (Tree.pad t).at' (Query.padQ P) = Option.map Tree.pad (t.at' P)
  | .hole, t => rfl
  | .step i q r rest, t => by
      cases t with
      | leaf v => rfl
      | node j p f =>
        by_cases h : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩
        · injection h with h1 h2
          cases h1
          cases (eq_of_heq h2 : q = p)
          show ((Tree.pad (Tree.node i q f)).stepAt (Fin.padI i) q r).bind
              (fun d' => d'.at' (Query.padQ rest))
            = Option.map Tree.pad
              (((Tree.node i q f).stepAt i q r).bind (fun d' => d'.at' rest))
          rw [Tree.pad, Tree.stepAt_self, Tree.stepAt_self]
          show ((Tree.pad (f r)).at' (Query.padQ rest))
            = Option.map Tree.pad ((f r).at' rest)
          exact at'_pad rest (f r)
        · have hne : ¬ ((⟨Fin.padI i, q⟩ : NodeVal (𝕆 ⇒ σ))
              = ⟨Fin.padI j, p⟩) :=
            fun he => h ((padNodeVal_eq_iff i j q p).mp he)
          show ((Tree.pad (Tree.node j p f)).stepAt (Fin.padI i) q r).bind
              (fun d' => d'.at' (Query.padQ rest))
            = Option.map Tree.pad
              (((Tree.node j p f).stepAt i q r).bind (fun d' => d'.at' rest))
          rw [Tree.pad]
          rw [show ((Tree.node (Fin.padI j) p (fun r' => Tree.pad (f r'))).stepAt
              (Fin.padI i) q r : Option (Tree (𝕆 ⇒ σ))) = none from by
            show (dite _ _ _) = _
            rw [dif_neg hne]]
          rw [show ((Tree.node j p f).stepAt i q r : Option (Tree σ))
              = none from by
            show (dite _ _ _) = _
            rw [dif_neg h]]
          rfl

/-- Planting commutes with padding. -/
theorem plant_pad {σ : Ty} : ∀ (P : Query σ) (t e : Tree σ),
    plant (Query.padQ P) (Tree.pad t) (Tree.pad e) = Tree.pad (plant P t e)
  | .hole, t, e => rfl
  | .step i q r rest, t, e => by
      cases t with
      | leaf v => rfl
      | node j p f =>
        by_cases h : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩
        · injection h with h1 h2
          cases h1
          cases (eq_of_heq h2 : q = p)
          show plant (.step (Fin.padI i) q r (Query.padQ rest))
              (Tree.pad (Tree.node i q f)) (Tree.pad e) = _
          rw [Tree.pad, plant_step_self]
          show _ = Tree.pad (plant (.step i q r rest) (.node i q f) e)
          rw [plant_step_self, Tree.pad]
          refine congrArg (fun g => (Tree.node (Fin.padI i) q g
            : Tree (𝕆 ⇒ σ))) (funext fun sr => ?_)
          by_cases hs : sr = r
          · rw [if_pos hs, if_pos hs, plant_pad rest (f sr) e]
          · rw [if_neg hs, if_neg hs]
        · have hne : ¬ ((⟨Fin.padI i, q⟩ : NodeVal (𝕆 ⇒ σ))
              = ⟨Fin.padI j, p⟩) :=
            fun he => h ((padNodeVal_eq_iff i j q p).mp he)
          show plant (.step (Fin.padI i) q r (Query.padQ rest))
              (Tree.pad (Tree.node j p f)) (Tree.pad e) = _
          rw [Tree.pad]
          show (dite _ _ _ : Tree (𝕆 ⇒ σ)) = _
          rw [dif_neg hne]
          show _ = Tree.pad (plant (.step i q r rest) (.node j p f) e)
          show _ = Tree.pad (dite _ _ _ : Tree σ)
          rw [dif_neg h, Tree.pad]

/-- Query well-formedness survives padding: padding touches only the top-level
argument indices, not the recorded responses. -/
theorem QueryOk_padQ {σ : Ty} : ∀ (P : Query σ), QueryOk σ P →
    QueryOk (𝕆 ⇒ σ) (Query.padQ P)
  | .hole, _ => QueryOk_hole
  | .step i q r rest, h => by
      obtain ⟨hs, hrest⟩ := (QueryOk_step i q r rest).mp h
      show QueryOk (𝕆 ⇒ σ) (.step (Fin.padI i) q r (Query.padQ rest))
      exact (QueryOk_step (Fin.padI i) q r (Query.padQ rest)).mpr
        ⟨hs, QueryOk_padQ rest hrest⟩

/-- The context of a padded query is the padded context. -/
theorem ctxFrom_padQ {σ : Ty} : ∀ (P : Query σ) (γ : Ctx σ),
    (Query.padQ P).ctxFrom (Ctx.padC γ) = Ctx.padC (P.ctxFrom γ)
  | .hole, γ => rfl
  | .step i q r rest, γ => by
      show (Query.padQ rest).ctxFrom ((Ctx.padC γ).cons (Fin.padI i) r) = _
      rw [Ctx.padC_cons γ i r]
      exact ctxFrom_padQ rest (γ.cons i r)

/-- Legality survives padding. -/
theorem TreeOk_pad {σ : Ty} {γ : Ctx σ} {t : Tree σ} (h : TreeOk γ t) :
    TreeOk (Ctx.padC γ) (Tree.pad t) := by
  induction h with
  | leaf γ v => exact TreeOk.leaf _ _
  | node γ i q f hq hfin hsub hnon ihsub =>
    rw [Tree.pad]
    refine TreeOk.node (Ctx.padC γ) (Fin.padI i) q _ ?_ ?_
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [Ctx.padC_padI]; exact hq
    · obtain ⟨l, hl⟩ := hfin
      exact ⟨l, fun r hr =>
        hl r (fun hb => hr ((Tree.pad_eq_bot_iff (f r)).mpr hb))⟩
    · rw [Ctx.padC_cons γ i r]
      exact ihsub r hr
    · rw [hnon r hr]
      rfl

/-! ## Iterated padding, probes, and reading a probe back

`Ty.pads m σ` prefixes `σ` with `m` ground arguments.  A *probe* at one of
those arguments, grafted into a padded tree at a perimeter position, is what
the §5 expression `Bₕ` uses to report back: applying the `m` ground arguments
turns the probe into whatever flat value the corresponding argument carries. -/

/-- `𝕆 → … → 𝕆 → σ`, with `m` leading ground arguments. -/
def Ty.pads : Nat → Ty → Ty
  | 0, σ => σ
  | m + 1, σ => 𝕆 ⇒ Ty.pads m σ

theorem Ty.arity_pads : ∀ (m : Nat) (σ : Ty), (Ty.pads m σ).arity = m + σ.arity
  | 0, σ => (Nat.zero_add _).symm
  | m + 1, σ => by
      show (Ty.pads m σ).arity + 1 = _
      rw [Ty.arity_pads m σ]
      omega

/-- Iterated padding of a tree. -/
noncomputable def Tree.padN : ∀ (m : Nat) {σ : Ty}, Tree σ → Tree (Ty.pads m σ)
  | 0, _, t => t
  | m + 1, _, t => Tree.pad (Tree.padN m t)

theorem Tree.padN_leaf : ∀ (m : Nat) {σ : Ty} (v : Val),
    Tree.padN m (Tree.leaf v : Tree σ) = Tree.leaf v
  | 0, _, v => rfl
  | m + 1, σ, v => by
      show Tree.pad (Tree.padN m (Tree.leaf v : Tree σ)) = _
      rw [Tree.padN_leaf m v]
      rfl

/-- Iterated padding of a query. -/
def Query.padQN : ∀ (m : Nat) {σ : Ty}, Query σ → Query (Ty.pads m σ)
  | 0, _, P => P
  | m + 1, _, P => Query.padQ (Query.padQN m P)

/-- Iterated padding of a context. -/
noncomputable def Ctx.padCN : ∀ (m : Nat) {σ : Ty}, Ctx σ → Ctx (Ty.pads m σ)
  | 0, _, γ => γ
  | m + 1, _, γ => Ctx.padC (Ctx.padCN m γ)

theorem Ctx.padCN_empty : ∀ (m : Nat) (σ : Ty),
    Ctx.padCN m (Ctx.empty : Ctx σ) = (Ctx.empty : Ctx (Ty.pads m σ))
  | 0, _ => rfl
  | m + 1, σ => by
      show Ctx.padC (Ctx.padCN m (Ctx.empty : Ctx σ)) = _
      rw [Ctx.padCN_empty m σ]
      exact Ctx.padC_empty

theorem TreeOk_padN : ∀ (m : Nat) {σ : Ty} {γ : Ctx σ} {t : Tree σ}, TreeOk γ t →
    TreeOk (Ctx.padCN m γ) (Tree.padN m t)
  | 0, _, _, _, h => h
  | m + 1, _, _, _, h => TreeOk_pad (TreeOk_padN m h)

theorem QueryOk_padQN : ∀ (m : Nat) {σ : Ty} (P : Query σ), QueryOk σ P →
    QueryOk (Ty.pads m σ) (Query.padQN m P)
  | 0, _, _, h => h
  | m + 1, σ, P, h => QueryOk_padQ (Query.padQN m P) (QueryOk_padQN m P h)

/-- Applying the `m` leading ground arguments. -/
noncomputable def applyFront : ∀ (m : Nat) {σ : Ty}, Tree (Ty.pads m σ) →
    (Nat → Tree 𝕆) → Tree σ
  | 0, _, t, _ => t
  | m + 1, _, t, vs => applyFront m (apply0 t (vs 0)) (fun k => vs (k + 1))

/-- A padded tree ignores every one of the new arguments. -/
theorem applyFront_padN : ∀ (m : Nat) {σ : Ty} (t : Tree σ) (vs : Nat → Tree 𝕆),
    applyFront m (Tree.padN m t) vs = t
  | 0, _, t, vs => rfl
  | m + 1, σ, t, vs => by
      show applyFront m (apply0 (Tree.pad (Tree.padN m t)) (vs 0)) _ = _
      rw [apply0_pad]
      exact applyFront_padN m t _

/-- `applyFront` is monotone in the tree. -/
theorem applyFront_mono : ∀ (m : Nat) {σ : Ty} {t t' : Tree (Ty.pads m σ)}
    (vs : Nat → Tree 𝕆), Tree.Le t t' → Tree.Le (applyFront m t vs)
      (applyFront m t' vs)
  | 0, _, _, _, _, h => h
  | m + 1, σ, t, t', vs, h =>
      applyFront_mono m _ (apply0_mono_left h (vs 0))

/-- Navigation along a padded position survives applying the new arguments. -/
theorem at'_apply0_padQ {σ : Ty} : ∀ (P : Query σ) (t : Tree (𝕆 ⇒ σ))
    (d : Tree 𝕆) (x : Tree (𝕆 ⇒ σ)), t.at' (Query.padQ P) = some x →
    (apply0 t d).at' P = some (apply0 x d)
  | .hole, t, d, x, h => by
      have hx : t = x := by injection h
      rw [hx]
      rfl
  | .step i q r rest, t, d, x, h => by
      have h2 : t.at' (.step (Fin.padI i) q r (Query.padQ rest)) = some x := h
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv h2
      have happ : apply0 (Tree.node (Fin.padI i) q f) d
          = Tree.node i q (fun s => apply0 (f s) d) := by
        simp only [Fin.padI]
        rw [apply0]
      rw [happ, Tree.at'_step_self]
      exact at'_apply0_padQ rest (f r) d x hrest

theorem at'_applyFront : ∀ (m : Nat) {σ : Ty} (P : Query σ)
    (t : Tree (Ty.pads m σ)) (vs : Nat → Tree 𝕆) (x : Tree (Ty.pads m σ)),
    t.at' (Query.padQN m P) = some x →
    (applyFront m t vs).at' P = some (applyFront m x vs)
  | 0, _, P, t, vs, x, h => h
  | m + 1, σ, P, t, vs, x, h => by
      show (applyFront m (apply0 t (vs 0)) _).at' P
        = some (applyFront m (apply0 x (vs 0)) _)
      refine at'_applyFront m P (apply0 t (vs 0)) _ (apply0 x (vs 0)) ?_
      exact at'_apply0_padQ (Query.padQN m P) t (vs 0) x h

/-- Applying the new arguments commutes with planting at a padded position that
the tree actually reaches. -/
theorem apply0_plant_padQ {σ : Ty} : ∀ (P : Query σ) (t e : Tree (𝕆 ⇒ σ))
    (d : Tree 𝕆), (∃ x, t.at' (Query.padQ P) = some x) →
    apply0 (plant (Query.padQ P) t e) d = plant P (apply0 t d) (apply0 e d)
  | .hole, t, e, d, _ => rfl
  | .step i q r rest, t, e, d, ⟨x, hx⟩ => by
      have h2 : t.at' (.step (Fin.padI i) q r (Query.padQ rest)) = some x := hx
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv h2
      have happ : ∀ g : Resp (σ.arg i) → Tree (𝕆 ⇒ σ),
          apply0 (Tree.node (Fin.padI i) q g) d
            = Tree.node i q (fun s => apply0 (g s) d) := by
        intro g
        simp only [Fin.padI]
        rw [apply0]
      show apply0 (plant (.step (Fin.padI i) q r (Query.padQ rest))
        (Tree.node (Fin.padI i) q f) e) d = _
      rw [plant_step_self, happ, happ, plant_step_self]
      refine congrArg (fun g => (Tree.node i q g : Tree σ)) (funext fun sr => ?_)
      by_cases hs : sr = r
      · rw [if_pos hs, if_pos hs]
        subst hs
        exact apply0_plant_padQ rest (f sr) e d ⟨x, hrest⟩
      · rw [if_neg hs, if_neg hs]

theorem applyFront_plant : ∀ (m : Nat) {σ : Ty} (P : Query σ)
    (t e : Tree (Ty.pads m σ)) (vs : Nat → Tree 𝕆),
    (∃ x, t.at' (Query.padQN m P) = some x) →
    applyFront m (plant (Query.padQN m P) t e) vs
      = plant P (applyFront m t vs) (applyFront m e vs)
  | 0, _, P, t, e, vs, _ => rfl
  | m + 1, σ, P, t, e, vs, ⟨x, hx⟩ => by
      show applyFront m (apply0 (plant (Query.padQ (Query.padQN m P)) t e)
        (vs 0)) _ = _
      rw [apply0_plant_padQ (Query.padQN m P) t e (vs 0) ⟨x, hx⟩]
      exact applyFront_plant m P (apply0 t (vs 0)) (apply0 e (vs 0)) _
        ⟨apply0 x (vs 0), at'_apply0_padQ (Query.padQN m P) t (vs 0) x hx⟩

/-- A probe of one of the `m` leading ground arguments. -/
noncomputable def probeT (m : Nat) (σ : Ty) (l : Nat) (hl : l < m) :
    Tree (Ty.pads m σ) :=
  Tree.node ⟨l, by rw [Ty.arity_pads]; omega⟩ Query.hole (fun _ => Tree.bot)

/-- What a probe reports about a flat value. -/
def probeVal (σ : Ty) : Val → Tree σ
  | .err b => .leaf (.err b)
  | _ => Tree.bot

theorem Tree.padN_probeVal (m : Nat) (σ : Ty) (w : Val) :
    Tree.padN m (probeVal σ w) = probeVal (Ty.pads m σ) w := by
  cases w with
  | bot =>
    show Tree.padN m (Tree.bot : Tree σ) = _
    exact Tree.padN_leaf m Val.bot
  | err b =>
    show Tree.padN m (Tree.leaf (Val.err b) : Tree σ) = _
    exact Tree.padN_leaf m (Val.err b)
  | num n =>
    show Tree.padN m (Tree.bot : Tree σ) = _
    exact Tree.padN_leaf m Val.bot

/-- Applying the leading ground arguments to a probe reads off the flat value
the probed argument carries. -/
theorem applyFront_probeT : ∀ (m : Nat) (σ : Ty) (l : Nat) (hl : l < m)
    (vs : Nat → Tree 𝕆) (w : Val), vs l = Tree.leaf w →
    applyFront m (probeT m σ l hl) vs = probeVal σ w
  | 0, _, _, hl, _, _, _ => absurd hl (Nat.not_lt_zero _)
  | m + 1, σ, 0, hl, vs, w, hw => by
      show applyFront m (apply0 (probeT (m + 1) σ 0 hl) (vs 0)) _ = _
      have hcomp : apply0 (probeT (m + 1) σ 0 hl) (vs 0)
          = Tree.padN m (probeVal σ w) := by
        rw [Tree.padN_probeVal, probeT, hw, apply0]
        simp only [Tree.at'_hole]
        cases w <;> rfl
      rw [hcomp, applyFront_padN]
  | m + 1, σ, l + 1, hl, vs, w, hw => by
      show applyFront m (apply0 (probeT (m + 1) σ (l + 1) hl) (vs 0)) _ = _
      have hlm : l < m := Nat.lt_of_succ_lt_succ hl
      have hcomp : apply0 (probeT (m + 1) σ (l + 1) hl) (vs 0)
          = probeT m σ l hlm := by
        rw [probeT, apply0, probeT]
        rfl
      rw [hcomp]
      exact applyFront_probeT m σ l hlm (fun k => vs (k + 1)) w hw

/-- A probe is a legal tree in the empty context. -/
theorem TreeOk_probeT (m : Nat) (σ : Ty) (l : Nat) (hl : l < m) :
    TreeOk (Ctx.empty : Ctx (Ty.pads m σ)) (probeT m σ l hl) := by
  rw [probeT]
  exact TreeOk.node _ _ _ _ LegalQuery.root ⟨[], fun r hr => absurd rfl hr⟩
    (fun r _ => TreeOk.leaf _ _) (fun r _ => rfl)

/-! ## The flat ground domain, as ideals -/

/-- Every ideal at ground type is the principal ideal of a leaf: `T_o` is the
flat domain `ℕ^E_⊥`. -/
theorem T_ground_flat (X : T 𝕆) : ∃ v : Val, X = leafT 𝕆 v := by
  by_cases h : ∀ a, a ∈ X → a = DSub.bot
  · exact ⟨.bot, by rw [T_eq_bot X h]; rfl⟩
  · have hex : ∃ a, a ∈ X ∧ a ≠ DSub.bot := by
      refine Classical.byContradiction fun h2 => h fun a ha => ?_
      exact Classical.byContradiction fun hne => h2 ⟨a, ha, hne⟩
    obtain ⟨a, ha, hane⟩ := hex
    obtain ⟨v, hv⟩ := tree_base_leaf a.1
    refine ⟨v, ?_⟩
    apply Ideal.ext
    intro c
    constructor
    · intro hc
      obtain ⟨u, hu, hcu, hau⟩ := X.directed' c a hc ha
      have hau' : a = u := D_base_flat a u hane hau
      show Tree.Le c.1 (.leaf v)
      rw [← hv]
      exact hau' ▸ hcu
    · intro hc
      have hca : Tree.Le c.1 a.1 := by
        rw [hv]
        exact hc
      exact X.downward c a hca ha

/-! ## `if0` on non-numeric scrutinees -/

/-- `if0` is strict: a `⊥` scrutinee gives `⊥`, whatever the arms. -/
theorem applyT_if0_bot' :
    applyT (idealOf treeIf0) (leafT 𝕆 .bot) = leafT (𝕆 ⇒ 𝕆 ⇒ 𝕆) .bot := by
  rw [treeIf0]
  exact applyT_rootProbe_bot (Nat.succ_pos _) _

/-- `if0` propagates an error in the scrutinee. -/
theorem applyT_if0_err' (b : Bool) :
    applyT (idealOf treeIf0) (leafT 𝕆 (.err b)) = leafT (𝕆 ⇒ 𝕆 ⇒ 𝕆) (.err b) := by
  rw [treeIf0]
  exact applyT_rootProbe_err (Nat.succ_pos _) _ b

/-- The full `if0` chain on a `⊥` scrutinee. -/
theorem applyT_if0_chain_bot (A B : T 𝕆) :
    applyT (applyT (applyT (idealOf treeIf0) (leafT 𝕆 .bot)) A) B
      = leafT 𝕆 .bot := by
  rw [applyT_if0_bot', applyT_leafT, applyT_leafT]

/-- The full `if0` chain on an error scrutinee. -/
theorem applyT_if0_chain_err (b : Bool) (A B : T 𝕆) :
    applyT (applyT (applyT (idealOf treeIf0) (leafT 𝕆 (.err b))) A) B
      = leafT 𝕆 (.err b) := by
  rw [applyT_if0_err', applyT_leafT, applyT_leafT]

/-! ## `sub1` dynamics, unified over the flat values -/

/-- The action of `sub1` on a flat ground value. -/
def sub1Val : Val → Val
  | .num 0 => .bot
  | .num (n + 1) => .num n
  | .bot => .bot
  | .err b => .err b

/-- `sub1` on any flat value. -/
theorem applyT_sub1_leafT (v : Val) :
    applyT (idealOf treeSub1) (leafT 𝕆 v) = leafT 𝕆 (sub1Val v) := by
  cases v with
  | bot => exact applyT_sub1_bot
  | err b => exact applyT_sub1_err b
  | num n =>
    cases n with
    | zero => exact applyT_sub1_zero'
    | succ n => exact applyT_sub1_succ n

/-! ## Meanings of applications, in any environment -/

/-- The meaning of a term-level application, given the argument's type. -/
theorem meaning_app_term (Env : Tmodel.Env) (M N : Term SPCF) (a ρ : Ty)
    (Γ : List (Nat × Ty)) (hN : Term.HasTy Γ N a) :
    Tmodel.meaning Env (.app M N) ρ
      = applyT (Tmodel.meaning Env M (a ⇒ ρ)) (Tmodel.meaning Env N a) := by
  show Tmodel.combMeaning Env (.app (Term.toComb M) (Term.toComb N)) ρ = _
  rw [meaning_app Tmodel Env _ _ a ρ (Term.tyOf_toComb hN)]
  rfl

/-- The meaning of a fully applied `if0`. -/
theorem meaning_if0 (Env : Tmodel.Env) (S A B : Term SPCF)
    (Γ : List (Nat × Ty)) (hS : Term.HasTy Γ S 𝕆) (hA : Term.HasTy Γ A 𝕆)
    (hB : Term.HasTy Γ B 𝕆) :
    Tmodel.meaning Env (.app (.app (.app (.const .if0) S) A) B) 𝕆
      = applyT (applyT (applyT (idealOf treeIf0)
          (Tmodel.meaning Env S 𝕆))
          (Tmodel.meaning Env A 𝕆))
          (Tmodel.meaning Env B 𝕆) := by
  rw [meaning_app_term Env _ B 𝕆 𝕆 Γ hB,
    meaning_app_term Env _ A 𝕆 (𝕆 ⇒ 𝕆) Γ hA,
    meaning_app_term Env _ S 𝕆 (𝕆 ⇒ 𝕆 ⇒ 𝕆) Γ hS]
  have hc : Tmodel.meaning Env (.const .if0) (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆)
      = idealOf treeIf0 := by
    exact Model.combMeaning_const Tmodel Env SConst.if0
  rw [hc]

/-- The meaning of an applied `sub1`. -/
theorem meaning_sub1 (Env : Tmodel.Env) (N : Term SPCF)
    (Γ : List (Nat × Ty)) (hN : Term.HasTy Γ N 𝕆) :
    Tmodel.meaning Env (.app (.const .sub1) N) 𝕆
      = applyT (idealOf treeSub1) (Tmodel.meaning Env N 𝕆) := by
  rw [meaning_app_term Env _ N 𝕆 𝕆 Γ hN]
  have hc : Tmodel.meaning Env (.const .sub1) (𝕆 ⇒ 𝕆)
      = idealOf treeSub1 := by
    exact Model.combMeaning_const Tmodel Env SConst.sub1
  rw [hc]

/-- `Ω` is well typed in any context. -/
theorem hasTy_omegaTerm' (Γ : List (Nat × Ty)) : Term.HasTy Γ omegaTerm 𝕆 :=
  Term.HasTy.app Term.HasTy.const Term.HasTy.const

/-- `Ω` denotes `⊥` in every environment, as a `leafT`. -/
theorem meaning_omegaTerm' (Env : Tmodel.Env) :
    Tmodel.meaning Env omegaTerm 𝕆 = leafT 𝕆 .bot := by
  rw [meaning_omegaTerm Env]
  rfl

/-! ## The `sub1⊥` procedure and its iterates (§5)

`sub1⊥ = λx.(if0 x Ω (sub1 x))` is "identical to `sub1` except that it
diverges on the input `0`". -/

/-- `sub1⊥`. -/
def sub1BotTerm : Term SPCF :=
  .lam 0 𝕆 (.app (.app (.app (.const .if0) (.var 0 𝕆)) omegaTerm)
    (.app (.const .sub1) (.var 0 𝕆)))

theorem sub1BotTerm_hasTy (Γ : List (Nat × Ty)) :
    Term.HasTy Γ sub1BotTerm (𝕆 ⇒ 𝕆) := by
  refine Term.HasTy.lam (Term.HasTy.app (Term.HasTy.app (Term.HasTy.app
    Term.HasTy.const (Term.HasTy.var (List.mem_cons_self ..)))
    (Term.HasTy.app Term.HasTy.const Term.HasTy.const))
    (Term.HasTy.app Term.HasTy.const (Term.HasTy.var (List.mem_cons_self ..))))

theorem sub1BotTerm_closed : Term.Closed sub1BotTerm := by
  rintro p ⟨(((hp | hp) | (hp | hp)) | (hp | hp)), hne⟩ <;>
    first | exact hp | exact hne hp

/-- The action of `sub1⊥` on a flat value: as `sub1`, except `⊥` at `0`. -/
def sub1BotVal : Val → Val
  | .num 0 => .bot
  | .num (n + 1) => .num n
  | .bot => .bot
  | .err b => .err b

/-- `sub1⊥` applied to a flat value. -/
theorem sub1BotTerm_apply (Env : Tmodel.Env) (v : Val) :
    applyT (Tmodel.meaning Env sub1BotTerm (𝕆 ⇒ 𝕆)) (leafT 𝕆 v)
      = leafT 𝕆 (sub1BotVal v) := by
  have hbodyTy : Term.HasTy [(0, 𝕆)]
      (Term.app (Term.app (Term.app (Term.const .if0) (Term.var 0 𝕆)) omegaTerm)
        (Term.app (Term.const .sub1) (Term.var 0 𝕆)) : Term SPCF) 𝕆 :=
    Term.HasTy.app (Term.HasTy.app (Term.HasTy.app Term.HasTy.const
      (Term.HasTy.var (List.mem_cons_self ..)))
      (Term.HasTy.app Term.HasTy.const Term.HasTy.const))
      (Term.HasTy.app Term.HasTy.const (Term.HasTy.var (List.mem_cons_self ..)))
  have hpeel : applyT (Tmodel.meaning Env sub1BotTerm (𝕆 ⇒ 𝕆)) (leafT 𝕆 v)
      = Tmodel.meaning (Model.envUpdate Env 0 𝕆 (leafT 𝕆 v))
          (Term.app (Term.app (Term.app (Term.const .if0) (Term.var 0 𝕆)) omegaTerm)
            (Term.app (Term.const .sub1) (Term.var 0 𝕆))) 𝕆 := by
    show applyT (Tmodel.combMeaning Env (Comb.lamStar 0 𝕆 _) (𝕆 ⇒ 𝕆)) _ = _
    exact lamStar_apply Env 0 𝕆 (leafT 𝕆 v) _ 𝕆 []
      (Term.toComb_hasTy hbodyTy)
  rw [hpeel]
  have hvar : Tmodel.meaning (Model.envUpdate Env 0 𝕆 (leafT 𝕆 v))
      (Term.var 0 𝕆) 𝕆 = leafT 𝕆 v := by
    show Tmodel.combMeaning _ (.var 0 𝕆) 𝕆 = _
    rw [Model.combMeaning_var, Model.envUpdate_self]
  rw [meaning_if0 (Model.envUpdate Env 0 𝕆 (leafT 𝕆 v)) (.var 0 𝕆) omegaTerm
      (.app (.const .sub1) (.var 0 𝕆)) ([(0, 𝕆)])
      (Term.HasTy.var (List.mem_cons_self ..))
      (hasTy_omegaTerm' _)
      (Term.HasTy.app Term.HasTy.const (Term.HasTy.var (List.mem_cons_self ..))),
    hvar,
    meaning_sub1 (Model.envUpdate Env 0 𝕆 (leafT 𝕆 v)) (.var 0 𝕆) ([(0, 𝕆)])
      (Term.HasTy.var (List.mem_cons_self ..)),
    hvar, meaning_omegaTerm' _, applyT_sub1_leafT]
  cases v with
  | bot => exact applyT_if0_chain_bot _ _
  | err b => exact applyT_if0_chain_err b _ _
  | num n =>
    cases n with
    | zero =>
      have h := applyT_if0_chain 0 ⟨.leaf .bot, TreeOk.leaf _ _⟩
        ⟨.leaf (sub1Val (.num 0)), TreeOk.leaf _ _⟩
      rw [show (natAns 0 : T 𝕆) = leafT 𝕆 (.num 0) from rfl] at h
      rw [show (Ideal.principal ⟨.leaf .bot, TreeOk.leaf _ _⟩ : T 𝕆)
          = leafT 𝕆 .bot from rfl] at h
      rw [show (Ideal.principal ⟨.leaf (sub1Val (.num 0)), TreeOk.leaf _ _⟩ : T 𝕆)
          = leafT 𝕆 (sub1Val (.num 0)) from rfl] at h
      rw [h, if_pos rfl]
      rfl
    | succ n =>
      have h := applyT_if0_chain (n + 1) ⟨.leaf .bot, TreeOk.leaf _ _⟩
        ⟨.leaf (sub1Val (.num (n + 1))), TreeOk.leaf _ _⟩
      rw [show (natAns (n + 1) : T 𝕆) = leafT 𝕆 (.num (n + 1)) from rfl] at h
      rw [show (Ideal.principal ⟨.leaf .bot, TreeOk.leaf _ _⟩ : T 𝕆)
          = leafT 𝕆 .bot from rfl] at h
      rw [show (Ideal.principal ⟨.leaf (sub1Val (.num (n + 1))), TreeOk.leaf _ _⟩ : T 𝕆)
          = leafT 𝕆 (sub1Val (.num (n + 1))) from rfl] at h
      rw [h, if_neg (by omega)]
      rfl

/-- `(sub1⊥^c N)`: the `c`-fold application of `sub1⊥` to `N`. -/
def subIter : Nat → Term SPCF → Term SPCF
  | 0, N => N
  | c + 1, N => .app sub1BotTerm (subIter c N)

theorem subIter_hasTy (c : Nat) (N : Term SPCF) (Γ : List (Nat × Ty))
    (hN : Term.HasTy Γ N 𝕆) : Term.HasTy Γ (subIter c N) 𝕆 := by
  induction c with
  | zero => exact hN
  | succ c ih => exact Term.HasTy.app (sub1BotTerm_hasTy Γ) ih

/-- The value of the `c`-fold `sub1⊥`. -/
def subIterVal : Nat → Val → Val
  | 0, v => v
  | c + 1, v => sub1BotVal (subIterVal c v)

theorem subIterVal_bot (c : Nat) : subIterVal c .bot = .bot := by
  induction c with
  | zero => rfl
  | succ c ih => show sub1BotVal (subIterVal c .bot) = _; rw [ih]; rfl

theorem subIterVal_err (c : Nat) (b : Bool) : subIterVal c (.err b) = .err b := by
  induction c with
  | zero => rfl
  | succ c ih => show sub1BotVal (subIterVal c (.err b)) = _; rw [ih]; rfl

theorem subIterVal_num_le (c u : Nat) (h : c ≤ u) :
    subIterVal c (.num u) = .num (u - c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show sub1BotVal (subIterVal c (.num u)) = _
    rw [ih (by omega)]
    have h2 : u - c = (u - (c + 1)) + 1 := by omega
    rw [h2]
    rfl

theorem subIterVal_num_lt (c u : Nat) (h : u < c) :
    subIterVal c (.num u) = .bot := by
  induction c with
  | zero => omega
  | succ c ih =>
    show sub1BotVal (subIterVal c (.num u)) = _
    by_cases hc : u < c
    · rw [ih hc]; rfl
    · have hu : u = c := by omega
      subst hu
      rw [subIterVal_num_le u u (Nat.le_refl _), Nat.sub_self]
      rfl

/-- The meaning of `(sub1⊥^c N)` on a flat value. -/
theorem subIter_meaning (Env : Tmodel.Env) (c : Nat) (N : Term SPCF)
    (Γ : List (Nat × Ty)) (hN : Term.HasTy Γ N 𝕆) (v : Val)
    (hv : Tmodel.meaning Env N 𝕆 = leafT 𝕆 v) :
    Tmodel.meaning Env (subIter c N) 𝕆 = leafT 𝕆 (subIterVal c v) := by
  induction c with
  | zero => exact hv
  | succ c ih =>
    show Tmodel.meaning Env (.app sub1BotTerm (subIter c N)) 𝕆 = _
    rw [meaning_app_term Env _ _ 𝕆 𝕆 Γ (subIter_hasTy c N Γ hN), ih]
    exact sub1BotTerm_apply Env (subIterVal c v)

/-! ## The sequential case split of §5

`cascadeTerm W arms` is the paper's nest
`(if0 (sub1⊥^{v₁} W) A₁ (if0 (sub1⊥^{v₂} W) A₂ … Ω))`, testing the scrutinee
`W` against the ascending values `vⱼ` and dispatching to the arm `Aⱼ`. -/

/-- The nested sequential case split on `W`. -/
def cascadeTerm (W : Term SPCF) : List (Nat × Term SPCF) → Term SPCF
  | [] => .app (.app (.app (.const .if0) W) omegaTerm) omegaTerm
  | (c, A) :: arms =>
      .app (.app (.app (.const .if0) (subIter c W)) A) (cascadeTerm W arms)

theorem cascadeTerm_hasTy (W : Term SPCF) (arms : List (Nat × Term SPCF))
    (Γ : List (Nat × Ty)) (hW : Term.HasTy Γ W 𝕆)
    (harms : ∀ p ∈ arms, Term.HasTy Γ p.2 𝕆) :
    Term.HasTy Γ (cascadeTerm W arms) 𝕆 := by
  induction arms with
  | nil =>
    exact Term.HasTy.app (Term.HasTy.app (Term.HasTy.app Term.HasTy.const hW)
      (hasTy_omegaTerm' Γ)) (hasTy_omegaTerm' Γ)
  | cons p arms ih =>
    obtain ⟨c, A⟩ := p
    exact Term.HasTy.app (Term.HasTy.app (Term.HasTy.app Term.HasTy.const
      (subIter_hasTy c W Γ hW)) (harms (c, A) (List.mem_cons_self ..)))
      (ih (fun p hp => harms p (List.mem_cons_of_mem _ hp)))

/-- The cascade is strict: `⊥` scrutinee gives `⊥`. -/
theorem cascade_bot (Env : Tmodel.Env) (W : Term SPCF)
    (arms : List (Nat × Term SPCF)) (Γ : List (Nat × Ty))
    (hWty : Term.HasTy Γ W 𝕆) (harms : ∀ p ∈ arms, Term.HasTy Γ p.2 𝕆)
    (hW : Tmodel.meaning Env W 𝕆 = leafT 𝕆 .bot) :
    Tmodel.meaning Env (cascadeTerm W arms) 𝕆 = leafT 𝕆 .bot := by
  cases arms with
  | nil =>
    rw [show cascadeTerm W []
        = .app (.app (.app (.const .if0) W) omegaTerm) omegaTerm from rfl,
      meaning_if0 Env W omegaTerm omegaTerm Γ hWty
        (hasTy_omegaTerm' Γ) (hasTy_omegaTerm' Γ), hW]
    exact applyT_if0_chain_bot _ _
  | cons p arms =>
    obtain ⟨c, A⟩ := p
    rw [show cascadeTerm W ((c, A) :: arms)
        = .app (.app (.app (.const .if0) (subIter c W)) A) (cascadeTerm W arms)
        from rfl,
      meaning_if0 Env (subIter c W) A (cascadeTerm W arms) Γ
        (subIter_hasTy c W Γ hWty)
        (harms (c, A) (List.mem_cons_self ..))
        (cascadeTerm_hasTy W arms Γ hWty
          (fun p hp => harms p (List.mem_cons_of_mem _ hp))),
      subIter_meaning Env c W Γ hWty .bot hW, subIterVal_bot]
    exact applyT_if0_chain_bot _ _

/-- The cascade propagates an error in the scrutinee. -/
theorem cascade_err (Env : Tmodel.Env) (W : Term SPCF)
    (arms : List (Nat × Term SPCF)) (Γ : List (Nat × Ty)) (b : Bool)
    (hWty : Term.HasTy Γ W 𝕆) (harms : ∀ p ∈ arms, Term.HasTy Γ p.2 𝕆)
    (hW : Tmodel.meaning Env W 𝕆 = leafT 𝕆 (.err b)) :
    Tmodel.meaning Env (cascadeTerm W arms) 𝕆 = leafT 𝕆 (.err b) := by
  cases arms with
  | nil =>
    rw [show cascadeTerm W []
        = .app (.app (.app (.const .if0) W) omegaTerm) omegaTerm from rfl,
      meaning_if0 Env W omegaTerm omegaTerm Γ hWty
        (hasTy_omegaTerm' Γ) (hasTy_omegaTerm' Γ), hW]
    exact applyT_if0_chain_err b _ _
  | cons p arms =>
    obtain ⟨c, A⟩ := p
    rw [show cascadeTerm W ((c, A) :: arms)
        = .app (.app (.app (.const .if0) (subIter c W)) A) (cascadeTerm W arms)
        from rfl,
      meaning_if0 Env (subIter c W) A (cascadeTerm W arms) Γ
        (subIter_hasTy c W Γ hWty)
        (harms (c, A) (List.mem_cons_self ..))
        (cascadeTerm_hasTy W arms Γ hWty
          (fun p hp => harms p (List.mem_cons_of_mem _ hp))),
      subIter_meaning Env c W Γ hWty (.err b) hW, subIterVal_err]
    exact applyT_if0_chain_err b _ _

/-- The if0 chain with a numeric scrutinee, in `leafT` form. -/
theorem applyT_if0_chain' (u : Nat) (A B : T 𝕆) :
    applyT (applyT (applyT (idealOf treeIf0) (leafT 𝕆 (.num u))) A) B
      = if u = 0 then A else B := by
  obtain ⟨va, hva⟩ := T_ground_flat A
  obtain ⟨vb, hvb⟩ := T_ground_flat B
  subst hva hvb
  have h := applyT_if0_chain u ⟨.leaf va, TreeOk.leaf _ _⟩ ⟨.leaf vb, TreeOk.leaf _ _⟩
  rw [show (natAns u : T 𝕆) = leafT 𝕆 (.num u) from rfl] at h
  rw [show (Ideal.principal ⟨.leaf va, TreeOk.leaf _ _⟩ : T 𝕆) = leafT 𝕆 va from rfl,
    show (Ideal.principal ⟨.leaf vb, TreeOk.leaf _ _⟩ : T 𝕆) = leafT 𝕆 vb from rfl] at h
  rw [h]
  by_cases hu : u = 0
  · rw [if_pos hu, if_pos hu]
    rfl
  · rw [if_neg hu, if_neg hu]
    rfl

/-- A numeric scrutinee matching no arm sends the cascade to `⊥`. -/
theorem cascade_num_miss (Env : Tmodel.Env) (W : Term SPCF)
    (arms : List (Nat × Term SPCF)) (Γ : List (Nat × Ty)) (u : Nat)
    (hWty : Term.HasTy Γ W 𝕆) (harms : ∀ p ∈ arms, Term.HasTy Γ p.2 𝕆)
    (hW : Tmodel.meaning Env W 𝕆 = leafT 𝕆 (.num u))
    (hmiss : ∀ p ∈ arms, p.1 ≠ u) :
    Tmodel.meaning Env (cascadeTerm W arms) 𝕆 = leafT 𝕆 .bot := by
  induction arms with
  | nil =>
    rw [show cascadeTerm W []
        = .app (.app (.app (.const .if0) W) omegaTerm) omegaTerm from rfl,
      meaning_if0 Env W omegaTerm omegaTerm Γ hWty
        (hasTy_omegaTerm' Γ) (hasTy_omegaTerm' Γ), hW,
      applyT_if0_chain' u _ _, meaning_omegaTerm' Env]
    by_cases hu : u = 0
    · rw [if_pos hu]
    · rw [if_neg hu]
  | cons p arms ih =>
    obtain ⟨c, A⟩ := p
    rw [show cascadeTerm W ((c, A) :: arms)
        = .app (.app (.app (.const .if0) (subIter c W)) A) (cascadeTerm W arms)
        from rfl,
      meaning_if0 Env (subIter c W) A (cascadeTerm W arms) Γ
        (subIter_hasTy c W Γ hWty)
        (harms (c, A) (List.mem_cons_self ..))
        (cascadeTerm_hasTy W arms Γ hWty
          (fun p hp => harms p (List.mem_cons_of_mem _ hp))),
      subIter_meaning Env c W Γ hWty (.num u) hW]
    by_cases hcu : c ≤ u
    · have hne : c ≠ u := hmiss (c, A) (List.mem_cons_self ..)
      rw [subIterVal_num_le c u hcu, applyT_if0_chain' (u - c) _ _,
        if_neg (by omega)]
      exact ih (fun p hp => harms p (List.mem_cons_of_mem _ hp))
        (fun p hp => hmiss p (List.mem_cons_of_mem _ hp))
    · rw [subIterVal_num_lt c u (by omega)]
      exact applyT_if0_chain_bot _ _

/-- A numeric scrutinee matching an arm of the (strictly ascending) cascade
dispatches to that arm. -/
theorem cascade_num_hit (Env : Tmodel.Env) (W : Term SPCF)
    (arms : List (Nat × Term SPCF)) (Γ : List (Nat × Ty)) (u : Nat)
    (A : Term SPCF)
    (hWty : Term.HasTy Γ W 𝕆) (harms : ∀ p ∈ arms, Term.HasTy Γ p.2 𝕆)
    (hsorted : List.Pairwise (fun p q => p.1 < q.1) arms)
    (hW : Tmodel.meaning Env W 𝕆 = leafT 𝕆 (.num u))
    (hmem : (u, A) ∈ arms) :
    Tmodel.meaning Env (cascadeTerm W arms) 𝕆 = Tmodel.meaning Env A 𝕆 := by
  induction arms with
  | nil => cases hmem
  | cons p arms ih =>
    obtain ⟨c, A₀⟩ := p
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    rw [show cascadeTerm W ((c, A₀) :: arms)
        = .app (.app (.app (.const .if0) (subIter c W)) A₀) (cascadeTerm W arms)
        from rfl,
      meaning_if0 Env (subIter c W) A₀ (cascadeTerm W arms) Γ
        (subIter_hasTy c W Γ hWty)
        (harms (c, A₀) (List.mem_cons_self ..))
        (cascadeTerm_hasTy W arms Γ hWty
          (fun p hp => harms p (List.mem_cons_of_mem _ hp))),
      subIter_meaning Env c W Γ hWty (.num u) hW]
    rcases List.mem_cons.mp hmem with heq | htl
    · injection heq with h1 h2
      subst h1 h2
      rw [subIterVal_num_le u u (Nat.le_refl _), Nat.sub_self,
        applyT_if0_chain' 0 _ _, if_pos rfl]
    · have hcu : c < u := hhead (u, A) htl
      rw [subIterVal_num_le c u (by omega), applyT_if0_chain' (u - c) _ _,
        if_neg (by omega)]
      exact ih (fun p hp => harms p (List.mem_cons_of_mem _ hp)) htail htl

end FA
