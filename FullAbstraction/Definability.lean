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
theorem meaning_apps_env : ∀ (σ : Ty) (Env : Tmodel.Env) (Γ : List (Nat × Ty))
    (M : Term SPCF) (E : (i : Fin σ.arity) → Term SPCF)
    (ds : (i : Fin σ.arity) → T (σ.arg i)),
    (∀ i, Term.HasTy Γ (E i) (σ.arg i)) →
    (∀ i, Tmodel.meaning Env (E i) (σ.arg i) = ds i) →
    Tmodel.meaning Env (Term.apps M (List.ofFn E)) 𝕆
      = applyIdeals σ (Tmodel.meaning Env M σ) ds
  | .base, Env, Γ, M, E, ds, _, _ => by
      show Tmodel.meaning Env (Term.apps M (List.ofFn E)) 𝕆 = _
      rw [show (List.ofFn E : List (Term SPCF)) = [] from List.ofFn_zero]
      rfl
  | .arrow a τ, Env, Γ, M, E, ds, hty, hE => by
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
        meaning_apps_env τ Env Γ (.app M (E ⟨0, Nat.succ_pos _⟩))
          (fun i => E ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => hty ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => hE ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)]
      show applyIdeals τ (Tmodel.combMeaning Env
        (.app (Term.toComb M) (Term.toComb (E ⟨0, Nat.succ_pos _⟩))) τ) _ = _
      rw [meaning_app Tmodel Env _ _ a τ (Term.tyOf_toComb (hty ⟨0, Nat.succ_pos _⟩))]
      have h0 : Tmodel.combMeaning Env (Term.toComb (E ⟨0, Nat.succ_pos _⟩)) a
          = ds ⟨0, Nat.succ_pos _⟩ := hE ⟨0, Nat.succ_pos _⟩
      rw [h0]
      rfl

/-- The meaning of `(M E₁ … Eₖ)` is `apply (T[[M]], T[[E₁]], …, T[[Eₖ]])`.

This is what makes the applicative context `C[·] = ([·] E₁ … Eₖ)` of the proof
of Theorem 5.1 compute the `k`-ary application of the meanings. -/
theorem meaning_apps (σ : Ty) (M : Term SPCF) (E : (i : Fin σ.arity) → Term SPCF)
    (ds : (i : Fin σ.arity) → T (σ.arg i))
    (hty : ∀ i, Term.HasTy [] (E i) (σ.arg i))
    (hE : ∀ i, Tmodel.meaning botEnv (E i) (σ.arg i) = ds i) :
    Tmodel.meaning botEnv (Term.apps M (List.ofFn E)) 𝕆
      = applyIdeals σ (Tmodel.meaning botEnv M σ) ds :=
  meaning_apps_env σ botEnv [] M E ds hty hE

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
noncomputable def probeT (m : Nat) (σ : Ty) (l : Nat) : Tree (Ty.pads m σ) :=
  if h : l < (Ty.pads m σ).arity then
    Tree.node ⟨l, h⟩ Query.hole (fun _ => Tree.bot)
  else Tree.bot

theorem probeT_lt (m : Nat) (σ : Ty) (l : Nat) (hl : l < m) :
    probeT m σ l = Tree.node ⟨l, by rw [Ty.arity_pads]; omega⟩ Query.hole
      (fun _ => Tree.bot) := by
  rw [probeT, dif_pos]

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
    applyFront m (probeT m σ l) vs = probeVal σ w
  | 0, _, _, hl, _, _, _ => absurd hl (Nat.not_lt_zero _)
  | m + 1, σ, 0, hl, vs, w, hw => by
      show applyFront m (apply0 (probeT (m + 1) σ 0) (vs 0)) _ = _
      have hcomp : apply0 (probeT (m + 1) σ 0) (vs 0)
          = Tree.padN m (probeVal σ w) := by
        rw [Tree.padN_probeVal, probeT_lt (m + 1) σ 0 hl, hw, apply0]
        simp only [Tree.at'_hole]
        cases w <;> rfl
      rw [hcomp, applyFront_padN]
  | m + 1, σ, l + 1, hl, vs, w, hw => by
      show applyFront m (apply0 (probeT (m + 1) σ (l + 1)) (vs 0)) _ = _
      have hlm : l < m := Nat.lt_of_succ_lt_succ hl
      have hcomp : apply0 (probeT (m + 1) σ (l + 1)) (vs 0)
          = probeT m σ l := by
        rw [probeT_lt (m + 1) σ (l + 1) hl, apply0, probeT_lt m σ l hlm]
        rfl
      rw [hcomp]
      exact applyFront_probeT m σ l hlm (fun k => vs (k + 1)) w hw

/-- A probe is a legal tree in the empty context. -/
theorem TreeOk_probeT (m : Nat) (σ : Ty) (l : Nat) (hl : l < m) :
    TreeOk (Ctx.empty : Ctx (Ty.pads m σ)) (probeT m σ l) := by
  rw [probeT_lt m σ l hl]
  exact TreeOk.node _ _ _ _ LegalQuery.root ⟨[], fun r hr => absurd rfl hr⟩
    (fun r _ => TreeOk.leaf _ _) (fun r _ => rfl)

/-! ## Grafting probes into a padded tree

`graftT m base ps` plants, for each `(l, P)` in `ps`, a probe of the `l`-th new
ground argument at the position `P` of the padded `base`.  The positions are
perimeter positions of `base`, so the plants do not disturb one another. -/

/-- Planting at one perimeter position leaves another one untouched — the
version needed when the other position already carries a planted subtree.  The
two positions are perimeter positions of a common tree, so neither extends the
other. -/
theorem at'_plant_disjoint {σ : Ty} : ∀ (P' P : Query σ) (base d e x : Tree σ),
    base.at' P = some Tree.bot → base.at' P' = some Tree.bot → P ≠ P' →
    d.at' P' = some x → (plant P d e).at' P' = some x
  | .hole, P, base, d, e, x, hbP, hbP', hne, hd => by
      have hbb : base = Tree.bot := by injection hbP'
      subst hbb
      cases P with
      | hole => exact absurd rfl hne
      | step i p r rest =>
        exact absurd hbP (by simp [Tree.at', Tree.stepAt, Tree.bot])
  | .step j p' s rest', .hole, base, d, e, x, hbP, hbP', hne, hd => by
      have hbb : base = Tree.bot := by injection hbP
      subst hbb
      exact absurd hbP' (by simp [Tree.at', Tree.stepAt, Tree.bot])
  | .step j p' s rest', .step i p r rest, base, d, e, x, hbP, hbP', hne, hd => by
      obtain ⟨fb, rfl, hbrest⟩ := at'_step_inv hbP
      obtain ⟨fb', hb', hbrest'⟩ := at'_step_inv hbP'
      injection hb' with hjj hpp hff
      subst hjj
      have hp2 : p = p' := eq_of_heq hpp
      subst hp2
      have hf2 : fb = fb' := eq_of_heq hff
      subst hf2
      obtain ⟨g, rfl, hdrest⟩ := at'_step_inv hd
      rw [plant_step_self, Tree.at'_step_self]
      by_cases hrs : s = r
      · subst hrs
        rw [if_pos rfl]
        refine at'_plant_disjoint rest' rest (fb s) (g s) e x hbrest hbrest'
          (fun hc => hne ?_) hdrest
        rw [hc]
      · rw [if_neg hrs]
        exact hdrest

/-- Iterated `at'` under padding. -/
theorem at'_padN : ∀ (m : Nat) {σ : Ty} (P : Query σ) (t x : Tree σ),
    t.at' P = some x →
    (Tree.padN m t).at' (Query.padQN m P) = some (Tree.padN m x)
  | 0, _, P, t, x, h => h
  | m + 1, σ, P, t, x, h => by
      show (Tree.pad (Tree.padN m t)).at' (Query.padQ (Query.padQN m P)) = _
      rw [at'_pad (Query.padQN m P) (Tree.padN m t),
        at'_padN m P t x h]
      rfl

theorem Query.padQ_inj {σ : Ty} : ∀ {P P' : Query σ},
    Query.padQ P = Query.padQ P' → P = P'
  | .hole, .hole, _ => rfl
  | .hole, .step _ _ _ _, h => Query.noConfusion h
  | .step _ _ _ _, .hole, h => Query.noConfusion h
  | .step i q r rest, .step i' q' r' rest', h => by
      injection h with _ h1 h2 h3 h4
      cases Fin.padI_inj h1
      cases (eq_of_heq h2 : q = q')
      cases (eq_of_heq h3 : r = r')
      rw [Query.padQ_inj h4]

theorem Query.padQN_inj : ∀ (m : Nat) {σ : Ty} {P P' : Query σ},
    Query.padQN m P = Query.padQN m P' → P = P'
  | 0, _, _, _, h => h
  | m + 1, σ, P, P', h =>
      Query.padQN_inj m (Query.padQ_inj
        (h : Query.padQ (Query.padQN m P) = Query.padQ (Query.padQN m P')))

/-- The grafted tree: probes of the new ground arguments, planted at perimeter
positions of a padded tree. -/
noncomputable def graftT (m : Nat) {σ : Ty} (base : Tree σ) :
    List (Nat × Query σ) → Tree (Ty.pads m σ)
  | [] => Tree.padN m base
  | p :: ps => plant (Query.padQN m p.2) (graftT m base ps)
      (probeT m σ p.1)

/-- The positions of a graft: perimeter positions of the base, pairwise
distinct. -/
def GoodPositions {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)) : Prop :=
  (∀ p ∈ ps, base.at' p.2 = some Tree.bot) ∧
    List.Pairwise (fun p q : Nat × Query σ => p.2 ≠ q.2) ps

/-- A position of the base that no probe occupies is still a perimeter position
of the graft. -/
theorem at'_graftT_bot : ∀ (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)), GoodPositions base ps →
    ∀ P : Query σ, base.at' P = some Tree.bot → (∀ p ∈ ps, p.2 ≠ P) →
    (graftT m base ps).at' (Query.padQN m P) = some Tree.bot
  | m, σ, base, [], _, P, hP, _ => by
      show (Tree.padN m base).at' (Query.padQN m P) = _
      rw [at'_padN m P base Tree.bot hP]
      show some (Tree.padN m (Tree.leaf Val.bot)) = _
      rw [Tree.padN_leaf]
      rfl
  | m, σ, base, p :: ps, ⟨hall, hpair⟩, P, hP, hnotin => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hgood : GoodPositions base ps :=
        ⟨fun q hq => hall q (List.mem_cons_of_mem _ hq), htail⟩
      have hrec := at'_graftT_bot m base ps hgood P hP
        (fun q hq => hnotin q (List.mem_cons_of_mem _ hq))
      have hhead2 := at'_graftT_bot m base ps hgood p.2
        (hall p (List.mem_cons_self ..))
        (fun q hq => Ne.symm (hhead q hq))
      show (plant (Query.padQN m p.2) (graftT m base ps)
        (probeT m σ p.1)).at' (Query.padQN m P) = _
      exact at'_plant_other (Query.padQN m p.2) _ _ (Query.padQN m P)
        hhead2 hrec (fun hc => hnotin p (List.mem_cons_self ..)
          (Query.padQN_inj m hc))

/-- The graft only grows the padded base. -/
theorem le_graftT : ∀ (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)), GoodPositions base ps →
    Tree.Le (Tree.padN m base) (graftT m base ps)
  | m, σ, base, [], _ => Tree.Le.refl _
  | m, σ, base, p :: ps, ⟨hall, hpair⟩ => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hgood : GoodPositions base ps :=
        ⟨fun q hq => hall q (List.mem_cons_of_mem _ hq), htail⟩
      refine Tree.Le.trans (le_graftT m base ps hgood) ?_
      exact le_plant (Query.padQN m p.2) _ _
        (at'_graftT_bot m base ps hgood p.2 (hall p (List.mem_cons_self ..))
          (fun q hq => Ne.symm (hhead q hq)))

/-- Each probe sits at its position in the graft. -/
theorem at'_graftT_probe : ∀ (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)), GoodPositions base ps →
    ∀ p ∈ ps, (graftT m base ps).at' (Query.padQN m p.2)
      = some (probeT m σ p.1)
  | m, σ, base, [], _, p, hp => absurd hp (by simp)
  | m, σ, base, q :: ps, ⟨hall, hpair⟩, p, hp => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hgood : GoodPositions base ps :=
        ⟨fun r hr => hall r (List.mem_cons_of_mem _ hr), htail⟩
      have hqbot := at'_graftT_bot m base ps hgood q.2
        (hall q (List.mem_cons_self ..)) (fun r hr => Ne.symm (hhead r hr))
      show (plant (Query.padQN m q.2) (graftT m base ps)
        (probeT m σ q.1)).at' (Query.padQN m p.2) = _
      rcases List.mem_cons.mp hp with rfl | htl
      · rw [at'_plant_self (Query.padQN m p.2) _ _ ⟨Tree.bot, hqbot⟩]
      · have hne : q.2 ≠ p.2 := hhead p htl
        refine at'_plant_disjoint (Query.padQN m p.2) (Query.padQN m q.2)
          (Tree.padN m base) _ _ _ ?_ ?_
          (fun hc => hne (Query.padQN_inj m hc)) ?_
        · exact at'_padN m q.2 base Tree.bot (hall q (List.mem_cons_self ..))
            |>.trans (by rw [show Tree.padN m (Tree.bot : Tree σ)
              = (Tree.bot : Tree (Ty.pads m σ)) from Tree.padN_leaf m Val.bot])
        · exact at'_padN m p.2 base Tree.bot
            (hall p (List.mem_cons_of_mem _ htl))
            |>.trans (by rw [show Tree.padN m (Tree.bot : Tree σ)
              = (Tree.bot : Tree (Ty.pads m σ)) from Tree.padN_leaf m Val.bot])
        · exact at'_graftT_probe m base ps hgood p htl

/-- **The graft, seen from the outside.**  Applying the new ground arguments to
the graft gives a tree above the base which reports, at each probe position,
the flat value of the probed argument. -/
theorem applyFront_graftT_le (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)) (hgood : GoodPositions base ps)
    (vs : Nat → Tree 𝕆) :
    Tree.Le base (applyFront m (graftT m base ps) vs) := by
  have h := applyFront_mono m (t := Tree.padN m base)
    (t' := graftT m base ps) vs (le_graftT m base ps hgood)
  rwa [applyFront_padN] at h

theorem applyFront_graftT_probe (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)) (hgood : GoodPositions base ps)
    (vs : Nat → Tree 𝕆) (ws : Nat → Val) (hvs : ∀ k, vs k = Tree.leaf (ws k))
    (p : Nat × Query σ) (hp : p ∈ ps) (hlt : p.1 < m) :
    (applyFront m (graftT m base ps) vs).at' p.2
      = some (probeVal σ (ws p.1)) := by
  rw [at'_applyFront m p.2 (graftT m base ps) vs _
    (at'_graftT_probe m base ps hgood p hp)]
  rw [applyFront_probeT m σ p.1 hlt vs (ws p.1) (hvs _)]

/-! ## Legality of the graft -/

/-- Planting a legal subtree at a perimeter position keeps the tree legal.  The
general form of `TreeOk_plant_leaf`: the planted tree must be legal in the
context the position determines. -/
theorem TreeOk_plant {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (t e : Tree σ),
    TreeOk γ t → t.at' q = some Tree.bot → QueryOk σ q →
    TreeOk (q.ctxFrom γ) e → TreeOk γ (plant q t e)
  | .hole, γ, t, e, _, _, _, he => he
  | .step i p s rest, γ, t, e, ht, hat, hok, he => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hat
      obtain ⟨hp, hfin, hsub, hnon⟩ := TreeOk_node_inv ht
      obtain ⟨hs, hokr⟩ := (QueryOk_step i p s rest).mp hok
      rw [plant_step_self]
      refine TreeOk.node γ i p _ hp ?_ (fun u _ => ?_) (fun u hu => ?_)
      · obtain ⟨l, hl⟩ := hfin
        refine ⟨s :: l, fun u hu => ?_⟩
        by_cases hus : u = s
        · rw [hus]; exact List.mem_cons_self ..
        · dsimp only at hu
          rw [if_neg hus] at hu
          exact List.mem_cons_of_mem _ (hl u hu)
      · by_cases hus : u = s
        · subst hus
          rw [if_pos rfl]
          exact TreeOk_plant rest (γ.cons i u) (f u) e (hsub u hs) hrest hokr he
        · rw [if_neg hus]
          by_cases hlu : LegalResp p u
          · exact hsub u hlu
          · rw [hnon u hlu]; exact TreeOk.leaf _ _
      · have hus : ¬ u = s := fun he2 => hu (he2 ▸ hs)
        rw [if_neg hus]
        exact hnon u hu

theorem Ctx.padCN_lt : ∀ (m : Nat) {σ : Ty} (γ : Ctx σ) (l : Nat) (hl : l < m)
    (h : l < (Ty.pads m σ).arity),
    (Ctx.padCN m γ : Ctx (Ty.pads m σ)) ⟨l, h⟩ = Tree.bot
  | 0, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | m + 1, σ, γ, 0, _, h => rfl
  | m + 1, σ, γ, l + 1, hl, h => by
      show (Ctx.padCN m γ : Ctx (Ty.pads m σ)) ⟨l, _⟩ = Tree.bot
      exact Ctx.padCN_lt m γ l (Nat.lt_of_succ_lt_succ hl) _

theorem ctxFrom_padQN : ∀ (m : Nat) {σ : Ty} (P : Query σ) (γ : Ctx σ),
    (Query.padQN m P).ctxFrom (Ctx.padCN m γ) = Ctx.padCN m (P.ctxFrom γ)
  | 0, _, P, γ => rfl
  | m + 1, σ, P, γ => by
      show (Query.padQ (Query.padQN m P)).ctxFrom
        (Ctx.padC (Ctx.padCN m γ)) = _
      rw [ctxFrom_padQ (Query.padQN m P) (Ctx.padCN m γ),
        ctxFrom_padQN m P γ]
      rfl

/-- A probe is legal in the context a padded position determines. -/
theorem TreeOk_probeT_ctx (m : Nat) (σ : Ty) (l : Nat) (hl : l < m)
    (P : Query σ) :
    TreeOk ((Query.padQN m P).ctxFrom (Ctx.empty : Ctx (Ty.pads m σ)))
      (probeT m σ l) := by
  rw [show (Ctx.empty : Ctx (Ty.pads m σ)) = Ctx.padCN m (Ctx.empty : Ctx σ)
    from (Ctx.padCN_empty m σ).symm, ctxFrom_padQN m P Ctx.empty]
  rw [probeT_lt m σ l hl]
  refine TreeOk.node _ _ _ _ ?_ ⟨[], fun r hr => absurd rfl hr⟩
    (fun r _ => TreeOk.leaf _ _) (fun r _ => rfl)
  rw [Ctx.padCN_lt m _ l hl]
  exact LegalQuery.root

/-- The graft of legal probes into a legal padded base is legal. -/
theorem TreeOk_graftT : ∀ (m : Nat) {σ : Ty} (base : Tree σ)
    (ps : List (Nat × Query σ)), GoodPositions base ps →
    (∀ p ∈ ps, QueryOk σ p.2) → (∀ p ∈ ps, p.1 < m) →
    TreeOk (Ctx.empty : Ctx σ) base →
    TreeOk (Ctx.empty : Ctx (Ty.pads m σ)) (graftT m base ps)
  | m, σ, base, [], _, _, _, hbase => by
      show TreeOk _ (Tree.padN m base)
      rw [show (Ctx.empty : Ctx (Ty.pads m σ)) = Ctx.padCN m (Ctx.empty : Ctx σ)
        from (Ctx.padCN_empty m σ).symm]
      exact TreeOk_padN m hbase
  | m, σ, base, p :: ps, ⟨hall, hpair⟩, hqok, hlt, hbase => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hgood : GoodPositions base ps :=
        ⟨fun q hq => hall q (List.mem_cons_of_mem _ hq), htail⟩
      show TreeOk _ (plant (Query.padQN m p.2) (graftT m base ps)
        (probeT m σ p.1))
      refine TreeOk_plant (Query.padQN m p.2) Ctx.empty _ _
        (TreeOk_graftT m base ps hgood
          (fun q hq => hqok q (List.mem_cons_of_mem _ hq))
          (fun q hq => hlt q (List.mem_cons_of_mem _ hq)) hbase)
        (at'_graftT_bot m base ps hgood p.2 (hall p (List.mem_cons_self ..))
          (fun q hq => Ne.symm (hhead q hq)))
        (QueryOk_padQN m p.2 (hqok p (List.mem_cons_self ..)))
        (TreeOk_probeT_ctx m σ p.1 (hlt p (List.mem_cons_self ..)) p.2)

/-- Adding ground arguments costs at most one level of depth. -/
theorem Ty.depth_pads : ∀ (m : Nat) (σ : Ty),
    (Ty.pads m σ).depth ≤ max 2 σ.depth
  | 0, σ => Nat.le_max_right _ _
  | m + 1, σ => by
      show max (1 + Ty.depth 𝕆) (Ty.pads m σ).depth ≤ _
      have h := Ty.depth_pads m σ
      show max (1 + 1) (Ty.pads m σ).depth ≤ _
      omega

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

/-- `apply` is determined by its values on *finite* arguments: this is the
continuity of `apply` in its second argument (Definition 4.9). -/
theorem applyT_eq_of_principal {σ τ : Ty} (F G : T (σ ⇒ τ))
    (h : ∀ d : D σ, applyT F (Ideal.principal d) = applyT G (Ideal.principal d)) :
    ∀ E : T σ, applyT F E = applyT G E := by
  intro E
  apply Ideal.ext
  intro c
  have key : ∀ (F' G' : T (σ ⇒ τ)),
      (∀ d : D σ, applyT F' (Ideal.principal d) = applyT G' (Ideal.principal d)) →
      c ∈ applyT F' E → c ∈ applyT G' E := by
    rintro F' G' hFG ⟨f, hf, d, hd, hc⟩
    have hdd : d ∈ Ideal.principal d := Po.le_refl d
    have hmem : c ∈ applyT F' (Ideal.principal d) := ⟨f, hf, d, hdd, hc⟩
    rw [hFG d] at hmem
    obtain ⟨g, hg, d', hd', hc'⟩ := hmem
    exact ⟨g, hg, d, hd, Po.le_trans hc' (apply0_mono_right g.1 hd')⟩
  exact ⟨key F G h, key G F fun d => (h d).symm⟩

/-- Two elements of `T_σ` that apply alike to all tuples of *finite* arguments
are equal.  The induction is on `σ`: extensionality (Theorem 4.11) reduces
equality at `σ → τ` to equality of the applications, continuity reduces those to
finite arguments, and the induction hypothesis at `τ` consumes the remaining
arguments. -/
theorem eq_of_principal_applyIdeals : ∀ (σ : Ty) (F G : T σ),
    (∀ ds : (i : Fin σ.arity) → D (σ.arg i),
      applyIdeals σ F (fun i => Ideal.principal (ds i))
        = applyIdeals σ G (fun i => Ideal.principal (ds i))) → F = G
  | .base, F, G, h => h fun i => absurd i.isLt (by simp)
  | .arrow a τ, F, G, h => by
      refine theorem_4_11.2 a τ F G fun x => ?_
      refine applyT_eq_of_principal F G (fun d => ?_) x
      refine eq_of_principal_applyIdeals τ (applyT F (Ideal.principal d))
        (applyT G (Ideal.principal d)) fun es => ?_
      exact h fun i =>
        match i with
        | ⟨0, _⟩ => d
        | ⟨j + 1, hj⟩ => es ⟨j, Nat.lt_of_succ_lt_succ hj⟩


/-! ## Bridging lemmas for the representability construction -/

/-- **Every path with legal responses into a legal tree is legal.**  The
strengthening of `legalPath_of_TreeOk` that Definition 4.2's `QueryOk` makes
available: it is the recorded responses, not the subtree reached, that decide
legality. -/
theorem legalIn_of_TreeOk {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (d e : Tree σ),
    TreeOk γ d → d.at' q = some e → QueryOk σ q → q.LegalIn γ
  | .hole, _, _, _, _, _, _ => trivial
  | .step i p r rest, γ, d, e, hd, hq, hok => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      obtain ⟨hp, _, hsub, _⟩ := TreeOk_node_inv hd
      obtain ⟨hr, hokr⟩ := (QueryOk_step i p r rest).mp hok
      exact ⟨hp, hr,
        legalIn_of_TreeOk rest (γ.cons i r) (f r) e (hsub r hr) hrest hokr⟩

/-- Being above what a context records is preserved by growing the tree. -/
theorem RespCtx.Above.mono {σ : Ty} {γ : RespCtx σ} {i : Fin σ.arity}
    {d d' : Tree (σ.arg i)} (h : RespCtx.Above γ i d) (hle : Tree.Le d d') :
    RespCtx.Above γ i d' :=
  fun r hr => Tree.Le.trans (h r hr) hle

/-- A legal context knows only legal closed trees about its arguments. -/
theorem CtxOk.treeOk {σ : Ty} : ∀ {γ : Ctx σ}, CtxOk γ →
    ∀ i, TreeOk (Ctx.empty : Ctx (σ.arg i)) (γ i)
  | _, .empty, _ => TreeOk.leaf _ _
  | _, @CtxOk.cons _ γ i q r hγ hq hr, j => by
      by_cases hij : i = j
      · subst hij
        rw [Ctx.cons_self]
        obtain ⟨x, rfl, hx⟩ := hr
        refine TreeOk_join_resp _ Ctx.empty (γ i) (CtxOk.treeOk hγ i) ?_ ?_ ?_
        · rw [Query.qry_substAns]; exact hq.1
        · rw [Query.qry_substAns]; exact hq.2
        · rw [Query.qry_substAns, Query.ansOf_substAns]; exact hx
      · rw [Ctx.cons_other _ _ hij]; exact CtxOk.treeOk hγ j

/-- The context a legal path determines is legal. -/
theorem CtxOk.ctxFrom {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ), CtxOk γ →
    q.LegalIn γ → CtxOk (q.ctxFrom γ)
  | .hole, γ, h, _ => h
  | .step i p r rest, γ, h, ⟨hp, hr, hrest⟩ =>
      CtxOk.ctxFrom rest (γ.cons i r) (CtxOk.cons h hp hr) hrest

/-- The context determined by a legal query inside a legal tree is legal. -/
theorem CtxOk.ofQuery {σ : Ty} {γ : Ctx σ} (hγ : CtxOk γ) {q : Query σ}
    {d e : Tree σ} (hd : TreeOk γ d) (hq : d.at' q = some e) (hok : QueryOk σ q) :
    CtxOk (q.ctxFrom γ) :=
  CtxOk.ctxFrom q γ hγ (legalIn_of_TreeOk q γ d e hd hq hok)

/-- Every response a legal query records is below the tree it determines. -/
theorem above_ctx_of_TreeOk {σ : Ty} {γ : Ctx σ} {q : Query σ} {d e : Tree σ}
    (hd : TreeOk γ d) (hq : d.at' q = some e) (hok : QueryOk σ q)
    (i : Fin σ.arity) : RespCtx.Above q.ctxList i ((q.ctxFrom γ) i) :=
  Ctx.above_ctxFrom q γ (legalIn_of_TreeOk q γ d e hd hq hok) i

/-- A representable closed tree is the meaning of a closed expression: the
"reduces to tree representability by extensionality" remark of
Definition 5.3. -/
theorem meaning_of_representable (σ : Ty) (t : Tree σ)
    (hok : TreeOk (Ctx.empty : Ctx σ) t) (hrep : Representable σ Ctx.empty t) :
    ∃ M : Term SPCF, Term.Closed M ∧ Term.HasTy [] M σ ∧
      Tmodel.meaning botEnv M σ = Ideal.principal ⟨t, hok⟩ := by
  obtain ⟨M, hcl, hty, happ⟩ := hrep
  refine ⟨M, hcl, hty, ?_⟩
  refine eq_of_principal_applyIdeals σ _ _ fun ds => ?_
  rw [happ ds (fun i => Tree.Le.bot _),
    applyIdeals_principal σ ⟨t, hok⟩ ds]

/-! ## Depth of argument types -/

/-- Every argument type is at least one level shallower. -/
theorem Ty.depth_arg : ∀ (σ : Ty) (i : Fin σ.arity), 1 + (σ.arg i).depth ≤ σ.depth
  | .base, i => absurd i.isLt (by simp [Ty.arity])
  | .arrow a b, ⟨0, _⟩ => by
      show 1 + a.depth ≤ max (1 + a.depth) b.depth
      omega
  | .arrow a b, ⟨j + 1, hj⟩ => by
      have hjb : j < b.arity := Nat.lt_of_succ_lt_succ hj
      have h := Ty.depth_arg b ⟨j, hjb⟩
      show 1 + (b.arg ⟨j, hjb⟩).depth ≤ max (1 + a.depth) b.depth
      omega

/-! ## A response realised by a tree is a path in that tree -/

/-- If a tree carries a numeral at position `q`, it contains the response
`q[?/a]`. -/
theorem Resp.toTree_le_of_at'_num {σ : Ty} : ∀ (q : Query σ) (d : Tree σ) (a : Nat),
    d.at' q = some (.leaf (.num a)) →
    Tree.Le (q.substAns (RAns.num a)).toTree d
  | .hole, d, a, h => by
      have hd : d = Tree.leaf (.num a) := by injection h
      rw [hd]
      exact Tree.Le.refl _
  | .step i p r rest, d, a, h => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv h
      show Tree.Le (Tree.node i p _) _
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs
        rw [if_pos rfl]
        exact Resp.toTree_le_of_at'_num rest (f s) a hrest
      · rw [if_neg hs]
        exact Tree.Le.bot _

/-- If a tree carries a node at position `q`, it contains the response
`q[?/⟨j,p,⊥⟩]`. -/
theorem Resp.toTree_le_of_at'_node {σ : Ty} : ∀ (q : Query σ) (d : Tree σ)
    (j : Fin σ.arity) (p : Query (σ.arg j)) (g : Resp (σ.arg j) → Tree σ),
    d.at' q = some (.node j p g) →
    Tree.Le (q.substAns (RAns.node j p)).toTree d
  | .hole, d, j, p, g, h => by
      have hd : d = Tree.node j p g := by injection h
      rw [hd]
      show Tree.Le (Tree.node j p (fun _ => Tree.bot)) _
      exact Tree.Le.node _ _ _ _ fun s => Tree.Le.bot _
  | .step i p' r rest, d, j, p, g, h => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv h
      show Tree.Le (Tree.node i p' _) _
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs
        rw [if_pos rfl]
        exact Resp.toTree_le_of_at'_node rest (f s) j p g hrest
      · rw [if_neg hs]
        exact Tree.Le.bot _

/-- An argument that extends the context and realises a response also extends
the context enlarged by that response. -/
theorem Ctx.above_cons {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity)
    (r : Resp (σ.arg i)) (ds : (j : Fin σ.arity) → Tree (σ.arg j))
    (hds : ∀ j, Ctx.Above γ j (ds j)) (hr : Tree.Le r.toTree (ds i))
    (j : Fin σ.arity) : Ctx.Above (γ.cons i r) j (ds j) := by
  by_cases hij : i = j
  · subst hij
    show Tree.Le ((γ.cons i r) i) (ds i)
    rw [Ctx.cons_self]
    exact (Tree.join_spec (γ i) r.toTree (ds i) (hds i) hr).2.2 (ds i) (hds i) hr
  · show Tree.Le ((γ.cons i r) j) (ds j)
    rw [Ctx.cons_other _ _ hij]
    exact hds j

/-! ## Feeding the ground arguments of a padded expression -/

/-- `(M y_b y_{b+1} … y_{b+m-1})`: apply `M` to `m` consecutive ground
variables. -/
def appsFrom (M : Term SPCF) (b : Nat) : Nat → Term SPCF
  | 0 => M
  | j + 1 => appsFrom (.app M (.var b 𝕆)) (b + 1) j

theorem appsFrom_hasTy : ∀ (m : Nat) {σ : Ty} (M : Term SPCF) (b : Nat)
    (Γ : List (Nat × Ty)), Term.HasTy Γ M (Ty.pads m σ) →
    (∀ k, k < m → (b + k, 𝕆) ∈ Γ) → Term.HasTy Γ (appsFrom M b m) σ
  | 0, _, M, b, Γ, hM, _ => hM
  | m + 1, σ, M, b, Γ, hM, hvars => by
      refine appsFrom_hasTy m (.app M (.var b 𝕆)) (b + 1) Γ
        (Term.HasTy.app hM (Term.HasTy.var ?_)) (fun k hk => ?_)
      · have h := hvars 0 (Nat.succ_pos _)
        rwa [Nat.add_zero] at h
      · have h := hvars (k + 1) (Nat.succ_lt_succ hk)
        rwa [show b + (k + 1) = b + 1 + k from by omega] at h

/-- Feeding `m` ground values to a finite element of a padded type. -/
noncomputable def applyFrontD : ∀ (m : Nat) {σ : Ty}, D (Ty.pads m σ) →
    (Nat → Val) → D σ
  | 0, _, t, _ => t
  | m + 1, _, t, ws =>
      applyFrontD m (applyD t ⟨.leaf (ws 0), TreeOk.leaf _ _⟩) (fun k => ws (k + 1))

theorem applyFrontD_val : ∀ (m : Nat) {σ : Ty} (t : D (Ty.pads m σ))
    (ws : Nat → Val),
    (applyFrontD m t ws).1 = applyFront m t.1 (fun k => Tree.leaf (ws k))
  | 0, _, t, ws => rfl
  | m + 1, σ, t, ws => by
      show (applyFrontD m (applyD t ⟨.leaf (ws 0), TreeOk.leaf _ _⟩) _).1 = _
      rw [applyFrontD_val m _ _]
      rfl

/-- The meaning of a padded expression fed its ground arguments. -/
theorem meaning_appsFrom : ∀ (m : Nat) {σ : Ty} (M : Term SPCF) (b : Nat)
    (Env : Tmodel.Env) (t : D (Ty.pads m σ)) (ws : Nat → Val),
    Tmodel.meaning Env M (Ty.pads m σ) = Ideal.principal t →
    (∀ k, k < m → Env (b + k) 𝕆 = leafT 𝕆 (ws k)) →
    Tmodel.meaning Env (appsFrom M b m) σ = Ideal.principal (applyFrontD m t ws)
  | 0, _, M, b, Env, t, ws, hM, _ => hM
  | m + 1, σ, M, b, Env, t, ws, hM, hEnv => by
      refine meaning_appsFrom m (.app M (.var b 𝕆)) (b + 1) Env
        (applyD t ⟨.leaf (ws 0), TreeOk.leaf _ _⟩) (fun k => ws (k + 1)) ?_
        (fun k hk => ?_)
      · have hvar : Tmodel.meaning Env (Term.var b 𝕆) 𝕆
            = leafT 𝕆 (ws 0) := by
          show Tmodel.combMeaning Env (.var b 𝕆) 𝕆 = _
          rw [Model.combMeaning_var]
          have h := hEnv 0 (Nat.succ_pos _)
          rwa [Nat.add_zero] at h
        rw [meaning_app_term Env M (.var b 𝕆) 𝕆 (Ty.pads m σ) [(b, 𝕆)]
            (Term.HasTy.var (List.mem_cons_self ..))]
        rw [show ((T⟦M⟧Env) (𝕆 ⇒ Ty.pads m σ)) = Ideal.principal t from hM, hvar]
        show applyT (Ideal.principal t) (Ideal.principal
          (⟨.leaf (ws 0), TreeOk.leaf _ _⟩ : D 𝕆)) = _
        exact applyT_principal t _
      · have h := hEnv (k + 1) (Nat.succ_lt_succ hk)
        rwa [show b + (k + 1) = b + 1 + k from by omega] at h

/-! ## Numbering a finite set of responses

The construction of §5 numbers the query responses below the root of `e`: the
`j`-th response is the one whose probe `catch` reports as `j`. -/

/-- Pair each element of a list with its position, counting from `n₀`. -/
def enumFrom' {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, a :: l => (n, a) :: enumFrom' (n + 1) l

theorem enumFrom'_length {α : Type} : ∀ (n : Nat) (l : List α),
    (enumFrom' n l).length = l.length
  | _, [] => rfl
  | n, a :: l => by
      show (enumFrom' (n + 1) l).length + 1 = l.length + 1
      rw [enumFrom'_length (n + 1) l]

theorem mem_enumFrom' {α : Type} : ∀ (n : Nat) (l : List α) (a : α), a ∈ l →
    ∃ k, (n + k, a) ∈ enumFrom' n l ∧ k < l.length
  | _, [], _, h => absurd h (fun hc => List.not_mem_nil hc)
  | n, b :: l, a, h => by
      rcases List.mem_cons.mp h with rfl | htl
      · exact ⟨0, by rw [Nat.add_zero]; exact List.mem_cons_self .., Nat.succ_pos _⟩
      · obtain ⟨k, hk, hlt⟩ := mem_enumFrom' (n + 1) l a htl
        refine ⟨k + 1, ?_, Nat.succ_lt_succ hlt⟩
        rw [show n + (k + 1) = n + 1 + k from by omega]
        exact List.mem_cons_of_mem _ hk

theorem enumFrom'_mem_snd {α : Type} : ∀ (n : Nat) (l : List α) (p : Nat × α),
    p ∈ enumFrom' n l → p.2 ∈ l
  | _, [], _, h => absurd h (fun hc => List.not_mem_nil hc)
  | n, b :: l, p, h => by
      rcases List.mem_cons.mp h with rfl | htl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (enumFrom'_mem_snd (n + 1) l p htl)

theorem enumFrom'_lt {α : Type} : ∀ (n : Nat) (l : List α) (p : Nat × α),
    p ∈ enumFrom' n l → p.1 < n + l.length
  | _, [], _, h => absurd h (fun hc => List.not_mem_nil hc)
  | n, b :: l, p, h => by
      rcases List.mem_cons.mp h with rfl | htl
      · show n < n + (l.length + 1)
        omega
      · have h2 := enumFrom'_lt (n + 1) l p htl
        show p.1 < n + (l.length + 1)
        omega

theorem enumFrom'_ge {α : Type} : ∀ (n : Nat) (l : List α) (p : Nat × α),
    p ∈ enumFrom' n l → n ≤ p.1
  | _, [], _, h => absurd h (fun hc => List.not_mem_nil hc)
  | n, b :: l, p, h => by
      rcases List.mem_cons.mp h with rfl | htl
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (enumFrom'_ge (n + 1) l p htl)

theorem enumFrom'_pairwise_lt {α : Type} : ∀ (n : Nat) (l : List α),
    List.Pairwise (fun p q : Nat × α => p.1 < q.1) (enumFrom' n l)
  | _, [] => List.Pairwise.nil
  | n, a :: l => by
      refine List.pairwise_cons.mpr ⟨fun q hq => ?_, enumFrom'_pairwise_lt (n + 1) l⟩
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (enumFrom'_ge (n + 1) l q hq)

/-- Two entries of an enumeration with the same index are the same entry. -/
theorem enumFrom'_fst_inj {α : Type} : ∀ (n : Nat) (l : List α) (p q : Nat × α),
    p ∈ enumFrom' n l → q ∈ enumFrom' n l → p.1 = q.1 → p.2 = q.2
  | _, [], _, _, h, _, _ => absurd h (fun hc => List.not_mem_nil hc)
  | n, a :: l, p, q, hp, hq, heq => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · exact absurd (heq ▸ enumFrom'_ge (n + 1) l q hq') (by omega)
      · rcases List.mem_cons.mp hq with rfl | hq'
        · exact absurd (heq ▸ enumFrom'_ge (n + 1) l p hp') (by omega)
        · exact enumFrom'_fst_inj (n + 1) l p q hp' hq' heq

/-- Removing duplicates from a list. -/
noncomputable def dedupL {α : Type} : List α → List α
  | [] => []
  | a :: l =>
      if _ : (Classical.propDecidable (a ∈ dedupL l)).decide = true then dedupL l
      else a :: dedupL l

theorem dedupL_cons_pos {α : Type} (b : α) (l : List α) (h : b ∈ dedupL l) :
    dedupL (b :: l) = dedupL l := by
  show (if _ : (Classical.propDecidable (b ∈ dedupL l)).decide = true then _
    else _) = _
  rw [dif_pos (by simpa using h)]

theorem dedupL_cons_neg {α : Type} (b : α) (l : List α) (h : ¬ b ∈ dedupL l) :
    dedupL (b :: l) = b :: dedupL l := by
  show (if _ : (Classical.propDecidable (b ∈ dedupL l)).decide = true then _
    else _) = _
  rw [dif_neg (by simpa using h)]

theorem mem_dedupL {α : Type} : ∀ (l : List α) (a : α), a ∈ dedupL l ↔ a ∈ l
  | [], a => Iff.rfl
  | b :: l, a => by
      by_cases hb : b ∈ dedupL l
      · rw [dedupL_cons_pos b l hb]
        constructor
        · intro h; exact List.mem_cons_of_mem _ ((mem_dedupL l a).mp h)
        · intro h
          rcases List.mem_cons.mp h with rfl | htl
          · exact hb
          · exact (mem_dedupL l a).mpr htl
      · rw [dedupL_cons_neg b l hb]
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl | htl
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ ((mem_dedupL l a).mp htl)
        · intro h
          rcases List.mem_cons.mp h with rfl | htl
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ ((mem_dedupL l a).mpr htl)

theorem dedupL_pairwise {α : Type} : ∀ (l : List α),
    List.Pairwise (fun a b : α => a ≠ b) (dedupL l)
  | [] => List.Pairwise.nil
  | b :: l => by
      by_cases hb : b ∈ dedupL l
      · rw [dedupL_cons_pos b l hb]
        exact dedupL_pairwise l
      · rw [dedupL_cons_neg b l hb]
        exact List.pairwise_cons.mpr
          ⟨fun a ha hc => hb (hc ▸ ha), dedupL_pairwise l⟩

/-- The largest element of a list of naturals (or `0`). -/
def maxOfL : List Nat → Nat
  | [] => 0
  | a :: l => max a (maxOfL l)

theorem le_maxOfL : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ maxOfL l
  | [], _, h => absurd h (fun hc => List.not_mem_nil hc)
  | b :: l, a, h => by
      rcases List.mem_cons.mp h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_maxOfL l a htl) (Nat.le_max_right _ _)

/-! ## Ingredients of the `catch`-based construction of §5 -/

/-- Classical filtering by a proposition. -/
noncomputable def filterP {α : Type} (P : α → Prop) (l : List α) : List α :=
  l.filterMap (fun a =>
    if _ : (Classical.propDecidable (P a)).decide = true then some a else none)

theorem mem_filterP {α : Type} (P : α → Prop) (l : List α) (a : α) :
    a ∈ filterP P l ↔ a ∈ l ∧ P a := by
  rw [filterP, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hres⟩
    by_cases hP : P b
    · rw [dif_pos (by simpa using hP)] at hres
      have : b = a := Option.some.inj hres
      subst this
      exact ⟨hb, hP⟩
    · rw [dif_neg (by simpa using hP)] at hres
      exact absurd hres (fun hc => Option.noConfusion hc)
  · rintro ⟨ha, hP⟩
    exact ⟨a, ha, by rw [dif_pos (by simpa using hP)]⟩

/-- The `m` bound variables of `M'`, named from `b` on. -/
def yvars (b : Nat) : Nat → List (Nat × Ty)
  | 0 => []
  | m + 1 => (b, 𝕆) :: yvars (b + 1) m

theorem foldX_yvars : ∀ (m b : Nat), foldX (yvars b m) = Ty.pads m 𝕆
  | 0, _ => rfl
  | m + 1, b => by
      show (𝕆 ⇒ foldX (yvars (b + 1) m)) = _
      rw [foldX_yvars m (b + 1)]
      rfl

theorem mem_yvars : ∀ (m b k : Nat), k < m → (b + k, 𝕆) ∈ yvars b m
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, b, 0, _ => by
      rw [Nat.add_zero]
      exact List.mem_cons_self ..
  | m + 1, b, k + 1, hk => by
      rw [show b + (k + 1) = b + 1 + k from by omega]
      exact List.mem_cons_of_mem _ (mem_yvars m (b + 1) k (Nat.lt_of_succ_lt_succ hk))

theorem yvars_ty : ∀ (m b : Nat) (p : Nat × Ty), p ∈ yvars b m → p.2 = 𝕆
  | 0, _, _, hp => absurd hp (fun hc => List.not_mem_nil hc)
  | m + 1, b, p, hp => by
      rcases List.mem_cons.mp hp with rfl | htl
      · rfl
      · exact yvars_ty m (b + 1) p htl

theorem yvars_fst_ge : ∀ (m b : Nat) (p : Nat × Ty), p ∈ yvars b m → b ≤ p.1
  | 0, _, _, hp => absurd hp (fun hc => List.not_mem_nil hc)
  | m + 1, b, p, hp => by
      rcases List.mem_cons.mp hp with rfl | htl
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (yvars_fst_ge m (b + 1) p htl)

theorem yvars_length : ∀ (m b : Nat), (yvars b m).length = m
  | 0, _ => rfl
  | m + 1, b => by
      show (yvars (b + 1) m).length + 1 = m + 1
      rw [yvars_length m (b + 1)]

/-- Distinct positions of `yvars` carry distinct variables. -/
theorem yvars_getElem : ∀ (m b : Nat) (k : Nat) (h : k < (yvars b m).length),
    (yvars b m)[k]'h = (b + k, 𝕆)
  | 0, _, _, h => absurd h (by simp [yvars_length])
  | m + 1, b, 0, h => rfl
  | m + 1, b, k + 1, h => by
      show (yvars (b + 1) m)[k]'_ = _
      rw [yvars_getElem m (b + 1) k _,
        show b + 1 + k = b + (k + 1) from by omega]

/-! ## Abstracting over the arguments, type-directed

`varsFrom b σ.args` names the arguments of `σ` consecutively from `b`;
`Term.lams` binds them and `applyIdeals` feeds them back. -/

/-- Consecutive names for a list of types. -/
def varsFrom (b : Nat) : List Ty → List (Nat × Ty)
  | [] => []
  | a :: as => (b, a) :: varsFrom (b + 1) as

theorem varsFrom_cons (b : Nat) (a : Ty) (as : List Ty) :
    varsFrom b (a :: as) = (b, a) :: varsFrom (b + 1) as := rfl

theorem mem_varsFrom : ∀ (σ : Ty) (b : Nat) (j : Fin σ.arity),
    (b + j.val, σ.arg j) ∈ varsFrom b σ.args
  | .base, _, j => absurd j.isLt (by simp [Ty.arity])
  | .arrow a τ, b, ⟨0, _⟩ => by
      show (b + 0, a) ∈ (b, a) :: varsFrom (b + 1) τ.args
      rw [Nat.add_zero]
      exact List.mem_cons_self ..
  | .arrow a τ, b, ⟨j + 1, hj⟩ => by
      have hjt : j < τ.arity := Nat.lt_of_succ_lt_succ hj
      have h := mem_varsFrom τ (b + 1) ⟨j, hjt⟩
      show (b + (j + 1), τ.arg ⟨j, hjt⟩) ∈ (b, a) :: varsFrom (b + 1) τ.args
      rw [show b + (j + 1) = b + 1 + j from by omega]
      exact List.mem_cons_of_mem _ h

theorem varsFrom_fst_ge : ∀ (as : List Ty) (b : Nat) (p : Nat × Ty),
    p ∈ varsFrom b as → b ≤ p.1
  | [], _, _, hp => absurd hp (fun hc => List.not_mem_nil hc)
  | a :: as, b, p, hp => by
      rcases List.mem_cons.mp hp with rfl | htl
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (varsFrom_fst_ge as (b + 1) p htl)

theorem varsFrom_fst_lt : ∀ (as : List Ty) (b : Nat) (p : Nat × Ty),
    p ∈ varsFrom b as → p.1 < b + as.length
  | [], _, _, hp => absurd hp (fun hc => List.not_mem_nil hc)
  | a :: as, b, p, hp => by
      rcases List.mem_cons.mp hp with rfl | htl
      · show b < b + (as.length + 1); omega
      · have h := varsFrom_fst_lt as (b + 1) p htl
        show p.1 < b + (as.length + 1)
        omega

/-- The environment that binds `varsFrom b σ.args` to a tuple of arguments. -/
noncomputable def envArgs : ∀ (b : Nat) (σ : Ty),
    ((j : Fin σ.arity) → T (σ.arg j)) → Tmodel.Env → Tmodel.Env
  | _, .base, _, Env => Env
  | b, .arrow a τ, ds, Env =>
      envArgs (b + 1) τ (fun j => ds ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (Model.envUpdate Env b a (ds ⟨0, Nat.succ_pos _⟩))

/-- Outside the names it binds, `envArgs` changes nothing. -/
theorem envArgs_other : ∀ (σ : Ty) (b : Nat)
    (ds : (j : Fin σ.arity) → T (σ.arg j)) (Env : Tmodel.Env) (x : Nat) (ν : Ty),
    x < b → envArgs b σ ds Env x ν = Env x ν
  | .base, _, _, _, _, _, _ => rfl
  | .arrow a τ, b, ds, Env, x, ν, hx => by
      show envArgs (b + 1) τ _ (Model.envUpdate Env b a _) x ν = _
      rw [envArgs_other τ (b + 1) _ _ x ν (by omega),
        Model.envUpdate_other Env b a _ x ν (fun hc => by omega)]

/-- `envArgs` binds the `j`-th name to the `j`-th argument. -/
theorem envArgs_self : ∀ (σ : Ty) (b : Nat)
    (ds : (j : Fin σ.arity) → T (σ.arg j)) (Env : Tmodel.Env) (j : Fin σ.arity),
    envArgs b σ ds Env (b + j.val) (σ.arg j) = ds j
  | .base, _, _, _, j => absurd j.isLt (by simp [Ty.arity])
  | .arrow a τ, b, ds, Env, ⟨0, h0⟩ => by
      show envArgs (b + 1) τ _ (Model.envUpdate Env b a _) (b + 0) a = _
      rw [envArgs_other τ (b + 1) _ _ (b + 0) a (by omega)]
      exact Model.envUpdate_self Env b a _
  | .arrow a τ, b, ds, Env, ⟨j + 1, hj⟩ => by
      have hjt : j < τ.arity := Nat.lt_of_succ_lt_succ hj
      have h := envArgs_self τ (b + 1) (fun j' =>
        ds ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩)
        (Model.envUpdate Env b a (ds ⟨0, Nat.succ_pos _⟩)) ⟨j, hjt⟩
      show envArgs (b + 1) τ (fun j' => ds ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩)
        (Model.envUpdate Env b a (ds ⟨0, Nat.succ_pos _⟩))
        (b + (j + 1)) (τ.arg ⟨j, hjt⟩) = _
      rw [show b + (j + 1) = b + 1 + j from by omega]
      exact h

theorem foldr_varsFrom : ∀ (as : List Ty) (b : Nat) (ρ : Ty),
    (varsFrom b as).foldr (fun p τ => p.2 ⇒ τ) ρ
      = as.foldr (fun a τ => a ⇒ τ) ρ
  | [], _, _ => rfl
  | a :: as, b, ρ => by
      show (a ⇒ (varsFrom (b + 1) as).foldr (fun p τ => p.2 ⇒ τ) ρ) = _
      rw [foldr_varsFrom as (b + 1) ρ]
      rfl

theorem lams_varsFrom_hasTy (σ : Ty) (b : Nat) (B : Term SPCF)
    (Γ : List (Nat × Ty)) (hB : Term.HasTy (varsFrom b σ.args ++ Γ) B 𝕆) :
    Term.HasTy Γ (Term.lams (varsFrom b σ.args) B) σ := by
  have h := Term.lams_hasTy (varsFrom b σ.args) Γ B 𝕆 hB
  rwa [foldr_varsFrom, Ty.foldr_args] at h

/-- **Abstracting and re-applying.**  Binding the arguments of `σ` and feeding
them back gives the body's meaning in the environment that binds them. -/
theorem applyIdeals_lams : ∀ (σ : Ty) (b : Nat) (Env : Tmodel.Env)
    (B : Term SPCF) (Γ : List (Nat × Ty)),
    Term.HasTy (varsFrom b σ.args ++ Γ) B 𝕆 →
    ∀ ds : (j : Fin σ.arity) → T (σ.arg j),
    applyIdeals σ (Tmodel.meaning Env (Term.lams (varsFrom b σ.args) B) σ) ds
      = Tmodel.meaning (envArgs b σ ds Env) B 𝕆
  | .base, b, Env, B, Γ, _, ds => rfl
  | .arrow a τ, b, Env, B, Γ, hB, ds => by
      have hB' : Term.HasTy ((b, a) :: (varsFrom (b + 1) τ.args ++ Γ)) B 𝕆 := hB
      have hB2 : Term.HasTy (varsFrom (b + 1) τ.args ++ ((b, a) :: Γ)) B 𝕆 := by
        refine Term.weaken (fun p hp => ?_) hB'
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        rcases hp with hp | hp | hp
        · exact Or.inr (Or.inl hp)
        · exact Or.inl hp
        · exact Or.inr (Or.inr hp)
      have hbody : Comb.HasTy ((b, a) :: Γ)
          (Term.toComb (Term.lams (varsFrom (b + 1) τ.args) B)) τ :=
        Term.toComb_hasTy (lams_varsFrom_hasTy τ (b + 1) B ((b, a) :: Γ) hB2)
      show applyIdeals τ (applyT (Tmodel.meaning Env
        (Term.lams ((b, a) :: varsFrom (b + 1) τ.args) B) (a ⇒ τ))
        (ds ⟨0, Nat.succ_pos _⟩)) _ = _
      rw [show Tmodel.meaning Env
            (Term.lams ((b, a) :: varsFrom (b + 1) τ.args) B) (a ⇒ τ)
          = Tmodel.combMeaning Env
              (Comb.lamStar b a
                (Term.toComb (Term.lams (varsFrom (b + 1) τ.args) B))) (a ⇒ τ)
          from rfl,
        lamStar_apply Env b a (ds ⟨0, Nat.succ_pos _⟩) _ τ Γ hbody]
      exact applyIdeals_lams τ (b + 1) _ B ((b, a) :: Γ) hB2 _

/-! ## The construction of §5

Given a node `⟨i, q, f⟩`, the expression `M` of §5 is

```
M = λ*x₁ … x_k .
      let w = (catch (λ*y₁ … y_m . (x_i B₁ … B_l))) in
      (if0 w        (F₁ x₁ … x_k)
      (if0 (sub1⊥ w) (F₂ x₁ … x_k) …))
```

where the `Bₕ` report, through `catch`, which response below the root of `e`
the argument `x_i` realises, and the `F`s represent the subtrees. -/

/-- The node responses in a list, numbered. -/
noncomputable def nodeResps {α : Ty} (q : Query α) (l₀ : List (Resp α)) :
    List (Resp α) :=
  dedupL (filterP (fun r => LegalResp q r ∧
    ∃ (j : Fin α.arity) (p : Query (α.arg j)), r.ansOf = RAns.node j p) l₀)

theorem mem_nodeResps {α : Ty} (q : Query α) (l₀ : List (Resp α)) (r : Resp α) :
    r ∈ nodeResps q l₀ ↔ (r ∈ l₀ ∧ LegalResp q r ∧
      ∃ (j : Fin α.arity) (p : Query (α.arg j)), r.ansOf = RAns.node j p) := by
  rw [nodeResps, mem_dedupL, mem_filterP]

theorem nodeResps_pairwise {α : Ty} (q : Query α) (l₀ : List (Resp α)) :
    List.Pairwise (fun a b : Resp α => a ≠ b) (nodeResps q l₀) :=
  dedupL_pairwise _

/-- The position, among the arguments of `α`, that an answer probes. -/
noncomputable def posOfAns {α : Ty} (h : Fin α.arity) :
    RAns α → Option (Query (α.arg h))
  | .num _ => none
  | .node j p => if hj : j = h then some (hj ▸ p) else none

/-- The position, among the arguments of `α`, that a response probes. -/
noncomputable def posOf {α : Ty} (h : Fin α.arity) (r : Resp α) :
    Option (Query (α.arg h)) := posOfAns h r.ansOf

theorem posOf_of_ansOf {α : Ty} (h : Fin α.arity) (r : Resp α)
    (p : Query (α.arg h)) (hAns : r.ansOf = RAns.node h p) :
    posOf h r = some p := by
  show posOfAns h r.ansOf = some p
  rw [hAns, posOfAns, dif_pos rfl]

theorem ansOf_of_posOf {α : Ty} (h : Fin α.arity) (r : Resp α)
    (p : Query (α.arg h)) (hpos : posOf h r = some p) :
    r.ansOf = RAns.node h p := by
  have hpos' : posOfAns h r.ansOf = some p := hpos
  cases hAns : r.ansOf with
  | num n =>
    rw [hAns, posOfAns] at hpos'
    exact absurd hpos' (fun hc => Option.noConfusion hc)
  | node j p' =>
    rw [hAns, posOfAns] at hpos'
    by_cases hj : j = h
    · subst hj
      rw [dif_pos rfl] at hpos'
      have hp : p' = p := Option.some.inj hpos'
      rw [hp]
    · rw [dif_neg hj] at hpos'
      exact absurd hpos' (fun hc => Option.noConfusion hc)

/-- The graft positions for argument `h`: the numbered responses that probe
it. -/
noncomputable def psForArg {α : Ty} (rs : List (Resp α)) (h : Fin α.arity) :
    List (Nat × Query (α.arg h)) :=
  (enumFrom' 0 rs).filterMap (fun pr => (posOf h pr.2).map (fun p => (pr.1, p)))

theorem mem_psForArg {α : Ty} (rs : List (Resp α)) (h : Fin α.arity)
    (np : Nat × Query (α.arg h)) :
    np ∈ psForArg rs h ↔
      ∃ r, (np.1, r) ∈ enumFrom' 0 rs ∧ posOf h r = some np.2 := by
  rw [psForArg, List.mem_filterMap]
  constructor
  · rintro ⟨pr, hpr, hres⟩
    cases hp : posOf h pr.2 with
    | none => rw [hp] at hres; exact absurd hres (fun hc => Option.noConfusion hc)
    | some p =>
      rw [hp] at hres
      have heq : (pr.1, p) = np := Option.some.inj hres
      refine ⟨pr.2, ?_, ?_⟩
      · rw [← congrArg Prod.fst heq]
        exact hpr
      · rw [hp, ← congrArg Prod.snd heq]
  · rintro ⟨r, hmem, hpos⟩
    refine ⟨(np.1, r), hmem, ?_⟩
    show Option.map (fun p => (np.1, p)) (posOf h r) = some np
    rw [hpos]
    rfl

/-- The `k` argument variables of `M`, as expressions. -/
def xargs (σ : Ty) : List (Term SPCF) :=
  List.ofFn (fun j : Fin σ.arity => (Term.var j.val (σ.arg j) : Term SPCF))

/-- The body `M'` of the `catch`, and the whole expression `M` of §5. -/
noncomputable def catchBody (σ : Ty) (i : Fin σ.arity) (m : Nat)
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF) : Term SPCF :=
  Term.lams (yvars σ.arity m)
    (Term.apps (Term.var i.val (σ.arg i))
      (List.ofFn (fun h : Fin (σ.arg i).arity => appsFrom (Es h) σ.arity m)))

/-- The arms of the sequential case split. -/
noncomputable def caseArms (σ : Ty) (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i))) (A : Nat)
    (Fs : Resp (σ.arg i) → Term SPCF) : List (Nat × Term SPCF) :=
  (enumFrom' 0 rs).map (fun pr => (pr.1, Term.apps (Fs pr.2) (xargs σ)))
    ++ (List.range (A + 1)).map
        (fun a => (rs.length + a,
          Term.apps (Fs (q.substAns (RAns.num a))) (xargs σ)))

/-- The expression `M` of §5. -/
noncomputable def nodeTerm (σ : Ty) (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i))) (A : Nat)
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (Fs : Resp (σ.arg i) → Term SPCF) : Term SPCF :=
  Term.lams (varsFrom 0 σ.args)
    (Term.app
      (Term.lam (σ.arity + rs.length) 𝕆
        (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
          (caseArms σ i q rs A Fs)))
      (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
        (catchBody σ i rs.length Es)))

/-! ## The graft positions are good -/

theorem pairwise_filterMap' {α β : Type} (g : α → Option β) (R : α → α → Prop)
    (S : β → β → Prop) : ∀ (l : List α), List.Pairwise R l →
    (∀ a ∈ l, ∀ a' ∈ l, ∀ b b', R a a' → g a = some b → g a' = some b' → S b b') →
    List.Pairwise S (l.filterMap g)
  | [], _, _ => List.Pairwise.nil
  | a :: l, h, hg => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      have hrec := pairwise_filterMap' g R S l htail
        (fun x hx x' hx' b b' hR hb hb' =>
          hg x (List.mem_cons_of_mem _ hx) x' (List.mem_cons_of_mem _ hx') b b'
            hR hb hb')
      cases hga : g a with
      | none =>
        rw [List.filterMap_cons_none hga]
        exact hrec
      | some b =>
        rw [List.filterMap_cons_some hga]
        refine List.pairwise_cons.mpr ⟨fun b' hb' => ?_, hrec⟩
        obtain ⟨a', ha', hga'⟩ := List.mem_filterMap.mp hb'
        exact hg a (List.mem_cons_self ..) a' (List.mem_cons_of_mem _ ha') b b'
          (hhead a' ha') hga hga'

/-- In a duplicate-free list, an element occupies one position. -/
theorem enumFrom'_snd_inj {α : Type} : ∀ (n : Nat) (l : List α),
    List.Pairwise (fun a b : α => a ≠ b) l →
    ∀ (p p' : Nat × α), p ∈ enumFrom' n l → p' ∈ enumFrom' n l → p.2 = p'.2 →
    p.1 = p'.1
  | _, [], _, _, _, hp, _, _ => absurd hp (fun hc => List.not_mem_nil hc)
  | n, a :: l, hnd, p, p', hp, hp', heq => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hnd
      rcases List.mem_cons.mp hp with rfl | hp2
      · rcases List.mem_cons.mp hp' with rfl | hp2'
        · rfl
        · exact absurd heq (hhead p'.2 (enumFrom'_mem_snd (n + 1) l p' hp2'))
      · rcases List.mem_cons.mp hp' with rfl | hp2'
        · exact absurd heq.symm (hhead p.2 (enumFrom'_mem_snd (n + 1) l p hp2))
        · exact enumFrom'_snd_inj (n + 1) l htail p p' hp2 hp2' heq

/-- A legal response is the query answered by its own answer. -/
theorem legalResp_ansOf {α : Ty} {q : Query α} {r : Resp α} (h : LegalResp q r) :
    r = q.substAns r.ansOf ∧ RAns.Ok q r.ansOf := by
  obtain ⟨x, rfl, hok⟩ := h
  rw [Query.ansOf_substAns]
  exact ⟨rfl, hok⟩

/-- The numbered position that an entry of the enumeration contributes. -/
theorem psForArg_entry {α : Ty} {h : Fin α.arity}
    {a : Nat × Resp α} {b : Nat × Query (α.arg h)}
    (hga : (posOf h a.2).map (fun p => (a.1, p)) = some b) :
    posOf h a.2 = some b.2 ∧ a.1 = b.1 := by
  cases hp : posOf h a.2 with
  | none => rw [hp] at hga; exact absurd hga (fun hc => Option.noConfusion hc)
  | some pp =>
    rw [hp] at hga
    have heq : (a.1, pp) = b := Option.some.inj hga
    exact ⟨congrArg some (congrArg Prod.snd heq), congrArg Prod.fst heq⟩

/-- The positions the responses of `rs` graft into argument `h` are perimeter
positions of `q̂(h)`, and no two of them coincide. -/
theorem goodPositions_psForArg {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp α => a ≠ b) rs) (h : Fin α.arity) :
    GoodPositions (q.ctx h) (psForArg rs h) := by
  have hlq : ∀ np ∈ psForArg rs h, LegalQuery (q.ctx h) np.2 := by
    intro np hnp
    obtain ⟨r, hmem, hpos⟩ := (mem_psForArg rs h np).mp hnp
    have hr : r ∈ rs := enumFrom'_mem_snd 0 rs (np.1, r) hmem
    obtain ⟨_, hok⟩ := legalResp_ansOf (hlegal r hr)
    rw [ansOf_of_posOf h r np.2 hpos] at hok
    exact hok
  refine ⟨fun np hnp => (hlq np hnp).1, ?_⟩
  refine pairwise_filterMap' _ (fun a b : Nat × Resp α => a.1 < b.1) _
    (enumFrom' 0 rs) (enumFrom'_pairwise_lt 0 rs) ?_
  intro a ha a' ha' b b' hab hga hga' hcon
  obtain ⟨hpa, hia⟩ := psForArg_entry hga
  obtain ⟨hpa', hia'⟩ := psForArg_entry hga'
  have h1 : a.2.ansOf = RAns.node h b.2 := ansOf_of_posOf h a.2 b.2 hpa
  have h2 : a'.2.ansOf = RAns.node h b.2 := by
    rw [ansOf_of_posOf h a'.2 b'.2 hpa', hcon]
  have hra : a.2 ∈ rs := enumFrom'_mem_snd 0 rs a ha
  have hra' : a'.2 ∈ rs := enumFrom'_mem_snd 0 rs a' ha'
  have heq : a.2 = a'.2 := by
    rw [(legalResp_ansOf (hlegal a.2 hra)).1,
      (legalResp_ansOf (hlegal a'.2 hra')).1, h1, h2]
  have : a.1 = a'.1 := enumFrom'_snd_inj 0 rs hnd a a' ha ha' heq
  omega

/-- Every graft index is a legal response number. -/
theorem psForArg_lt {α : Ty} (rs : List (Resp α)) (h : Fin α.arity)
    (np : Nat × Query (α.arg h)) (hnp : np ∈ psForArg rs h) : np.1 < rs.length := by
  obtain ⟨r, hmem, _⟩ := (mem_psForArg rs h np).mp hnp
  have := enumFrom'_lt 0 rs (np.1, r) hmem
  omega

/-- Every graft position is a legal query. -/
theorem psForArg_queryOk {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r) (h : Fin α.arity)
    (np : Nat × Query (α.arg h)) (hnp : np ∈ psForArg rs h) :
    QueryOk (α.arg h) np.2 := by
  obtain ⟨r, hmem, hpos⟩ := (mem_psForArg rs h np).mp hnp
  have hr : r ∈ rs := enumFrom'_mem_snd 0 rs (np.1, r) hmem
  obtain ⟨_, hok⟩ := legalResp_ansOf (hlegal r hr)
  rw [ansOf_of_posOf h r np.2 hpos] at hok
  exact hok.2

/-! ## The argument expressions `Bₕ` and what they denote -/

/-- The meaning of a closed expression does not depend on the environment. -/
theorem meaning_closed (M : Term SPCF) (hcl : Term.Closed M) (ρ : Ty)
    (E E' : Tmodel.Env) : Tmodel.meaning E M ρ = Tmodel.meaning E' M ρ :=
  Model.combMeaning_congr_env E E' _ ρ fun z ν hz =>
    absurd (Term.FV_toComb M (z, ν) hz) (hcl (z, ν))

/-- The tree `e_h` of §5: the tree context `q̂(h)`, padded with the response
arguments and grafted with a probe at each position a response asks about. -/
noncomputable def graftFor {α : Ty} (q : Query α) (rs : List (Resp α))
    (h : Fin α.arity) : Tree (Ty.pads rs.length (α.arg h)) :=
  graftT rs.length (q.ctx h) (psForArg rs h)

theorem graftFor_ok {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp α => a ≠ b) rs)
    (h : Fin α.arity) (hctx : TreeOk (Ctx.empty : Ctx (α.arg h)) (q.ctx h)) :
    TreeOk (Ctx.empty : Ctx (Ty.pads rs.length (α.arg h))) (graftFor q rs h) :=
  TreeOk_graftT rs.length (q.ctx h) (psForArg rs h)
    (goodPositions_psForArg q rs hlegal hnd h)
    (psForArg_queryOk q rs hlegal h) (psForArg_lt rs h) hctx

/-- `b_h`: the value of the argument expression `B_h` when the response
variables carry the flat values `ws`. -/
noncomputable def argVal {α : Ty} (q : Query α) (rs : List (Resp α))
    (h : Fin α.arity) (ws : Nat → Val) : Tree (α.arg h) :=
  applyFront rs.length (graftFor q rs h) (fun k => Tree.leaf (ws k))

/-- `b_h` extends what `q` records about argument `h`. -/
theorem le_argVal {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp α => a ≠ b) rs)
    (h : Fin α.arity) (ws : Nat → Val) :
    Tree.Le (q.ctx h) (argVal q rs h ws) :=
  applyFront_graftT_le rs.length (q.ctx h) (psForArg rs h)
    (goodPositions_psForArg q rs hlegal hnd h) _

/-- At the position a numbered response asks about, `b_h` reports that
response's flat value. -/
theorem at'_argVal_probe {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp α => a ≠ b) rs)
    (h : Fin α.arity) (ws : Nat → Val) (n : Nat) (r : Resp α)
    (p : Query (α.arg h)) (hmem : (n, r) ∈ enumFrom' 0 rs)
    (hAns : r.ansOf = RAns.node h p) :
    (argVal q rs h ws).at' p = some (probeVal (α.arg h) (ws n)) := by
  have hnp : ((n, p) : Nat × Query (α.arg h)) ∈ psForArg rs h :=
    (mem_psForArg rs h (n, p)).mpr ⟨r, hmem, posOf_of_ansOf h r p hAns⟩
  exact applyFront_graftT_probe rs.length (q.ctx h) (psForArg rs h)
    (goodPositions_psForArg q rs hlegal hnd h) _ ws (fun k => rfl) (n, p) hnp
    (psForArg_lt rs h (n, p) hnp)

/-- At a perimeter position no response asks about, `b_h` is still `⊥`. -/
theorem at'_argVal_bot {α : Ty} (q : Query α) (rs : List (Resp α))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp α => a ≠ b) rs)
    (h : Fin α.arity) (ws : Nat → Val) (p : Query (α.arg h))
    (hp : (q.ctx h).at' p = some Tree.bot)
    (hnot : ∀ np ∈ psForArg rs h, np.2 ≠ p) :
    (argVal q rs h ws).at' p = some Tree.bot := by
  have h1 := at'_graftT_bot rs.length (q.ctx h) (psForArg rs h)
    (goodPositions_psForArg q rs hlegal hnd h) p hp hnot
  have h2 := at'_applyFront rs.length p (graftFor q rs h)
    (fun k => Tree.leaf (ws k)) Tree.bot h1
  rw [show applyFront rs.length (Tree.bot : Tree (Ty.pads rs.length (α.arg h)))
      (fun k => Tree.leaf (ws k)) = Tree.bot from by
    rw [show (Tree.bot : Tree (Ty.pads rs.length (α.arg h)))
        = Tree.padN rs.length (Tree.bot : Tree (α.arg h)) from
      (Tree.padN_leaf rs.length Val.bot).symm]
    exact applyFront_padN rs.length Tree.bot _] at h2
  exact h2

/-- **The body of `M'`.**  In an environment binding `x_i` to a finite argument
and the response variables to flat values, `(x_i B₁ … B_l)` denotes the
application of that argument to the `b_h`. -/
theorem meaning_inner {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Env : Tmodel.Env) (dsi : D (σ.arg i)) (ws : Nat → Val)
    (hx : Env i.val (σ.arg i) = Ideal.principal dsi)
    (hy : ∀ n, n < rs.length → Env (σ.arity + n) 𝕆 = leafT 𝕆 (ws n))
    (Γ : List (Nat × Ty)) (hΓ : ∀ n, n < rs.length → (σ.arity + n, 𝕆) ∈ Γ) :
    Tmodel.meaning Env (Term.apps (Term.var i.val (σ.arg i))
        (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length))) 𝕆
      = Ideal.principal (groundD (applyArgs (σ.arg i) dsi.1
          (fun h => argVal q rs h ws))) := by
  have hBty : ∀ h : Fin (σ.arg i).arity,
      Term.HasTy Γ (appsFrom (Es h) σ.arity rs.length) ((σ.arg i).arg h) := by
    intro h
    refine appsFrom_hasTy rs.length (Es h) σ.arity Γ ?_ (fun k hk => hΓ k hk)
    exact Term.weaken (fun p hp => absurd hp (fun hc => List.not_mem_nil hc))
      (hEs_ty h)
  have hBmean : ∀ h : Fin (σ.arg i).arity,
      Tmodel.meaning Env (appsFrom (Es h) σ.arity rs.length) ((σ.arg i).arg h)
        = Ideal.principal (applyFrontD rs.length ⟨graftFor q rs h, hgok h⟩ ws) := by
    intro h
    refine meaning_appsFrom rs.length (Es h) σ.arity Env ⟨graftFor q rs h, hgok h⟩ ws ?_
      (fun k hk => hy k hk)
    rw [meaning_closed (Es h) (hEs_cl h) _ Env botEnv]
    exact hEs_mean h
  rw [meaning_apps_env (σ.arg i) Env Γ (Term.var i.val (σ.arg i))
      (fun h => appsFrom (Es h) σ.arity rs.length)
      (fun h => Ideal.principal (applyFrontD rs.length ⟨graftFor q rs h, hgok h⟩ ws))
      hBty hBmean]
  have hvar : Tmodel.meaning Env (Term.var i.val (σ.arg i)) (σ.arg i)
      = Ideal.principal dsi := by
    show Tmodel.combMeaning Env (.var i.val (σ.arg i)) (σ.arg i) = _
    rw [Model.combMeaning_var]
    exact hx
  rw [hvar, applyIdeals_principal (σ.arg i) dsi
    (fun h => applyFrontD rs.length ⟨graftFor q rs h, hgok h⟩ ws)]
  refine congrArg (fun t => Ideal.principal (groundD t))
    (congrArg (applyArgs (σ.arg i) dsi.1) (funext fun h => ?_))
  exact applyFrontD_val rs.length ⟨graftFor q rs h, hgok h⟩ ws

/-! ## `M'` and the value `catch` reports -/

/-- The typing of the body of `M'`. -/
theorem inner_hasTy {σ : Ty} (i : Fin σ.arity) (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (Γ : List (Nat × Ty)) (hxΓ : (i.val, σ.arg i) ∈ Γ)
    (hyΓ : ∀ n, n < rs.length → (σ.arity + n, 𝕆) ∈ Γ) :
    Term.HasTy Γ (Term.apps (Term.var i.val (σ.arg i))
      (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length))) 𝕆 := by
  have hgen : ∀ (τ : Ty) (M : Term SPCF), Term.HasTy Γ M τ →
      ∀ (E : (h : Fin τ.arity) → Term SPCF),
      (∀ h, Term.HasTy Γ (E h) (τ.arg h)) →
      Term.HasTy Γ (Term.apps M (List.ofFn E)) 𝕆 := by
    intro τ
    induction τ with
    | base =>
      intro M hM E _
      rw [show (List.ofFn E : List (Term SPCF)) = [] from List.ofFn_zero]
      exact hM
    | arrow a b iha ihb =>
      intro M hM E hE
      have hsucc : (List.ofFn E : List (Term SPCF))
          = E ⟨0, Nat.succ_pos _⟩ :: List.ofFn fun j : Fin b.arity =>
              E ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
        rw [List.ofFn_succ]; rfl
      rw [show Term.apps M (List.ofFn E)
          = Term.apps (.app M (E ⟨0, Nat.succ_pos _⟩))
              (List.ofFn fun j : Fin b.arity =>
                E ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) from by rw [hsucc]; rfl]
      exact ihb _ (Term.HasTy.app hM (hE ⟨0, Nat.succ_pos _⟩)) _
        (fun j => hE ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
  refine hgen (σ.arg i) _ (Term.HasTy.var hxΓ) _ (fun h => ?_)
  exact appsFrom_hasTy rs.length (Es h) σ.arity Γ
    (Term.weaken (fun p hp => absurd hp (fun hc => List.not_mem_nil hc))
      (hEs_ty h)) (fun k hk => hyΓ k hk)

/-- The `x`-variable of `M` is not one of the response variables of `M'`. -/
theorem xvar_not_mem_yvars {σ : Ty} (i : Fin σ.arity) (m : Nat) :
    ¬ ((i.val, σ.arg i) ∈ yvars σ.arity m) := by
  intro hmem
  have h := yvars_fst_ge m σ.arity (i.val, σ.arg i) hmem
  exact absurd i.isLt (by omega)

/-- **`M'` is a constant.**  If the application `(x_i B̄)` denotes the leaf `v`
whatever flat values the response variables carry, then `M'` denotes `v`. -/
theorem catchBody_const {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Env : Tmodel.Env) (dsi : D (σ.arg i))
    (hx : Env i.val (σ.arg i) = Ideal.principal dsi)
    (Γ : List (Nat × Ty)) (hxΓ : (i.val, σ.arg i) ∈ Γ)
    (v : Val)
    (hconst : ∀ ws : Nat → Val,
      applyArgs (σ.arg i) dsi.1 (fun h => argVal q rs h ws) = Tree.leaf v) :
    Tmodel.meaning Env (catchBody σ i rs.length Es) (Ty.pads rs.length 𝕆)
      = leafT (Ty.pads rs.length 𝕆) v := by
  classical
  have hyΓ : ∀ n, n < rs.length →
      (σ.arity + n, 𝕆) ∈ (yvars σ.arity rs.length ++ Γ) :=
    fun n hn => List.mem_append_left _ (mem_yvars rs.length σ.arity n hn)
  have hty := inner_hasTy i rs Es hEs_ty (yvars σ.arity rs.length ++ Γ)
    (List.mem_append_right _ hxΓ) hyΓ
  have hgoal : Tmodel.combMeaning Env
      (Comb.lamStars (yvars σ.arity rs.length)
        (Term.toComb (Term.apps (Term.var i.val (σ.arg i))
          (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length)))))
      ((yvars σ.arity rs.length).foldr (fun p τ => p.2 ⇒ τ) 𝕆)
      = leafT _ v := by
    refine lamStars_meaning_leaf (yvars σ.arity rs.length) Env _ 𝕆 Γ
      (Term.toComb_hasTy hty) v (fun Env' hEnv' => ?_)
    -- the response variables carry flat values, whatever `Env'` says
    have hws : ∀ n : Nat, ∃ w : Val,
        Env' (σ.arity + n) 𝕆 = leafT 𝕆 w :=
      fun n => T_ground_flat (Env' (σ.arity + n) 𝕆)
    have hxEnv' : Env' i.val (σ.arg i) = Ideal.principal dsi := by
      rw [hEnv' (i.val, σ.arg i) (xvar_not_mem_yvars i rs.length)]
      exact hx
    have hmean := meaning_inner i q rs Es hEs_cl hEs_ty hgok hEs_mean Env' dsi
      (fun n => Classical.choose (hws n)) hxEnv'
      (fun n _ => Classical.choose_spec (hws n))
      (yvars σ.arity rs.length ++ Γ) hyΓ
    show Tmodel.meaning Env' (Term.apps (Term.var i.val (σ.arg i))
      (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length))) 𝕆 = _
    rw [hmean, hconst (fun n => Classical.choose (hws n))]
    rfl
  show Tmodel.combMeaning Env
    (Term.toComb (Term.lams (yvars σ.arity rs.length) _)) _ = _
  rw [Term.toComb_lams]
  rw [show (Ty.pads rs.length 𝕆)
      = (yvars σ.arity rs.length).foldr (fun p τ => p.2 ⇒ τ) 𝕆 from
    (foldX_yvars rs.length σ.arity).symm]
  exact hgoal

/-- `leafT` determines its value. -/
theorem leafT_inj {σ : Ty} {v w : Val} (h : leafT σ v = leafT σ w) : v = w := by
  have h1 := Ideal.principal_inj h
  have h2 : (Tree.leaf v : Tree σ) = Tree.leaf w := congrArg Subtype.val h1
  injection h2

/-- **A run of `M'`.**  Feeding the response variables flat values computes the
application of the argument to the `b_h`. -/
theorem catchBody_run {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Env : Tmodel.Env) (dsi : D (σ.arg i))
    (hx : Env i.val (σ.arg i) = Ideal.principal dsi)
    (Γ : List (Nat × Ty)) (hxΓ : (i.val, σ.arg i) ∈ Γ)
    (vs : ∀ p : Nat × Ty, T p.2) (ws : Nat → Val)
    (hvs : ∀ n, n < rs.length → vs (σ.arity + n, 𝕆) = leafT 𝕆 (ws n)) :
    applyTChainX (yvars σ.arity rs.length)
        (Tmodel.meaning Env (catchBody σ i rs.length Es) (foldX (yvars σ.arity rs.length))) vs
      = Ideal.principal (groundD (applyArgs (σ.arg i) dsi.1
          (fun h => argVal q rs h ws))) := by
  have hyΓ : ∀ n, n < rs.length →
      (σ.arity + n, 𝕆) ∈ (yvars σ.arity rs.length ++ Γ) :=
    fun n hn => List.mem_append_left _ (mem_yvars rs.length σ.arity n hn)
  have hty := inner_hasTy i rs Es hEs_ty (yvars σ.arity rs.length ++ Γ)
    (List.mem_append_right _ hxΓ) hyΓ
  have hpeel := lamStars_peel (yvars σ.arity rs.length) Env
    (Term.toComb (Term.apps (Term.var i.val (σ.arg i))
      (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length)))) Γ
    (Term.toComb_hasTy hty) vs
  have hM' : Tmodel.meaning Env (catchBody σ i rs.length Es)
      (foldX (yvars σ.arity rs.length))
      = Tmodel.combMeaning Env (Comb.lamStars (yvars σ.arity rs.length)
          (Term.toComb (Term.apps (Term.var i.val (σ.arg i))
            (List.ofFn (fun h => appsFrom (Es h) σ.arity rs.length)))))
          (foldX (yvars σ.arity rs.length)) := by
    show Tmodel.combMeaning Env
      (Term.toComb (Term.lams (yvars σ.arity rs.length) _)) _ = _
    rw [Term.toComb_lams]
  rw [hM', hpeel]
  have hxU : (updEnvX (yvars σ.arity rs.length) Env vs) i.val (σ.arg i)
      = Ideal.principal dsi := by
    rw [updEnvX_other (yvars σ.arity rs.length) Env vs i.val (σ.arg i)
      (fun p hp hc => by
        have h := yvars_fst_ge rs.length σ.arity p hp
        have : i.val = p.1 := hc.1
        omega)]
    exact hx
  have hyU : ∀ n, n < rs.length →
      (updEnvX (yvars σ.arity rs.length) Env vs) (σ.arity + n) 𝕆
        = leafT 𝕆 (ws n) := by
    intro n hn
    rw [show (updEnvX (yvars σ.arity rs.length) Env vs) (σ.arity + n) 𝕆
        = vs (σ.arity + n, 𝕆) from
      updEnvX_lookup (yvars σ.arity rs.length) Env vs (σ.arity + n, 𝕆)
        (mem_yvars rs.length σ.arity n hn)]
    exact hvs n hn
  exact meaning_inner i q rs Es hEs_cl hEs_ty hgok hEs_mean
    (updEnvX (yvars σ.arity rs.length) Env vs) dsi ws hxU hyU
    (yvars σ.arity rs.length ++ Γ) hyΓ

/-! ## What `catch` reports -/

theorem meaning_catch (Env : Tmodel.Env) (M' : Term SPCF) (σ' : Ty)
    (Γ : List (Nat × Ty)) (hM' : Term.HasTy Γ M' σ') :
    Tmodel.meaning Env (Term.app (Term.const (SConst.catchC σ')) M') 𝕆
      = applyT (idealOf (treeCatch σ')) (Tmodel.meaning Env M' σ') := by
  rw [meaning_app_term Env _ M' σ' 𝕆 Γ hM']
  have hc : Tmodel.meaning Env (Term.const (SConst.catchC σ')) (σ' ⇒ 𝕆)
      = idealOf (treeCatch σ') :=
    Model.combMeaning_const Tmodel Env (SConst.catchC σ')
  rw [hc]

/-- `catch` of a constant procedure. -/
theorem applyT_catch_leafT (σ' : Ty) (v : Val) :
    applyT (idealOf (treeCatch σ')) (leafT σ' v)
      = leafT 𝕆 (match v with
          | .num a => Val.num (a + σ'.arity)
          | w => w) := by
  cases v with
  | bot =>
    show applyT (idealOf (treeCatch σ')) (leafT σ' .bot) = leafT 𝕆 .bot
    rw [treeCatch]
    exact applyT_rootProbe_bot (Nat.succ_pos _) _
  | err b =>
    show applyT (idealOf (treeCatch σ')) (leafT σ' (.err b)) = leafT 𝕆 (.err b)
    rw [treeCatch]
    exact applyT_rootProbe_err (Nat.succ_pos _) _ b
  | num a =>
    show applyT (idealOf (treeCatch σ')) (leafT σ' (.num a))
      = leafT 𝕆 (.num (a + σ'.arity))
    exact applyT_catch_num σ' a

theorem arity_pads_base (m : Nat) : (Ty.pads m 𝕆).arity = m := by
  rw [Ty.arity_pads]
  rfl

/-- The flat values the two runs of `M'` feed the response variables. -/
def wsBot : Nat → Val := fun _ => Val.bot

/-- The flat values of the error run at index `n`. -/
noncomputable def wsErrAt (n : Nat) : Nat → Val :=
  fun k => if k = n then Val.err true else Val.bot

/-- The typing of `M'`. -/
theorem catchBody_hasTy {σ : Ty} (i : Fin σ.arity) (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (Γ : List (Nat × Ty)) (hxΓ : (i.val, σ.arg i) ∈ Γ) :
    Term.HasTy Γ (catchBody σ i rs.length Es) (Ty.pads rs.length 𝕆) := by
  have hyΓ : ∀ n, n < rs.length →
      (σ.arity + n, 𝕆) ∈ (yvars σ.arity rs.length ++ Γ) :=
    fun n hn => List.mem_append_left _ (mem_yvars rs.length σ.arity n hn)
  have hty := inner_hasTy i rs Es hEs_ty (yvars σ.arity rs.length ++ Γ)
    (List.mem_append_right _ hxΓ) hyΓ
  have h := Term.lams_hasTy (yvars σ.arity rs.length) Γ _ 𝕆 hty
  rw [show (Ty.pads rs.length 𝕆)
      = (yvars σ.arity rs.length).foldr (fun p τ => p.2 ⇒ τ) 𝕆 from
    (foldX_yvars rs.length σ.arity).symm]
  exact h

/-- **`catch` reports the response the argument realises.**  If the `⊥`-run of
`M'` diverges and the run that errs at the `n`-th response variable errs, then
`(catch M')` is `n`. -/
theorem catchVal_node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i)))
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Env : Tmodel.Env) (dsi : D (σ.arg i))
    (hx : Env i.val (σ.arg i) = Ideal.principal dsi)
    (Γ : List (Nat × Ty)) (hxΓ : (i.val, σ.arg i) ∈ Γ)
    (n : Nat) (hn : n < rs.length)
    (hrunB : applyArgs (σ.arg i) dsi.1 (fun h => argVal q rs h wsBot) = Tree.bot)
    (hrunE : applyArgs (σ.arg i) dsi.1 (fun h => argVal q rs h (wsErrAt n))
      = Tree.leaf (.err true)) :
    Tmodel.meaning Env (Term.app
        (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
        (catchBody σ i rs.length Es)) 𝕆 = natAns n := by
  have hjlen : n < (yvars σ.arity rs.length).length := by
    rw [yvars_length]; exact hn
  have hy : (yvars σ.arity rs.length)[n]'hjlen = (σ.arity + n, 𝕆) :=
    yvars_getElem rs.length σ.arity n hjlen
  -- the two runs
  have hB : applyTChainX (yvars σ.arity rs.length)
      (Tmodel.meaning Env (catchBody σ i rs.length Es)
        (foldX (yvars σ.arity rs.length))) vsBot = leafT 𝕆 .bot := by
    rw [catchBody_run i q rs Es hEs_cl hEs_ty hgok hEs_mean Env dsi hx Γ hxΓ
      vsBot wsBot (fun n' _ => rfl), hrunB]
    rfl
  have hE : applyTChainX (yvars σ.arity rs.length)
      (Tmodel.meaning Env (catchBody σ i rs.length Es)
        (foldX (yvars σ.arity rs.length)))
      (vsErr (σ.arity + n) 𝕆) = leafT 𝕆 (.err true) := by
    rw [catchBody_run i q rs Es hEs_cl hEs_ty hgok hEs_mean Env dsi hx Γ hxΓ
      (vsErr (σ.arity + n) 𝕆) (wsErrAt n) (fun n' _ => ?_), hrunE]
    · rfl
    · show (if ((σ.arity + n', 𝕆) : Nat × Ty) = (σ.arity + n, 𝕆) then _ else _)
        = leafT 𝕆 (wsErrAt n n')
      by_cases hnn : n' = n
      · subst hnn
        rw [if_pos rfl, wsErrAt, if_pos rfl]
      · rw [if_neg (fun hc => hnn (by
          have hc2 := congrArg Prod.fst hc
          simp only at hc2
          omega)), wsErrAt, if_neg hnn]
  -- the root shape, and hence the value of `catch`
  have hshape := root_shape_of_runs (yvars σ.arity rs.length)
    (Tmodel.meaning Env (catchBody σ i rs.length Es)
      (foldX (yvars σ.arity rs.length))) ⟨n, hjlen⟩
    (fun j' hj' hc => by
      rw [yvars_getElem rs.length σ.arity j'.val j'.isLt, hy] at hc
      refine hj' ?_
      have hc2 : σ.arity + j'.val = σ.arity + n := congrArg Prod.fst hc
      exact Nat.add_left_cancel hc2)
    hB (by rw [hy]; exact hE)
  have hcatch := applyT_catch_gen (foldX (yvars σ.arity rs.length))
    (Tmodel.meaning Env (catchBody σ i rs.length Es)
      (foldX (yvars σ.arity rs.length))) n
    (by rw [arity_foldrX, yvars_length]; exact hn)
    (by
      obtain ⟨s, hs, g, hg⟩ := hshape.1
      exact ⟨s, hs, g, hg⟩)
    (fun s hs => by
      rcases hshape.2 s hs with h1 | ⟨g, hg⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g, hg⟩)
  rw [meaning_catch Env _ (Ty.pads rs.length 𝕆) Γ ?_]
  · rw [show (Ty.pads rs.length 𝕆) = foldX (yvars σ.arity rs.length) from
      (foldX_yvars rs.length σ.arity).symm]
    exact hcatch
  · -- typing of `M'`
    refine catchBody_hasTy i rs Es hEs_ty Γ hxΓ

/-! ## Typing implies closedness -/

/-- A well-typed phrase has its free variables in its typing context. -/
theorem Term.fv_subset_of_hasTy {L : Lang} : ∀ {Γ : List (Nat × Ty)} {M : Term L}
    {ρ : Ty}, Term.HasTy Γ M ρ → ∀ p, p ∈ Term.FV M → p ∈ Γ := by
  intro Γ M ρ h
  induction h with
  | var hx => intro p hp; exact (hp : p = _) ▸ hx
  | const => intro p hp; exact absurd hp (fun hc => hc)
  | app _ _ ihM ihN =>
    intro p hp
    rcases (hp : p ∈ Term.FV _ ∪ Term.FV _) with h1 | h1
    · exact ihM p h1
    · exact ihN p h1
  | lam _ ih =>
    intro p hp
    obtain ⟨hp1, hp2⟩ : p ∈ Term.FV _ ∧ p ≠ _ := hp
    rcases List.mem_cons.mp (ih p hp1) with h1 | h1
    · exact absurd h1 hp2
    · exact h1

theorem Term.closed_of_hasTy {L : Lang} {M : Term L} {ρ : Ty}
    (h : Term.HasTy [] M ρ) : Term.Closed M :=
  fun p hp => absurd (Term.fv_subset_of_hasTy h p hp) (fun hc => List.not_mem_nil hc)

/-! ## The arms of the case split -/

/-- The meaning of an arm `(F x₁ … x_k)`. -/
theorem meaning_arm (σ : Ty) (Env : Tmodel.Env) (F : Term SPCF)
    (Γ : List (Nat × Ty)) (hΓ : ∀ j : Fin σ.arity, (j.val, σ.arg j) ∈ Γ)
    (ds : (j : Fin σ.arity) → T (σ.arg j))
    (hEnv : ∀ j : Fin σ.arity, Env j.val (σ.arg j) = ds j) :
    Tmodel.meaning Env (Term.apps F (xargs σ)) 𝕆
      = applyIdeals σ (Tmodel.meaning Env F σ) ds := by
  refine meaning_apps_env σ Env Γ F
    (fun j : Fin σ.arity => (Term.var j.val (σ.arg j) : Term SPCF)) ds
    (fun j => Term.HasTy.var (hΓ j)) (fun j => ?_)
  show Tmodel.combMeaning Env (.var j.val (σ.arg j)) (σ.arg j) = ds j
  rw [Model.combMeaning_var]
  exact hEnv j

theorem arm_hasTy (σ : Ty) (F : Term SPCF) (Γ : List (Nat × Ty))
    (hΓ : ∀ j : Fin σ.arity, (j.val, σ.arg j) ∈ Γ) (hF : Term.HasTy Γ F σ) :
    Term.HasTy Γ (Term.apps F (xargs σ)) 𝕆 := by
  have hgen : ∀ (τ : Ty) (M : Term SPCF), Term.HasTy Γ M τ →
      ∀ (E : (h : Fin τ.arity) → Term SPCF),
      (∀ h, Term.HasTy Γ (E h) (τ.arg h)) →
      Term.HasTy Γ (Term.apps M (List.ofFn E)) 𝕆 := by
    intro τ
    induction τ with
    | base =>
      intro M hM E _
      rw [show (List.ofFn E : List (Term SPCF)) = [] from List.ofFn_zero]
      exact hM
    | arrow a b iha ihb =>
      intro M hM E hE
      have hsucc : (List.ofFn E : List (Term SPCF))
          = E ⟨0, Nat.succ_pos _⟩ :: List.ofFn fun j : Fin b.arity =>
              E ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
        rw [List.ofFn_succ]; rfl
      rw [show Term.apps M (List.ofFn E)
          = Term.apps (.app M (E ⟨0, Nat.succ_pos _⟩))
              (List.ofFn fun j : Fin b.arity =>
                E ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) from by rw [hsucc]; rfl]
      exact ihb _ (Term.HasTy.app hM (hE ⟨0, Nat.succ_pos _⟩)) _
        (fun j => hE ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
  exact hgen σ F hF _ (fun j => Term.HasTy.var (hΓ j))

/-- The keys of the case split ascend. -/
theorem caseArms_pairwise (σ : Ty) (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i))) (A : Nat) (Fs : Resp (σ.arg i) → Term SPCF) :
    List.Pairwise (fun p p' : Nat × Term SPCF => p.1 < p'.1)
      (caseArms σ i q rs A Fs) := by
  rw [caseArms, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact enumFrom'_pairwise_lt 0 rs
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro a b hab
    exact Nat.add_lt_add_left hab _
  · intro a ha b hb
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have h1 : pr.1 < rs.length := by
      have := enumFrom'_lt 0 rs pr hpr
      omega
    show pr.1 < rs.length + c
    omega

theorem caseArms_hasTy (σ : Ty) (i : Fin σ.arity) (q : Query (σ.arg i))
    (rs : List (Resp (σ.arg i))) (A : Nat) (Fs : Resp (σ.arg i) → Term SPCF)
    (Γ : List (Nat × Ty)) (hΓ : ∀ j : Fin σ.arity, (j.val, σ.arg j) ∈ Γ)
    (hFs : ∀ r, Term.HasTy Γ (Fs r) σ) :
    ∀ p ∈ caseArms σ i q rs A Fs, Term.HasTy Γ p.2 𝕆 := by
  intro p hp
  rw [caseArms, List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨pr, _, rfl⟩ := List.mem_map.mp hp
    exact arm_hasTy σ (Fs pr.2) Γ hΓ (hFs _)
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact arm_hasTy σ _ Γ hΓ (hFs _)

/-! ## Corollary 4.15 for the construction -/

/-- The application `(x_i B̄)` sees only the subtree of the argument at `q`. -/
theorem inner_value {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i)) (γ : Ctx σ)
    (hγ : CtxOk γ) (hq : LegalQuery (γ i) q) (rs : List (Resp (σ.arg i)))
    (hlegal : ∀ r ∈ rs, LegalResp q r)
    (hnd : List.Pairwise (fun a b : Resp (σ.arg i) => a ≠ b) rs)
    (di : Tree (σ.arg i)) (e : Tree (σ.arg i)) (hat : di.at' q = some e)
    (ws : Nat → Val) :
    applyArgs (σ.arg i) di (fun h => argVal q rs h ws)
      = applyArgs (σ.arg i) e (fun h => argVal q rs h ws) := by
  refine applyArgs_at_query (σ.arg i) q di e _ (QueryOk.coherent hq.2) hat
    (fun h => ?_)
  exact RespCtx.Above.mono
    (above_ctx_of_TreeOk (CtxOk.treeOk hγ i) hq.1 hq.2 h)
    (le_argVal q rs hlegal hnd h ws)

/-- The response a node subtree realises is legal for `q`. -/
theorem legalResp_of_at'_node {α : Ty} {q : Query α} {d : Tree α}
    {h : Fin α.arity} {p : Query (α.arg h)}
    {g : Resp (α.arg h) → Tree α}
    (hd : TreeOk (Ctx.empty : Ctx α) d)
    (hat : d.at' q = some (.node h p g)) :
    LegalResp q (q.substAns (RAns.node h p)) := by
  have hsub : TreeOk (q.ctxFrom (Ctx.empty : Ctx α)) (.node h p g) :=
    TreeOk_at' q Ctx.empty d _ hd hat
  obtain ⟨hlq, _, _, _⟩ := TreeOk_node_inv hsub
  exact ⟨RAns.node h p, rfl, hlq⟩

/-! ## The node case of Lemma 5.2 -/

/-- **The construction of §5 represents the node.** -/
theorem representable_node_of {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (γ : Ctx σ) (hγ : CtxOk γ)
    (hok : TreeOk γ (Tree.node i q f))
    (rs : List (Resp (σ.arg i))) (A : Nat)
    (hrs_legal : ∀ r ∈ rs, LegalResp q r)
    (hrs_nd : List.Pairwise (fun a b : Resp (σ.arg i) => a ≠ b) rs)
    (hrs_cover : ∀ (h : Fin (σ.arg i).arity) (p : Query ((σ.arg i).arg h)),
      f (q.substAns (RAns.node h p)) ≠ Tree.bot →
      q.substAns (RAns.node h p) ∈ rs)
    (hA : ∀ a : Nat, f (q.substAns (RAns.num a)) ≠ Tree.bot → a ≤ A)
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Fs : Resp (σ.arg i) → Term SPCF)
    (hFs_ty : ∀ r, Term.HasTy [] (Fs r) σ)
    (hFs_mean : ∀ r, LegalResp q r → ∀ ds : (j : Fin σ.arity) → D (σ.arg j),
      (∀ j, Ctx.Above (γ.cons i r) j (ds j).1) →
      applyIdeals σ (Tmodel.meaning botEnv (Fs r) σ)
          (fun j => Ideal.principal (ds j))
        = Ideal.principal (groundD (applyArgs σ (f r) (fun j => (ds j).1)))) :
    Representable σ γ (Tree.node i q f) := by
  classical
  obtain ⟨hq, hfin, hsub, hnon⟩ := TreeOk_node_inv hok
  have hxΓ : ∀ j : Fin σ.arity, (j.val, σ.arg j) ∈ varsFrom 0 σ.args := by
    intro j
    have h := mem_varsFrom σ 0 j
    rwa [Nat.zero_add] at h
  -- the pieces of `M`
  have hWty : Term.HasTy (varsFrom 0 σ.args)
      (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
        (catchBody σ i rs.length Es)) 𝕆 :=
    Term.HasTy.app Term.HasTy.const
      (catchBody_hasTy i rs Es hEs_ty _ (hxΓ i))
  have hxΓ' : ∀ j : Fin σ.arity,
      (j.val, σ.arg j) ∈ ((σ.arity + rs.length, 𝕆) :: varsFrom 0 σ.args) :=
    fun j => List.mem_cons_of_mem _ (hxΓ j)
  have hcasty : Term.HasTy ((σ.arity + rs.length, 𝕆) :: varsFrom 0 σ.args)
      (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
        (caseArms σ i q rs A Fs)) 𝕆 :=
    cascadeTerm_hasTy _ _ _ (Term.HasTy.var (List.mem_cons_self ..))
      (caseArms_hasTy σ i q rs A Fs _ hxΓ' (fun r =>
        Term.weaken (fun p hp => absurd hp (fun hc => List.not_mem_nil hc))
          (hFs_ty r)))
  have hbody : Term.HasTy (varsFrom 0 σ.args ++ [])
      (Term.app (Term.lam (σ.arity + rs.length) 𝕆
        (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
          (caseArms σ i q rs A Fs)))
        (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
          (catchBody σ i rs.length Es))) 𝕆 := by
    rw [List.append_nil]
    exact Term.HasTy.app (Term.HasTy.lam hcasty) hWty
  have htyM : Term.HasTy [] (nodeTerm σ i q rs A Es Fs) σ :=
    lams_varsFrom_hasTy σ 0 _ [] hbody
  refine ⟨nodeTerm σ i q rs A Es Fs, Term.closed_of_hasTy htyM, htyM, ?_⟩
  intro ds hds
  rw [show nodeTerm σ i q rs A Es Fs
      = Term.lams (varsFrom 0 σ.args)
        (Term.app (Term.lam (σ.arity + rs.length) 𝕆
          (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
            (caseArms σ i q rs A Fs)))
          (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
            (catchBody σ i rs.length Es))) from rfl,
    applyIdeals_lams σ 0 botEnv _ [] hbody (fun j => Ideal.principal (ds j))]
  sorry

/-- **The body of `M` computes the node.**  With the arguments bound in `Env`,
`let w = catch M' in cascade` denotes exactly what applying the node to those
arguments gives. -/
theorem nodeBody_value {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (γ : Ctx σ) (hγ : CtxOk γ)
    (hq : LegalQuery (γ i) q)
    (rs : List (Resp (σ.arg i))) (A : Nat)
    (hrs_legal : ∀ r ∈ rs, LegalResp q r)
    (hrs_nd : List.Pairwise (fun a b : Resp (σ.arg i) => a ≠ b) rs)
    (hrs_cover : ∀ (h : Fin (σ.arg i).arity) (p : Query ((σ.arg i).arg h)),
      f (q.substAns (RAns.node h p)) ≠ Tree.bot →
      q.substAns (RAns.node h p) ∈ rs)
    (hA : ∀ a : Nat, f (q.substAns (RAns.num a)) ≠ Tree.bot → a ≤ A)
    (Es : (h : Fin (σ.arg i).arity) → Term SPCF)
    (hEs_cl : ∀ h, Term.Closed (Es h))
    (hEs_ty : ∀ h, Term.HasTy [] (Es h) (Ty.pads rs.length ((σ.arg i).arg h)))
    (hgok : ∀ h, TreeOk (Ctx.empty : Ctx (Ty.pads rs.length ((σ.arg i).arg h)))
      (graftFor q rs h))
    (hEs_mean : ∀ h, Tmodel.meaning botEnv (Es h)
        (Ty.pads rs.length ((σ.arg i).arg h))
      = Ideal.principal ⟨graftFor q rs h, hgok h⟩)
    (Fs : Resp (σ.arg i) → Term SPCF)
    (hFs_ty : ∀ r, Term.HasTy [] (Fs r) σ)
    (hFs_mean : ∀ r, LegalResp q r → ∀ ds : (j : Fin σ.arity) → D (σ.arg j),
      (∀ j, Ctx.Above (γ.cons i r) j (ds j).1) →
      applyIdeals σ (Tmodel.meaning botEnv (Fs r) σ)
          (fun j => Ideal.principal (ds j))
        = Ideal.principal (groundD (applyArgs σ (f r) (fun j => (ds j).1))))
    (ds : (j : Fin σ.arity) → D (σ.arg j))
    (hds : ∀ j, Ctx.Above γ j (ds j).1)
    (Env : Tmodel.Env)
    (hEnvx : ∀ j : Fin σ.arity, Env j.val (σ.arg j) = Ideal.principal (ds j))
    (Γ : List (Nat × Ty)) (hΓ : ∀ j : Fin σ.arity, (j.val, σ.arg j) ∈ Γ)
    (hw : ∀ (ν : Ty) (x : T ν),
      ∀ j : Fin σ.arity, Model.envUpdate Env (σ.arity + rs.length) ν x
        j.val (σ.arg j) = Ideal.principal (ds j)) :
    Tmodel.meaning Env (Term.app (Term.lam (σ.arity + rs.length) 𝕆
        (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
          (caseArms σ i q rs A Fs)))
        (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
          (catchBody σ i rs.length Es))) 𝕆
      = Ideal.principal (groundD (applyArgs σ (Tree.node i q f)
          (fun j => (ds j).1))) := by
  classical
  -- the subtree of the probed argument at `q`
  have hate : ∃ e', (ds i).1.at' q = some e' := by
    rcases at'_mono q (hds i : Tree.Le (γ i) (ds i).1) with hnone | ⟨_, e2, _, h2, _⟩
    · exact absurd (hq.1.symm.trans hnone) (fun hc => Option.noConfusion hc)
    · exact ⟨e2, h2⟩
  obtain ⟨e', hate'⟩ := hate
  -- the typing of the pieces
  have hWty : Term.HasTy Γ
      (Term.app (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
        (catchBody σ i rs.length Es)) 𝕆 :=
    Term.HasTy.app Term.HasTy.const
      (catchBody_hasTy i rs Es hEs_ty _ (hΓ i))
  have hΓ' : ∀ j : Fin σ.arity,
      (j.val, σ.arg j) ∈ ((σ.arity + rs.length, 𝕆) :: Γ) :=
    fun j => List.mem_cons_of_mem _ (hΓ j)
  have hFs_cl : ∀ r, Term.Closed (Fs r) := fun r => Term.closed_of_hasTy (hFs_ty r)
  have hFsΓ : ∀ r, Term.HasTy ((σ.arity + rs.length, 𝕆) :: Γ) (Fs r) σ :=
    fun r => Term.weaken (fun p hp => absurd hp (fun hc => List.not_mem_nil hc))
      (hFs_ty r)
  have hcasty : Term.HasTy ((σ.arity + rs.length, 𝕆) :: Γ)
      (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
        (caseArms σ i q rs A Fs)) 𝕆 :=
    cascadeTerm_hasTy _ _ _ (Term.HasTy.var (List.mem_cons_self ..))
      (caseArms_hasTy σ i q rs A Fs _ hΓ' hFsΓ)
  -- peel the `let`
  rw [meaning_app_term Env _ _ 𝕆 𝕆 Γ hWty,
    show Tmodel.meaning Env (Term.lam (σ.arity + rs.length) 𝕆
        (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
          (caseArms σ i q rs A Fs))) (𝕆 ⇒ 𝕆)
      = Tmodel.combMeaning Env (Comb.lamStar (σ.arity + rs.length) 𝕆
          (Term.toComb (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
            (caseArms σ i q rs A Fs)))) (𝕆 ⇒ 𝕆) from rfl,
    lamStar_apply Env (σ.arity + rs.length) 𝕆 _ _ 𝕆 Γ
      (Term.toComb_hasTy hcasty)]
  show Tmodel.meaning (Model.envUpdate Env (σ.arity + rs.length) 𝕆
      (Tmodel.meaning Env (Term.app
        (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
        (catchBody σ i rs.length Es)) 𝕆))
      (cascadeTerm (Term.var (σ.arity + rs.length) 𝕆)
        (caseArms σ i q rs A Fs)) 𝕆 = _
  -- the scrutinee
  have hscrut : ∀ x : T 𝕆,
      Tmodel.meaning (Model.envUpdate Env (σ.arity + rs.length) 𝕆 x)
        (Term.var (σ.arity + rs.length) 𝕆) 𝕆 = x := by
    intro x
    show Tmodel.combMeaning _ (.var (σ.arity + rs.length) 𝕆) 𝕆 = _
    rw [Model.combMeaning_var, Model.envUpdate_self]
  -- the value of an arm
  have harm : ∀ (x : T 𝕆) (r : Resp (σ.arg i)), LegalResp q r →
      Tree.Le r.toTree (ds i).1 →
      Tmodel.meaning (Model.envUpdate Env (σ.arity + rs.length) 𝕆 x)
          (Term.apps (Fs r) (xargs σ)) 𝕆
        = Ideal.principal (groundD (applyArgs σ (f r) (fun j => (ds j).1))) := by
    intro x r hr hle
    rw [meaning_arm σ _ (Fs r) ((σ.arity + rs.length, 𝕆) :: Γ) hΓ'
      (fun j => Ideal.principal (ds j)) (fun j => hw 𝕆 x j),
      meaning_closed (Fs r) (hFs_cl r) σ _ botEnv]
    exact hFs_mean r hr ds (Ctx.above_cons γ i r (fun j => (ds j).1) hds hle)
  -- the value of `catch M'` when `M'` is a constant
  have hcatchOf : ∀ v : Val,
      (∀ ws : Nat → Val, applyArgs (σ.arg i) (ds i).1
        (fun h => argVal q rs h ws) = Tree.leaf v) →
      Tmodel.meaning Env (Term.app
          (Term.const (SConst.catchC (Ty.pads rs.length 𝕆)))
          (catchBody σ i rs.length Es)) 𝕆
        = applyT (idealOf (treeCatch (Ty.pads rs.length 𝕆)))
            (leafT (Ty.pads rs.length 𝕆) v) := by
    intro v hv
    rw [meaning_catch Env _ (Ty.pads rs.length 𝕆) Γ
      (catchBody_hasTy i rs Es hEs_ty _ (hΓ i)),
      catchBody_const i q rs Es hEs_cl hEs_ty hgok hEs_mean Env (ds i)
        (hEnvx i) Γ (hΓ i) v hv]
  -- the arms are typed and ordered
  have harmsty : ∀ p ∈ caseArms σ i q rs A Fs,
      Term.HasTy ((σ.arity + rs.length, 𝕆) :: Γ) p.2 𝕆 :=
    caseArms_hasTy σ i q rs A Fs _ hΓ' hFsΓ
  have hsorted := caseArms_pairwise σ i q rs A Fs
  have hvarty : Term.HasTy ((σ.arity + rs.length, 𝕆) :: Γ)
      (Term.var (σ.arity + rs.length) 𝕆 : Term SPCF) 𝕆 :=
    Term.HasTy.var (List.mem_cons_self ..)
  -- the expected value
  rw [applyArgs_node σ i q f (fun j => (ds j).1), hate']
  cases e' with
  | leaf v =>
    have hconst : ∀ ws : Nat → Val, applyArgs (σ.arg i) (ds i).1
        (fun h => argVal q rs h ws) = Tree.leaf v := by
      intro ws
      rw [inner_value i q γ hγ hq rs hrs_legal hrs_nd (ds i).1 (Tree.leaf v)
        hate' ws]
      exact applyArgs_leaf (σ.arg i) v _
    rw [hcatchOf v hconst, applyT_catch_leafT (Ty.pads rs.length 𝕆) v]
    cases v with
    | bot =>
      show Tmodel.meaning _ _ 𝕆 = _
      rw [cascade_bot _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ) hvarty harmsty
        (by rw [hscrut])]
      rfl
    | err b =>
      show Tmodel.meaning _ _ 𝕆 = _
      rw [cascade_err _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ) b hvarty harmsty
        (by rw [hscrut])]
      rfl
    | num a =>
      have hleaf : Tree.Le (q.substAns (RAns.num a)).toTree (ds i).1 :=
        Resp.toTree_le_of_at'_num q (ds i).1 a hate'
      have hlegal : LegalResp q (q.substAns (RAns.num a)) := LegalResp.num q a
      have hscr : Tmodel.meaning (Model.envUpdate Env (σ.arity + rs.length) 𝕆
          (leafT 𝕆 (Val.num (a + (Ty.pads rs.length 𝕆).arity))))
          (Term.var (σ.arity + rs.length) 𝕆) 𝕆
          = leafT 𝕆 (Val.num (a + rs.length)) := by
        rw [hscrut, arity_pads_base]
      by_cases hcase : a ≤ A
      · -- the case split dispatches to the arm for the answer `a`
        have hmem : ((rs.length + a, Term.apps (Fs (q.substAns (RAns.num a)))
            (xargs σ)) : Nat × Term SPCF) ∈ caseArms σ i q rs A Fs := by
          rw [caseArms]
          refine List.mem_append_right _ (List.mem_map.mpr ⟨a, ?_, rfl⟩)
          exact List.mem_range.mpr (by omega)
        rw [cascade_num_hit _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ)
          (rs.length + a) _ hvarty harmsty hsorted
          (by rw [hscr, Nat.add_comm]) hmem]
        exact harm _ _ hlegal hleaf
      · -- no arm matches, and the branch is `⊥`
        have hfbot : f (q.substAns (RAns.num a)) = Tree.bot :=
          Classical.byContradiction fun hc => hcase (hA a hc)
        rw [cascade_num_miss _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ)
          (rs.length + a) hvarty harmsty (by rw [hscr, Nat.add_comm])
          (fun p hp => ?_)]
        · show leafT 𝕆 Val.bot = Ideal.principal (groundD
            (applyArgs σ (f (q.substAns (RAns.num a))) (fun j => (ds j).1)))
          rw [hfbot, show (Tree.bot : Tree σ) = Tree.leaf Val.bot from rfl,
            applyArgs_leaf σ Val.bot (fun j => (ds j).1)]
          rfl
        · rw [caseArms, List.mem_append] at hp
          rcases hp with hp | hp
          · obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hp
            have := enumFrom'_lt 0 rs pr hpr
            show pr.1 ≠ rs.length + a
            omega
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
            have hcA : c < A + 1 := List.mem_range.mp hc
            show rs.length + c ≠ rs.length + a
            omega
  | node h p g =>
    have hlegal : LegalResp q (q.substAns (RAns.node h p)) :=
      legalResp_of_at'_node (ds i).2 hate'
    have hle : Tree.Le (q.substAns (RAns.node h p)).toTree (ds i).1 :=
      Resp.toTree_le_of_at'_node q (ds i).1 h p g hate'
    have hAns : (q.substAns (RAns.node h p)).ansOf = RAns.node h p :=
      Query.ansOf_substAns q (RAns.node h p)
    by_cases hin : q.substAns (RAns.node h p) ∈ rs
    · -- the numbered response the argument realises
      obtain ⟨n, hn, hnlt⟩ := mem_enumFrom' 0 rs _ hin
      rw [Nat.zero_add] at hn
      have hprobe : ∀ ws : Nat → Val,
          (argVal q rs h ws).at' p = some (probeVal ((σ.arg i).arg h) (ws n)) :=
        fun ws => at'_argVal_probe q rs hrs_legal hrs_nd h ws n _ p hn hAns
      have hrun : ∀ ws : Nat → Val, applyArgs (σ.arg i) (ds i).1
          (fun h' => argVal q rs h' ws)
          = (match ws n with
              | .err b => Tree.leaf (Val.err b)
              | _ => Tree.bot) := by
        intro ws
        rw [inner_value i q γ hγ hq rs hrs_legal hrs_nd (ds i).1 _ hate' ws,
          applyArgs_node (σ.arg i) h p g (fun h' => argVal q rs h' ws),
          hprobe ws]
        cases hws : ws n with
        | bot => rfl
        | err b => rfl
        | num u => rfl
      have hcatchn := catchVal_node i q rs Es hEs_cl hEs_ty hgok hEs_mean Env
        (ds i) (hEnvx i) Γ (hΓ i) n hnlt
        (by rw [hrun wsBot]; rfl)
        (by rw [hrun (wsErrAt n),
          show wsErrAt n n = Val.err true from by rw [wsErrAt, if_pos rfl]])
      have hmem : ((n, Term.apps (Fs (q.substAns (RAns.node h p))) (xargs σ))
          : Nat × Term SPCF) ∈ caseArms σ i q rs A Fs := by
        rw [caseArms]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨(n, _), hn, rfl⟩)
      rw [hcatchn, cascade_num_hit _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ) n _
        hvarty harmsty hsorted (by rw [hscrut]; rfl) hmem]
      exact harm _ _ hlegal hle
    · -- the response is not in the list, so the branch is `⊥`
      have hfbot : f (q.substAns (RAns.node h p)) = Tree.bot :=
        Classical.byContradiction fun hc => hin (hrs_cover h p hc)
      have hnotpos : ∀ np ∈ psForArg rs h, np.2 ≠ p := by
        intro np hnp hcon
        obtain ⟨r, hmem, hpos⟩ := (mem_psForArg rs h np).mp hnp
        have hrmem : r ∈ rs := enumFrom'_mem_snd 0 rs (np.1, r) hmem
        have hr : r.ansOf = RAns.node h np.2 := ansOf_of_posOf h r np.2 hpos
        rw [hcon] at hr
        rw [(legalResp_ansOf (hrs_legal r hrmem)).1, hr] at hrmem
        exact hin hrmem
      have hconst : ∀ ws : Nat → Val, applyArgs (σ.arg i) (ds i).1
          (fun h' => argVal q rs h' ws) = Tree.leaf Val.bot := by
        intro ws
        rw [inner_value i q γ hγ hq rs hrs_legal hrs_nd (ds i).1 _ hate' ws,
          applyArgs_node (σ.arg i) h p g (fun h' => argVal q rs h' ws),
          at'_argVal_bot q rs hrs_legal hrs_nd h ws p
            ((TreeOk_node_inv (TreeOk_at' q Ctx.empty (ds i).1 _ (ds i).2 hate')).1).1
            hnotpos]
        rfl
      rw [hcatchOf Val.bot hconst,
        applyT_catch_leafT (Ty.pads rs.length 𝕆) Val.bot]
      show Tmodel.meaning _ _ 𝕆 = _
      rw [cascade_bot _ _ _ ((σ.arity + rs.length, 𝕆) :: Γ) hvarty harmsty
        (by rw [hscrut])]
      show leafT 𝕆 Val.bot = Ideal.principal (groundD
        (applyArgs σ (f (q.substAns (RAns.node h p))) (fun j => (ds j).1)))
      rw [hfbot, show (Tree.bot : Tree σ) = Tree.leaf Val.bot from rfl,
        applyArgs_leaf σ Val.bot (fun j => (ds j).1)]
      rfl

end FA
