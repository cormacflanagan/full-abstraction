/-
# The Full Abstraction Theorem (§5)

Formalises **Definition 5.3** (subtree representability), **Lemma 5.2**
(definability of the finite elements) and **Theorem 5.1** (full abstraction of
`T` and SPCF).

Theorem 5.1 is *derived* here from exactly the ingredients the paper's proof
appeals to:

* `soundness` — "The other direction is an immediate consequence of the
  compositionality of the meaning function `T`";
* `separation` — "Since `T[[M]]_E ≠ T[[N]]_E`, the domains `T_σᵢ` are algebraic,
  `apply` is continuous, and SPCF is extensional, it is easy to prove by
  contradiction that there exist finite trees `d₁ ⊑ t₁, …, dₖ ⊑ tₖ` such that
  `apply (T[[M]]_E, d₁, …, dₖ) ≠ apply (T[[N]]_E, d₁, …, dₖ)`";
* `meaning_apps` — the meaning of `(M E₁ … Eₖ)` is `apply (T[[M]], e₁, …, eₖ)`;
* `lemma_5_2` — "Thus, the proof that SPCF is fully abstract reduces to the
  proof of the following lemma."
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

/-! ## Applicative contexts -/

/-- An SPCF term, viewed as a context with no holes. -/
def MCtx.ofTerm {L : Lang} {k : Nat} : Term L → MCtx L k
  | .var x σ => .var x σ
  | .const c => .const c
  | .app M N => .app (MCtx.ofTerm M) (MCtx.ofTerm N)
  | .lam x σ M => .lam x σ (MCtx.ofTerm M)

theorem MCtx.fill_ofTerm {L : Lang} {k : Nat} (M : Term L) (Ms : Fin k → Term L) :
    (MCtx.ofTerm M : MCtx L k).fill Ms = M := by
  induction M with
  | var x σ => rfl
  | const c => rfl
  | app M N ihM ihN => simp [MCtx.ofTerm, MCtx.fill, ihM, ihN]
  | lam x σ M ih => simp [MCtx.ofTerm, MCtx.fill, ih]

/-- The applicative context `C[·] = ([·] E₁ … Eₖ)` of the proof of
Theorem 5.1. -/
def appCtx (Es : List (Term SPCF)) : MCtx SPCF 1 :=
  Es.foldl (fun C E => .app C (MCtx.ofTerm E)) (.hole 0)

theorem appCtx_fill (Es : List (Term SPCF)) (M : Term SPCF) :
    (appCtx Es).fill (fun _ => M) = Term.apps M Es := by
  have h : ∀ (Es : List (Term SPCF)) (C : MCtx SPCF 1) (N : Term SPCF),
      C.fill (fun _ => M) = N →
      (Es.foldl (fun C E => MCtx.app C (MCtx.ofTerm E)) C).fill (fun _ => M)
        = Es.foldl Term.app N := by
    intro Es
    induction Es with
    | nil => intro C N h; exact h
    | cons E Es ih =>
      intro C N h
      exact ih _ _ (by simp [MCtx.fill, h, MCtx.fill_ofTerm])
  exact h Es (.hole 0) M rfl

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

/-- The node case of the induction of Lemma 5.2: the `catch`-based
construction of §5. -/
theorem representable_node (n : Nat)
    (ihOut : ∀ σ' : Ty, σ'.depth ≤ n → ∀ (γ' : Ctx σ') (e' : Tree σ'),
      TreeOk γ' e' → Representable σ' γ' e')
    (σ : Ty) (hσ : σ.depth ≤ n + 1) (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ)
    (ihIn : ∀ (r : Resp (σ.arg i)) (γ' : Ctx σ), TreeOk γ' (f r) →
      Representable σ γ' (f r))
    (γ : Ctx σ) (hok : TreeOk γ (.node i q f)) :
    Representable σ γ (.node i q f) := by
  sorry

/-- The depth of a type is positive. -/
theorem Ty.depth_pos : ∀ σ : Ty, 0 < σ.depth
  | .base => Nat.one_pos
  | .arrow a b => by
      show 0 < max (1 + a.depth) b.depth
      have := Ty.depth_pos b
      omega

/-- The nested induction of §5, staged on the depth of the type. -/
theorem repSubtrees : ∀ (n : Nat) (σ : Ty), σ.depth ≤ n →
    ∀ (e : Tree σ) (γ : Ctx σ), TreeOk γ e → Representable σ γ e := by
  intro n
  induction n with
  | zero =>
    intro σ hσ
    exact absurd (Nat.lt_of_lt_of_le (Ty.depth_pos σ) hσ) (by omega)
  | succ n ihn =>
    intro σ hσ e
    induction e with
    | leaf v =>
      intro γ _
      exact representable_leaf σ γ v
    | node i q f ihf =>
      intro γ hok
      exact representable_node n (fun σ' h γ' e' he' => ihn σ' h e' γ' he')
        σ hσ i q f (fun r γ' h' => ihf r γ' h') γ hok

/-- The stronger statement actually proved by the nested induction of §5:
every finite subtree is representable in every legal context. -/
theorem lemma_5_2_subtrees (σ : Ty) (γ : Ctx σ) (e : Tree σ) (he : TreeOk γ e) :
    Representable σ γ e :=
  repSubtrees σ.depth σ (Nat.le_refl _) e γ he

/-! ## The ingredients of Theorem 5.1 -/

/-- Filling a context with either of two closed phrases of the same type gives
terms of the same type. -/
theorem MCtx.fill_hasTy_congr (M N : Term SPCF) (σ : Ty)
    (hM : Term.HasTy [] M σ) (hN : Term.HasTy [] N σ) :
    ∀ (C : MCtx SPCF 1) (Γ : List (Nat × Ty)) (ρ : Ty),
      Term.HasTy Γ (C.fill fun _ => M) ρ → Term.HasTy Γ (C.fill fun _ => N) ρ := by
  intro C
  induction C with
  | hole i =>
    intro Γ ρ h
    have : ρ = σ := Term.hasTy_unique h hM
    subst this
    exact Term.weaken (fun _ hp => absurd hp (by simp)) hN
  | var x ν => intro Γ ρ h; exact h
  | const c => intro Γ ρ h; exact h
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ h
    cases h with | app h₁ h₂ => exact Term.HasTy.app (ih₁ _ _ h₁) (ih₂ _ _ h₂)
  | lam x ν C ih =>
    intro Γ ρ h
    cases h with | lam hC => exact Term.HasTy.lam (ih _ _ hC)

/-- Compositionality of `T`: denotationally equal phrases have equal meanings in
every context.  "The other direction is an immediate consequence of the
compositionality of the meaning function `T`" (proof of Theorem 5.1).

The `λ` case is where Corollary 4.23's abstraction lemma does the work. -/
theorem soundness_aux (M N : Term SPCF) (σ : Ty)
    (hM : Term.HasTy [] M σ) (hN : Term.HasTy [] N σ)
    (hden : ∀ E : Tmodel.Env, Tmodel.combMeaning E (Term.toComb M) σ
      = Tmodel.combMeaning E (Term.toComb N) σ) :
    ∀ (C : MCtx SPCF 1) (Γ : List (Nat × Ty)) (ρ : Ty) (E : Tmodel.Env),
      Term.HasTy Γ (C.fill fun _ => M) ρ →
      Tmodel.combMeaning E (Term.toComb (C.fill fun _ => M)) ρ
        = Tmodel.combMeaning E (Term.toComb (C.fill fun _ => N)) ρ := by
  intro C
  induction C with
  | hole i =>
    intro Γ ρ E h
    have : ρ = σ := Term.hasTy_unique h hM
    subst this
    exact hden E
  | var x ν => intro Γ ρ E _; rfl
  | const c => intro Γ ρ E _; rfl
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ E h
    cases h with
    | app h₁ h₂ =>
      rename_i α
      have e₂ : Comb.tyOf (Term.toComb (C₂.fill fun _ => M)) = α := Term.tyOf_toComb h₂
      have e₂' : Comb.tyOf (Term.toComb (C₂.fill fun _ => N)) = α :=
        Term.tyOf_toComb (MCtx.fill_hasTy_congr M N σ hM hN C₂ Γ α h₂)
      show Tmodel.combMeaning E (.app (Term.toComb (C₁.fill fun _ => M))
          (Term.toComb (C₂.fill fun _ => M))) ρ = _
      rw [Model.combMeaning_app, e₂, ih₁ Γ (α ⇒ ρ) E h₁, ih₂ Γ α E h₂]
      show _ = Tmodel.combMeaning E (.app (Term.toComb (C₁.fill fun _ => N))
        (Term.toComb (C₂.fill fun _ => N))) ρ
      rw [Model.combMeaning_app, e₂']
  | lam x ν C ih =>
    intro Γ ρ E h
    cases h with
    | lam hC =>
      rename_i τ
      have hCM : Comb.HasTy ((x, ν) :: Γ) (Term.toComb (C.fill fun _ => M)) τ :=
        Term.toComb_hasTy hC
      have hCN : Comb.HasTy ((x, ν) :: Γ) (Term.toComb (C.fill fun _ => N)) τ :=
        Term.toComb_hasTy (MCtx.fill_hasTy_congr M N σ hM hN C ((x, ν) :: Γ) τ hC)
      show Tmodel.combMeaning E (Comb.lamStar x ν (Term.toComb (C.fill fun _ => M))) (ν ⇒ τ)
        = Tmodel.combMeaning E (Comb.lamStar x ν (Term.toComb (C.fill fun _ => N))) (ν ⇒ τ)
      refine theorem_4_11.2 ν τ _ _ fun z => ?_
      rw [lamStar_apply E x ν z _ τ Γ hCM, lamStar_apply E x ν z _ τ Γ hCN]
      exact ih ((x, ν) :: Γ) τ (Model.envUpdate E x ν z) hC

/-- Compositionality of `T`: denotationally equal phrases are observationally
equivalent. -/
theorem soundness (σ : Ty) (M N : Term SPCF)
    (hM : Term.HasTy [] M σ) (hN : Term.HasTy [] N σ)
    (h : Tmodel.DenEquiv σ M N) : SemDef.ObsEquiv SPCFSem M N := by
  intro C hprogM _
  exact soundness_aux M N σ hM hN (fun E => h E) C [] 𝕆 botEnv hprogM.2

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

/-- The separation step of Theorem 5.1.

"Since `T[[M]]_E ≠ T[[N]]_E`, the domains `T_σᵢ` are algebraic, `apply` is
continuous, and SPCF is extensional, it is easy to prove by contradiction that
there exist finite trees `d₁ ⊑ t₁, …, dₖ ⊑ tₖ` such that
`apply (T[[M]]_E, d₁, …, dₖ) ≠ apply (T[[N]]_E, d₁, …, dₖ)`." -/
theorem separation (σ : Ty) (F G : T σ) (h : F ≠ G) :
    ∃ ds : (i : Fin σ.arity) → D (σ.arg i),
      applyIdeals σ F (fun i => Ideal.principal (ds i))
        ≠ applyIdeals σ G (fun i => Ideal.principal (ds i)) :=
  Classical.byContradiction fun hcon =>
    h (eq_of_principal_applyIdeals σ F G fun ds =>
      Classical.byContradiction fun hne => hcon ⟨ds, hne⟩)

/-- **Lemma 5.2.**  *For every finite element `d ∈ D_σ`, there is a closed SPCF
expression `M` such that `T[[M]] = d`.*

"The proof of the lemma proceeds by induction on the depth of the type
`σ = σ₁ → … → σₖ → o`. … we must prove that for all contexts `γ ∈ C_σ`, every
finite subtree `e` in `D_σ(γ)` is representable in SPCF."  The passage from
subtree representability at the empty context back to `T[[M]] = d` is the
"reduces to tree representability by extensionality" remark of
Definition 5.3. -/
theorem lemma_5_2 (σ : Ty) (d : D σ) :
    ∃ M : Term SPCF, Term.Closed M ∧ Term.HasTy [] M σ ∧
      Tmodel.meaning botEnv M σ = Ideal.principal d := by
  obtain ⟨M, hcl, hty, happ⟩ := lemma_5_2_subtrees σ Ctx.empty d.1 d.2
  refine ⟨M, hcl, hty, ?_⟩
  refine eq_of_principal_applyIdeals σ _ _ fun ds => ?_
  rw [happ ds (fun i => Tree.Le.bot _), applyIdeals_principal σ d ds]

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

/-! ## Theorem 5.1 -/

/-- **Theorem 5.1** (*Full Abstraction of `T` and SPCF*), contrapositive form.

*If `M` and `N` are closed phrases of type `σ` with `T[[M]] ≠ T[[N]]`, then
`M ≄ N`.*

This is the substance of the theorem, and it is proved here from `separation`,
`lemma_5_2` and `meaning_apps`, by exhibiting the paper's distinguishing context
`C[·] = ([·] E₁ … Eₖ)`. -/
theorem theorem_5_1_separating (σ : Ty) (M N : Term SPCF)
    (hne : Tmodel.meaning botEnv M σ ≠ Tmodel.meaning botEnv N σ)
    (hprog : ∀ (Es : List (Term SPCF)) (P : Term SPCF),
      SPCFSem.Program ((appCtx Es).fill fun _ => P)) :
    ¬ SemDef.ObsEquiv SPCFSem M N := by
  intro hobs
  -- separation: finite arguments distinguishing the two denotations
  obtain ⟨ds, hds⟩ := separation σ _ _ hne
  -- Lemma 5.2: name each `dᵢ` by a closed SPCF expression `Eᵢ`
  have hrep : ∀ i : Fin σ.arity, ∃ E : Term SPCF,
      Term.Closed E ∧ Term.HasTy [] E (σ.arg i) ∧
      Tmodel.meaning botEnv E (σ.arg i) = Ideal.principal (ds i) :=
    fun i => lemma_5_2 (σ.arg i) (ds i)
  let E : (i : Fin σ.arity) → Term SPCF := fun i => Classical.choose (hrep i)
  have hE : ∀ i, Tmodel.meaning botEnv (E i) (σ.arg i) = Ideal.principal (ds i) :=
    fun i => (Classical.choose_spec (hrep i)).2.2
  -- the distinguishing context `C[·] = ([·] E₁ … Eₖ)`
  let Es : List (Term SPCF) := List.ofFn E
  have hM := hobs (appCtx Es) (hprog Es M) (hprog Es N)
  rw [appCtx_fill, appCtx_fill] at hM
  have hEty : ∀ i, Term.HasTy [] (E i) (σ.arg i) :=
    fun i => (Classical.choose_spec (hrep i)).2.1
  have hMval : SPCFSem.meaning (Term.apps M Es)
      = applyIdeals σ (Tmodel.meaning botEnv M σ) (fun i => Ideal.principal (ds i)) :=
    meaning_apps σ M E _ hEty hE
  have hNval : SPCFSem.meaning (Term.apps N Es)
      = applyIdeals σ (Tmodel.meaning botEnv N σ) (fun i => Ideal.principal (ds i)) :=
    meaning_apps σ N E _ hEty hE
  exact hds (hMval ▸ hNval ▸ hM)

/-- **Theorem 5.1** (*Full Abstraction of `T` and SPCF*).

*For all SPCF phrases `M` and `N`, `M ≈_T N` iff `M ≃ N`.* -/
theorem theorem_5_1 (σ : Ty) (M N : Term SPCF)
    (henv : ∀ P : Term SPCF, Term.Closed P →
      ∀ Env : Tmodel.Env, Tmodel.meaning Env P σ = Tmodel.meaning botEnv P σ)
    (hMty : Term.HasTy [] M σ) (hNty : Term.HasTy [] N σ)
    (hM : Term.Closed M) (hN : Term.Closed N)
    (hprog : ∀ (Es : List (Term SPCF)) (P : Term SPCF),
      SPCFSem.Program ((appCtx Es).fill fun _ => P)) :
    Tmodel.DenEquiv σ M N ↔ SemDef.ObsEquiv SPCFSem M N := by
  refine ⟨soundness σ M N hMty hNty, fun hobs => ?_⟩
  intro Env
  rw [henv M hM Env, henv N hN Env]
  exact Classical.byContradiction fun hne => theorem_5_1_separating σ M N hne hprog hobs

/-- **Theorem 5.1**, in the form of Definition 2.8: the tree model `T` is fully
abstract for SPCF. -/
theorem theorem_5_1_fullyAbstract
    (henv : ∀ (σ : Ty) (P : Term SPCF), Term.Closed P →
      ∀ Env : Tmodel.Env, Tmodel.meaning Env P σ = Tmodel.meaning botEnv P σ)
    (hprog : ∀ (Es : List (Term SPCF)) (P : Term SPCF),
      SPCFSem.Program ((appCtx Es).fill fun _ => P))
    (hty : ∀ (σ : Ty) (P : Term SPCF), Term.Closed P → Term.HasTy [] P σ) :
    Tmodel.FullyAbstract SPCFSem := by
  intro σ N N' hN hN' hobs
  exact (theorem_5_1 σ N N' (henv σ) (hty σ N hN) (hty σ N' hN') hN hN' hprog).mpr hobs

end FA
