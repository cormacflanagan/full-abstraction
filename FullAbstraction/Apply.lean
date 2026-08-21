/-
# Application and extensionality (§4.2)

Formalises **Definition 4.9** (`apply`), **Definition 4.17** (`F_{σ→τ}` and
`fun`), and states **Lemma 4.7**, **Claim 4.8**, **Theorem 4.11**,
**Lemma 4.14**, **Corollary 4.15**, **Lemma 4.16** and **Corollary 4.18**.
-/
import FullAbstraction.Trees

namespace FA

open Po

namespace RAns
variable {σ : Ty}

/-- An answer, viewed as the one-node tree it describes. -/
noncomputable def toTree : RAns σ → Tree σ
  | .num n => .leaf (.num n)
  | .node i p => .node i p fun _ => Tree.bot

end RAns

namespace Resp
variable {σ : Ty}

/-- The query part of a response: the path with its final answer removed. -/
def qry : Resp σ → Query σ
  | .ans _ => .hole
  | .node _ _ => .hole
  | .step i q r rest => .step i q r rest.qry

/-- The answer part of a response. -/
def ansOf : Resp σ → RAns σ
  | .ans n => .num n
  | .node i p => .node i p
  | .step _ _ _ rest => rest.ansOf

/-- `r = r.qry[?/r.ansOf]`: a response is its query with its answer plugged in
(Definition 4.2, *Legal Responses*). -/
theorem substAns_qry_ansOf : ∀ r : Resp σ, r.qry.substAns r.ansOf = r
  | .ans _ => rfl
  | .node _ _ => rfl
  | .step i q r rest => by
      show Resp.step i q r (rest.qry.substAns rest.ansOf) = _
      rw [substAns_qry_ansOf rest]

end Resp

namespace Query
variable {σ : Ty}

@[simp] theorem qry_substAns : ∀ (q : Query σ) (x : RAns σ), (q.substAns x).qry = q
  | .hole, .num _ => rfl
  | .hole, .node _ _ => rfl
  | .step i p r rest, x => by
      show Query.step i p r ((rest.substAns x).qry) = _
      rw [qry_substAns rest x]

@[simp] theorem ansOf_substAns : ∀ (q : Query σ) (x : RAns σ), (q.substAns x).ansOf = x
  | .hole, .num _ => rfl
  | .hole, .node _ _ => rfl
  | .step _ _ _ rest, x => ansOf_substAns rest x

/-- `q.answerOf r` returns the answer `x` with `r = q[?/x]`, if `r` is a
response to `q` at all.  This inverts the substitution `q[?/x]` of
Definition 4.2 and is what lets the branching functions of Definitions 4.19–4.21
be given by case analysis on the response received. -/
noncomputable def answerOf : Query σ → Resp σ → Option (RAns σ)
  | .hole, .ans n => some (.num n)
  | .hole, .node i p => some (.node i p)
  | .hole, .step _ _ _ _ => none
  | .step i q r rest, .step j q' r' rest' =>
      if (⟨i, q, r⟩ : PStep σ) = ⟨j, q', r'⟩ then rest.answerOf rest' else none
  | .step _ _ _ _, .ans _ => none
  | .step _ _ _ _, .node _ _ => none

/-- `q.snoc j p r'`: the query `q` extended by one further step. -/
def snoc : Query σ → (j : Fin σ.arity) → Query (σ.arg j) → Resp (σ.arg j) → Query σ
  | .hole, j, p, r' => .step j p r' .hole
  | .step i a b rest, j, p, r' => .step i a b (rest.snoc j p r')

/-- A query is **coherent** when each of its steps records a response to the
query that step asks.  Every legal query is coherent — this is exactly what
Definition 4.2's requirement `r ∈ ℛ_σᵢ(q)` says — so assuming coherence is no
more than assuming `q ∈ Q_σ` in the paper's sense. -/
def Coherent : Query σ → Prop
  | .hole => True
  | .step _ q r rest => r.qry = q ∧ rest.Coherent

end Query

/-- `answerOf` inverts `substAns`. -/
@[simp] theorem Query.answerOf_substAns {σ : Ty} : ∀ (q : Query σ) (x : RAns σ),
    q.answerOf (q.substAns x) = some x
  | .hole, .num _ => rfl
  | .hole, .node _ _ => rfl
  | .step i p r rest, x => by
      show (if (⟨i, p, r⟩ : PStep σ) = ⟨i, p, r⟩ then rest.answerOf (rest.substAns x)
        else none) = some x
      rw [if_pos rfl, Query.answerOf_substAns rest x]

/-- Extending the response `q[?/⟨j,p⟩]` by a response `r'` to `p` gives `q`
followed by the step `⟨j, p, r'⟩` (Definition 4.2, `r : f`). -/
theorem extendHole_substAns_node {σ : Ty} : ∀ (q : Query σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)),
    (q.substAns (.node j p)).extendHole ⟨j, r'⟩ = q.snoc j p r'
  | .hole, j, p, r' => by
      show (if h : j = j then Query.step j p (h ▸ r') Query.hole else Query.hole)
        = Query.step j p r' Query.hole
      rw [dif_pos rfl]
  | .step i a b rest, j, p, r' => by
      show Query.step i a b ((rest.substAns (.node j p)).extendHole ⟨j, r'⟩) = _
      rw [extendHole_substAns_node rest j p r']
      rfl

/-- `@` along an extended query descends one further step. -/
theorem at'_snoc {σ : Ty} : ∀ (q : Query σ) (d : Tree σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)),
    d.at' (q.snoc j p r') = (d.at' q).bind fun t => t.stepAt j p r'
  | .hole, d, j, p, r' => by
      show (d.stepAt j p r').bind (fun t => t.at' .hole) = d.stepAt j p r'
      cases d.stepAt j p r' <;> rfl
  | .step i a b rest, d, j, p, r' => by
      show (d.stepAt i a b).bind (fun t => t.at' (rest.snoc j p r'))
        = ((d.stepAt i a b).bind fun t => t.at' rest).bind fun t => t.stepAt j p r'
      cases d.stepAt i a b with
      | none => rfl
      | some t =>
        show t.at' (rest.snoc j p r') = (t.at' rest).bind fun u => u.stepAt j p r'
        exact at'_snoc rest t j p r'

/-- Every legal query is coherent: each step records a response to the query
that step asks. -/
theorem QueryOk.coherent {σ : Ty} : ∀ {q : Query σ}, QueryOk σ q → q.Coherent
  | .hole, _ => trivial
  | .step i p s rest, h => by
      obtain ⟨hs, hrest⟩ := (QueryOk_step i p s rest).mp h
      obtain ⟨x, rfl, _⟩ := hs
      exact ⟨Query.qry_substAns p x, QueryOk.coherent hrest⟩

/-- Legal responses are responses to the query they answer. -/
theorem qry_of_legalResp {σ : Ty} {q : Query σ} {r : Resp σ} (h : LegalResp q r) :
    r.qry = q := by
  obtain ⟨x, rfl, _⟩ := h
  exact Query.qry_substAns q x

/-! ## Definition 4.9: `apply` -/

/-- **Definition 4.9** (*`apply`*), the auxiliary partial function `apply₀`.

```
apply₀ (f, d)          = f                              if f ∈ ℕ^E_⊥
apply₀ (⟨1,q,g⟩, d)    = d @ q                          if d @ q ∈ E
                       = apply₀ (g (q[?/d@q]), d)       if d @ q ∈ ℕ
                       = apply₀ (g (q[?/⟨j,p⟩]), d)     if d @ q = ⟨j,p,d'⟩
apply₀ (⟨i+1,q,g⟩, d)  = ⟨i, q, λ rᵢ . apply₀ (g (rᵢ), d)⟩
```

The paper's partiality (`apply₀` is only constrained when `⊔γ(1) ⊑ d`) is
rendered by returning `⊥` where the paper leaves the value irrelevant:
"the behaviour of `apply₀` on finite trees `d ∈ D_σ` where `⊔γ(1) ⋢ d` is
irrelevant". -/
noncomputable def apply0 {σ τ : Ty} : Tree (σ ⇒ τ) → Tree σ → Tree τ
  | .leaf v, _ => .leaf v
  | .node ⟨0, _⟩ q g, d =>
      match d.at' q with
      | none => Tree.bot
      | some (.leaf .bot) => Tree.bot
      | some (.leaf (.err b)) => .leaf (.err b)
      | some (.leaf (.num n)) => apply0 (g (q.substAns (.num n))) d
      | some (.node j p _) => apply0 (g (q.substAns (.node j p))) d
  | .node ⟨i + 1, h⟩ q g, d =>
      .node ⟨i, Nat.lt_of_succ_lt_succ h⟩ q (fun r => apply0 (g r) d)

/-- Iterated application `apply (f, d₁, …, dₖ)` on finite trees, indexed by the
argument types of `σ` itself (§4.2 and Corollary 4.15). -/
noncomputable def applyArgs : ∀ σ : Ty, Tree σ → ((i : Fin σ.arity) → Tree (σ.arg i)) → Tree 𝕆
  | .base, t, _ => t
  | .arrow _ b, t, ds =>
      applyArgs b (apply0 t (ds ⟨0, Nat.succ_pos _⟩))
        (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-! ### Well-definedness obligations of Definition 4.9

"It is easy to show that `apply₀` produces a well-defined output in `D_τ(γ')`
… In addition, it is straightforward to check that … the set
`{apply₀ (f', d') | f' ⊑ f, d' ⊑ d}` is directed, implying that it has a least
upper bound.  Hence, `apply` is a well-defined, continuous function from pairs
of trees to trees." -/

/-- `γ'` is the **shift** of `γ` (Definition 4.9: `γ'(i) = γ(i+1)`): it knows
about argument `i` exactly what `γ` knows about argument `i + 1`. -/
def Ctx.IsShift {a τ : Ty} (γ : Ctx (a ⇒ τ)) (γ' : Ctx τ) : Prop :=
  ∀ (i : Fin τ.arity) (h : i.val + 1 < (a ⇒ τ).arity), γ' i = γ ⟨i.val + 1, h⟩

/-- The empty context is its own shift. -/
theorem Ctx.isShift_empty {a τ : Ty} :
    Ctx.IsShift (Ctx.empty : Ctx (a ⇒ τ)) (Ctx.empty : Ctx τ) := fun _ _ => rfl

/-- Extending both contexts at corresponding indices preserves the shift
relation. -/
theorem Ctx.isShift_cons {a τ : Ty} {γ : Ctx (a ⇒ τ)} {γ' : Ctx τ}
    (hs : Ctx.IsShift γ γ') (k : Fin τ.arity) (hk : k.val + 1 < (a ⇒ τ).arity)
    (s : Resp (τ.arg k)) :
    Ctx.IsShift (γ.cons ⟨k.val + 1, hk⟩ s) (γ'.cons k s) := by
  intro i h
  by_cases hik : k = i
  · subst hik
    rw [Ctx.cons_self, Ctx.cons_self, hs k h]
  · rw [Ctx.cons_other _ _ hik, Ctx.cons_other _ _ (fun he => hik (Fin.ext
      (Nat.succ_inj.mp (congrArg Fin.val he)))), hs i h]

/-- Recording a response about the *first* argument does not change the shift. -/
theorem Ctx.isShift_cons_zero {a τ : Ty} {γ : Ctx (a ⇒ τ)} {γ' : Ctx τ}
    (hs : Ctx.IsShift γ γ') (h0 : 0 < (a ⇒ τ).arity) (s : Resp ((a ⇒ τ).arg ⟨0, h0⟩)) :
    Ctx.IsShift (γ.cons ⟨0, h0⟩ s) γ' := by
  intro i h
  rw [Ctx.cons_other _ _ (fun he : (⟨0, h0⟩ : Fin (a ⇒ τ).arity) = ⟨i.val + 1, h⟩ =>
    Nat.succ_ne_zero i.val (congrArg Fin.val he).symm)]
  exact hs i h

/-- **Definition 4.9**: `apply₀` maps `D_{σ→τ}(γ) × D_σ` into `D_τ(γ')`.

"It is easy to show that `apply₀` produces a well-defined output in `D_τ(γ')`."
Where the paper's side condition `⊔γ(1) ⊑ d` fails, `apply₀` returns `⊥`, which
is legal in every context, so no hypothesis on `d` is needed. -/
theorem apply0_ok {σ τ : Ty} : ∀ (f : Tree (σ ⇒ τ)) (γ : Ctx (σ ⇒ τ)) (γ' : Ctx τ)
    (d : Tree σ), TreeOk γ f → Ctx.IsShift γ γ' → TreeOk γ' (apply0 f d) := by
  intro f
  induction f with
  | leaf v => intro γ γ' d _ _; exact TreeOk.leaf γ' v
  | node i q g ih =>
    intro γ γ' d hf hs
    obtain ⟨hq, hfin, hsub, hnon⟩ := TreeOk_node_inv hf
    match i with
    | ⟨0, h0⟩ =>
      rw [apply0]
      -- the recursive call is on a branch of `g`; illegal branches are `⊥`
      have hbranch : ∀ x : RAns σ, TreeOk γ' (apply0 (g (q.substAns x)) d) := by
        intro x
        by_cases hlegal : LegalResp q (q.substAns x)
        · exact ih _ (γ.cons ⟨0, h0⟩ (q.substAns x)) γ' d (hsub _ hlegal)
            (Ctx.isShift_cons_zero hs h0 _)
        · rw [hnon _ hlegal]; exact TreeOk.leaf γ' _
      cases hd : d.at' q with
      | none => exact TreeOk.leaf γ' _
      | some e =>
        cases e with
        | leaf v => cases v <;> first | exact TreeOk.leaf γ' _ | exact hbranch _
        | node j p _ => exact hbranch (.node j p)
    | ⟨k + 1, hk⟩ =>
      rw [apply0]
      refine TreeOk.node γ' ⟨k, Nat.lt_of_succ_lt_succ hk⟩ q _ ?_ ?_ ?_ ?_
      · rw [hs ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hk]; exact hq
      · obtain ⟨l, hl⟩ := hfin
        refine ⟨l, fun r hr => hl r ?_⟩
        intro hgr
        have hb : apply0 (g r) d = Tree.bot := by rw [hgr]; rfl
        exact hr hb
      · intro r hr
        exact ih r (γ.cons ⟨k + 1, hk⟩ r) (γ'.cons ⟨k, Nat.lt_of_succ_lt_succ hk⟩ r) d
          (hsub r hr) (Ctx.isShift_cons hs ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hk r)
      · intro r hr
        have hb : apply0 (g r) d = Tree.bot := by rw [hnon r hr]; rfl
        exact hb

/-- `apply₀` is monotone in its first argument.

The proof is by induction on the derivation of `f ⊑ f'`: comparable trees have
the same root, so `apply₀` takes the same branch on both sides and the induction
hypothesis applies. -/
theorem apply0_mono_left {σ τ : Ty} {f f' : Tree (σ ⇒ τ)} (h : Tree.Le f f') (d : Tree σ) :
    apply0 f d ⊑ apply0 f' d := by
  induction h generalizing d with
  | bot e => exact Tree.Le.bot _
  | leaf v => exact Tree.Le.refl _
  | node i q g g' _ ih =>
    match i with
    | ⟨0, hi⟩ =>
      show Tree.Le (apply0 (.node ⟨0, hi⟩ q g) d) (apply0 (.node ⟨0, hi⟩ q g') d)
      rw [apply0, apply0]
      cases hd : d.at' q with
      | none => exact Tree.Le.refl _
      | some e =>
        cases e with
        | leaf v => cases v <;> simp only [] <;> first
            | exact Tree.Le.refl _
            | exact ih _ d
        | node j p _ => exact ih _ d
    | ⟨n + 1, hi⟩ =>
      show Tree.Le (apply0 (.node ⟨n + 1, hi⟩ q g) d) (apply0 (.node ⟨n + 1, hi⟩ q g') d)
      rw [apply0, apply0]
      exact Tree.Le.node _ _ _ _ fun r => ih r d

/-- Comparable trees answer a query compatibly: if `d ⊑ d'` and `d @ q` is
defined, then `d' @ q` is defined and `d @ q ⊑ d' @ q`. -/
theorem at'_mono {σ : Ty} : ∀ (q : Query σ) {d d' : Tree σ}, Tree.Le d d' →
    d.at' q = none ∨ ∃ e e', d.at' q = some e ∧ d'.at' q = some e' ∧ Tree.Le e e'
  | .hole, d, d', h => Or.inr ⟨d, d', rfl, rfl, h⟩
  | .step i p r rest, d, d', h => by
    cases h with
    | bot e => exact Or.inl rfl
    | leaf v => exact Or.inl rfl
    | node j p' g g' hg =>
      by_cases hEq : (⟨i, p⟩ : NodeVal σ) = ⟨j, p'⟩
      · have hstep : ∀ k : Resp (σ.arg j) → Tree σ,
            (Tree.node j p' k).stepAt i p r
              = some (k (Tree.castResp (congrArg Sigma.fst hEq) r)) := by
          intro k; simp only [Tree.stepAt, dif_pos hEq]
        simp only [Tree.at', hstep, Option.bind]
        exact at'_mono rest (hg (Tree.castResp (congrArg Sigma.fst hEq) r))
      · simp only [Tree.at', Tree.stepAt, dif_neg hEq, Option.bind]
        exact Or.inl trivial

/-- `apply₀` is monotone in its second argument. -/
theorem apply0_mono_right {σ τ : Ty} :
    ∀ (f : Tree (σ ⇒ τ)) {d d' : Tree σ}, Tree.Le d d' → apply0 f d ⊑ apply0 f d' := by
  intro f
  induction f with
  | leaf v => intro d d' _; exact Tree.Le.refl _
  | node i q g ih =>
    intro d d' h
    match i with
    | ⟨0, hi⟩ =>
      show Tree.Le (apply0 (.node ⟨0, hi⟩ q g) d) (apply0 (.node ⟨0, hi⟩ q g) d')
      rw [apply0, apply0]
      rcases at'_mono q h with hnone | ⟨e, e', he, he', hee⟩
      · rw [hnone]; exact Tree.Le.bot _
      · cases hee with
        | bot t => rw [he]; exact Tree.Le.bot _
        | leaf v =>
          rw [he, he']
          cases v
          · exact Tree.Le.bot _
          · exact Tree.Le.refl _
          · exact ih _ h
        | node j p k k' _ => rw [he, he']; exact ih _ h
    | ⟨n + 1, hi⟩ =>
      show Tree.Le (apply0 (.node ⟨n + 1, hi⟩ q g) d) (apply0 (.node ⟨n + 1, hi⟩ q g) d')
      rw [apply0, apply0]
      exact Tree.Le.node _ _ _ _ fun r => ih r h

/-- `apply₀` restricted to the finitary bases. -/
noncomputable def applyD {σ τ : Ty} (f : D (σ ⇒ τ)) (d : D σ) : D τ :=
  ⟨apply0 f.1 d.1, apply0_ok f.1 Ctx.empty Ctx.empty d.1 f.2 Ctx.isShift_empty⟩

/-- **Definition 4.9**, the continuous extension:

`apply (f, d) = ⊔ {apply₀ (f', d') | f' ⊑ f, f' ∈ D_{σ→τ}, d' ⊑ d, d' ∈ D_σ}`.

Because `apply₀` is monotone in both arguments (`apply0_mono_left`,
`apply0_mono_right`), the displayed set is directed and its downward closure is
an ideal, i.e. an element of `T_τ`. -/
noncomputable def applyT {σ τ : Ty} (F : T (σ ⇒ τ)) (G : T σ) : T τ where
  carrier := fun c => ∃ f, f ∈ F ∧ ∃ d, d ∈ G ∧ c ⊑ applyD f d
  nonempty' := by
    obtain ⟨f, hf⟩ := F.nonempty'
    obtain ⟨d, hd⟩ := G.nonempty'
    exact ⟨applyD f d, f, hf, d, hd, Po.le_refl _⟩
  downward a b hab := by
    rintro ⟨f, hf, d, hd, hb⟩; exact ⟨f, hf, d, hd, Po.le_trans hab hb⟩
  directed' a b := by
    rintro ⟨f₁, hf₁, d₁, hd₁, ha⟩ ⟨f₂, hf₂, d₂, hd₂, hb⟩
    obtain ⟨f, hf, hf1, hf2⟩ := F.directed' f₁ f₂ hf₁ hf₂
    obtain ⟨d, hd, hd1, hd2⟩ := G.directed' d₁ d₂ hd₁ hd₂
    refine ⟨applyD f d, ⟨f, hf, d, hd, Po.le_refl _⟩, ?_, ?_⟩
    · refine Po.le_trans ha ?_
      show apply0 f₁.1 d₁.1 ⊑ apply0 f.1 d.1
      exact Po.le_trans (apply0_mono_left hf1 d₁.1) (apply0_mono_right f.1 hd1)
    · refine Po.le_trans hb ?_
      show apply0 f₂.1 d₂.1 ⊑ apply0 f.1 d.1
      exact Po.le_trans (apply0_mono_left hf2 d₂.1) (apply0_mono_right f.1 hd2)

/-- `⊥` is the principal ideal of `⊥`. -/
theorem principal_bot_le {σ : Ty} (I : T σ) : Ideal.principal (DSub.bot : D σ) ⊑ I := by
  intro a ha
  obtain ⟨b, hb⟩ := I.nonempty'
  have hle : a ⊑ (DSub.bot : D σ) := ha
  exact I.downward a b (Po.le_trans hle (DSub.bot_le b)) hb

theorem bot_eq_principal (σ : Ty) :
    (ScottDomain.bot : T σ) = Ideal.principal (DSub.bot : D σ) :=
  Po.le_antisymm (ScottDomain.bot_le _) (principal_bot_le _)

/-- `apply (⊥, x) = ⊥`. -/
theorem applyT_bot (σ τ : Ty) (x : T σ) :
    applyT (ScottDomain.bot : T (σ ⇒ τ)) x = Ideal.principal (DSub.bot : D τ) := by
  refine Po.le_antisymm ?_ (principal_bot_le _)
  rintro c ⟨f, hf, d, _, hc⟩
  have hfb : f ⊑ (DSub.bot : D (σ ⇒ τ)) :=
    Po.le_trans (show f ⊑ FinitaryBasis.bot from hf) (FinitaryBasis.bot_le DSub.bot)
  have hfeq : f = DSub.bot := Po.le_antisymm hfb (DSub.bot_le f)
  subst hfeq
  exact hc

/-- `apply` is monotone in its first argument. -/
theorem applyT_mono_left {σ τ : Ty} {F G : T (σ ⇒ τ)} (h : F ⊑ G) (E : T σ) :
    applyT F E ⊑ applyT G E := by
  rintro c ⟨f, hf, d, hd, hc⟩
  exact ⟨f, h f hf, d, hd, hc⟩

/-- `apply` is monotone in its second argument. -/
theorem applyT_mono_right {σ τ : Ty} (F : T (σ ⇒ τ)) {E E' : T σ} (h : E ⊑ E') :
    applyT F E ⊑ applyT F E' := by
  rintro c ⟨f, hf, d, hd, hc⟩
  exact ⟨f, hf, d, h d hd, hc⟩

/-! ## Lemma 4.7 and Claim 4.8 -/

/-- **Claim 4.8.**  *For `d ∈ D_σ`,
`d = ⊔ {q[?/a] | q ∈ Q_σ, q[?/a] ⊑ d, a ∈ ℕ^E_⊥}`.*

The set of single-branch approximations of `d` obtained by substituting a leaf
value at the end of a valid query. -/
def claim_4_8_approx {σ : Ty} (d : Tree σ) : Set (Tree σ) :=
  fun t => ∃ (q : Query σ) (a : Val), t = q.substTree (.leaf a) ∧ t ⊑ d

/-- A one-step query with a `⊥` leaf is the bare node `⟨i, q, ⊥⟩`. -/
theorem substTree_step_hole_bot {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (r : Resp (σ.arg i)) :
    Query.substTree (.step i q r .hole) (.leaf .bot) = Tree.node i q fun _ => Tree.bot := by
  simp only [Query.substTree]
  congr 1
  funext s
  split <;> rfl

theorem substTree_step {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (r : Resp (σ.arg i)) (p : Query σ) (a : Val) :
    Query.substTree (.step i q r p) (.leaf a)
      = Tree.node i q fun s => if s = r then Query.substTree p (.leaf a) else Tree.bot := rfl

/-- The least-upper-bound half of Claim 4.8: any tree above every single-branch
approximation of `d` is above `d`. -/
theorem claim_4_8_least {σ : Ty} : ∀ (d v : Tree σ),
    UpperBound (claim_4_8_approx d) v → Tree.Le d v := by
  intro d
  induction d with
  | leaf a =>
    intro v hv
    exact hv (.leaf a) ⟨.hole, a, rfl, Tree.Le.refl _⟩
  | node i q f ih =>
    intro v hv
    -- the bare node `⟨i, q, ⊥⟩` is one of the approximations, so `v` is a node
    have hbare : Tree.Le (Tree.node i q fun _ => Tree.bot) v := by
      have hmem : (Tree.node i q fun _ => Tree.bot) ∈ claim_4_8_approx (Tree.node i q f) := by
        refine ⟨.step i q (Resp.ans 0) .hole, .bot, (substTree_step_hole_bot i q _).symm, ?_⟩
        exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
      exact hv _ hmem
    obtain ⟨g, rfl⟩ := Tree.eq_node_of_le hbare
    refine Tree.Le.node _ _ _ _ fun s => ih s (g s) ?_
    -- every approximation of the `s`-branch of `d` lifts to an approximation of `d`
    rintro t ⟨p, a, rfl, hle⟩
    have hmem : (Tree.node i q fun u => if u = s then Query.substTree p (.leaf a) else Tree.bot)
        ∈ claim_4_8_approx (Tree.node i q f) := by
      refine ⟨.step i q s p, a, (substTree_step i q s p a).symm, ?_⟩
      refine Tree.Le.node _ _ _ _ fun u => ?_
      by_cases hu : u = s
      · subst hu; rw [if_pos rfl]; exact hle
      · rw [if_neg hu]; exact Tree.Le.bot _
    have := Tree.Le_node_inv (Tree.Le.trans (Tree.Le.refl _) (hv _ hmem)) s
    rwa [if_pos rfl] at this

/-- **Claim 4.8.** -/
theorem claim_4_8 {σ : Ty} (d : Tree σ) : IsLUB (claim_4_8_approx d) d := by
  refine ⟨?_, claim_4_8_least d⟩
  rintro t ⟨p, a, rfl, hle⟩
  exact hle

/-- Two trees with the same root either are both leaves with the same value, or
are both nodes with the same node value. -/
theorem eq_root_cases {σ : Ty} {d e : Tree σ} (h : d.root = e.root) :
    (∃ v, d = .leaf v ∧ e = .leaf v) ∨
    (∃ (i : Fin σ.arity) (q : Query (σ.arg i)) (f g : Resp (σ.arg i) → Tree σ),
      d = .node i q f ∧ e = .node i q g) := by
  cases d with
  | leaf v =>
    cases e with
    | leaf w =>
      have hvw : v = w := by simpa [Tree.root] using h
      exact Or.inl ⟨v, rfl, by rw [hvw]⟩
    | node j p g => exact absurd h (by simp [Tree.root])
  | node i q f =>
    cases e with
    | leaf w => exact absurd h (by simp [Tree.root])
    | node j p g =>
      have hij : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩ := by
        simpa [Tree.root] using h
      cases hij
      exact Or.inr ⟨i, q, f, g, rfl, rfl⟩

/-- **Lemma 4.7.**  *For `f, g ∈ D_σ`, `f ⋢ g` implies that there is a query `p`
such that `f @ p` and `g @ p` are both defined, `f @ p ⋢ g @ p`, and the
subtrees `f @ p` and `g @ p` are immediately incomparable.*

The proof is by induction on `f`.  If `f` and `g` have different roots the empty
query `?` already works.  If they have the same root they are either equal
leaves — impossible, since then `f ⊑ g` — or nodes `⟨i, q, h⟩` and `⟨i, q, h'⟩`
with `h r ⋢ h' r` for some response `r`; prefixing the query supplied by the
induction hypothesis with the step `⟨i, q, r⟩` gives the required query. -/
theorem lemma_4_7 {σ : Ty} : ∀ (f g : Tree σ), ¬ Tree.Le f g →
    ∃ (p : Query σ) (f' g' : Tree σ),
      f.at' p = some f' ∧ g.at' p = some g' ∧ ¬ Tree.Le f' g' ∧
      Tree.ImmIncomparable f' g' := by
  intro f
  induction f with
  | leaf v =>
    intro g h
    refine ⟨.hole, .leaf v, g, rfl, rfl, h, ?_⟩
    intro hroot
    rcases eq_root_cases hroot with ⟨w, hw, hg⟩ | ⟨i, q, f', g', hf', _⟩
    · cases hw; exact h (hg ▸ Tree.Le.leaf v)
    · exact absurd hf' (by simp)
  | node i q hf ih =>
    intro g h
    by_cases hroot : (Tree.node i q hf).root = g.root
    · rcases eq_root_cases hroot with ⟨w, hw, _⟩ | ⟨j, p, f', g', hfj, hgj⟩
      · exact absurd hw (by simp)
      · -- same node value: some branch must fail
        cases hfj
        have hex : ∃ r, ¬ Tree.Le (hf r) (g' r) := by
          refine Classical.byContradiction fun hall => h ?_
          rw [hgj]
          exact Tree.Le.node _ _ _ _ fun r =>
            Classical.byContradiction fun hr => hall ⟨r, hr⟩
        obtain ⟨r, hr⟩ := hex
        obtain ⟨p', a, b, ha, hb, hab, hinc⟩ := ih r (g' r) hr
        refine ⟨.step i q r p', a, b, ?_, ?_, hab, hinc⟩
        · rw [Tree.at'_step_self]; exact ha
        · rw [hgj, Tree.at'_step_self]; exact hb
    · exact ⟨.hole, .node i q hf, g, rfl, rfl, h, hroot⟩

/-! ### Reading answers out of a tree -/

/-- Inversion for `@` along a step. -/
theorem at'_step_inv {σ : Ty} {d : Tree σ} {i : Fin σ.arity} {q : Query (σ.arg i)}
    {r : Resp (σ.arg i)} {rest : Query σ} {e : Tree σ}
    (h : d.at' (.step i q r rest) = some e) :
    ∃ f : Resp (σ.arg i) → Tree σ, d = .node i q f ∧ (f r).at' rest = some e := by
  cases d with
  | leaf v => exact absurd h (by simp [Tree.at', Tree.stepAt])
  | node j p g =>
    by_cases hEq : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩
    · have h1 : i = j := congrArg Sigma.fst hEq
      subst h1
      have h2 : q = p := by injection hEq
      subst h2
      rw [Tree.at'_step_self] at h
      exact ⟨g, rfl, h⟩
    · rw [show (Tree.node j p g).at' (.step i q r rest) = none by
            simp only [Tree.at', Tree.stepAt, dif_neg hEq, Option.bind]] at h
      exact absurd h (by simp)

/-- `q[?/e] @ q = e`: substituting `e` at the marker of `q` puts `e` exactly at
position `q`. -/
theorem at'_substTree {σ : Ty} : ∀ (q : Query σ) (e : Tree σ),
    (q.substTree e).at' q = some e
  | .hole, e => rfl
  | .step i p r rest, e => by
      rw [show Query.substTree (.step i p r rest) e
            = Tree.node i p (fun s => if s = r then Query.substTree rest e else Tree.bot) from
          rfl, Tree.at'_step_self, if_pos rfl]
      exact at'_substTree rest e

/-- The tree of a response is the tree of its query with the answer planted. -/
theorem Resp.toTree_substAns {σ : Ty} : ∀ (q : Query σ) (x : RAns σ),
    (q.substAns x).toTree = q.substTree x.toTree
  | .hole, .num n => rfl
  | .hole, .node i p => rfl
  | .step i p r rest, x => by
      show Tree.node i p (fun s => if s = r then (rest.substAns x).toTree else Tree.bot) = _
      rw [Resp.toTree_substAns rest x]
      rfl

/-- `q[?/·]` is monotone. -/
theorem substTree_mono {σ : Ty} : ∀ (q : Query σ) {e e' : Tree σ}, Tree.Le e e' →
    Tree.Le (q.substTree e) (q.substTree e')
  | .hole, e, e', h => h
  | .step i p r rest, e, e', h => by
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs; rw [if_pos rfl, if_pos rfl]; exact substTree_mono rest h
      · rw [if_neg hs, if_neg hs]; exact Tree.Le.refl _

/-- A query's own tree is strictly below the tree of any response to it. -/
theorem toTree_lt_substAns {σ : Ty} (q : Query σ) (i : Fin σ.arity) (p : Query (σ.arg i)) :
    Tree.Le q.toTree (q.substAns (.node i p)).toTree ∧
      q.toTree ≠ (q.substAns (.node i p)).toTree := by
  rw [Resp.toTree_substAns]
  refine ⟨substTree_mono q (Tree.Le.bot _), fun hcon => ?_⟩
  have h1 : (Query.toTree q).at' q = some Tree.bot := at'_substTree q Tree.bot
  have h2 : (q.substTree (RAns.toTree (RAns.node i p))).at' q
      = some (RAns.toTree (RAns.node i p)) := at'_substTree q _
  rw [hcon, h2] at h1
  exact absurd (Option.some.inj h1) (by simp [RAns.toTree, Tree.bot])

/-! ### Planting a subtree at the perimeter

The proof of Lemma 4.16 separates two trees by feeding the argument a tree that
answers one of two competing queries with an error.  `plant q d e` writes `e` at
position `q` of `d`; where `q` probes the perimeter of `d` (Definition 4.5) this
is the join of `d` with the path `q[?/e]`. -/

/-- `d[q := e]`: replace the subtree of `d` at position `q` by `e`. -/
noncomputable def plant {σ : Ty} : Query σ → Tree σ → Tree σ → Tree σ
  | .hole, _, e => e
  | .step j p r rest, d, e =>
      match d with
      | .leaf v => .leaf v
      | .node i q f =>
          if h : (⟨j, p⟩ : NodeVal σ) = ⟨i, q⟩ then
            .node i q fun s =>
              if s = Tree.castResp (congrArg Sigma.fst h) r then plant rest (f s) e else f s
          else .node i q f

@[simp] theorem plant_hole {σ : Ty} (d e : Tree σ) : plant .hole d e = e := rfl

theorem plant_step_self {σ : Ty} (j : Fin σ.arity) (p : Query (σ.arg j))
    (r : Resp (σ.arg j)) (rest : Query σ) (f : Resp (σ.arg j) → Tree σ) (e : Tree σ) :
    plant (.step j p r rest) (.node j p f) e
      = .node j p fun s => if s = r then plant rest (f s) e else f s := by
  show (dite _ _ _) = _
  rw [dif_pos (rfl : (⟨j, p⟩ : NodeVal σ) = ⟨j, p⟩)]
  rfl

/-- Planting at a valid position puts the planted tree there. -/
theorem at'_plant_self {σ : Ty} : ∀ (q : Query σ) (d e : Tree σ),
    (∃ t, d.at' q = some t) → (plant q d e).at' q = some e
  | .hole, d, e, _ => rfl
  | .step j p r rest, d, e, ⟨t, ht⟩ => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv ht
      rw [plant_step_self, Tree.at'_step_self, if_pos rfl]
      exact at'_plant_self rest (f r) e ⟨t, hrest⟩

/-- Planting over `⊥` only increases the tree. -/
theorem le_plant {σ : Ty} : ∀ (q : Query σ) (d e : Tree σ),
    d.at' q = some Tree.bot → Tree.Le d (plant q d e)
  | .hole, d, e, hd => by
      have : d = Tree.bot := by injection hd
      subst this
      exact Tree.Le.bot e
  | .step j p r rest, d, e, hd => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hd
      rw [plant_step_self]
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs; rw [if_pos rfl]; exact le_plant rest (f s) e hrest
      · rw [if_neg hs]; exact Tree.Le.refl _

theorem at'_step_of_node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (j : Fin σ.arity) (p : Query (σ.arg j))
    (r : Resp (σ.arg j)) (rest : Query σ) (h : (⟨j, p⟩ : NodeVal σ) = ⟨i, q⟩) :
    (Tree.node i q f).at' (.step j p r rest)
      = (f (Tree.castResp (congrArg Sigma.fst h) r)).at' rest := by
  simp only [Tree.at', Tree.stepAt, dif_pos h, Option.bind]

theorem plant_step_of_node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (j : Fin σ.arity) (p : Query (σ.arg j))
    (r : Resp (σ.arg j)) (rest : Query σ) (e : Tree σ) (h : (⟨j, p⟩ : NodeVal σ) = ⟨i, q⟩) :
    plant (.step j p r rest) (.node i q f) e
      = .node i q fun s =>
          if s = Tree.castResp (congrArg Sigma.fst h) r then plant rest (f s) e else f s := by
  show (dite _ _ _) = _
  rw [dif_pos h]

/-- Planting at one perimeter position leaves the others untouched. -/
theorem at'_plant_other {σ : Ty} : ∀ (q : Query σ) (d e : Tree σ) (q' : Query σ),
    d.at' q = some Tree.bot → d.at' q' = some Tree.bot → q ≠ q' →
    (plant q d e).at' q' = some Tree.bot
  | .hole, d, e, q', hd, hd', hne => by
      have hdb : d = Tree.bot := by injection hd
      subst hdb
      cases q' with
      | hole => exact absurd rfl hne
      | step j p r rest => exact absurd hd' (by simp [Tree.at', Tree.stepAt, Tree.bot])
  | .step j p r rest, d, e, .hole, hd, hd', hne => by
      have hdb : d = Tree.bot := by injection hd'
      subst hdb
      exact absurd hd (by simp [Tree.at', Tree.stepAt, Tree.bot])
  | .step j p r rest, d, e, .step j' p' r' rest', hd, hd', hne => by
      obtain ⟨f, rfl, hdr⟩ := at'_step_inv hd
      obtain ⟨f', hf', hdr'⟩ := at'_step_inv hd'
      injection hf' with hjj hpp hff
      subst hjj
      have hp2 : p = p' := eq_of_heq hpp
      subst hp2
      have hf2 : f = f' := eq_of_heq hff
      subst hf2
      rw [plant_step_self, Tree.at'_step_self]
      by_cases hr : r' = r
      · subst hr
        rw [if_pos rfl]
        refine at'_plant_other rest (f r') e rest' hdr hdr' ?_
        intro hcon
        exact hne (by rw [hcon])
      · rw [if_neg hr]
        exact hdr'

/-- The path `q[?/e]` is below the tree obtained by planting `e` at `q`. -/
theorem substTree_le_plant {σ : Ty} : ∀ (q : Query σ) (d e : Tree σ),
    d.at' q = some Tree.bot → Tree.Le (q.substTree e) (plant q d e)
  | .hole, d, e, _ => Tree.Le.refl _
  | .step j p r rest, d, e, hd => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hd
      rw [plant_step_self]
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs; rw [if_pos rfl, if_pos rfl]; exact substTree_le_plant rest (f s) e hrest
      · rw [if_neg hs, if_neg hs]; exact Tree.Le.bot _

/-- If a tree contains the path `r`, then querying it along `r`'s query returns
the answer that `r` records.  This is what makes `apply₀` take the branch that
the argument's response selects (Definition 4.9). -/
theorem at'_resp {σ : Ty} : ∀ (r : Resp σ) (d : Tree σ), Tree.Le r.toTree d →
    (∃ n, r.ansOf = RAns.num n ∧ d.at' r.qry = some (.leaf (.num n))) ∨
    (∃ (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ),
      r.ansOf = RAns.node j p ∧ d.at' r.qry = some (.node j p h))
  | .ans n, d, hle => by
      refine Or.inl ⟨n, rfl, ?_⟩
      cases hle with
      | leaf _ => rfl
  | .node i p, d, hle => by
      obtain ⟨g, rfl⟩ := Tree.eq_node_of_le hle
      exact Or.inr ⟨i, p, g, rfl, rfl⟩
  | .step i q r rest, d, hle => by
      obtain ⟨g, rfl⟩ := Tree.eq_node_of_le hle
      have hb := Tree.Le_node_inv hle r
      rw [if_pos rfl] at hb
      have hrec := at'_resp rest (g r) hb
      show (∃ n, rest.ansOf = RAns.num n ∧
              (Tree.node i q g).at' (Query.step i q r rest.qry)
                = some (Tree.leaf (Val.num n))) ∨
           (∃ (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ),
              rest.ansOf = RAns.node j p ∧
              (Tree.node i q g).at' (Query.step i q r rest.qry)
                = some (Tree.node j p h))
      rw [Tree.at'_step_self]
      exact hrec

/-- `apply₀` on a node that probes the *first* argument takes the branch that
the argument's response selects. -/
theorem apply0_first {σ τ : Ty} (hi : 0 < (σ ⇒ τ).arity) (q : Query σ)
    (g : Resp σ → Tree (σ ⇒ τ)) (d₁ : Tree σ)
    (r : Resp σ) (hq : r.qry = q) (hle : Tree.Le r.toTree d₁) :
    apply0 (.node ⟨0, hi⟩ q g) d₁ = apply0 (g r) d₁ := by
  subst hq
  have hr : r.qry.substAns r.ansOf = r := Resp.substAns_qry_ansOf r
  rcases at'_resp r d₁ hle with ⟨n, hA, he⟩ | ⟨j, p, h, hA, he⟩
  · rw [apply0, he]
    show apply0 (g (r.qry.substAns (RAns.num n))) d₁ = apply0 (g r) d₁
    rw [← hA, hr]
  · rw [apply0, he]
    show apply0 (g (r.qry.substAns (RAns.node j p))) d₁ = apply0 (g r) d₁
    rw [← hA, hr]

/-! ## Lemma 4.14, Corollary 4.15 -/

/-- "`d₁ ⊒ ⊔ γ(i)`": `d₁` is an upper bound of the responses that `γ` records
about argument `i`.  Stating the hypothesis this way avoids presupposing that
the least upper bound exists. -/
def RespCtx.Above {σ : Ty} (γ : RespCtx σ) (i : Fin σ.arity)
    (d : Tree (σ.arg i)) : Prop :=
  ∀ r, r ∈ γ.at' i → r.toTree ⊑ d

/-- The same hypothesis for a tree context: `d` extends what `γ` knows about
argument `i`. -/
def Ctx.Above {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity) (d : Tree (σ.arg i)) : Prop :=
  γ i ⊑ d

/-- **Lemma 4.14.**  *Let `d ∈ D_σ`, let `q ∈ Q_σ` be a query that determines the
context `q̂`, and let `e` be a subtree in `D_σ(q̂)`.  If `d @ q = e` and
`d₁ ⊒ ⊔ q̂(1)`, then `apply (d, d₁) @ shift₁ (q) = apply (e, d₁)`.*

The hypothesis `q.Coherent` is the paper's `q ∈ Q_σ`: each step of `q` records a
response to the query that step asks (Definition 4.2, *Legal Responses*).  The
proof is the paper's induction on `q`: at a step probing the first argument,
`d₁ ⊒ ⊔ q̂(1)` means `d₁` contains that step's response, so `apply₀` takes
exactly that branch and `shift₁` erases the step; at a step probing a later
argument, `apply₀` reproduces the node with its index shifted down by one. -/
theorem lemma_4_14 : ∀ {a τ : Ty} (q : Query (a ⇒ τ)) (d e : Tree (a ⇒ τ)) (d₁ : Tree a),
    q.Coherent → d.at' q = some e → RespCtx.Above q.ctxList ⟨0, Nat.succ_pos _⟩ d₁ →
    (apply0 d d₁).at' q.shift1 = some (apply0 e d₁)
  | _, _, .hole, d, e, _, _, hq, _ => by
      have hde : d = e := by injection hq
      subst hde
      simp only [Query.shift1, Tree.at'_hole]
  | a, τ, .step i p r rest, d, e, d₁, hco, hq, hab => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      obtain ⟨hcr, hco'⟩ := hco
      have habTail : RespCtx.Above rest.ctxList ⟨0, Nat.succ_pos _⟩ d₁ := fun s hs =>
        hab s (List.mem_cons_of_mem _ hs)
      match i with
      | ⟨0, hi⟩ =>
        have hle : Tree.Le r.toTree d₁ := hab r (List.mem_cons_self ..)
        have hs : (Query.step ⟨0, hi⟩ p r rest).shift1 = rest.shift1 := by
          simp only [Query.shift1]
        rw [apply0_first hi p f d₁ r hcr hle, hs]
        exact lemma_4_14 rest (f r) e d₁ hco' hrest habTail
      | ⟨k + 1, hi⟩ =>
        have ha : apply0 (Tree.node ⟨k + 1, hi⟩ p f) d₁
            = Tree.node ⟨k, Nat.lt_of_succ_lt_succ hi⟩ p fun s => apply0 (f s) d₁ := by
          rw [apply0]
        have hs : (Query.step ⟨k + 1, hi⟩ p r rest).shift1
            = Query.step ⟨k, Nat.lt_of_succ_lt_succ hi⟩ p r rest.shift1 := by
          simp only [Query.shift1]
        rw [ha, hs, Tree.at'_step_self]
        exact lemma_4_14 rest (f r) e d₁ hco' hrest habTail

/-! ### `shift₁` and tree contexts -/

/-- `shift₁` preserves coherence. -/
theorem shift1_coherent : ∀ {a τ : Ty} (q : Query (a ⇒ τ)), q.Coherent → q.shift1.Coherent
  | _, _, .hole, _ => by simp only [Query.shift1]; exact trivial
  | a, τ, .step i p r rest, hco => by
      obtain ⟨hcr, hco'⟩ := hco
      match i with
      | ⟨0, hi⟩ =>
        rw [show (Query.step ⟨0, hi⟩ p r rest).shift1 = rest.shift1 by
          simp only [Query.shift1]]
        exact shift1_coherent rest hco'
      | ⟨k + 1, hi⟩ =>
        rw [show (Query.step ⟨k + 1, hi⟩ p r rest).shift1
            = Query.step ⟨k, Nat.lt_of_succ_lt_succ hi⟩ p r rest.shift1 by
          simp only [Query.shift1]]
        exact ⟨hcr, shift1_coherent rest hco'⟩

/-- A pair recorded in the context of `shift₁ q` about argument `i` is recorded
in the context of `q` about argument `i + 1`. -/
theorem mem_ctx_shift1 : ∀ {a τ : Ty} (q : Query (a ⇒ τ)) (i : Fin τ.arity)
    (hi : i.val + 1 < (a ⇒ τ).arity) (r : Resp (τ.arg i)),
    (⟨i, r⟩ : (j : Fin τ.arity) × Resp (τ.arg j)) ∈ q.shift1.ctxList →
    (⟨⟨i.val + 1, hi⟩, r⟩ : (j : Fin (a ⇒ τ).arity) × Resp ((a ⇒ τ).arg j)) ∈ q.ctxList
  | _, _, .hole, i, hi, r, hmem => by
      rw [show (Query.hole : Query (_ ⇒ _)).shift1 = Query.hole by
        simp only [Query.shift1]] at hmem
      exact absurd hmem (by simp [Query.ctxList])
  | a, τ, .step j p s rest, i, hi, r, hmem => by
      match j with
      | ⟨0, hj⟩ =>
        rw [show (Query.step ⟨0, hj⟩ p s rest).shift1 = rest.shift1 by
          simp only [Query.shift1]] at hmem
        exact List.mem_cons_of_mem _ (mem_ctx_shift1 rest i hi r hmem)
      | ⟨k + 1, hk⟩ =>
        rw [show (Query.step ⟨k + 1, hk⟩ p s rest).shift1
            = Query.step ⟨k, Nat.lt_of_succ_lt_succ hk⟩ p s rest.shift1 by
          simp only [Query.shift1]] at hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · -- the head: `i = ⟨k, _⟩` and `r = s`
          have hik : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := congrArg Sigma.fst heq
          subst hik
          have hrs : r = s := by injection heq
          subst hrs
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_ctx_shift1 rest i hi r htail)

/-- The `k`-ary form of Lemma 4.14: applying all the arguments to `d` gives the
same ground answer as applying them to the subtree `d @ q`, provided each
argument extends what `q̂` records about it. -/
theorem applyArgs_at_query : ∀ (σ : Ty) (q : Query σ) (d e : Tree σ)
    (ds : (i : Fin σ.arity) → Tree (σ.arg i)),
    q.Coherent → d.at' q = some e → (∀ i, RespCtx.Above q.ctxList i (ds i)) →
    applyArgs σ d ds = applyArgs σ e ds
  | .base, q, d, e, ds, _, hq, _ => by
      cases q with
      | hole =>
        have hde : d = e := by injection hq
        subst hde
        rfl
      | step i _ _ _ => exact absurd i.isLt (by simp)
  | .arrow a τ, q, d, e, ds, hco, hq, hab => by
      have h14 := lemma_4_14 q d e (ds ⟨0, Nat.succ_pos _⟩) hco hq (hab _)
      have habs : ∀ i : Fin τ.arity,
          RespCtx.Above q.shift1.ctxList i (ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by
        intro i r hr
        exact hab ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ r
          (mem_ctx_shift1 q i (Nat.succ_lt_succ i.isLt) r hr)
      show applyArgs τ (apply0 d (ds ⟨0, Nat.succ_pos _⟩)) _
          = applyArgs τ (apply0 e (ds ⟨0, Nat.succ_pos _⟩)) _
      exact applyArgs_at_query τ q.shift1 _ _ _ (shift1_coherent q hco) h14 habs

/-- **Corollary 4.15.**  *Let `σ = σ₁ → … σₖ → o`.  Let `q ∈ Q_σ` be a query that
determines the context `q̂`, and let `e` be a subtree in `D_σ(q̂)`.  If
`d ⊒ q[?/e]` and `dᵢ ⊒ ⊔ q̂(i)` for `i`, `1 ≤ i ≤ k`, then*
`apply (d, d₁, …, dₖ) = apply (q[?/e], d₁, …, dₖ) = apply (e, d₁, …, dₖ)`.

Both equations are instances of the `k`-ary form of Lemma 4.14.

A remark on the hypothesis.  Read literally, `d ⊒ q[?/e]` makes the first
equation false: taking `q = ?` and `e = ⊥` it would say that `apply` is constant
above `⊥`.  The reading under which the corollary is true, and the one the paper
uses (§5, in the representability argument, where the corollary is applied to
`q[?/aⱼ]` itself), is that `d` carries `e` *at* position `q`, i.e. `d @ q = e`.
That is the hypothesis taken here; the second equation, which is the one the
paper actually invokes, needs no hypothesis on `d` at all. -/
theorem corollary_4_15 (σ : Ty) (q : Query σ) (e d : Tree σ)
    (ds : (i : Fin σ.arity) → Tree (σ.arg i))
    (hco : q.Coherent) (hd : d.at' q = some e)
    (hab : ∀ i, RespCtx.Above q.ctxList i (ds i)) :
    applyArgs σ d ds = applyArgs σ (q.substTree e) ds ∧
    applyArgs σ (q.substTree e) ds = applyArgs σ e ds := by
  have h₂ : applyArgs σ (q.substTree e) ds = applyArgs σ e ds :=
    applyArgs_at_query σ q (q.substTree e) e ds hco (at'_substTree q e) hab
  exact ⟨by rw [applyArgs_at_query σ q d e ds hco hd hab, h₂], h₂⟩

/-- The half of Corollary 4.15 the paper invokes: a path carrying `e` at its
marker applies exactly like `e`. -/
theorem corollary_4_15_path (σ : Ty) (q : Query σ) (e : Tree σ)
    (ds : (i : Fin σ.arity) → Tree (σ.arg i))
    (hco : q.Coherent) (hab : ∀ i, RespCtx.Above q.ctxList i (ds i)) :
    applyArgs σ (q.substTree e) ds = applyArgs σ e ds :=
  applyArgs_at_query σ q (q.substTree e) e ds hco (at'_substTree q e) hab

/-! ### Descending into a legal tree

Two facts about Definition 4.2 that the tree-context reading makes available:
the context determined by a query grows by one response per step, and a subtree
reached by `@` is legal in the context its path determines. -/

/-- `R(q ⟨j,p,r'⟩, γ) = R(q, γ) ∪ {⟨j,r'⟩}` (Definition 4.12). -/
theorem Query.ctxFrom_snoc {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)),
    (q.snoc j p r').ctxFrom γ = (q.ctxFrom γ).cons j r'
  | .hole, _, _, _, _ => rfl
  | .step i a b rest, γ, j, p, r' => by
      show (rest.snoc j p r').ctxFrom (γ.cons i b) = _
      rw [Query.ctxFrom_snoc rest (γ.cons i b) j p r']
      rfl

/-- `q̂ ⟨j,p,r'⟩ = q̂ ∪ {⟨j,r'⟩}`. -/
theorem Query.ctx_snoc {σ : Ty} (q : Query σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)) :
    (q.snoc j p r').ctx = q.ctx.cons j r' :=
  Query.ctxFrom_snoc q Ctx.empty j p r'

/-- **Definition 4.2 travels down `@`.**  If `d ∈ D_σ(γ)` and `d @ q = e` then
`e ∈ D_σ(R(q, γ))`: the subtree reached along `q` is legal in the context `q`
determines.

This is the fact that Definition 4.12 presupposes when it speaks of "a subtree
`e` in `D_σ(q̂)`", and it is available here because a context records
approximation trees: descending one step through the branch `r` records exactly
the response `r`. -/
theorem TreeOk_at' {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (d e : Tree σ),
    TreeOk γ d → d.at' q = some e → TreeOk (q.ctxFrom γ) e
  | .hole, _, d, e, hd, hq => by
      have hde : d = e := by injection hq
      exact hde ▸ hd
  | .step i p r rest, γ, d, e, hd, hq => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      obtain ⟨_, _, hsub, hnon⟩ := TreeOk_node_inv hd
      have hfr : TreeOk (γ.cons i r) (f r) := by
        by_cases hr : LegalResp p r
        · exact hsub r hr
        · rw [hnon r hr]; exact TreeOk.leaf _ _
      exact TreeOk_at' rest (γ.cons i r) (f r) e hfr hrest

/-- Extending a legal query by one step keeps every recorded response legal. -/
theorem QueryOk_snoc {σ : Ty} : ∀ (q : Query σ) (j : Fin σ.arity) (p : Query (σ.arg j))
    (r' : Resp (σ.arg j)), QueryOk σ q → LegalResp p r' → QueryOk σ (q.snoc j p r')
  | .hole, j, p, r', _, hr => (QueryOk_step j p r' .hole).mpr ⟨hr, QueryOk_hole⟩
  | .step i a b rest, j, p, r', hq, hr => by
      obtain ⟨hb, hrest⟩ := (QueryOk_step i a b rest).mp hq
      exact (QueryOk_step i a b (rest.snoc j p r')).mpr
        ⟨hb, QueryOk_snoc rest j p r' hrest hr⟩

/-- Recording the response `q[?/⟨j,p,⊥⟩]` opens exactly the positions one step
beyond `q`: what was the perimeter position `q` becomes the perimeter position
`q ⟨j,p,r'⟩`, for every `r'`. -/
theorem at'_join_snoc {σ : Ty} : ∀ (q : Query σ) (t : Tree σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)), t.at' q = some Tree.bot →
    (Tree.join t (q.substAns (.node j p)).toTree).at' (q.snoc j p r') = some Tree.bot
  | .hole, t, j, p, r', ht => by
      have htb : t = Tree.bot := by injection ht
      subst htb
      show (Tree.node j p fun _ => Tree.bot).at' (.step j p r' .hole) = _
      rw [Tree.at'_step_self]
      rfl
  | .step i a b rest, t, j, p, r', ht => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv ht
      have hjoin : Tree.join (Tree.node i a f)
            ((Query.step i a b rest).substAns (.node j p)).toTree
          = Tree.node i a fun s => Tree.join (f s)
              (if s = b then (rest.substAns (.node j p)).toTree else Tree.bot) := by
        show Tree.join (Tree.node i a f) (Tree.node i a _) = _
        rw [Tree.join_node_self]
      show Tree.at' _ (Query.step i a b (rest.snoc j p r')) = _
      rw [hjoin, Tree.at'_step_self, if_pos rfl]
      exact at'_join_snoc rest (f b) j p r' hrest

/-- **Definition 4.2's "extend by exactly one node".**  Recording the response
`q[?/⟨j,p,⊥⟩]` turns the perimeter position `q` into the perimeter positions
`q ⟨j,p,r'⟩`, one for each legal response `r'` to `p`. -/
theorem legalQuery_join_snoc {σ : Ty} (q : Query σ) (t : Tree σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (r' : Resp (σ.arg j)) (ht : LegalQuery t q)
    (hr : LegalResp p r') :
    LegalQuery (Tree.join t (q.substAns (.node j p)).toTree) (q.snoc j p r') :=
  ⟨at'_join_snoc q t j p r' ht.1, QueryOk_snoc q j p r' ht.2 hr⟩

/-- A finitary tree has only finitely many **live positions**: there is a list
containing every query `q` with `d @ q` defined and proper.  A path to a proper
subtree passes only through proper branches, of which each node has finitely
many. -/
theorem Finitary_live_queries {σ : Ty} : ∀ {d : Tree σ}, Tree.Finitary d →
    ∃ l : List (Query σ), ∀ (q : Query σ) (e : Tree σ),
      d.at' q = some e → e ≠ Tree.bot → q ∈ l := by
  intro d hd
  induction hd with
  | leaf v =>
    refine ⟨[.hole], fun q e hq he => ?_⟩
    cases q with
    | hole => exact List.mem_cons_self ..
    | step j p r rest => exact absurd hq (by simp [Tree.at', Tree.stepAt])
  | node i p f hfin _ ih =>
    obtain ⟨pl, hpl⟩ := hfin
    have hL : ∀ r, ∃ lr : List (Query σ), ∀ (q : Query σ) (e : Tree σ),
        (f r).at' q = some e → e ≠ Tree.bot → q ∈ lr := fun r => ih r
    refine ⟨.hole :: pl.flatMap (fun r => (Classical.choose (hL r)).map (.step i p r)),
      fun q e hq he => ?_⟩
    cases q with
    | hole => exact List.mem_cons_self ..
    | step j p' r rest =>
      obtain ⟨f₂, hf₂, hrest⟩ := at'_step_inv hq
      injection hf₂ with hji hpp hff
      subst hji
      have hp2 : p = p' := eq_of_heq hpp
      subst hp2
      have hf2 : f = f₂ := eq_of_heq hff
      subst hf2
      have hfr : f r ≠ Tree.bot := by
        intro hb
        rw [hb] at hrest
        cases rest with
        | hole => exact he (Option.some.inj hrest).symm
        | step _ _ _ _ => exact absurd hrest (by simp [Tree.at', Tree.stepAt, Tree.bot])
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, hpl r hfr, ?_⟩)
      exact List.mem_map.mpr ⟨rest, Classical.choose_spec (hL r) rest e hrest he, rfl⟩

/-! ### Legal paths

The argument tree that the proof of Lemma 4.16 feeds to `f` and `g` is `⊔ q̂(1)`,
the approximation tree the separating path determines for the first argument.
These lemmas say what is needed about it: it is legal, it dominates every
response the path records, and one further error may be planted at any perimeter
position. -/

/-- `q` is a **legal path** in the context `γ`: each step probes the perimeter of
what the context then knows and records a legal response to that probe. -/
def Query.LegalIn {σ : Ty} : Ctx σ → Query σ → Prop
  | _, .hole => True
  | γ, .step i p r rest => LegalQuery (γ i) p ∧ LegalResp p r ∧ Query.LegalIn (γ.cons i r) rest

/-- A legal path records legal responses. -/
theorem Query.queryOk_of_legalIn {σ : Ty} : ∀ (γ : Ctx σ) (q : Query σ),
    q.LegalIn γ → QueryOk σ q
  | _, .hole, _ => QueryOk_hole
  | γ, .step i p r rest, ⟨_, hr, hrest⟩ =>
      (QueryOk_step i p r rest).mpr ⟨hr, Query.queryOk_of_legalIn _ rest hrest⟩

/-- **Every path to a non-`⊥` subtree of a legal tree is legal.**  A step
through an illegal response leads to `⊥` and stays there. -/
theorem legalPath_of_TreeOk {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (d e : Tree σ),
    TreeOk γ d → d.at' q = some e → e ≠ Tree.bot → q.LegalIn γ
  | .hole, _, _, _, _, _, _ => trivial
  | .step i p r rest, γ, d, e, hd, hq, hne => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      obtain ⟨hp, _, hsub, hnon⟩ := TreeOk_node_inv hd
      have hr : LegalResp p r := by
        refine Classical.byContradiction fun hcon => ?_
        rw [hnon r hcon] at hrest
        cases rest with
        | hole => exact hne (Option.some.inj hrest).symm
        | step j a b rest' =>
          exact absurd hrest (by simp [Tree.at', Tree.stepAt, Tree.bot])
      exact ⟨hp, hr, legalPath_of_TreeOk rest (γ.cons i r) (f r) e (hsub r hr) hrest hne⟩

/-- Joining in a response that answers a perimeter position only grows the tree,
and the response's own path is below the result. -/
theorem le_join_resp {σ : Ty} : ∀ (r : Resp σ) (t : Tree σ),
    t.at' r.qry = some Tree.bot →
    Tree.Le t (Tree.join t r.toTree) ∧ Tree.Le r.toTree (Tree.join t r.toTree)
  | .ans n, t, ht => by
      have htb : t = Tree.bot := by injection ht
      subst htb
      exact ⟨Tree.Le.bot _, Tree.Le.refl _⟩
  | .node j p, t, ht => by
      have htb : t = Tree.bot := by injection ht
      subst htb
      exact ⟨Tree.Le.bot _, Tree.Le.refl _⟩
  | .step i p s rest, t, ht => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv ht
      have hjoin : Tree.join (Tree.node i p f) (Resp.step i p s rest).toTree
          = Tree.node i p fun u => Tree.join (f u)
              (if u = s then rest.toTree else Tree.bot) := by
        show Tree.join (Tree.node i p f) (Tree.node i p _) = _
        rw [Tree.join_node_self]
      rw [hjoin]
      constructor
      · refine Tree.Le.node _ _ _ _ fun u => ?_
        by_cases hu : u = s
        · subst hu; rw [if_pos rfl]; exact (le_join_resp rest (f u) hrest).1
        · rw [if_neg hu, Tree.join_bot_right]; exact Tree.Le.refl _
      · show Tree.Le (Tree.node i p _) _
        refine Tree.Le.node _ _ _ _ fun u => ?_
        by_cases hu : u = s
        · subst hu; rw [if_pos rfl]; exact (le_join_resp rest (f u) hrest).2
        · rw [if_neg hu]; exact Tree.Le.bot _

/-- Along a legal path the context only grows. -/
theorem Ctx.le_ctxFrom {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ), q.LegalIn γ →
    ∀ i, Tree.Le (γ i) ((q.ctxFrom γ) i)
  | .hole, _, _, _ => Tree.Le.refl _
  | .step k p r rest, γ, ⟨hp, hr, hrest⟩, i => by
      refine Tree.Le.trans ?_ (Ctx.le_ctxFrom rest (γ.cons k r) hrest i)
      by_cases hik : k = i
      · subst hik
        rw [Ctx.cons_self]
        exact (le_join_resp r (γ k) (qry_of_legalResp hr ▸ hp.1)).1
      · rw [Ctx.cons_other _ _ hik]; exact Tree.Le.refl _

/-- Every response a legal path records is below the tree the path determines:
this is the hypothesis `d₁ ⊒ ⊔ q̂(1)` of Lemma 4.14. -/
theorem Ctx.above_ctxFrom {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ), q.LegalIn γ →
    ∀ i, RespCtx.Above q.ctxList i ((q.ctxFrom γ) i)
  | .hole, _, _, _, r, hr => absurd hr (by simp [Query.ctxList, RespCtx.at'])
  | .step k p s rest, γ, ⟨hp, hs, hrest⟩, i, r, hr => by
      rcases List.mem_cons.mp hr with heq | htail
      · have hik : i = k := congrArg Sigma.fst heq
        subst hik
        have hrs : r = s := by injection heq
        subst hrs
        refine Tree.Le.trans ?_ (Ctx.le_ctxFrom rest (γ.cons i r) hrest i)
        rw [Ctx.cons_self]
        exact (le_join_resp r (γ i) (qry_of_legalResp hs ▸ hp.1)).2
      · exact Ctx.above_ctxFrom rest (γ.cons k s) hrest i r htail

/-- Joining in a legal response keeps the tree legal. -/
theorem TreeOk_join_resp {σ : Ty} : ∀ (r : Resp σ) (γ : Ctx σ) (t : Tree σ),
    TreeOk γ t → t.at' r.qry = some Tree.bot → QueryOk σ r.qry →
    RAns.Ok' ((r.qry).ctxFrom γ) r.ansOf → TreeOk γ (Tree.join t r.toTree)
  | .ans n, γ, t, ht, hat, _, _ => by
      have htb : t = Tree.bot := by injection hat
      subst htb
      exact TreeOk.leaf γ _
  | .node j p, γ, t, ht, hat, _, hans => by
      have htb : t = Tree.bot := by injection hat
      subst htb
      show TreeOk γ (Tree.node j p fun _ => Tree.bot)
      exact TreeOk.node γ j p _ hans ⟨[], fun _ hr => absurd rfl hr⟩
        (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
  | .step i p s rest, γ, t, ht, hat, hok, hans => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hat
      obtain ⟨hp, hfin, hsub, hnon⟩ := TreeOk_node_inv ht
      obtain ⟨hs, hokr⟩ := (QueryOk_step i p s rest.qry).mp hok
      have hjoin : Tree.join (Tree.node i p f) (Resp.step i p s rest).toTree
          = Tree.node i p fun u => Tree.join (f u)
              (if u = s then rest.toTree else Tree.bot) := by
        show Tree.join (Tree.node i p f) (Tree.node i p _) = _
        rw [Tree.join_node_self]
      rw [hjoin]
      refine TreeOk.node γ i p _ hp ?_ (fun u _ => ?_) (fun u hu => ?_)
      · obtain ⟨l, hl⟩ := hfin
        refine ⟨s :: l, fun u hu => ?_⟩
        by_cases hus : u = s
        · rw [hus]; exact List.mem_cons_self ..
        · dsimp only at hu
          rw [if_neg hus, Tree.join_bot_right] at hu
          exact List.mem_cons_of_mem _ (hl u hu)
      · by_cases hus : u = s
        · subst hus
          rw [if_pos rfl]
          exact TreeOk_join_resp rest (γ.cons i u) (f u) (hsub u hs) hrest hokr hans
        · rw [if_neg hus, Tree.join_bot_right]
          by_cases hlu : LegalResp p u
          · exact hsub u hlu
          · rw [hnon u hlu]; exact TreeOk.leaf _ _
      · have hus : ¬ u = s := fun he => hu (he ▸ hs)
        rw [if_neg hus, Tree.join_bot_right]
        exact hnon u hu

/-- Planting a leaf at a perimeter position of a legal tree keeps it legal. -/
theorem TreeOk_plant_leaf {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ) (t : Tree σ) (v : Val),
    TreeOk γ t → t.at' q = some Tree.bot → QueryOk σ q →
    TreeOk γ (plant q t (.leaf v))
  | .hole, γ, t, v, _, _, _ => TreeOk.leaf γ v
  | .step i p s rest, γ, t, v, ht, hat, hok => by
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
          exact TreeOk_plant_leaf rest (γ.cons i u) (f u) v (hsub u hs) hrest hokr
        · rw [if_neg hus]
          by_cases hlu : LegalResp p u
          · exact hsub u hlu
          · rw [hnon u hlu]; exact TreeOk.leaf _ _
      · have hus : ¬ u = s := fun he => hu (he ▸ hs)
        rw [if_neg hus]
        exact hnon u hu

/-- The tree a legal path determines for each argument is itself legal. -/
theorem TreeOk_ctxFrom {σ : Ty} : ∀ (q : Query σ) (γ : Ctx σ), q.LegalIn γ →
    (∀ i, TreeOk Ctx.empty (γ i)) → ∀ i, TreeOk Ctx.empty ((q.ctxFrom γ) i)
  | .hole, _, _, hγ, i => hγ i
  | .step k p s rest, γ, ⟨hp, hs, hrest⟩, hγ, i => by
      refine TreeOk_ctxFrom rest (γ.cons k s) hrest (fun j => ?_) i
      by_cases hkj : k = j
      · subst hkj
        rw [Ctx.cons_self]
        obtain ⟨x, rfl, hx⟩ := hs
        refine TreeOk_join_resp _ Ctx.empty (γ k) (hγ k) ?_ ?_ ?_
        · rw [Query.qry_substAns]; exact hp.1
        · rw [Query.qry_substAns]; exact hp.2
        · rw [Query.qry_substAns, Query.ansOf_substAns]
          exact hx
      · rw [Ctx.cons_other _ _ hkj]; exact hγ j

/-! ## Lemma 4.16, Theorem 4.11 -/

/-- An error value distinct from a given leaf value.  The proof of Lemma 4.16
needs *two* error values: with only one, `error` and `⟨1,?,λx.error⟩` are
incomparable yet apply alike, and order-extensionality fails (footnote 7,
attributed to P.-L. Curien). -/
def Val.otherErr : Val → Bool
  | .err true => false
  | _ => true

theorem Val.err_otherErr_ne : ∀ v : Val, Val.err v.otherErr ≠ v
  | .bot => fun h => Val.noConfusion h
  | .num _ => fun h => Val.noConfusion h
  | .err true => fun h => by injection h with hb; exact Bool.noConfusion hb
  | .err false => fun h => by injection h with hb; exact Bool.noConfusion hb

/-- **The separating argument of Lemma 4.16.**

Given two immediately incomparable subtrees `f'`, `g'` of `D_{σ→τ}(γ)` with
`f' ⋢ g'`, an argument tree `d ⊒ ⊔γ(1)` on which they disagree.  Following the
paper's case analysis: where one side is a constant and the other probes its
first argument, `d` answers that probe with an error the constant is not; where
both probe the first argument, they probe *different* perimeter positions
(legality), so answering one with an error leaves the other at `⊥`; in every
remaining case `d = ⊔γ(1)` already works, because `apply₀` turns a probe of a
later argument into a node and a node is never comparable to a leaf or to a node
with a different node value. -/
theorem lemma_4_16_separate {σ τ : Ty} (γ : Ctx (σ ⇒ τ))
    (hd₁ : TreeOk Ctx.empty (γ ⟨0, Nat.succ_pos _⟩))
    (f' g' : Tree (σ ⇒ τ)) (hfok : TreeOk γ f') (hgok : TreeOk γ g')
    (hnle : ¬ Tree.Le f' g') (hroot : f'.root ≠ g'.root) :
    ∃ d : Tree σ, TreeOk Ctx.empty d ∧ Tree.Le (γ ⟨0, Nat.succ_pos _⟩) d ∧
      ∀ g'' : Tree (σ ⇒ τ), g''.root = g'.root →
        ¬ Tree.Le (apply0 f' d) (apply0 g'' d) := by
  -- planting an error at a perimeter position of the first argument's tree
  have hplant : ∀ (p : Query σ) (b : Bool), LegalQuery (γ ⟨0, Nat.succ_pos _⟩) p →
      ∃ d : Tree σ, TreeOk Ctx.empty d ∧ Tree.Le (γ ⟨0, Nat.succ_pos _⟩) d ∧
        d.at' p = some (.leaf (.err b)) ∧
        ∀ p' : Query σ, LegalQuery (γ ⟨0, Nat.succ_pos _⟩) p' → p ≠ p' →
          d.at' p' = some Tree.bot := by
    intro p b hp
    refine ⟨plant p (γ ⟨0, Nat.succ_pos _⟩) (.leaf (.err b)),
      TreeOk_plant_leaf p Ctx.empty _ _ hd₁ hp.1 hp.2,
      le_plant p _ _ hp.1, at'_plant_self p _ _ ⟨_, hp.1⟩, fun p' hp' hne => ?_⟩
    exact at'_plant_other p _ _ p' hp.1 hp'.1 hne
  cases f' with
  | leaf v =>
    have hvb : v ≠ Val.bot := by
      intro hb; subst hb; exact hnle (Tree.Le.bot g')
    cases g' with
    | leaf w =>
      refine ⟨_, hd₁, Tree.Le.refl _, ?_⟩
      rintro (w'' | ⟨j'', p'', k''⟩) hgr
      · simp only [Tree.root, Sum.inl.injEq] at hgr
        rw [hgr]
        show ¬ Tree.Le (Tree.leaf v : Tree τ) (Tree.leaf w)
        have hvw : v ≠ w := fun he => hnle (he ▸ Tree.Le.leaf v)
        exact Tree.not_leaf_le_leaf hvb hvw
      · exact absurd hgr (by simp [Tree.root])
    | node j p' k' =>
      match j with
      | ⟨0, hj⟩ =>
        obtain ⟨hp', _, _, _⟩ := TreeOk_node_inv hgok
        obtain ⟨d, hdok, hdle, hdp, _⟩ := hplant p' v.otherErr hp'
        refine ⟨d, hdok, hdle, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨0, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (Tree.leaf v) (apply0 (Tree.node ⟨0, hj⟩ p' k'') d)
          rw [apply0, hdp]
          exact Tree.not_leaf_le_leaf hvb fun he => Val.err_otherErr_ne v he.symm
      | ⟨m + 1, hj⟩ =>
        refine ⟨_, hd₁, Tree.Le.refl _, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨m + 1, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (Tree.leaf v) (apply0 (Tree.node ⟨m + 1, hj⟩ p' k'') _)
          rw [apply0]
          exact Tree.not_leaf_le_node hvb
  | node i p k =>
    cases g' with
    | leaf w =>
      match i with
      | ⟨0, hi⟩ =>
        obtain ⟨hp, _, _, _⟩ := TreeOk_node_inv hfok
        obtain ⟨d, hdok, hdle, hdp, _⟩ := hplant p w.otherErr hp
        refine ⟨d, hdok, hdle, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · simp only [Tree.root, Sum.inl.injEq] at hgr
          rw [hgr]
          show ¬ Tree.Le (apply0 (Tree.node ⟨0, hi⟩ p k) d) (Tree.leaf w)
          rw [apply0, hdp]
          exact Tree.not_leaf_le_leaf (fun he => Val.noConfusion he)
            (fun he => Val.err_otherErr_ne w he)
        · exact absurd hgr (by simp [Tree.root])
      | ⟨n + 1, hi⟩ =>
        refine ⟨_, hd₁, Tree.Le.refl _, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · simp only [Tree.root, Sum.inl.injEq] at hgr
          rw [hgr]
          show ¬ Tree.Le (apply0 (Tree.node ⟨n + 1, hi⟩ p k) _) (Tree.leaf w)
          rw [apply0]
          exact Tree.not_le_leaf
        · exact absurd hgr (by simp [Tree.root])
    | node j p' k' =>
      have hnv : (⟨i, p⟩ : NodeVal (σ ⇒ τ)) ≠ ⟨j, p'⟩ := fun he =>
        hroot (by rw [Tree.root, Tree.root, he])
      match i, j with
      | ⟨0, hi⟩, ⟨0, hj⟩ =>
        obtain ⟨hp, _, _, _⟩ := TreeOk_node_inv hfok
        obtain ⟨hp', _, _, _⟩ := TreeOk_node_inv hgok
        have hpp : p ≠ p' := fun he => hnv (by subst he; rfl)
        obtain ⟨d, hdok, hdle, hdp, hdo⟩ := hplant p true hp
        refine ⟨d, hdok, hdle, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨0, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (apply0 (Tree.node ⟨0, hi⟩ p k) d)
            (apply0 (Tree.node ⟨0, hj⟩ p' k'') d)
          rw [apply0, apply0, hdp, hdo p' hp' hpp]
          exact Tree.not_leaf_le_leaf (fun he => Val.noConfusion he)
            (fun he => Val.noConfusion he)
      | ⟨0, hi⟩, ⟨m + 1, hj⟩ =>
        obtain ⟨hp, _, _, _⟩ := TreeOk_node_inv hfok
        obtain ⟨d, hdok, hdle, hdp, _⟩ := hplant p true hp
        refine ⟨d, hdok, hdle, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨m + 1, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (apply0 (Tree.node ⟨0, hi⟩ p k) d)
            (apply0 (Tree.node ⟨m + 1, hj⟩ p' k'') d)
          rw [apply0, apply0, hdp]
          exact Tree.not_leaf_le_node (fun he => Val.noConfusion he)
      | ⟨n + 1, hi⟩, ⟨0, hj⟩ =>
        obtain ⟨hp', _, _, _⟩ := TreeOk_node_inv hgok
        obtain ⟨d, hdok, hdle, hdp, _⟩ := hplant p' true hp'
        refine ⟨d, hdok, hdle, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨0, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (apply0 (Tree.node ⟨n + 1, hi⟩ p k) d)
            (apply0 (Tree.node ⟨0, hj⟩ p' k'') d)
          rw [apply0, apply0, hdp]
          exact Tree.not_le_leaf
      | ⟨n + 1, hi⟩, ⟨m + 1, hj⟩ =>
        refine ⟨_, hd₁, Tree.Le.refl _, ?_⟩
        rintro (w'' | ⟨j'', p'', k''⟩) hgr
        · exact absurd hgr (by simp [Tree.root])
        · simp only [Tree.root, Sum.inr.injEq] at hgr
          have h1 : j'' = ⟨m + 1, hj⟩ := congrArg Sigma.fst hgr
          subst h1
          have h2 : p'' = p' := by injection hgr
          rw [h2]
          show ¬ Tree.Le (apply0 (Tree.node ⟨n + 1, hi⟩ p k) _)
            (apply0 (Tree.node ⟨m + 1, hj⟩ p' k'') _)
          rw [apply0, apply0]
          refine Tree.not_node_le_node fun he => hnv ?_
          have hnm : n = m := by
            have := congrArg (fun x => x.1.val) he
            simpa using this
          subst hnm
          have hpp2 : p = p' := by injection he
          subst hpp2
          rfl

/-- **Lemma 4.16.**  *Let `f, g` be elements in `D_{σ→τ}`.  If for all finite
`d ∈ D_σ`, `apply (f, d) ⊑ apply (g, d)`, then `f ⊑ g`.*

The hypotheses `TreeOk Ctx.empty f` and `TreeOk Ctx.empty g` render "`f, g ∈ D_{σ→τ}`" and are
*not* removable.  The paper's proof separates `f` from `g` at a position where
their subtrees are immediately incomparable (Lemma 4.7) by feeding the argument
a tree that answers one of the two competing queries with `error₁` and the other
with `error₂`.  That the two queries can be answered independently is exactly
Definition 4.2's legality condition — a legal query never re-probes a node the
context has already answered — so without legality no separating argument need
exist. -/
theorem lemma_4_16 {σ τ : Ty} (f g : Tree (σ ⇒ τ))
    (hf : TreeOk Ctx.empty f) (hg : TreeOk Ctx.empty g)
    (h : ∀ d : Tree σ, TreeOk Ctx.empty d → apply0 f d ⊑ apply0 g d) : f ⊑ g := by
  refine Classical.byContradiction fun hfg => ?_
  -- Lemma 4.7: a path to immediately incomparable subtrees
  obtain ⟨q, f', g', hfq, hgq, hnle, hroot⟩ := lemma_4_7 f g hfg
  have hf'ne : f' ≠ Tree.bot := by
    intro hb; subst hb; exact hnle (Tree.Le.bot g')
  -- the path is legal, hence coherent, and determines a legal argument tree
  have hpath : q.LegalIn Ctx.empty :=
    legalPath_of_TreeOk q Ctx.empty f f' hf hfq hf'ne
  have hco : q.Coherent := QueryOk.coherent (Query.queryOk_of_legalIn Ctx.empty q hpath)
  have hd₁ : TreeOk Ctx.empty (q.ctx ⟨0, Nat.succ_pos _⟩) :=
    TreeOk_ctxFrom q Ctx.empty hpath (fun _ => TreeOk.leaf _ _) _
  have hab₁ : RespCtx.Above q.ctxList ⟨0, Nat.succ_pos _⟩ (q.ctx ⟨0, Nat.succ_pos _⟩) :=
    Ctx.above_ctxFrom q Ctx.empty hpath _
  -- the separating argument, on which the two subtrees disagree
  obtain ⟨d, hdok, hdle, hsep⟩ := lemma_4_16_separate q.ctx hd₁ f' g'
    (TreeOk_at' q Ctx.empty f f' hf hfq) (TreeOk_at' q Ctx.empty g g' hg hgq) hnle hroot
  -- Lemma 4.14 transports the disagreement to `shift₁ q`
  have hab : RespCtx.Above q.ctxList ⟨0, Nat.succ_pos _⟩ d :=
    fun r hr => Tree.Le.trans (hab₁ r hr) hdle
  have h14f := lemma_4_14 q f f' d hco hfq hab
  have h14g := lemma_4_14 q g g' d hco hgq hab
  rcases at'_mono q.shift1 (h d hdok) with hn | ⟨e, e', he, he', hee⟩
  · rw [h14f] at hn; exact Option.noConfusion hn
  · have h1 : apply0 f' d = e := Option.some.inj (h14f.symm.trans he)
    have h2 : apply0 g' d = e' := Option.some.inj (h14g.symm.trans he')
    exact hsep g' rfl (h1 ▸ h2 ▸ hee)

/-- **Uniform separation**: the content of Theorem 4.11's continuity argument.
If the finite `f₀ ∈ D_{σ→τ}` is not in the ideal `G`, then a *single* finite
argument `d` witnesses `apply (f₀, d) ⋢ apply (g₀, d)` for every `g₀ ∈ G` at
once.

Uniformity holds for two reasons.  The separating positions produced by
Lemma 4.7 all lie in the finite tree `f₀`, so there are finitely many of them
(`Finitary_live_queries`); choosing, for each one that any member of `G` ever
answers properly, a member that does, and a bound `g⁎ ∈ G` of those finitely
many members, Lemma 4.7 against `g⁎` yields a position `q` at which every
`g₀ ⊒ g⁎` — hence, by directedness, effectively every `g₀ ∈ G` — carries a
subtree with the *same root* as `g⁎ @ q`.  And the root is all the separating
argument (`lemma_4_16_separate`) consults about the right-hand side. -/
theorem uniform_separation {σ τ : Ty} (f₀ : Tree (σ ⇒ τ)) (hf : TreeOk Ctx.empty f₀)
    (G : T (σ ⇒ τ)) (hnot : ∀ g : D (σ ⇒ τ), g ∈ G → ¬ Tree.Le f₀ g.1) :
    ∃ d : Tree σ, TreeOk Ctx.empty d ∧
      ∀ g : D (σ ⇒ τ), g ∈ G → ¬ Tree.Le (apply0 f₀ d) (apply0 g.1 d) := by
  -- the finitely many positions of `f₀` carrying a proper subtree
  obtain ⟨l, hl⟩ := Finitary_live_queries (Finitary_of_TreeOk hf)
  -- for each position that some member of `G` answers properly, a witness
  have hsel : ∃ ws : List (D (σ ⇒ τ)), (∀ w, w ∈ ws → w ∈ G) ∧
      ∀ q, q ∈ l →
        (∃ g : D (σ ⇒ τ), g ∈ G ∧ ∃ e, g.1.at' q = some e ∧ e ≠ Tree.bot) →
        ∃ w, w ∈ ws ∧ ∃ e, w.1.at' q = some e ∧ e ≠ Tree.bot := by
    clear hl
    induction l with
    | nil => exact ⟨[], fun _ h => absurd h (by simp), fun q hq => absurd hq (by simp)⟩
    | cons q l ih =>
      obtain ⟨ws, hws, hcov⟩ := ih
      by_cases hq : ∃ g : D (σ ⇒ τ), g ∈ G ∧ ∃ e, g.1.at' q = some e ∧ e ≠ Tree.bot
      · obtain ⟨g, hg, he⟩ := hq
        refine ⟨g :: ws, fun w hw => ?_, fun q' hq' hex => ?_⟩
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact hg
          · exact hws w hw
        · rcases List.mem_cons.mp hq' with rfl | hq'
          · exact ⟨g, List.mem_cons_self .., he⟩
          · obtain ⟨w, hw, hwe⟩ := hcov q' hq' hex
            exact ⟨w, List.mem_cons_of_mem _ hw, hwe⟩
      · refine ⟨ws, hws, fun q' hq' hex => ?_⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact absurd hex hq
        · exact hcov q' hq' hex
  obtain ⟨ws, hws, hcov⟩ := hsel
  -- a single member of `G` above all the witnesses
  obtain ⟨gm, hgm, hub⟩ := G.list_bounded ws hws
  -- Lemma 4.7 against that member
  obtain ⟨q, f', g', hfq, hgq, hnle, hroot⟩ := lemma_4_7 f₀ gm.1 (hnot gm hgm)
  have hf'ne : f' ≠ Tree.bot := fun hb => hnle (hb ▸ Tree.Le.bot g')
  have hql : q ∈ l := hl q f' hfq hf'ne
  -- above `gm`, the root of the subtree at `q` is fixed
  have hstable : ∀ g : D (σ ⇒ τ), g ∈ G → gm ⊑ g →
      ∃ g'', g.1.at' q = some g'' ∧ g''.root = g'.root := by
    intro g hg hle
    rcases at'_mono q (show Tree.Le gm.1 g.1 from hle) with hn | ⟨e, e', he, he', hee⟩
    · rw [hgq] at hn; exact Option.noConfusion hn
    · have hge : g' = e := by rw [hgq] at he; exact Option.some.inj he
      subst hge
      refine ⟨e', he', ?_⟩
      by_cases hb : g' = Tree.bot
      · -- no member of `G` answers `q` properly, so `e' = ⊥` too
        have he'b : e' = Tree.bot := by
          refine Classical.byContradiction fun hne => ?_
          obtain ⟨w, hw, ew, hew, hewne⟩ := hcov q hql ⟨g, hg, e', he', hne⟩
          rcases at'_mono q (show Tree.Le w.1 gm.1 from hub w hw) with
            hn | ⟨a, b, ha, hb', hab⟩
          · rw [hew] at hn; exact Option.noConfusion hn
          · have h1 : ew = a := by rw [hew] at ha; exact Option.some.inj ha
            have h2 : g' = b := by rw [hgq] at hb'; exact Option.some.inj hb'
            subst h1
            rw [← h2, hb] at hab
            exact hewne (Tree.eq_bot_of_le_bot hab)
        rw [he'b, hb]
      · exact Tree.root_of_le hee hb
  -- the context determined by the separating path
  have hpath : q.LegalIn Ctx.empty := legalPath_of_TreeOk q Ctx.empty f₀ f' hf hfq hf'ne
  have hco : q.Coherent := QueryOk.coherent (Query.queryOk_of_legalIn Ctx.empty q hpath)
  have hd₁ : TreeOk Ctx.empty (q.ctx ⟨0, Nat.succ_pos _⟩) :=
    TreeOk_ctxFrom q Ctx.empty hpath (fun _ => TreeOk.leaf _ _) _
  have hab₁ : RespCtx.Above q.ctxList ⟨0, Nat.succ_pos _⟩ (q.ctx ⟨0, Nat.succ_pos _⟩) :=
    Ctx.above_ctxFrom q Ctx.empty hpath _
  -- the separating argument
  obtain ⟨d, hdok, hdle, hsep⟩ := lemma_4_16_separate q.ctx hd₁ f' g'
    (TreeOk_at' q Ctx.empty f₀ f' hf hfq) (TreeOk_at' q Ctx.empty gm.1 g' gm.2 hgq)
    hnle hroot
  refine ⟨d, hdok, fun g hg hcon => ?_⟩
  -- pass to an upper bound of `g` and `gm` in `G`
  obtain ⟨g₁, hg₁, hleg, hlegm⟩ := G.directed' g gm hg hgm
  have hcon₁ : Tree.Le (apply0 f₀ d) (apply0 g₁.1 d) :=
    Tree.Le.trans hcon (apply0_mono_left (show Tree.Le g.1 g₁.1 from hleg) d)
  obtain ⟨g'', hg''q, hg''root⟩ := hstable g₁ hg₁ hlegm
  -- Lemma 4.14 transports the disagreement to `shift₁ q`
  have habd : RespCtx.Above q.ctxList ⟨0, Nat.succ_pos _⟩ d :=
    fun r hr => Tree.Le.trans (hab₁ r hr) hdle
  have h14f := lemma_4_14 q f₀ f' d hco hfq habd
  have h14g := lemma_4_14 q g₁.1 g'' d hco hg''q habd
  rcases at'_mono q.shift1 hcon₁ with hn | ⟨e, e', he, he', hee⟩
  · rw [h14f] at hn; exact Option.noConfusion hn
  · have h1 : apply0 f' d = e := Option.some.inj (h14f.symm.trans he)
    have h2 : apply0 g'' d = e' := Option.some.inj (h14g.symm.trans he')
    exact hsep g'' hg''root (h1 ▸ h2 ▸ hee)

/-- The ideal-completion form of Lemma 4.16, i.e. the remaining step of
**Theorem 4.11**: `apply (F, ·) ⊑ apply (G, ·)` pointwise forces `F ⊑ G` in
`T_{σ→τ}`.

Given a finite `f₀ ∈ F` not in `G`, `uniform_separation` produces one finite
argument `d` on which `f₀` disagrees with every member of `G`; applying the
hypothesis at the principal ideal of `d` then exhibits a member of `G` it must
agree with. -/
theorem orderExtensional_T {σ τ : Ty} (F G : T (σ ⇒ τ))
    (h : ∀ E : T σ, applyT F E ⊑ applyT G E) : F ⊑ G := by
  intro f₀ hf₀
  refine Classical.byContradiction fun hnot => ?_
  have hnotG : ∀ g : D (σ ⇒ τ), g ∈ G → ¬ Tree.Le f₀.1 g.1 := fun g hg hle =>
    hnot (G.downward f₀ g hle hg)
  obtain ⟨d, hdok, hsep⟩ := uniform_separation f₀.1 f₀.2 G hnotG
  -- apply both sides to the principal ideal of `d`
  have hc : applyD f₀ ⟨d, hdok⟩ ∈ applyT F (Ideal.principal ⟨d, hdok⟩) :=
    ⟨f₀, hf₀, ⟨d, hdok⟩, Ideal.mem_principal.mpr (Po.le_refl _), Po.le_refl _⟩
  obtain ⟨g, hg, e, he, hle⟩ := h (Ideal.principal ⟨d, hdok⟩) _ hc
  refine hsep g hg ?_
  exact Tree.Le.trans (show Tree.Le (apply0 f₀.1 d) (apply0 g.1 e.1) from hle)
    (apply0_mono_right g.1 (show Tree.Le e.1 d from he))

/-- **Theorem 4.11.**  *`T` is extensional and order-extensional.*

"Since extensionality is obviously implied by order-extensionality, we will only
prove the second claim." -/
theorem theorem_4_11 :
    (∀ (σ τ : Ty) (F G : T (σ ⇒ τ)), (∀ E : T σ, applyT F E ⊑ applyT G E) → F ⊑ G) ∧
    (∀ (σ τ : Ty) (F G : T (σ ⇒ τ)), (∀ E : T σ, applyT F E = applyT G E) → F = G) := by
  refine ⟨fun σ τ F G h => orderExtensional_T F G h, fun σ τ F G h => ?_⟩
  exact Po.le_antisymm
    (orderExtensional_T F G fun E => (h E) ▸ Po.le_refl _)
    (orderExtensional_T G F fun E => (h E) ▸ Po.le_refl _)

/-! ## Definition 4.17 and Corollary 4.18 -/

/-- **Definition 4.17** (`F_{σ→τ}`).

"For each `f` in `T_{σ→τ}`, let `fun (f)` denote the function
`λ x : T_σ . apply (f, x)`.  The domain `F_{σ→τ}` is the set
`{fun (f) | f ∈ T_{σ→τ}}` under the pointwise ordering on functions." -/
noncomputable def funOf {σ τ : Ty} (f : T (σ ⇒ τ)) : T σ → T τ := fun x => applyT f x

/-- The carrier of `F_{σ→τ}` (Definition 4.17). -/
def FunDom (σ τ : Ty) : Set (T σ → T τ) := Set.range (funOf (σ := σ) (τ := τ))

/-- The pointwise ordering on `F_{σ→τ}` (Definition 4.17). -/
def FunLe {σ τ : Ty} (f g : T σ → T τ) : Prop := ∀ x, f x ⊑ g x

/-- **Corollary 4.18.**  *`T_{σ→τ}` is isomorphic to `F_{σ→τ}`.*

`funOf` is monotone, reflects the order, and is onto `F_{σ→τ}`; hence it is an
order isomorphism.  Injectivity is the extensionality half of Theorem 4.11. -/
theorem corollary_4_18 {σ τ : Ty} :
    (∀ f g : T (σ ⇒ τ), f ⊑ g → FunLe (funOf f) (funOf g)) ∧
    (∀ f g : T (σ ⇒ τ), FunLe (funOf f) (funOf g) → f ⊑ g) ∧
    (∀ f g : T (σ ⇒ τ), funOf f = funOf g → f = g) ∧
    (∀ h, h ∈ FunDom σ τ → ∃ f : T (σ ⇒ τ), funOf f = h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- monotonicity of `apply` in its first argument
    intro f g hfg x a
    rintro ⟨d, hd, e, he, ha⟩
    exact ⟨d, hfg d hd, e, he, ha⟩
  · intro f g h; exact orderExtensional_T f g h
  · intro f g h
    have hE : ∀ E : T σ, applyT f E = applyT g E := fun E => congrFun h E
    exact Po.le_antisymm
      (orderExtensional_T f g fun E => (hE E) ▸ Po.le_refl _)
      (orderExtensional_T g f fun E => (hE E) ▸ Po.le_refl _)
  · rintro h ⟨f, rfl⟩; exact ⟨f, rfl⟩

end FA
