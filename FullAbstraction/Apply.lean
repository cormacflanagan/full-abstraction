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

/-- Legal responses are responses to the query they answer. -/
theorem qry_of_legalResp {σ : Ty} {q : Query σ} {r : Resp σ} (h : LegalResp q r) :
    r.qry = q := by
  cases h with
  | num q n => exact Query.qry_substAns q (.num n)
  | node q i p _ => exact Query.qry_substAns q (.node i p)

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

/-- `γ'` is the **shift** of `γ` (Definition 4.9: `γ'(i) = γ(i+1)`): it records
about argument `i` exactly what `γ` records about argument `i + 1`. -/
def Ctx.IsShift {a τ : Ty} (γ : Ctx (a ⇒ τ)) (γ' : Ctx τ) : Prop :=
  ∀ (i : Fin τ.arity) (h : i.val + 1 < (a ⇒ τ).arity) (r : Resp (τ.arg i)),
    (⟨i, r⟩ : (j : Fin τ.arity) × Resp (τ.arg j)) ∈ γ' ↔
    (⟨⟨i.val + 1, h⟩, r⟩ : (j : Fin (a ⇒ τ).arity) × Resp ((a ⇒ τ).arg j)) ∈ γ

/-- Comparing indexed pairs before and after the shift. -/
theorem shiftSigma_eq_iff {a τ : Ty} (i k : Fin τ.arity)
    (hi : i.val + 1 < (a ⇒ τ).arity) (hk : k.val + 1 < (a ⇒ τ).arity)
    (r : Resp (τ.arg i)) (s : Resp (τ.arg k)) :
    ((⟨i, r⟩ : (j : Fin τ.arity) × Resp (τ.arg j)) = ⟨k, s⟩) ↔
    ((⟨⟨i.val + 1, hi⟩, r⟩ : (j : Fin (a ⇒ τ).arity) × Resp ((a ⇒ τ).arg j))
      = ⟨⟨k.val + 1, hk⟩, s⟩) := by
  constructor
  · intro h
    have h1 : i = k := congrArg Sigma.fst h
    subst h1
    have h2 : r = s := by injection h
    subst h2
    rfl
  · intro h
    have h1 : (⟨i.val + 1, hi⟩ : Fin (a ⇒ τ).arity) = ⟨k.val + 1, hk⟩ := congrArg Sigma.fst h
    have h2 : i = k := by
      apply Fin.ext
      have hv := congrArg Fin.val h1
      simpa using hv
    subst h2
    have h3 : r = s := by injection h
    subst h3
    rfl

/-- The empty context is its own shift. -/
theorem Ctx.isShift_nil {a τ : Ty} : Ctx.IsShift ([] : Ctx (a ⇒ τ)) ([] : Ctx τ) := by
  intro i h r
  constructor <;> intro hm <;> exact absurd hm (by simp)

/-- Extending both contexts at corresponding indices preserves the shift
relation. -/
theorem Ctx.isShift_cons {a τ : Ty} {γ : Ctx (a ⇒ τ)} {γ' : Ctx τ}
    (hs : Ctx.IsShift γ γ') (k : Fin τ.arity) (hk : k.val + 1 < (a ⇒ τ).arity)
    (s : Resp (τ.arg k)) :
    Ctx.IsShift (γ.cons ⟨k.val + 1, hk⟩ s) (γ'.cons k s) := by
  intro i h r
  simp only [Ctx.cons, List.mem_cons]
  rw [hs i h r, shiftSigma_eq_iff i k h hk r s]

/-- Recording a response about the *first* argument does not change the shift. -/
theorem Ctx.isShift_cons_zero {a τ : Ty} {γ : Ctx (a ⇒ τ)} {γ' : Ctx τ}
    (hs : Ctx.IsShift γ γ') (h0 : 0 < (a ⇒ τ).arity) (s : Resp ((a ⇒ τ).arg ⟨0, h0⟩)) :
    Ctx.IsShift (γ.cons ⟨0, h0⟩ s) γ' := by
  intro i h r
  rw [hs i h r]
  simp only [Ctx.cons, List.mem_cons]
  constructor
  · exact fun hm => Or.inr hm
  · rintro (heq | hm)
    · exact absurd (congrArg (fun x => x.1.val) heq) (by simp)
    · exact hm

/-- Shifted contexts record the same responses. -/
theorem Ctx.at'_of_isShift {a τ : Ty} {γ : Ctx (a ⇒ τ)} {γ' : Ctx τ}
    (hs : Ctx.IsShift γ γ') (i : Fin τ.arity) (h : i.val + 1 < (a ⇒ τ).arity) :
    γ'.at' i = γ.at' ⟨i.val + 1, h⟩ :=
  Set.ext fun r => hs i h r

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
      · rw [Ctx.at'_of_isShift hs ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hk]; exact hq
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
  ⟨apply0 f.1 d.1, apply0_ok f.1 [] [] d.1 f.2 Ctx.isShift_nil⟩

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
def Ctx.Above {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity) (d : Tree (σ.arg i)) : Prop :=
  ∀ r, r ∈ γ.at' i → r.toTree ⊑ d

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
    q.Coherent → d.at' q = some e → Ctx.Above q.ctx ⟨0, Nat.succ_pos _⟩ d₁ →
    (apply0 d d₁).at' q.shift1 = some (apply0 e d₁)
  | _, _, .hole, d, e, _, _, hq, _ => by
      have hde : d = e := by injection hq
      subst hde
      simp only [Query.shift1, Tree.at'_hole]
  | a, τ, .step i p r rest, d, e, d₁, hco, hq, hab => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      obtain ⟨hcr, hco'⟩ := hco
      have habTail : Ctx.Above rest.ctx ⟨0, Nat.succ_pos _⟩ d₁ := fun s hs =>
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
    (⟨i, r⟩ : (j : Fin τ.arity) × Resp (τ.arg j)) ∈ q.shift1.ctx →
    (⟨⟨i.val + 1, hi⟩, r⟩ : (j : Fin (a ⇒ τ).arity) × Resp ((a ⇒ τ).arg j)) ∈ q.ctx
  | _, _, .hole, i, hi, r, hmem => by
      rw [show (Query.hole : Query (_ ⇒ _)).shift1 = Query.hole by
        simp only [Query.shift1]] at hmem
      exact absurd hmem (by simp [Query.ctx])
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
    q.Coherent → d.at' q = some e → (∀ i, Ctx.Above q.ctx i (ds i)) →
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
          Ctx.Above q.shift1.ctx i (ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by
        intro i r hr
        exact hab ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ r
          (mem_ctx_shift1 q i (Nat.succ_lt_succ i.isLt) r hr)
      show applyArgs τ (apply0 d (ds ⟨0, Nat.succ_pos _⟩)) _
          = applyArgs τ (apply0 e (ds ⟨0, Nat.succ_pos _⟩)) _
      exact applyArgs_at_query τ q.shift1 _ _ _ (shift1_coherent q hco) h14 habs

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
    (hab : ∀ i, Ctx.Above q.ctx i (ds i)) :
    applyArgs σ d ds = applyArgs σ (q.substTree e) ds ∧
    applyArgs σ (q.substTree e) ds = applyArgs σ e ds := by
  have h₂ : applyArgs σ (q.substTree e) ds = applyArgs σ e ds :=
    applyArgs_at_query σ q (q.substTree e) e ds hco (at'_substTree q e) hab
  exact ⟨by rw [applyArgs_at_query σ q d e ds hco hd hab, h₂], h₂⟩

/-- The half of Corollary 4.15 the paper invokes: a path carrying `e` at its
marker applies exactly like `e`. -/
theorem corollary_4_15_path (σ : Ty) (q : Query σ) (e : Tree σ)
    (ds : (i : Fin σ.arity) → Tree (σ.arg i))
    (hco : q.Coherent) (hab : ∀ i, Ctx.Above q.ctx i (ds i)) :
    applyArgs σ (q.substTree e) ds = applyArgs σ e ds :=
  applyArgs_at_query σ q (q.substTree e) e ds hco (at'_substTree q e) hab

/-! ## Lemma 4.16, Theorem 4.11 -/

/-- **Lemma 4.16.**  *Let `f, g` be elements in `D_{σ→τ}`.  If for all finite
`d ∈ D_σ`, `apply (f, d) ⊑ apply (g, d)`, then `f ⊑ g`.*

The hypotheses `TreeOk [] f` and `TreeOk [] g` render "`f, g ∈ D_{σ→τ}`" and are
*not* removable.  The paper's proof separates `f` from `g` at a position where
their subtrees are immediately incomparable (Lemma 4.7) by feeding the argument
a tree that answers one of the two competing queries with `error₁` and the other
with `error₂`.  That the two queries can be answered independently is exactly
Definition 4.2's legality condition — a legal query never re-probes a node the
context has already answered — so without legality no separating argument need
exist. -/
theorem lemma_4_16 {σ τ : Ty} (f g : Tree (σ ⇒ τ))
    (hf : TreeOk [] f) (hg : TreeOk [] g)
    (h : ∀ d : Tree σ, TreeOk [] d → apply0 f d ⊑ apply0 g d) : f ⊑ g := by
  sorry

/-- Order-extensionality at the level of the ideal completions `T_σ`, which is
what Theorem 4.11 asserts. -/
theorem orderExtensional_T {σ τ : Ty} (F G : T (σ ⇒ τ))
    (h : ∀ E : T σ, applyT F E ⊑ applyT G E) : F ⊑ G := by
  sorry

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
