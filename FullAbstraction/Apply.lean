/-
# Application and extensionality (§4.2)

Formalises **Definition 4.9** (`apply`), **Definition 4.17** (`F_{σ→τ}` and
`fun`), and states **Lemma 4.7**, **Claim 4.8**, **Theorem 4.11**,
**Lemma 4.14**, **Corollary 4.15**, **Lemma 4.16** and **Corollary 4.18**.
-/
import FullAbstraction.Trees

namespace FA

open Po

namespace Resp
variable {σ : Ty}

/-- "Every response `r` of type `σ` is a finite tree in `D_σ`" (§4.1). -/
noncomputable def toTree : Resp σ → Tree σ
  | .ans n => .leaf (.num n)
  | .node i p => .node i p (fun _ => Tree.bot)
  | .step i q r rest => .node i q (fun s => if s = r then rest.toTree else Tree.bot)

end Resp

namespace Query
variable {σ : Ty}

/-- "Every query `q` of type `σ` becomes an element of `D_σ` if we replace `?`
by `⊥`.  For the sake of brevity, we will abbreviate the path `q[?/⊥]` by the
symbol `q`" (§4.1). -/
noncomputable def toTree (q : Query σ) : Tree σ := q.substTree Tree.bot

end Query

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

/-- Iterated application `apply (f, d₁, …, dₖ)`, used from Corollary 4.15 on. -/
noncomputable def apply0s {τ : Ty} : ∀ (l : List Ty), Tree (l.foldr Ty.arrow τ) →
    ((i : Fin l.length) → Tree (l[i.val]'i.isLt)) → Tree τ
  | [], f, _ => f
  | a :: l, f, ds =>
      apply0s l (apply0 f (ds ⟨0, Nat.succ_pos _⟩))
        (fun i => ds ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-! ### Well-definedness obligations of Definition 4.9

"It is easy to show that `apply₀` produces a well-defined output in `D_τ(γ')`
… In addition, it is straightforward to check that … the set
`{apply₀ (f', d') | f' ⊑ f, d' ⊑ d}` is directed, implying that it has a least
upper bound.  Hence, `apply` is a well-defined, continuous function from pairs
of trees to trees." -/

/-- Shifting a tree context by one argument: `γ'(i) = γ(i+1)`
(Definition 4.9). -/
def Ctx.shift {a τ : Ty} (γ : Ctx (a ⇒ τ)) : Ctx τ :=
  γ.filterMap fun x =>
    match x with
    | ⟨⟨0, _⟩, _⟩ => none
    | ⟨⟨i + 1, h⟩, r⟩ => some ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, r⟩

/-- `apply₀` maps `D_{σ→τ}(γ) × D_σ` into `D_τ(γ')` (Definition 4.9). -/
theorem apply0_ok {σ τ : Ty} {γ : Ctx (σ ⇒ τ)} {f : Tree (σ ⇒ τ)} {d : Tree σ}
    (hf : TreeOk γ f) (hd : TreeOk ([] : Ctx σ) d) :
    TreeOk γ.shift (apply0 f d) := by
  sorry

/-- `apply₀` is monotone in its first argument. -/
theorem apply0_mono_left {σ τ : Ty} {f f' : Tree (σ ⇒ τ)} (h : f ⊑ f') (d : Tree σ) :
    apply0 f d ⊑ apply0 f' d := by
  sorry

/-- `apply₀` is monotone in its second argument. -/
theorem apply0_mono_right {σ τ : Ty} (f : Tree (σ ⇒ τ)) {d d' : Tree σ} (h : d ⊑ d') :
    apply0 f d ⊑ apply0 f d' := by
  sorry

/-- `apply₀` restricted to the finitary bases. -/
noncomputable def applyD {σ τ : Ty} (f : D (σ ⇒ τ)) (d : D σ) : D τ :=
  ⟨apply0 f.1 d.1, by
    have h := apply0_ok f.2 d.2
    simpa [Ctx.shift] using h⟩

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

/-! ## Lemma 4.7 and Claim 4.8 -/

/-- **Claim 4.8.**  *For `d ∈ D_σ`,
`d = ⊔ {q[?/a] | q ∈ Q_σ, q[?/a] ⊑ d, a ∈ ℕ^E_⊥}`.*

The set of single-branch approximations of `d` obtained by substituting a leaf
value at the end of a valid query. -/
def claim_4_8_approx {σ : Ty} (d : Tree σ) : Set (Tree σ) :=
  fun t => ∃ (q : Query σ) (a : Val), t = q.substTree (.leaf a) ∧ t ⊑ d

/-- **Claim 4.8.** -/
theorem claim_4_8 {σ : Ty} (d : Tree σ) : IsLUB (claim_4_8_approx d) d := by
  sorry

/-- **Lemma 4.7.**  *For `f, g ∈ D_σ`, `f ⋢ g` implies that there is a query `p`
such that `f @ p` and `g @ p` are both defined, `f @ p ⋢ g @ p`, and the
subtrees `f @ p` and `g @ p` are immediately incomparable.* -/
theorem lemma_4_7 {σ : Ty} (f g : Tree σ) (h : ¬ f ⊑ g) :
    ∃ (p : Query σ) (f' g' : Tree σ),
      f.at' p = some f' ∧ g.at' p = some g' ∧ ¬ f' ⊑ g' ∧ Tree.ImmIncomparable f' g' := by
  sorry

/-! ## Lemma 4.14, Corollary 4.15 -/

/-- "`d₁ ⊒ ⊔ γ(i)`": `d₁` is an upper bound of the responses that `γ` records
about argument `i`.  Stating the hypothesis this way avoids presupposing that
the least upper bound exists. -/
def Ctx.Above {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity) (d : Tree (σ.arg i)) : Prop :=
  ∀ r, r ∈ γ.at' i → r.toTree ⊑ d

/-- **Lemma 4.14.**  *Let `d ∈ D_σ`, let `q ∈ Q_σ` be a query that determines the
context `q̂`, and let `e` be a subtree in `D_σ(q̂)`.  If `d @ q = e` and
`d₁ ⊒ ⊔ q̂(1)`, then `apply (d, d₁) @ shift₁ (q) = apply (e, d₁)`.* -/
theorem lemma_4_14 {a τ : Ty} (d : Tree (a ⇒ τ)) (q : Query (a ⇒ τ)) (e : Tree (a ⇒ τ))
    (d₁ : Tree a)
    (hq : d.at' q = some e)
    (hd₁ : Ctx.Above q.ctx ⟨0, Nat.succ_pos _⟩ d₁) :
    (apply0 d d₁).at' q.shift1 = some (apply0 e d₁) := by
  sorry

/-- **Corollary 4.15.**  *Let `σ = σ₁ → … → σₖ → o`, let `q ∈ Q_σ` be a query
determining the context `q̂`, and let `e` be a subtree in `D_σ(q̂)`.  If
`d ⊒ q[?/e]` and `dᵢ ⊒ ⊔ q̂(i)` for `1 ≤ i ≤ k`, then
`apply (d, d₁, …, dₖ) = apply (q[?/e], d₁, …, dₖ) = apply (e, d₁, …, dₖ)`.* -/
theorem corollary_4_15 {a τ : Ty} (q : Query (a ⇒ τ)) (e d : Tree (a ⇒ τ)) (d₁ : Tree a)
    (hd : q.substTree e ⊑ d)
    (hd₁ : Ctx.Above q.ctx ⟨0, Nat.succ_pos _⟩ d₁) :
    apply0 d d₁ = apply0 (q.substTree e) d₁ ∧ apply0 (q.substTree e) d₁ = apply0 e d₁ := by
  sorry

/-! ## Lemma 4.16, Theorem 4.11 -/

/-- **Lemma 4.16.**  *Let `f, g` be elements in `D_{σ→τ}`.  If for all finite
`d ∈ D_σ`, `apply (f, d) ⊑ apply (g, d)`, then `f ⊑ g`.* -/
theorem lemma_4_16 {σ τ : Ty} (f g : Tree (σ ⇒ τ))
    (h : ∀ d : Tree σ, apply0 f d ⊑ apply0 g d) : f ⊑ g := by
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
