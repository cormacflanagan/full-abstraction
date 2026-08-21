/-
# The tree domains (§4.1)

Formalises **Definition 4.2** — the finitary bases `D_σ` together with the tree
contexts `C_σ`, the paths `P_σ`, the queries `Q_σ`, the responses `R_σ`, the
legal-query and legal-response functions `𝒬_σ` and `ℛ_σ`, and the auxiliary
operations `q[?/x]` and `r : f` — as well as **Definition 4.5** (the `@`
operator, valid queries, query prefixes), **Definition 4.6** (`root`,
immediately incomparable subtrees), **Definition 4.12** (the tree context
determined by a query) and **Definition 4.13** (`shift₁`).

**Lemma 4.3** (`D_σ` is a finitary basis) is stated at the end of the file.

## Encoding

The paper defines paths as trees with a single branch (§4.1, footnote 6).  A
path of type `σ` is therefore a finite sequence of *steps* `⟨i, q, r⟩` — "probe
argument `i` with the query `q`, receive the response `r`" — terminated by a
leaf.  The terminating leaf distinguishes the three kinds of path:

* a **query** (`Q_σ = P_σ(∅, {?})`) ends in the marker `?`;
* a **response** (`R_σ = P_σ(∅, ℕ_⊥) − {⊥}`) ends either in a *final answer*
  `n ∈ ℕ` or in an *intermediate answer* `⟨i, p, ⊥⟩`, i.e. an unexplored node.

We take this as the definition of `Query` and `Resp`, which makes the recursion
of Definition 4.2 into a mutual inductive family indexed by `Ty`.
-/
import FullAbstraction.Order
import FullAbstraction.Types

namespace FA

open Po

/-! ## The ground domain `ℕ^E_⊥` (Definition 4.2, base case) -/

/-- `D_o = ℕ^E_⊥ = ℕ ∪ E` where `E = {⊥, error₁, error₂}` (Definition 4.2). -/
inductive Val where
  /-- The divergent computation `⊥`. -/
  | bot : Val
  /-- `error₁` (`b = true`) and `error₂` (`b = false`). -/
  | err : Bool → Val
  /-- A natural number answer. -/
  | num : Nat → Val
  deriving DecidableEq, Repr

/-- `E = {⊥, error₁, error₂}`, the *improper* answers (§4.2, case 2 of `apply`). -/
def Val.isImproper : Val → Bool
  | .num _ => false
  | _ => true

/-- "`⊥` approximates all other elements, and the rest of the elements are
mutually incomparable" (Definition 4.2, base case). -/
inductive Val.Le : Val → Val → Prop where
  | bot (v : Val) : Val.Le .bot v
  | rfl (v : Val) : Val.Le v v

instance : Po Val where
  le := Val.Le
  le_refl := Val.Le.rfl
  le_trans := by
    rintro a b c (_ | _) h
    · exact Val.Le.bot _
    · exact h
  le_antisymm := by
    rintro a b (_ | _) h
    · cases h with
      | bot => rfl
      | rfl => rfl
    · rfl

/-! ## Queries and responses (Definition 4.2, *Finite Paths*) -/

mutual
/-- `Q_σ`, the set of **queries**: paths ending in the marker `?`
(Definition 4.2, *Queries*). -/
inductive Query : Ty → Type where
  /-- The initial query `?`. -/
  | hole {σ : Ty} : Query σ
  /-- `⟨i, q, ⟨r, rest⟩⟩`: probe argument `i` with `q`, get `r`, continue. -/
  | step {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i)) (r : Resp (σ.arg i))
      (rest : Query σ) : Query σ
/-- `R_σ`, the set of **responses**: paths ending in a final answer `n ∈ ℕ` or
in an intermediate answer `⟨i, p, ⊥⟩` (Definition 4.2, *Responses*). -/
inductive Resp : Ty → Type where
  /-- A final answer `n ∈ ℕ`. -/
  | ans {σ : Ty} (n : Nat) : Resp σ
  /-- An intermediate answer: the unexplored node `⟨i, p, ⊥⟩`. -/
  | node {σ : Ty} (i : Fin σ.arity) (p : Query (σ.arg i)) : Resp σ
  /-- A step, as for queries. -/
  | step {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i)) (r : Resp (σ.arg i))
      (rest : Resp σ) : Resp σ
end

/-- Equality of queries and responses is decidable; we only ever need it
classically. -/
noncomputable instance {σ : Ty} : DecidableEq (Query σ) :=
  fun a b => Classical.propDecidable (a = b)
noncomputable instance {σ : Ty} : DecidableEq (Resp σ) :=
  fun a b => Classical.propDecidable (a = b)

/-- A single step `⟨i, q, r⟩` of a path. -/
abbrev PStep (σ : Ty) : Type := (i : Fin σ.arity) × Query (σ.arg i) × Resp (σ.arg i)

/-- A node value `⟨i, q⟩` (Definition 4.6: "We sometimes refer to the value
`⟨i,q⟩` at a node `⟨i,q,f⟩` as a node"). -/
abbrev NodeVal (σ : Ty) : Type := (i : Fin σ.arity) × Query (σ.arg i)

noncomputable instance {σ : Ty} : DecidableEq (NodeVal σ) :=
  fun a b => Classical.propDecidable (a = b)

/-- The answer part of a response: a final answer or an intermediate one.  This
is the `x` of the substitution `q[?/x]` (Definition 4.2). -/
inductive RAns (σ : Ty) : Type where
  | num (n : Nat) : RAns σ
  | node (i : Fin σ.arity) (p : Query (σ.arg i)) : RAns σ

namespace Query
variable {σ : Ty}

/-- `q[?/x]`: replace the terminating `?` of the query `q` by the answer `x`,
producing a response (Definition 4.2, *Auxiliary functions*). -/
def substAns : Query σ → RAns σ → Resp σ
  | .hole, .num n => .ans n
  | .hole, .node i p => .node i p
  | .step i q r rest, x => .step i q r (rest.substAns x)

/-- `q̂`, the **tree context determined by the query `q`**
(Definition 4.12): `R(?, γ) = γ` and `R(⟨i,p,⟨r,q'⟩⟩, γ) = R(q', γ ∪ {⟨i,r⟩})`. -/
def ctx : Query σ → List ((i : Fin σ.arity) × Resp (σ.arg i))
  | .hole => []
  | .step i _ r rest => ⟨i, r⟩ :: rest.ctx

/-- The length of a query, i.e. the number of nodes it visits. -/
def length : Query σ → Nat
  | .hole => 0
  | .step _ _ _ rest => rest.length + 1

end Query

/-- A **tree context** `γ ∈ C_σ`: "a relation associating argument indices with
responses; we will use it as a set-valued function from indices to sets of
responses" (Definition 4.2, *Contexts*). -/
abbrev Ctx (σ : Ty) : Type := List ((i : Fin σ.arity) × Resp (σ.arg i))

namespace Ctx
variable {σ : Ty}

/-- `γ(i) ≝ {s | ⟨i,s⟩ ∈ γ}` (Definition 4.2, *Contexts*). -/
def at' (γ : Ctx σ) (i : Fin σ.arity) : Set (Resp (σ.arg i)) := fun r => ⟨i, r⟩ ∈ γ

/-- `γ ∪ {⟨i,r⟩}`. -/
def cons (γ : Ctx σ) (i : Fin σ.arity) (r : Resp (σ.arg i)) : Ctx σ := ⟨i, r⟩ :: γ

end Ctx

/-- `q̂(i)`, the set of responses about argument `i` recorded in the tree context
determined by `q`. -/
def Query.ctxAt {σ : Ty} (q : Query σ) (i : Fin σ.arity) : Set (Resp (σ.arg i)) :=
  Ctx.at' q.ctx i

namespace Resp
variable {σ : Ty}

/-- The unexplored node `⟨i,p⟩` at the end of a response, when there is one. -/
def lastNode : Resp σ → Option (NodeVal σ)
  | .ans _ => none
  | .node i p => some ⟨i, p⟩
  | .step _ _ _ rest => rest.lastNode

/-- `r : ⟨r', ?⟩` (Definition 4.2, *Auxiliary functions*): "replaces the empty
branching function `⊥` at the end of a response `r` by the branching function
`f`".  Here `f = ⟨r', ?⟩` maps the response `r'` to the marker `?`, so the
result is the query obtained by extending `r` by exactly one node. -/
def extendHole : Resp σ → ((i : Fin σ.arity) × Resp (σ.arg i)) → Query σ
  | .ans _, _ => .hole
  | .node j p, ⟨i, r'⟩ => if h : i = j then .step j p (h ▸ r') .hole else .hole
  | .step j q s rest, x => .step j q s (rest.extendHole x)

end Resp

/-- `q ⊑ r`: the query `q` is a prefix of the response `r`, i.e. the node that
`q` probes has already been answered by `r` (Definition 4.5, *query prefix*, and
the side condition `¬∃r[q ⊏ r ⊑ ⊔R]` of Definition 4.2, *Legal Queries*). -/
def Query.prefixOf {σ : Ty} : Query σ → Resp σ → Prop
  | .hole, _ => True
  | .step i q r rest, .step j q' r' rest' =>
      (⟨i, q, r⟩ : PStep σ) = ⟨j, q', r'⟩ ∧ rest.prefixOf rest'
  | .step _ _ _ _, .ans _ => False
  | .step _ _ _ _, .node _ _ => False

/-! ## Legal queries and legal responses (Definition 4.2) -/

mutual
/-- `𝒬_σ(R)`: the **legal queries** extending a set `R` of previous responses.

"`𝒬_σ(R) = {?}` if `R = ∅`, and otherwise
`{q ∈ Q_σ | ¬∃r[q ⊏ r ⊑ ⊔R], ∃r ∈ R (q = r : ⟨r',?⟩)}`."

Operationally (§4.1, p. 19): "a query `q` on argument `i` must extend the
approximation tree `⊔γ(i)` for argument `i` by exactly one node".  -/
inductive LegalQuery : {σ : Ty} → Set (Resp σ) → Query σ → Prop where
  /-- `𝒬_σ(∅) = {?}`. -/
  | root {σ : Ty} {R : Set (Resp σ)} :
      ¬ Set.Nonempty R → LegalQuery R .hole
  /-- `q = r : ⟨r', ?⟩` for some `r ∈ R`, and `q` does not re-probe a node that
  `R` has already answered. -/
  | extend {σ : Ty} {R : Set (Resp σ)} {r : Resp σ} {i : Fin σ.arity}
      {p : Query (σ.arg i)} {r' : Resp (σ.arg i)} :
      r ∈ R → r.lastNode = some ⟨i, p⟩ → LegalResp p r' →
      (¬ ∃ s, s ∈ R ∧ (r.extendHole ⟨i, r'⟩).prefixOf s) →
      LegalQuery R (r.extendHole ⟨i, r'⟩)
/-- `ℛ_σ(q)`: the **legal responses** to the query `q`.

"`ℛ_σ(q) = {r ∈ R_σ | r = q[?/a] for a ∈ ℕ or r = q[?/⟨i,p,⊥⟩]}`", where the
intermediate answer `⟨i,p,⊥⟩` must itself be able to "appear at the point
specified by `q` in the selected argument tree", i.e. `p` must be a legal query
in the tree context `q̂` determined by `q`. -/
inductive LegalResp : {σ : Ty} → Query σ → Resp σ → Prop where
  /-- `r = q[?/a]` for a final answer `a ∈ ℕ`. -/
  | num {σ : Ty} (q : Query σ) (n : Nat) : LegalResp q (q.substAns (.num n))
  /-- `r = q[?/⟨i,p,⊥⟩]` for an intermediate answer. -/
  | node {σ : Ty} (q : Query σ) (i : Fin σ.arity) (p : Query (σ.arg i)) :
      LegalQuery (q.ctxAt i) p → LegalResp q (q.substAns (.node i p))
end

/-! ## Trees (Definition 4.2, *Subtrees*) -/

/-- The *preliminary* form of `D_σ` (§4.1): "An element of type `σ` is either a
leaf in `ℕ^E_⊥`, or a triple `⟨i, q, f⟩` consisting of an index `i`, a query
`q ∈ Q_σᵢ`, and a branching function `f` that maps responses in `R_σᵢ` to
simpler trees in `D_σ`."

The legality side conditions of Definition 4.2 are imposed separately by
`TreeOk` below. -/
inductive Tree : Ty → Type where
  /-- A leaf in `ℕ^E_⊥`. -/
  | leaf {σ : Ty} (v : Val) : Tree σ
  /-- The node `⟨i, q, f⟩`. -/
  | node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
      (f : Resp (σ.arg i) → Tree σ) : Tree σ

namespace Tree
variable {σ : Ty}

/-- `⊥`, the everywhere-undefined tree. -/
def bot : Tree σ := .leaf .bot

/-- `error_b`. -/
def err (b : Bool) : Tree σ := .leaf (.err b)

/-- The numeral `⌜n⌝` as a tree. -/
def num (n : Nat) : Tree σ := .leaf (.num n)

/-- The *proper domain* of a branching function is finite: "for all but a finite
set of proper responses in `R_σᵢ`, called the proper domain of `f`, the function
must produce the value `⊥`" (Definition 4.2). -/
def FiniteProperDomain {τ : Ty} (f : Resp τ → Tree σ) : Prop :=
  ∃ l : List (Resp τ), ∀ r, f r ≠ bot → r ∈ l

/-- **Definition 4.6** (*root operator*).

`root a = a` for `a ∈ ℕ_⊥` and `root ⟨i,q,f⟩ = ⟨i,q⟩`. -/
def root : Tree σ → Val ⊕ NodeVal σ
  | .leaf v => .inl v
  | .node i q _ => .inr ⟨i, q⟩

/-- **Definition 4.6** (*immediately incomparable subtrees*).

"Two subtrees `d, e ∈ D_σ(γ)` are immediately incomparable iff
`root(d) ≠ root(e)`." -/
def ImmIncomparable (d e : Tree σ) : Prop := d.root ≠ e.root

/-- "They are immediately comparable iff `root(d) = root(e)`." -/
def ImmComparable (d e : Tree σ) : Prop := d.root = e.root

/-- **Definition 4.2** (*approximation relation*).

"The approximation relation `⊑` for `D_σ(γ)` is the least relation satisfying
the properties `⊥ ⊑ d` for all `d ∈ D_σ(γ)`, and `⟨i,q,f⟩ ⊑ ⟨i,q,g⟩` if
`f(r) ⊑ g(r)` for all `r ∈ ℛ_σᵢ(q)`."

Well-formed trees send illegal responses to `⊥`, so quantifying over *all*
responses is equivalent on `D_σ(γ)` and avoids a dependence on legality. -/
inductive Le : {σ : Ty} → Tree σ → Tree σ → Prop where
  | bot {σ : Ty} (d : Tree σ) : Le bot d
  | leaf {σ : Ty} (v : Val) : Le (.leaf v : Tree σ) (.leaf v)
  | node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i))
      (f g : Resp (σ.arg i) → Tree σ) :
      (∀ r, Le (f r) (g r)) → Le (.node i q f) (.node i q g)

theorem Le.refl : ∀ {σ : Ty} (d : Tree σ), Le d d := by
  intro σ d
  induction d with
  | leaf v => exact Le.leaf v
  | node i q f ih => exact Le.node i q f f ih

theorem Le.trans : ∀ {σ : Ty} {a b c : Tree σ}, Le a b → Le b c → Le a c := by
  intro σ a b c hab
  induction hab generalizing c with
  | bot d => intro _; exact Le.bot _
  | leaf v => intro h; exact h
  | node i q f g _ ih =>
    intro hbc
    cases hbc with
    | node _ _ _ g₂ h₂ => exact Le.node _ _ _ _ fun r => ih r (h₂ r)

theorem Le.antisymm : ∀ {σ : Ty} {a b : Tree σ}, Le a b → Le b a → a = b := by
  intro σ a b hab
  induction hab with
  | bot d =>
    intro h
    cases h with
    | bot => rfl
    | leaf v => rfl
  | leaf v => intro _; rfl
  | node i q f g _ ih =>
    intro hba
    cases hba with
    | node _ _ _ f₂ h₂ => exact congrArg (Tree.node i q) (funext fun r => ih r (h₂ r))

instance : Po (Tree σ) where
  le := Le
  le_refl := Le.refl
  le_trans := Le.trans
  le_antisymm := Le.antisymm

theorem bot_le (d : Tree σ) : (bot : Tree σ) ⊑ d := Le.bot d

/-! ### Definition 4.5: the `@` operator -/

/-- Transport a response along an equality of argument indices. -/
def castResp {σ : Ty} {i j : Fin σ.arity} (h : i = j) (r : Resp (σ.arg i)) :
    Resp (σ.arg j) := h ▸ r

/-- One step of `@`: descend into the branch of `d` selected by the step
`⟨i, q, r⟩`, if `d`'s root is the node `⟨i, q⟩`. -/
noncomputable def stepAt (d : Tree σ) (i : Fin σ.arity) (q : Query (σ.arg i))
    (r : Resp (σ.arg i)) : Option (Tree σ) :=
  match d with
  | .leaf _ => none
  | .node j p f =>
      if h : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩ then
        some (f (castResp (congrArg Sigma.fst h) r))
      else none

/-- **Definition 4.5** (*`@` operator*).

"`d @ q` denotes the subtree identified by the `?` marker in `q`.  More
formally, `@` is the least partial function … satisfying `d @ ? = d` and
`⟨i,p,f⟩ @ ⟨i,p,⟨r,q'⟩⟩ = f(r) @ q'`."

The paper's partiality is rendered by `Option`. -/
noncomputable def at' : Tree σ → Query σ → Option (Tree σ)
  | d, .hole => some d
  | d, .step i q r rest => (d.stepAt i q r).bind fun d' => d'.at' rest

@[inherit_doc] scoped infixl:70 " @@ " => Tree.at'

/-- "If `d @ q` is defined for `d ∈ D_σ` and `q ∈ Q_σ`, then we say `q` is a
**valid query** in `d`" (Definition 4.5). -/
def ValidQuery (d : Tree σ) (q : Query σ) : Prop := ∃ e, d.at' q = some e

/-- "When `d @ q = ⊥`, we say that `q` **probes the perimeter** of `d`"
(Definition 4.5). -/
def ProbesPerimeter (d : Tree σ) (q : Query σ) : Prop := d.at' q = some bot

/-- `q[?/e]`: replace the `?` marker of `q` by the subtree `e`
(Definition 4.2, extended to trees as in Corollary 4.15). -/
noncomputable def _root_.FA.Query.substTree {σ : Ty} :
    Query σ → Tree σ → Tree σ
  | .hole, e => e
  | .step i q r rest, e =>
      .node i q (fun s => if s = r then Query.substTree rest e else bot)

/-! ### Definition 4.13: `shift₁` -/

end Tree

/-- **Definition 4.13** (*`shift₁`*).

"The function `shift₁` from queries of type `σ₁ → … → σₖ → o` to queries of type
`σ₂ → … → σₖ → o` … eliminates queries about the first argument and converts
queries about argument `i+1` into queries about argument `i`."

```
shift₁ (⟨1, p, ⟨r, q⟩⟩)     = shift₁ (q)
shift₁ (⟨i+1, p, ⟨r, q⟩⟩)   = ⟨i, p, ⟨r, shift₁ (q)⟩⟩
shift₁ (?)                  = ?
```

For `σ = σ₁ ⇒ τ` the target type is `τ`, and `τ.arg i = σ.arg (i+1)`, which the
`shiftArg` lemma below records. -/
theorem Ty.shiftArg (a τ : Ty) (i : Fin τ.arity) :
    (a ⇒ τ).arg ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = τ.arg i := rfl

namespace Query

/-- `shift₁` (Definition 4.13). -/
def shift1 {a τ : Ty} : Query (a ⇒ τ) → Query τ
  | .hole => .hole
  | .step ⟨0, _⟩ _ _ rest => shift1 rest
  | .step ⟨i + 1, h⟩ p r rest =>
      .step ⟨i, Nat.lt_of_succ_lt_succ h⟩ p r (shift1 rest)

end Query

/-! ## Definition 4.2: the finitary bases `D_σ(γ)` -/

/-- **Definition 4.2** (*Subtrees*).

"For each context `γ ∈ C_σ`, the partial order `D_σ(γ)` of finite subtrees …

```
D_σ(γ) = ℕ^E_⊥ ∪ {⟨i,q,f⟩ | 1 ≤ i ≤ k, q ∈ 𝒬_σᵢ(γ(i)), {r | f(r) ≠ ⊥} finite,
                              f : r ∈ ℛ_σᵢ(q) ↦ d ∈ D_σ(γ ∪ {⟨i,r⟩})}
```
" -/
inductive TreeOk : {σ : Ty} → Ctx σ → Tree σ → Prop where
  /-- `ℕ^E_⊥ ⊆ D_σ(γ)`. -/
  | leaf {σ : Ty} (γ : Ctx σ) (v : Val) : TreeOk γ (.leaf v)
  /-- `⟨i,q,f⟩ ∈ D_σ(γ)` under the conditions of Definition 4.2. -/
  | node {σ : Ty} (γ : Ctx σ) (i : Fin σ.arity) (q : Query (σ.arg i))
      (f : Resp (σ.arg i) → Tree σ) :
      LegalQuery (γ.at' i) q →
      Tree.FiniteProperDomain f →
      (∀ r, LegalResp q r → TreeOk (γ.cons i r) (f r)) →
      (∀ r, ¬ LegalResp q r → f r = Tree.bot) →
      TreeOk γ (.node i q f)

/-- **Definition 4.2** (*Contexts*).

"The set of tree contexts `C_σ` is the least set of ordered pairs of the form
`{⟨i,r⟩}` … satisfying the closure properties `∅ ∈ C_σ`; and
`γ ∪ {⟨i,r⟩} ∈ C_σ` if `γ ∈ C_σ` and `r ∈ ℛ_σᵢ(q)` for some `q ∈ 𝒬_σᵢ(γ(i))`." -/
inductive CtxOk : {σ : Ty} → Ctx σ → Prop where
  | nil {σ : Ty} : CtxOk ([] : Ctx σ)
  | cons {σ : Ty} {γ : Ctx σ} {i : Fin σ.arity} {q : Query (σ.arg i)}
      {r : Resp (σ.arg i)} :
      CtxOk γ → LegalQuery (γ.at' i) q → LegalResp q r → CtxOk (γ.cons i r)

/-- `D_σ(γ)`, the finite subtrees legal in the context `γ`. -/
def DSub (σ : Ty) (γ : Ctx σ) : Type := { d : Tree σ // TreeOk γ d }

/-- "The partial order `D_σ` of finite trees of type `σ` is defined as
`D_σ(∅)`" (Definition 4.2). -/
abbrev D (σ : Ty) : Type := DSub σ []

namespace DSub
variable {σ : Ty} {γ : Ctx σ}

instance : Po (DSub σ γ) where
  le d e := d.1 ⊑ e.1
  le_refl d := Po.le_refl d.1
  le_trans h₁ h₂ := Po.le_trans h₁ h₂
  le_antisymm h₁ h₂ := Subtype.ext (Po.le_antisymm h₁ h₂)

/-- `⊥ ∈ D_σ(γ)`. -/
def bot : DSub σ γ := ⟨Tree.bot, TreeOk.leaf γ .bot⟩

theorem bot_le (d : DSub σ γ) : bot ⊑ d := Tree.Le.bot d.1

end DSub

/-! ## Lemma 4.3 -/

/-- Every finite bounded subset of `D_σ(γ)` has a least upper bound.

"It is straightforward but tedious to prove that every finite bounded subset of
`D_σ` has a least upper bound" (proof of Lemma 4.3). -/
theorem dsub_lub_of_finite_bounded {σ : Ty} {γ : Ctx σ} (l : List (DSub σ γ))
    (h : Bounded (Set.ofList l)) : ∃ d, IsLUB (Set.ofList l) d := by
  sorry

/-- `D_σ(γ)` is countable: "`D_σ` is countable because every branching function
has a finite proper domain" (proof of Lemma 4.3). -/
theorem dsub_countable {σ : Ty} {γ : Ctx σ} : Countable (DSub σ γ) := by
  sorry

/-- **Lemma 4.3.**  *`D_σ` is a finitary basis.*

"`D_σ` is a partial order because `⊑` is reflexive, anti-symmetric, and
transitive.  `D_σ` is countable because every branching function has a finite
proper domain.  It is straightforward but tedious to prove that every finite
bounded subset of `D_σ` has a least upper bound." -/
noncomputable instance lemma_4_3 {σ : Ty} {γ : Ctx σ} : FinitaryBasis (DSub σ γ) where
  toPo := inferInstance
  elt := DSub.bot
  countable := dsub_countable
  lub_of_finite_bounded := dsub_lub_of_finite_bounded

/-- "As an immediate consequence of this lemma, we conclude that the ideal
completion of `D_σ` is a Scott domain (ω-algebraic bounded-complete cpo). …
The result is the Scott domain designated `T_σ`."  (§4.1, after Lemma 4.3.) -/
abbrev T (σ : Ty) : Type := Ideal (D σ)

/-- The reflexivity, antisymmetry and transitivity half of Lemma 4.3, which is
proved outright. -/
theorem lemma_4_3_partial_order {σ : Ty} {γ : Ctx σ} :
    (∀ d : DSub σ γ, d ⊑ d) ∧
    (∀ d e f : DSub σ γ, d ⊑ e → e ⊑ f → d ⊑ f) ∧
    (∀ d e : DSub σ γ, d ⊑ e → e ⊑ d → d = e) :=
  ⟨Po.le_refl, fun _ _ _ h₁ h₂ => Po.le_trans h₁ h₂, fun _ _ h₁ h₂ => Po.le_antisymm h₁ h₂⟩

end FA
