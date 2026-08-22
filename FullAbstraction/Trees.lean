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

noncomputable instance {σ : Ty} : DecidableEq (PStep σ) :=
  fun a b => Classical.propDecidable (a = b)

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

/-- A **response context**: the literal reading of Definition 4.2's "relation
associating argument indices with responses".

This is the bookkeeping form of a tree context — the list of responses recorded
along a path.  The form used for legality (Definition 4.2, *Subtrees*) is the
equivalent one in which each argument carries the *approximation tree* those
responses determine; see `Ctx` below. -/
abbrev RespCtx (σ : Ty) : Type := List ((i : Fin σ.arity) × Resp (σ.arg i))

namespace RespCtx
variable {σ : Ty}

/-- `γ(i) ≝ {s | ⟨i,s⟩ ∈ γ}` (Definition 4.2, *Contexts*). -/
def at' (γ : RespCtx σ) (i : Fin σ.arity) : Set (Resp (σ.arg i)) := fun r => ⟨i, r⟩ ∈ γ

/-- `γ ∪ {⟨i,r⟩}`. -/
def cons (γ : RespCtx σ) (i : Fin σ.arity) (r : Resp (σ.arg i)) : RespCtx σ :=
  ⟨i, r⟩ :: γ

end RespCtx

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
def ctxList : Query σ → RespCtx σ
  | .hole => []
  | .step i _ r rest => ⟨i, r⟩ :: rest.ctxList

/-- The length of a query, i.e. the number of nodes it visits. -/
def length : Query σ → Nat
  | .hole => 0
  | .step _ _ _ rest => rest.length + 1

end Query


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

/-- A tree is **finitary** when every branching function in it has a finite
proper domain, which is the shape condition of Definition 4.2 with legality
forgotten. -/
inductive Finitary : {σ : Ty} → Tree σ → Prop where
  | leaf {σ : Ty} (v : Val) : Finitary (.leaf v : Tree σ)
  | node {σ : Ty} (i : Fin σ.arity) (q : Query (σ.arg i)) (f : Resp (σ.arg i) → Tree σ) :
      FiniteProperDomain f → (∀ r, Finitary (f r)) → Finitary (.node i q f)

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

noncomputable instance {σ : Ty} : DecidableEq (Tree σ) :=
  fun a b => Classical.propDecidable (a = b)

/-- Transport a response along an equality of argument indices. -/
def castResp {σ : Ty} {i j : Fin σ.arity} (h : i = j) (r : Resp (σ.arg i)) :
    Resp (σ.arg j) := h ▸ r

@[simp] theorem castResp_rfl {σ : Ty} {i : Fin σ.arity} (r : Resp (σ.arg i)) :
    castResp (rfl : i = i) r = r := rfl

/-! ### Joins of bounded trees

The least-upper-bound half of Lemma 4.3 ("It is straightforward but tedious to
prove that every finite bounded subset of `D_σ` has a least upper bound").  Two
trees with a common upper bound have a join, computed branch by branch. -/

/-- The join of two trees.  When they have a common upper bound this is their
least upper bound (`join_spec`); otherwise its value is unconstrained. -/
noncomputable def join {σ : Ty} : Tree σ → Tree σ → Tree σ
  | .leaf .bot, e => e
  | .leaf (.err b), _ => .leaf (.err b)
  | .leaf (.num n), _ => .leaf (.num n)
  | .node i q f, .node j p g =>
      if h : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩ then
        .node i q fun r => join (f r) (g (castResp (congrArg Sigma.fst h) r))
      else .node i q f
  | .node i q f, .leaf _ => .node i q f

@[simp] theorem join_bot_left (e : Tree σ) : join (.leaf .bot : Tree σ) e = e := rfl

@[simp] theorem join_node_leaf (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (v : Val) :
    join (.node i q f) (.leaf v) = .node i q f := by
  cases v <;> rfl

/-- Two nodes with the same node value join branchwise. -/
theorem join_node_self (i : Fin σ.arity) (q : Query (σ.arg i))
    (f g : Resp (σ.arg i) → Tree σ) :
    join (.node i q f) (.node i q g) = .node i q fun r => join (f r) (g r) := by
  show (dite _ _ _) = _
  rw [dif_pos (rfl : (⟨i, q⟩ : NodeVal σ) = ⟨i, q⟩)]
  rfl

@[simp] theorem join_bot_right (d : Tree σ) : join d (bot : Tree σ) = d := by
  cases d with
  | leaf v => cases v <;> rfl
  | node i q f => exact join_node_leaf i q f .bot

theorem join_bot_bot : join (bot : Tree σ) bot = bot := rfl

/-- Two nodes with distinct node values join to the left node. -/
theorem join_node_ne {i j : Fin σ.arity} {q : Query (σ.arg i)} {p : Query (σ.arg j)}
    (f : Resp (σ.arg i) → Tree σ) (g : Resp (σ.arg j) → Tree σ)
    (hEq : ¬ (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩) :
    join (.node i q f) (.node j p g) = .node i q f := by
  show (dite _ _ _) = _
  rw [dif_neg hEq]

/-- **Lemma 4.3**, the least-upper-bound property: two trees with a common upper
bound `t` have `join` as their least upper bound. -/
theorem join_spec : ∀ (d e t : Tree σ), Le d t → Le e t →
    Le d (join d e) ∧ Le e (join d e) ∧ ∀ u, Le d u → Le e u → Le (join d e) u := by
  intro d
  induction d with
  | leaf v =>
    intro e t hd he
    cases v with
    | bot =>
      exact ⟨Le.bot e, Le.refl e, fun _ _ hu => hu⟩
    | err b =>
      cases hd with
      | leaf _ =>
        exact ⟨Le.refl _, he, fun u hu _ => hu⟩
    | num n =>
      cases hd with
      | leaf _ =>
        exact ⟨Le.refl _, he, fun u hu _ => hu⟩
  | node i q f ih =>
    intro e t hd he
    cases hd with
    | node _ _ _ ft hft =>
      cases he with
      | bot =>
        exact ⟨Le.refl _, Le.bot _, fun _ hu _ => hu⟩
      | node _ _ ge _ hge =>
        rw [join_node_self]
        refine ⟨Le.node _ _ _ _ fun r => (ih r (ge r) (ft r) (hft r) (hge r)).1,
          Le.node _ _ _ _ fun r => (ih r (ge r) (ft r) (hft r) (hge r)).2.1, ?_⟩
        intro u hu hu'
        cases hu with
        | node _ _ _ gu hfu =>
          cases hu' with
          | node _ _ _ gu' hgeu =>
            exact Le.node _ _ _ _ fun r =>
              (ih r (ge r) (ft r) (hft r) (hge r)).2.2 (gu r) (hfu r) (hgeu r)

/-- `join` is monotone in its second argument below a common upper bound. -/
theorem join_le_join_right {t d u v : Tree σ} (hd : Le d t) (hu : Le u t)
    (hv : Le v t) (huv : Le u v) : Le (join d u) (join d v) :=
  (join_spec d u t hd hu).2.2 (join d v) (join_spec d v t hd hv).1
    (Le.trans huv (join_spec d v t hd hv).2.1)

/-- **Absorption**: a tree between `d` and `join d u` joins with `u` to
`join d u` itself. -/
theorem join_eq_of_between {t d g u : Tree σ} (hdt : Le d t) (hgt : Le g t)
    (hut : Le u t) (hdg : Le d g) (hgu : Le g (join d u)) : join g u = join d u := by
  have hs1 := join_spec g u t hgt hut
  have hs2 := join_spec d u t hdt hut
  exact Le.antisymm (hs1.2.2 _ hgu hs2.2.1) (hs2.2.2 _ (Le.trans hdg hs1.1) hs1.2.1)

/-! ### Definition 4.5: the `@` operator -/

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

/-- Inversion for `⊑` between two nodes with the same node value. -/
theorem Le_node_inv {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f g : Resp (σ.arg i) → Tree σ} (h : Le (.node i q f) (.node i q g)) :
    ∀ r, Le (f r) (g r) := by
  cases h with | node _ _ _ _ h => exact h

/-- A node is never below a leaf. -/
theorem not_le_leaf {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f : Resp (σ.arg i) → Tree σ} {v : Val} : ¬ Le (.node i q f) (.leaf v) := by
  intro h; cases h

/-- A proper leaf is never below a node. -/
theorem not_leaf_le_node {v : Val} (hv : v ≠ .bot) {i : Fin σ.arity}
    {q : Query (σ.arg i)} {g : Resp (σ.arg i) → Tree σ} :
    ¬ Le (.leaf v : Tree σ) (.node i q g) := by
  intro h; cases h with | bot _ => exact hv rfl

/-- A proper leaf is below only itself. -/
theorem not_leaf_le_leaf {v w : Val} (hv : v ≠ .bot) (hvw : v ≠ w) :
    ¬ Le (.leaf v : Tree σ) (.leaf w) := by
  intro h
  cases h with
  | bot _ => exact hv rfl
  | leaf _ => exact hvw rfl

/-- Nodes with different node values are incomparable. -/
theorem not_node_le_node {i j : Fin σ.arity} {q : Query (σ.arg i)} {q' : Query (σ.arg j)}
    {f : Resp (σ.arg i) → Tree σ} {g : Resp (σ.arg j) → Tree σ}
    (hne : (⟨i, q⟩ : NodeVal σ) ≠ ⟨j, q'⟩) : ¬ Le (.node i q f) (.node j q' g) := by
  intro h; cases h; exact hne rfl

/-- `d ⊑ ⊥` forces `d = ⊥`. -/
theorem eq_bot_of_le_bot {d : Tree σ} (h : Le d bot) : d = bot := by
  cases h with
  | bot _ => rfl
  | leaf v => rfl

/-- The root of a tree is fixed by any proper approximation: comparable trees
share their root as soon as the smaller one is not `⊥`. -/
theorem root_of_le {d e : Tree σ} (h : Le d e) (hd : d ≠ bot) : e.root = d.root := by
  cases h with
  | bot _ => exact absurd rfl hd
  | leaf v => rfl
  | node i q f g _ => rfl

/-- A tree above a node is a node with the same node value. -/
theorem eq_node_of_le {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f : Resp (σ.arg i) → Tree σ} {v : Tree σ} (h : Le (.node i q f) v) :
    ∃ g, v = .node i q g := by
  cases h with | node _ _ _ g _ => exact ⟨g, rfl⟩

/-- Descending into a node along its own query selects the corresponding
branch. -/
theorem stepAt_self (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (r : Resp (σ.arg i)) :
    (Tree.node i q f).stepAt i q r = some (f r) := by
  simp only [Tree.stepAt, dif_pos rfl]
  rfl

@[simp] theorem at'_hole (d : Tree σ) : d.at' .hole = some d := rfl

theorem at'_step_self (i : Fin σ.arity) (q : Query (σ.arg i))
    (f : Resp (σ.arg i) → Tree σ) (r : Resp (σ.arg i)) (rest : Query σ) :
    (Tree.node i q f).at' (.step i q r rest) = (f r).at' rest := by
  simp only [Tree.at', stepAt_self, Option.bind]

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

/-- A query at a type with no argument positions is trivial. -/
theorem Query.eq_hole_of_arity_zero {τ : Ty} (h : τ.arity = 0) :
    ∀ q : Query τ, q = .hole
  | .hole => rfl
  | .step i _ _ _ => absurd (Nat.lt_of_lt_of_eq i.isLt h) (by omega)

/-- "Every query `q` of type `σ` becomes an element of `D_σ` if we replace `?`
by `⊥`.  For the sake of brevity, we will abbreviate the path `q[?/⊥]` by the
symbol `q`" (§4.1). -/
noncomputable def Query.toTree {σ : Ty} (q : Query σ) : Tree σ := q.substTree Tree.bot

/-- "Every response `r` of type `σ` is a finite tree in `D_σ`" (§4.1). -/
noncomputable def Resp.toTree {σ : Ty} : Resp σ → Tree σ
  | .ans n => .leaf (.num n)
  | .node i p => .node i p (fun _ => Tree.bot)
  | .step i q r rest => .node i q (fun s => if s = r then rest.toTree else Tree.bot)

/-! ### Error-free trees

The knowledge trees the `S` combinator accumulates about its arguments are
built exclusively from responses, which contain no `errorᵢ` leaves. -/

/-- No leaf of the tree is an `errorᵢ`. -/
def Tree.ErrFree {σ : Ty} : Tree σ → Prop
  | .leaf v => ∀ b, v ≠ Val.err b
  | .node _ _ f => ∀ r, Tree.ErrFree (f r)

theorem Tree.ErrFree_bot {σ : Ty} : (Tree.bot : Tree σ).ErrFree := by
  simp only [Tree.bot, Tree.ErrFree]
  intro b h
  exact Val.noConfusion h

theorem Tree.ErrFree_leaf_num {σ : Ty} (n : Nat) :
    (Tree.leaf (.num n) : Tree σ).ErrFree := by
  simp only [Tree.ErrFree]
  intro b h
  exact Val.noConfusion h

theorem Tree.ErrFree.not_err {σ : Ty} {b : Bool}
    (h : (Tree.leaf (Val.err b) : Tree σ).ErrFree) : False := by
  simp only [Tree.ErrFree] at h
  exact h b rfl

/-- The join of two error-free trees is error-free. -/
theorem Tree.ErrFree_join {σ : Ty} : ∀ (d e : Tree σ),
    d.ErrFree → e.ErrFree → (Tree.join d e).ErrFree := by
  intro d
  induction d with
  | leaf v =>
    intro e hd he
    cases v with
    | bot => exact he
    | err b => exact absurd hd (fun h => Tree.ErrFree.not_err h)
    | num n => exact hd
  | node i q f ih =>
    intro e hd he
    cases e with
    | leaf v => rw [Tree.join_node_leaf]; exact hd
    | node j p g =>
      by_cases hEq : (⟨i, q⟩ : NodeVal σ) = ⟨j, p⟩
      · have h1 : i = j := congrArg Sigma.fst hEq
        subst h1
        have h2 : q = p := by injection hEq
        subst h2
        rw [Tree.join_node_self]
        simp only [Tree.ErrFree] at hd he ⊢
        exact fun r => ih r (g r) (hd r) (he r)
      · rw [Tree.join_node_ne f g hEq]
        exact hd

/-- Response trees are error-free. -/
theorem Resp.toTree_errFree {σ : Ty} : ∀ r : Resp σ, r.toTree.ErrFree
  | .ans n => by
      simp only [Resp.toTree]
      exact Tree.ErrFree_leaf_num n
  | .node i p => by
      simp only [Resp.toTree, Tree.ErrFree]
      exact fun _ => Tree.ErrFree_bot
  | .step i q r rest => by
      simp only [Resp.toTree, Tree.ErrFree]
      intro s
      by_cases hs : s = r
      · rw [if_pos hs]; exact Resp.toTree_errFree rest
      · rw [if_neg hs]; exact Tree.ErrFree_bot

/-- The path-with-`⊥`-tip tree of a query lies below the tree of any of its
answers. -/
theorem Query.toTree_le_substAns {σ : Ty} : ∀ (q : Query σ) (x : RAns σ),
    Tree.Le q.toTree (q.substAns x).toTree
  | .hole, .num n => Tree.Le.bot _
  | .hole, .node i p => Tree.Le.bot _
  | .step i p r rest, x => by
      simp only [Query.toTree, Query.substTree, Query.substAns, Resp.toTree]
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · rw [if_pos hs, if_pos hs]
        exact Query.toTree_le_substAns rest x
      · rw [if_neg hs, if_neg hs]
        exact Tree.Le.bot _

/-! ## Tree contexts (Definition 4.2, *Contexts*) -/

/-- A **tree context** `γ ∈ C_σ`.

Definition 4.2 introduces a context as "a relation associating argument indices
with responses", used "as a set-valued function from indices to sets of
responses".  But every use a context is put to in that definition is through the
*approximation tree* `⊔γ(i)` those responses determine: the query `q` of a node
`⟨i,q,f⟩` must "extend the approximation tree `⊔γ(i)` for argument `i` by exactly
one node" (§4.1, p. 19).  We therefore record the approximation trees directly —
`γ i` is the tree of type `σᵢ` built from everything the context knows about
argument `i`.

This does not presuppose that `⊔γ(i)` exists, and it makes the two facts the
development needs immediate rather than derived: a legal query addresses a
position that is present in `γ i` but unexplored, and recording a response fills
exactly that position.  (The literal, bookkeeping reading of a context is
`RespCtx` above; it is what the *statement* of Lemma 4.14 uses.) -/
abbrev Ctx (σ : Ty) : Type := (i : Fin σ.arity) → Tree (σ.arg i)

namespace Ctx
variable {σ : Ty}

/-- `∅ ∈ C_σ`: nothing is known about any argument. -/
def empty : Ctx σ := fun _ => Tree.bot

/-- `γ ∪ {⟨i,r⟩} ∈ C_σ`: record the response `r` about argument `i`, i.e. extend
that argument's approximation tree by the path `r` describes. -/
noncomputable def cons (γ : Ctx σ) (i : Fin σ.arity) (r : Resp (σ.arg i)) : Ctx σ :=
  fun j => if h : i = j then Tree.join (γ j) (Tree.castResp h r).toTree else γ j

@[simp] theorem empty_apply (i : Fin σ.arity) : (Ctx.empty : Ctx σ) i = Tree.bot := rfl

@[simp] theorem cons_self (γ : Ctx σ) (i : Fin σ.arity) (r : Resp (σ.arg i)) :
    γ.cons i r i = Tree.join (γ i) r.toTree := by
  show (dite _ _ _) = _
  rw [dif_pos (rfl : i = i)]
  exact rfl

theorem cons_other (γ : Ctx σ) {i j : Fin σ.arity} (r : Resp (σ.arg i)) (h : ¬ i = j) :
    γ.cons i r j = γ j := by
  show (dite _ _ _) = _
  rw [dif_neg h]

end Ctx

namespace Query
variable {σ : Ty}

/-- `R(q, γ)` (Definition 4.12): `R(?, γ) = γ` and
`R(⟨i,p,⟨r,q'⟩⟩, γ) = R(q', γ ∪ {⟨i,r⟩})`. -/
noncomputable def ctxFrom : Query σ → Ctx σ → Ctx σ
  | .hole, γ => γ
  | .step i _ r rest, γ => rest.ctxFrom (γ.cons i r)

/-- `q̂`, the **tree context determined by the query `q`** (Definition 4.12):
`q̂ = R(q, ∅)`. -/
noncomputable def ctx (q : Query σ) : Ctx σ := q.ctxFrom Ctx.empty

end Query

/-! ## Legal queries and legal responses (Definition 4.2) -/

/-- **The responses recorded along a query are themselves legal.**

Definition 4.2's `𝒬_σ(R)` asks for `q = r : ⟨r',?⟩` where `r` is a *recorded*
response and `r' ∈ ℛ_σᵢ(p)` is a *legal* response to the query `p` that the last
step asks.  Following an existing path is not enough: a tree carries `⊥` at the
position reached by answering `p` with an illegal `r'` too, and that position is
not a legal query — nothing legal will ever be written there.

This is the one place where Definition 4.2's recursion genuinely descends into
the argument types, and it descends on `Ty.depth`: a step about argument `i`
constrains a response of type `σᵢ`, whose intermediate answers constrain queries
of type `(σᵢ)ⱼ`.  The condition on an answer is spelled out here rather than
written as `RAns.Ok` because that predicate is defined below in terms of this
one. -/
def QueryOk : (σ : Ty) → Query σ → Prop
  | _, .hole => True
  | σ, .step i p s rest =>
      (∃ x : RAns (σ.arg i), s = p.substAns x ∧
        (match x with
          | .num _ => True
          | .node j p' =>
              (p.ctx j).at' p' = some Tree.bot ∧ QueryOk ((σ.arg i).arg j) p'))
      ∧ QueryOk σ rest
termination_by σ q => (σ.depth, q.length)
decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_trans (Ty.depth_arg_lt _ j) (Ty.depth_arg_lt σ i))
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)

@[simp] theorem QueryOk_hole {σ : Ty} : QueryOk σ .hole := by rw [QueryOk]; trivial

/-- `𝒬_σ(γ(i))`: `q` is a **legal query** about an argument whose approximation
tree is `t`.

"`𝒬_σ(R) = {?}` if `R = ∅`, and otherwise
`{q ∈ Q_σ | ¬∃r[q ⊏ r ⊑ ⊔R], ∃r ∈ R (q = r : ⟨r',?⟩)}`."

Operationally (§4.1, p. 19): "a query `q` on argument `i` must extend the
approximation tree `⊔γ(i)` for argument `i` by exactly one node".  That is the
first conjunct: `t @ q = ⊥` says both that `q` follows only nodes `t` already
contains — so `q` extends `t` — and that the node `q` probes is still
unanswered, which is the side condition `¬∃r[q ⊏ r ⊑ ⊔R]`, i.e. the *probes the
perimeter* condition of Definition 4.5.  The second conjunct is `r' ∈ ℛ_σᵢ(p)`
for each step, as discussed at `QueryOk`.

Two remarks on the paper's phrasing.  First, `¬∃r[q ⊏ r ⊑ ⊔R]` is genuinely
stronger than "`q` is not a prefix of any `s ∈ R`": if `s` answers the node `q`
probes with a *different* response than `q` records, `q` is not a prefix of `s`,
yet `q[?/⊥]` is still strictly below `s` and the query does re-probe an answered
node.  Stating legality against the approximation tree gets this right
automatically.  Second, `⊔R` need not be assumed to exist. -/
def LegalQuery {σ : Ty} (t : Tree σ) (q : Query σ) : Prop :=
  t.at' q = some Tree.bot ∧ QueryOk σ q

/-- `? ∈ 𝒬_σ(∅)`. -/
theorem LegalQuery.root {σ : Ty} : LegalQuery (Tree.bot : Tree σ) .hole :=
  ⟨rfl, QueryOk_hole⟩

/-- `𝒬_σ(∅) = {?}`: in the empty context no query but `?` is legal. -/
theorem LegalQuery.eq_hole_of_bot {σ : Ty} : ∀ {q : Query σ},
    LegalQuery (Tree.bot : Tree σ) q → q = .hole
  | .hole, _ => rfl
  | .step _ _ _ _, h =>
      absurd h.1 (by simp [Tree.at', Tree.stepAt, Tree.bot])

/-- The side condition on the answer `x` of a legal response `q[?/x]`
(Definition 4.2, *Legal Responses*).

A final answer `a ∈ ℕ` is always legal.  An intermediate answer `⟨i,p,⊥⟩` is
legal exactly when `p` can "appear at the point specified by `q` in the selected
argument tree", i.e. when `p` is a legal query about argument `i` in the tree
context `q̂` determined by `q`.  As the paper puts it, "this test reduces to
confirming that the response `q[?/x]` is a well-formed tree (path)". -/
def RAns.Ok' {σ : Ty} (δ : Ctx σ) : RAns σ → Prop
  | .num _ => True
  | .node i p => LegalQuery (δ i) p

/-- `RAns.Ok'` at the context `q̂` determined by `q`. -/
def RAns.Ok {σ : Ty} (q : Query σ) : RAns σ → Prop := RAns.Ok' q.ctx

/-- `ℛ_σ(q)`: the **legal responses** to the query `q`.

"`ℛ_σ(q) = {r ∈ R_σ | r = q[?/a] for a ∈ ℕ or r = q[?/⟨i,p,⊥⟩]}`." -/
def LegalResp {σ : Ty} (q : Query σ) (r : Resp σ) : Prop :=
  ∃ x : RAns σ, r = q.substAns x ∧ RAns.Ok q x

/-- `r = q[?/a]` for a final answer `a ∈ ℕ`. -/
theorem LegalResp.num {σ : Ty} (q : Query σ) (n : Nat) :
    LegalResp q (q.substAns (.num n)) := ⟨.num n, rfl, trivial⟩

/-- `r = q[?/⟨i,p,⊥⟩]` for an intermediate answer. -/
theorem LegalResp.node {σ : Ty} (q : Query σ) (i : Fin σ.arity) (p : Query (σ.arg i))
    (h : LegalQuery (q.ctx i) p) : LegalResp q (q.substAns (.node i p)) :=
  ⟨.node i p, rfl, h⟩

/-- `QueryOk` says exactly that each step of a query records a legal response to
the query that step asks. -/
theorem QueryOk_step {σ : Ty} (i : Fin σ.arity) (p : Query (σ.arg i))
    (s : Resp (σ.arg i)) (rest : Query σ) :
    QueryOk σ (.step i p s rest) ↔ (LegalResp p s ∧ QueryOk σ rest) := by
  rw [QueryOk]
  constructor
  · rintro ⟨⟨x, hx, hox⟩, hrest⟩
    exact ⟨⟨x, hx, by cases x <;> exact hox⟩, hrest⟩
  · rintro ⟨⟨x, hx, hox⟩, hrest⟩
    exact ⟨⟨x, hx, by cases x <;> exact hox⟩, hrest⟩

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
      LegalQuery (γ i) q →
      Tree.FiniteProperDomain f →
      (∀ r, LegalResp q r → TreeOk (γ.cons i r) (f r)) →
      (∀ r, ¬ LegalResp q r → f r = Tree.bot) →
      TreeOk γ (.node i q f)

/-- **Definition 4.2** (*Contexts*).

"The set of tree contexts `C_σ` is the least set of ordered pairs of the form
`{⟨i,r⟩}` … satisfying the closure properties `∅ ∈ C_σ`; and
`γ ∪ {⟨i,r⟩} ∈ C_σ` if `γ ∈ C_σ` and `r ∈ ℛ_σᵢ(q)` for some `q ∈ 𝒬_σᵢ(γ(i))`." -/
inductive CtxOk : {σ : Ty} → Ctx σ → Prop where
  | empty {σ : Ty} : CtxOk (Ctx.empty : Ctx σ)
  | cons {σ : Ty} {γ : Ctx σ} {i : Fin σ.arity} {q : Query (σ.arg i)}
      {r : Resp (σ.arg i)} :
      CtxOk γ → LegalQuery (γ i) q → LegalResp q r → CtxOk (γ.cons i r)

/-- Inversion for `TreeOk` at a node. -/
theorem TreeOk_node_inv {σ : Ty} {γ : Ctx σ} {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f : Resp (σ.arg i) → Tree σ} (h : TreeOk γ (.node i q f)) :
    LegalQuery (γ i) q ∧ Tree.FiniteProperDomain f ∧
    (∀ r, LegalResp q r → TreeOk (γ.cons i r) (f r)) ∧
    (∀ r, ¬ LegalResp q r → f r = Tree.bot) := by
  cases h with
  | node _ _ _ _ hq hfin hsub hnon => exact ⟨hq, hfin, hsub, hnon⟩

/-- Two contexts that know the same about every argument are interchangeable in
`TreeOk`. -/
theorem TreeOk_congr_ctx {σ : Ty} (d : Tree σ) (γ γ' : Ctx σ)
    (hset : ∀ i, γ i = γ' i) (h : TreeOk γ d) : TreeOk γ' d :=
  funext hset ▸ h

/-- The join of two legal subtrees with a common upper bound is legal.  This is
the second half of the least-upper-bound property of Lemma 4.3. -/
theorem TreeOk_join {σ : Ty} : ∀ (d : Tree σ) (γ : Ctx σ) (e t : Tree σ),
    TreeOk γ d → TreeOk γ e → Tree.Le d t → Tree.Le e t → TreeOk γ (Tree.join d e) := by
  intro d
  induction d with
  | leaf v =>
    intro γ e t hd he hdt het
    cases v with
    | bot => exact he
    | err b => exact TreeOk.leaf γ _
    | num n => exact TreeOk.leaf γ _
  | node i q f ih =>
    intro γ e t hd he hdt het
    obtain ⟨hq, hfin, hsub, hnon⟩ := TreeOk_node_inv hd
    cases hdt with
    | node _ _ _ ft hft =>
      cases het with
      | bot => exact hd
      | node _ _ ge _ hge =>
        obtain ⟨hq', hfin', hsub', hnon'⟩ := TreeOk_node_inv he
        rw [Tree.join_node_self]
        refine TreeOk.node γ i q _ hq ?_ ?_ ?_
        · obtain ⟨l, hl⟩ := hfin
          obtain ⟨l', hl'⟩ := hfin'
          refine ⟨l ++ l', fun r hr => ?_⟩
          by_cases h1 : f r = Tree.bot
          · by_cases h2 : ge r = Tree.bot
            · have hbot : Tree.join (f r) (ge r) = Tree.bot := by rw [h1, h2]; rfl
              exact absurd hbot hr
            · exact List.mem_append.mpr (Or.inr (hl' r h2))
          · exact List.mem_append.mpr (Or.inl (hl r h1))
        · intro r hr
          exact ih r (γ.cons i r) (ge r) (ft r) (hsub r hr) (hsub' r hr) (hft r) (hge r)
        · intro r hr
          have hbot : Tree.join (f r) (ge r) = Tree.bot := by
            rw [hnon r hr, hnon' r hr]; rfl
          exact hbot

/-- Legal subtrees are finitary. -/
theorem Finitary_of_TreeOk {σ : Ty} {γ : Ctx σ} {d : Tree σ} (h : TreeOk γ d) :
    Tree.Finitary d := by
  induction h with
  | leaf γ v => exact Tree.Finitary.leaf v
  | node γ i q f _ hfin hsub hnon ih =>
    refine Tree.Finitary.node i q f hfin fun r => ?_
    by_cases hr : LegalResp q r
    · exact ih r hr
    · rw [hnon r hr]; exact Tree.Finitary.leaf _

/-- `D_σ(γ)`, the finite subtrees legal in the context `γ`. -/
def DSub (σ : Ty) (γ : Ctx σ) : Type := { d : Tree σ // TreeOk γ d }

/-- "The partial order `D_σ` of finite trees of type `σ` is defined as
`D_σ(∅)`" (Definition 4.2). -/
abbrev D (σ : Ty) : Type := DSub σ Ctx.empty

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
theorem dsub_lub_of_finite_bounded {σ : Ty} {γ : Ctx σ} : ∀ l : List (DSub σ γ),
    Bounded (Set.ofList l) → ∃ d, IsLUB (Set.ofList l) d := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨DSub.bot, fun a ha => absurd ha (by simp [Set.ofList]), fun v _ => DSub.bot_le v⟩
  | cons a l ih =>
    rintro ⟨u, hu⟩
    have hsub : ∀ x, x ∈ Set.ofList l → x ∈ Set.ofList (a :: l) := by
      intro x hx; simp only [Set.mem_ofList, List.mem_cons]; exact Or.inr hx
    have hamem : a ∈ Set.ofList (a :: l) := by simp [Set.ofList]
    obtain ⟨d, hd⟩ := ih ⟨u, fun x hx => hu x (hsub x hx)⟩
    have hau : Tree.Le a.1 u.1 := hu a hamem
    have hdu : Tree.Le d.1 u.1 := hd.2 u fun x hx => hu x (hsub x hx)
    have hj := Tree.join_spec a.1 d.1 u.1 hau hdu
    refine ⟨⟨Tree.join a.1 d.1, TreeOk_join a.1 γ d.1 u.1 a.2 d.2 hau hdu⟩, ?_, ?_⟩
    · intro x hx
      simp only [Set.mem_ofList, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hj.1
      · exact Po.le_trans (show Tree.Le x.1 d.1 from hd.1 x hx) hj.2.1
    · intro v hv
      exact hj.2.2 v.1 (hv a hamem) (hd.2 v fun x hx => hv x (hsub x hx))

/-! ### Countability of the syntactic material -/

/-- An injection of `Val` into `Nat`. -/
def Val.encode : Val → Nat
  | .bot => 0
  | .err b => if b then 1 else 2
  | .num n => n + 3

theorem Val.encode_inj : ∀ {v w : Val}, v.encode = w.encode → v = w
  | .bot, .bot, _ => rfl
  | .bot, .err b, h => by cases b <;> exact absurd h (by simp [Val.encode])
  | .bot, .num n, h => by exact absurd h (by simp [Val.encode])
  | .err b, .bot, h => by cases b <;> exact absurd h (by simp [Val.encode])
  | .err b, .err b', h => by
      cases b <;> cases b' <;> first | rfl | exact absurd h (by simp [Val.encode])
  | .err b, .num n, h => by
      cases b <;> exact absurd h (by simp [Val.encode])
  | .num n, .bot, h => by exact absurd h (by simp [Val.encode])
  | .num n, .err b, h => by
      cases b <;> exact absurd h (by simp [Val.encode])
  | .num n, .num m, h => by
      simp only [Val.encode, Nat.add_right_cancel_iff] at h
      rw [h]

mutual
/-- An injection of queries into `Enc`. -/
def Query.enc : {σ : Ty} → Query σ → Enc
  | _, .hole => .leaf 0
  | _, .step i q r rest => .node (.leaf i.val) (.node q.enc (.node r.enc rest.enc))

/-- An injection of responses into `Enc`. -/
def Resp.enc : {σ : Ty} → Resp σ → Enc
  | _, .ans n => .leaf n
  | _, .node i p => .node (.leaf 0) (.node (.leaf i.val) p.enc)
  | _, .step i q r rest =>
      .node (.leaf 1) (.node (.leaf i.val) (.node q.enc (.node r.enc rest.enc)))
end

mutual
theorem Query.enc_inj : ∀ {σ : Ty} (q q' : Query σ), q.enc = q'.enc → q = q'
  | _, .hole, .hole, _ => rfl
  | _, .hole, .step _ _ _ _, h => by exact Enc.noConfusion h
  | _, .step _ _ _ _, .hole, h => by exact Enc.noConfusion h
  | _, .step i q r rest, .step i' q' r' rest', h => by
      injection h with h1 h2
      injection h1 with hi
      injection h2 with h3 h4
      injection h4 with h5 h6
      have hii : i = i' := Fin.ext hi
      subst hii
      have hq : q = q' := Query.enc_inj q q' h3
      subst hq
      have hr : r = r' := Resp.enc_inj r r' h5
      subst hr
      rw [Query.enc_inj rest rest' h6]

theorem Resp.enc_inj : ∀ {σ : Ty} (r r' : Resp σ), r.enc = r'.enc → r = r'
  | _, .ans n, .ans m, h => by
      injection h with h1
      rw [h1]
  | _, .ans _, .node _ _, h => by exact Enc.noConfusion h
  | _, .ans _, .step _ _ _ _, h => by exact Enc.noConfusion h
  | _, .node _ _, .ans _, h => by exact Enc.noConfusion h
  | _, .step _ _ _ _, .ans _, h => by exact Enc.noConfusion h
  | _, .node i p, .node i' p', h => by
      injection h with h1 h2
      injection h2 with h3 h4
      injection h3 with hi
      have hii : i = i' := Fin.ext hi
      subst hii
      rw [Query.enc_inj p p' h4]
  | _, .node _ _, .step _ _ _ _, h => by
      injection h with h1 h2
      injection h1 with h0
      exact absurd h0 (by omega)
  | _, .step _ _ _ _, .node _ _, h => by
      injection h with h1 h2
      injection h1 with h0
      exact absurd h0 (by omega)
  | _, .step i q r rest, .step i' q' r' rest', h => by
      injection h with h1 h2
      injection h2 with h3 h4
      injection h3 with hi
      injection h4 with h5 h6
      injection h6 with h7 h8
      have hii : i = i' := Fin.ext hi
      subst hii
      have hq : q = q' := Query.enc_inj q q' h5
      subst hq
      have hr : r = r' := Resp.enc_inj r r' h7
      subst hr
      rw [Resp.enc_inj rest rest' h8]
end

/-- Inversion for `Finitary` at a node. -/
theorem Tree.Finitary_node_inv {σ : Ty} {i : Fin σ.arity} {q : Query (σ.arg i)}
    {f : Resp (σ.arg i) → Tree σ} (h : Tree.Finitary (.node i q f)) :
    Tree.FiniteProperDomain f ∧ ∀ r, Tree.Finitary (f r) := by
  cases h with
  | node _ _ _ hfin hsub => exact ⟨hfin, hsub⟩

/-- An injection of *finitary* trees into `Enc`.

A branching function with a finite proper domain is determined by its node
value together with its (encoded) branches over any list covering the proper
domain: everything off the list is `⊥`.  The list is `Classical.choose` of the
finiteness proposition, which depends only on the branching function, so the
encoding is a genuine function of the tree. -/
noncomputable def encFin {σ : Ty} : (d : Tree σ) → Tree.Finitary d → Enc
  | .leaf v, _ => .leaf v.encode
  | .node i q f, h =>
      .node (.node (.leaf i.val) q.enc)
        (encList ((Classical.choose (Tree.Finitary_node_inv h).1).map
          fun r => Enc.node r.enc (encFin (f r) ((Tree.Finitary_node_inv h).2 r))))

theorem encFin_inj {σ : Ty} : ∀ (d e : Tree σ) (hd : Tree.Finitary d)
    (he : Tree.Finitary e), encFin d hd = encFin e he → d = e
  | .leaf v, .leaf w, _, _, h => by
      simp only [encFin] at h
      injection h with h1
      rw [Val.encode_inj h1]
  | .leaf _, .node _ _ _, _, _, h => by
      simp only [encFin] at h
      exact Enc.noConfusion h
  | .node _ _ _, .leaf _, _, _, h => by
      simp only [encFin] at h
      exact Enc.noConfusion h
  | .node i q f, .node i' q' f', hd, he, h => by
      simp only [encFin] at h
      injection h with h1 h2
      injection h1 with h1a h1b
      injection h1a with hi
      have hii : i = i' := Fin.ext hi
      subst hii
      have hqq : q = q' := Query.enc_inj q q' h1b
      subst hqq
      have hmap := encList_inj _ _ h2
      have hlists : ∀ (l1 l2 : List (Resp (σ.arg i)))
          (hf1 : ∀ r, Tree.Finitary (f r)) (hf2 : ∀ r, Tree.Finitary (f' r)),
          l1.map (fun r => Enc.node r.enc (encFin (f r) (hf1 r)))
            = l2.map (fun r => Enc.node r.enc (encFin (f' r) (hf2 r))) →
          l1 = l2 ∧ ∀ r, r ∈ l1 → f r = f' r := by
        intro l1
        induction l1 with
        | nil =>
          intro l2 _ _ hm
          cases l2 with
          | nil => exact ⟨rfl, fun r hr => absurd hr (by simp)⟩
          | cons _ _ => exact absurd hm (by simp)
        | cons r l1 ih =>
          intro l2 hf1 hf2 hm
          cases l2 with
          | nil => exact absurd hm (by simp)
          | cons r₂ l2 =>
            simp only [List.map_cons, List.cons.injEq] at hm
            obtain ⟨hh, ht⟩ := hm
            injection hh with hr1 hr2
            have hrr : r = r₂ := Resp.enc_inj r r₂ hr1
            subst hrr
            have hbr : f r = f' r := encFin_inj (f r) (f' r) (hf1 r) (hf2 r) hr2
            obtain ⟨hl, hall⟩ := ih l2 hf1 hf2 ht
            refine ⟨by rw [hl], fun s hs => ?_⟩
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hbr
            · exact hall s hs
      obtain ⟨hl, hall⟩ := hlists _ _ _ _ hmap
      have hfeq : f = f' := by
        funext r
        by_cases hr : r ∈ Classical.choose (Tree.Finitary_node_inv hd).1
        · exact hall r hr
        · have h1 : f r = Tree.bot := by
            refine Classical.byContradiction fun hne => ?_
            exact hr (Classical.choose_spec (Tree.Finitary_node_inv hd).1 r hne)
          have h2 : f' r = Tree.bot := by
            refine Classical.byContradiction fun hne => ?_
            have hmem := Classical.choose_spec (Tree.Finitary_node_inv he).1 r hne
            rw [← hl] at hmem
            exact hr hmem
          rw [h1, h2]
      rw [hfeq]

/-- `D_σ(γ)` is countable: "`D_σ` is countable because every branching function
has a finite proper domain" (proof of Lemma 4.3).

Legal trees are finitary (`Finitary_of_TreeOk`), and `encFin` injects the
finitary trees into the countable type `Enc`. -/
theorem dsub_countable {σ : Ty} {γ : Ctx σ} : Countable (DSub σ γ) := by
  refine Countable.ofInjection countable_Enc
    (fun d => encFin d.1 (Finitary_of_TreeOk d.2)) ?_
  intro a b h
  exact Subtype.ext (encFin_inj a.1 b.1 _ _ h)

/-- **Lemma 4.3.**  *`D_σ` is a finitary basis.*

"`D_σ` is a partial order because `⊑` is reflexive, anti-symmetric, and
transitive.  `D_σ` is countable because every branching function has a finite
proper domain.  It is straightforward but tedious to prove that every finite
bounded subset of `D_σ` has a least upper bound." -/
instance lemma_4_3 {σ : Ty} {γ : Ctx σ} : FinitaryBasis (DSub σ γ) where
  toPo := inferInstance
  elt := DSub.bot
  lub_of_finite_bounded := dsub_lub_of_finite_bounded

/-- "As an immediate consequence of this lemma, we conclude that the ideal
completion of `D_σ` is a Scott domain (ω-algebraic bounded-complete cpo). …
The result is the Scott domain designated `T_σ`."  (§4.1, after Lemma 4.3.) -/
abbrev T (σ : Ty) : Type := Ideal (D σ)

/-- The finite approximations of a tree are directed.

This is a consequence of Lemma 4.3: two finite trees below `t` form a bounded
subset of `D_σ`, hence have a least upper bound, which is again below `t`.

It is needed because most of the trees named in Definitions 4.19–4.21 —
`add1`, `if0`, `catch`, and the approximants to `K`, `I` and `S` — branch over
*infinitely* many responses and so are *not* elements of the finitary basis
`D_σ`; they are limit points of `T_σ`. -/
theorem finiteApprox_directed {σ : Ty} (t : Tree σ) (d₁ d₂ : D σ)
    (h₁ : d₁.1 ⊑ t) (h₂ : d₂.1 ⊑ t) : ∃ d : D σ, d.1 ⊑ t ∧ d₁ ⊑ d ∧ d₂ ⊑ d := by
  have hj := Tree.join_spec d₁.1 d₂.1 t h₁ h₂
  exact ⟨⟨Tree.join d₁.1 d₂.1, TreeOk_join d₁.1 Ctx.empty d₂.1 t d₁.2 d₂.2 h₁ h₂⟩,
    hj.2.2 t h₁ h₂, hj.1, hj.2.1⟩

/-- The element of `T_σ` determined by a (possibly infinite) tree `t`: the ideal
of its finite approximations.  For a finite `t` this is the principal ideal
`I_t` of Theorem 4.4. -/
noncomputable def idealOf {σ : Ty} (t : Tree σ) : T σ where
  carrier := fun d => d.1 ⊑ t
  nonempty' := ⟨DSub.bot, Tree.Le.bot t⟩
  downward a b hab hb := Po.le_trans (show a.1 ⊑ b.1 from hab) hb
  directed' a b ha hb := by
    obtain ⟨d, hd, h1, h2⟩ := finiteApprox_directed t a b ha hb
    exact ⟨d, hd, h1, h2⟩

/-- The ideal of finite approximations of a chain of trees. -/
noncomputable def idealOfChain {σ : Ty} (c : Nat → Tree σ)
    (hmono : ∀ m n : Nat, m ≤ n → c m ⊑ c n) : T σ where
  carrier := fun d => ∃ n, d.1 ⊑ c n
  nonempty' := ⟨DSub.bot, 0, Tree.Le.bot _⟩
  downward a b hab := by
    rintro ⟨n, hn⟩; exact ⟨n, Po.le_trans (show a.1 ⊑ b.1 from hab) hn⟩
  directed' a b := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    have hm' : a.1 ⊑ c (m + n) := Po.le_trans hm (hmono m (m + n) (Nat.le_add_right m n))
    have hn' : b.1 ⊑ c (m + n) := Po.le_trans hn (hmono n (m + n) (Nat.le_add_left n m))
    obtain ⟨d, hd, h1, h2⟩ := finiteApprox_directed (c (m + n)) a b hm' hn'
    exact ⟨d, ⟨m + n, hd⟩, h1, h2⟩

/-- **Theorem 4.4**, ω-algebraicity of the tree domains, from the countability
half of Lemma 4.3. -/
theorem lemma_4_3_omega_algebraic {σ : Ty} :
    ScottDomain.OmegaAlgebraic (T σ) := idealOmegaAlgebraic dsub_countable

/-- The reflexivity, antisymmetry and transitivity half of Lemma 4.3, which is
proved outright. -/
theorem lemma_4_3_partial_order {σ : Ty} {γ : Ctx σ} :
    (∀ d : DSub σ γ, d ⊑ d) ∧
    (∀ d e f : DSub σ γ, d ⊑ e → e ⊑ f → d ⊑ f) ∧
    (∀ d e : DSub σ γ, d ⊑ e → e ⊑ d → d = e) :=
  ⟨Po.le_refl, fun _ _ _ h₁ h₂ => Po.le_trans h₁ h₂, fun _ _ h₁ h₂ => Po.le_antisymm h₁ h₂⟩

end FA
