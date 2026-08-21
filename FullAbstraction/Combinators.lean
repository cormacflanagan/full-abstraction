/-
# The constants and combinators of the tree model (§4.3, §4.4, Appendix A)

Formalises **Definition 4.19** (`add1`, `sub1`, `if0`, `catch`),
**Definition 4.20** (`K`), **Definition 4.21** (`S`), the meaning of `Y_σ`, and
**Definition 4.1** (the tree model `T` for SPCF); states **Theorem 4.22**,
**Corollary 4.23**, **Corollary 4.24** and the results of Appendix A
(**Lemma A.1**, **Claim A.2**, **Definition A.3**, **Definition A.4**,
**Claim A.5**, **Lemma A.6**, **Lemma A.7**).
-/
import FullAbstraction.Apply
import FullAbstraction.Semantics

namespace FA

open Po

/-! ## Definition 4.19: `add1`, `sub1`, `if0`, `catch` -/

/-- For a ground argument, the only query is `?` and the only responses are
final answers, so a branching function on `Resp 𝕆` is determined by its values
on the numerals. -/
noncomputable def groundBranch {σ : Ty} (h : Nat → Tree σ) : Resp 𝕆 → Tree σ
  | .ans n => h n
  | _ => Tree.bot

/-- `T[[add1]] = ⟨1, ?, {(n, n+1) | n ∈ ℕ}⟩` (Definition 4.19). -/
noncomputable def treeAdd1 : Tree (𝕆 ⇒ 𝕆) :=
  .node ⟨0, Nat.succ_pos _⟩ .hole (groundBranch fun n => .leaf (.num (n + 1)))

/-- `T[[sub1]] = ⟨1, ?, {(n+1, n) | n ∈ ℕ} ∪ {(0, ⊥)}⟩` (Definition 4.19). -/
noncomputable def treeSub1 : Tree (𝕆 ⇒ 𝕆) :=
  .node ⟨0, Nat.succ_pos _⟩ .hole
    (groundBranch fun n => match n with | 0 => Tree.bot | m + 1 => .leaf (.num m))

/-- `T[[if0_o]] = ⟨1, ?, {(0, ⟨2,?,λj.j⟩)} ∪ {(n+1, ⟨3,?,λj.j⟩) | n ∈ ℕ}⟩`
(Definition 4.19). -/
noncomputable def treeIf0 : Tree (𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆) :=
  .node ⟨0, by decide⟩ .hole
    (groundBranch fun n =>
      match n with
      | 0 => .node ⟨1, by decide⟩ .hole (groundBranch fun j => .leaf (.num j))
      | _ + 1 => .node ⟨2, by decide⟩ .hole (groundBranch fun j => .leaf (.num j)))

/-- `T[[catch_k]] = ⟨1, ?, {(j, j+k) | j ∈ ℕ} ∪ {(⟨j,?⟩, j−1) | 1 ≤ j ≤ k}⟩`
(Definition 4.19).

`catch_σ` has type `σ ⇒ o` and `k = σ.arity`.  The paper indexes arguments from
`1`, so its `j − 1` is our `i.val`. -/
noncomputable def treeCatch (σ : Ty) : Tree (σ ⇒ 𝕆) :=
  .node ⟨0, Nat.succ_pos _⟩ .hole fun r =>
    match r with
    | .ans j => .leaf (.num (j + σ.arity))
    | .node i _ => .leaf (.num i.val)
    | .step _ _ _ _ => Tree.bot

/-! ## Definition 4.20: the combinator `K` -/

/-- The bound needed to convert an argument index of `σ` into the corresponding
argument index of `σ ⇒ τ ⇒ σ`, which is shifted by two. -/
theorem K_index_lt {σ τ : Ty} (i : Fin σ.arity) : i.val + 2 < (σ ⇒ τ ⇒ σ).arity := by
  have h := i.isLt
  simp only [Ty.arity_arrow]
  omega

/-- **Definition 4.20** (`K`), the finite approximants.

"The solution of this recursion equation is the least upper bound of finitely
deep approximations to `K`:

```
K₀ (q)    = ⊥
K_{n+1}(q) = ⟨1, q, λ r . { a                                if r = q[?/a], a ∈ ℕ
                          { ⟨i+2, p, λ r' . Kₙ (r : ⟨r',?⟩)⟩  if r = q[?/⟨i,p⟩] }⟩
```
" -/
noncomputable def Kn (σ τ : Ty) : Nat → Query σ → Tree (σ ⇒ τ ⇒ σ)
  | 0, _ => Tree.bot
  | n + 1, q =>
      .node ⟨0, Nat.succ_pos _⟩ q fun r =>
        match q.answerOf r with
        | some (.num a) => .leaf (.num a)
        | some (.node i p) =>
            .node ⟨i.val + 2, K_index_lt i⟩ p fun r' => Kn σ τ n (r.extendHole ⟨i, r'⟩)
        | none => Tree.bot

/-- The approximants to `K` form a chain. -/
theorem Kn_mono (σ τ : Ty) : ∀ (n : Nat) (q : Query σ), Kn σ τ n q ⊑ Kn σ τ (n + 1) q := by
  intro n
  induction n with
  | zero => intro q; exact Tree.Le.bot _
  | succ n ih =>
    intro q
    refine Tree.Le.node _ _ _ _ fun r => ?_
    cases h : q.answerOf r with
    | none => simp only [Kn, h]; exact Tree.Le.refl _
    | some x =>
      cases x with
      | num a => simp only [Kn, h]; exact Tree.Le.refl _
      | node i p =>
        simp only [Kn, h]
        exact Tree.Le.node _ _ _ _ fun r' => ih _

/-- Monotonicity of the `K` chain in the index. -/
theorem Kn_le_of_le (σ τ : Ty) {m n : Nat} (h : m ≤ n) (q : Query σ) :
    Kn σ τ m q ⊑ Kn σ τ n q := by
  induction h with
  | refl => exact Tree.Le.refl _
  | step _ ih => exact Po.le_trans ih (Kn_mono σ τ _ q)

/-- `K_{σ,τ}` denotes the tree `K(?) = ⊔ {Kₙ(?) | n ∈ ℕ}` (Definition 4.20).

Note that each `Kₙ(?)` branches over the infinitely many final answers `a ∈ ℕ`,
so it is a limit point of `T_{σ→τ→σ}` rather than an element of the finitary
basis; `K` is therefore the ideal of the finite approximations of the whole
chain. -/
noncomputable def treeK (σ τ : Ty) : T (σ ⇒ τ ⇒ σ) :=
  idealOfChain (fun n => Kn σ τ n .hole) fun _ _ h => Kn_le_of_le σ τ h .hole

/-! ### Claim A.2: `K` performs a recursive copy -/

/-- One unfolding of `apply₀ (K_{n+1}(q), d)` when `d @ q` is a node: `K`
switches to probing the `(j+2)`-nd argument, i.e. the `j`-th argument of its
first argument, and recurs on the query extended by that step. -/
theorem apply0_Kn_node (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (e : Tree τ)
    (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ)
    (hq : d.at' q = some (.node j p h)) :
    apply0 (apply0 (Kn σ τ (n + 1) q) d) e
      = .node j p fun r' => apply0 (apply0 (Kn σ τ n (q.snoc j p r')) d) e := by
  rw [Kn, apply0, hq]
  dsimp only
  rw [Query.answerOf_substAns]
  dsimp only
  rw [apply0, apply0]
  simp only [extendHole_substAns_node]

/-- `apply₀ (K_{n+1}(q), d, e) = errorᵢ` when `d @ q = errorᵢ`. -/
theorem apply0_Kn_err (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (e : Tree τ) (b : Bool)
    (hq : d.at' q = some (.leaf (.err b))) :
    apply0 (apply0 (Kn σ τ (n + 1) q) d) e = .leaf (.err b) := by
  rw [Kn, apply0, hq]
  dsimp only
  rfl

/-- `apply₀ (K_{n+1}(q), d, e) = ⌜a⌝` when `d @ q = ⌜a⌝`. -/
theorem apply0_Kn_num (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (e : Tree τ) (a : Nat)
    (hq : d.at' q = some (.leaf (.num a))) :
    apply0 (apply0 (Kn σ τ (n + 1) q) d) e = .leaf (.num a) := by
  rw [Kn, apply0, hq]
  dsimp only
  rw [Query.answerOf_substAns]
  dsimp only
  rfl

/-- **Claim A.2** (the `⊑` half).  *Let `d ∈ D_σ`, `e ∈ D_τ` and let `q ∈ Q_σ` be
a valid path in `d`.  Then `apply (K(q), d, e) = d @ q`.*

Every approximant of `K(q)` yields at most `d @ q`. -/
theorem claim_A_2_le (σ τ : Ty) : ∀ (n : Nat) (q : Query σ) (d : Tree σ) (e : Tree τ)
    (d' : Tree σ), d.at' q = some d' → Tree.Le (apply0 (apply0 (Kn σ τ n q) d) e) d' := by
  intro n
  induction n with
  | zero => intro q d e d' _; exact Tree.Le.bot _
  | succ n ih =>
    intro q d e d' hq
    cases d' with
    | leaf v =>
      cases v with
      | bot => rw [Kn, apply0, hq]; dsimp only; exact Tree.Le.bot _
      | err b =>
        rw [Kn, apply0, hq]
        dsimp only
        exact Tree.Le.refl _
      | num a =>
        rw [Kn, apply0, hq]
        dsimp only
        rw [Query.answerOf_substAns]
        dsimp only
        exact Tree.Le.refl _
    | node j p h =>
      rw [apply0_Kn_node σ τ n q d e j p h hq]
      refine Tree.Le.node _ _ _ _ fun r' => ih (q.snoc j p r') d e (h r') ?_
      rw [at'_snoc, hq]
      exact Tree.stepAt_self j p h r'

/-- **Claim A.2** (the `⊒` half).  Every finitary approximation of `d @ q` is
reached by some approximant `Kₙ(q)`. -/
theorem claim_A_2_ge (σ τ : Ty) : ∀ {a : Tree σ}, Tree.Finitary a →
    ∀ (q : Query σ) (d : Tree σ) (e : Tree τ) (d' : Tree σ),
      d.at' q = some d' → Tree.Le a d' →
      ∃ n, Tree.Le a (apply0 (apply0 (Kn σ τ n q) d) e) := by
  intro a ha
  induction ha with
  | leaf v =>
    intro q d e d' hq hle
    cases v with
    | bot => exact ⟨0, Tree.Le.bot _⟩
    | err b =>
      cases hle with
      | leaf _ =>
        refine ⟨1, ?_⟩
        rw [apply0_Kn_err σ τ 0 q d e b hq]
        exact Tree.Le.refl _
    | num m =>
      cases hle with
      | leaf _ =>
        refine ⟨1, ?_⟩
        rw [apply0_Kn_num σ τ 0 q d e m hq]
        exact Tree.Le.refl _
  | node i p g hfin _ ih =>
    intro q d e d' hq hle
    obtain ⟨h, rfl⟩ := Tree.eq_node_of_le hle
    have hgh := Tree.Le_node_inv hle
    have hat : ∀ r, d.at' (q.snoc i p r) = some (h r) := by
      intro r
      rw [at'_snoc, hq]
      exact Tree.stepAt_self i p h r
    have hex : ∀ r, ∃ n, Tree.Le (g r) (apply0 (apply0 (Kn σ τ n (q.snoc i p r)) d) e) :=
      fun r => ih r (q.snoc i p r) d e (h r) (hat r) (hgh r)
    obtain ⟨l, hl⟩ := hfin
    refine ⟨maxOver l (fun r => Classical.choose (hex r)) + 1, ?_⟩
    rw [apply0_Kn_node σ τ _ q d e i p h hq]
    refine Tree.Le.node _ _ _ _ fun r => ?_
    by_cases hr : g r = Tree.bot
    · rw [hr]; exact Tree.Le.bot _
    · exact Tree.Le.trans (Classical.choose_spec (hex r))
        (apply0_mono_left
          (apply0_mono_left (Kn_le_of_le σ τ
            (le_maxOver (fun s => Classical.choose (hex s)) l r (hl r hr)) _) d) e)

/-- **Claim A.2.**  *Let `d ∈ D_σ`, `e ∈ D_τ` and let `q ∈ Q_σ` be a valid path
in `d` (`d @ q` is defined).  Then `apply (K(q), d, e) = d @ q`.*

Stated as the two halves of the equality between `d @ q` and the least upper
bound of `{apply₀ (K_n(q), d, e) | n ∈ ℕ}`. -/
theorem claim_A_2 (σ τ : Ty) (q : Query σ) (d : Tree σ) (e : Tree τ) (d' : Tree σ)
    (hq : d.at' q = some d') :
    (∀ n, Tree.Le (apply0 (apply0 (Kn σ τ n q) d) e) d') ∧
    (∀ a : Tree σ, Tree.Finitary a → Tree.Le a d' →
      ∃ n, Tree.Le a (apply0 (apply0 (Kn σ τ n q) d) e)) :=
  ⟨fun n => claim_A_2_le σ τ n q d e d' hq,
   fun a hfa hle => claim_A_2_ge σ τ hfa q d e d' hq hle⟩


/-! ### Legal approximants to `K`

`Kₙ(q)` is not an element of the finitary basis `D_{σ→τ→σ}`: it branches over
all final answers `a ∈ ℕ`, and it answers responses that are not legal for `q`.
Definition 4.20's "`Kₙ : Q_σ → D_{σ→τ→σ}(q̂)`" therefore cannot be read
literally.  What is true, and what Lemma A.1 needs, is that the finite *legal*
trees below `Kₙ(q)` already compute whatever `Kₙ(q)` computes. -/

/-- `(σ→τ→σ)ᵢ₊₂ = σᵢ`: `K`'s `(i+2)`-nd argument is the `i`-th argument of its
first argument. -/
theorem K_shiftArg (σ τ : Ty) (i : Fin σ.arity) :
    (σ ⇒ τ ⇒ σ).arg ⟨i.val + 2, K_index_lt i⟩ = σ.arg i := rfl

/-- `K`'s first argument is not one of the arguments it inherits from `σ`. -/
theorem K_zero_ne_shift (σ τ : Ty) (j : Fin σ.arity) :
    ¬ ((⟨0, Nat.succ_pos _⟩ : Fin (σ ⇒ τ ⇒ σ).arity) = ⟨j.val + 2, K_index_lt j⟩) := by
  intro h
  rw [Fin.mk.injEq] at h
  omega

/-- Distinct arguments of `σ` stay distinct as arguments of `σ → τ → σ`. -/
theorem K_shift_ne (σ τ : Ty) {i j : Fin σ.arity} (hij : ¬ i = j) :
    ¬ ((⟨j.val + 2, K_index_lt j⟩ : Fin (σ ⇒ τ ⇒ σ).arity)
        = ⟨i.val + 2, K_index_lt i⟩) := by
  intro he
  rw [Fin.mk.injEq] at he
  exact hij (Fin.ext (show j.val = i.val by omega)).symm

/-- The **pruning** of `Kₙ(q)` along a finite argument `d`: `Kₙ(q)` with every
branch removed that `d` does not take — at each query only the response `d`
gives, and at each node only the responses `d` answers.  Both sets are finite
because `d` is, and both are legal because `d` is. -/
noncomputable def KnP (σ τ : Ty) : Nat → Query σ → Tree σ → Tree (σ ⇒ τ ⇒ σ)
  | 0, _, _ => Tree.bot
  | n + 1, q, d =>
      match d.at' q with
      | some (.leaf (.num m)) =>
          .node ⟨0, Nat.succ_pos _⟩ q fun r =>
            if r = q.substAns (.num m) then .leaf (.num m) else Tree.bot
      | some (.node j p h) =>
          .node ⟨0, Nat.succ_pos _⟩ q fun r =>
            if r = q.substAns (.node j p) then
              .node ⟨j.val + 2, K_index_lt j⟩ p fun r' =>
                if h r' = Tree.bot then Tree.bot else KnP σ τ n (q.snoc j p r') d
            else Tree.bot
      | _ => .node ⟨0, Nat.succ_pos _⟩ q fun _ => Tree.bot

theorem KnP_num (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (m : Nat)
    (hq : d.at' q = some (.leaf (.num m))) :
    KnP σ τ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun r =>
      if r = q.substAns (.num m) then .leaf (.num m) else Tree.bot := by
  rw [KnP, hq]

theorem KnP_node (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ)
    (hq : d.at' q = some (.node j p h)) :
    KnP σ τ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun r =>
      if r = q.substAns (.node j p) then
        .node ⟨j.val + 2, K_index_lt j⟩ p fun r' =>
          if h r' = Tree.bot then Tree.bot else KnP σ τ n (q.snoc j p r') d
      else Tree.bot := by
  rw [KnP, hq]

theorem KnP_other (σ τ : Ty) (n : Nat) (q : Query σ) (d : Tree σ)
    (hq : (∀ m, d.at' q ≠ some (.leaf (.num m))) ∧
      ∀ (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ),
        d.at' q ≠ some (.node j p h)) :
    KnP σ τ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun _ => Tree.bot := by
  rw [KnP]
  cases hdq : d.at' q with
  | none => rfl
  | some t =>
    cases t with
    | leaf v =>
      cases v with
      | bot => rfl
      | err b => rfl
      | num m => exact absurd hdq (hq.1 m)
    | node j p h => exact absurd hdq (hq.2 j p h)

/-- The pruned approximants lie below the approximants of Definition 4.20. -/
theorem KnP_le_Kn (σ τ : Ty) : ∀ (n : Nat) (q : Query σ) (d : Tree σ),
    KnP σ τ n q d ⊑ Kn σ τ n q := by
  intro n
  induction n with
  | zero => intro q d; exact Tree.Le.bot _
  | succ n ih =>
    intro q d
    cases hdq : d.at' q with
    | none =>
      rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact Option.noConfusion hm,
        fun j p h hm => by rw [hdq] at hm; exact Option.noConfusion hm⟩, Kn]
      exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, Kn]
          exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
        | err b =>
          rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, Kn]
          exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
        | num m =>
          rw [KnP_num σ τ n q d m hdq, Kn]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = q.substAns (.num m)
          · subst hr
            rw [if_pos rfl]
            simp only [Query.answerOf_substAns]
            exact Tree.Le.refl _
          · rw [if_neg hr]; exact Tree.Le.bot _
      | node j p h =>
        rw [KnP_node σ τ n q d j p h hdq, Kn]
        refine Tree.Le.node _ _ _ _ fun r => ?_
        by_cases hr : r = q.substAns (.node j p)
        · subst hr
          rw [if_pos rfl]
          simp only [Query.answerOf_substAns]
          refine Tree.Le.node _ _ _ _ fun r' => ?_
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb]; exact Tree.Le.bot _
          · rw [if_neg hb, extendHole_substAns_node]
            exact ih (q.snoc j p r') d
        · rw [if_neg hr]; exact Tree.Le.bot _

/-- Pruning loses nothing: whatever a finite tree gets out of `Kₙ(q)` applied to
`d`, it already gets out of the pruned `KnP n q d`. -/
theorem apply0_KnP_ge (σ τ : Ty) : ∀ (n : Nat) (q : Query σ) (d : Tree σ) (e : Tree τ)
    (a : Tree σ), Tree.Le a (apply0 (apply0 (Kn σ τ n q) d) e) →
      Tree.Le a (apply0 (apply0 (KnP σ τ n q d) d) e) := by
  intro n
  induction n with
  | zero =>
    intro q d e a ha
    have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
    rw [hab]; exact Tree.Le.bot _
  | succ n ih =>
    intro q d e a ha
    cases hdq : d.at' q with
    | none =>
      have hK : apply0 (apply0 (Kn σ τ (n + 1) q) d) e = Tree.bot := by
        rw [Kn, apply0, hdq]; rfl
      rw [hK] at ha
      have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
      rw [hab]; exact Tree.Le.bot _
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          have hK : apply0 (apply0 (Kn σ τ (n + 1) q) d) e = Tree.bot := by
            rw [Kn, apply0, hdq]; rfl
          rw [hK] at ha
          have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
          rw [hab]; exact Tree.Le.bot _
        | err b =>
          rw [apply0_Kn_err σ τ n q d e b hdq] at ha
          have hP : apply0 (apply0 (KnP σ τ (n + 1) q d) d) e = .leaf (.err b) := by
            rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
              fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, apply0, hdq]
            rfl
          rw [hP]; exact ha
        | num m =>
          rw [apply0_Kn_num σ τ n q d e m hdq] at ha
          have hP : apply0 (apply0 (KnP σ τ (n + 1) q d) d) e = .leaf (.num m) := by
            rw [KnP_num σ τ n q d m hdq, apply0, hdq]
            dsimp only
            rw [if_pos rfl]
            rfl
          rw [hP]; exact ha
      | node j p h =>
        rw [apply0_Kn_node σ τ n q d e j p h hdq] at ha
        have hat : ∀ r', d.at' (q.snoc j p r') = some (h r') := by
          intro r'
          rw [at'_snoc, hdq]
          exact Tree.stepAt_self j p h r'
        have hP : apply0 (apply0 (KnP σ τ (n + 1) q d) d) e
            = .node j p fun r' =>
                if h r' = Tree.bot then Tree.bot
                else apply0 (apply0 (KnP σ τ n (q.snoc j p r') d) d) e := by
          rw [KnP_node σ τ n q d j p h hdq, apply0, hdq]
          dsimp only
          rw [if_pos rfl, apply0, apply0]
          refine congrArg _ (funext fun r' => ?_)
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb, if_pos hb]; rfl
          · rw [if_neg hb, if_neg hb]
        rw [hP]
        cases ha with
        | bot _ => exact Tree.Le.bot _
        | node _ _ g _ hgr =>
          refine Tree.Le.node _ _ _ _ fun r' => ?_
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb]
            have hle : Tree.Le (g r') (h r') :=
              Tree.Le.trans (hgr r')
                (claim_A_2_le σ τ n (q.snoc j p r') d e (h r') (hat r'))
            rw [hb] at hle
            have hgb : g r' = Tree.bot := Po.le_antisymm hle (Tree.Le.bot _)
            rw [hgb]; exact Tree.Le.bot _
          · rw [if_neg hb]
            exact ih (q.snoc j p r') d e (g r') (hgr r')

/-- **Definition 4.20 made good.**  The pruned approximants are legal.

The hypotheses are the invariant the definition intends: `q` probes the
perimeter of what the context knows about `K`'s first argument, and what the
context knows about `K`'s `(i+2)`-nd argument is what `q̂` knows about the
`i`-th argument of `σ`. -/
theorem KnP_ok (σ τ : Ty) (d : Tree σ) (hd : TreeOk Ctx.empty d) :
    ∀ (n : Nat) (q : Query σ) (γ : Ctx (σ ⇒ τ ⇒ σ)),
      LegalQuery (γ ⟨0, Nat.succ_pos _⟩) q →
      (∀ i : Fin σ.arity, γ ⟨i.val + 2, K_index_lt i⟩ = q.ctx i) →
      TreeOk γ (KnP σ τ n q d) := by
  intro n
  induction n with
  | zero => intro q γ _ _; exact TreeOk.leaf γ _
  | succ n ih =>
    intro q γ h1 h2
    cases hdq : d.at' q with
    | none =>
      rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact Option.noConfusion hm,
        fun j p hf hm => by rw [hdq] at hm; exact Option.noConfusion hm⟩]
      exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
        (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p hf hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩]
          exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
            (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
        | err b =>
          rw [KnP_other σ τ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p hf hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩]
          exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
            (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
        | num m =>
          rw [KnP_num σ τ n q d m hdq]
          refine TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[q.substAns (.num m)], fun r hr => ?_⟩
            (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hrm : r = q.substAns (.num m)
            · rw [hrm]; exact List.mem_cons_self ..
            · exact absurd (if_neg hrm) hr
          · by_cases hrm : r = q.substAns (.num m)
            · rw [if_pos hrm]; exact TreeOk.leaf _ _
            · rw [if_neg hrm]; exact TreeOk.leaf _ _
          · by_cases hrm : r = q.substAns (.num m)
            · exact absurd (hrm ▸ LegalResp.num q m) hr
            · exact if_neg hrm
      | node j p hf =>
        have hsub : TreeOk q.ctx (Tree.node j p hf) :=
          TreeOk_at' q Ctx.empty d _ hd hdq
        obtain ⟨hp, hffin, hfsub, hfnon⟩ := TreeOk_node_inv hsub
        have hlegal : LegalResp q (q.substAns (.node j p)) := LegalResp.node q j p hp
        rw [KnP_node σ τ n q d j p hf hdq]
        refine TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[q.substAns (.node j p)], fun r hr => ?_⟩
          (fun r _ => ?_) (fun r hr => ?_)
        · by_cases hrm : r = q.substAns (.node j p)
          · rw [hrm]; exact List.mem_cons_self ..
          · exact absurd (if_neg hrm) hr
        · by_cases hrm : r = q.substAns (.node j p)
          · rw [if_pos hrm]
            subst hrm
            refine TreeOk.node _ ⟨j.val + 2, K_index_lt j⟩ p _ ?_ ?_ (fun r' hr' => ?_)
              (fun r' hr' => ?_)
            · rw [Ctx.cons_other _ _ (K_zero_ne_shift σ τ j), h2 j]
              exact hp
            · obtain ⟨l, hl⟩ := hffin
              refine ⟨l, fun r' hr' => hl r' ?_⟩
              intro hb
              exact hr' (if_pos hb)
            · by_cases hb : hf r' = Tree.bot
              · rw [if_pos hb]; exact TreeOk.leaf _ _
              · rw [if_neg hb]
                refine ih (q.snoc j p r') _ ?_ ?_
                · rw [Ctx.cons_other _ _ fun he =>
                    K_zero_ne_shift σ τ j he.symm, Ctx.cons_self]
                  exact legalQuery_join_snoc q _ j p r' h1 hr'
                · intro i
                  rw [Query.ctx_snoc]
                  by_cases hij : i = j
                  · subst hij
                    rw [Ctx.cons_self, Ctx.cons_other _ _ (K_zero_ne_shift σ τ i),
                      h2 i, Ctx.cons_self]
                  · rw [Ctx.cons_other _ _ (K_shift_ne σ τ hij),
                      Ctx.cons_other _ _ (K_zero_ne_shift σ τ i), h2 i,
                      Ctx.cons_other _ _ (fun he : j = i => hij he.symm)]
            · rw [if_pos (hfnon r' hr')]
          · rw [if_neg hrm]; exact TreeOk.leaf _ _
        · by_cases hrm : r = q.substAns (.node j p)
          · exact absurd (hrm ▸ hlegal) hr
          · exact if_neg hrm

/-! ## The combinator `I`

"The proof for `I` closely follows the proof for `K`" (Theorem 4.22); the tree
for `I` is constructed by the same recursive search process. -/

/-- The index shift for `I_σ : σ → σ`, which is by one. -/
theorem I_index_lt {σ : Ty} (i : Fin σ.arity) : i.val + 1 < (σ ⇒ σ).arity := by
  have h := i.isLt
  simp only [Ty.arity_arrow]
  omega

/-- Finite approximants to `I_σ`, defined by the analogue of Definition 4.20. -/
noncomputable def In (σ : Ty) : Nat → Query σ → Tree (σ ⇒ σ)
  | 0, _ => Tree.bot
  | n + 1, q =>
      .node ⟨0, Nat.succ_pos _⟩ q fun r =>
        match q.answerOf r with
        | some (.num a) => .leaf (.num a)
        | some (.node i p) =>
            .node ⟨i.val + 1, I_index_lt i⟩ p fun r' => In σ n (r.extendHole ⟨i, r'⟩)
        | none => Tree.bot

theorem In_mono (σ : Ty) : ∀ (n : Nat) (q : Query σ), In σ n q ⊑ In σ (n + 1) q := by
  intro n
  induction n with
  | zero => intro q; exact Tree.Le.bot _
  | succ n ih =>
    intro q
    refine Tree.Le.node _ _ _ _ fun r => ?_
    cases h : q.answerOf r with
    | none => simp only [In, h]; exact Tree.Le.refl _
    | some x =>
      cases x with
      | num a => simp only [In, h]; exact Tree.Le.refl _
      | node i p =>
        simp only [In, h]
        exact Tree.Le.node _ _ _ _ fun r' => ih _

theorem In_le_of_le (σ : Ty) {m n : Nat} (h : m ≤ n) (q : Query σ) :
    In σ m q ⊑ In σ n q := by
  induction h with
  | refl => exact Tree.Le.refl _
  | step _ ih => exact Po.le_trans ih (In_mono σ _ q)

/-! ### The `I` analogue of Claim A.2 -/

/-- One unfolding of `apply₀ (I_{n+1}(q), d)` when `d @ q` is a node. -/
theorem apply0_In_node (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ)
    (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ)
    (hq : d.at' q = some (.node j p h)) :
    apply0 (In σ (n + 1) q) d = .node j p fun r' => apply0 (In σ n (q.snoc j p r')) d := by
  rw [In, apply0, hq]
  dsimp only
  rw [Query.answerOf_substAns]
  dsimp only
  rw [apply0]
  simp only [extendHole_substAns_node]

theorem apply0_In_err (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (b : Bool)
    (hq : d.at' q = some (.leaf (.err b))) :
    apply0 (In σ (n + 1) q) d = .leaf (.err b) := by
  rw [In, apply0, hq]

theorem apply0_In_num (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (a : Nat)
    (hq : d.at' q = some (.leaf (.num a))) :
    apply0 (In σ (n + 1) q) d = .leaf (.num a) := by
  rw [In, apply0, hq]
  dsimp only
  rw [Query.answerOf_substAns]
  dsimp only
  rfl

/-- The `I` analogue of Claim A.2, `⊑` half: `apply (I(q), d) ⊑ d @ q`. -/
theorem claim_I_le (σ : Ty) : ∀ (n : Nat) (q : Query σ) (d d' : Tree σ),
    d.at' q = some d' → Tree.Le (apply0 (In σ n q) d) d' := by
  intro n
  induction n with
  | zero => intro q d d' _; exact Tree.Le.bot _
  | succ n ih =>
    intro q d d' hq
    cases d' with
    | leaf v =>
      cases v with
      | bot => rw [In, apply0, hq]; dsimp only; exact Tree.Le.bot _
      | err b => rw [apply0_In_err σ n q d b hq]; exact Tree.Le.refl _
      | num a => rw [apply0_In_num σ n q d a hq]; exact Tree.Le.refl _
    | node j p h =>
      rw [apply0_In_node σ n q d j p h hq]
      refine Tree.Le.node _ _ _ _ fun r' => ih (q.snoc j p r') d (h r') ?_
      rw [at'_snoc, hq]
      exact Tree.stepAt_self j p h r'

/-- The `I` analogue of Claim A.2, `⊒` half. -/
theorem claim_I_ge (σ : Ty) : ∀ {a : Tree σ}, Tree.Finitary a →
    ∀ (q : Query σ) (d d' : Tree σ), d.at' q = some d' → Tree.Le a d' →
      ∃ n, Tree.Le a (apply0 (In σ n q) d) := by
  intro a ha
  induction ha with
  | leaf v =>
    intro q d d' hq hle
    cases v with
    | bot => exact ⟨0, Tree.Le.bot _⟩
    | err b =>
      cases hle with
      | leaf _ => exact ⟨1, by rw [apply0_In_err σ 0 q d b hq]; exact Tree.Le.refl _⟩
    | num m =>
      cases hle with
      | leaf _ => exact ⟨1, by rw [apply0_In_num σ 0 q d m hq]; exact Tree.Le.refl _⟩
  | node i p g hfin _ ih =>
    intro q d d' hq hle
    obtain ⟨h, rfl⟩ := Tree.eq_node_of_le hle
    have hgh := Tree.Le_node_inv hle
    have hat : ∀ r, d.at' (q.snoc i p r) = some (h r) := by
      intro r
      rw [at'_snoc, hq]
      exact Tree.stepAt_self i p h r
    have hex : ∀ r, ∃ n, Tree.Le (g r) (apply0 (In σ n (q.snoc i p r)) d) :=
      fun r => ih r (q.snoc i p r) d (h r) (hat r) (hgh r)
    obtain ⟨l, hl⟩ := hfin
    refine ⟨maxOver l (fun r => Classical.choose (hex r)) + 1, ?_⟩
    rw [apply0_In_node σ _ q d i p h hq]
    refine Tree.Le.node _ _ _ _ fun r => ?_
    by_cases hr : g r = Tree.bot
    · rw [hr]; exact Tree.Le.bot _
    · exact Tree.Le.trans (Classical.choose_spec (hex r))
        (apply0_mono_left (In_le_of_le σ
          (le_maxOver (fun s => Classical.choose (hex s)) l r (hl r hr)) _) d)


/-! ### Legal approximants to `I` -/

/-- `(σ→σ)ᵢ₊₁ = σᵢ`. -/
theorem I_shiftArg (σ : Ty) (i : Fin σ.arity) :
    (σ ⇒ σ).arg ⟨i.val + 1, I_index_lt i⟩ = σ.arg i := rfl

theorem I_zero_ne_shift (σ : Ty) (j : Fin σ.arity) :
    ¬ ((⟨0, Nat.succ_pos _⟩ : Fin (σ ⇒ σ).arity) = ⟨j.val + 1, I_index_lt j⟩) := by
  intro h
  rw [Fin.mk.injEq] at h
  omega

theorem I_shift_ne (σ : Ty) {i j : Fin σ.arity} (hij : ¬ i = j) :
    ¬ ((⟨j.val + 1, I_index_lt j⟩ : Fin (σ ⇒ σ).arity) = ⟨i.val + 1, I_index_lt i⟩) := by
  intro he
  rw [Fin.mk.injEq] at he
  exact hij (Fin.ext (show j.val = i.val by omega)).symm

/-- The pruning of `Iₙ(q)` along a finite argument `d`, exactly as for `K`. -/
noncomputable def InP (σ : Ty) : Nat → Query σ → Tree σ → Tree (σ ⇒ σ)
  | 0, _, _ => Tree.bot
  | n + 1, q, d =>
      match d.at' q with
      | some (.leaf (.num m)) =>
          .node ⟨0, Nat.succ_pos _⟩ q fun r =>
            if r = q.substAns (.num m) then .leaf (.num m) else Tree.bot
      | some (.node j p h) =>
          .node ⟨0, Nat.succ_pos _⟩ q fun r =>
            if r = q.substAns (.node j p) then
              .node ⟨j.val + 1, I_index_lt j⟩ p fun r' =>
                if h r' = Tree.bot then Tree.bot else InP σ n (q.snoc j p r') d
            else Tree.bot
      | _ => .node ⟨0, Nat.succ_pos _⟩ q fun _ => Tree.bot

theorem InP_num (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (m : Nat)
    (hq : d.at' q = some (.leaf (.num m))) :
    InP σ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun r =>
      if r = q.substAns (.num m) then .leaf (.num m) else Tree.bot := by
  rw [InP, hq]

theorem InP_node (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ) (j : Fin σ.arity)
    (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ)
    (hq : d.at' q = some (.node j p h)) :
    InP σ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun r =>
      if r = q.substAns (.node j p) then
        .node ⟨j.val + 1, I_index_lt j⟩ p fun r' =>
          if h r' = Tree.bot then Tree.bot else InP σ n (q.snoc j p r') d
      else Tree.bot := by
  rw [InP, hq]

theorem InP_other (σ : Ty) (n : Nat) (q : Query σ) (d : Tree σ)
    (hq : (∀ m, d.at' q ≠ some (.leaf (.num m))) ∧
      ∀ (j : Fin σ.arity) (p : Query (σ.arg j)) (h : Resp (σ.arg j) → Tree σ),
        d.at' q ≠ some (.node j p h)) :
    InP σ (n + 1) q d = .node ⟨0, Nat.succ_pos _⟩ q fun _ => Tree.bot := by
  rw [InP]
  cases hdq : d.at' q with
  | none => rfl
  | some t =>
    cases t with
    | leaf v =>
      cases v with
      | bot => rfl
      | err b => rfl
      | num m => exact absurd hdq (hq.1 m)
    | node j p h => exact absurd hdq (hq.2 j p h)

theorem InP_le_In (σ : Ty) : ∀ (n : Nat) (q : Query σ) (d : Tree σ),
    InP σ n q d ⊑ In σ n q := by
  intro n
  induction n with
  | zero => intro q d; exact Tree.Le.bot _
  | succ n ih =>
    intro q d
    cases hdq : d.at' q with
    | none =>
      rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact Option.noConfusion hm,
        fun j p h hm => by rw [hdq] at hm; exact Option.noConfusion hm⟩, In]
      exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, In]
          exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
        | err b =>
          rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, In]
          exact Tree.Le.node _ _ _ _ fun _ => Tree.Le.bot _
        | num m =>
          rw [InP_num σ n q d m hdq, In]
          refine Tree.Le.node _ _ _ _ fun r => ?_
          by_cases hr : r = q.substAns (.num m)
          · subst hr
            rw [if_pos rfl]
            simp only [Query.answerOf_substAns]
            exact Tree.Le.refl _
          · rw [if_neg hr]; exact Tree.Le.bot _
      | node j p h =>
        rw [InP_node σ n q d j p h hdq, In]
        refine Tree.Le.node _ _ _ _ fun r => ?_
        by_cases hr : r = q.substAns (.node j p)
        · subst hr
          rw [if_pos rfl]
          simp only [Query.answerOf_substAns]
          refine Tree.Le.node _ _ _ _ fun r' => ?_
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb]; exact Tree.Le.bot _
          · rw [if_neg hb, extendHole_substAns_node]
            exact ih (q.snoc j p r') d
        · rw [if_neg hr]; exact Tree.Le.bot _

theorem apply0_InP_ge (σ : Ty) : ∀ (n : Nat) (q : Query σ) (d : Tree σ)
    (a : Tree σ), Tree.Le a (apply0 (In σ n q) d) →
      Tree.Le a (apply0 (InP σ n q d) d) := by
  intro n
  induction n with
  | zero =>
    intro q d a ha
    have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
    rw [hab]; exact Tree.Le.bot _
  | succ n ih =>
    intro q d a ha
    cases hdq : d.at' q with
    | none =>
      have hI : apply0 (In σ (n + 1) q) d = Tree.bot := by rw [In, apply0, hdq]
      rw [hI] at ha
      have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
      rw [hab]; exact Tree.Le.bot _
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          have hI : apply0 (In σ (n + 1) q) d = Tree.bot := by rw [In, apply0, hdq]
          rw [hI] at ha
          have hab : a = Tree.bot := Po.le_antisymm ha (Tree.Le.bot a)
          rw [hab]; exact Tree.Le.bot _
        | err b =>
          rw [apply0_In_err σ n q d b hdq] at ha
          have hP : apply0 (InP σ (n + 1) q d) d = .leaf (.err b) := by
            rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
              fun j p h hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩, apply0, hdq]
          rw [hP]; exact ha
        | num m =>
          rw [apply0_In_num σ n q d m hdq] at ha
          have hP : apply0 (InP σ (n + 1) q d) d = .leaf (.num m) := by
            rw [InP_num σ n q d m hdq, apply0, hdq]
            dsimp only
            rw [if_pos rfl]
            rfl
          rw [hP]; exact ha
      | node j p h =>
        rw [apply0_In_node σ n q d j p h hdq] at ha
        have hat : ∀ r', d.at' (q.snoc j p r') = some (h r') := by
          intro r'
          rw [at'_snoc, hdq]
          exact Tree.stepAt_self j p h r'
        have hP : apply0 (InP σ (n + 1) q d) d
            = .node j p fun r' =>
                if h r' = Tree.bot then Tree.bot
                else apply0 (InP σ n (q.snoc j p r') d) d := by
          rw [InP_node σ n q d j p h hdq, apply0, hdq]
          dsimp only
          rw [if_pos rfl, apply0]
          refine congrArg _ (funext fun r' => ?_)
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb, if_pos hb]; rfl
          · rw [if_neg hb, if_neg hb]
        rw [hP]
        cases ha with
        | bot _ => exact Tree.Le.bot _
        | node _ _ g _ hgr =>
          refine Tree.Le.node _ _ _ _ fun r' => ?_
          by_cases hb : h r' = Tree.bot
          · rw [if_pos hb]
            have hle : Tree.Le (g r') (h r') :=
              Tree.Le.trans (hgr r') (claim_I_le σ n (q.snoc j p r') d (h r') (hat r'))
            rw [hb] at hle
            have hgb : g r' = Tree.bot := Po.le_antisymm hle (Tree.Le.bot _)
            rw [hgb]; exact Tree.Le.bot _
          · rw [if_neg hb]
            exact ih (q.snoc j p r') d (g r') (hgr r')

/-- The `I` analogue of `KnP_ok`. -/
theorem InP_ok (σ : Ty) (d : Tree σ) (hd : TreeOk Ctx.empty d) :
    ∀ (n : Nat) (q : Query σ) (γ : Ctx (σ ⇒ σ)),
      LegalQuery (γ ⟨0, Nat.succ_pos _⟩) q →
      (∀ i : Fin σ.arity, γ ⟨i.val + 1, I_index_lt i⟩ = q.ctx i) →
      TreeOk γ (InP σ n q d) := by
  intro n
  induction n with
  | zero => intro q γ _ _; exact TreeOk.leaf γ _
  | succ n ih =>
    intro q γ h1 h2
    cases hdq : d.at' q with
    | none =>
      rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact Option.noConfusion hm,
        fun j p hf hm => by rw [hdq] at hm; exact Option.noConfusion hm⟩]
      exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
        (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
    | some t =>
      cases t with
      | leaf v =>
        cases v with
        | bot =>
          rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p hf hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩]
          exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
            (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
        | err b =>
          rw [InP_other σ n q d ⟨fun m hm => by rw [hdq] at hm; exact absurd hm (by simp),
            fun j p hf hm => by rw [hdq] at hm; exact absurd hm (by simp)⟩]
          exact TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1 ⟨[], fun _ hr => absurd rfl hr⟩
            (fun _ _ => TreeOk.leaf _ _) (fun _ _ => rfl)
        | num m =>
          rw [InP_num σ n q d m hdq]
          refine TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1
            ⟨[q.substAns (.num m)], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
          · by_cases hrm : r = q.substAns (.num m)
            · rw [hrm]; exact List.mem_cons_self ..
            · exact absurd (if_neg hrm) hr
          · by_cases hrm : r = q.substAns (.num m)
            · rw [if_pos hrm]; exact TreeOk.leaf _ _
            · rw [if_neg hrm]; exact TreeOk.leaf _ _
          · by_cases hrm : r = q.substAns (.num m)
            · exact absurd (hrm ▸ LegalResp.num q m) hr
            · exact if_neg hrm
      | node j p hf =>
        have hsubtree : TreeOk q.ctx (Tree.node j p hf) :=
          TreeOk_at' q Ctx.empty d _ hd hdq
        obtain ⟨hp, hffin, hfsub, hfnon⟩ := TreeOk_node_inv hsubtree
        have hlegal : LegalResp q (q.substAns (.node j p)) := LegalResp.node q j p hp
        rw [InP_node σ n q d j p hf hdq]
        refine TreeOk.node γ ⟨0, Nat.succ_pos _⟩ q _ h1
          ⟨[q.substAns (.node j p)], fun r hr => ?_⟩ (fun r _ => ?_) (fun r hr => ?_)
        · by_cases hrm : r = q.substAns (.node j p)
          · rw [hrm]; exact List.mem_cons_self ..
          · exact absurd (if_neg hrm) hr
        · by_cases hrm : r = q.substAns (.node j p)
          · rw [if_pos hrm]
            subst hrm
            refine TreeOk.node _ ⟨j.val + 1, I_index_lt j⟩ p _ ?_ ?_ (fun r' hr' => ?_)
              (fun r' hr' => ?_)
            · rw [Ctx.cons_other _ _ (I_zero_ne_shift σ j), h2 j]
              exact hp
            · obtain ⟨l, hl⟩ := hffin
              refine ⟨l, fun r' hr' => hl r' ?_⟩
              intro hb
              exact hr' (if_pos hb)
            · by_cases hb : hf r' = Tree.bot
              · rw [if_pos hb]; exact TreeOk.leaf _ _
              · rw [if_neg hb]
                refine ih (q.snoc j p r') _ ?_ ?_
                · rw [Ctx.cons_other _ _ fun he => I_zero_ne_shift σ j he.symm,
                    Ctx.cons_self]
                  exact legalQuery_join_snoc q _ j p r' h1 hr'
                · intro i
                  rw [Query.ctx_snoc]
                  by_cases hij : i = j
                  · subst hij
                    rw [Ctx.cons_self, Ctx.cons_other _ _ (I_zero_ne_shift σ i),
                      h2 i, Ctx.cons_self]
                  · rw [Ctx.cons_other _ _ (I_shift_ne σ hij),
                      Ctx.cons_other _ _ (I_zero_ne_shift σ i), h2 i,
                      Ctx.cons_other _ _ (fun he : j = i => hij he.symm)]
            · rw [if_pos (hfnon r' hr')]
          · rw [if_neg hrm]; exact TreeOk.leaf _ _
        · by_cases hrm : r = q.substAns (.node j p)
          · exact absurd (hrm ▸ hlegal) hr
          · exact if_neg hrm

/-- `I_σ` denotes `⊔ {Iₙ(?) | n ∈ ℕ}`. -/
noncomputable def treeI (σ : Ty) : T (σ ⇒ σ) :=
  idealOfChain (fun n => In σ n .hole) fun _ _ h => In_le_of_le σ h .hole

/-! ## Definitions 4.21 and A.3, Claim A.5: the combinator `S`

Definition 4.21 defines `S_{σ,τ,ρ}` as the tree `S(?, ?)` where `S` is given by
the mutual recursion equations of Figure 5, together with the auxiliary
functions `T : R × Q → …` and `encode : D_{σ→τ} × Q_τ → Q_{σ→τ}`.
**Definition A.3** gives the finite approximants `Sₙ` and `Tₙ`, and
**Claim A.5** establishes that they are well formed, so that
`S = ⊔ₙ Sₙ(?,?) ∈ T_{(σ→τ→ρ)→(σ→τ)→σ→ρ}`. -/

/-- The type of the `S` combinator. -/
abbrev STy (σ τ ρ : Ty) : Ty := (σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ

/-- **Definition A.3** (`S`, `T`, `Sₙ`, `Tₙ`) together with **Claim A.5**.

"*The following two statements about `Sₙ` and `Tₙ` both hold: 1. For all `p_S`
and `q₁` satisfying the invariant `Φ`, `Sₙ(p_S, q₁) ∈ D_{(σ→τ→ρ)→(σ→τ)→σ→ρ}(p̂_S)`
… `S = ⊔ₙ {Sₙ(?,?)} ∈ T_{(σ→τ→ρ)→(σ→τ)→σ→ρ}`*"

together with **Lemma A.6**, "*For all `e₁, e₂, e₃` in appropriate domains,
`apply (S(?,?), e₁, e₂, e₃) = apply (apply (e₁, e₃), apply (e₂, e₃))`*".

Packaging the construction of Definition 4.21 and Figure 5 as a single existence
statement lets every use of `S` in the development be a genuine consequence of
Appendix A rather than a further assumption. -/
theorem claim_A_5 (σ τ ρ : Ty) :
    ∃ S : T (STy σ τ ρ), ∀ (e₁ : T (σ ⇒ τ ⇒ ρ)) (e₂ : T (σ ⇒ τ)) (e₃ : T σ),
      applyT (applyT (applyT S e₁) e₂) e₃ = applyT (applyT e₁ e₃) (applyT e₂ e₃) := by
  sorry

/-- `S_{σ,τ,ρ}` denotes the tree `S(?,?)` of Definition 4.21. -/
noncomputable def treeS (σ τ ρ : Ty) : T (STy σ τ ρ) := Classical.choose (claim_A_5 σ τ ρ)

/-! ## `Ω_σ` and the meaning of `Y_σ` (§4.3) -/

/-- `Ω_o = apply (sub1, ⌜0⌝)` and `Ω_{σ→τ} = λ*x^σ . Ω_τ` (§4.3).

"The expression `Ω_σ` has the same meaning (`⊥_σ`) in `T` as the definition for
`Ω` given at the beginning of Section 2, but the new definition does not contain
any occurrences of constants `Y_σ`." -/
def Omega : Ty → Comb SPCF
  | .base => .app (.const .sub1) (.const (.num 0))
  | .arrow a b => Comb.lamStar 0 a (Omega b)

/-- `apply (f, … apply (f, Ω_σ) …)` with `n` occurrences of the variable `f`. -/
def Yunfold (σ : Ty) : Nat → Comb SPCF
  | 0 => Omega σ
  | n + 1 => .app (.var 0 (σ ⇒ σ)) (Yunfold σ n)

/-- `λ*f . apply (f, … apply (f, Ω_σ) …)` with `n` occurrences of `f` (§4.3). -/
def Yapprox (σ : Ty) (n : Nat) : Comb SPCF := Comb.lamStar 0 (σ ⇒ σ) (Yunfold σ n)

/-- `Ω_σ` has type `σ`. -/
theorem hasTy_Omega : ∀ (σ : Ty) (Γ : List (Nat × Ty)), Comb.HasTy Γ (Omega σ) σ
  | .base, Γ => Comb.HasTy.app Comb.HasTy.const Comb.HasTy.const
  | .arrow a b, Γ => Comb.lamStar_hasTy (hasTy_Omega b ((0, a) :: Γ))

theorem hasTy_Yunfold (σ : Ty) : ∀ (n : Nat) (Γ : List (Nat × Ty)),
    Comb.HasTy ((0, σ ⇒ σ) :: Γ) (Yunfold σ n) σ
  | 0, Γ => hasTy_Omega σ _
  | n + 1, Γ =>
      Comb.HasTy.app (Comb.HasTy.var (List.mem_cons_self ..)) (hasTy_Yunfold σ n Γ)

theorem hasTy_Yapprox (σ : Ty) (n : Nat) (Γ : List (Nat × Ty)) :
    Comb.HasTy Γ (Yapprox σ n) ((σ ⇒ σ) ⇒ σ) :=
  Comb.lamStar_hasTy (hasTy_Yunfold σ n Γ)

/-! ## Definition 4.1: the tree model `T` for SPCF -/

/-- The interpretation of the SPCF constants other than `Y_σ`
(Definition 4.19).  Numerals, errors and the primitive functions are the
principal ideals of the corresponding finite trees. -/
noncomputable def interpBase : (c : SConst) → T (SConst.ty c)
  | .num n => Ideal.principal ⟨.leaf (.num n), TreeOk.leaf _ _⟩
  | .err b => Ideal.principal ⟨.leaf (.err b), TreeOk.leaf _ _⟩
  | .add1 => idealOf treeAdd1
  | .sub1 => idealOf treeSub1
  | .if0 => idealOf treeIf0
  | .catchC σ => idealOf (treeCatch σ)
  | .Y _ => ScottDomain.bot

/-- The tree model determined by an interpretation of the SPCF constants.

Every model of Definition 4.1 has the same domains, the same `apply`, and the
same combinators `S`, `K`, `I` — the trees of Definitions 4.20 and 4.21.  Only
the interpretation of the constants of `F` varies, and it varies exactly once:
`T₀` interprets `Y_σ` as `⊥` and is used to give meaning to the `Y`-free
approximants of §4.3, while `T` interprets it by their least upper bound. -/
noncomputable def mkTreeModel (ic : (c : SConst) → T (SConst.ty c)) : Model SPCF where
  Dom := T
  dom σ := inferInstance
  interpConst c := ic c
  interpS σ τ ρ := treeS σ τ ρ
  interpK σ τ := treeK σ τ
  interpI σ := treeI σ
  apply {σ τ} f d := applyT f d

/-- The model `T₀`: `T` with `Y_σ` interpreted as `⊥`.  It is used only to give
meaning to the `Y`-free approximants `Yapprox σ n`, exactly as in §4.3. -/
noncomputable def T0 : Model SPCF := mkTreeModel interpBase

/-! ## Theorem 4.22 and its corollaries -/

/-- **Definition 4.20 for `K`, correctly stated.**

`Kₙ(?)` branches over the infinitely many final answers `a ∈ ℕ`, so it is *not*
an element of the finitary basis `D_{σ→τ→σ}`; `K` is the ideal of the finite
*legal* trees below the chain (`treeK`).  To read the equation
`apply (K, d, e) = d` off Claim A.2 one therefore needs that those finite legal
trees already compute whatever `Kₙ(?)` computes — that they are cofinal for
application.  This is `KnP`, the pruning of `Kₙ(?)` along `d`. -/
theorem Kn_legal_cofinal (σ τ : Ty) (n : Nat) (d : D σ) (e : D τ) (a : D σ)
    (h : Tree.Le a.1 (apply0 (apply0 (Kn σ τ n .hole) d.1) e.1)) :
    ∃ k : D (σ ⇒ τ ⇒ σ), Tree.Le k.1 (Kn σ τ n .hole) ∧
      Tree.Le a.1 (apply0 (apply0 k.1 d.1) e.1) :=
  ⟨⟨KnP σ τ n .hole d.1,
      KnP_ok σ τ d.1 d.2 n .hole Ctx.empty LegalQuery.root fun _ => rfl⟩,
    KnP_le_Kn σ τ n .hole d.1, apply0_KnP_ge σ τ n .hole d.1 e.1 a.1 h⟩

/-- **Lemma A.1.**  *For all `d ∈ T_σ`, `e ∈ T_τ`,
`apply (K_{σ,τ}, d, e) = d`.*

"We will prove this lemma for finite trees and then use a continuity argument to
extend the lemma to all trees."  The finite-tree half is Claim A.2, proved
above; the passage to the ideal completion is here. -/
theorem lemma_A_1 (σ τ : Ty) (d : T σ) (e : T τ) :
    applyT (applyT (treeK σ τ) d) e = d := by
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨m, ⟨k, ⟨n, hk⟩, d0, hd0, hm⟩, e0, _, hc⟩
    have h1 : Tree.Le c.1 (apply0 m.1 e0.1) := hc
    have h3 : Tree.Le (apply0 m.1 e0.1) (apply0 (apply0 k.1 d0.1) e0.1) :=
      apply0_mono_left (show Tree.Le m.1 (apply0 k.1 d0.1) from hm) e0.1
    have h4 : Tree.Le (apply0 (apply0 k.1 d0.1) e0.1)
        (apply0 (apply0 (Kn σ τ n .hole) d0.1) e0.1) :=
      apply0_mono_left (apply0_mono_left (show Tree.Le k.1 (Kn σ τ n .hole) from hk) d0.1) e0.1
    have h5 : Tree.Le (apply0 (apply0 (Kn σ τ n .hole) d0.1) e0.1) d0.1 :=
      claim_A_2_le σ τ n .hole d0.1 e0.1 d0.1 rfl
    exact d.downward c d0 (Tree.Le.trans h1 (Tree.Le.trans h3 (Tree.Le.trans h4 h5))) hd0
  · intro hc
    obtain ⟨e0, he0⟩ := e.nonempty'
    obtain ⟨n, hn⟩ := claim_A_2_ge σ τ (Finitary_of_TreeOk c.2) .hole c.1 e0.1 c.1 rfl
      (Tree.Le.refl _)
    obtain ⟨k, hkle, hka⟩ := Kn_legal_cofinal σ τ n c e0 c hn
    exact ⟨applyD k c, ⟨k, ⟨n, hkle⟩, c, hc, Po.le_refl _⟩, e0, he0, hka⟩

/-- **Definition A.4** (*Error variant*).

"Given a finite tree `d ∈ D_σ` that does not contain any leaves of the form
`error₁` or `error₂`, a finite tree `d' ∈ D_σ` is an `errorᵢ` variant of `d` iff
`d'` is identical to `d` except for one subtree position `q` where
`d' @ q = errorᵢ` but `d @ q ≠ ⊥`." -/
def ErrorVariant {σ : Ty} (b : Bool) (d d' : Tree σ) : Prop :=
  ∃ q : Query σ,
    d'.at' q = some (.leaf (.err b)) ∧ d.at' q ≠ some Tree.bot ∧
    ∀ p : Query σ, (¬ ∃ e, d.at' p = some e ∧ p = q) →
      (d.at' p = none ↔ d'.at' p = none)

/-- **Lemma A.7.**  *Let `p_S` and `q₁` be queries satisfying the invariant `Φ`
and let `e₁, e₂, e₃` be finite elements in appropriate domains such that
`q₁ ⊑ e₁`, … .*

The lemma states that the inputs `e₁, e₂, e₃` "direct the application process
from the root of a tree to the given subtree"; the way it is used in the proof
of Lemma A.6 is that the finite approximants `Sₙ` of Definition A.3 already
satisfy the `S` equation on finite inputs, whence Lemma A.6 follows by
continuity of `apply`. -/
theorem lemma_A_7 (σ τ ρ : Ty) :
    ∃ Sn : Nat → Tree (STy σ τ ρ),
      (∀ n, Sn n ⊑ Sn (n + 1)) ∧
      ∀ (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ),
        ∃ n, apply0 (apply0 (apply0 (Sn n) e₁) e₂) e₃
              = apply0 (apply0 e₁ e₃) (apply0 e₂ e₃) := by
  sorry

/-- **Lemma A.6.**  *For all `e₁, e₂, e₃` in appropriate domains,
`apply (S(?,?), e₁, e₂, e₃) = apply (apply (e₁, e₃), apply (e₂, e₃))`.*

An immediate consequence of Claim A.5. -/
theorem lemma_A_6 (σ τ ρ : Ty) (e₁ : T (σ ⇒ τ ⇒ ρ)) (e₂ : T (σ ⇒ τ)) (e₃ : T σ) :
    applyT (applyT (applyT (treeS σ τ ρ) e₁) e₂) e₃
      = applyT (applyT e₁ e₃) (applyT e₂ e₃) :=
  Classical.choose_spec (claim_A_5 σ τ ρ) e₁ e₂ e₃

/-- The `I` analogue of `Kn_legal_cofinal`: the finite legal trees below the
chain `Iₙ(?)` are cofinal for application. -/
theorem In_legal_cofinal (σ : Ty) (n : Nat) (d : D σ) (a : D σ)
    (h : Tree.Le a.1 (apply0 (In σ n .hole) d.1)) :
    ∃ k : D (σ ⇒ σ), Tree.Le k.1 (In σ n .hole) ∧ Tree.Le a.1 (apply0 k.1 d.1) :=
  ⟨⟨InP σ n .hole d.1, InP_ok σ d.1 d.2 n .hole Ctx.empty LegalQuery.root fun _ => rfl⟩,
    InP_le_In σ n .hole d.1, apply0_InP_ge σ n .hole d.1 a.1 h⟩

/-- The `(I)` equation of Theorem 4.22; "the proof for `I` closely follows the
proof for `K`". -/
theorem theorem_4_22_I : ∀ (σ : Ty) (x : T σ), applyT (treeI σ) x = x := by
  intro σ x
  apply Ideal.ext
  intro c
  constructor
  · rintro ⟨k, ⟨n, hk⟩, d0, hd0, hc⟩
    refine x.downward c d0 (Tree.Le.trans (show Tree.Le c.1 (apply0 k.1 d0.1) from hc) ?_) hd0
    exact Tree.Le.trans (apply0_mono_left (show Tree.Le k.1 (In σ n .hole) from hk) d0.1)
      (claim_I_le σ n .hole d0.1 d0.1 rfl)
  · intro hc
    obtain ⟨n, hn⟩ := claim_I_ge σ (Finitary_of_TreeOk c.2) .hole c.1 c.1 rfl (Tree.Le.refl _)
    obtain ⟨k, hkle, hka⟩ := In_legal_cofinal σ n c c hn
    exact ⟨k, ⟨n, hkle⟩, c, hc, hka⟩

/-- **Theorem 4.22.**  *Let `x, y, z` be variables ranging over arbitrary
elements in appropriate domains.  Then*

```
apply (S, x, y, z) = apply (apply (x, z), apply (y, z))     (S)
apply (K, x, y)    = x                                     (K)
apply (I, x)       = x                                     (I)
```
-/
theorem theorem_4_22 :
    (∀ (σ τ ρ : Ty) (x : T (σ ⇒ τ ⇒ ρ)) (y : T (σ ⇒ τ)) (z : T σ),
      applyT (applyT (applyT (treeS σ τ ρ) x) y) z = applyT (applyT x z) (applyT y z)) ∧
    (∀ (σ τ : Ty) (x : T σ) (y : T τ), applyT (applyT (treeK σ τ) x) y = x) ∧
    (∀ (σ : Ty) (x : T σ), applyT (treeI σ) x = x) :=
  ⟨lemma_A_6, lemma_A_1, theorem_4_22_I⟩

/-- **The abstraction lemma**: `λ*` really does denote abstraction.

`apply (T[[λ*y . P]]_E, x) = T[[P]]_{E[y := x]}`.  It is proved by the same
combinatory-logic induction as `beta_law`, driven by the `(S)`, `(K)` and `(I)`
equations of Theorem 4.22, and it is what makes the `η` law and the
compositionality of `T` work. -/
theorem lamStar_apply' (ic : (c : SConst) → T (SConst.ty c)) (E : (mkTreeModel ic).Env) (y : Nat) (σ : Ty) (x : T σ) :
    ∀ (P : Comb SPCF) (ρ : Ty) (Γ : List (Nat × Ty)), Comb.HasTy ((y, σ) :: Γ) P ρ →
      applyT ((mkTreeModel ic).combMeaning E (Comb.lamStar y σ P) (σ ⇒ ρ)) x
        = (mkTreeModel ic).combMeaning (Model.envUpdate E y σ x) P ρ := by
  intro P
  induction P with
  | var z ν =>
    intro ρ Γ h
    cases h with
    | var hmem =>
      by_cases hz : z = y ∧ ν = σ
      · obtain ⟨rfl, rfl⟩ := hz
        rw [show Comb.lamStar z ν (Comb.var z ν : Comb SPCF) = .I ν by simp [Comb.lamStar],
          Model.combMeaning_I, Model.combMeaning_var, Model.envUpdate_self]
        exact theorem_4_22_I ν x
      · rw [show Comb.lamStar y σ (Comb.var z ν : Comb SPCF) = .app (.K ν σ) (.var z ν) by
            simp only [Comb.lamStar, if_neg hz],
          Model.combMeaning_app, show Comb.tyOf (Comb.var z ν : Comb SPCF) = ν from rfl,
          Model.combMeaning_K, Model.combMeaning_var, Model.combMeaning_var,
          Model.envUpdate_other E y σ x z ν hz]
        exact lemma_A_1 ν σ (E z ν) x
  | const c =>
    intro ρ Γ h
    cases h with
    | const =>
      rw [show Comb.lamStar y σ (Comb.const c : Comb SPCF)
            = .app (.K (SPCF.constTy c) σ) (.const c) from rfl,
        Model.combMeaning_app, show Comb.tyOf (Comb.const c : Comb SPCF)
          = SPCF.constTy c from rfl,
        Model.combMeaning_K, Model.combMeaning_const, Model.combMeaning_const]
      exact lemma_A_1 _ σ ((mkTreeModel ic).interpConst c) x
  | S a b c =>
    intro ρ Γ h
    cases h with
    | S =>
      rw [show Comb.lamStar y σ (Comb.S a b c : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.S a b c : Comb SPCF)) σ) (.S a b c) from rfl,
        Model.combMeaning_app, show Comb.tyOf (Comb.S a b c : Comb SPCF)
          = ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c) from rfl,
        Model.combMeaning_K, Model.combMeaning_S, Model.combMeaning_S]
      exact lemma_A_1 _ σ ((mkTreeModel ic).interpS a b c) x
  | K a b =>
    intro ρ Γ h
    cases h with
    | K =>
      rw [show Comb.lamStar y σ (Comb.K a b : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.K a b : Comb SPCF)) σ) (.K a b) from rfl,
        Model.combMeaning_app, show Comb.tyOf (Comb.K a b : Comb SPCF) = (a ⇒ b ⇒ a) from rfl,
        Model.combMeaning_K, Model.combMeaning_K, Model.combMeaning_K]
      exact lemma_A_1 _ σ ((mkTreeModel ic).interpK a b) x
  | I a =>
    intro ρ Γ h
    cases h with
    | I =>
      rw [show Comb.lamStar y σ (Comb.I a : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.I a : Comb SPCF)) σ) (.I a) from rfl,
        Model.combMeaning_app, show Comb.tyOf (Comb.I a : Comb SPCF) = (a ⇒ a) from rfl,
        Model.combMeaning_K, Model.combMeaning_I, Model.combMeaning_I]
      exact lemma_A_1 _ σ ((mkTreeModel ic).interpI a) x
  | app P₁ P₂ ih₁ ih₂ =>
    intro ρ Γ h
    cases h with
    | app hP₁ hP₂ =>
      rename_i α
      have e₂ : Comb.tyOf P₂ = α := Comb.tyOf_of_hasTy hP₂
      have eρ : Comb.tyOf (Comb.app P₁ P₂ : Comb SPCF) = ρ :=
        Comb.tyOf_of_hasTy (Comb.HasTy.app hP₁ hP₂)
      have hl₁ : Comb.tyOf (Comb.lamStar y σ P₁) = (σ ⇒ α ⇒ ρ) :=
        Comb.tyOf_of_hasTy (Comb.lamStar_hasTy hP₁)
      have hl₂ : Comb.tyOf (Comb.lamStar y σ P₂) = (σ ⇒ α) :=
        Comb.tyOf_of_hasTy (Comb.lamStar_hasTy hP₂)
      rw [show Comb.lamStar y σ (Comb.app P₁ P₂)
            = .app (.app (.S σ (Comb.tyOf P₂) (Comb.tyOf (Comb.app P₁ P₂)))
                (Comb.lamStar y σ P₁)) (Comb.lamStar y σ P₂) from rfl,
        e₂, eρ, Model.combMeaning_app, hl₂, Model.combMeaning_app, hl₁, Model.combMeaning_S,
        Model.combMeaning_app, e₂]
      have hS := lemma_A_6 σ α ρ ((mkTreeModel ic).combMeaning E (Comb.lamStar y σ P₁) (σ ⇒ α ⇒ ρ))
        ((mkTreeModel ic).combMeaning E (Comb.lamStar y σ P₂) (σ ⇒ α)) x
      show applyT (applyT (applyT (treeS σ α ρ) _) _) _ = _
      rw [hS, ih₁ (α ⇒ ρ) Γ hP₁, ih₂ α Γ hP₂]
      rfl

/-- `Ω_σ` denotes `⊥`.

"The expression `Ω_σ` has the same meaning (`⊥_σ`) in `T` as the definition for
`Ω` given at the beginning of Section 2, but the new definition does not contain
any occurrences of constants `Y_σ`" (§4.3). -/
theorem meaning_Omega (ic : (c : SConst) → T (SConst.ty c))
    (hsub1 : ic .sub1 = interpBase .sub1) (hnum : ic (.num 0) = interpBase (.num 0)) :
    ∀ (σ : Ty) (E : (mkTreeModel ic).Env),
      (mkTreeModel ic).combMeaning E (Omega σ) σ = Ideal.principal (DSub.bot : D σ)
  | .base, E => by
      have h1 : (mkTreeModel ic).combMeaning E (Comb.const SConst.sub1) (𝕆 ⇒ 𝕆)
          = idealOf treeSub1 :=
        (Model.combMeaning_const (M := mkTreeModel ic) E SConst.sub1).trans hsub1
      have h2 : (mkTreeModel ic).combMeaning E (Comb.const (SConst.num 0)) 𝕆
          = Ideal.principal ⟨.leaf (.num 0), TreeOk.leaf _ _⟩ :=
        (Model.combMeaning_const (M := mkTreeModel ic) E (SConst.num 0)).trans hnum
      show applyT ((mkTreeModel ic).combMeaning E (Comb.const SConst.sub1) (𝕆 ⇒ 𝕆))
        ((mkTreeModel ic).combMeaning E (Comb.const (SConst.num 0)) 𝕆) = _
      rw [h1, h2]
      -- every finite approximation of `apply (sub1, ⌜0⌝)` is below `⊥`
      refine Po.le_antisymm ?_ (principal_bot_le _)
      rintro c ⟨f, hf, d, hd, hc⟩
      have hstep : apply0 f.1 d.1 ⊑ (Tree.bot : Tree 𝕆) := by
        rw [show (Tree.bot : Tree 𝕆) = apply0 treeSub1 (.leaf (.num 0)) from rfl]
        exact Po.le_trans (apply0_mono_left (show Tree.Le f.1 treeSub1 from hf) d.1)
          (apply0_mono_right treeSub1 (show Tree.Le d.1 (.leaf (.num 0)) from hd))
      exact Po.le_trans (show c.1 ⊑ apply0 f.1 d.1 from hc) hstep
  | .arrow a b, E => by
      show (mkTreeModel ic).combMeaning E (Comb.lamStar 0 a (Omega b)) (a ⇒ b) = _
      rw [← bot_eq_principal (a ⇒ b)]
      refine theorem_4_11.2 a b _ _ fun x => ?_
      rw [show applyT ((mkTreeModel ic).combMeaning E (Comb.lamStar 0 a (Omega b)) (a ⇒ b)) x
          = (mkTreeModel ic).combMeaning (Model.envUpdate E 0 a x) (Omega b) b from
        lamStar_apply' ic E 0 a x (Omega b) b [] (hasTy_Omega b _),
        meaning_Omega ic hsub1 hnum b _, applyT_bot a b x]

/-- The approximants to `Y_σ` form a chain: the meaning of `Yunfold` is monotone
in the number of unfoldings. -/
theorem Yunfold_mono (ic : (c : SConst) → T (SConst.ty c))
    (hsub1 : ic .sub1 = interpBase .sub1) (hnum : ic (.num 0) = interpBase (.num 0))
    (σ : Ty) : ∀ (n : Nat) (E : (mkTreeModel ic).Env),
      (mkTreeModel ic).combMeaning E (Yunfold σ n) σ
        ⊑ (mkTreeModel ic).combMeaning E (Yunfold σ (n + 1)) σ := by
  intro n
  induction n with
  | zero =>
    intro E
    rw [show Yunfold σ 0 = Omega σ from rfl, meaning_Omega ic hsub1 hnum σ E]
    exact principal_bot_le _
  | succ n ih =>
    intro E
    have hty : Comb.tyOf (Yunfold σ n) = σ := Comb.tyOf_of_hasTy (hasTy_Yunfold σ n [])
    have hty' : Comb.tyOf (Yunfold σ (n + 1)) = σ :=
      Comb.tyOf_of_hasTy (hasTy_Yunfold σ (n + 1) [])
    show (mkTreeModel ic).combMeaning E (.app (.var 0 (σ ⇒ σ)) (Yunfold σ n)) σ
      ⊑ (mkTreeModel ic).combMeaning E (.app (.var 0 (σ ⇒ σ)) (Yunfold σ (n + 1))) σ
    rw [Model.combMeaning_app, hty, Model.combMeaning_app, hty']
    exact applyT_mono_right _ (ih E)

theorem Yapprox_mono (ic : (c : SConst) → T (SConst.ty c))
    (hsub1 : ic .sub1 = interpBase .sub1) (hnum : ic (.num 0) = interpBase (.num 0))
    (σ : Ty) (E : (mkTreeModel ic).Env) : ∀ m n : Nat, m ≤ n →
      (mkTreeModel ic).combMeaning E (Yapprox σ m) ((σ ⇒ σ) ⇒ σ)
        ⊑ (mkTreeModel ic).combMeaning E (Yapprox σ n) ((σ ⇒ σ) ⇒ σ) := by
  have step : ∀ n : Nat,
      (mkTreeModel ic).combMeaning E (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)
        ⊑ (mkTreeModel ic).combMeaning E (Yapprox σ (n + 1)) ((σ ⇒ σ) ⇒ σ) := by
    intro n
    refine orderExtensional_T _ _ fun x => ?_
    rw [show applyT ((mkTreeModel ic).combMeaning E (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) x
        = (mkTreeModel ic).combMeaning (Model.envUpdate E 0 (σ ⇒ σ) x) (Yunfold σ n) σ from
      lamStar_apply' ic E 0 (σ ⇒ σ) x (Yunfold σ n) σ [] (hasTy_Yunfold σ n []),
      show applyT ((mkTreeModel ic).combMeaning E (Yapprox σ (n + 1)) ((σ ⇒ σ) ⇒ σ)) x
        = (mkTreeModel ic).combMeaning (Model.envUpdate E 0 (σ ⇒ σ) x) (Yunfold σ (n + 1)) σ from
      lamStar_apply' ic E 0 (σ ⇒ σ) x (Yunfold σ (n + 1)) σ [] (hasTy_Yunfold σ (n + 1) [])]
    exact Yunfold_mono ic hsub1 hnum σ n _
  intro m n h
  induction h with
  | refl => exact Po.le_refl _
  | step _ ih => exact Po.le_trans ih (step _)

/-- `T[[Y_σ]] = ⊔ {T[[λ*f . apply (f, … apply (f, Ω) …)]] | n ∈ ℕ}` (§4.3).

"It is easy to prove that the set … forms a chain by induction on `n` (since
`T[[apply]]` is monotonic).  Hence, the specified least upper bound exists." -/
theorem Y_chain_directed (σ : Ty) :
    DirectedSet (Set.range fun n => T0.combMeaning (fun _ _ => ScottDomain.bot)
      (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) :=
  chain_directed _ (Yapprox_mono interpBase rfl rfl σ (fun _ _ => ScottDomain.bot))

/-- `T[[Y_σ]]`. -/
noncomputable def interpY (σ : Ty) : T ((σ ⇒ σ) ⇒ σ) :=
  ScottDomain.dsup _ (Y_chain_directed σ)

/-- `mⁿ(⊥)`, the `n`-th approximation to the least fixed point of `m`. -/
noncomputable def Yiter (σ : Ty) (m : T (σ ⇒ σ)) (n : Nat) : T σ :=
  (mkTreeModel interpBase).combMeaning
    (Model.envUpdate (fun _ _ => ScottDomain.bot) 0 (σ ⇒ σ) m) (Yunfold σ n) σ

theorem Yiter_zero (σ : Ty) (m : T (σ ⇒ σ)) :
    Yiter σ m 0 = Ideal.principal (DSub.bot : D σ) :=
  meaning_Omega interpBase rfl rfl σ _

theorem Yiter_succ (σ : Ty) (m : T (σ ⇒ σ)) (n : Nat) :
    Yiter σ m (n + 1) = applyT m (Yiter σ m n) := by
  have hty : Comb.tyOf (Yunfold σ n) = σ := Comb.tyOf_of_hasTy (hasTy_Yunfold σ n [])
  show (mkTreeModel interpBase).combMeaning _ (.app (.var 0 (σ ⇒ σ)) (Yunfold σ n)) σ = _
  rw [Model.combMeaning_app, hty, Model.combMeaning_var, Model.envUpdate_self]
  rfl

/-- The `n`-th approximant of `Y_σ`, applied to `m`, is `mⁿ(⊥)`. -/
theorem applyT_Yapprox (σ : Ty) (m : T (σ ⇒ σ)) (n : Nat) :
    applyT ((mkTreeModel interpBase).combMeaning (fun _ _ => ScottDomain.bot)
      (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) m = Yiter σ m n :=
  lamStar_apply' interpBase _ 0 (σ ⇒ σ) m (Yunfold σ n) σ [] (hasTy_Yunfold σ n [])

/-- `apply (Y_σ, m) = ⊔ₙ mⁿ(⊥)`. -/
theorem mem_applyT_interpY (σ : Ty) (m : T (σ ⇒ σ)) (c : D σ) :
    c ∈ applyT (interpY σ) m ↔ ∃ n, c ∈ Yiter σ m n := by
  constructor
  · rintro ⟨f, ⟨F, ⟨n, rfl⟩, hfF⟩, d, hd, hc⟩
    exact ⟨n, (applyT_Yapprox σ m n) ▸ (⟨f, hfF, d, hd, hc⟩ :
      c ∈ applyT ((mkTreeModel interpBase).combMeaning (fun _ _ => ScottDomain.bot)
        (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) m)⟩
  · rintro ⟨n, hn⟩
    have hn' : c ∈ applyT ((mkTreeModel interpBase).combMeaning (fun _ _ => ScottDomain.bot)
        (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) m := (applyT_Yapprox σ m n) ▸ hn
    obtain ⟨f, hfF, d, hd, hc⟩ := hn'
    exact ⟨f, ⟨_, ⟨n, rfl⟩, hfF⟩, d, hd, hc⟩

/-- `Y_σ` yields a fixed point: `apply (m, apply (Y_σ, m)) = apply (Y_σ, m)`.

`apply (Y_σ, m) = ⊔ₙ mⁿ(⊥)`, and applying `m` shifts the chain by one, which
leaves the least upper bound unchanged because `m⁰(⊥) = ⊥`. -/
theorem applyT_interpY_fix (σ : Ty) (m : T (σ ⇒ σ)) :
    applyT m (applyT (interpY σ) m) = applyT (interpY σ) m := by
  refine Po.le_antisymm ?_ ?_
  · rintro c ⟨f, hf, d, hd, hc⟩
    obtain ⟨n, hn⟩ := (mem_applyT_interpY σ m d).mp hd
    refine (mem_applyT_interpY σ m c).mpr ⟨n + 1, ?_⟩
    rw [Yiter_succ]
    exact (applyT m (Yiter σ m n)).downward c (applyD f d) hc ⟨f, hf, d, hn, Po.le_refl _⟩
  · intro c hc
    obtain ⟨n, hn⟩ := (mem_applyT_interpY σ m c).mp hc
    cases n with
    | zero =>
      rw [Yiter_zero] at hn
      exact principal_bot_le _ c hn
    | succ n =>
      rw [Yiter_succ] at hn
      obtain ⟨f, hf, d, hd, hcd⟩ := hn
      exact ⟨f, hf, d, (mem_applyT_interpY σ m d).mpr ⟨n, hd⟩, hcd⟩

/-- **Definition 4.1** (*Tree model for SPCF*).

"`T` is the model for SPCF mapping: (1) each type `σ` to the tree domain `T_σ`;
(2) each constant `c` in `O ∪ F` to the tree defined in Section 4.3; and (3) the
function symbols `apply_{σ,τ}` to the functions `T[[apply_{σ,τ}]]`." -/
noncomputable def Tmodel : Model SPCF :=
  mkTreeModel fun c =>
    match c with
    | .Y σ => interpY σ
    | c' => interpBase c'

@[inherit_doc] scoped notation:max "T⟦" M "⟧" E => Model.meaning Tmodel E M

/-- The abstraction lemma for the tree model `T` itself. -/
theorem lamStar_apply (E : Tmodel.Env) (y : Nat) (σ : Ty) (x : T σ) :
    ∀ (P : Comb SPCF) (ρ : Ty) (Γ : List (Nat × Ty)), Comb.HasTy ((y, σ) :: Γ) P ρ →
      applyT (Tmodel.combMeaning E (Comb.lamStar y σ P) (σ ⇒ ρ)) x
        = Tmodel.combMeaning (Model.envUpdate E y σ x) P ρ :=
  lamStar_apply' _ E y σ x

/-- The `β` half of **Corollary 4.23**, in the form used by the induction.

"Both equations can be proved using standard methods"; this is the usual
combinatory-logic argument, driven by the `(S)`, `(K)` and `(I)` equations of
Theorem 4.22. -/
theorem beta_law (E : Tmodel.Env) (Γ : List (Nat × Ty)) (y : Nat) (σ : Ty)
    (N : Comb SPCF) (hN : Comb.HasTy Γ N σ) :
    ∀ (M : Comb SPCF) (ρ : Ty), Comb.HasTy ((y, σ) :: Γ) M ρ →
      Tmodel.combMeaning E (.app (Comb.lamStar y σ M) N) ρ
        = Tmodel.combMeaning E (Comb.subst y σ N M) ρ := by
  have hNty : Comb.tyOf N = σ := Comb.tyOf_of_hasTy hN
  intro M
  induction M with
  | var z ν =>
    intro ρ h
    cases h with
    | var hmem =>
      by_cases hz : z = y ∧ ν = σ
      · obtain ⟨rfl, rfl⟩ := hz
        rw [show Comb.lamStar z ν (Comb.var z ν : Comb SPCF) = .I ν by simp [Comb.lamStar],
          show Comb.subst z ν N (Comb.var z ν : Comb SPCF) = N by simp [Comb.subst]]
        rw [Model.combMeaning_app, hNty, Model.combMeaning_I]
        exact theorem_4_22_I ν (Tmodel.combMeaning E N ν)
      · rw [show Comb.lamStar y σ (Comb.var z ν : Comb SPCF) = .app (.K ν σ) (.var z ν) by
            simp only [Comb.lamStar, if_neg hz],
          show Comb.subst y σ N (Comb.var z ν : Comb SPCF) = .var z ν by
            simp only [Comb.subst, if_neg hz]]
        rw [Model.combMeaning_app, hNty, Model.combMeaning_app,
          show Comb.tyOf (Comb.var z ν : Comb SPCF) = ν from rfl,
          Model.combMeaning_K, Model.combMeaning_var]
        exact lemma_A_1 ν σ (E z ν) (Tmodel.combMeaning E N σ)
  | const c =>
    intro ρ h
    cases h with
    | const =>
      rw [show Comb.lamStar y σ (Comb.const c : Comb SPCF)
            = .app (.K (SPCF.constTy c) σ) (.const c) from rfl,
        show Comb.subst y σ N (Comb.const c : Comb SPCF) = .const c from rfl]
      rw [Model.combMeaning_app, hNty, Model.combMeaning_app,
        show Comb.tyOf (Comb.const c : Comb SPCF) = SPCF.constTy c from rfl,
        Model.combMeaning_K, Model.combMeaning_const]
      exact lemma_A_1 _ σ (Tmodel.interpConst c) (Tmodel.combMeaning E N σ)
  | S a b c =>
    intro ρ h
    cases h with
    | S =>
      rw [show Comb.lamStar y σ (Comb.S a b c : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.S a b c : Comb SPCF)) σ) (.S a b c) from rfl,
        show Comb.subst y σ N (Comb.S a b c : Comb SPCF) = .S a b c from rfl]
      rw [Model.combMeaning_app, hNty, Model.combMeaning_app,
        show Comb.tyOf (Comb.S a b c : Comb SPCF)
          = ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c) from rfl,
        Model.combMeaning_K, Model.combMeaning_S]
      exact lemma_A_1 _ σ (Tmodel.interpS a b c) (Tmodel.combMeaning E N σ)
  | K a b =>
    intro ρ h
    cases h with
    | K =>
      rw [show Comb.lamStar y σ (Comb.K a b : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.K a b : Comb SPCF)) σ) (.K a b) from rfl,
        show Comb.subst y σ N (Comb.K a b : Comb SPCF) = .K a b from rfl]
      rw [Model.combMeaning_app, hNty, Model.combMeaning_app,
        show Comb.tyOf (Comb.K a b : Comb SPCF) = (a ⇒ b ⇒ a) from rfl,
        Model.combMeaning_K, Model.combMeaning_K]
      exact lemma_A_1 _ σ (Tmodel.interpK a b) (Tmodel.combMeaning E N σ)
  | I a =>
    intro ρ h
    cases h with
    | I =>
      rw [show Comb.lamStar y σ (Comb.I a : Comb SPCF)
            = .app (.K (Comb.tyOf (Comb.I a : Comb SPCF)) σ) (.I a) from rfl,
        show Comb.subst y σ N (Comb.I a : Comb SPCF) = .I a from rfl]
      rw [Model.combMeaning_app, hNty, Model.combMeaning_app,
        show Comb.tyOf (Comb.I a : Comb SPCF) = (a ⇒ a) from rfl,
        Model.combMeaning_K, Model.combMeaning_I]
      exact lemma_A_1 _ σ (Tmodel.interpI a) (Tmodel.combMeaning E N σ)
  | app M₁ M₂ ih₁ ih₂ =>
    intro ρ h
    cases h with
    | app hM₁ hM₂ =>
      rename_i α
      have e₂ : Comb.tyOf M₂ = α := Comb.tyOf_of_hasTy hM₂
      have eρ : Comb.tyOf (Comb.app M₁ M₂ : Comb SPCF) = ρ :=
        Comb.tyOf_of_hasTy (Comb.HasTy.app hM₁ hM₂)
      have hl₁ : Comb.tyOf (Comb.lamStar y σ M₁) = (σ ⇒ α ⇒ ρ) :=
        Comb.tyOf_of_hasTy (Comb.lamStar_hasTy hM₁)
      have hl₂ : Comb.tyOf (Comb.lamStar y σ M₂) = (σ ⇒ α) :=
        Comb.tyOf_of_hasTy (Comb.lamStar_hasTy hM₂)
      have hs₂ : Comb.tyOf (Comb.subst y σ N M₂) = α :=
        Comb.tyOf_of_hasTy (Comb.subst_hasTy hN hM₂)
      -- unfold the left-hand side down to the `(S)` equation
      rw [show Comb.lamStar y σ (Comb.app M₁ M₂)
            = .app (.app (.S σ (Comb.tyOf M₂) (Comb.tyOf (Comb.app M₁ M₂)))
                (Comb.lamStar y σ M₁)) (Comb.lamStar y σ M₂) from rfl,
        e₂, eρ]
      rw [Model.combMeaning_app, hNty, Model.combMeaning_app, hl₂,
        Model.combMeaning_app, hl₁, Model.combMeaning_S]
      -- the right-hand side
      rw [show Comb.subst y σ N (Comb.app M₁ M₂)
            = .app (Comb.subst y σ N M₁) (Comb.subst y σ N M₂) from rfl,
        Model.combMeaning_app, hs₂]
      -- apply the `(S)` equation and the two induction hypotheses
      have hS := lemma_A_6 σ α ρ (Tmodel.combMeaning E (Comb.lamStar y σ M₁) (σ ⇒ α ⇒ ρ))
        (Tmodel.combMeaning E (Comb.lamStar y σ M₂) (σ ⇒ α)) (Tmodel.combMeaning E N σ)
      have h₁ := ih₁ (α ⇒ ρ) hM₁
      have h₂ := ih₂ α hM₂
      rw [Model.combMeaning_app, hNty] at h₁
      rw [Model.combMeaning_app, hNty] at h₂
      have h₁' : applyT (Tmodel.combMeaning E (Comb.lamStar y σ M₁) (σ ⇒ α ⇒ ρ))
          (Tmodel.combMeaning E N σ)
          = Tmodel.combMeaning E (Comb.subst y σ N M₁) (α ⇒ ρ) := h₁
      have h₂' : applyT (Tmodel.combMeaning E (Comb.lamStar y σ M₂) (σ ⇒ α))
          (Tmodel.combMeaning E N σ)
          = Tmodel.combMeaning E (Comb.subst y σ N M₂) α := h₂
      show applyT (applyT (applyT (treeS σ α ρ) _) _) _ = _
      rw [hS, h₁', h₂']
      rfl

/-- **Corollary 4.23** (`β`, `η`).

The well-typedness hypotheses render Definition 2.2's "and the type constraints
of typed λ-calculus"; without them the equations fail, because `combMeaning`
returns `⊥` at a type a term does not have.

"(i) If `E` is an environment that binds each variable `x^σ` in
`FV(M) ∪ FV(N)` to an element in `T_σ`, then
`T[[apply (λ*y . M, N)]]_E = T[[M[y := N]]]_E`.  (ii) … then
`T[[λ*y . apply (M, y)]]_E = T[[M]]_E` (if `y ∉ FV(M)`)."

"Both equations can be proved using standard methods; the proof of (η) depends
on the extensionality theorem (Theorem 4.11)." -/
theorem corollary_4_23 :
    (∀ (E : Tmodel.Env) (Γ : List (Nat × Ty)) (y : Nat) (σ ρ : Ty) (M N : Comb SPCF),
      Comb.HasTy ((y, σ) :: Γ) M ρ → Comb.HasTy Γ N σ →
      Tmodel.combMeaning E (.app (Comb.lamStar y σ M) N) ρ
        = Tmodel.combMeaning E (Comb.subst y σ N M) ρ) ∧
    (∀ (E : Tmodel.Env) (Γ : List (Nat × Ty)) (y : Nat) (σ τ : Ty) (M : Comb SPCF),
      Comb.HasTy Γ M (σ ⇒ τ) → (y, σ) ∉ Comb.FV M →
      Tmodel.combMeaning E (Comb.lamStar y σ (.app M (.var y σ))) (σ ⇒ τ)
        = Tmodel.combMeaning E M (σ ⇒ τ)) := by
  refine ⟨fun E Γ y σ ρ M N hM hN => beta_law E Γ y σ N hN M ρ hM, ?_⟩
  intro E Γ y σ τ M hM hy
  -- by extensionality it suffices to compare the two applications
  refine theorem_4_11.2 σ τ _ _ fun x => ?_
  have hty : Comb.HasTy ((y, σ) :: Γ) (Comb.app M (.var y σ)) τ :=
    Comb.HasTy.app (Comb.weaken_cons (y, σ) hM) (Comb.HasTy.var (List.mem_cons_self ..))
  rw [lamStar_apply E y σ x _ τ Γ hty, Model.combMeaning_app,
    show Comb.tyOf (Comb.var y σ : Comb SPCF) = σ from rfl,
    Model.combMeaning_var, Model.envUpdate_self]
  -- the update is invisible to `M`, which does not contain `y^σ`
  have hcongr : Tmodel.combMeaning (Model.envUpdate E y σ x) M (σ ⇒ τ)
      = Tmodel.combMeaning E M (σ ⇒ τ) := by
    refine Model.combMeaning_congr_env _ _ M (σ ⇒ τ) fun z ν hz => ?_
    refine Model.envUpdate_other E y σ x z ν ?_
    rintro ⟨rfl, rfl⟩
    exact hy hz
  rw [hcongr]
  rfl

/-- **Corollary 4.24** (`Y` operator).  *For all closed combinatory terms `M` of
type `σ → σ`, `T[[apply (M, apply (Y_σ, M))]] = T[[apply (Y_σ, M)]]`.* -/
theorem corollary_4_24 (σ : Ty) (M : Comb SPCF) (E : Tmodel.Env)
    (hM : Comb.HasTy [] M (σ ⇒ σ)) :
    Tmodel.combMeaning E (.app M (.app (.const (.Y σ)) M)) σ
      = Tmodel.combMeaning E (.app (.const (.Y σ)) M) σ := by
  have hMty : Comb.tyOf M = (σ ⇒ σ) := Comb.tyOf_of_hasTy hM
  have hYc : Tmodel.combMeaning E (Comb.const (SConst.Y σ)) ((σ ⇒ σ) ⇒ σ) = interpY σ :=
    Model.combMeaning_const (M := Tmodel) E (SConst.Y σ)
  have hY : Tmodel.combMeaning E (.app (.const (.Y σ)) M) σ
      = applyT (interpY σ) (Tmodel.combMeaning E M (σ ⇒ σ)) := by
    rw [Model.combMeaning_app, hMty, hYc]
    rfl
  have hOuter : Tmodel.combMeaning E (.app M (.app (.const (.Y σ)) M)) σ
      = applyT (Tmodel.combMeaning E M (σ ⇒ σ))
          (Tmodel.combMeaning E (.app (.const (.Y σ)) M) σ) := by
    rw [Model.combMeaning_app,
      show Comb.tyOf (Comb.app (Comb.const (SConst.Y σ)) M : Comb SPCF) = σ from rfl]
    rfl
  rw [hOuter, hY]
  exact applyT_interpY_fix σ _

end FA
