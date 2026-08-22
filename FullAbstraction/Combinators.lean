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

section SCombinator
variable {σ τ ρ : Ty}

/-- The unique proper branch of a branching function, when there is one
(Figure 5, fact 1: "the approximation `d₂` has exactly one son below each node
value of the form `⟨1,p⟩`"). -/
noncomputable def properBranch {γ δ : Ty} (f : Resp γ → Tree δ) : Resp γ :=
  @dite _ _ (Classical.propDecidable _)
    (fun h : ∃ r, f r ≠ Tree.bot => Classical.choose h) (fun _ => .ans 0)

/-- Figure 5's `encode : D_{σ→τ} × Q_τ → Q_{σ→τ}`: reconstruct the query about
`y` corresponding to a query about `y·z`, threading it through the accumulated
knowledge `d₂` — replay `d₂`'s probes of `z` (each has a unique recorded
answer), and step through its other nodes as the query dictates. -/
noncomputable def encode : Tree (σ ⇒ τ) → Query τ → Query (σ ⇒ τ)
  | .leaf _, _ => .hole
  | .node ⟨0, h0⟩ qz f, p =>
      .step ⟨0, h0⟩ qz (properBranch f) (encode (f (properBranch f)) p)
  | .node ⟨_ + 1, _⟩ _ _, .hole => .hole
  | .node ⟨j + 1, hj⟩ qt f, .step i p' r rest =>
      if h : (⟨i, p'⟩ : NodeVal τ) = ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, qt⟩ then
        .step ⟨j + 1, hj⟩ qt
          (Tree.castResp (congrArg Sigma.fst h) r
            : Resp (τ.arg ⟨j, Nat.lt_of_succ_lt_succ hj⟩))
          (encode (f (Tree.castResp (congrArg Sigma.fst h) r
            : Resp (τ.arg ⟨j, Nat.lt_of_succ_lt_succ hj⟩))) rest)
      else .hole

mutual
/-- **Definition A.3 / Figure 8**, the generating function `Sₙ` in state-passing
form: the paper's path argument `p_S` is replaced by the data actually consulted
— the current query `q₁` on argument 1 (the paper's redundant second argument)
and the approximation trees `d₂ = ⊔ĉp_S(2)`, `d₃ = ⊔ĉp_S(3)` of arguments 2
and 3, which the tree-context reading of Definition 4.2 provides directly. -/
noncomputable def Sfun : Nat → Query (σ ⇒ τ ⇒ ρ) → Tree (σ ⇒ τ) → Tree σ →
    Tree (STy σ τ ρ)
  | 0, _, _, _ => Tree.bot
  | n + 1, q₁, d₂, d₃ =>
      .node ⟨0, Nat.succ_pos _⟩ q₁ fun r₁ =>
        match q₁.answerOf r₁ with
        | some (.num a) => .leaf (.num a)
        | some (.node ⟨0, h0⟩ p) =>
            -- `x` asks about `z` at `p`: consult `d₃`
            match d₃.at' p with
            | some (.leaf (.num a)) =>
                Sfun n (q₁.snoc ⟨0, h0⟩ p (p.substAns (.num a))) d₂ d₃
            | some (.node jz pz _) =>
                Sfun n (q₁.snoc ⟨0, h0⟩ p (p.substAns (.node jz pz))) d₂ d₃
            | some (.leaf .bot) =>
                -- unknown: probe argument 3
                .node ⟨2, by show 2 < ρ.arity + 3; omega⟩ p fun s =>
                  Sfun n (q₁.snoc ⟨0, h0⟩ p s) d₂ (Tree.join d₃ s.toTree)
            | _ => Tree.bot
        | some (.node ⟨1, _⟩ p) =>
            -- `x` asks about `y·z` at `p`: switch to probing argument 2
            Tfun n q₁ p (encode d₂ p) d₂ d₃
        | some (.node ⟨i + 2, hi⟩ p) =>
            -- `x` asks about `ρᵢ`: probe argument `i + 3`
            .node ⟨i + 3, by
                show i + 3 < ρ.arity + 3
                have h' : i + 2 < ρ.arity + 2 := hi
                omega⟩ p
              fun s => Sfun n (q₁.snoc ⟨i + 2, hi⟩ p s) d₂ d₃
        | none => Tree.bot

/-- **Definition A.3 / Figure 8**, the generating function `Tₙ`, likewise in
state-passing form; `p` is the pending query of `x` about `y·z` and `q₂` the
current query on argument 2. -/
noncomputable def Tfun : Nat → Query (σ ⇒ τ ⇒ ρ) → Query τ → Query (σ ⇒ τ) →
    Tree (σ ⇒ τ) → Tree σ → Tree (STy σ τ ρ)
  | 0, _, _, _, _, _ => Tree.bot
  | n + 1, q₁, p, q₂, d₂, d₃ =>
      .node ⟨1, by show 1 < ρ.arity + 3; omega⟩ q₂ fun r₂ =>
        match q₂.answerOf r₂ with
        | some (.num a) =>
            -- `y` answers a numeral: it resolves `x`'s query about `y·z`
            Sfun n (q₁.snoc ⟨1, by show 1 < ρ.arity + 2; omega⟩ p
                (p.substAns (.num a)))
              (Tree.join d₂ r₂.toTree) d₃
        | some (.node ⟨0, h0⟩ pz) =>
            -- `y` asks about `z` at `pz`: consult `d₃`
            match d₃.at' pz with
            | some (.leaf (.num a)) =>
                Tfun n q₁ p (q₂.snoc ⟨0, h0⟩ pz (pz.substAns (.num a))) d₂ d₃
            | some (.node jz pzz _) =>
                Tfun n q₁ p (q₂.snoc ⟨0, h0⟩ pz (pz.substAns (.node jz pzz))) d₂ d₃
            | some (.leaf .bot) =>
                .node ⟨2, by show 2 < ρ.arity + 3; omega⟩ pz fun s =>
                  Tfun n q₁ p (q₂.snoc ⟨0, h0⟩ pz s) d₂ (Tree.join d₃ s.toTree)
            | _ => Tree.bot
        | some (.node ⟨j + 1, hj⟩ pj) =>
            -- `y` announces a node about `τⱼ`: it resolves `x`'s query
            Sfun n (q₁.snoc ⟨1, by show 1 < ρ.arity + 2; omega⟩ p
                (p.substAns (.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ pj)))
              (Tree.join d₂ r₂.toTree) d₃
        | none => Tree.bot
end

end SCombinator

/-! ### The invariant on the accumulated knowledge, and `encode`'s correctness -/

/-- A response's tree lies below any tree that answers its query with the
matching root. -/
theorem substAns_toTree_le {γ : Ty} : ∀ (q : Query γ) (e t : Tree γ) (x : RAns γ),
    e.at' q = some t → t.root = (RAns.toTree x).root →
    Tree.Le (q.substAns x).toTree e
  | .hole, e, t, x, hq, hroot => by
      have het : e = t := Option.some.inj hq
      subst het
      cases x with
      | num a =>
        cases e with
        | leaf v =>
          have hv : v = Val.num a := by
            simpa [Tree.root, RAns.toTree] using hroot
          subst hv
          exact Tree.Le.refl _
        | node i q f => exact absurd hroot (by simp [Tree.root, RAns.toTree])
      | node j p =>
        cases e with
        | leaf v => exact absurd hroot (by simp [Tree.root, RAns.toTree])
        | node i q f =>
          have hij : (⟨i, q⟩ : NodeVal γ) = ⟨j, p⟩ := by
            simpa [Tree.root, RAns.toTree] using hroot
          have h1 : i = j := congrArg Sigma.fst hij
          subst h1
          have h2 : q = p := by injection hij
          subst h2
          show Tree.Le (Tree.node i q fun _ => Tree.bot) (Tree.node i q f)
          exact Tree.Le.node _ _ _ _ fun s => Tree.Le.bot _
  | .step i p r rest, e, t, x, hq, hroot => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hq
      show Tree.Le (Tree.node i p fun s =>
        if s = r then (rest.substAns x).toTree else Tree.bot) (Tree.node i p f)
      refine Tree.Le.node _ _ _ _ fun s => ?_
      by_cases hs : s = r
      · subst hs
        rw [if_pos rfl]
        exact substAns_toTree_le rest (f s) t x hrest hroot
      · rw [if_neg hs]
        exact Tree.Le.bot _

section SCombinator
variable {σ τ ρ : Ty}

/-- The tree accumulated about argument 2 is **well-formed over `d₃`**
(Figure 5, facts 1 and 2): every recorded probe of `z` carries exactly one
recorded answer — the one `d₃` gives — and a recorded continuation beyond it. -/
inductive Accum (d₃ : Tree σ) : Tree (σ ⇒ τ) → Prop where
  | leaf (v : Val) : Accum d₃ (.leaf v)
  | node0 {h0 : 0 < (σ ⇒ τ).arity} (qz : Query ((σ ⇒ τ).arg ⟨0, h0⟩))
      (f : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)) (x : RAns σ) (t : Tree σ)
      (hans : d₃.at' qz = some t) (hroot : t.root = (RAns.toTree x).root)
      (hone : ∀ s, f s ≠ Tree.bot → s = qz.substAns x)
      (hprop : f (qz.substAns x) ≠ Tree.bot)
      (hsub : ∀ s, Accum d₃ (f s)) :
      Accum d₃ (.node ⟨0, h0⟩ qz f)
  | nodeS {j : Nat} {hj : j + 1 < (σ ⇒ τ).arity}
      (qt : Query ((σ ⇒ τ).arg ⟨j + 1, hj⟩))
      (f : Resp ((σ ⇒ τ).arg ⟨j + 1, hj⟩) → Tree (σ ⇒ τ))
      (hsub : ∀ r, Accum d₃ (f r)) :
      Accum d₃ (.node ⟨j + 1, hj⟩ qt f)

/-- The recorded answer of an `Accum` node is proper. -/
theorem RAns.toTree_root_ne_bot {γ : Ty} (x : RAns γ) {t : Tree γ}
    (h : t.root = (RAns.toTree x).root) : t ≠ Tree.bot := by
  intro hb
  subst hb
  cases x <;> simp [Tree.root, RAns.toTree, Tree.bot] at h

/-- `Accum` survives growth of the knowledge about argument 3. -/
theorem Accum.mono_d3 {d₃ d₃' : Tree σ} (h : Tree.Le d₃ d₃') :
    ∀ {d₂ : Tree (σ ⇒ τ)}, Accum d₃ d₂ → Accum d₃' d₂ := by
  intro d₂ hacc
  induction hacc with
  | leaf v => exact Accum.leaf v
  | node0 qz f x t hans hroot hone hprop hsub ih =>
    rcases at'_mono qz h with hn | ⟨a, b, ha, hb, hab⟩
    · rw [hans] at hn; exact Option.noConfusion hn
    · have hta : t = a := by rw [hans] at ha; exact Option.some.inj ha
      subst hta
      refine Accum.node0 qz f x b hb ?_ hone hprop fun s => ih s
      rw [Tree.root_of_le hab (RAns.toTree_root_ne_bot x hroot)]
      exact hroot
  | nodeS qt f hsub ih => exact Accum.nodeS qt f fun r => ih r

/-- The composite `apply (d₂, d₃)` does not change when `d₃` grows: `d₂`'s
recorded probes of `z` are all answered by `d₃` already. -/
theorem apply0_congr_d3 {d₃ d₃' : Tree σ} (h : Tree.Le d₃ d₃') :
    ∀ {d₂ : Tree (σ ⇒ τ)}, Accum d₃ d₂ → apply0 d₂ d₃' = apply0 d₂ d₃ := by
  intro d₂ hacc
  induction hacc with
  | leaf v => rfl
  | node0 qz f x t hans hroot hone hprop hsub ih =>
    rcases at'_mono qz h with hn | ⟨a, b, ha, hb, hab⟩
    · rw [hans] at hn; exact Option.noConfusion hn
    · have hta : t = a := by rw [hans] at ha; exact Option.some.inj ha
      subst hta
      cases x with
      | num n =>
        have ht : t = Tree.leaf (.num n) := by
          cases t with
          | leaf v =>
            have : v = Val.num n := by simpa [Tree.root, RAns.toTree] using hroot
            rw [this]
          | node _ _ _ => exact absurd hroot (by simp [Tree.root, RAns.toTree])
        subst ht
        have hb' : b = Tree.leaf (.num n) := by
          cases hab with
          | leaf _ => rfl
        subst hb'
        rw [apply0, apply0, hans, hb]
        exact ih _
      | node jz pz =>
        obtain ⟨f₃, hf₃⟩ : ∃ f₃, t = Tree.node jz pz f₃ := by
          cases t with
          | leaf v => exact absurd hroot (by simp [Tree.root, RAns.toTree])
          | node j' p' f₃ =>
            have hij : (⟨j', p'⟩ : NodeVal σ) = ⟨jz, pz⟩ := by
              simpa [Tree.root, RAns.toTree] using hroot
            have h1 : j' = jz := congrArg Sigma.fst hij
            subst h1
            have h2 : p' = pz := by injection hij
            subst h2
            exact ⟨f₃, rfl⟩
        subst hf₃
        obtain ⟨g₃, hg₃⟩ := Tree.eq_node_of_le hab
        subst hg₃
        rw [apply0, apply0, hans, hb]
        exact ih _
  | nodeS qt f hsub ih =>
    rw [apply0, apply0]
    exact congrArg _ (funext fun r => ih r)
end SCombinator


/-- Root-directed inversion: a tree whose root is a numeral is that leaf. -/
theorem root_num_inv {γ : Ty} {t : Tree γ} {n : Nat}
    (h : t.root = Sum.inl (Val.num n)) : t = .leaf (.num n) := by
  cases t with
  | leaf v =>
    have : v = Val.num n := by simpa [Tree.root] using h
    rw [this]
  | node i q f => exact absurd h (by simp [Tree.root])

/-- Root-directed inversion: a tree whose root is a node value is a node. -/
theorem root_node_inv {γ : Ty} {t : Tree γ} {j : Fin γ.arity} {p : Query (γ.arg j)}
    (h : t.root = Sum.inr ⟨j, p⟩) : ∃ f, t = .node j p f := by
  cases t with
  | leaf v => exact absurd h (by simp [Tree.root])
  | node i q f =>
    have hij : (⟨i, q⟩ : NodeVal γ) = ⟨j, p⟩ := by simpa [Tree.root] using h
    have h1 : i = j := congrArg Sigma.fst hij
    subst h1
    have h2 : q = p := by injection hij
    subst h2
    exact ⟨f, rfl⟩

section SCombinator
variable {σ τ ρ : Ty}

/-- One step of the composite along an answered probe of `z`. -/
theorem apply0_accum_step {d₃ : Tree σ} {h0 : 0 < (σ ⇒ τ).arity}
    {qz : Query ((σ ⇒ τ).arg ⟨0, h0⟩)} {f : Resp ((σ ⇒ τ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ)}
    {x : RAns σ} {t : Tree σ} (hans : d₃.at' qz = some t)
    (hroot : t.root = (RAns.toTree x).root) :
    apply0 (Tree.node ⟨0, h0⟩ qz f) d₃ = apply0 (f (qz.substAns x)) d₃ := by
  cases x with
  | num n =>
    have ht : t = Tree.leaf (.num n) := root_num_inv (by
      rw [hroot]; rfl)
    subst ht
    rw [apply0, hans]
  | node jz pz =>
    obtain ⟨f₃, ht⟩ := root_node_inv (t := t) (j := jz) (p := pz) (by
      rw [hroot]; rfl)
    subst ht
    rw [apply0, hans]

/-- The recorded probes of `z` along a query are answered by `d₃`
(the traversed branches of the `T`-loop record only what `d₃` says). -/
def ZConsistent (d₃ : Tree σ) : Query (σ ⇒ τ) → Prop
  | .hole => True
  | .step ⟨0, _⟩ qz s rest =>
      (∃ (x' : RAns σ) (t : Tree σ), s = qz.substAns x' ∧
        d₃.at' qz = some t ∧ t.root = (RAns.toTree x').root) ∧ ZConsistent d₃ rest
  | .step ⟨_ + 1, _⟩ _ _ rest => ZConsistent d₃ rest

/-- The shift of a resolved answer about `x`'s second argument. -/
def shiftAns : RAns (σ ⇒ τ) → RAns τ
  | .num a => .num a
  | .node ⟨0, _⟩ _ => .num 0
  | .node ⟨j + 1, hj⟩ pj => .node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ pj

/-- An answer about argument 2 is **resolved** when it is not a probe of `z`. -/
def RAns.Resolved : RAns (σ ⇒ τ) → Prop
  | .num _ => True
  | .node ⟨0, _⟩ _ => False
  | .node ⟨_ + 1, _⟩ _ => True

/-- **Correctness of `encode`** (Figure 5): under the invariant, the encoded
query shifts back to `p`, probes the perimeter of `d₂`, is coherent, and
records about `z` only answers that `d₃` gives. -/
theorem encode_spec (d₃ : Tree σ) :
    ∀ (d₂ : Tree (σ ⇒ τ)) (p : Query τ), Accum d₃ d₂ → p.Coherent →
    (apply0 d₂ d₃).at' p = some Tree.bot →
    (encode d₂ p).shift1 = p ∧
    d₂.at' (encode d₂ p) = some Tree.bot ∧
    (encode d₂ p).Coherent ∧
    RespCtx.Above (encode d₂ p).ctxList ⟨0, Nat.succ_pos _⟩ d₃ ∧
    ZConsistent d₃ (encode d₂ p)
  | .leaf v, p, _, _, hper => by
      rw [show apply0 (Tree.leaf v : Tree (σ ⇒ τ)) d₃ = .leaf v from rfl] at hper
      obtain ⟨rfl, rfl⟩ : p = .hole ∧ v = Val.bot := by
        cases p with
        | hole =>
          refine ⟨rfl, ?_⟩
          have h := Option.some.inj hper
          injection h
        | step i p' r rest => exact absurd hper (by simp [Tree.at', Tree.stepAt])
      refine ⟨?_, ?_, trivial, ?_, ?_⟩
      · rw [encode]
        simp only [Query.shift1]
      · rw [encode]
        rfl
      · rw [encode]
        intro s hs
        exact absurd hs (by simp [Query.ctxList, RespCtx.at'])
      · rw [encode]
        simp only [ZConsistent]
  | .node ⟨0, h0⟩ qz f, p, hacc, hcoh, hper => by
      cases hacc with
      | node0 _ _ x t hans hroot hone hprop hsub =>
        have hex : ∃ s, f s ≠ Tree.bot := ⟨qz.substAns x, hprop⟩
        have hpb : properBranch f = qz.substAns x := by
          rw [properBranch, dif_pos hex]
          exact hone _ (Classical.choose_spec hex)
        rw [apply0_accum_step hans hroot] at hper
        obtain ⟨h1, h2, h3, h4, h5⟩ :=
          encode_spec d₃ (f (qz.substAns x)) p (hsub _) hcoh hper
        rw [encode, hpb]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show Query.shift1 (.step ⟨0, h0⟩ qz (qz.substAns x)
            (encode (f (qz.substAns x)) p)) = p
          simp only [Query.shift1]
          exact h1
        · rw [Tree.at'_step_self]
          exact h2
        · exact ⟨Query.qry_substAns qz x, h3⟩
        · intro s hs
          rcases List.mem_cons.mp hs with heq | hmem
          · have hs2 : s = qz.substAns x := by injection heq
            subst hs2
            exact substAns_toTree_le qz d₃ t x hans hroot
          · exact h4 s hmem
        · simp only [ZConsistent]
          exact ⟨⟨x, t, rfl, hans, hroot⟩, h5⟩
  | .node ⟨j + 1, hj⟩ qt f, p, hacc, hcoh, hper => by
      cases hacc with
      | nodeS _ _ hsub =>
        rw [apply0] at hper
        cases p with
        | hole =>
          exfalso
          have h := Option.some.inj hper
          exact absurd h.symm (by simp [Tree.bot])
        | step i p' r rest =>
          obtain ⟨g, hg, hrest⟩ := at'_step_inv hper
          injection hg with hij hqq hgg
          subst hij
          have hq2 : qt = p' := eq_of_heq hqq
          subst hq2
          have hg2 : (fun r => apply0 (f r) d₃) = g := eq_of_heq hgg
          subst hg2
          obtain ⟨hc1, hc2⟩ := hcoh
          obtain ⟨h1, h2, h3, h4, h5⟩ := encode_spec d₃ (f r) rest (hsub r) hc2 hrest
          rw [encode, dif_pos rfl]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show Query.shift1 (.step ⟨j + 1, hj⟩ qt (Tree.castResp rfl r)
              (encode (f (Tree.castResp rfl r)) rest)) = _
            simp only [Query.shift1, Tree.castResp_rfl]
            rw [h1]
          · rw [Tree.castResp_rfl, Tree.at'_step_self]
            exact h2
          · rw [Tree.castResp_rfl]
            exact ⟨hc1, h3⟩
          · intro s hs
            rw [Tree.castResp_rfl] at hs
            rcases List.mem_cons.mp hs with heq | hmem
            · exact absurd (congrArg (fun z => z.1.val) heq) (by simp)
            · exact h4 s hmem
          · rw [Tree.castResp_rfl]
            simp only [ZConsistent]
            exact h5

/-- **Legality of the encoded query.**  Each step of `encode d₂ p` records a
legal response: the `z`-steps replay answers `d₃` gives, which are roots of
subtrees of the legal tree `e₃ ⊒ d₃`, and the `τ`-steps replay the answers
recorded along `p`, which are legal because `p` is. -/
theorem encode_queryOk (e₃ : Tree σ) (he₃ : TreeOk Ctx.empty e₃) (d₃ : Tree σ)
    (hd₃ : Tree.Le d₃ e₃) :
    ∀ (d₂ : Tree (σ ⇒ τ)) (p : Query τ), Accum d₃ d₂ → QueryOk τ p →
    QueryOk (σ ⇒ τ) (encode d₂ p)
  | .leaf v, p, _, _ => by
      rw [encode]
      exact QueryOk_hole
  | .node ⟨0, h0⟩ qz f, p, hacc, hp => by
      cases hacc with
      | node0 _ _ x t hans hroot hone hprop hsub =>
        have hex : ∃ s, f s ≠ Tree.bot := ⟨qz.substAns x, hprop⟩
        have hpb : properBranch f = qz.substAns x := by
          rw [properBranch, dif_pos hex]
          exact hone _ (Classical.choose_spec hex)
        rw [encode, hpb]
        refine (QueryOk_step _ _ _ _).mpr
          ⟨?_, encode_queryOk e₃ he₃ d₃ hd₃ _ p (hsub _) hp⟩
        cases x with
        | num a => exact LegalResp.num qz a
        | node jz pz =>
          obtain ⟨f₃, ht⟩ := root_node_inv (t := t) (j := jz) (p := pz) (by
            rw [hroot]; rfl)
          subst ht
          rcases at'_mono qz hd₃ with hn | ⟨u, u', hu, hu', huu⟩
          · rw [hans] at hn; exact Option.noConfusion hn
          · have htu : Tree.node jz pz f₃ = u := by
              rw [hans] at hu; exact Option.some.inj hu
            obtain ⟨g₃, hg₃⟩ := Tree.eq_node_of_le (htu ▸ huu)
            subst hg₃
            have hok := TreeOk_at' qz Ctx.empty e₃ _ he₃ hu'
            obtain ⟨hlq, _, _, _⟩ := TreeOk_node_inv hok
            exact LegalResp.node qz jz pz hlq
  | .node ⟨j + 1, hj⟩ qt f, .hole, hacc, hp => by
      rw [encode]
      exact QueryOk_hole
  | .node ⟨j + 1, hj⟩ qt f, .step i p' r rest, hacc, hp => by
      cases hacc with
      | nodeS _ _ hsub =>
        by_cases h : (⟨i, p'⟩ : NodeVal τ) = ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, qt⟩
        · have h1 : i = ⟨j, Nat.lt_of_succ_lt_succ hj⟩ := congrArg Sigma.fst h
          subst h1
          have h2 : p' = qt := by injection h
          subst h2
          obtain ⟨hr, hrest⟩ := (QueryOk_step _ _ _ _).mp hp
          rw [encode, dif_pos rfl]
          refine (QueryOk_step _ _ _ _).mpr ⟨?_, ?_⟩
          · rw [Tree.castResp_rfl]
            exact hr
          · rw [Tree.castResp_rfl]
            exact encode_queryOk e₃ he₃ d₃ hd₃ _ rest (hsub _) hrest
        · rw [encode, dif_neg h]
          exact QueryOk_hole
end SCombinator


section SCombinator
variable {σ τ ρ : Ty}

/-- The answer determines the answer: two answers with the same tree root are
equal. -/
theorem RAns.root_inj {γ : Ty} {x x' : RAns γ}
    (h : (RAns.toTree x).root = (RAns.toTree x').root) : x = x' := by
  cases x with
  | num a =>
    cases x' with
    | num b =>
      have hab : a = b := by simpa [RAns.toTree, Tree.root] using h
      rw [hab]
    | node j p => exact absurd h (by simp [RAns.toTree, Tree.root])
  | node j p =>
    cases x' with
    | num b => exact absurd h (by simp [RAns.toTree, Tree.root])
    | node j' p' =>
      have hjp : (⟨j, p⟩ : NodeVal γ) = ⟨j', p'⟩ := by
        simpa [RAns.toTree, Tree.root] using h
      have h1 : j = j' := congrArg Sigma.fst hjp
      subst h1
      have h2 : p = p' := by injection hjp
      rw [h2]

/-- A join of trees is `⊥` only if both are. -/
theorem Tree.join_ne_bot_left {γ : Ty} {a b : Tree γ} (ha : a ≠ Tree.bot) :
    Tree.join a b ≠ Tree.bot := by
  intro hj
  cases a with
  | leaf v =>
    cases v with
    | bot => exact ha rfl
    | err e => cases b <;> simp [Tree.join, Tree.bot] at hj
    | num n => cases b <;> simp [Tree.join, Tree.bot] at hj
  | node i q f =>
    cases b with
    | leaf v => rw [Tree.join_node_leaf] at hj; exact Tree.noConfusion hj
    | node j p g =>
      by_cases h : (⟨i, q⟩ : NodeVal γ) = ⟨j, p⟩
      · rw [Tree.join] at hj
        rw [dif_pos h] at hj
        exact Tree.noConfusion hj
      · rw [Tree.join] at hj
        rw [dif_neg h] at hj
        exact Tree.noConfusion hj

end SCombinator


section SCombinator
variable {σ τ ρ : Ty}

/-- A response's tree is never `⊥`. -/
theorem Resp.toTree_ne_bot {γ : Ty} : ∀ r : Resp γ, r.toTree ≠ Tree.bot
  | .ans n => fun h => by simp [Resp.toTree, Tree.bot] at h
  | .node i p => fun h => by simp [Resp.toTree, Tree.bot] at h
  | .step i q r rest => fun h => by simp [Resp.toTree, Tree.bot] at h

/-- `q` follows the nodes of `d₂` until `d₂` runs out, then continues freely.
This is the state of the current query on argument 2 during the `T`-loop: it
begins at `d₂`'s perimeter (`encode`) and then extends beyond it. -/
def FollowsToBot (d₂ : Tree (σ ⇒ τ)) : Query (σ ⇒ τ) → Prop
  | .hole => d₂ = Tree.bot
  | .step i p r rest => d₂ = Tree.bot ∨
      ∃ f, d₂ = Tree.node i p f ∧ FollowsToBot (f r) rest

/-- A query reaching `⊥` follows to `⊥`. -/
theorem FollowsToBot_of_at' : ∀ (q : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ)),
    d₂.at' q = some Tree.bot → FollowsToBot d₂ q
  | .hole, d₂, h => by
      simp only [FollowsToBot]
      exact Option.some.inj h
  | .step i p r rest, d₂, h => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv h
      simp only [FollowsToBot]
      exact Or.inr ⟨f, rfl, FollowsToBot_of_at' rest (f r) hrest⟩

/-- Following to `⊥` is stable under extending the query. -/
theorem FollowsToBot_snoc : ∀ (q : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ))
    (j : Fin (σ ⇒ τ).arity) (p : Query ((σ ⇒ τ).arg j)) (r : Resp ((σ ⇒ τ).arg j)),
    FollowsToBot d₂ q → FollowsToBot d₂ (q.snoc j p r)
  | .hole, d₂, j, p, r, h => by
      simp only [FollowsToBot] at h
      subst h
      simp only [Query.snoc, FollowsToBot]
      exact Or.inl trivial
  | .step i p' r' rest, d₂, j, p, r, h => by
      simp only [FollowsToBot] at h
      simp only [Query.snoc, FollowsToBot]
      rcases h with hd | ⟨f, rfl, hrest⟩
      · exact Or.inl hd
      · exact Or.inr ⟨f, rfl, FollowsToBot_snoc rest (f r') j p r hrest⟩

/-- Coherence is stable under extending by a coherent step. -/
theorem Query.coherent_snoc {γ : Ty} : ∀ (q : Query γ) (j : Fin γ.arity)
    (p : Query (γ.arg j)) (r : Resp (γ.arg j)),
    q.Coherent → r.qry = p → (q.snoc j p r).Coherent
  | .hole, j, p, r, _, hr => ⟨hr, trivial⟩
  | .step i p' r' rest, j, p, r, h, hr =>
      ⟨h.1, Query.coherent_snoc rest j p r h.2 hr⟩

/-- `shift₁` ignores a recorded probe of the first argument. -/
theorem Query.shift1_snoc0 {a γ : Ty} : ∀ (q : Query (a ⇒ γ)) (h0 : 0 < (a ⇒ γ).arity)
    (p : Query ((a ⇒ γ).arg ⟨0, h0⟩)) (r : Resp ((a ⇒ γ).arg ⟨0, h0⟩)),
    (q.snoc ⟨0, h0⟩ p r).shift1 = q.shift1
  | .hole, h0, p, r => by
      show (Query.step ⟨0, h0⟩ p r .hole).shift1 = Query.hole.shift1
      simp only [Query.shift1]
  | .step ⟨0, hi⟩ p' r' rest, h0, p, r => by
      show (Query.step ⟨0, hi⟩ p' r' (rest.snoc ⟨0, h0⟩ p r)).shift1 = _
      simp only [Query.shift1]
      exact Query.shift1_snoc0 rest h0 p r
  | .step ⟨i + 1, hi⟩ p' r' rest, h0, p, r => by
      show (Query.step ⟨i + 1, hi⟩ p' r' (rest.snoc ⟨0, h0⟩ p r)).shift1 = _
      simp only [Query.shift1]
      rw [Query.shift1_snoc0 rest h0 p r]

/-- `ZConsistent` survives growth of `d₃`. -/
theorem ZConsistent.mono_d3 {d₃ d₃' : Tree σ} (h : Tree.Le d₃ d₃') :
    ∀ q : Query (σ ⇒ τ), ZConsistent d₃ q → ZConsistent d₃' q
  | .hole, _ => by simp only [ZConsistent]
  | .step ⟨0, h0⟩ qz s rest, hzc => by
      simp only [ZConsistent] at hzc ⊢
      obtain ⟨⟨x', t, hs, hans, hroot⟩, hrest⟩ := hzc
      rcases at'_mono qz h with hn | ⟨a, b, ha, hb, hab⟩
      · rw [hans] at hn; exact Option.noConfusion hn
      · have hta : t = a := by rw [hans] at ha; exact Option.some.inj ha
        subst hta
        refine ⟨⟨x', b, hs, hb, ?_⟩, ZConsistent.mono_d3 h rest hrest⟩
        rw [Tree.root_of_le hab (RAns.toTree_root_ne_bot x' hroot)]
        exact hroot
  | .step ⟨j + 1, hj⟩ qt r rest, hzc => by
      simp only [ZConsistent] at hzc ⊢
      exact ZConsistent.mono_d3 h rest hzc

/-- Extending by a `d₃`-answered probe of `z` keeps a query `ZConsistent`. -/
theorem ZConsistent_snoc0 (d₃ : Tree σ) : ∀ (q : Query (σ ⇒ τ))
    (h0 : 0 < (σ ⇒ τ).arity) (pz : Query ((σ ⇒ τ).arg ⟨0, h0⟩)) (x₃ : RAns σ)
    (t : Tree σ), ZConsistent d₃ q → d₃.at' pz = some t →
    t.root = (RAns.toTree x₃).root →
    ZConsistent d₃ (q.snoc ⟨0, h0⟩ pz (pz.substAns x₃))
  | .hole, h0, pz, x₃, t, _, hans, hroot => by
      simp only [Query.snoc, ZConsistent]
      exact ⟨⟨x₃, t, rfl, hans, hroot⟩, by simp only [ZConsistent]⟩
  | .step ⟨0, hi⟩ qz s rest, h0, pz, x₃, t, hzc, hans, hroot => by
      simp only [ZConsistent] at hzc
      simp only [Query.snoc, ZConsistent]
      exact ⟨hzc.1, ZConsistent_snoc0 d₃ rest h0 pz x₃ t hzc.2 hans hroot⟩
  | .step ⟨j + 1, hj⟩ qt r rest, h0, pz, x₃, t, hzc, hans, hroot => by
      simp only [ZConsistent] at hzc
      simp only [Query.snoc, ZConsistent]
      exact ZConsistent_snoc0 d₃ rest h0 pz x₃ t hzc hans hroot

/-- Extending by any recorded response about a later argument keeps a query
`ZConsistent`. -/
theorem ZConsistent_snocS (d₃ : Tree σ) : ∀ (q : Query (σ ⇒ τ)) {j : Nat}
    (hj : j + 1 < (σ ⇒ τ).arity) (pt : Query ((σ ⇒ τ).arg ⟨j + 1, hj⟩))
    (r : Resp ((σ ⇒ τ).arg ⟨j + 1, hj⟩)),
    ZConsistent d₃ q → ZConsistent d₃ (q.snoc ⟨j + 1, hj⟩ pt r)
  | .hole, j, hj, pt, r, _ => by
      simp only [Query.snoc, ZConsistent]
  | .step ⟨0, hi⟩ qz s rest, j, hj, pt, r, hzc => by
      simp only [ZConsistent] at hzc
      simp only [Query.snoc, ZConsistent]
      exact ⟨hzc.1, ZConsistent_snocS d₃ rest hj pt r hzc.2⟩
  | .step ⟨j' + 1, hj'⟩ qt r' rest, j, hj, pt, r, hzc => by
      simp only [ZConsistent] at hzc
      simp only [Query.snoc, ZConsistent]
      exact ZConsistent_snocS d₃ rest hj pt r hzc

/-- The `z`-responses of a `ZConsistent` query lie below `d₃`. -/
theorem ZConsistent.above (d₃ : Tree σ) : ∀ (q : Query (σ ⇒ τ))
    (h0 : 0 < (σ ⇒ τ).arity), ZConsistent d₃ q →
    RespCtx.Above q.ctxList ⟨0, h0⟩ d₃
  | .hole, h0, _ => fun s hs => absurd hs (by simp [Query.ctxList, RespCtx.at'])
  | .step ⟨0, hi⟩ qz s rest, h0, hzc => by
      simp only [ZConsistent] at hzc
      obtain ⟨⟨x', t, hs, hans, hroot⟩, hrest⟩ := hzc
      intro s' hs'
      rcases List.mem_cons.mp hs' with heq | hmem
      · have : s' = s := by injection heq
        subst this
        subst hs
        exact substAns_toTree_le qz d₃ t x' hans hroot
      · exact ZConsistent.above d₃ rest h0 hrest s' hmem
  | .step ⟨j + 1, hj⟩ qt r rest, h0, hzc => by
      simp only [ZConsistent] at hzc
      intro s' hs'
      rcases List.mem_cons.mp hs' with heq | hmem
      · exact absurd (congrArg (fun z => z.1.val) heq) (by simp)
      · exact ZConsistent.above d₃ rest h0 hzc s' hmem


/-- Applying a pure recorded path: the `z`-probes are consumed by `d₃`'s
answers and the rest shifts down. -/
theorem apply0_respTree (d₃ : Tree σ) : ∀ (q₂ : Query (σ ⇒ τ)) (x : RAns (σ ⇒ τ)),
    ZConsistent d₃ q₂ → x.Resolved →
    apply0 ((q₂.substAns x).toTree) d₃
      = ((q₂.shift1).substAns (shiftAns x)).toTree
  | .hole, x, _, hres => by
      cases x with
      | num a =>
        simp only [Query.shift1, Query.substAns, shiftAns, Resp.toTree]
        rfl
      | node j pj =>
        match j with
        | ⟨0, h0⟩ => exact absurd hres (by simp [RAns.Resolved])
        | ⟨j' + 1, hj⟩ =>
          simp only [Query.shift1, Query.substAns, shiftAns, Resp.toTree]
          rw [apply0]
          exact congrArg _ (funext fun _ => rfl)
  | .step ⟨0, h0⟩ qz s rest, x, hzc, hres => by
      simp only [ZConsistent] at hzc
      obtain ⟨⟨x', t, hs, hans, hroot⟩, hrest⟩ := hzc
      subst hs
      show apply0 (Tree.node ⟨0, h0⟩ qz fun s' =>
        if s' = qz.substAns x' then ((rest.substAns x).toTree) else Tree.bot) d₃ = _
      rw [apply0_accum_step (f := fun s' => if s' = qz.substAns x'
        then ((rest.substAns x).toTree) else Tree.bot) hans hroot, if_pos rfl]
      simp only [Query.shift1]
      exact apply0_respTree d₃ rest x hrest hres
  | .step ⟨j + 1, hj⟩ qt r rest, x, hzc, hres => by
      simp only [ZConsistent] at hzc
      show apply0 (Tree.node ⟨j + 1, hj⟩ qt fun r' =>
        if r' = r then ((rest.substAns x).toTree) else Tree.bot) d₃ = _
      rw [apply0]
      have hshift : (Query.step ⟨j + 1, hj⟩ qt r rest).shift1
          = Query.step ⟨j, Nat.lt_of_succ_lt_succ hj⟩ qt r rest.shift1 := by
        simp only [Query.shift1]
      rw [hshift]
      show _ = Tree.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ qt (fun r' => if r' = r
        then ((rest.shift1.substAns (shiftAns x)).toTree) else Tree.bot)
      refine congrArg _ (funext fun r' => ?_)
      by_cases hr : r' = r
      · rw [if_pos hr, if_pos hr]
        exact apply0_respTree d₃ rest x hzc hres
      · rw [if_neg hr, if_neg hr]
        rfl

/-- A pure recorded path is well-formed knowledge. -/
theorem Accum_respTree (d₃ : Tree σ) : ∀ (q₂ : Query (σ ⇒ τ)) (x : RAns (σ ⇒ τ)),
    ZConsistent d₃ q₂ → x.Resolved →
    Accum d₃ ((q₂.substAns x).toTree)
  | .hole, x, _, hres => by
      cases x with
      | num a => exact Accum.leaf _
      | node j pj =>
        match j with
        | ⟨0, h0⟩ => exact absurd hres (by simp [RAns.Resolved])
        | ⟨j' + 1, hj⟩ =>
          show Accum d₃ (Tree.node ⟨j' + 1, hj⟩ pj fun _ => Tree.bot)
          exact Accum.nodeS pj _ fun _ => Accum.leaf _
  | .step ⟨0, h0⟩ qz s rest, x, hzc, hres => by
      simp only [ZConsistent] at hzc
      obtain ⟨⟨x', t, hs, hans, hroot⟩, hrest⟩ := hzc
      subst hs
      show Accum d₃ (Tree.node ⟨0, h0⟩ qz fun s' =>
        if s' = qz.substAns x' then ((rest.substAns x).toTree) else Tree.bot)
      refine Accum.node0 qz _ x' t hans hroot (fun s' hs' => ?_) ?_ (fun s' => ?_)
      · by_cases h2 : s' = qz.substAns x'
        · exact h2
        · rw [if_neg h2] at hs'
          exact absurd rfl hs'
      · rw [if_pos rfl]
        exact Resp.toTree_ne_bot _
      · by_cases h2 : s' = qz.substAns x'
        · rw [if_pos h2]
          exact Accum_respTree d₃ rest x hrest hres
        · rw [if_neg h2]
          exact Accum.leaf _
  | .step ⟨j + 1, hj⟩ qt r rest, x, hzc, hres => by
      simp only [ZConsistent] at hzc
      show Accum d₃ (Tree.node ⟨j + 1, hj⟩ qt fun r' =>
        if r' = r then ((rest.substAns x).toTree) else Tree.bot)
      refine Accum.nodeS qt _ fun r' => ?_
      by_cases h2 : r' = r
      · rw [if_pos h2]
        exact Accum_respTree d₃ rest x hzc hres
      · rw [if_neg h2]
        exact Accum.leaf _

/-- **Recording a resolved response**: joining `q₂[?/x]` into `d₂` extends the
composite `apply (d₂, d₃)` by exactly the shifted response. -/
theorem apply0_join_resolved (d₃ : Tree σ) :
    ∀ (q₂ : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ)) (x : RAns (σ ⇒ τ)),
    FollowsToBot d₂ q₂ → ZConsistent d₃ q₂ → x.Resolved →
    apply0 (Tree.join d₂ (q₂.substAns x).toTree) d₃
      = Tree.join (apply0 d₂ d₃) ((q₂.shift1.substAns (shiftAns x)).toTree)
  | .hole, d₂, x, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      subst hper
      rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ)) ((Query.hole.substAns x).toTree)
        = (Query.hole.substAns x).toTree from Tree.join_bot_left _,
        show apply0 (Tree.bot : Tree (σ ⇒ τ)) d₃ = Tree.bot from rfl,
        show Tree.join (Tree.bot : Tree τ)
          ((Query.hole.shift1.substAns (shiftAns x)).toTree)
          = (Query.hole.shift1.substAns (shiftAns x)).toTree from Tree.join_bot_left _]
      exact apply0_respTree d₃ .hole x (by simp only [ZConsistent]) hres
  | .step ⟨0, h0⟩ qz s rest, d₂, x, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      rcases hper with hd | ⟨f, rfl, hrest⟩
      · subst hd
        rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ))
            (((Query.step ⟨0, h0⟩ qz s rest).substAns x).toTree)
            = ((Query.step ⟨0, h0⟩ qz s rest).substAns x).toTree
            from Tree.join_bot_left _,
          show apply0 (Tree.bot : Tree (σ ⇒ τ)) d₃ = Tree.bot from rfl,
          show Tree.join (Tree.bot : Tree τ)
            (((Query.step ⟨0, h0⟩ qz s rest).shift1.substAns (shiftAns x)).toTree)
            = ((Query.step ⟨0, h0⟩ qz s rest).shift1.substAns (shiftAns x)).toTree
            from Tree.join_bot_left _]
        exact apply0_respTree d₃ _ x hzc hres
      · simp only [ZConsistent] at hzc
        obtain ⟨⟨x', t, hs, hans, hroot⟩, hzc'⟩ := hzc
        subst hs
        have hjoin : Tree.join (Tree.node ⟨0, h0⟩ qz f)
            ((Query.step ⟨0, h0⟩ qz (qz.substAns x') rest).substAns x).toTree
            = Tree.node ⟨0, h0⟩ qz fun s' =>
                Tree.join (f s') (if s' = qz.substAns x'
                  then (rest.substAns x).toTree else Tree.bot) := by
          show Tree.join (Tree.node ⟨0, h0⟩ qz f) (Tree.node ⟨0, h0⟩ qz _) = _
          rw [Tree.join_node_self]
        rw [hjoin]
        rw [apply0_accum_step (f := fun s' =>
              Tree.join (f s') (if s' = qz.substAns x'
                then (rest.substAns x).toTree else Tree.bot)) hans hroot,
          apply0_accum_step (f := f) hans hroot]
        rw [if_pos rfl]
        have hshift : (Query.step ⟨0, h0⟩ qz (qz.substAns x') rest).shift1
            = rest.shift1 := by
          simp only [Query.shift1]
        rw [hshift]
        exact apply0_join_resolved d₃ rest (f (qz.substAns x')) x hrest hzc' hres
  | .step ⟨j + 1, hj⟩ qt r rest, d₂, x, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      simp only [ZConsistent] at hzc
      rcases hper with hd | ⟨f, rfl, hrest⟩
      · subst hd
        rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ))
            (((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree)
            = ((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree
            from Tree.join_bot_left _,
          show apply0 (Tree.bot : Tree (σ ⇒ τ)) d₃ = Tree.bot from rfl,
          show Tree.join (Tree.bot : Tree τ)
            (((Query.step ⟨j + 1, hj⟩ qt r rest).shift1.substAns (shiftAns x)).toTree)
            = ((Query.step ⟨j + 1, hj⟩ qt r rest).shift1.substAns (shiftAns x)).toTree
            from Tree.join_bot_left _]
        refine apply0_respTree d₃ _ x ?_ hres
        simp only [ZConsistent]
        exact hzc
      · have hjoin : Tree.join (Tree.node ⟨j + 1, hj⟩ qt f)
            ((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree
            = Tree.node ⟨j + 1, hj⟩ qt fun r' =>
                Tree.join (f r') (if r' = r then (rest.substAns x).toTree else Tree.bot) := by
          show Tree.join (Tree.node ⟨j + 1, hj⟩ qt f) (Tree.node ⟨j + 1, hj⟩ qt _) = _
          rw [Tree.join_node_self]
        rw [hjoin, apply0, apply0]
        have hshift : (Query.step ⟨j + 1, hj⟩ qt r rest).shift1
            = Query.step ⟨j, Nat.lt_of_succ_lt_succ hj⟩ qt r rest.shift1 := by
          simp only [Query.shift1]
        rw [hshift]
        show _ = Tree.join (Tree.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ qt
            fun r' => apply0 (f r') d₃)
          (Tree.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ qt fun r' => if r' = r
            then ((rest.shift1.substAns (shiftAns x)).toTree) else Tree.bot)
        rw [Tree.join_node_self]
        refine congrArg _ (funext fun r' => ?_)
        by_cases hr : r' = r
        · subst hr
          rw [if_pos rfl, if_pos rfl]
          exact apply0_join_resolved d₃ rest (f r') x hrest hzc hres
        · rw [if_neg hr, if_neg hr, Tree.join_bot_right, Tree.join_bot_right]

/-- Joining a resolved response into well-formed accumulated knowledge keeps it
well-formed. -/
theorem Accum_join_resolved (d₃ : Tree σ) :
    ∀ (q₂ : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ)) (x : RAns (σ ⇒ τ)),
    Accum d₃ d₂ → FollowsToBot d₂ q₂ → ZConsistent d₃ q₂ → x.Resolved →
    Accum d₃ (Tree.join d₂ (q₂.substAns x).toTree)
  | .hole, d₂, x, hacc, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      subst hper
      rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ)) ((Query.hole.substAns x).toTree)
        = (Query.hole.substAns x).toTree from Tree.join_bot_left _]
      exact Accum_respTree d₃ .hole x (by simp only [ZConsistent]) hres
  | .step ⟨0, h0⟩ qz s rest, d₂, x, hacc, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      rcases hper with hd | ⟨f, rfl, hrest⟩
      · subst hd
        rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ))
            (((Query.step ⟨0, h0⟩ qz s rest).substAns x).toTree)
            = ((Query.step ⟨0, h0⟩ qz s rest).substAns x).toTree
            from Tree.join_bot_left _]
        exact Accum_respTree d₃ _ x hzc hres
      · simp only [ZConsistent] at hzc
        obtain ⟨⟨x', t, hs, hans, hroot⟩, hzc'⟩ := hzc
        subst hs
        cases hacc with
        | node0 _ _ x₀ t₀ hans₀ hroot₀ hone hprop hsub =>
          have ht : t = t₀ := by rw [hans] at hans₀; exact Option.some.inj hans₀
          subst ht
          have hx : x' = x₀ := RAns.root_inj (by rw [← hroot, ← hroot₀])
          subst hx
          have hjoin : Tree.join (Tree.node ⟨0, h0⟩ qz f)
              ((Query.step ⟨0, h0⟩ qz (qz.substAns x') rest).substAns x).toTree
              = Tree.node ⟨0, h0⟩ qz fun s' =>
                  Tree.join (f s') (if s' = qz.substAns x'
                    then (rest.substAns x).toTree else Tree.bot) := by
            show Tree.join (Tree.node ⟨0, h0⟩ qz f) (Tree.node ⟨0, h0⟩ qz _) = _
            rw [Tree.join_node_self]
          rw [hjoin]
          refine Accum.node0 qz _ x' t hans hroot (fun s' hs' => ?_)
            (Tree.join_ne_bot_left hprop) (fun s' => ?_)
          · by_cases hs2 : s' = qz.substAns x'
            · exact hs2
            · rw [if_neg hs2, Tree.join_bot_right] at hs'
              exact hone s' hs'
          · by_cases hs2 : s' = qz.substAns x'
            · subst hs2
              rw [if_pos rfl]
              exact Accum_join_resolved d₃ rest (f (qz.substAns x')) x
                (hsub (qz.substAns x')) hrest hzc' hres
            · rw [if_neg hs2, Tree.join_bot_right]
              exact hsub s'
  | .step ⟨j + 1, hj⟩ qt r rest, d₂, x, hacc, hper, hzc, hres => by
      simp only [FollowsToBot] at hper
      simp only [ZConsistent] at hzc
      rcases hper with hd | ⟨f, rfl, hrest⟩
      · subst hd
        rw [show Tree.join (Tree.bot : Tree (σ ⇒ τ))
            (((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree)
            = ((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree
            from Tree.join_bot_left _]
        refine Accum_respTree d₃ _ x ?_ hres
        simp only [ZConsistent]
        exact hzc
      · cases hacc with
        | nodeS _ _ hsub =>
          have hjoin : Tree.join (Tree.node ⟨j + 1, hj⟩ qt f)
              ((Query.step ⟨j + 1, hj⟩ qt r rest).substAns x).toTree
              = Tree.node ⟨j + 1, hj⟩ qt fun r' =>
                  Tree.join (f r') (if r' = r
                    then (rest.substAns x).toTree else Tree.bot) := by
            show Tree.join (Tree.node ⟨j + 1, hj⟩ qt f) (Tree.node ⟨j + 1, hj⟩ qt _) = _
            rw [Tree.join_node_self]
          rw [hjoin]
          refine Accum.nodeS qt _ fun r' => ?_
          by_cases hr : r' = r
          · subst hr
            rw [if_pos rfl]
            exact Accum_join_resolved d₃ rest (f r') x (hsub r') hrest hzc hres
          · rw [if_neg hr, Tree.join_bot_right]
            exact hsub r'

/-- Grafting a response at a perimeter position records its answer there. -/
theorem at'_join_substAns {γ : Ty} : ∀ (p : Query γ) (d : Tree γ) (x : RAns γ),
    d.at' p = some Tree.bot →
    (Tree.join d (p.substAns x).toTree).at' p = some (RAns.toTree x)
  | .hole, d, x, hper => by
      have hd : d = Tree.bot := Option.some.inj hper
      subst hd
      rw [show Tree.join (Tree.bot : Tree γ) ((Query.hole.substAns x).toTree)
        = (Query.hole.substAns x).toTree from Tree.join_bot_left _]
      cases x with
      | num n => rfl
      | node i p => rfl
  | .step i p' r rest, d, x, hper => by
      obtain ⟨f, rfl, hrest⟩ := at'_step_inv hper
      have hjoin : Tree.join (Tree.node i p' f)
          ((Query.step i p' r rest).substAns x).toTree
          = Tree.node i p' fun s' =>
              Tree.join (f s') (if s' = r then (rest.substAns x).toTree else Tree.bot) := by
        show Tree.join (Tree.node i p' f) (Tree.node i p' _) = _
        rw [Tree.join_node_self]
      rw [hjoin, Tree.at'_step_self]
      show (Tree.join (f r) (if r = r then (rest.substAns x).toTree else Tree.bot)).at' rest
        = some (RAns.toTree x)
      rw [if_pos rfl]
      exact at'_join_substAns rest (f r) x hrest
end SCombinator


section SCombinator
variable {σ τ ρ : Ty}

/-- The three outer applications of the `(S)` equation. -/
noncomputable def app3 (s : Tree (STy σ τ ρ)) (e₁ : Tree (σ ⇒ τ ⇒ ρ))
    (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) : Tree ρ :=
  apply0 (apply0 (apply0 s e₁) e₂) e₃

theorem app3_leaf (v : Val) (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) :
    app3 (.leaf v : Tree (STy σ τ ρ)) e₁ e₂ e₃ = .leaf v := rfl

/-! The chain through the root probe of argument 1, by the shape of `e₁ @ q₁`. -/

theorem app3_node0_none (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (g : Resp ((STy σ τ ρ).arg ⟨0, Nat.succ_pos _⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ)
    (hq : e₁.at' q₁ = none) :
    app3 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁ e₂ e₃ = Tree.bot := by
  show apply0 (apply0 (apply0 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁) e₂) e₃ = _
  rw [apply0, hq]
  rfl

theorem app3_node0_bot (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (g : Resp ((STy σ τ ρ).arg ⟨0, Nat.succ_pos _⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ)
    (hq : e₁.at' q₁ = some Tree.bot) :
    app3 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁ e₂ e₃ = Tree.bot := by
  show apply0 (apply0 (apply0 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁) e₂) e₃ = _
  rw [apply0, hq]
  rfl

theorem app3_node0_err (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (g : Resp ((STy σ τ ρ).arg ⟨0, Nat.succ_pos _⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) (b : Bool)
    (hq : e₁.at' q₁ = some (.leaf (.err b))) :
    app3 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁ e₂ e₃ = .leaf (.err b) := by
  show apply0 (apply0 (apply0 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁) e₂) e₃ = _
  rw [apply0, hq]
  rfl

theorem app3_node0_num (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (g : Resp ((STy σ τ ρ).arg ⟨0, Nat.succ_pos _⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) (a : Nat)
    (hq : e₁.at' q₁ = some (.leaf (.num a))) :
    app3 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁ e₂ e₃
      = app3 (g (q₁.substAns (.num a))) e₁ e₂ e₃ := by
  show apply0 (apply0 (apply0 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁) e₂) e₃ = _
  rw [apply0, hq]
  rfl

theorem app3_node0_node (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (g : Resp ((STy σ τ ρ).arg ⟨0, Nat.succ_pos _⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ)
    (jt : Fin (σ ⇒ τ ⇒ ρ).arity) (pt : Query ((σ ⇒ τ ⇒ ρ).arg jt))
    (ft : Resp ((σ ⇒ τ ⇒ ρ).arg jt) → Tree (σ ⇒ τ ⇒ ρ))
    (hq : e₁.at' q₁ = some (.node jt pt ft)) :
    app3 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁ e₂ e₃
      = app3 (g (q₁.substAns (.node jt pt))) e₁ e₂ e₃ := by
  show apply0 (apply0 (apply0 (.node ⟨0, Nat.succ_pos _⟩ q₁ g) e₁) e₂) e₃ = _
  rw [apply0, hq]
  rfl

/-! The chain through a probe of argument 3, by the shape of `e₃ @ pz`. -/

theorem app3_node2 (h2 : 2 < (STy σ τ ρ).arity) (pz : Query ((STy σ τ ρ).arg ⟨2, h2⟩))
    (g : Resp ((STy σ τ ρ).arg ⟨2, h2⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) :
    app3 (.node ⟨2, h2⟩ pz g) e₁ e₂ e₃
      = match e₃.at' pz with
        | none => Tree.bot
        | some (.leaf .bot) => Tree.bot
        | some (.leaf (.err b)) => .leaf (.err b)
        | some (.leaf (.num a)) => app3 (g (pz.substAns (.num a))) e₁ e₂ e₃
        | some (.node jz pz' _) => app3 (g (pz.substAns (.node jz pz'))) e₁ e₂ e₃ := by
  show apply0 (apply0 (apply0 (.node ⟨2, h2⟩ pz g) e₁) e₂) e₃ = _
  rw [apply0, apply0, apply0]
  cases hz : e₃.at' pz with
  | none => rfl
  | some t =>
    cases t with
    | leaf v => cases v <;> rfl
    | node jz pz' fz => rfl

/-! The chain through a probe of argument `i + 3`. -/

theorem app3_nodeRho {i : Nat} (hi : i + 3 < (STy σ τ ρ).arity)
    (p : Query ((STy σ τ ρ).arg ⟨i + 3, hi⟩))
    (g : Resp ((STy σ τ ρ).arg ⟨i + 3, hi⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) :
    app3 (.node ⟨i + 3, hi⟩ p g) e₁ e₂ e₃
      = .node ⟨i, by
            have h' : i + 3 < ρ.arity + 3 := hi
            omega⟩ p
          fun s => app3 (g s) e₁ e₂ e₃ := by
  show apply0 (apply0 (apply0 (.node ⟨i + 3, hi⟩ p g) e₁) e₂) e₃ = _
  rw [apply0, apply0, apply0]
  rfl

/-! The chain through the `T`-loop's probe of argument 2, by the shape of
`e₂ @ q₂`. -/

theorem app3_node1 (h1 : 1 < (STy σ τ ρ).arity) (q₂ : Query ((STy σ τ ρ).arg ⟨1, h1⟩))
    (g : Resp ((STy σ τ ρ).arg ⟨1, h1⟩) → Tree (STy σ τ ρ))
    (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ) :
    app3 (.node ⟨1, h1⟩ q₂ g) e₁ e₂ e₃
      = match e₂.at' q₂ with
        | none => Tree.bot
        | some (.leaf .bot) => Tree.bot
        | some (.leaf (.err b)) => .leaf (.err b)
        | some (.leaf (.num a)) => app3 (g (q₂.substAns (.num a))) e₁ e₂ e₃
        | some (.node j p _) => app3 (g (q₂.substAns (.node j p))) e₁ e₂ e₃ := by
  show apply0 (apply0 (apply0 (.node ⟨1, h1⟩ q₂ g) e₁) e₂) e₃ = _
  rw [apply0, apply0]
  cases hz : e₂.at' q₂ with
  | none => rfl
  | some t =>
    cases t with
    | leaf v => cases v <;> rfl
    | node j p f => rfl

/-! The right-hand side's dispatch: `apply (apply (t₁, e₃), X)` by the shape of
`t₁` and the consulted answers. -/

theorem rhs1 (h1 : 1 < (σ ⇒ τ ⇒ ρ).arity) (pτ : Query ((σ ⇒ τ ⇒ ρ).arg ⟨1, h1⟩))
    (f₁ : Resp ((σ ⇒ τ ⇒ ρ).arg ⟨1, h1⟩) → Tree (σ ⇒ τ ⇒ ρ))
    (e₃ : Tree σ) (X : Tree τ) :
    apply0 (apply0 (Tree.node ⟨1, h1⟩ pτ f₁) e₃) X
      = match X.at' pτ with
        | none => Tree.bot
        | some (.leaf .bot) => Tree.bot
        | some (.leaf (.err b)) => .leaf (.err b)
        | some (.leaf (.num a)) => apply0 (apply0 (f₁ (pτ.substAns (.num a))) e₃) X
        | some (.node j p _) => apply0 (apply0 (f₁ (pτ.substAns (.node j p))) e₃) X := by
  rw [apply0, apply0]
  cases hz : X.at' pτ with
  | none => rfl
  | some t =>
    cases t with
    | leaf v => cases v <;> rfl
    | node j p f => rfl

theorem rhs0 (h0 : 0 < (σ ⇒ τ ⇒ ρ).arity) (pz : Query ((σ ⇒ τ ⇒ ρ).arg ⟨0, h0⟩))
    (f₁ : Resp ((σ ⇒ τ ⇒ ρ).arg ⟨0, h0⟩) → Tree (σ ⇒ τ ⇒ ρ))
    (e₃ : Tree σ) (X : Tree τ) :
    apply0 (apply0 (Tree.node ⟨0, h0⟩ pz f₁) e₃) X
      = match e₃.at' pz with
        | none => Tree.bot
        | some (.leaf .bot) => Tree.bot
        | some (.leaf (.err b)) => .leaf (.err b)
        | some (.leaf (.num a)) => apply0 (apply0 (f₁ (pz.substAns (.num a))) e₃) X
        | some (.node jz pz' _) => apply0 (apply0 (f₁ (pz.substAns (.node jz pz'))) e₃) X := by
  rw [apply0]
  cases hz : e₃.at' pz with
  | none => rfl
  | some t =>
    cases t with
    | leaf v => cases v <;> rfl
    | node jz pz' fz => rfl

theorem rhsRho {i : Nat} (hi : i + 2 < (σ ⇒ τ ⇒ ρ).arity)
    (p : Query ((σ ⇒ τ ⇒ ρ).arg ⟨i + 2, hi⟩))
    (f₁ : Resp ((σ ⇒ τ ⇒ ρ).arg ⟨i + 2, hi⟩) → Tree (σ ⇒ τ ⇒ ρ))
    (e₃ : Tree σ) (X : Tree τ) :
    apply0 (apply0 (Tree.node ⟨i + 2, hi⟩ p f₁) e₃) X
      = .node ⟨i, by
            have h' : i + 2 < ρ.arity + 2 := hi
            omega⟩ p
          fun s => apply0 (apply0 (f₁ s) e₃) X := by
  rw [apply0, apply0]
end SCombinator


section SCombinator
variable {σ τ ρ : Ty}

mutual
/-- The approximants `Sₙ` form a chain in the fuel. -/
theorem Sfun_mono : ∀ (n : Nat) (q₁ : Query (σ ⇒ τ ⇒ ρ)) (d₂ : Tree (σ ⇒ τ))
    (d₃ : Tree σ), Tree.Le (Sfun n q₁ d₂ d₃) (Sfun (n + 1) q₁ d₂ d₃)
  | 0, _, _, _ => Tree.Le.bot _
  | n + 1, q₁, d₂, d₃ => by
      simp only [Sfun]
      refine Tree.Le.node _ _ _ _ fun r₁ => ?_
      cases hq : q₁.answerOf r₁ with
      | none => exact Tree.Le.refl _
      | some x =>
        cases x with
        | num a => exact Tree.Le.refl _
        | node i p =>
          match i with
          | ⟨0, h0⟩ =>
            dsimp only
            cases hd : d₃.at' p with
            | none => exact Tree.Le.refl _
            | some t =>
              cases t with
              | leaf v =>
                cases v with
                | bot =>
                  exact Tree.Le.node _ _ _ _ fun s => Sfun_mono n _ _ _
                | err b => exact Tree.Le.refl _
                | num a => exact Sfun_mono n _ _ _
              | node jz pz fz => exact Sfun_mono n _ _ _
          | ⟨1, h1⟩ =>
            dsimp only
            exact Tfun_mono n _ _ _ _ _
          | ⟨i + 2, hi⟩ =>
            dsimp only
            exact Tree.Le.node _ _ _ _ fun s => Sfun_mono n _ _ _

/-- The approximants `Tₙ` form a chain in the fuel. -/
theorem Tfun_mono : ∀ (n : Nat) (q₁ : Query (σ ⇒ τ ⇒ ρ)) (p : Query τ)
    (q₂ : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ)) (d₃ : Tree σ),
    Tree.Le (Tfun n q₁ p q₂ d₂ d₃) (Tfun (n + 1) q₁ p q₂ d₂ d₃)
  | 0, _, _, _, _, _ => Tree.Le.bot _
  | n + 1, q₁, p, q₂, d₂, d₃ => by
      simp only [Tfun]
      refine Tree.Le.node _ _ _ _ fun r₂ => ?_
      cases hq : q₂.answerOf r₂ with
      | none => exact Tree.Le.refl _
      | some x =>
        cases x with
        | num a => exact Sfun_mono n _ _ _
        | node j pj =>
          match j with
          | ⟨0, h0⟩ =>
            dsimp only
            cases hd : d₃.at' pj with
            | none => exact Tree.Le.refl _
            | some t =>
              cases t with
              | leaf v =>
                cases v with
                | bot => exact Tree.Le.node _ _ _ _ fun s => Tfun_mono n _ _ _ _ _
                | err b => exact Tree.Le.refl _
                | num a => exact Tfun_mono n _ _ _ _ _
              | node jz pzz fz => exact Tfun_mono n _ _ _ _ _
          | ⟨j' + 1, hj⟩ =>
            dsimp only
            exact Sfun_mono n _ _ _
end

theorem Sfun_le_of_le {m n : Nat} (h : m ≤ n) (q₁ : Query (σ ⇒ τ ⇒ ρ))
    (d₂ : Tree (σ ⇒ τ)) (d₃ : Tree σ) :
    Tree.Le (Sfun m q₁ d₂ d₃) (Sfun n q₁ d₂ d₃) := by
  induction h with
  | refl => exact Tree.Le.refl _
  | step _ ih => exact Tree.Le.trans ih (Sfun_mono _ q₁ d₂ d₃)

end SCombinator

section SCombinator
variable {σ τ ρ : Ty}

/-- Descending one recorded step. -/
theorem at'_snoc_node {γ : Ty} (e : Tree γ) (q : Query γ) (j : Fin γ.arity)
    (p : Query (γ.arg j)) (f : Resp (γ.arg j) → Tree γ) (r : Resp (γ.arg j))
    (hq : e.at' q = some (.node j p f)) :
    e.at' (q.snoc j p r) = some (f r) := by
  rw [at'_snoc, hq]
  exact Tree.stepAt_self j p f r

mutual
/-- **The `⊑`-half of Lemma A.7**, by induction on the fuel: under the
invariant, every approximant computes at most the right-hand side of the `(S)`
equation, read at the current position `t₁ = e₁ @ q₁` of the first argument. -/
theorem Sfun_apply_le (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ)
    (he₁ : TreeOk Ctx.empty e₁) :
    ∀ (n : Nat) (q₁ : Query (σ ⇒ τ ⇒ ρ)) (d₂ : Tree (σ ⇒ τ)) (d₃ : Tree σ)
      (t₁ : Tree (σ ⇒ τ ⇒ ρ)),
    e₁.at' q₁ = some t₁ → Tree.Le d₂ e₂ → Tree.Le d₃ e₃ → Accum d₃ d₂ →
    q₁.ctx ⟨1, by show 1 < ρ.arity + 2; omega⟩ = apply0 d₂ d₃ →
    Tree.Le (app3 (Sfun n q₁ d₂ d₃) e₁ e₂ e₃)
      (apply0 (apply0 t₁ e₃) (apply0 e₂ e₃))
  | 0, _, _, _, _, _, _, _, _, _ => Tree.Le.bot _
  | n + 1, q₁, d₂, d₃, t₁, hq₁, hd₂, hd₃, hacc, hctx => by
      simp only [Sfun]
      cases t₁ with
      | leaf v =>
        cases v with
        | bot =>
          rw [app3_node0_bot q₁ _ e₁ e₂ e₃ hq₁]
          exact Tree.Le.bot _
        | err b =>
          rw [app3_node0_err q₁ _ e₁ e₂ e₃ b hq₁]
          exact Tree.Le.refl _
        | num a =>
          rw [app3_node0_num q₁ _ e₁ e₂ e₃ a hq₁]
          simp only [Query.answerOf_substAns]
          exact Tree.Le.refl _
      | node jt pt ft =>
        rw [app3_node0_node q₁ _ e₁ e₂ e₃ jt pt ft hq₁]
        simp only [Query.answerOf_substAns]
        match jt with
        | ⟨0, h0⟩ =>
          -- `x` asks about `z` at `pt`
          dsimp only
          rw [rhs0 h0 pt ft e₃ (apply0 e₂ e₃)]
          cases hd : d₃.at' pt with
          | none =>
            exact Tree.Le.bot _
          | some tz =>
            rcases at'_mono pt hd₃ with hn | ⟨a', tz', ha', he₃', hab'⟩
            · rw [hd] at hn; exact Option.noConfusion hn
            · have hta : tz = a' := by rw [hd] at ha'; exact Option.some.inj ha'
              subst hta
              cases tz with
              | leaf v =>
                cases v with
                | bot =>
                  -- unknown: the approximant probes argument 3
                  dsimp only
                  rw [app3_node2, he₃']
                  cases tz' with
                  | leaf v' =>
                    cases v' with
                    | bot => exact Tree.Le.bot _
                    | err b => exact Tree.Le.refl _
                    | num a =>
                      dsimp only
                      have hst : Tree.Le ((pt.substAns (RAns.num a)).toTree) e₃ :=
                        substAns_toTree_le pt e₃ _ (.num a) he₃' rfl
                      have hj := Tree.join_spec d₃ ((pt.substAns (RAns.num a)).toTree)
                        e₃ hd₃ hst
                      refine Sfun_apply_le e₁ e₂ e₃ he₁ n _ d₂ _
                        (ft (pt.substAns (.num a)))
                        (at'_snoc_node e₁ q₁ ⟨0, h0⟩ pt ft _ hq₁) hd₂
                        (hj.2.2 e₃ hd₃ hst) (Accum.mono_d3 hj.1 hacc) ?_
                      rw [Query.ctx_snoc, Ctx.cons_other _ _ (fun he =>
                          absurd (congrArg Fin.val he) (by simp)),
                        apply0_congr_d3 hj.1 hacc]
                      exact hctx
                  | node jz pz fz =>
                    dsimp only
                    have hst : Tree.Le ((pt.substAns (RAns.node jz pz)).toTree) e₃ :=
                      substAns_toTree_le pt e₃ _ (.node jz pz) he₃' rfl
                    have hj := Tree.join_spec d₃ ((pt.substAns (RAns.node jz pz)).toTree)
                      e₃ hd₃ hst
                    refine Sfun_apply_le e₁ e₂ e₃ he₁ n _ d₂ _
                      (ft (pt.substAns (.node jz pz)))
                      (at'_snoc_node e₁ q₁ ⟨0, h0⟩ pt ft _ hq₁) hd₂
                      (hj.2.2 e₃ hd₃ hst) (Accum.mono_d3 hj.1 hacc) ?_
                    rw [Query.ctx_snoc, Ctx.cons_other _ _ (fun he =>
                        absurd (congrArg Fin.val he) (by simp)),
                      apply0_congr_d3 hj.1 hacc]
                    exact hctx
                | err b => exact Tree.Le.bot _
                | num a =>
                  -- known numeral answer
                  have hb2 : tz' = Tree.leaf (.num a) := by
                    cases hab' with
                    | leaf _ => rfl
                  subst hb2
                  rw [he₃']
                  dsimp only
                  exact Sfun_apply_le e₁ e₂ e₃ he₁ n _ d₂ d₃
                    (ft (pt.substAns (.num a)))
                    (at'_snoc_node e₁ q₁ ⟨0, h0⟩ pt ft _ hq₁) hd₂ hd₃ hacc
                    (by rw [Query.ctx_snoc, Ctx.cons_other _ _ (fun he =>
                      absurd (congrArg Fin.val he) (by simp))]; exact hctx)
              | node jz pz fz =>
                -- known intermediate answer
                obtain ⟨gz, hgz⟩ := Tree.eq_node_of_le hab'
                subst hgz
                rw [he₃']
                dsimp only
                exact Sfun_apply_le e₁ e₂ e₃ he₁ n _ d₂ d₃
                  (ft (pt.substAns (.node jz pz)))
                  (at'_snoc_node e₁ q₁ ⟨0, h0⟩ pt ft _ hq₁) hd₂ hd₃ hacc
                  (by rw [Query.ctx_snoc, Ctx.cons_other _ _ (fun he =>
                    absurd (congrArg Fin.val he) (by simp))]; exact hctx)
        | ⟨1, h1⟩ =>
          -- `x` asks about `y·z` at `pt`: enter the `T`-loop
          dsimp only
          have ht := TreeOk_at' q₁ Ctx.empty e₁ _ he₁ hq₁
          obtain ⟨hlq, _, _, _⟩ := TreeOk_node_inv ht
          have hper : (apply0 d₂ d₃).at' pt = some Tree.bot := hctx ▸ hlq.1
          obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := encode_spec d₃ d₂ pt hacc
            (QueryOk.coherent hlq.2) hper
          rcases at'_mono (encode d₂ pt) hd₂ with hn | ⟨a', t₂, ha', ht₂, hat₂⟩
          · rw [hE2] at hn; exact Option.noConfusion hn
          · exact Tfun_apply_le e₁ e₂ e₃ he₁ n q₁ pt (encode d₂ pt) d₂ d₃ ft t₂
              hq₁ ht₂ hd₂ hd₃ hacc hctx hE3 hE1 hE5 (FollowsToBot_of_at' _ _ hE2)
        | ⟨i + 2, hi⟩ =>
          dsimp only
          rw [app3_nodeRho, rhsRho hi pt ft e₃ (apply0 e₂ e₃)]
          refine Tree.Le.node _ _ _ _ fun s => ?_
          exact Sfun_apply_le e₁ e₂ e₃ he₁ n _ d₂ d₃ (ft s)
            (at'_snoc_node e₁ q₁ ⟨i + 2, hi⟩ pt ft s hq₁) hd₂ hd₃ hacc
            (by rw [Query.ctx_snoc, Ctx.cons_other _ _ (fun he =>
              absurd (congrArg Fin.val he) (by simp))]; exact hctx)

/-- **The `⊑`-half of Lemma A.7**, `T`-mode. -/
theorem Tfun_apply_le (e₁ : Tree (σ ⇒ τ ⇒ ρ)) (e₂ : Tree (σ ⇒ τ)) (e₃ : Tree σ)
    (he₁ : TreeOk Ctx.empty e₁) :
    ∀ (n : Nat) (q₁ : Query (σ ⇒ τ ⇒ ρ))
      (pτ : Query ((σ ⇒ τ ⇒ ρ).arg ⟨1, by show 1 < ρ.arity + 2; omega⟩))
      (q₂ : Query (σ ⇒ τ)) (d₂ : Tree (σ ⇒ τ)) (d₃ : Tree σ)
      (f₁ : Resp ((σ ⇒ τ ⇒ ρ).arg ⟨1, by show 1 < ρ.arity + 2; omega⟩)
        → Tree (σ ⇒ τ ⇒ ρ)) (t₂ : Tree (σ ⇒ τ)),
    e₁.at' q₁ = some (Tree.node ⟨1, by show 1 < ρ.arity + 2; omega⟩ pτ f₁) →
    e₂.at' q₂ = some t₂ →
    Tree.Le d₂ e₂ → Tree.Le d₃ e₃ → Accum d₃ d₂ →
    q₁.ctx ⟨1, by show 1 < ρ.arity + 2; omega⟩ = apply0 d₂ d₃ →
    q₂.Coherent → q₂.shift1 = pτ → ZConsistent d₃ q₂ → FollowsToBot d₂ q₂ →
    Tree.Le (app3 (Tfun n q₁ pτ q₂ d₂ d₃) e₁ e₂ e₃)
      (apply0 (apply0 (Tree.node ⟨1, by show 1 < ρ.arity + 2; omega⟩ pτ f₁) e₃)
        (apply0 e₂ e₃))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => Tree.Le.bot _
  | n + 1, q₁, pτ, q₂, d₂, d₃, f₁, t₂, hq₁, hq₂, hd₂, hd₃, hacc, hctx, hcoh,
      hshift, hzc, hfb => by
      simp only [Tfun]
      have habv : RespCtx.Above q₂.ctxList ⟨0, Nat.succ_pos _⟩ e₃ := fun r hr =>
        Tree.Le.trans (ZConsistent.above d₃ q₂ _ hzc r hr) hd₃
      have h414 : (apply0 e₂ e₃).at' pτ = some (apply0 t₂ e₃) := by
        rw [← hshift]
        exact lemma_4_14 q₂ e₂ t₂ e₃ hcoh hq₂ habv
      rw [app3_node1, hq₂]
      cases t₂ with
      | leaf v =>
        cases v with
        | bot => exact Tree.Le.bot _
        | err b =>
          dsimp only
          have h414' : (apply0 e₂ e₃).at' pτ = some (Tree.leaf (.err b)) := by
            rw [h414]; rfl
          rw [rhs1 _ pτ f₁ e₃ (apply0 e₂ e₃), h414']
          exact Tree.Le.refl _
        | num a =>
          dsimp only
          simp only [Query.answerOf_substAns]
          have h414' : (apply0 e₂ e₃).at' pτ = some (Tree.leaf (.num a)) := by
            rw [h414]; rfl
          rw [rhs1 _ pτ f₁ e₃ (apply0 e₂ e₃), h414']
          dsimp only
          have hst : Tree.Le ((q₂.substAns (RAns.num a)).toTree) e₂ :=
            substAns_toTree_le q₂ e₂ _ (.num a) hq₂ rfl
          have hj := Tree.join_spec d₂ ((q₂.substAns (RAns.num a)).toTree) e₂ hd₂ hst
          have hresN : (RAns.num a : RAns (σ ⇒ τ)).Resolved := by
            simp [RAns.Resolved]
          refine Sfun_apply_le e₁ e₂ e₃ he₁ n _ _ d₃ (f₁ (pτ.substAns (.num a)))
            (at'_snoc_node e₁ q₁ _ pτ f₁ _ hq₁) (hj.2.2 e₂ hd₂ hst) hd₃
            (Accum_join_resolved d₃ q₂ d₂ (.num a) hacc hfb hzc hresN) ?_
          rw [Query.ctx_snoc, Ctx.cons_self, hctx,
            apply0_join_resolved d₃ q₂ d₂ (.num a) hfb hzc hresN, hshift]
          rfl
      | node jz2 pz f₂ =>
        match jz2 with
        | ⟨0, hz⟩ =>
          -- `y` asks about `z` at `pz`
          dsimp only
          simp only [Query.answerOf_substAns]
          cases hd : d₃.at' pz with
          | none => exact Tree.Le.bot _
          | some tz =>
            rcases at'_mono pz hd₃ with hn | ⟨a', tz', ha', he₃', hab'⟩
            · rw [hd] at hn; exact Option.noConfusion hn
            · have hta : tz = a' := by rw [hd] at ha'; exact Option.some.inj ha'
              subst hta
              cases tz with
              | leaf v =>
                cases v with
                | bot =>
                  -- unknown: probe argument 3
                  dsimp only
                  rw [app3_node2, he₃']
                  cases tz' with
                  | leaf v' =>
                    cases v' with
                    | bot => exact Tree.Le.bot _
                    | err b =>
                      have happ : apply0 (Tree.node ⟨0, hz⟩ pz f₂) e₃
                          = Tree.leaf (.err b) := by
                        rw [apply0, he₃']
                      have h414' : (apply0 e₂ e₃).at' pτ
                          = some (Tree.leaf (.err b)) := by
                        rw [h414, happ]
                      rw [rhs1 _ pτ f₁ e₃ (apply0 e₂ e₃), h414']
                      exact Tree.Le.refl _
                    | num a =>
                      dsimp only
                      have hst : Tree.Le ((pz.substAns (RAns.num a)).toTree) e₃ :=
                        substAns_toTree_le pz e₃ _ (.num a) he₃' rfl
                      have hj := Tree.join_spec d₃ ((pz.substAns (RAns.num a)).toTree)
                        e₃ hd₃ hst
                      refine Tfun_apply_le e₁ e₂ e₃ he₁ n q₁ pτ _ d₂ _ f₁
                        (f₂ (pz.substAns (.num a))) hq₁
                        (at'_snoc_node e₂ q₂ ⟨0, hz⟩ pz f₂ _ hq₂) hd₂
                        (hj.2.2 e₃ hd₃ hst) (Accum.mono_d3 hj.1 hacc) ?_ ?_ ?_ ?_ ?_
                      · rw [apply0_congr_d3 hj.1 hacc]
                        exact hctx
                      · exact Query.coherent_snoc q₂ _ pz _ hcoh
                          (Query.qry_substAns pz (.num a))
                      · rw [Query.shift1_snoc0]
                        exact hshift
                      · refine ZConsistent_snoc0 _ q₂ hz pz (.num a) _
                          (ZConsistent.mono_d3 hj.1 q₂ hzc) ?_ rfl
                        exact at'_join_substAns pz d₃ (.num a) hd
                      · exact FollowsToBot_snoc q₂ d₂ ⟨0, hz⟩ pz _ hfb
                  | node jz3 pz3 fz3 =>
                    dsimp only
                    have hst : Tree.Le ((pz.substAns (RAns.node jz3 pz3)).toTree) e₃ :=
                      substAns_toTree_le pz e₃ _ (.node jz3 pz3) he₃' rfl
                    have hj := Tree.join_spec d₃
                      ((pz.substAns (RAns.node jz3 pz3)).toTree) e₃ hd₃ hst
                    refine Tfun_apply_le e₁ e₂ e₃ he₁ n q₁ pτ _ d₂ _ f₁
                      (f₂ (pz.substAns (.node jz3 pz3))) hq₁
                      (at'_snoc_node e₂ q₂ ⟨0, hz⟩ pz f₂ _ hq₂) hd₂
                      (hj.2.2 e₃ hd₃ hst) (Accum.mono_d3 hj.1 hacc) ?_ ?_ ?_ ?_ ?_
                    · rw [apply0_congr_d3 hj.1 hacc]
                      exact hctx
                    · exact Query.coherent_snoc q₂ _ pz _ hcoh
                        (Query.qry_substAns pz (.node jz3 pz3))
                    · rw [Query.shift1_snoc0]
                      exact hshift
                    · refine ZConsistent_snoc0 _ q₂ hz pz (.node jz3 pz3) _
                        (ZConsistent.mono_d3 hj.1 q₂ hzc) ?_ rfl
                      exact at'_join_substAns pz d₃ (.node jz3 pz3) hd
                    · exact FollowsToBot_snoc q₂ d₂ ⟨0, hz⟩ pz _ hfb
                | err b => exact Tree.Le.bot _
                | num a =>
                  -- known numeral answer from `d₃`
                  have hb2 : tz' = Tree.leaf (.num a) := by
                    cases hab' with
                    | leaf _ => rfl
                  subst hb2
                  dsimp only
                  exact Tfun_apply_le e₁ e₂ e₃ he₁ n q₁ pτ _ d₂ d₃ f₁
                    (f₂ (pz.substAns (.num a))) hq₁
                    (at'_snoc_node e₂ q₂ ⟨0, hz⟩ pz f₂ _ hq₂) hd₂ hd₃ hacc hctx
                    (Query.coherent_snoc q₂ _ pz _ hcoh
                      (Query.qry_substAns pz (.num a)))
                    (by rw [Query.shift1_snoc0]; exact hshift)
                    (ZConsistent_snoc0 _ q₂ hz pz (.num a) _ hzc hd rfl)
                    (FollowsToBot_snoc q₂ d₂ ⟨0, hz⟩ pz _ hfb)
              | node jz3 pz3 fz3 =>
                obtain ⟨gz, hgz⟩ := Tree.eq_node_of_le hab'
                subst hgz
                dsimp only
                exact Tfun_apply_le e₁ e₂ e₃ he₁ n q₁ pτ _ d₂ d₃ f₁
                  (f₂ (pz.substAns (.node jz3 pz3))) hq₁
                  (at'_snoc_node e₂ q₂ ⟨0, hz⟩ pz f₂ _ hq₂) hd₂ hd₃ hacc hctx
                  (Query.coherent_snoc q₂ _ pz _ hcoh
                    (Query.qry_substAns pz (.node jz3 pz3)))
                  (by rw [Query.shift1_snoc0]; exact hshift)
                  (ZConsistent_snoc0 _ q₂ hz pz (.node jz3 pz3) _ hzc hd rfl)
                  (FollowsToBot_snoc q₂ d₂ ⟨0, hz⟩ pz _ hfb)
        | ⟨j + 1, hj⟩ =>
          -- `y` announces a node about `τⱼ`: resolution
          dsimp only
          simp only [Query.answerOf_substAns]
          have happ : apply0 (Tree.node ⟨j + 1, hj⟩ pz f₂) e₃
              = Tree.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ pz
                  (fun r => apply0 (f₂ r) e₃) := by
            rw [apply0]
          have h414' : (apply0 e₂ e₃).at' pτ
              = some (Tree.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ pz
                  fun r => apply0 (f₂ r) e₃) := by
            rw [h414, happ]
          rw [rhs1 _ pτ f₁ e₃ (apply0 e₂ e₃), h414']
          dsimp only
          have hst : Tree.Le ((q₂.substAns (RAns.node ⟨j + 1, hj⟩ pz)).toTree) e₂ :=
            substAns_toTree_le q₂ e₂ _ (.node ⟨j + 1, hj⟩ pz) hq₂ rfl
          have hj2 := Tree.join_spec d₂
            ((q₂.substAns (RAns.node ⟨j + 1, hj⟩ pz)).toTree) e₂ hd₂ hst
          have hresN : (RAns.node ⟨j + 1, hj⟩ pz : RAns (σ ⇒ τ)).Resolved := by
            simp [RAns.Resolved]
          refine Sfun_apply_le e₁ e₂ e₃ he₁ n _ _ d₃
            (f₁ (pτ.substAns (.node ⟨j, Nat.lt_of_succ_lt_succ hj⟩ pz)))
            (at'_snoc_node e₁ q₁ _ pτ f₁ _ hq₁) (hj2.2.2 e₂ hd₂ hst) hd₃
            (Accum_join_resolved d₃ q₂ d₂ _ hacc hfb hzc hresN) ?_
          rw [Query.ctx_snoc, Ctx.cons_self, hctx,
            apply0_join_resolved d₃ q₂ d₂ _ hfb hzc hresN, hshift]
          rfl
end

end SCombinator


/-- `S_{σ,τ,ρ}` denotes the tree `S(?,?)` of **Definition 4.21**:
`⊔ₙ Sₙ(?, ?)`, starting from the trivial query and empty knowledge. -/
noncomputable def treeS (σ τ ρ : Ty) : T (STy σ τ ρ) :=
  idealOfChain (fun n => Sfun n .hole Tree.bot Tree.bot)
    (fun _ _ h => Sfun_le_of_le h .hole Tree.bot Tree.bot)

/-- **Lemma A.6.**  *For all `e₁, e₂, e₃` in appropriate domains,
`apply (S(?,?), e₁, e₂, e₃) = apply (apply (e₁, e₃), apply (e₂, e₃))`.*

The two halves are Claim A.4's analogue (every approximant computes at most
the right-hand side) and Lemma A.7 (the approximants reach every finite
approximation of it). -/
theorem lemma_A_6 (σ τ ρ : Ty) (e₁ : T (σ ⇒ τ ⇒ ρ)) (e₂ : T (σ ⇒ τ)) (e₃ : T σ) :
    applyT (applyT (applyT (treeS σ τ ρ) e₁) e₂) e₃
      = applyT (applyT e₁ e₃) (applyT e₂ e₃) := by
  sorry

/-- **Claim A.5**, packaged: the tree `S(?,?)` of Definition 4.21 exists and
satisfies the `(S)` equation.  The construction is `Sfun`/`Tfun` above; the
equation is Lemma A.6. -/
theorem claim_A_5 (σ τ ρ : Ty) :
    ∃ S : T (STy σ τ ρ), ∀ (e₁ : T (σ ⇒ τ ⇒ ρ)) (e₂ : T (σ ⇒ τ)) (e₃ : T σ),
      applyT (applyT (applyT S e₁) e₂) e₃ = applyT (applyT e₁ e₃) (applyT e₂ e₃) :=
  ⟨treeS σ τ ρ, lemma_A_6 σ τ ρ⟩

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
