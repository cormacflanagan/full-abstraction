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

/-! ## Inverting `q[?/x]` -/

namespace Query
variable {σ : Ty}

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

end Query

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

/-- `λ*f . apply (f, … apply (f, Ω_σ) …)` with `n` occurrences of `f` (§4.3). -/
def Yapprox (σ : Ty) : Nat → Comb SPCF
  | 0 => Comb.lamStar 0 (σ ⇒ σ) (Omega σ)
  | n + 1 => Comb.lamStar 0 (σ ⇒ σ) (.app (.var 0 (σ ⇒ σ)) (unfold n))
where
  /-- `apply (f, … apply (f, Ω_σ) …)` with `n` occurrences of the variable `f`. -/
  unfold : Nat → Comb SPCF
    | 0 => Omega σ
    | n + 1 => .app (.var 0 (σ ⇒ σ)) (unfold n)

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

/-- The model `T₀`: `T` with `Y_σ` interpreted as `⊥`.  It is used only to give
meaning to the `Y`-free approximants `Yapprox σ n`, exactly as in §4.3. -/
noncomputable def T0 : Model SPCF where
  Dom := T
  dom σ := inferInstance
  interpConst c := interpBase c
  interpS σ τ ρ := treeS σ τ ρ
  interpK σ τ := treeK σ τ
  interpI σ := treeI σ
  apply {σ τ} f d := applyT f d

/-- `T[[Y_σ]] = ⊔ {T[[λ*f . apply (f, … apply (f, Ω) …)]] | n ∈ ℕ}` (§4.3).

"It is easy to prove that the set … forms a chain by induction on `n` (since
`T[[apply]]` is monotonic).  Hence, the specified least upper bound exists." -/
theorem Y_chain_directed (σ : Ty) :
    DirectedSet (Set.range fun n => T0.combMeaning (fun _ _ => ScottDomain.bot)
      (Yapprox σ n) ((σ ⇒ σ) ⇒ σ)) := by
  sorry

/-- `T[[Y_σ]]`. -/
noncomputable def interpY (σ : Ty) : T ((σ ⇒ σ) ⇒ σ) :=
  ScottDomain.dsup _ (Y_chain_directed σ)

/-- **Definition 4.1** (*Tree model for SPCF*).

"`T` is the model for SPCF mapping: (1) each type `σ` to the tree domain `T_σ`;
(2) each constant `c` in `O ∪ F` to the tree defined in Section 4.3; and (3) the
function symbols `apply_{σ,τ}` to the functions `T[[apply_{σ,τ}]]`." -/
noncomputable def Tmodel : Model SPCF where
  Dom := T
  dom σ := inferInstance
  interpConst c :=
    match c with
    | .Y σ => interpY σ
    | c' => interpBase c'
  interpS σ τ ρ := treeS σ τ ρ
  interpK σ τ := treeK σ τ
  interpI σ := treeI σ
  apply {σ τ} f d := applyT f d

@[inherit_doc] scoped notation:max "T⟦" M "⟧" E => Model.meaning Tmodel E M

/-! ## Theorem 4.22 and its corollaries -/

/-- **Lemma A.1.**  *For all `d ∈ T_σ`, `e ∈ T_τ`,
`apply (K_{σ,τ}, d, e) = d`.* -/
theorem lemma_A_1 (σ τ : Ty) (d : T σ) (e : T τ) :
    applyT (applyT (treeK σ τ) d) e = d := by
  sorry

/-- **Claim A.2.**  *Let `d ∈ D_σ`, `e ∈ D_τ` and let `q ∈ Q_σ` be a valid path
in `d` (`d @ q` is defined).  Then `apply (K(q), d, e) = d @ q`.* -/
theorem claim_A_2 (σ τ : Ty) (d : Tree σ) (e : Tree τ) (q : Query σ) (d' : Tree σ)
    (hq : d.at' q = some d') (n : Nat) :
    ∀ m, n ≤ m → apply0 (apply0 (Kn σ τ m q) d) e ⊑ d' := by
  sorry

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

/-- The `(I)` equation of Theorem 4.22; "the proof for `I` closely follows the
proof for `K`". -/
theorem theorem_4_22_I : ∀ (σ : Ty) (x : T σ), applyT (treeI σ) x = x := by
  sorry

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

/-- **Corollary 4.23** (`β`, `η`).

"(i) If `E` is an environment that binds each variable `x^σ` in
`FV(M) ∪ FV(N)` to an element in `T_σ`, then
`T[[apply (λ*y . M, N)]]_E = T[[M[y := N]]]_E`.  (ii) … then
`T[[λ*y . apply (M, y)]]_E = T[[M]]_E` (if `y ∉ FV(M)`)."

"Both equations can be proved using standard methods; the proof of (η) depends
on the extensionality theorem (Theorem 4.11)." -/
theorem corollary_4_23 :
    (∀ (E : Tmodel.Env) (y : Nat) (σ ρ : Ty) (M N : Comb SPCF),
      Tmodel.combMeaning E (.app (Comb.lamStar y σ M) N) ρ
        = Tmodel.combMeaning E (Comb.subst y σ N M) ρ) ∧
    (∀ (E : Tmodel.Env) (y : Nat) (σ τ : Ty) (M : Comb SPCF),
      (y, σ) ∉ Comb.FV M →
      Tmodel.combMeaning E (Comb.lamStar y σ (.app M (.var y σ))) (σ ⇒ τ)
        = Tmodel.combMeaning E M (σ ⇒ τ)) := by
  sorry

/-- **Corollary 4.24** (`Y` operator).  *For all closed combinatory terms `M` of
type `σ → σ`, `T[[apply (M, apply (Y_σ, M))]] = T[[apply (Y_σ, M)]]`.* -/
theorem corollary_4_24 (σ : Ty) (M : Comb SPCF) (E : Tmodel.Env) :
    Tmodel.combMeaning E (.app M (.app (.const (.Y σ)) M)) σ
      = Tmodel.combMeaning E (.app (.const (.Y σ)) M) σ := by
  sorry

end FA
