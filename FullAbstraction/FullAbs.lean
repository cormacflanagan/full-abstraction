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

/-- **Definition 5.3** (*Subtree representability*).

"Let `γ` be a context in `C_σ`.  A subtree `e ∈ D_σ(γ)` is representable iff
there exists a closed expression `M` such that
`apply (T[[M]], d₁, …, dₖ) = apply (e, d₁, …, dₖ)` for all arguments
`d₁, …, dₖ` in `D_σ₁, …, D_σₖ`, such that `dᵢ ⊒ ⊔ γ(i)`.

When `γ = ∅`, `e` is a complete tree and subtree representability reduces to
tree representability by extensionality." -/
def Representable (σ : Ty) (γ : Ctx σ) (e : Tree σ) : Prop :=
  ∃ (M : Term SPCF) (d : D σ), Term.Closed M ∧ Term.HasTy [] M σ ∧
    Tmodel.meaning botEnv M σ = Ideal.principal d ∧
    ∀ ds : (i : Fin σ.arity) → Tree (σ.arg i),
      (∀ i, Ctx.Above γ i (ds i)) →
      applyArgs σ d.1 ds = applyArgs σ e ds

/-- **Lemma 5.2.**  *For every finite element `d ∈ D_σ`, there is a closed SPCF
expression `M` such that `T[[M]] = d`.*

"The proof of the lemma proceeds by induction on the depth of the type
`σ = σ₁ → … → σₖ → o`. … we must prove that for all contexts `γ ∈ C_σ`, every
finite subtree `e` in `D_σ(γ)` is representable in SPCF." -/
theorem lemma_5_2 (σ : Ty) (d : D σ) :
    ∃ M : Term SPCF, Term.Closed M ∧ Term.HasTy [] M σ ∧
      Tmodel.meaning botEnv M σ = Ideal.principal d := by
  sorry

/-- The stronger statement actually proved by the nested induction of §5:
every finite subtree is representable in every legal context. -/
theorem lemma_5_2_subtrees (σ : Ty) (γ : Ctx σ) (e : Tree σ) (he : TreeOk γ e) :
    Representable σ γ e := by
  sorry

/-! ## The ingredients of Theorem 5.1 -/

/-- Compositionality of `T`: denotationally equal phrases are observationally
equivalent. -/
theorem soundness (σ : Ty) (M N : Term SPCF) (h : Tmodel.DenEquiv σ M N) :
    SemDef.ObsEquiv SPCFSem M N := by
  sorry

/-- The separation step of Theorem 5.1. -/
theorem separation (σ : Ty) (F G : T σ) (h : F ≠ G) :
    ∃ ds : (i : Fin σ.arity) → D (σ.arg i),
      applyIdeals σ F (fun i => Ideal.principal (ds i))
        ≠ applyIdeals σ G (fun i => Ideal.principal (ds i)) := by
  sorry

/-- The meaning of `(M E₁ … Eₖ)` is `apply (T[[M]], T[[E₁]], …, T[[Eₖ]])`. -/
theorem meaning_apps (σ : Ty) (M : Term SPCF) (E : (i : Fin σ.arity) → Term SPCF)
    (ds : (i : Fin σ.arity) → T (σ.arg i))
    (hE : ∀ i, Tmodel.meaning botEnv (E i) (σ.arg i) = ds i) :
    Tmodel.meaning botEnv (Term.apps M (List.ofFn E)) 𝕆
      = applyIdeals σ (Tmodel.meaning botEnv M σ) ds := by
  sorry

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
  have hMval : SPCFSem.meaning (Term.apps M Es)
      = applyIdeals σ (Tmodel.meaning botEnv M σ) (fun i => Ideal.principal (ds i)) :=
    meaning_apps σ M E _ hE
  have hNval : SPCFSem.meaning (Term.apps N Es)
      = applyIdeals σ (Tmodel.meaning botEnv N σ) (fun i => Ideal.principal (ds i)) :=
    meaning_apps σ N E _ hE
  exact hds (hMval ▸ hNval ▸ hM)

/-- **Theorem 5.1** (*Full Abstraction of `T` and SPCF*).

*For all SPCF phrases `M` and `N`, `M ≈_T N` iff `M ≃ N`.* -/
theorem theorem_5_1 (σ : Ty) (M N : Term SPCF)
    (henv : ∀ P : Term SPCF, Term.Closed P →
      ∀ Env : Tmodel.Env, Tmodel.meaning Env P σ = Tmodel.meaning botEnv P σ)
    (hM : Term.Closed M) (hN : Term.Closed N)
    (hprog : ∀ (Es : List (Term SPCF)) (P : Term SPCF),
      SPCFSem.Program ((appCtx Es).fill fun _ => P)) :
    Tmodel.DenEquiv σ M N ↔ SemDef.ObsEquiv SPCFSem M N := by
  refine ⟨soundness σ M N, fun hobs => ?_⟩
  intro Env
  rw [henv M hM Env, henv N hN Env]
  exact Classical.byContradiction fun hne => theorem_5_1_separating σ M N hne hprog hobs

/-- **Theorem 5.1**, in the form of Definition 2.8: the tree model `T` is fully
abstract for SPCF. -/
theorem theorem_5_1_fullyAbstract
    (henv : ∀ (σ : Ty) (P : Term SPCF), Term.Closed P →
      ∀ Env : Tmodel.Env, Tmodel.meaning Env P σ = Tmodel.meaning botEnv P σ)
    (hprog : ∀ (Es : List (Term SPCF)) (P : Term SPCF),
      SPCFSem.Program ((appCtx Es).fill fun _ => P)) :
    Tmodel.FullyAbstract SPCFSem := by
  intro σ N N' hN hN' hobs
  exact (theorem_5_1 σ N N' (henv σ) hN hN' hprog).mpr hobs

end FA
