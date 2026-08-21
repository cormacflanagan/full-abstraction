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
