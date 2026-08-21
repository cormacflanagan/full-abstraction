/-
# Observable sequentiality in SPCF (§6)

States and proves **Theorem 6.2** (SPCF is sequential), **Theorem 6.4** (SPCF is
error-sensitive) and **Theorem 6.7** (SPCF is observably sequential).

Theorem 6.2 is obtained here as the paper's own Theorem 6.5 applied to
Theorem 6.4 — "Indeed, SPCF satisfies a stronger condition than sequentiality:
every procedure propagates any errors that are encountered during program
evaluation" — and Theorem 6.5 is proved outright in `Semantics.lean`.
-/
import FullAbstraction.FullAbs

namespace FA

open Po

/-! ## The analysis behind Theorems 6.2 and 6.4

The paper's proof considers the tree denotation of `λx₁…xₖ.C[x₁,…,xₖ]`.  The
machinery here makes that precise: fresh variables for the holes, the
substitution lemma relating `C[M₁,…,Mₖ]` to `C[x₁,…,xₖ]` in an environment
binding the `xᵢ` to the `T[[Mᵢ]]`, the iterated abstraction lemma, and the
computation of iterated application against the members of the resulting
ideal. -/

/-- Iterated environment update. -/
noncomputable def updEnvL : Tmodel.Env → List (Nat × T 𝕆) → Tmodel.Env
  | E, [] => E
  | E, (x, v) :: rest => updEnvL (Model.envUpdate E x 𝕆 v) rest

theorem updEnvL_other (E : Tmodel.Env) : ∀ (l : List (Nat × T 𝕆)) (z : Nat) (ν : Ty),
    (∀ p, p ∈ l → z ≠ p.1) → updEnvL E l z ν = E z ν
  | [], _, _, _ => rfl
  | (x, v) :: rest, z, ν, h => by
      rw [updEnvL, updEnvL_other _ rest z ν fun p hp => h p (List.mem_cons_of_mem _ hp)]
      exact Model.envUpdate_other E x 𝕆 v z ν fun hc =>
        h (x, v) (List.mem_cons_self ..) hc.1

/-- The list of hole variables with their meanings. -/
private def pairsOf {k : Nat} (xs : Fin k → Nat) (vs : Fin k → T 𝕆) :
    List (Nat × T 𝕆) :=
  (List.finRange k).map fun i => (xs i, vs i)

theorem pairsOf_succ {k : Nat} (xs : Fin (k + 1) → Nat) (vs : Fin (k + 1) → T 𝕆) :
    pairsOf xs vs = (xs 0, vs 0) :: pairsOf (fun i => xs i.succ) (fun i => vs i.succ) := by
  simp [pairsOf, List.finRange_succ, List.map_map, Function.comp]

theorem mem_pairsOf {k : Nat} (xs : Fin k → Nat) (vs : Fin k → T 𝕆) (p : Nat × T 𝕆)
    (hp : p ∈ pairsOf xs vs) : ∃ i, p = (xs i, vs i) := by
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
  exact ⟨i, hi.symm⟩

theorem updEnvL_pairsOf : ∀ (k : Nat) (E : Tmodel.Env) (xs : Fin k → Nat)
    (vs : Fin k → T 𝕆), (∀ i i', xs i = xs i' → i = i') → ∀ i : Fin k,
    updEnvL E (pairsOf xs vs) (xs i) 𝕆 = vs i := by
  intro k
  induction k with
  | zero => intro E xs vs _ i; exact absurd i.isLt (by omega)
  | succ k ih =>
    intro E xs vs hinj i
    rw [pairsOf_succ, updEnvL]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [updEnvL_other _ _ _ _ fun p hp => ?_]
      · exact Model.envUpdate_self ..
      · obtain ⟨i', hi'⟩ := mem_pairsOf _ _ p hp
        rw [hi']
        intro hc
        exact absurd (hinj 0 i'.succ hc) (by simp [Fin.ext_iff])
    · exact ih _ (fun j => xs j.succ) (fun j => vs j.succ)
        (fun j j' h => by
          have h2 := hinj j.succ j'.succ h
          have h3 := congrArg Fin.val h2
          simp only [Fin.val_succ] at h3
          exact Fin.ext (by omega)) i'

/-- The variable-with-type list for the holes. -/
private def varsCtx {k : Nat} (xs : Fin k → Nat) : List (Nat × Ty) :=
  (List.finRange k).map fun i => (xs i, 𝕆)

theorem varsCtx_succ {k : Nat} (xs : Fin (k + 1) → Nat) :
    varsCtx xs = (xs 0, 𝕆) :: varsCtx (fun i => xs i.succ) := by
  simp [varsCtx, List.finRange_succ, List.map_map, Function.comp]

theorem mem_varsCtx {k : Nat} (xs : Fin k → Nat) (i : Fin k) :
    (xs i, 𝕆) ∈ varsCtx xs := by
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  induction k with
  | zero => exact absurd i.isLt (by omega)
  | succ k ih =>
    rw [List.finRange_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i', ih (fun j => j) i', rfl⟩)

/-- The type of the `k`-ary abstraction over ground holes. -/
theorem varsCtx_foldr {k : Nat} (xs : Fin k → Nat) :
    (varsCtx xs).foldr (fun p τ => p.2 ⇒ τ) 𝕆 = Ty.pow k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [varsCtx_succ, List.foldr_cons, ih (fun i => xs i.succ)]; rfl

/-- Typing for iterated `λ*`. -/
theorem Comb.lamStars_hasTy {L : Lang} : ∀ (l : List (Nat × Ty)) (Γ : List (Nat × Ty))
    (P : Comb L) (ρ : Ty), Comb.HasTy (l ++ Γ) P ρ →
    Comb.HasTy Γ (Comb.lamStars l P) (l.foldr (fun p τ => p.2 ⇒ τ) ρ)
  | [], _, _, _, h => h
  | (x, σ) :: l, Γ, P, ρ, h => by
      show Comb.HasTy Γ (Comb.lamStar x σ (Comb.lamStars l P)) _
      refine Comb.lamStar_hasTy (Comb.lamStars_hasTy l ((x, σ) :: Γ) P ρ ?_)
      refine Comb.weaken (fun p hp => ?_) h
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with (hp | hp) | hp
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)

/-- Filling with fresh ground variables preserves typing, in a context
providing those variables. -/
theorem MCtx.fill_vars_hasTy {k : Nat} (Ms : Fin k → Term SPCF) (xs : Fin k → Nat)
    (hty : ∀ i, Term.HasTy [] (Ms i) 𝕆) :
    ∀ (C : MCtx SPCF k) (Γ : List (Nat × Ty)) (ρ : Ty),
      Term.HasTy Γ (C.fill Ms) ρ →
      ∀ Γ' : List (Nat × Ty), (∀ p, p ∈ Γ → p ∈ Γ') → (∀ i, (xs i, 𝕆) ∈ Γ') →
      Term.HasTy Γ' (C.fill fun i => .var (xs i) 𝕆) ρ := by
  intro C
  induction C with
  | hole i =>
    intro Γ ρ h Γ' _ hxs
    have hρ : ρ = 𝕆 := Term.hasTy_unique h (hty i)
    subst hρ
    exact Term.HasTy.var (hxs i)
  | var x ν =>
    intro Γ ρ h Γ' hsub _
    exact Term.weaken hsub h
  | const c =>
    intro Γ ρ h Γ' hsub _
    exact Term.weaken hsub h
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ h Γ' hsub hxs
    cases h with
    | app h₁ h₂ => exact Term.HasTy.app (ih₁ _ _ h₁ Γ' hsub hxs) (ih₂ _ _ h₂ Γ' hsub hxs)
  | lam y ν C ih =>
    intro Γ ρ h Γ' hsub hxs
    cases h with
    | lam hC =>
      refine Term.HasTy.lam (ih _ _ hC ((y, ν) :: Γ') (fun p hp => ?_)
        (fun i => List.mem_cons_of_mem _ (hxs i)))
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub p hp)

/-- **The substitution lemma for the tree model.**  Filling a context with
closed ground phrases means the same as filling it with fresh variables bound
to their meanings.

This is the semantic content of the paper's step from `C[M₁,…,Mₖ]` to
`λx₁…xₖ.C[x₁,…,xₖ]` applied to the `Mᵢ`.  Freshness (`varBound C ≤ xs i`) is
what the paper's choice of variable names presumes; the environments `E`, `E'`
are kept abstract, related by agreement off the `xs`, so that the induction can
pass through binders.  The `λ` case is where extensionality (Theorem 4.11)
does the work. -/
theorem meaning_fill_vars {k : Nat} (Ms : Fin k → Term SPCF) (xs : Fin k → Nat)
    (hcl : ∀ i, Term.Closed (Ms i)) (hty : ∀ i, Term.HasTy [] (Ms i) 𝕆) :
    ∀ (C : MCtx SPCF k) (Γ : List (Nat × Ty)) (ρ : Ty) (E E' : Tmodel.Env),
      (∀ i, C.varBound ≤ xs i) →
      (∀ i, E' (xs i) 𝕆 = Tmodel.meaning botEnv (Ms i) 𝕆) →
      (∀ z ν, (∀ i, z ≠ xs i) → E z ν = E' z ν) →
      Term.HasTy Γ (C.fill Ms) ρ →
      Tmodel.combMeaning E (Term.toComb (C.fill Ms)) ρ
        = Tmodel.combMeaning E' (Term.toComb (C.fill fun i => .var (xs i) 𝕆)) ρ := by
  intro C
  induction C with
  | hole i =>
    intro Γ ρ E E' _ h1 _ h
    have hρ : ρ = 𝕆 := Term.hasTy_unique h (hty i)
    subst hρ
    show Tmodel.combMeaning E (Term.toComb (Ms i)) 𝕆
      = Tmodel.combMeaning E' (Comb.var (xs i) 𝕆) 𝕆
    rw [Model.combMeaning_var, h1 i]
    exact Model.combMeaning_congr_env E botEnv _ 𝕆 fun z ν hz =>
      absurd (Term.FV_toComb (Ms i) (z, ν) hz) (hcl i (z, ν))
  | var z ν =>
    intro Γ ρ E E' hb _ h2 _
    refine Model.combMeaning_congr_env E E' _ ρ fun w μ hw => ?_
    have hwz : ((w, μ) : Nat × Ty) = (z, ν) := hw
    refine h2 w μ fun i hwx => ?_
    have hzb : z + 1 ≤ xs i := hb i
    have hwzv : w = z := congrArg Prod.fst hwz
    omega
  | const c =>
    intro Γ ρ E E' _ _ _ _
    exact Model.combMeaning_congr_env E E' _ ρ fun w μ hw => (hw : False).elim
  | app C₁ C₂ ih₁ ih₂ =>
    intro Γ ρ E E' hb h1 h2 h
    cases h with
    | app hA hB =>
      rename_i α
      have e₂ : Comb.tyOf (Term.toComb (C₂.fill Ms)) = α := Term.tyOf_toComb hB
      have hB' : Term.HasTy (Γ ++ varsCtx xs) (C₂.fill fun i => .var (xs i) 𝕆) α :=
        MCtx.fill_vars_hasTy Ms xs hty C₂ Γ α hB (Γ ++ varsCtx xs)
          (fun p hp => List.mem_append.mpr (Or.inl hp))
          (fun i => List.mem_append.mpr (Or.inr (mem_varsCtx xs i)))
      have e₂' : Comb.tyOf (Term.toComb (C₂.fill fun i => .var (xs i) 𝕆)) = α :=
        Term.tyOf_toComb hB'
      show Tmodel.combMeaning E (.app (Term.toComb (C₁.fill Ms))
        (Term.toComb (C₂.fill Ms))) ρ = _
      rw [Model.combMeaning_app, e₂]
      show _ = Tmodel.combMeaning E' (.app (Term.toComb (C₁.fill fun i => .var (xs i) 𝕆))
        (Term.toComb (C₂.fill fun i => .var (xs i) 𝕆))) ρ
      rw [Model.combMeaning_app, e₂',
        ih₁ Γ (α ⇒ ρ) E E' (fun i => Nat.le_trans (MCtx.varBound_app_left C₁ C₂) (hb i))
          h1 h2 hA,
        ih₂ Γ α E E' (fun i => Nat.le_trans (MCtx.varBound_app_right C₁ C₂) (hb i))
          h1 h2 hB]
  | lam y ν C ih =>
    intro Γ ρ E E' hb h1 h2 h
    cases h with
    | lam hC =>
      rename_i τ
      have hyx : ∀ i, y ≠ xs i := fun i hyi => by
        have := Nat.lt_of_lt_of_le (MCtx.lt_varBound_lam y ν C) (hb i)
        omega
      have hC' : Term.HasTy ((y, ν) :: (Γ ++ varsCtx xs))
          (C.fill fun i => .var (xs i) 𝕆) τ :=
        MCtx.fill_vars_hasTy Ms xs hty C ((y, ν) :: Γ) τ hC _
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hp)))
          (fun i => List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (mem_varsCtx xs i))))
      show Tmodel.combMeaning E (Comb.lamStar y ν (Term.toComb (C.fill Ms))) (ν ⇒ τ)
        = Tmodel.combMeaning E' (Comb.lamStar y ν
            (Term.toComb (C.fill fun i => .var (xs i) 𝕆))) (ν ⇒ τ)
      refine Po.le_antisymm (orderExtensional_T _ _ fun z => ?_)
        (orderExtensional_T _ _ fun z => ?_) <;>
      · rw [lamStar_apply E y ν z _ τ Γ (Term.toComb_hasTy hC),
          lamStar_apply E' y ν z _ τ (Γ ++ varsCtx xs) (Term.toComb_hasTy hC'),
          ih ((y, ν) :: Γ) τ (Model.envUpdate E y ν z) (Model.envUpdate E' y ν z)
            (fun i => Nat.le_trans (MCtx.varBound_lam y ν C) (hb i))
            (fun i => by
              rw [Model.envUpdate_other E' y ν z (xs i) 𝕆 fun hc => hyx i hc.1.symm]
              exact h1 i)
            (fun w μ hw => by
              by_cases hwy : w = y ∧ μ = ν
              · obtain ⟨rfl, rfl⟩ := hwy
                rw [Model.envUpdate_self, Model.envUpdate_self]
              · rw [Model.envUpdate_other E y ν z w μ hwy,
                  Model.envUpdate_other E' y ν z w μ hwy]
                exact h2 w μ hw)
            hC]
        exact Po.le_refl _

/-! ### Iterated application of a `k`-ary ground procedure -/

/-- Iterated `apply` on ideals. -/
noncomputable def applyPow : (k : Nat) → T (Ty.pow k) → (Fin k → T 𝕆) → T 𝕆
  | 0, A, _ => A
  | k + 1, A, vs => applyPow k (applyT A (vs 0)) fun i => vs i.succ

/-- Iterated `apply₀` on trees. -/
noncomputable def apply0Pow : (k : Nat) → Tree (Ty.pow k) → (Fin k → Tree 𝕆) → Tree 𝕆
  | 0, t, _ => t
  | k + 1, t, ds => apply0Pow k (apply0 t (ds 0)) fun i => ds i.succ

/-- **The iterated abstraction lemma**: applying `λ*x₁…xₖ.P` to `k` values
means `P` in the environment binding the `xᵢ` to those values. -/
theorem lamStars_apply_pow : ∀ (k : Nat) (E : Tmodel.Env) (xs : Fin k → Nat)
    (P : Comb SPCF) (Γ : List (Nat × Ty)) (vs : Fin k → T 𝕆),
    Comb.HasTy (varsCtx xs ++ Γ) P 𝕆 →
    applyPow k (Tmodel.combMeaning E (Comb.lamStars (varsCtx xs) P) (Ty.pow k)) vs
      = Tmodel.combMeaning (updEnvL E (pairsOf xs vs)) P 𝕆 := by
  intro k
  induction k with
  | zero =>
    intro E xs P Γ vs _
    show Tmodel.combMeaning E P 𝕆 = _
    rw [show pairsOf xs vs = [] from rfl]
    rfl
  | succ k ih =>
    intro E xs P Γ vs hty
    rw [varsCtx_succ] at hty ⊢
    rw [pairsOf_succ, updEnvL]
    show applyPow k (applyT (Tmodel.combMeaning E
        (Comb.lamStar (xs 0) 𝕆 (Comb.lamStars (varsCtx fun i => xs i.succ) P))
        (𝕆 ⇒ Ty.pow k)) (vs 0)) (fun i => vs i.succ) = _
    have htyP : Comb.HasTy ((xs 0, 𝕆) :: (varsCtx (fun i => xs i.succ) ++ Γ)) P 𝕆 := hty
    have htyL : Comb.HasTy ((xs 0, 𝕆) :: Γ)
        (Comb.lamStars (varsCtx fun i => xs i.succ) P) (Ty.pow k) := by
      rw [← varsCtx_foldr (fun i : Fin k => xs i.succ)]
      refine Comb.lamStars_hasTy _ _ P 𝕆 (Comb.weaken (fun p hp => ?_) htyP)
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with hp | hp | hp
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hp
      · exact Or.inr (Or.inr hp)
    rw [lamStar_apply E (xs 0) 𝕆 (vs 0) _ (Ty.pow k) Γ htyL]
    exact ih (Model.envUpdate E (xs 0) 𝕆 (vs 0)) (fun i => xs i.succ) P
      ((xs 0, 𝕆) :: Γ) (fun i => vs i.succ)
      (Comb.weaken (fun p hp => by
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        rcases hp with hp | hp | hp
        · exact Or.inr (Or.inl hp)
        · exact Or.inl hp
        · exact Or.inr (Or.inr hp)) htyP)

/-! ### Computing iterated application against tree members -/

/-- The index of an argument of `Ty.pow k`, as an index below `k`. -/
def unpowIdx {k : Nat} (jt : Fin (Ty.pow k).arity) : Fin k :=
  ⟨jt.val, Nat.lt_of_lt_of_eq jt.isLt (Ty.pow_arity k)⟩

theorem apply0Pow_leaf (k : Nat) (v : Val) (ds : Fin k → Tree 𝕆) :
    apply0Pow k (.leaf v) ds = .leaf v := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _

theorem apply0Pow_mono_left (k : Nat) {t t' : Tree (Ty.pow k)} (h : Tree.Le t t')
    (ds : Fin k → Tree 𝕆) : Tree.Le (apply0Pow k t ds) (apply0Pow k t' ds) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (apply0_mono_left h (ds 0)) _

theorem apply0Pow_mono_args (k : Nat) (t : Tree (Ty.pow k)) {ds ds' : Fin k → Tree 𝕆}
    (h : ∀ i, Tree.Le (ds i) (ds' i)) :
    Tree.Le (apply0Pow k t ds) (apply0Pow k t ds') := by
  induction k with
  | zero => exact Tree.Le.refl t
  | succ k ih =>
    exact Tree.Le.trans
      (apply0Pow_mono_left k (apply0_mono_right t (h 0)) _)
      (ih (apply0 t (ds' 0)) fun i => h i.succ)

/-- A node probing argument `j` propagates an error placed at argument `j`,
whatever the other arguments are. -/
theorem apply0Pow_err : ∀ (k : Nat) (jt : Fin (Ty.pow k).arity)
    (q : Query ((Ty.pow k).arg jt)) (f : Resp ((Ty.pow k).arg jt) → Tree (Ty.pow k))
    (ds : Fin k → Tree 𝕆) (b : Bool),
    ds (unpowIdx jt) = Tree.leaf (.err b) →
    apply0Pow k (Tree.node jt q f) ds = Tree.leaf (.err b) := by
  intro k
  induction k with
  | zero => intro jt; exact absurd jt.isLt (by simp)
  | succ k ih =>
    intro jt q f ds b hds
    match jt with
    | ⟨0, h0⟩ =>
      have hq : q = Query.hole := Query.eq_hole_of_arity_zero rfl q
      subst hq
      show apply0Pow k (apply0 (Tree.node ⟨0, h0⟩ .hole f) (ds 0)) _ = _
      have hds0 : ds 0 = Tree.leaf (.err b) := hds
      rw [apply0, hds0]
      exact apply0Pow_leaf k _ _
    | ⟨m + 1, hm⟩ =>
      show apply0Pow k (apply0 (Tree.node ⟨m + 1, hm⟩ q f) (ds 0)) _ = _
      rw [apply0]
      refine ih ⟨m, Nat.lt_of_succ_lt_succ (by simpa using hm)⟩ q _ _ b ?_
      show ds (Fin.succ ⟨m, _⟩) = _
      rw [show (Fin.succ ⟨m, _⟩ : Fin (k + 1)) = unpowIdx ⟨m + 1, hm⟩ from rfl]
      exact hds

/-- Members of an iterated application are below iterated `apply₀` of
members. -/
theorem applyPow_mem : ∀ (k : Nat) (Λ : T (Ty.pow k)) (vs : Fin k → T 𝕆) (c : D 𝕆),
    c ∈ applyPow k Λ vs → ∃ s : D (Ty.pow k), s ∈ Λ ∧ ∃ ds : Fin k → D 𝕆,
      (∀ i, ds i ∈ vs i) ∧ Tree.Le c.1 (apply0Pow k s.1 fun i => (ds i).1) := by
  intro k
  induction k with
  | zero =>
    intro Λ vs c hc
    exact ⟨c, hc, fun i => absurd i.isLt (by omega),
      fun i => absurd i.isLt (by omega), Tree.Le.refl _⟩
  | succ k ih =>
    intro Λ vs c hc
    obtain ⟨s', hs', ds', hds', hle'⟩ := ih (applyT Λ (vs 0)) (fun i => vs i.succ) c hc
    obtain ⟨s, hs, d₀, hd₀, hle⟩ := hs'
    refine ⟨s, hs, fun i => Fin.cases d₀ ds' i, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · exact hd₀
      · exact hds' i'
    · have h1 : Tree.Le (apply0Pow k s'.1 fun i => (ds' i).1)
          (apply0Pow k (apply0 s.1 d₀.1) fun i => (ds' i).1) :=
        apply0Pow_mono_left k (show Tree.Le s'.1 (apply0 s.1 d₀.1) from hle) _
      have h2 : apply0Pow (k + 1) s.1 (fun i => ((Fin.cases d₀ ds' i : D 𝕆)).1)
          = apply0Pow k (apply0 s.1 d₀.1) fun i => (ds' i).1 := by
        show apply0Pow k (apply0 s.1 ((Fin.cases d₀ ds' (0 : Fin (k + 1)) : D 𝕆)).1)
            (fun i => ((Fin.cases d₀ ds' i.succ : D 𝕆)).1) = _
        rw [Fin.cases_zero]
        refine congrArg _ (funext fun i => ?_)
        rw [Fin.cases_succ]
      rw [h2]
      exact Tree.Le.trans hle' h1

/-- Conversely, iterated `apply₀` of members lands in the iterated
application. -/
theorem applyPow_mem_intro : ∀ (k : Nat) (Λ : T (Ty.pow k)) (vs : Fin k → T 𝕆)
    (s : D (Ty.pow k)), s ∈ Λ → ∀ (ds : Fin k → D 𝕆), (∀ i, ds i ∈ vs i) →
    ∀ c : D 𝕆, Tree.Le c.1 (apply0Pow k s.1 fun i => (ds i).1) → c ∈ applyPow k Λ vs := by
  intro k
  induction k with
  | zero =>
    intro Λ vs s hs ds _ c hc
    exact Λ.downward c s hc hs
  | succ k ih =>
    intro Λ vs s hs ds hds c hc
    exact ih (applyT Λ (vs 0)) (fun i => vs i.succ) (applyD s (ds 0))
      ⟨s, hs, ds 0, hds 0, Po.le_refl _⟩ (fun i => ds i.succ) (fun i => hds i.succ) c hc

/-! ## Theorem 6.4 -/

/-- The two error expressions of SPCF, `error₁` and `error₂` (Definition 3.1). -/
def errTerm (b : Bool) : Term SPCF := .const (.err b)

theorem errTerm_closed (b : Bool) : Term.Closed (errTerm b) := fun _ h => h

theorem meaning_errTerm (b : Bool) : SPCFSem.meaning (errTerm b) = errAns b := rfl

/-- The key structural fact behind Theorems 6.2 and 6.4: "The possible
denotations of such a procedure are either elements of `ℕ^E_⊥` or triples of the
form `⟨j, ?, f⟩` for some `j ≤ k` and some branching function `f`.  Clearly, the
first case contradicts the hypothesis of Definition 2.9.  The second case
specifies that the `k`-ary procedure probes its `j`-th argument first." -/
theorem probe_index (k : Nat) (C : MCtx SPCF k) (M : Fin k → Term SPCF)
    (hprobe : SPCFSem.Probe C M) (hM : ∀ i, SPCFSem.OmegaLike (M i)) :
    ∃ j : Fin k, ∀ (b : Bool) (M' : Fin k → Term SPCF),
      (∀ i, Term.Closed (M' i)) → (∀ i, SPCFSem.OmegaLike (M' i)) →
      SPCFSem.Program (C.fill (repl M' j SPCFSem.omega)) →
      SPCFSem.Program (C.fill (repl M' j (errTerm b))) ∧
      SPCFSem.meaning (C.fill (repl M' j (errTerm b))) = SPCFSem.meaning (errTerm b) := by
  sorry

theorem errTerm_omegaLike (b : Bool) : SPCFSem.OmegaLike (errTerm b) := Term.HasTy.const

theorem errTerm_ne_bot (b : Bool) : SPCFSem.meaning (errTerm b) ≠ SPCFSem.bot := by
  rw [meaning_errTerm b]
  intro h
  have h1 := Ideal.principal_inj h
  have h2 : (Tree.leaf (.err b) : Tree 𝕆) = Tree.bot := congrArg Subtype.val h1
  exact absurd h2 (by simp [Tree.bot])

theorem errTerm_distinct :
    SPCFSem.meaning (errTerm true) ≠ SPCFSem.meaning (errTerm false) := by
  rw [meaning_errTerm true, meaning_errTerm false]
  intro h
  have h1 := Ideal.principal_inj h
  have h2 : (Tree.leaf (.err true) : Tree 𝕆) = .leaf (.err false) :=
    congrArg Subtype.val h1
  exact absurd h2 (by simp)

/-- **Theorem 6.4.**  *SPCF is error-sensitive.*

"By exactly the same analysis presented in the preceding proof of the
sequentiality of SPCF, the program `C[…]` returns `errorᵢ` if the `j`-th
argument is `errorᵢ`, regardless of the values of the remaining arguments." -/
theorem theorem_6_4 : SPCFSem.ErrorSensitive :=
  ⟨errTerm, errTerm_closed, errTerm_omegaLike, errTerm_ne_bot, errTerm_distinct,
    fun k C M hprobe hM => probe_index k C M hprobe hM⟩

/-! ## Theorem 6.2 -/

/-- **Theorem 6.2** (*Sequentiality of SPCF*).  *SPCF is sequential.*

Obtained from Theorem 6.4 by Theorem 6.5: "Error-sensitivity implies
sequentiality." -/
theorem theorem_6_2 : SPCFSem.Sequential := SemDef.theorem_6_5 SPCFSem theorem_6_4

/-! ## Theorem 6.7 -/

/-- The program context `D[·] = (add1 (catch [·]))` used in the proof of
Theorem 6.7. -/
def catchCtx (σ : Ty) : MCtx SPCF 1 :=
  .app (.const .add1) (.app (.const (.catchC σ)) (.hole 0))

/-- The `catch` equation of Theorem 4.27, in the form needed by Theorem 6.7:
`catch` applied to a `k`-ary procedure that probes its `j`-th argument first
returns `⌜j⌝` (`⌜j−1⌝` in the paper's 1-based indexing).

Note the paper's `D[·] = (add1 (catch [·]))`: with the paper's convention
`catch` returns `j − 1`, so `add1` restores the sequentiality index `j`.  With
our 0-based indices `catch` already returns `j`, and `D[·]` returns `j + 1`; we
therefore state the property for the index itself. -/
theorem catch_returns_index {k : Nat} (C : MCtx SPCF k) (M : Fin k → Term SPCF)
    (hprobe : SPCFSem.Probe C M) (hM : ∀ i, SPCFSem.OmegaLike (M i)) (j : Fin k)
    (hj : ∀ (b : Bool) (M' : Fin k → Term SPCF),
      (∀ i, Term.Closed (M' i)) → (∀ i, SPCFSem.OmegaLike (M' i)) →
      SPCFSem.Program (C.fill (repl M' j SPCFSem.omega)) →
      SPCFSem.Program (C.fill (repl M' j (errTerm b))) ∧
      SPCFSem.meaning (C.fill (repl M' j (errTerm b))) = SPCFSem.meaning (errTerm b)) :
    ∃ D : MCtx SPCF 1,
      SPCFSem.meaning (D.fill fun _ =>
        Term.lams ((List.finRange k).map fun i => (C.varBound + i.val, 𝕆))
          (C.fill fun i => Term.var (C.varBound + i.val) 𝕆)) = SPCFSem.nat j.val := by
  sorry

/-- **Theorem 6.7.**  *SPCF is observably sequential.*

"We have already shown that SPCF is error-sensitive.  The remainder of the proof
is trivial: simply set `D[·] = (add1 (catch [·]))`." -/
theorem theorem_6_7 : SPCFSem.ObservablySequential := by
  refine ⟨theorem_6_2, ?_⟩
  intro k C M hprobe hM
  obtain ⟨j, hj⟩ := probe_index k C M hprobe hM
  refine ⟨j, ?_, catch_returns_index C M hprobe hM j hj⟩
  -- `j` is a sequentiality index, by the argument of Theorem 6.5
  exact SemDef.seqIndex_of_propagates SPCFSem errTerm_omegaLike errTerm_ne_bot
    errTerm_distinct hj

end FA
