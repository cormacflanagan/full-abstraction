/-
# The general semantic framework (§2.1, §2.2, §6)

Formalises the language-independent definitions of the paper —

* **Definition 2.1** (semantic definition),
* **Definition 2.3** (denotational model),
* **Definition 2.4** (semantics of closed phrases),
* **Definition 2.5** (semantics of open phrases),
* **Definition 2.6** (semantic definition of PCF),
* **Definition 2.8** (denotational / observational equivalence, full abstraction),
* **Definition 2.9** (sequentiality),
* **Definition 4.10** (extensionality, order-extensionality),
* **Definition 6.3** (error-sensitivity),
* **Definition 6.6** (observable sequentiality)

— and proves **Theorem 6.5**: error-sensitivity implies sequentiality.
-/
import FullAbstraction.Order
import FullAbstraction.Syntax

namespace FA

open Po

/-! ## Definition 2.1: semantic definitions

"Let `L` be a language based on the typed λ-calculus.  A semantic definition
for `L` is a function `P` mapping the programs of `L` to meanings in a set `A`
of answers." -/

/-- **Definition 2.1** (*Semantic Definition*).

The answer set is equipped with the structure the paper tacitly uses in §6: it
is a *flat* domain of ground values containing the naturals and a least element
`⊥` (Definition 2.7), `Ω` is a canonical divergent program, and the meaning
function is monotone in each hole of a context. -/
structure SemDef (L : Lang) where
  /-- The set `A` of answers. -/
  Ans : Type
  /-- Answers carry the approximation ordering `⊑` of Definition 2.7. -/
  po : Po Ans
  /-- `⊥`, the meaning of a divergent program. -/
  bot : Ans
  bot_le : ∀ a, @Po.le _ po bot a
  /-- `A` is a *flat* domain: distinct proper answers are incomparable. -/
  flat : ∀ a b, a ≠ bot → @Po.le _ po a b → a = b
  /-- The embedding of the natural-number answers. -/
  nat : Nat → Ans
  nat_inj : ∀ m n, nat m = nat n → m = n
  nat_ne_bot : ∀ n, nat n ≠ bot
  /-- Which phrases are *programs*. -/
  Program : Term L → Prop
  /-- `P[[·]]`. -/
  meaning : Term L → Ans
  /-- A canonical divergent expression `Ω`. -/
  omega : Term L
  meaning_omega : meaning omega = bot
  /-- The meaning function is monotone in every hole: replacing `Ω` by any
  phrase can only increase the answer.

  The two `Program` hypotheses are needed.  Without them the field is *false*:
  if `N` does not have the type of hole `j`, the filled context is ill-typed and
  its meaning is unconstrained, so it need not dominate the meaning of the
  well-typed `Ω`-fill. -/
  mono : ∀ {k : Nat} (C : MCtx L k) (M : Fin k → Term L) (j : Fin k) (N : Term L),
    Program (C.fill (repl M j omega)) → Program (C.fill (repl M j N)) →
    @Po.le _ po (meaning (C.fill (repl M j omega))) (meaning (C.fill (repl M j N)))

namespace SemDef
variable {L : Lang} (P : SemDef L)

/-- `⊑` on answers. -/
scoped notation:50 a " ⊑[" P "] " b => @Po.le _ (SemDef.po P) a b

/-- "`P[[M]] ∈ ℕ`": the program returns a natural-number answer. -/
def Returns (M : Term L) : Prop := ∃ n : Nat, P.meaning M = P.nat n

/-- "`P[[M]] = P[[Ω]]`": the program diverges. -/
def Diverges (M : Term L) : Prop := P.meaning M = P.bot

theorem returns_ne_bot {M : Term L} (h : P.Returns M) : P.meaning M ≠ P.bot := by
  obtain ⟨n, hn⟩ := h; rw [hn]; exact P.nat_ne_bot n

/-- Two answers below two *distinct* proper answers must be `⊥`: this is what
"denoting distinct and inconsistent elements of a flat domain" buys us
(Definition 6.3, used in the proof of Theorem 6.5). -/
theorem eq_bot_of_le_two {a b c : P.Ans} (hb : b ≠ P.bot) (hc : c ≠ P.bot)
    (hbc : b ≠ c) (h₁ : a ⊑[P] b) (h₂ : a ⊑[P] c) : a = P.bot :=
  Classical.byContradiction fun hne =>
    hbc ((P.flat a b hne h₁).symm.trans (P.flat a c hne h₂))

end SemDef

/-! ## Definitions 2.3–2.5: denotational models -/

/-- **Definition 2.3** (*Denotational Model*).

"A denotational model `M` for `L` is a function interpreting each type `σ`,
each constant in `F ∪ O`, and each function symbol in the set `A` of `apply`
symbols.  `M` maps each type `σ` to a Scott domain `M_σ`, each constant `c` of
type `σ` to an element in `M_σ`, and each function symbol `apply_{σ,τ}` to a
function `M[[apply_{σ,τ}]] : M_{σ→τ} × M_σ → M_τ`." -/
structure Model (L : Lang) where
  /-- The Scott domain `M_σ` interpreting the type `σ`. -/
  Dom : Ty → Type
  /-- "`M` maps each type `σ` to a Scott domain `M_σ`" (Definition 2.3). -/
  dom : ∀ σ, ScottDomain (Dom σ)
  /-- The interpretation of the constants of `L`. -/
  interpConst : (c : L.Const) → Dom (L.constTy c)
  /-- The interpretation of `S_{σ,τ,ρ}`. -/
  interpS : ∀ σ τ ρ, Dom ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  /-- The interpretation of `K_{σ,τ}`. -/
  interpK : ∀ σ τ, Dom (σ ⇒ τ ⇒ σ)
  /-- The interpretation of `I_σ`. -/
  interpI : ∀ σ, Dom (σ ⇒ σ)
  /-- The interpretation `M[[apply_{σ,τ}]]` of the function symbols. -/
  apply : ∀ {σ τ}, Dom (σ ⇒ τ) → Dom σ → Dom τ

namespace Model
variable {L : Lang} (M : Model L)

/-- Each `M_σ` is a Scott domain, hence in particular a partial order. -/
instance domScott (M : Model L) (σ : Ty) : ScottDomain (M.Dom σ) := M.dom σ

/-- An environment `E` maps each variable `x^σ` to an element of `M_σ`. -/
def Env := (x : Nat) → (σ : Ty) → M.Dom σ

/-- **Definitions 2.4 and 2.5** (*Semantics of Closed / Open Phrases*).

"The algebraic meaning that `M` assigns to the combinatory term `[N]_CL`."
The meaning is defined on combinatory terms; the meaning of a λ-term `N` is by
definition the meaning of `[N]_CL`.

The definition is partial in the same sense as the paper's: the interpretation
of an ill-typed application is unconstrained, so we return a default element of
the expected domain. -/
def combMeaning (E : M.Env) : (t : Comb L) → (σ : Ty) → M.Dom σ
  | .var x τ, σ => if h : τ = σ then h ▸ E x τ else (M.dom σ).bot
  | .const c, σ => if h : L.constTy c = σ then h ▸ M.interpConst c else (M.dom σ).bot
  | .S a b c, σ =>
      if h : ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c) = σ then h ▸ M.interpS a b c
      else (M.dom σ).bot
  | .K a b, σ => if h : (a ⇒ b ⇒ a) = σ then h ▸ M.interpK a b else (M.dom σ).bot
  | .I a, σ => if h : (a ⇒ a) = σ then h ▸ M.interpI a else (M.dom σ).bot
  | .app t u, σ =>
      let α := Comb.tyOf u
      M.apply (combMeaning E t (α ⇒ σ)) (combMeaning E u α)

/-- `E[x^σ := v]`, the environment `E` updated at one variable. -/
noncomputable def envUpdate {L : Lang} {M : Model L} (E : M.Env) (x : Nat) (σ : Ty)
    (v : M.Dom σ) : M.Env :=
  fun z ν => if h : z = x ∧ ν = σ then h.2.symm ▸ v else E z ν

theorem envUpdate_self {L : Lang} {M : Model L} (E : M.Env) (x : Nat) (σ : Ty)
    (v : M.Dom σ) : envUpdate E x σ v x σ = v := by
  show (if h : x = x ∧ σ = σ then h.2.symm ▸ v else E x σ) = v
  rw [dif_pos (⟨rfl, rfl⟩ : x = x ∧ σ = σ)]

theorem envUpdate_other {L : Lang} {M : Model L} (E : M.Env) (x : Nat) (σ : Ty)
    (v : M.Dom σ) (z : Nat) (ν : Ty) (h : ¬ (z = x ∧ ν = σ)) :
    envUpdate E x σ v z ν = E z ν := by
  show (if h : z = x ∧ ν = σ then h.2.symm ▸ v else E z ν) = E z ν
  rw [dif_neg h]

@[simp] theorem combMeaning_var (E : M.Env) (x : Nat) (τ : Ty) :
    M.combMeaning E (.var x τ) τ = E x τ := by
  show (if h : τ = τ then h ▸ E x τ else (M.dom τ).bot) = _
  rw [dif_pos rfl]

@[simp] theorem combMeaning_const (E : M.Env) (c : L.Const) :
    M.combMeaning E (.const c) (L.constTy c) = M.interpConst c := by
  show (if h : L.constTy c = L.constTy c then h ▸ M.interpConst c else _) = _
  rw [dif_pos rfl]

@[simp] theorem combMeaning_S (E : M.Env) (a b c : Ty) :
    M.combMeaning E (.S a b c) ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c) = M.interpS a b c := by
  show (if h : ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c) = ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
    then h ▸ M.interpS a b c else _) = _
  rw [dif_pos rfl]

@[simp] theorem combMeaning_K (E : M.Env) (a b : Ty) :
    M.combMeaning E (.K a b) (a ⇒ b ⇒ a) = M.interpK a b := by
  show (if h : (a ⇒ b ⇒ a) = (a ⇒ b ⇒ a) then h ▸ M.interpK a b else _) = _
  rw [dif_pos rfl]

@[simp] theorem combMeaning_I (E : M.Env) (a : Ty) :
    M.combMeaning E (.I a) (a ⇒ a) = M.interpI a := by
  show (if h : (a ⇒ a) = (a ⇒ a) then h ▸ M.interpI a else _) = _
  rw [dif_pos rfl]

@[simp] theorem combMeaning_app (E : M.Env) (t u : Comb L) (ρ : Ty) :
    M.combMeaning E (.app t u) ρ
      = M.apply (M.combMeaning E t (Comb.tyOf u ⇒ ρ)) (M.combMeaning E u (Comb.tyOf u)) := rfl

/-- The meaning of a combinatory term depends only on its free variables. -/
theorem combMeaning_congr_env {L : Lang} {M : Model L} (E E' : M.Env) :
    ∀ (t : Comb L) (ρ : Ty), (∀ z ν, (z, ν) ∈ Comb.FV t → E z ν = E' z ν) →
      M.combMeaning E t ρ = M.combMeaning E' t ρ := by
  intro t
  induction t with
  | var z ν =>
    intro ρ h
    have hzz : E z ν = E' z ν := h z ν rfl
    show (if hh : ν = ρ then hh ▸ E z ν else (M.dom ρ).bot)
      = (if hh : ν = ρ then hh ▸ E' z ν else (M.dom ρ).bot)
    rw [hzz]
  | const c => intro ρ _; rfl
  | S a b c => intro ρ _; rfl
  | K a b => intro ρ _; rfl
  | I a => intro ρ _; rfl
  | app t u iht ihu =>
    intro ρ h
    rw [Model.combMeaning_app, Model.combMeaning_app,
      iht _ (fun z ν hz => h z ν (Or.inl hz)),
      ihu _ (fun z ν hz => h z ν (Or.inr hz))]

/-- `M[[N]]_E`, the meaning of a λ-term in an environment (Definition 2.5). -/
def meaning (E : M.Env) (N : Term L) (σ : Ty) : M.Dom σ :=
  M.combMeaning E (Term.toComb N) σ

/-- **Definition 2.6** (*Semantic Definition of PCF*).

"The semantic definition of PCF is the restriction of the meaning function `C`
to programs."

`C` is the continuous function model of Figure 1, which interprets `σ → τ` as
the domain `[C_σ →_c C_τ]` of *all* continuous functions.  That particular model
is not constructed here: nothing in Sections 4–6 depends on it, and the paper
uses it only to motivate the failure of full abstraction for PCF (the family
`pᵢ` of the introduction).  Definition 2.6 itself is the restriction operation
below, which applies to any model of any language. -/
def semanticsOfPrograms (Program : Term L → Prop)
    (N : { N : Term L // Program N }) (σ : Ty) : M.Dom σ :=
  M.meaning (fun _ τ => ScottDomain.bot (α := M.Dom τ)) N.1 σ

/-! ### Definition 4.10: extensionality and order-extensionality -/

/-- **Definition 4.10** (*Extensionality*).  "A model `M` for `L` is
extensional iff for all `f, g ∈ M_{σ→τ}`, `apply (f, d) = apply (g, d)` for all
`d ∈ M_σ` implies `f = g`." -/
def Extensional : Prop :=
  ∀ σ τ (f g : M.Dom (σ ⇒ τ)), (∀ d : M.Dom σ, M.apply f d = M.apply g d) → f = g

/-- **Definition 4.10** (*Order-extensionality*).  "It is order-extensional iff
for all `f, g ∈ M_{σ→τ}`, `apply (f, d) ⊑ apply (g, d)` for all `d ∈ M_σ`
implies `f ⊑ g`." -/
def OrderExtensional : Prop :=
  ∀ σ τ (f g : M.Dom (σ ⇒ τ)),
    (∀ d : M.Dom σ, M.apply f d ⊑ M.apply g d) → f ⊑ g

/-- Order-extensionality implies extensionality — "since extensionality is
obviously implied by order-extensionality" (proof of Theorem 4.11). -/
theorem extensional_of_orderExtensional (h : M.OrderExtensional) : M.Extensional := by
  intro σ τ f g hfg
  have h₁ : f ⊑ g := h σ τ f g fun d => (hfg d) ▸ Po.le_refl _
  have h₂ : g ⊑ f := h σ τ g f fun d => (hfg d) ▸ Po.le_refl _
  exact Po.le_antisymm h₁ h₂

end Model

/-! ## Definition 2.8: equivalences and full abstraction -/

namespace SemDef
variable {L : Lang}

/-- **Definition 2.8** (*Observational Equivalence*).

"`N ≃ N'` iff `N` and `N'` have the same type and for all contexts `C[·]` such
that `C[N]` and `C[N']` are programs, `M[[C[N]]] = M[[C[N']]]`." -/
def ObsEquiv (P : SemDef L) (N N' : Term L) : Prop :=
  ∀ C : MCtx L 1, P.Program (C.fill fun _ => N) → P.Program (C.fill fun _ => N') →
    P.meaning (C.fill fun _ => N) = P.meaning (C.fill fun _ => N')

@[inherit_doc] scoped notation:50 N " ≃[" P "] " N' => SemDef.ObsEquiv P N N'

end SemDef

namespace Model
variable {L : Lang}

/-- **Definition 2.8** (*Denotational Equivalence*).

"`N ≈_M N'` iff `N` and `N'` have the same type and `M[[N]]_E = M[[N']]_E` for
all environments `E`." -/
def DenEquiv (M : Model L) (σ : Ty) (N N' : Term L) : Prop :=
  ∀ E : M.Env, M.meaning E N σ = M.meaning E N' σ

/-- **Definition 2.8** (*Full Abstraction*).

"A model `M` is fully abstract iff `N ≃ N'` implies `N ≈_M N'` for closed
`N, N'`." -/
def FullyAbstract (M : Model L) (P : SemDef L) : Prop :=
  ∀ σ (N N' : Term L), Term.Closed N → Term.Closed N' →
    (SemDef.ObsEquiv P N N') → M.DenEquiv σ N N'

end Model

/-! ## Definitions 2.9, 6.3, 6.6 and Theorem 6.5 -/

namespace SemDef
variable {L : Lang} (P : SemDef L)

/-- The hypotheses shared by Definitions 2.9, 6.3 and 6.6: `C[M₁,…,Mₖ]` is a
program returning a natural number, while `C[Ω,…,Ω]` diverges. -/
structure Probe {k : Nat} (C : MCtx L k) (M : Fin k → Term L) : Prop where
  /-- `C[M₁,…,Mₖ]` is a program. -/
  isProgram : P.Program (C.fill M)
  /-- Each `Mᵢ` is closed. -/
  closed : ∀ i, Term.Closed (M i)
  /-- `P[[C[M₁,…,Mₖ]]] ∈ ℕ`. -/
  returns : P.Returns (C.fill M)
  /-- `P[[C[Ω,…,Ω]]] = P[[Ω]]`. -/
  divergesAtBot : P.Diverges (C.fill fun _ => P.omega)

/-- `j` is a **sequentiality index** of `C[·,…,·]` (Definition 2.9):
`P[[C[M'₁,…,M'_{j-1}, Ω, M'_{j+1},…,M'ₖ]]] = P[[Ω]]` for all `M'ᵢ`, `i ≠ j`. -/
def SeqIndex {k : Nat} (C : MCtx L k) (j : Fin k) : Prop :=
  ∀ M' : Fin k → Term L, P.Program (C.fill (repl M' j P.omega)) →
    P.Diverges (C.fill (repl M' j P.omega))

/-- **Definition 2.9** (*Sequentiality*).

"A language `L` with semantic definition `P` is sequential iff … there exists
`j ∈ ℕ`, called a sequentiality index of `C[·,…,·]`, such that
`P[[C[M'₁,…,Ω,…,M'ₖ]]] = P[[Ω]]` for all expressions `M'ᵢ`, `i ≠ j`." -/
def Sequential : Prop :=
  ∀ (k : Nat) (C : MCtx L k) (M : Fin k → Term L), P.Probe C M → ∃ j : Fin k, P.SeqIndex C j

/-- **Definition 6.3** (*Error-Sensitivity*).

"A semantic definition `P` for `L` is error-sensitive iff there exist two closed
expressions `E₁` and `E₂`, denoting distinct and inconsistent elements of a flat
domain for the ground type, with the following property.  Let `C[M₁,…,Mₖ]` be a
terminating program … Then there exists `j` such that
`P[[C[M'₁,…,Eⱼ,…,M'ₖ]]] = P[[Eⱼ]]` for all `M'ₗ`."

The conclusion quantifies over *both* error expressions at the *same* hole `j`,
which is exactly how it is used in the paper's proof of Theorem 6.5. -/
def ErrorSensitive : Prop :=
  ∃ E : Bool → Term L,
    -- `E₁` and `E₂` are closed …
    (∀ b, Term.Closed (E b)) ∧
    -- … denote *proper* (non-`⊥`) elements …
    (∀ b, P.meaning (E b) ≠ P.bot) ∧
    -- … that are *distinct*, hence inconsistent in the flat ground domain …
    (P.meaning (E true) ≠ P.meaning (E false)) ∧
    -- … and every probing context propagates an error from one fixed hole.
    (∀ (k : Nat) (C : MCtx L k) (M : Fin k → Term L), P.Probe C M →
      ∃ j : Fin k, ∀ (b : Bool) (M' : Fin k → Term L),
        P.Program (C.fill (repl M' j P.omega)) →
        P.Program (C.fill (repl M' j (E b))) ∧
        P.meaning (C.fill (repl M' j (E b))) = P.meaning (E b))

/-- The core of Theorem 6.5: a hole that propagates both error expressions is a
sequentiality index. -/
theorem seqIndex_of_propagates {E : Bool → Term L}
    (hne : ∀ b, P.meaning (E b) ≠ P.bot)
    (hdist : P.meaning (E true) ≠ P.meaning (E false))
    {k : Nat} {C : MCtx L k} {j : Fin k}
    (hj : ∀ (b : Bool) (M' : Fin k → Term L),
      P.Program (C.fill (repl M' j P.omega)) →
      P.Program (C.fill (repl M' j (E b))) ∧
      P.meaning (C.fill (repl M' j (E b))) = P.meaning (E b)) :
    P.SeqIndex C j := by
  intro M' hprog
  have hrepl : ∀ N : Term L, repl (repl M' j P.omega) j N = repl M' j N := by
    intro N; funext i; by_cases hij : i = j <;> simp [repl, hij]
  -- monotonicity: replacing `Ω` at hole `j` by `E b` can only increase the answer
  have hmono : ∀ b : Bool,
      P.meaning (C.fill (repl M' j P.omega)) ⊑[P] P.meaning (E b) := by
    intro b
    obtain ⟨hprogE, heq⟩ := hj b M' hprog
    have hm := P.mono C (repl M' j P.omega) j (E b)
      (by rw [hrepl P.omega]; exact hprog) (by rw [hrepl (E b)]; exact hprogE)
    rw [hrepl (E b), hrepl P.omega, heq] at hm
    exact hm
  exact P.eq_bot_of_le_two (hne true) (hne false) hdist (hmono true) (hmono false)

/-- **Theorem 6.5.**  *If a semantic definition `P` of a language `L` is
error-sensitive, then it is sequential.*

The proof is the paper's: error-sensitivity supplies a hole `j` that propagates
both errors; monotonicity places `P[[C[…,Ω,…]]]` below both `P[[E₁]]` and
`P[[E₂]]`; and since `E₁` and `E₂` denote distinct proper elements of a flat
domain, `P[[C[…,Ω,…]]]` must be `⊥ = P[[Ω]]`. -/
theorem theorem_6_5 (h : P.ErrorSensitive) : P.Sequential := by
  obtain ⟨E, _hclosed, hne, hdist, hprop⟩ := h
  intro k C M hprobe
  obtain ⟨j, hj⟩ := hprop k C M hprobe
  exact ⟨j, seqIndex_of_propagates P hne hdist hj⟩

/-- **Definition 6.6** (*Observable Sequentiality*).

"A semantic definition `P` of a language `L` based on the typed λ-calculus is
observably sequential iff it is sequential and it satisfies the following
property. … Then there exists a program context `D[·]` such that
`P[[D[λx₁…xₖ. C[x₁,…,xₖ]]]] = P[[j]]` where `j` is the sequentiality index
of `C`." -/
def ObservablySequential : Prop :=
  P.Sequential ∧
  ∀ (k : Nat) (C : MCtx L k) (M : Fin k → Term L), P.Probe C M → ∀ τs : Fin k → Ty,
    ∃ j : Fin k, P.SeqIndex C j ∧ ∃ D : MCtx L 1,
      P.meaning (D.fill fun _ =>
        Term.lams ((List.finRange k).map fun i => (i.val, τs i))
          (C.fill fun i => Term.var i.val (τs i))) = P.nat j.val

end SemDef

end FA
