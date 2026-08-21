/-
# Syntax: PCF, SPCF, combinatory terms, contexts (§2, §3, §4.4)

Formalises:

* the generic notion of "a language based on the typed λ-calculus"
  (used in Definitions 2.1, 2.3, 4.10, 6.3, 6.6);
* **Definition 2.2** (combinatory terms), the constants `S`, `K`, `I` and the
  function symbols `apply_{σ,τ}`;
* the translation `[·]_CL` and the abstraction algorithm `λ*` of Figure 1;
* the constants of PCF and **Definition 3.1** (SPCF);
* multi-hole contexts `C[M₁,…,Mₖ]`, needed by Definitions 2.8, 2.9, 6.3, 6.6;
* **Definition 4.25** (evaluation contexts).
-/
import FullAbstraction.Types

namespace FA

/-! ## Languages based on the typed λ-calculus -/

/-- "A language `L` based on the typed λ-calculus with variables `V` and
constants `F`" (Definitions 2.1, 2.2, 2.3).  Variables are natural numbers
tagged with their type. -/
structure Lang where
  /-- The set of constants `F`. -/
  Const : Type
  /-- The type of each constant. -/
  constTy : Const → Ty
  /-- Constants are compared for equality syntactically. -/
  [decEq : DecidableEq Const]

attribute [instance] Lang.decEq

/-! ## λ-terms -/

/-- Terms of `L`: variables, constants, application and abstraction. -/
inductive Term (L : Lang) where
  | var : Nat → Ty → Term L
  | const : L.Const → Term L
  | app : Term L → Term L → Term L
  | lam : Nat → Ty → Term L → Term L

namespace Term
variable {L : Lang}

/-- Multiple abstraction `λ x₁ … xₙ . M`. -/
def lams (xs : List (Nat × Ty)) (M : Term L) : Term L :=
  xs.foldr (fun p N => .lam p.1 p.2 N) M

/-- Multiple application `(M N₁ … Nₙ)`. -/
def apps (M : Term L) (Ns : List (Term L)) : Term L :=
  Ns.foldl .app M

/-- The typing relation of the simply typed λ-calculus. -/
inductive HasTy : List (Nat × Ty) → Term L → Ty → Prop where
  | var {Γ x σ} : (x, σ) ∈ Γ → (∀ τ, (x, τ) ∈ Γ → τ = σ) → HasTy Γ (.var x σ) σ
  | const {Γ c} : HasTy Γ (.const c) (L.constTy c)
  | app {Γ M N σ τ} : HasTy Γ M (σ ⇒ τ) → HasTy Γ N σ → HasTy Γ (.app M N) τ
  | lam {Γ x σ M τ} : HasTy ((x, σ) :: Γ) M τ → HasTy Γ (.lam x σ M) (σ ⇒ τ)

/-- The free variables of a term. -/
def FV : Term L → Set (Nat × Ty)
  | .var x σ => {(x, σ)}
  | .const _ => ∅
  | .app M N => FV M ∪ FV N
  | .lam x σ M => fun p => p ∈ FV M ∧ p ≠ (x, σ)

/-- A *closed* phrase has no free variables. -/
def Closed (M : Term L) : Prop := ∀ p, p ∉ FV M

/-- Capture-avoiding substitution is not needed below; we only need the
"substitute a closed term" case, for which naive substitution is correct. -/
def subst (x : Nat) (σ : Ty) (N : Term L) : Term L → Term L
  | .var y τ => if y = x ∧ τ = σ then N else .var y τ
  | .const c => .const c
  | .app M₁ M₂ => .app (subst x σ N M₁) (subst x σ N M₂)
  | .lam y τ M => if y = x ∧ τ = σ then .lam y τ M else .lam y τ (subst x σ N M)

end Term

/-! ## Definition 2.2: combinatory terms -/

/-- The auxiliary constants `O = {S_{σ,τ,ρ}} ∪ {K_{σ,τ}} ∪ {I_σ}` and the
function symbols `A = {apply_{σ,τ}}` of Definition 2.2. -/
inductive Comb (L : Lang) where
  | var : Nat → Ty → Comb L
  | const : L.Const → Comb L
  /-- `S_{σ,τ,ρ} : (σ → τ → ρ) → (σ → τ) → σ → ρ`. -/
  | S : Ty → Ty → Ty → Comb L
  /-- `K_{σ,τ} : σ → τ → σ`. -/
  | K : Ty → Ty → Comb L
  /-- `I_σ : σ → σ`. -/
  | I : Ty → Comb L
  /-- `apply_{σ,τ} : (σ → τ) × σ → τ`. -/
  | app : Comb L → Comb L → Comb L

namespace Comb
variable {L : Lang}

/-- Typing of combinatory terms: "and the type constraints of typed
λ-calculus" (Definition 2.2). -/
inductive HasTy : List (Nat × Ty) → Comb L → Ty → Prop where
  | var {Γ x σ} : (x, σ) ∈ Γ → HasTy Γ (.var x σ) σ
  | const {Γ c} : HasTy Γ (.const c) (L.constTy c)
  | S {Γ σ τ ρ} : HasTy Γ (.S σ τ ρ) ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  | K {Γ σ τ} : HasTy Γ (.K σ τ) (σ ⇒ τ ⇒ σ)
  | I {Γ σ} : HasTy Γ (.I σ) (σ ⇒ σ)
  | app {Γ M N σ τ} : HasTy Γ M (σ ⇒ τ) → HasTy Γ N σ → HasTy Γ (.app M N) τ

/-- Free variables of a combinatory term. -/
def FV : Comb L → Set (Nat × Ty)
  | .var x σ => {(x, σ)}
  | .const _ => ∅
  | .S _ _ _ => ∅
  | .K _ _ => ∅
  | .I _ => ∅
  | .app M N => FV M ∪ FV N

/-- Substitution of a combinatory term for a variable. -/
def subst (x : Nat) (σ : Ty) (N : Comb L) : Comb L → Comb L
  | .var y τ => if y = x ∧ τ = σ then N else .var y τ
  | .const c => .const c
  | .S a b c => .S a b c
  | .K a b => .K a b
  | .I a => .I a
  | .app M₁ M₂ => .app (subst x σ N M₁) (subst x σ N M₂)

/-- The type of a combinatory term, computed structurally.  It is correct on
well-typed terms (`Comb.HasTy Γ M σ → M.tyOf = σ`) and returns the ground type
as a dummy on ill-typed ones. -/
def tyOf : Comb L → Ty
  | .var _ σ => σ
  | .const c => L.constTy c
  | .S σ τ ρ => (σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ
  | .K σ τ => σ ⇒ τ ⇒ σ
  | .I σ => σ ⇒ σ
  | .app M _ => match tyOf M with
    | .arrow _ b => b
    | _ => 𝕆

/-- The abstraction algorithm `λ*ₓ` of Figure 1:

```
λ*x. x                = I
λ*x. M                = apply (K, M)                            (x ∉ FV(M))
λ*x. apply (M₁, M₂)   = apply (apply (S, λ*x.M₁), λ*x.M₂)
```
The `x ∉ FV(M)` side condition is decided structurally: we use the `K` clause
for every atom other than `x` itself. -/
def lamStar (x : Nat) (σ : Ty) : Comb L → Comb L
  | .var y τ => if y = x ∧ τ = σ then .I σ else .app (.K τ σ) (.var y τ)
  | .const c => .app (.K (L.constTy c) σ) (.const c)
  | .S a b c => .app (.K (tyOf (.S a b c : Comb L)) σ) (.S a b c)
  | .K a b => .app (.K (tyOf (.K a b : Comb L)) σ) (.K a b)
  | .I a => .app (.K (tyOf (.I a : Comb L)) σ) (.I a)
  | .app M₁ M₂ =>
      .app (.app (.S σ (tyOf M₂) (tyOf (.app M₁ M₂))) (lamStar x σ M₁)) (lamStar x σ M₂)

/-- Iterated `λ*`. -/
def lamStars (xs : List (Nat × Ty)) (M : Comb L) : Comb L :=
  xs.foldr (fun p N => lamStar p.1 p.2 N) M

/-- Iterated application. -/
def apps (M : Comb L) (Ns : List (Comb L)) : Comb L := Ns.foldl .app M

end Comb

/-- The translation `[·]_CL` of Figure 1, extended to SPCF "in the obvious way"
(§4). -/
def Term.toComb {L : Lang} : Term L → Comb L
  | .var x σ => .var x σ
  | .const c => .const c
  | .app M N => .app (Term.toComb M) (Term.toComb N)
  | .lam x σ M => Comb.lamStar x σ (Term.toComb M)

@[inherit_doc] scoped notation:max "⟦" M "⟧CL" => Term.toComb M

/-! ## The constants of PCF and SPCF -/

/-! ## The translation preserves types

Figure 1's `[·]_CL` and `λ*` take well-typed λ-terms to well-typed combinatory
terms of the same type; `Comb.tyOf` computes that type. -/

namespace Comb
variable {L : Lang}

/-- `tyOf` computes the type of a well-typed combinatory term. -/
theorem tyOf_of_hasTy {Γ : List (Nat × Ty)} {c : Comb L} {ρ : Ty} :
    HasTy Γ c ρ → c.tyOf = ρ := by
  intro h
  induction h with
  | var _ => rfl
  | const => rfl
  | S => rfl
  | K => rfl
  | I => rfl
  | app _ _ ihM _ => show (match tyOf _ with | .arrow _ b => b | _ => 𝕆) = _
                     rw [ihM]

/-- The abstraction algorithm `λ*` of Figure 1 preserves typing. -/
theorem lamStar_hasTy {Γ : List (Nat × Ty)} {x : Nat} {σ : Ty} :
    ∀ {t : Comb L} {τ : Ty}, HasTy ((x, σ) :: Γ) t τ → HasTy Γ (lamStar x σ t) (σ ⇒ τ) := by
  intro t
  induction t with
  | var y ρ =>
    intro τ h
    cases h with
    | var hmem =>
      by_cases hx : y = x ∧ ρ = σ
      · obtain ⟨rfl, rfl⟩ := hx
        show HasTy Γ (lamStar y ρ (.var y ρ)) (ρ ⇒ ρ)
        rw [show lamStar y ρ (Comb.var y ρ : Comb L) = .I ρ by simp [lamStar]]
        exact HasTy.I
      · rw [show lamStar x σ (Comb.var y ρ : Comb L) = .app (.K ρ σ) (.var y ρ) by
          simp only [lamStar, if_neg hx]]
        refine HasTy.app HasTy.K (HasTy.var ?_)
        rcases List.mem_cons.mp hmem with heq | hmem'
        · have h1 : y = x := congrArg Prod.fst heq
          have h2 : ρ = σ := congrArg Prod.snd heq
          exact absurd ⟨h1, h2⟩ hx
        · exact hmem'
  | const c =>
    intro τ h
    cases h with
    | const => exact HasTy.app HasTy.K HasTy.const
  | S a b c =>
    intro τ h
    cases h with
    | S => exact HasTy.app HasTy.K HasTy.S
  | K a b =>
    intro τ h
    cases h with
    | K => exact HasTy.app HasTy.K HasTy.K
  | I a =>
    intro τ h
    cases h with
    | I => exact HasTy.app HasTy.K HasTy.I
  | app M₁ M₂ ih₁ ih₂ =>
    intro τ h
    cases h with
    | app hM₁ hM₂ =>
      rename_i ρ
      have e₂ : tyOf M₂ = ρ := tyOf_of_hasTy hM₂
      have e₁ : tyOf (Comb.app M₁ M₂) = τ := tyOf_of_hasTy (HasTy.app hM₁ hM₂)
      rw [show lamStar x σ (Comb.app M₁ M₂)
          = .app (.app (.S σ (tyOf M₂) (tyOf (Comb.app M₁ M₂))) (lamStar x σ M₁))
              (lamStar x σ M₂) from rfl, e₂, e₁]
      exact HasTy.app (HasTy.app HasTy.S (ih₁ hM₁)) (ih₂ hM₂)

/-- Typing is preserved by enlarging the context. -/
theorem weaken {Γ Γ' : List (Nat × Ty)} (hsub : ∀ p, p ∈ Γ → p ∈ Γ') :
    ∀ {t : Comb L} {ρ : Ty}, HasTy Γ t ρ → HasTy Γ' t ρ := by
  intro t ρ h
  induction h with
  | var hmem => exact HasTy.var (hsub _ hmem)
  | const => exact HasTy.const
  | S => exact HasTy.S
  | K => exact HasTy.K
  | I => exact HasTy.I
  | app _ _ ih₁ ih₂ => exact HasTy.app ih₁ ih₂

theorem weaken_cons {Γ : List (Nat × Ty)} (p : Nat × Ty) {t : Comb L} {ρ : Ty}
    (h : HasTy Γ t ρ) : HasTy (p :: Γ) t ρ :=
  weaken (fun _ hq => List.mem_cons_of_mem p hq) h

/-- Substitution of a well-typed term for a variable preserves typing. -/
theorem subst_hasTy {Γ : List (Nat × Ty)} {x : Nat} {σ : Ty} {N : Comb L}
    (hN : HasTy Γ N σ) :
    ∀ {t : Comb L} {τ : Ty}, HasTy ((x, σ) :: Γ) t τ → HasTy Γ (subst x σ N t) τ := by
  intro t
  induction t with
  | var y ρ =>
    intro τ h
    cases h with
    | var hmem =>
      by_cases hx : y = x ∧ ρ = σ
      · obtain ⟨rfl, rfl⟩ := hx
        rw [show subst y ρ N (Comb.var y ρ : Comb L) = N by simp [subst]]
        exact hN
      · rw [show subst x σ N (Comb.var y ρ : Comb L) = .var y ρ by simp only [subst, if_neg hx]]
        refine HasTy.var ?_
        rcases List.mem_cons.mp hmem with heq | hmem'
        · have h1 : y = x := congrArg Prod.fst heq
          have h2 : ρ = σ := congrArg Prod.snd heq
          exact absurd ⟨h1, h2⟩ hx
        · exact hmem'
  | const c => intro τ h; cases h with | const => exact HasTy.const
  | S a b c => intro τ h; cases h with | S => exact HasTy.S
  | K a b => intro τ h; cases h with | K => exact HasTy.K
  | I a => intro τ h; cases h with | I => exact HasTy.I
  | app M₁ M₂ ih₁ ih₂ =>
    intro τ h
    cases h with
    | app hM₁ hM₂ => exact HasTy.app (ih₁ hM₁) (ih₂ hM₂)

end Comb

/-- `[·]_CL` preserves typing. -/
theorem Term.toComb_hasTy {L : Lang} {Γ : List (Nat × Ty)} {N : Term L} {ρ : Ty} :
    Term.HasTy Γ N ρ → Comb.HasTy Γ (Term.toComb N) ρ := by
  intro h
  induction h with
  | var hmem _ => exact Comb.HasTy.var hmem
  | const => exact Comb.HasTy.const
  | app _ _ ih₁ ih₂ => exact Comb.HasTy.app ih₁ ih₂
  | lam _ ih => exact Comb.lamStar_hasTy ih

/-- The type of the combinatory form of a well-typed term. -/
theorem Term.tyOf_toComb {L : Lang} {Γ : List (Nat × Ty)} {N : Term L} {ρ : Ty}
    (h : Term.HasTy Γ N ρ) : (Term.toComb N).tyOf = ρ :=
  Comb.tyOf_of_hasTy (Term.toComb_hasTy h)

/-- The constants of SPCF (Definition 3.1).  PCF is the sublanguage that omits
`err` and `catch`:

`F = {⌜n⌝ | n ∈ ℕ} ∪ {add1, sub1, if0, error₁, error₂} ∪ {Y_σ} ∪ {catch_σ}`. -/
inductive SConst where
  /-- The numeral `⌜n⌝`. -/
  | num : Nat → SConst
  | add1 : SConst
  | sub1 : SConst
  | if0 : SConst
  /-- The fixed-point operator `Y_σ : (σ → σ) → σ`. -/
  | Y : Ty → SConst
  /-- `error₁` and `error₂`, both of type `o`. -/
  | err : Bool → SConst
  /-- `catch_σ : (σ → o)`.  Note the paper's typing: `catch_σ` *is* of type
  `σ → o`, so it may be applied to an argument of type `σ`. -/
  | catchC : Ty → SConst
  deriving DecidableEq

/-- Types of the SPCF constants (Definition 3.1). -/
def SConst.ty : SConst → Ty
  | num _ => 𝕆
  | add1 => 𝕆 ⇒ 𝕆
  | sub1 => 𝕆 ⇒ 𝕆
  | if0 => 𝕆 ⇒ 𝕆 ⇒ 𝕆 ⇒ 𝕆
  | Y σ => (σ ⇒ σ) ⇒ σ
  | err _ => 𝕆
  | catchC σ => σ ⇒ 𝕆

/-- Is this constant part of PCF (as opposed to SPCF only)? -/
def SConst.isPCF : SConst → Bool
  | err _ => false
  | catchC _ => false
  | _ => true

/-- The language **SPCF** (Definition 3.1). -/
def SPCF : Lang := { Const := SConst, constTy := SConst.ty }

/-- The language **PCF** (§2). -/
def PCF : Lang := { Const := { c : SConst // c.isPCF }, constTy := fun c => c.1.ty }

/-! ## Multi-hole contexts -/

/-- A context `C[·,…,·]` with `k` holes; `C[M₁,…,Mₖ]` is `MCtx.fill`.
Substitution into a hole is *not* capture avoiding, exactly as for the
syntactic contexts of Definitions 2.8, 2.9, 6.3 and 6.6. -/
inductive MCtx (L : Lang) (k : Nat) where
  | hole : Fin k → MCtx L k
  | var : Nat → Ty → MCtx L k
  | const : L.Const → MCtx L k
  | app : MCtx L k → MCtx L k → MCtx L k
  | lam : Nat → Ty → MCtx L k → MCtx L k

namespace MCtx
variable {L : Lang} {k : Nat}

/-- `C[M₁,…,Mₖ]`. -/
def fill : MCtx L k → (Fin k → Term L) → Term L
  | .hole i, M => M i
  | .var x σ, _ => .var x σ
  | .const c, _ => .const c
  | .app C₁ C₂, M => .app (C₁.fill M) (C₂.fill M)
  | .lam x σ C, M => .lam x σ (C.fill M)

end MCtx

/-- Replace the `j`-th entry of a tuple of arguments. -/
def repl {k : Nat} {α : Type _} (M : Fin k → α) (j : Fin k) (N : α) : Fin k → α :=
  fun i => if i = j then N else M i

@[simp] theorem repl_self {k : Nat} {α : Type _} (M : Fin k → α) (j : Fin k) (N : α) :
    repl M j N j = N := by simp [repl]

/-! ## Definition 4.25: evaluation contexts -/

/-- The primitive function symbols `F ::= add1 | sub1 | if0 | catch`
(Definition 4.25). -/
inductive PrimF where
  | add1 | sub1 | if0 | catchF (σ : Ty)

/-- **Definition 4.25** (*Evaluation context*).

```
E ::= [ ] | apply (F, E) | apply (E, M) | apply (catch, (λ* x₁ … xₙ . E))
F ::= add1 | sub1 | if0 | catch
```
"An evaluation context is a syntactic context where the hole is in
leftmost-outermost position." -/
inductive EvalCtx : Type where
  | hole : EvalCtx
  | primApp : PrimF → EvalCtx → EvalCtx
  | appL : EvalCtx → Comb SPCF → EvalCtx
  | catchLam : Ty → List (Nat × Ty) → EvalCtx → EvalCtx

/-- The combinatory term denoted by a primitive function symbol. -/
def PrimF.toComb : PrimF → Comb SPCF
  | .add1 => .const .add1
  | .sub1 => .const .sub1
  | .if0 => .const .if0
  | .catchF σ => .const (.catchC σ)

namespace EvalCtx

/-- `E[M]`: plug a combinatory term into the hole of an evaluation context. -/
def fill : EvalCtx → Comb SPCF → Comb SPCF
  | .hole, M => M
  | .primApp f E, M => .app f.toComb (fill E M)
  | .appL E N, M => .app (fill E M) N
  | .catchLam σ xs E, M => .app (.const (.catchC σ)) (Comb.lamStars xs (fill E M))

end EvalCtx

end FA
