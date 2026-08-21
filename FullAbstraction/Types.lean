/-
# Types of PCF and SPCF (§2)

The type structure `σ ::= o | σ → σ` shared by PCF and SPCF, together with the
"uncurried" view `σ₁ → … → σₖ → o` that the paper uses throughout Section 4:
"we will associate each higher order type `σ₁ → … → σₖ → o` with the
corresponding uncurried type `σ₁ × … × σₖ → o`".
-/
import FullAbstraction.Prelude

namespace FA

/-- Types of the simply typed λ-calculus over the single ground type `o`. -/
inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

@[inherit_doc] scoped notation:max "𝕆" => Ty.base
@[inherit_doc] scoped infixr:25 " ⇒ " => Ty.arrow

namespace Ty

/-- The argument types of `σ = σ₁ → … → σₖ → o`, in order. -/
def args : Ty → List Ty
  | base => []
  | arrow a b => a :: b.args

/-- The arity `k` of `σ = σ₁ → … → σₖ → o`. -/
def arity (σ : Ty) : Nat := σ.args.length

/-- The `i`-th argument type `σᵢ` of `σ = σ₁ → … → σₖ → o`. -/
def arg (σ : Ty) (i : Fin σ.arity) : Ty := σ.args[i.val]'i.isLt

/-- The depth of a type: `depth o = 1` and
`depth σ = 1 + max {depth σᵢ}` (used in the induction of Lemma 5.2). -/
def depth : Ty → Nat
  | base => 1
  | arrow a b => max (1 + a.depth) b.depth

@[simp] theorem args_base : (base).args = [] := rfl
@[simp] theorem args_arrow (a b : Ty) : (arrow a b).args = a :: b.args := rfl
@[simp] theorem arity_base : (base).arity = 0 := rfl
@[simp] theorem arity_arrow (a b : Ty) : (arrow a b).arity = b.arity + 1 := rfl

/-- Every argument type is strictly shallower than the type itself; this is the
well-founded measure driving the mutual definitions of Section 4.1. -/
theorem depth_arg_lt (σ : Ty) (i : Fin σ.arity) : (σ.arg i).depth < σ.depth := by
  induction σ with
  | base => exact absurd i.isLt (by simp)
  | arrow a b ih_a ih_b =>
    match i with
    | ⟨0, _⟩ =>
      show a.depth < max (1 + a.depth) b.depth
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    | ⟨n + 1, h⟩ =>
      have h' : n < b.arity := by simpa [arity] using Nat.lt_of_succ_lt_succ h
      have := ih_b ⟨n, h'⟩
      exact Nat.lt_of_lt_of_le this (Nat.le_max_right _ _)

/-- The "uncurried" reading of a type: `σ` is `σ.args` applied to the ground
type.  Recovering `σ` from `σ.args` is the content of this lemma. -/
theorem eq_of_args : ∀ σ : Ty, σ = σ.args.foldr arrow base
  | base => rfl
  | arrow a b => by simp [args, ← eq_of_args b]

/-- The argument list of the uncurried type built from `l`. -/
theorem args_foldr (l : List Ty) : (l.foldr arrow base).args = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [args, ih]

theorem arity_foldr (l : List Ty) : (l.foldr arrow base).arity = l.length := by
  simp [arity, args_foldr]

end Ty

/-- The index of `l`'s `j`-th argument, as an index of the uncurried type. -/
def finOf (l : List Ty) (j : Fin l.length) : Fin (l.foldr Ty.arrow Ty.base).arity :=
  ⟨j.val, by rw [Ty.arity_foldr]; exact j.isLt⟩

theorem arg_finOf (l : List Ty) (j : Fin l.length) :
    (l.foldr Ty.arrow Ty.base).arg (finOf l j) = l[j.val] := by
  simp only [Ty.arg, finOf]
  congr 1
  exact Ty.args_foldr l

end FA
