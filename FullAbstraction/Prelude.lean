/-
Copyright (c) 2026. Released under Apache 2.0.

# Prelude

A tiny, self-contained replacement for the fragments of `Mathlib` that this
development needs.  Keeping the formalisation Mathlib-free makes it compile in
seconds and makes every mathematical assumption used by the paper's proofs
visible in this file.

Reference: R. Cartwright and M. Felleisen, *Observable Sequentiality and Full
Abstraction*, Rice Technical Report CS 91-167 (August 13, 1992).
-/

namespace FA

universe u v w

/-! ## Sets as predicates -/

/-- A set of `α` is a predicate on `α`. -/
def Set (α : Type u) : Type u := α → Prop

namespace Set

instance : Membership α (Set α) := ⟨fun s a => s a⟩

@[simp] theorem mem_def {s : Set α} {a : α} : a ∈ s ↔ s a := Iff.rfl

/-- The empty set. -/
def empty : Set α := fun _ => False
/-- The full set. -/
def univ : Set α := fun _ => True
/-- The singleton `{a}`. -/
def singleton (a : α) : Set α := fun x => x = a
/-- Union. -/
def union (s t : Set α) : Set α := fun x => x ∈ s ∨ x ∈ t
/-- Intersection. -/
def inter (s t : Set α) : Set α := fun x => x ∈ s ∧ x ∈ t
/-- Set-theoretic inclusion. -/
def Subset (s t : Set α) : Prop := ∀ a, a ∈ s → a ∈ t
/-- `s` is inhabited. -/
def Nonempty (s : Set α) : Prop := ∃ a, a ∈ s
/-- Image of a set under a function. -/
def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, a ∈ s ∧ f a = b
/-- The range of a function, i.e. `{f a | a}`. -/
def range (f : α → β) : Set β := fun b => ∃ a, f a = b
/-- The set of members of a list. -/
def ofList (l : List α) : Set α := fun a => a ∈ l
/-- Indexed union. -/
def iUnion (S : Set (Set α)) : Set α := fun a => ∃ s, s ∈ S ∧ a ∈ s

instance : EmptyCollection (Set α) := ⟨empty⟩
instance : Union (Set α) := ⟨union⟩
instance : Inter (Set α) := ⟨inter⟩
instance : HasSubset (Set α) := ⟨Subset⟩
instance : Insert α (Set α) := ⟨fun a s => fun x => x = a ∨ x ∈ s⟩
instance : Singleton α (Set α) := ⟨singleton⟩

@[simp] theorem mem_empty {a : α} : a ∈ (∅ : Set α) ↔ False := Iff.rfl
@[simp] theorem mem_univ {a : α} : a ∈ (univ : Set α) := trivial
@[simp] theorem mem_singleton {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl
@[simp] theorem mem_union {s t : Set α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl
@[simp] theorem mem_inter {s t : Set α} {a : α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := Iff.rfl
@[simp] theorem mem_insert {s : Set α} {a b : α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := Iff.rfl
@[simp] theorem mem_ofList {l : List α} {a : α} : a ∈ ofList l ↔ a ∈ l := Iff.rfl
@[simp] theorem mem_image {f : α → β} {s : Set α} {b : β} :
    b ∈ image f s ↔ ∃ a, a ∈ s ∧ f a = b := Iff.rfl
@[simp] theorem mem_range {f : α → β} {b : β} : b ∈ range f ↔ ∃ a, f a = b := Iff.rfl
@[simp] theorem mem_iUnion {S : Set (Set α)} {a : α} :
    a ∈ iUnion S ↔ ∃ s, s ∈ S ∧ a ∈ s := Iff.rfl

theorem Subset.refl (s : Set α) : s ⊆ s := fun _ h => h
theorem Subset.trans {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun a h => h₂ a (h₁ a h)

/-- Two sets with the same members are equal (uses `funext` and `propext`). -/
theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

theorem Subset.antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  ext fun a => ⟨fun ha => h₁ a ha, fun ha => h₂ a ha⟩

end Set

/-! ## Countability -/

/-- `α` is countable when it injects into `Nat`. -/
def Countable (α : Type u) : Prop := ∃ f : α → Nat, Function.Injective f

theorem Countable.ofInjection {α : Type u} {β : Type v} (hβ : Countable β)
    (f : α → β) (hf : Function.Injective f) : Countable α := by
  obtain ⟨g, hg⟩ := hβ
  exact ⟨g ∘ f, fun {a b} h => hf (hg h)⟩

end FA
