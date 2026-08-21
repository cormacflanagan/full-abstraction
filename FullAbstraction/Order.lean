/-
# Domain theory: finitary bases and their ideal completions

This file formalises the domain-theoretic notions the paper relies on
(Definition 2.7 and the opening paragraphs of Section 4.1) and proves
**Theorem 4.4**, which states that the ideal completion of a finitary basis is
a bounded-complete, ω-algebraic cpo.

Reference: Cartwright & Felleisen, *Observable Sequentiality and Full
Abstraction*, §2.1 (Definition 2.7), §4.1 (Lemma 4.3, Theorem 4.4).
-/
import FullAbstraction.Prelude

namespace FA

universe u v

/-! ## Partial orders

Definition 2.7 (*Notation for Domains*): `⊑` denotes the approximation
ordering on a domain and `⊥` its least element. -/

/-- A partial order: the approximation ordering `⊑` of Definition 2.7. -/
class Po (α : Type u) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b

@[inherit_doc] scoped infix:50 " ⊑ " => Po.le

namespace Po
variable {α : Type u} [Po α]

theorem refl' (a : α) : a ⊑ a := Po.le_refl a
theorem trans' {a b c : α} : a ⊑ b → b ⊑ c → a ⊑ c := Po.le_trans
theorem antisymm' {a b : α} : a ⊑ b → b ⊑ a → a = b := Po.le_antisymm

end Po

open Po

/-! ## Upper bounds, least upper bounds, directed sets -/

variable {α : Type u}

/-- `u` is an upper bound of `S`. -/
def UpperBound [Po α] (S : Set α) (u : α) : Prop := ∀ a, a ∈ S → a ⊑ u

/-- `u` is a *least* upper bound of `S`. -/
def IsLUB [Po α] (S : Set α) (u : α) : Prop :=
  UpperBound S u ∧ ∀ v, UpperBound S v → u ⊑ v

/-- `S` has an upper bound; the paper calls such a set *consistent*. -/
def Bounded [Po α] (S : Set α) : Prop := ∃ u, UpperBound S u

/-- A *directed* set is non-empty and contains an upper bound for every pair of
its elements (the paper's phrasing, just before Theorem 4.4). -/
def DirectedSet [Po α] (S : Set α) : Prop :=
  Set.Nonempty S ∧ ∀ a b, a ∈ S → b ∈ S → ∃ c, c ∈ S ∧ a ⊑ c ∧ b ⊑ c

theorem IsLUB.unique [Po α] {S : Set α} {u v : α} (hu : IsLUB S u) (hv : IsLUB S v) :
    u = v :=
  Po.le_antisymm (hu.2 v hv.1) (hv.2 u hu.1)

theorem directed_of_lub [Po α] {S : Set α} (hne : Set.Nonempty S) {u : α}
    (h : UpperBound S u) : Bounded S := ⟨u, h⟩

/-! ## Finitary bases

"A finitary basis `B` is a countable, partially ordered set such that every
finite, bounded subset has a least upper bound." (§4.1) -/

/-- A **finitary basis** (§4.1): "a countable, partially ordered set such that
every finite, bounded subset has a least upper bound".

Countability is *not* a field here.  It plays no part in the construction of the
ideal completion or in parts (1)–(3) of Theorem 4.4; it is needed only for
ω-algebraicity, which therefore takes it as an explicit hypothesis
(`theorem_4_4_countably_many_finite`).  Separating the two makes it visible
which results depend on which half of the definition.

`elt` witnesses that the basis is inhabited, which together with
`lub_of_finite_bounded` on the empty list yields a least element `⊥`. -/
class FinitaryBasis (α : Type u) extends Po α where
  elt : α
  lub_of_finite_bounded :
    ∀ l : List α, Bounded (Set.ofList l) → ∃ d, IsLUB (Set.ofList l) d

namespace FinitaryBasis
variable [FinitaryBasis α]

theorem empty_bounded : Bounded (Set.ofList ([] : List α)) :=
  ⟨elt, fun _ h => absurd h (by simp [Set.ofList])⟩

/-- Every finitary basis has a least element, obtained as the least upper bound
of the empty set. -/
noncomputable def bot : α := Classical.choose (lub_of_finite_bounded [] empty_bounded)

theorem bot_spec : IsLUB (Set.ofList ([] : List α)) (bot : α) :=
  Classical.choose_spec (lub_of_finite_bounded [] empty_bounded)

theorem bot_le (a : α) : bot ⊑ a :=
  bot_spec.2 a (fun _ h => absurd h (by simp [Set.ofList]))

/-- Singletons have least upper bounds, namely themselves. -/
theorem isLUB_singleton (a : α) : IsLUB (Set.ofList [a]) a := by
  refine ⟨fun b hb => ?_, fun v hv => hv a (by simp [Set.ofList])⟩
  simp only [Set.mem_ofList, List.mem_singleton] at hb
  subst hb; exact Po.le_refl _

end FinitaryBasis

/-! ## Ideals

"The domain `D_B` determined by `B` is the set of ideals over `B`." (§4.1) -/

/-- An **ideal** over a finitary basis: a non-empty, downward-closed, directed
subset. -/
structure Ideal (α : Type u) [FinitaryBasis α] where
  carrier : Set α
  nonempty' : Set.Nonempty carrier
  downward : ∀ a b, a ⊑ b → b ∈ carrier → a ∈ carrier
  directed' : ∀ a b, a ∈ carrier → b ∈ carrier → ∃ c, c ∈ carrier ∧ a ⊑ c ∧ b ⊑ c

namespace Ideal
variable [FinitaryBasis α]

instance : Membership α (Ideal α) := ⟨fun I a => a ∈ I.carrier⟩

@[simp] theorem mem_carrier {I : Ideal α} {a : α} : a ∈ I ↔ a ∈ I.carrier := Iff.rfl

theorem ext {I J : Ideal α} (h : ∀ a, a ∈ I ↔ a ∈ J) : I = J := by
  cases I; cases J
  simp only [Ideal.mk.injEq]
  exact Set.ext h

/-- The **ideal completion** is ordered by set inclusion (Theorem 4.4). -/
instance : Po (Ideal α) where
  le I J := I.carrier ⊆ J.carrier
  le_refl _ := Set.Subset.refl _
  le_trans h₁ h₂ := Set.Subset.trans h₁ h₂
  le_antisymm h₁ h₂ := ext fun a => ⟨fun h => h₁ a h, fun h => h₂ a h⟩

theorem le_def {I J : Ideal α} : I ⊑ J ↔ ∀ a, a ∈ I → a ∈ J := Iff.rfl

/-- Any finite list of elements of an ideal has an upper bound inside it. -/
theorem list_bounded (I : Ideal α) : ∀ l : List α, (∀ a ∈ l, a ∈ I) →
    ∃ u, u ∈ I ∧ ∀ a ∈ l, a ⊑ u := by
  intro l
  induction l with
  | nil => intro _; obtain ⟨u, hu⟩ := I.nonempty'; exact ⟨u, hu, by simp⟩
  | cons a l ih =>
    intro h
    obtain ⟨u, hu, hul⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    obtain ⟨c, hc, hac, huc⟩ := I.directed' a u (h a (List.mem_cons_self ..)) hu
    refine ⟨c, hc, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hac
    · exact Po.le_trans (hul b hb) huc

/-- **Principal ideal** `I_e = {d ∈ D | d ⊑ e}` (Theorem 4.4). -/
def principal (e : α) : Ideal α where
  carrier := fun d => d ⊑ e
  nonempty' := ⟨e, Po.le_refl e⟩
  downward _ _ hab hb := Po.le_trans hab hb
  directed' a b ha hb := ⟨e, Po.le_refl e, ha, hb⟩

@[simp] theorem mem_principal {e a : α} : a ∈ principal e ↔ a ⊑ e := Iff.rfl

theorem principal_mono {d e : α} (h : d ⊑ e) : principal d ⊑ principal e :=
  fun _ ha => Po.le_trans ha h

theorem principal_le_iff {d e : α} : principal d ⊑ principal e ↔ d ⊑ e :=
  ⟨fun h => h d (Po.le_refl d), principal_mono⟩

theorem principal_inj {d e : α} (h : principal d = principal e) : d = e :=
  Po.le_antisymm (principal_le_iff.mp (h ▸ Po.le_refl _))
    (principal_le_iff.mp (h ▸ Po.le_refl _))

theorem mem_iff_principal_le {I : Ideal α} {d : α} : d ∈ I ↔ principal d ⊑ I :=
  ⟨fun hd _ ha => I.downward _ _ ha hd, fun h => h d (Po.le_refl d)⟩

/-! ### Directed suprema -/

/-- The union of a directed family of ideals, which Theorem 4.4(1) identifies as
its least upper bound. -/
def dirSup (S : Set (Ideal α)) (hS : DirectedSet S) : Ideal α where
  carrier := fun a => ∃ I, I ∈ S ∧ a ∈ I
  nonempty' := by
    obtain ⟨I, hI⟩ := hS.1
    obtain ⟨a, ha⟩ := I.nonempty'
    exact ⟨a, I, hI, ha⟩
  downward a b hab := by
    rintro ⟨I, hI, hb⟩; exact ⟨I, hI, I.downward _ _ hab hb⟩
  directed' a b := by
    rintro ⟨I, hI, ha⟩ ⟨J, hJ, hb⟩
    obtain ⟨K, hK, hIK, hJK⟩ := hS.2 I J hI hJ
    obtain ⟨c, hc, hac, hbc⟩ := K.directed' a b (hIK a ha) (hJK b hb)
    exact ⟨c, ⟨K, hK, hc⟩, hac, hbc⟩

theorem isLUB_dirSup (S : Set (Ideal α)) (hS : DirectedSet S) :
    IsLUB S (dirSup S hS) := by
  constructor
  · intro I hI a ha; exact ⟨I, hI, ha⟩
  · rintro V hV a ⟨I, hI, ha⟩; exact hV I hI a ha

/-! ### Bounded suprema -/

/-- The ideal generated by a bounded family: everything below the least upper
bound of a finite selection from `⋃ S`. -/
def bddSup (S : Set (Ideal α)) (hS : Bounded S) : Ideal α where
  carrier := fun a => ∃ l : List α, (∀ x ∈ l, ∃ I, I ∈ S ∧ x ∈ I) ∧
    ∃ d, IsLUB (Set.ofList l) d ∧ a ⊑ d
  nonempty' := by
    refine ⟨FinitaryBasis.bot, [], by simp, FinitaryBasis.bot, ?_, Po.le_refl _⟩
    exact FinitaryBasis.bot_spec
  downward a b hab := by
    rintro ⟨l, hl, d, hd, hbd⟩; exact ⟨l, hl, d, hd, Po.le_trans hab hbd⟩
  directed' a b := by
    rintro ⟨l₁, hl₁, d₁, hd₁, had₁⟩ ⟨l₂, hl₂, d₂, hd₂, hbd₂⟩
    obtain ⟨U, hU⟩ := hS
    -- every element of `l₁ ++ l₂` lies in the bounding ideal `U`
    have hmem : ∀ x ∈ l₁ ++ l₂, x ∈ U := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨I, hI, hxI⟩ := hl₁ x h; exact hU I hI x hxI
      · obtain ⟨I, hI, hxI⟩ := hl₂ x h; exact hU I hI x hxI
    obtain ⟨u, _, hu⟩ := U.list_bounded (l₁ ++ l₂) hmem
    obtain ⟨d, hd⟩ := FinitaryBasis.lub_of_finite_bounded (l₁ ++ l₂)
      ⟨u, fun x hx => hu x hx⟩
    have hsub : ∀ (l : List α), (∀ x ∈ l, x ∈ l₁ ++ l₂) → UpperBound (Set.ofList l) d :=
      fun l h x hx => hd.1 x (h x hx)
    have h₁ : d₁ ⊑ d := hd₁.2 d (hsub l₁ fun x hx => List.mem_append.mpr (Or.inl hx))
    have h₂ : d₂ ⊑ d := hd₂.2 d (hsub l₂ fun x hx => List.mem_append.mpr (Or.inr hx))
    refine ⟨d, ⟨l₁ ++ l₂, ?_, d, hd, Po.le_refl _⟩, Po.le_trans had₁ h₁,
      Po.le_trans hbd₂ h₂⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hl₁ x h
    · exact hl₂ x h

theorem isLUB_bddSup (S : Set (Ideal α)) (hS : Bounded S) : IsLUB S (bddSup S hS) := by
  constructor
  · intro I hI a ha
    exact ⟨[a], by simpa using ⟨I, hI, ha⟩, a, FinitaryBasis.isLUB_singleton a, Po.le_refl a⟩
  · rintro V hV a ⟨l, hl, d, hd, had⟩
    have hlV : ∀ x ∈ l, x ∈ V := by
      intro x hx; obtain ⟨I, hI, hxI⟩ := hl x hx; exact hV I hI x hxI
    obtain ⟨u, huV, hu⟩ := V.list_bounded l hlV
    have : d ⊑ u := hd.2 u fun x hx => hu x hx
    exact V.downward a u (Po.le_trans had this) huV

/-! ### Finite (compact) elements -/

/-- An element is **finite** (compact) when it is inaccessible by directed
suprema. -/
def IsFinite (I : Ideal α) : Prop :=
  ∀ S : Set (Ideal α), ∀ hS : DirectedSet S, I ⊑ dirSup S hS → ∃ J, J ∈ S ∧ I ⊑ J

/-- The family of principal ideals below `I`. -/
def approxSet (I : Ideal α) : Set (Ideal α) := fun J => ∃ d, d ∈ I ∧ J = principal d

theorem approxSet_directed (I : Ideal α) : DirectedSet (approxSet I) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := I.nonempty'; exact ⟨principal a, a, ha, rfl⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := I.directed' a b ha hb
    exact ⟨principal c, ⟨c, hc, rfl⟩, principal_mono hac, principal_mono hbc⟩

end Ideal

/-! ## Theorem 4.4 -/

open Ideal

/-- **Theorem 4.4** (part 1a).  Every directed subset of the ideal completion
has a least upper bound. -/
theorem theorem_4_4_directed_lub [FinitaryBasis α] (S : Set (Ideal α))
    (hS : DirectedSet S) : ∃ I : Ideal α, IsLUB S I :=
  ⟨dirSup S hS, isLUB_dirSup S hS⟩

/-- **Theorem 4.4** (part 1b).  Every bounded subset of the ideal completion has
a least upper bound; i.e. the ideal completion is bounded-complete. -/
theorem theorem_4_4_bounded_lub [FinitaryBasis α] (S : Set (Ideal α))
    (hS : Bounded S) : ∃ I : Ideal α, IsLUB S I :=
  ⟨bddSup S hS, isLUB_bddSup S hS⟩

/-- The ideal completion has a least element (Definition 2.7's `⊥`). -/
theorem theorem_4_4_bot [FinitaryBasis α] :
    ∃ I : Ideal α, ∀ J : Ideal α, I ⊑ J := by
  refine ⟨principal (FinitaryBasis.bot : α), fun J a ha => ?_⟩
  obtain ⟨b, hb⟩ := J.nonempty'
  exact J.downward a b (Po.le_trans ha (FinitaryBasis.bot_le b)) hb

/-- **Theorem 4.4** (part 3).  Every ideal is the directed least upper bound of
the principal ideals it contains. -/
theorem theorem_4_4_algebraic [FinitaryBasis α] (I : Ideal α) :
    IsLUB (approxSet I) I := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩ a ha; exact I.downward a d ha hd
  · intro V hV a ha
    exact hV (principal a) ⟨a, ha, rfl⟩ a (Po.le_refl a)

/-- **Theorem 4.4** (part 2, "⊇").  Principal ideals are finite elements. -/
theorem theorem_4_4_principal_isFinite [FinitaryBasis α] (d : α) :
    IsFinite (principal d : Ideal α) := by
  intro S hS h
  obtain ⟨J, hJ, hdJ⟩ := h d (Po.le_refl d)
  exact ⟨J, hJ, mem_iff_principal_le.mp hdJ⟩

/-- **Theorem 4.4** (part 2, "⊆").  Every finite element is a principal ideal. -/
theorem theorem_4_4_isFinite_principal [FinitaryBasis α] (I : Ideal α)
    (h : IsFinite I) : ∃ d : α, I = principal d := by
  have hdir := approxSet_directed I
  have hlub : I ⊑ dirSup (approxSet I) hdir := by
    intro a ha; exact ⟨principal a, ⟨a, ha, rfl⟩, Po.le_refl a⟩
  obtain ⟨J, ⟨d, hd, rfl⟩, hIJ⟩ := h (approxSet I) hdir hlub
  exact ⟨d, Po.le_antisymm hIJ (mem_iff_principal_le.mp hd)⟩

/-- **Theorem 4.4** (part 2).  The finite elements are *precisely* the principal
ideals. -/
theorem theorem_4_4_finite_elements [FinitaryBasis α] (I : Ideal α) :
    IsFinite I ↔ ∃ d : α, I = principal d := by
  refine ⟨theorem_4_4_isFinite_principal I, ?_⟩
  rintro ⟨d, rfl⟩; exact theorem_4_4_principal_isFinite d

/-- **Theorem 4.4** (ω-algebraicity).  There are only countably many finite
elements, because the basis is countable. -/
theorem theorem_4_4_countably_many_finite [FinitaryBasis α] (hcount : Countable α) :
    Countable { I : Ideal α // IsFinite I } := by
  classical
  have hchoice : ∀ I : { I : Ideal α // IsFinite I }, ∃ d : α, I.1 = principal d :=
    fun I => theorem_4_4_isFinite_principal I.1 I.2
  refine Countable.ofInjection hcount
    (fun I => Classical.choose (hchoice I)) ?_
  intro I J h
  have hI := Classical.choose_spec (hchoice I)
  have hJ := Classical.choose_spec (hchoice J)
  apply Subtype.ext
  simp only at h
  rw [hI, hJ, h]

/-! ## Scott domains

"A Scott domain is the ideal completion of a finitary basis [7, 20]. … By this
construction, a domain is a bounded-complete, ω-algebraic cpo (complete partial
order)." (§4.1) -/

/-- A **Scott domain**: a bounded-complete, ω-algebraic cpo.  These are exactly
the properties that Theorem 4.4 establishes for ideal completions. -/
class ScottDomain (α : Type u) extends Po α where
  /-- `⊥`, the least element (Definition 2.7). -/
  bot : α
  bot_le : ∀ a, Po.le bot a
  /-- Least upper bounds of directed sets (Theorem 4.4(1a)). -/
  dsup : ∀ S : Set α, DirectedSet S → α
  dsup_isLUB : ∀ (S : Set α) (h : DirectedSet S), IsLUB S (dsup S h)
  /-- Least upper bounds of bounded sets (Theorem 4.4(1b)). -/
  bsup : ∀ S : Set α, Bounded S → α
  bsup_isLUB : ∀ (S : Set α) (h : Bounded S), IsLUB S (bsup S h)
  /-- The finite (compact) elements (Theorem 4.4(2)). -/
  Fin' : α → Prop
  /-- Algebraicity (Theorem 4.4(3)). -/
  algebraic : ∀ a : α, IsLUB (fun b => Fin' b ∧ Po.le b a) a

/-- **Theorem 4.4**, packaged: the ideal completion of a finitary basis is a
Scott domain. -/
noncomputable instance idealScottDomain [FinitaryBasis α] : ScottDomain (Ideal α) where
  toPo := inferInstance
  bot := Ideal.principal (FinitaryBasis.bot : α)
  bot_le J := by
    intro a ha
    obtain ⟨b, hb⟩ := J.nonempty'
    exact J.downward a b (Po.le_trans ha (FinitaryBasis.bot_le b)) hb
  dsup S h := Ideal.dirSup S h
  dsup_isLUB S h := Ideal.isLUB_dirSup S h
  bsup S h := Ideal.bddSup S h
  bsup_isLUB S h := Ideal.isLUB_bddSup S h
  Fin' := Ideal.IsFinite
  algebraic I := by
    constructor
    · rintro J ⟨hfin, hJI⟩ a ha; exact hJI a ha
    · intro V hV a ha
      refine hV (Ideal.principal a) ⟨theorem_4_4_principal_isFinite a, ?_⟩ a (Po.le_refl a)
      intro b hb; exact I.downward b a hb ha

/-- ω-algebraicity of a Scott domain: only countably many finite elements. -/
def ScottDomain.OmegaAlgebraic (α : Type u) [ScottDomain α] : Prop :=
  Countable { a : α // ScottDomain.Fin' a }

/-- The ideal completion of a *countable* finitary basis is ω-algebraic. -/
theorem idealOmegaAlgebraic [FinitaryBasis α] (hcount : Countable α) :
    ScottDomain.OmegaAlgebraic (Ideal α) :=
  theorem_4_4_countably_many_finite hcount

end FA
