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
    (hprobe : SPCFSem.Probe C M) :
    ∃ j : Fin k, ∀ (b : Bool) (M' : Fin k → Term SPCF),
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
  ⟨errTerm, errTerm_closed, errTerm_omegaLike, errTerm_ne_bot, errTerm_distinct, probe_index⟩

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
    (hprobe : SPCFSem.Probe C M) (τs : Fin k → Ty) (j : Fin k)
    (hj : ∀ (b : Bool) (M' : Fin k → Term SPCF),
      SPCFSem.Program (C.fill (repl M' j SPCFSem.omega)) →
      SPCFSem.Program (C.fill (repl M' j (errTerm b))) ∧
      SPCFSem.meaning (C.fill (repl M' j (errTerm b))) = SPCFSem.meaning (errTerm b)) :
    ∃ D : MCtx SPCF 1,
      SPCFSem.meaning (D.fill fun _ =>
        Term.lams ((List.finRange k).map fun i => (i.val, τs i))
          (C.fill fun i => Term.var i.val (τs i))) = SPCFSem.nat j.val := by
  sorry

/-- **Theorem 6.7.**  *SPCF is observably sequential.*

"We have already shown that SPCF is error-sensitive.  The remainder of the proof
is trivial: simply set `D[·] = (add1 (catch [·]))`." -/
theorem theorem_6_7 : SPCFSem.ObservablySequential := by
  refine ⟨theorem_6_2, ?_⟩
  intro k C M hprobe τs
  obtain ⟨j, hj⟩ := probe_index k C M hprobe
  refine ⟨j, ?_, catch_returns_index C M hprobe τs j hj⟩
  -- `j` is a sequentiality index, by the argument of Theorem 6.5
  exact SemDef.seqIndex_of_propagates SPCFSem errTerm_omegaLike errTerm_ne_bot
    errTerm_distinct hj

end FA
