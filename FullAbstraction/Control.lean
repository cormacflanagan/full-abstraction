/-
# Equations for `catch` and `error` (§4.4, Appendix B)

States **Lemma 4.26**, **Theorem 4.27** and **Lemma B.1**.

"If we place an `error` value or `⊥` in the hole of an evaluation context, the
entire term denotes the value placed in the hole.  In addition, `catch` can
determine which variable occurs in the hole of an evaluation context in its
procedure argument." (§4.4)
-/
import FullAbstraction.SPCFSemantics

namespace FA

open Po

/-- The variables `x₁, …, xₙ` of a type list, named by their position. -/
def varsOf (l : List Ty) : List (Nat × Ty) :=
  (List.finRange l.length).map fun i => (i.val, l[i.val]'i.isLt)

/-- **Lemma B.1.**  *For all variables `x₁, …, xₙ`, for all evaluation contexts
`E`, and for all `1 ≤ j ≤ n`,*
`T[[λ* x₁ … xₙ . E[xⱼ]]] = ⟨j, ?, f⟩` *for an appropriate branching function
`f`.*

That is: a procedure whose body places the variable `xⱼ` in the hole of an
evaluation context probes its `j`-th argument first, with the initial query
`?`. -/
theorem lemma_B_1 (l : List Ty) (E : EvalCtx) (j : Fin l.length)
    (Env : Tmodel.Env) :
    ∃ (f : Resp ((l.foldr Ty.arrow 𝕆).arg (finOf l j)) → Tree (l.foldr Ty.arrow 𝕆))
      (d : D (l.foldr Ty.arrow 𝕆)),
      d.1 = .node (finOf l j) .hole f ∧
      Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (l.foldr Ty.arrow 𝕆) = Ideal.principal d := by
  sorry

/-- **Lemma 4.26.**  *For all variables `x₁, …, xₙ`, for all evaluation contexts
`E`, and for all `j`, `1 ≤ j ≤ n`, `T[[λ* x₁ … xₙ . E[xⱼ]]] = ⟨j, ?, f⟩` for
some appropriate branching function `f`.*

"Proof.  See Appendix B." -/
theorem lemma_4_26 (l : List Ty) (E : EvalCtx) (j : Fin l.length) (Env : Tmodel.Env) :
    ∃ (f : Resp ((l.foldr Ty.arrow 𝕆).arg (finOf l j)) → Tree (l.foldr Ty.arrow 𝕆))
      (d : D (l.foldr Ty.arrow 𝕆)),
      d.1 = .node (finOf l j) .hole f ∧
      Tmodel.combMeaning Env
        (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))
        (l.foldr Ty.arrow 𝕆) = Ideal.principal d :=
  lemma_B_1 l E j Env

/-- `errorᵢ` as an element of `T_o`. -/
noncomputable def errAns (b : Bool) : T 𝕆 :=
  Ideal.principal ⟨.leaf (.err b), TreeOk.leaf _ _⟩

/-- **Theorem 4.27.**  *For all evaluation contexts `E`, types
`σ = σ₁ → … → σₙ`, and variables `x₁, …, xₙ`:*

```
T[[E[errorⱼ]]]                            = errorⱼ           (error)
T[[E[⊥]]]                                 = ⊥                (bottom)
T[[apply (catch_σ, λ* x₁ … xₙ . E[xⱼ])]]  = ⌜j−1⌝            (catch), 1 ≤ j ≤ n
T[[apply (catch_σ, λ* x₁ … xₙ . ⌜k⌝)]]    = ⌜k+n⌝            (return)
```
-/
theorem theorem_4_27 :
    -- (error)
    (∀ (E : EvalCtx) (b : Bool) (Env : Tmodel.Env),
      Tmodel.combMeaning Env (E.fill (.const (.err b))) 𝕆 = errAns b) ∧
    -- (bottom)
    (∀ (E : EvalCtx) (Env : Tmodel.Env),
      Tmodel.combMeaning Env (E.fill (Omega 𝕆)) 𝕆
        = Ideal.principal (DSub.bot : D 𝕆)) ∧
    -- (catch)
    (∀ (l : List Ty) (E : EvalCtx) (j : Fin l.length) (Env : Tmodel.Env),
      Tmodel.combMeaning Env
        (.app (.const (.catchC (l.foldr Ty.arrow 𝕆)))
          (Comb.lamStars (varsOf l) (E.fill (.var j.val (l[j.val]'j.isLt))))) 𝕆
        = natAns j.val) ∧
    -- (return)
    (∀ (l : List Ty) (k : Nat) (Env : Tmodel.Env),
      Tmodel.combMeaning Env
        (.app (.const (.catchC (l.foldr Ty.arrow 𝕆)))
          (Comb.lamStars (varsOf l) (.const (.num k)))) 𝕆
        = natAns (k + l.length)) := by
  sorry

end FA
