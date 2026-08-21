# Observable Sequentiality and Full Abstraction — a Lean 4 formalisation

A formalisation of

> Robert Cartwright and Matthias Felleisen.
> **Observable Sequentiality and Full Abstraction.**
> Rice Technical Report CS 91-167, August 13, 1992.
> (A preliminary version appeared in *POPL '92*.)

The paper is included in this repository as
`Observable_Sequentiality_and_Full_Abstraction.pdf`.

Every numbered definition, lemma, claim, corollary and theorem of the paper —
including the two appendices — is stated in Lean 4.  Where a proof is complete
it is given; where it is not, the statement carries a `sorry` and appears in the
"outstanding" table below.  Nothing is asserted as an `axiom`: every gap is a
visible `sorry`, so `#print axioms` distinguishes finished results from
unfinished ones (see `FullAbstraction/Audit.lean`).

## Building

```
lake build              # the library
lake env lean FullAbstraction/Audit.lean    # per-result axiom audit
```

Requires Lean 4.24.0 (see `lean-toolchain`); `elan` will fetch it.  There are
**no dependencies** — not even Mathlib.  The fragment of order theory, set
theory and countability that the development needs is built from scratch in
`FullAbstraction/Prelude.lean` and `FullAbstraction/Order.lean`, so every
mathematical assumption in play is visible in this repository and the build
takes seconds.

## Module map

| Module | Contents |
| --- | --- |
| `Prelude.lean` | sets-as-predicates, countability |
| `Order.lean` | partial orders, directed and bounded sets, finitary bases, ideal completion, Scott domains — **Theorem 4.4** |
| `Types.lean` | the type structure `σ ::= o \| σ → σ` and the uncurried view of §4 |
| `Syntax.lean` | languages based on the typed λ-calculus, **Def. 2.2**, Figure 1's `[·]_CL` and `λ*`, **Def. 3.1** (SPCF), multi-hole contexts, **Def. 4.25** |
| `Semantics.lean` | **Defs. 2.1, 2.3–2.5, 2.8, 2.9, 4.10, 6.3, 6.6** — **Theorem 6.5** |
| `Trees.lean` | **Def. 4.2** (`C_σ`, `P_σ`, `Q_σ`, `R_σ`, `𝒬_σ`, `ℛ_σ`, `q[?/x]`, `r : f`, `D_σ`), **Defs. 4.5, 4.6, 4.12, 4.13** — **Lemma 4.3** |
| `Apply.lean` | **Def. 4.9** (`apply`), **Def. 4.17** (`F_{σ→τ}`) — **Lemma 4.7**, **Claim 4.8**, **Theorem 4.11**, **Lemma 4.14**, **Cor. 4.15**, **Lemma 4.16**, **Cor. 4.18** |
| `Combinators.lean` | **Def. 4.19** (`add1`, `sub1`, `if0`, `catch`), **Def. 4.20** (`K`), **Defs. 4.21/A.3** + **Claim A.5** (`S`), `Ω_σ`, `T[[Y_σ]]`, **Def. 4.1** (the model `T`) — **Theorem 4.22**, **Cors. 4.23, 4.24**, **Lemma A.1**, **Claim A.2**, **Def. A.4**, **Lemmas A.6, A.7** |
| `SPCFSemantics.lean` | **Def. 6.1**; the ground domain `T_o` is proved flat |
| `Control.lean` | **Lemma 4.26**, **Theorem 4.27**, **Lemma B.1** |
| `FullAbs.lean` | **Def. 5.3**, **Lemma 5.2**, **Theorem 5.1** |
| `Sequentiality.lean` | **Theorems 6.2, 6.4, 6.7** |
| `Audit.lean` | `#print axioms` for every named result |

## How the paper is encoded

**Paths.** §4.1 (footnote 6) observes that queries and responses are trees with
a single branch.  A path of type `σ` is therefore a finite sequence of steps
`⟨i, q, r⟩` — "probe argument `i` with query `q`, receive response `r`" —
terminated by a leaf.  A *query* ends in the marker `?`; a *response* ends
either in a final answer `n ∈ ℕ` or in an intermediate answer `⟨i, p, ⊥⟩`.  This
turns the simultaneous recursion of Definition 4.2 into a mutual inductive
family `Query`/`Resp` indexed by `Ty`, whose recursive occurrences are all at
*argument* types, i.e. structurally smaller ones.

**Tree contexts.** Definition 4.2 introduces a context as "a relation
associating argument indices with responses", used "as a set-valued function
from indices to sets of responses".  But every use it is put to in that
definition is through the *approximation tree* `⊔γ(i)` those responses
determine: a node's query must "extend the approximation tree `⊔γ(i)` for
argument `i` by exactly one node" (§4.1, p. 19).  A `Ctx σ` therefore records
those trees directly — `γ i : Tree (σ.arg i)`.  This does not presuppose that
`⊔γ(i)` exists, and it makes the facts the development needs immediate rather
than derived.  The literal, bookkeeping reading survives as `RespCtx`; it is
what the *statement* of Lemma 4.14 uses.

**Legality.** `𝒬_σ(γ(i))` is `LegalQuery t q`, and it has two halves.

`t @ q = ⊥` is the paper's side condition `¬∃r[q ⊏ r ⊑ ⊔R]` together with the
requirement that `q` extend `t`: the query follows only nodes `t` already
contains, and the node it probes is still unanswered, i.e. `q` *probes the
perimeter* of `t` in the sense of Definition 4.5.

Note that it is *not* enough to require that `q` is not a syntactic prefix of
any recorded `s`: if `s` answers the node `q` probes with a different response
than `q` records, `q` is not a prefix of `s`, yet `q[?/⊥]` — whose final
branching function `⟨r',⊥⟩` is the empty branching function — is still strictly
below `s`, and the query does re-probe an answered node.  Stating legality
against the approximation tree gets this right automatically.

`QueryOk σ q` is the paper's `∃r ∈ R (q = r : ⟨r',?⟩)` with `r' ∈ ℛ_σᵢ(p)`: the
response recorded at each step must itself be legal.  Following an existing path
is not enough, because a tree carries `⊥` at the position reached by answering a
query with an *illegal* response too, and nothing legal will ever be written
there.  Without this clause Lemma 4.16 is false.

`QueryOk` is the one place where Definition 4.2's recursion genuinely descends
into the argument types, and it descends on `Ty.depth`: a step about argument
`i` constrains a response of type `σᵢ`, whose intermediate answers constrain
queries of type `(σᵢ)ⱼ`.  Everything else — `ℛ_σ(q)` (`LegalResp`, "`r = q[?/x]`
with `x` admissible") and `D_σ(γ)` (`TreeOk`) — is then a plain definition or a
plain inductive on trees.

**Branching functions** are honest functions `Resp τ → Tree σ`, with "the proper
domain is finite" as a side condition (`Tree.FiniteProperDomain`), exactly as in
Definition 4.2.  Consequently `Tree σ` contains infinitely branching trees of
finite depth, `D_σ` is cut out of it by `TreeOk`, and `T_σ = Ideal (D σ)`.

**A modelling point worth flagging.**  `T[[add1]]`, `T[[if0]]`, `T[[catch]]` and
the approximants `Kₙ`, `Iₙ` all branch over infinitely many final answers, so
they are *not* elements of the finitary basis `D_σ` even though Definition 4.20
describes `Kₙ` as mapping into `D_{σ→τ}(q̂)`.  They are limit points of `T_σ`.
The formalisation treats them as such: `idealOf` and `idealOfChain` turn a tree
(or an ascending chain of trees) into the ideal of its finite approximations,
and this is what interprets those constants.

**Partiality.** `d @ q` (Definition 4.5) is `Option`-valued.  `apply₀`
(Definition 4.9) returns `⊥` where the paper says its value "is irrelevant".

**Definition 6.3.** The paper writes the conclusion of error-sensitivity as
`P[[C[M'₁,…,Eⱼ,…,M'ₖ]]] = P[[Eⱼ]]`.  The proof of Theorem 6.5 uses it for *both*
error expressions at the *same* hole `j`, so that is how it is formalised.

**Well-typedness.** Definition 2.2 ends "and the type constraints of typed
λ-calculus".  Where a result depends on them — Corollaries 4.23 and 4.24,
`meaning_apps`, `soundness`, Theorem 5.1 — the corresponding `Comb.HasTy` /
`Term.HasTy` hypotheses are present; without them the equations are false,
since `Model.combMeaning` returns `⊥` at a type a term does not have.

The same applies to Definition 2.1's monotonicity clause.  `mono` carries two
`Program` hypotheses and an `OmegaLike` hypothesis on the replacement (`Ω` and
the phrase replacing it are of the same, ground, type — Definition 6.3's error
expressions "denote distinct and inconsistent elements of a flat domain for the
ground type").  Without them the clause is *false*: an ill-typed replacement
makes the filled context ill-typed, and its meaning need not dominate the
meaning of the well-typed `Ω`-fill.  Definition 2.9's sequentiality index and
Definition 6.3's error-sensitivity carry the matching `Program` conditions,
which the paper leaves implicit in "let `M₁, …, Mₖ` be closed phrases such that
`C[M₁, …, Mₖ]` is a program".

**Indices.** The paper numbers arguments from 1; Lean's `Fin` numbers from 0.
Where this matters — notably `catch`, which the paper says returns `j − 1` — the
statement is adjusted and the adjustment is noted in the docstring.

## Status

### Proved outright

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for
each of these.

| Result | Lean name |
| --- | --- |
| Theorem 4.4 (1a): directed subsets of the ideal completion have lubs | `theorem_4_4_directed_lub` |
| Theorem 4.4 (1b): bounded subsets have lubs (bounded completeness) | `theorem_4_4_bounded_lub` |
| Theorem 4.4: the ideal completion has a least element | `theorem_4_4_bot` |
| Theorem 4.4 (2): the finite elements are exactly the principal ideals | `theorem_4_4_finite_elements` |
| Theorem 4.4 (3): algebraicity | `theorem_4_4_algebraic` |
| Theorem 4.4: ω-algebraicity (given a countable basis) | `theorem_4_4_countably_many_finite` |
| Theorem 4.4, packaged as a `ScottDomain` instance | `idealScottDomain` |
| **Lemma 4.3**: `⊑` is a partial order on `D_σ` | `lemma_4_3_partial_order` |
| **Lemma 4.3**: every finite bounded subset of `D_σ` has a lub | `dsub_lub_of_finite_bounded` |
| — the join of two bounded trees is their lub | `Tree.join_spec` |
| — the join of two legal subtrees is legal | `TreeOk_join` |
| **Lemma 4.3**: `D_σ` is a finitary basis | `lemma_4_3` |
| the finite approximations of a tree are directed | `finiteApprox_directed` |
| legal subtrees are finitary | `Finitary_of_TreeOk` |
| **Lemma 4.7** | `lemma_4_7` |
| **Claim 4.8** | `claim_4_8` |
| `apply` is monotone in each argument | `applyT_mono_left`, `applyT_mono_right` |
| `apply (⊥, x) = ⊥`; `⊥` is the principal ideal of `⊥` | `applyT_bot`, `bot_eq_principal` |
| planting a subtree at a perimeter position | `plant`, `at'_plant_self`, `le_plant`, `at'_plant_other`, `substTree_le_plant` |
| contexts recording the same responses are interchangeable | `TreeOk_congr_ctx` |
| every path to a non-`⊥` subtree of a legal tree is legal | `legalPath_of_TreeOk` |
| a subtree reached by `@` is legal in the context its path determines | `TreeOk_at'` |
| the tree a legal path determines is legal, and dominates the path's responses | `TreeOk_ctxFrom`, `Ctx.above_ctxFrom`, `Ctx.le_ctxFrom` |
| recording a response opens exactly the positions one step further | `legalQuery_join_snoc` |
| planting a leaf at a perimeter position keeps a tree legal | `TreeOk_plant_leaf` |
| a legal query is coherent | `QueryOk.coherent` |
| a response's tree is its query's tree with the answer planted | `Resp.toTree_substAns`, `substTree_mono`, `toTree_lt_substAns` |
| an ascending chain is directed | `chain_directed` |
| `apply₀` is monotone in each argument | `apply0_mono_left`, `apply0_mono_right` |
| comparable trees answer a query compatibly | `at'_mono` |
| a tree containing a path answers that path's query | `at'_resp`, `apply0_first` |
| **Definition 4.9**: `apply₀` lands in `D_τ(γ')` | `apply0_ok` |
| **Lemma 4.16** (order-extensionality for finite trees) | `lemma_4_16` |
| — the separating argument of its proof | `lemma_4_16_separate` |
| **Lemma 4.14** | `lemma_4_14` |
| — its `k`-ary form | `applyArgs_at_query` |
| **Corollary 4.15** | `corollary_4_15`, `corollary_4_15_path` |
| the ground domain `T_o` is flat | `T_base_flat` |
| `apply (sub1, ⌜0⌝) = ⊥` (Definition 4.19) | `apply0_sub1_zero` |
| `Comb.tyOf` computes the type of a well-typed combinatory term | `Comb.tyOf_of_hasTy` |
| Figure 1's `λ*` and `[·]_CL` preserve typing | `Comb.lamStar_hasTy`, `Term.toComb_hasTy` |
| weakening, substitution and uniqueness for typing | `Comb.weaken`, `Comb.subst_hasTy`, `Term.weaken`, `Term.hasTy_unique` |
| a term's meaning depends only on its free variables | `Model.combMeaning_congr_env` |
| the `K` and `I` approximants form chains | `Kn_mono`, `In_mono` |
| **Definition 4.20**: the pruned `K` / `I` approximants are legal | `KnP_ok`, `InP_ok` |
| — they lie below the chain and lose nothing | `KnP_le_Kn`, `apply0_KnP_ge`, `InP_le_In`, `apply0_InP_ge` |
| finite legal approximants of `K` / `I` are cofinal | `Kn_legal_cofinal`, `In_legal_cofinal` |
| **Claim A.2** (both halves) | `claim_A_2`, `claim_A_2_le`, `claim_A_2_ge` |
| **Lemma A.1** (the `K` equation) | `lemma_A_1` |
| Theorem 4.22, the `(I)` equation | `theorem_4_22_I` |
| the `I` analogue of Claim A.2 | `claim_I_le`, `claim_I_ge` |
| order-extensionality implies extensionality (proof of Thm. 4.11) | `Model.extensional_of_orderExtensional` |
| a hole that propagates both errors is a sequentiality index | `SemDef.seqIndex_of_propagates` |
| **Theorem 6.5**: error-sensitivity implies sequentiality | `SemDef.theorem_6_5` |

Note that `Countable` is *not* a field of `FinitaryBasis` here.  It plays no
part in the construction of the ideal completion or in parts (1)–(3) of
Theorem 4.4, so it is taken as an explicit hypothesis where it is actually
used — ω-algebraicity.  Splitting Lemma 4.3 this way is what lets the finitary
basis `D_σ`, and hence `T_σ`, be built without any outstanding assumption.

### Proved from stated ingredients

These have real proofs, but their statement or their ingredients still mention
a `sorry`, so `#print axioms` reports `sorryAx` for them.  In particular
anything mentioning `Tmodel` inherits it from `Y_chain_directed` and
`claim_A_5`, and anything mentioning `SPCFSem` from `Tmeaning_mono`.  The
derivation is the content.

| Result | Lean name | Derived from |
| --- | --- | --- |
| Theorem 4.11 (`T` is extensional and order-extensional) | `theorem_4_11` | `orderExtensional_T` |
| Corollary 4.18 (`T_{σ→τ} ≅ F_{σ→τ}`) | `corollary_4_18` | `orderExtensional_T` |
| **Corollary 4.23** (β, η) | `corollary_4_23` | Theorem 4.22; the abstraction lemma `lamStar_apply` and `beta_law` |
| **Corollary 4.24** (the `Y` operator) | `corollary_4_24` | `applyT_interpY_fix`: `apply (Y, m) = ⊔ₙ mⁿ(⊥)` |
| `Ω_σ` denotes `⊥` | `meaning_Omega` | extensionality |
| `T[[Y_σ]]` is well defined | `Y_chain_directed` | `Yapprox_mono`, `chain_directed` |
| Lemma A.6 (the `S` equation) | `lemma_A_6` | `claim_A_5` |
| Theorem 4.22 | `theorem_4_22` | `lemma_A_6` (`lemma_A_1` and `theorem_4_22_I` are proved outright) |
| Theorem 4.4: ω-algebraicity of `T_σ` | `lemma_4_3_omega_algebraic` | `dsub_countable` |
| `T[[errorᵢ]] = errorᵢ` | `meaning_errTerm` | holds by `rfl`; mentions `SPCFSem` |
| `T[[Ω]] = ⊥`, the `Ω` field of Definition 6.1 | `meaning_omegaTerm` | `apply0_sub1_zero` + monotonicity of `apply₀` |
| the meaning of `(M E₁ … Eₖ)` | `meaning_apps` | the typing lemmas above |
| `apply` is determined by its finite arguments | `applyT_eq_of_principal` | — |
| iterated extensionality | `eq_of_principal_applyIdeals` | Theorem 4.11 |
| separation by finite arguments | `separation` | the two above |
| compositionality of `T` | `soundness`, `soundness_aux` | Corollary 4.23 + extensionality |
| monotonicity of `T` in a hole (Definition 2.1's `mono`) | `Tmeaning_mono` | `applyT_mono_*`, `lamStar_apply`, order-extensionality |
| **Theorem 5.1** (full abstraction), separating form | `theorem_5_1_separating` | `separation`, `lemma_5_2`, `meaning_apps` |
| **Theorem 5.1** | `theorem_5_1`, `theorem_5_1_fullyAbstract` | the above + `soundness` |
| **Theorem 6.2** (SPCF is sequential) | `theorem_6_2` | Theorem 6.4 via Theorem 6.5 |
| **Theorem 6.4** (SPCF is error-sensitive) | `theorem_6_4` | `probe_index`, `meaning_errTerm` |
| **Theorem 6.7** (SPCF is observably sequential) | `theorem_6_7` | Theorem 6.2, `probe_index`, `catch_returns_index` |

### Outstanding

Ten declarations, stated faithfully, whose own proof is still `sorry`.

| Result | Lean name | Note |
| --- | --- | --- |
| Lemma 4.3: `D_σ` is countable | `dsub_countable` | the only remaining half of Lemma 4.3; needed for ω-algebraicity alone |
| order-extensionality of `T` | `orderExtensional_T` | the limit form of Lemma 4.16 — see below |
| **Claim A.5** (well-definedness of `S`) | `claim_A_5` | Definition 4.21 + Figure 5 + Appendix A.2 |
| **Lemma A.7** | `lemma_A_7` | |
| **Lemma B.1** / **Lemma 4.26** | `lemma_B_1` | Appendix B; `lemma_4_26` is `lemma_B_1` |
| **Theorem 4.27** (`error`, `bottom`, `catch`, `return`) | `theorem_4_27` | |
| **Lemma 5.2** (definability of the finite elements) | `lemma_5_2`, `lemma_5_2_subtrees` | the crux of §5; **Theorem 5.1 now rests only on this and the Theorem 4.22 chain** |
| a `k`-ary procedure probes one argument first | `probe_index` | the tree analysis behind Thms. 6.2 and 6.4 |
| `catch` reports the sequentiality index | `catch_returns_index` | Theorem 4.27's `(catch)` equation |

#### What `orderExtensional_T` still needs

Lemma 4.16 itself is proved.  What remains is the passage to the ideal
completion, which is the argument the paper gives for Theorem 4.11: from
`f₀ ⋢ g` with `f₀` finite and `g` an ideal, "there exists a finite `d ∈ D_σ`
such that `apply (f₀, d) ⋢ apply (g₀, d)` **for all** `g₀ ⊑ g`", after which
continuity of `apply` gives `apply (f₀, d) ⋢ ⊔{apply (g₀,d) | g₀ ⊑ g}`.

The uniformity in `g₀` is the difficulty.  `lemma_4_16_separate` builds `d` from
the path along which `f₀` and one `g₀` diverge, and a priori that path varies
with `g₀`.  It does not, for two reasons that are not formalised here: the
separating paths lie in the finite tree `f₀`, so there are finitely many of
them, and a path that separates `f₀` from `g₁` separates it from every
`g₀ ⊑ g₁`, so directedness of the ideal pins down a single one; and the
subtrees `g₀ @ q` are themselves directed, so they share a root, which is all
that the construction of `d` consults about them.

## Definitions

All of the paper's definitions are formalised:
2.1 (`SemDef`), 2.2 (`Comb`), 2.3 (`Model`), 2.4/2.5 (`Model.combMeaning`,
`Model.meaning`), 2.6 (`Model.semanticsOfPrograms`; Figure 1's continuous function model `C` is
not constructed — see the docstring), 2.7 (`Po`, `ScottDomain.bot`),
2.8 (`Model.DenEquiv`, `SemDef.ObsEquiv`, `Model.FullyAbstract`),
2.9 (`SemDef.Sequential`), 3.1 (`SPCF`), 4.1 (`Tmodel`),
4.2 (`Query`, `Resp`, `Ctx`, `RespCtx`, `CtxOk`, `QueryOk`, `LegalQuery`,
`LegalResp`, `Tree`, `TreeOk`, `DSub`, `D`, `Query.substAns`,
`Resp.extendHole`),
4.5 (`Tree.at'`, `Tree.ValidQuery`, `Query.prefixOf`),
4.6 (`Tree.root`, `Tree.ImmIncomparable`), 4.9 (`apply0`, `applyT`),
4.10 (`Model.Extensional`, `Model.OrderExtensional`), 4.12 (`Query.ctx`, `Query.ctxFrom`, `Query.ctxList`),
4.13 (`Query.shift1`), 4.17 (`funOf`, `FunDom`, `FunLe`),
4.19 (`treeAdd1`, `treeSub1`, `treeIf0`, `treeCatch`), 4.20 (`Kn`, `treeK`),
4.21 (`treeS`), 4.25 (`EvalCtx`), 5.3 (`Representable`), 6.1 (`SPCFSem`),
6.3 (`SemDef.ErrorSensitive`), 6.6 (`SemDef.ObservablySequential`),
A.3 (`claim_A_5`), A.4 (`ErrorVariant`).

## What §7 says

Section 7 ("Generalizing Observable Sequentiality") states no numbered results;
it discusses control delimiters and gives the example of `PCF⁺` with `%`.  It is
not formalised.
