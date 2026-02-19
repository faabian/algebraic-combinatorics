# Formalization of *Algebraic Combinatorics*

A Lean 4 formalization of the textbook *Math 701 — Algebraic Combinatorics*
(Spring 2021, version 31 May 2025) by Darij Grinberg, built on Mathlib.
The formalization covers 344 target theorems across 45 chapters, from formal power
series and integer partitions through permutations, determinants, and symmetric
functions.

> **Assessment policy**: A theorem is marked PROVED only if it and all its transitive
> dependencies are `sorry`-free.

## Overall Statistics

| | | | |
|---|---|---|---|
| Target theorems | 344 | Lean source files | 52 |
| Proved | 340 (99%) | Lines of Lean code | ~130,000 |
| Exercise | 4 (1%) | Sorry-free files | 48 of 51 |
| | | Sorry tactics | 5 (all exercise) |

### Growth

Lines of Lean code over time (~130k LOC at HEAD):

![Lean LOC over time](assets/loc_over_time.png)

Lean declarations (theorems, lemmas, definitions) over time (~5,900 at HEAD):

![Lean declarations over time](assets/declarations_over_time.png)

Cumulative lines added and removed (174k added, 47k removed):

![Code churn over time](assets/churn_over_time.png)

Target theorem status — each square is one of the 344 targets:

![Theorem-level formalization status](assets/dep_graph_theorems.png)

---

## Target Theorem Status

Of the 344 targets, 340 are PROVED (sorry-free with all transitive dependencies).
The remaining 4 are exercises in the TeX source — the textbook defers them to
exercises or leaves them to the reader. These have `sorry` stubs in the Lean code
(5 sorry tactics total, since `thm.sf.pieri` has two).

| Target | Description | Sorries |
|--------|-------------|--------:|
| `thm.sf.pieri` | Pieri rules (needs RSK insertion) | 2 |
| `thm.sf.jt-e` | Jacobi-Trudi for e (needs ω-involution) | 1 |
| `thm.det.cauchy` | Cauchy determinant (`ring` timeout n≥5) | 1 |
| `cor.lgv.catalan-hankel-det-0` | Catalan-Hankel det (general k≥8) | 1 |

There are no theorems blocked by upstream sorries. It appears that every theorem whose proof
appears in the TeX source has been fully formalized.

---

## Codebase Structure

```
AlgebraicCombinatorics/
├── FPS/                          # Formal power series (Ch. 3)
│   ├── CommutativeRings.lean         Commutative ring reminders
│   ├── NotationsExamples.lean        Notations + examples (Ch. 2.3, 3.1)
│   ├── Polynomials.lean              Polynomial rings
│   ├── Substitution.lean             Substitution and evaluation
│   ├── Derivatives.lean              Derivatives of FPS
│   ├── ExpLog.lean                   Exponentials and logarithms
│   ├── NonIntegerPowers.lean         Non-integer powers
│   ├── IntegerCompositions.lean      Integer compositions
│   ├── XnEquivalence.lean            x^n-equivalence
│   ├── InfiniteProducts.lean         Infinite products: properties
│   ├── InfiniteProducts1.lean        Infinite products: details part 1
│   ├── InfiniteProducts2.lean        Infinite products: product rules
│   ├── WeightedSets.lean             Generating function of weighted sets
│   ├── Limits.lean                   Limits of FPS
│   ├── Multivariate.lean             Multivariate FPS
│   └── LaurentSeries.lean            Laurent series (FPS namespace)
├── FPSDefinition.lean            # FPS ring definition (Ch. 3.2-3.6)
├── DividingFPS.lean              # Dividing FPS, Newton binomial (Ch. 3.7)
├── LaurentSeries.lean            # Laurent and doubly-infinite series (Ch. 3.14)
│
├── Partitions/                   # Integer partitions (Ch. 4)
│   ├── Basics.lean                   Partition basics, generating functions
│   └── QBinomialFormulas.lean        q-binomial formulas + limits
├── QBinomialBasic.lean           # q-binomial basic properties (Ch. 4.4)
├── PentagonalJacobi.lean         # Pentagonal theorem + Jacobi triple product (Ch. 4.2-4.3)
│
├── Permutations/                 # Permutations (Ch. 5)
│   ├── Basics.lean                   Definitions, transpositions, cycles
│   ├── Inversions1.lean              Inversions + Lehmer codes
│   ├── Inversions2.lean              More about lengths and simples
│   ├── Signs.lean                    Signs of permutations
│   └── CycleDecomposition.lean       Cycle decomposition
│
├── SignedCounting/               # Signed counting (Ch. 6.1-6.3)
│   ├── AlternatingSums.lean          Cancellations in alternating sums
│   ├── InclusionExclusion1.lean      Inclusion-exclusion
│   ├── BooleanMobiusInversion.lean   Boolean Möbius inversion
│   └── SubtractiveMethods.lean       More subtractive methods
│
├── DeterminantsBasic.lean        # Determinants: basic properties (Ch. 6.4.1-6.4.2)
├── CauchyBinet.lean              # Cauchy-Binet + factoring (Ch. 6.4.3-6.4.5)
├── DesnanotJacobi.lean           # Desnanot-Jacobi + Cauchy det (Ch. 6.4.6-6.4.8)
├── Determinants/                 # LGV lemma (Ch. 6.5)
│   ├── LGV1.lean                     Definitions + k paths
│   ├── LGV2.lean                     Weighted + nonpermutable
│   └── PermFinset.lean               (support) permutation images of finsets
│
├── SymmetricFunctions/           # Symmetric functions (Ch. 7)
│   ├── Definitions.lean              Definitions, fundamental theorem
│   ├── MonomialSymmetric.lean        Monomial symmetric polynomials
│   ├── SchurBasics.lean              Schur polynomials, skew Schur
│   ├── LittlewoodRichardson.lean     Littlewood-Richardson rule
│   ├── PieriJacobiTrudi.lean         Pieri rules + Jacobi-Trudi
│   ├── NPartition.lean               (support) N-partition shared defs
│   ├── SSYTEquiv.lean                (support) SSYT equivalence
│   └── OmegaInvolution.lean          (support) omega involution
│
├── Details/                      # Appendix B: omitted details
│   ├── DominoTilings.lean            Domino tilings
│   ├── DominoBridge.lean             (support) domino bridge
│   ├── InfiniteProducts2.lean        Infinite products details
│   └── Limits.lean                   Limits details
│
├── Fin/SkipTwo.lean              # (support) Fin index utilities
└── Extra/Pfaffian.lean           # (support) Pfaffian infrastructure
```

---

## Chapter-by-Chapter Status

### Chapter 2-3: FPS and Generating Functions

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Notations + Examples | NotationsExamples.lean | 4/4 | ✅ |
| Commutative Rings | CommutativeRings.lean | 2/2 | ✅ |
| FPS Definition | FPSDefinition.lean | 14/14 | ✅ |
| Dividing FPS | DividingFPS.lean | 19/19 | ✅ |
| Polynomials | Polynomials.lean | 6/6 | ✅ |
| Substitution | Substitution.lean | 5/5 | ✅ |
| Derivatives | Derivatives.lean | 2/2 | ✅ |
| Exp/Log | ExpLog.lean | 15/15 | ✅ |
| Non-Integer Powers | NonIntegerPowers.lean | 4/4 | ✅ |
| Integer Compositions | IntegerCompositions.lean | 7/7 | ✅ |
| x^n-Equivalence | XnEquivalence.lean | 4/4 | ✅ |
| Infinite Products (properties) | InfiniteProducts.lean | 21/21 | ✅ |
| Infinite Products (rules) | InfiniteProducts2.lean | 12/12 | ✅ |
| Weighted Sets | WeightedSets.lean | 9/9 | ✅ |
| Limits | Limits.lean | 14/14 | ✅ |
| Laurent Series | LaurentSeries.lean | 8/8 | ✅ |
| Multivariate FPS | Multivariate.lean | 1/1 | ✅ |

### Chapter 4: Partitions and q-Binomials

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Partition Basics | Basics.lean | 15/15 | ✅ |
| Pentagonal + Jacobi Triple Product | PentagonalJacobi.lean | 7/7 | ✅ |
| q-Binomial (basic) | QBinomialBasic.lean | 10/10 | ✅ |
| q-Binomial (formulas) | QBinomialFormulas.lean | 8/8 | ✅ |

### Chapter 5: Permutations

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Basics + Transpositions | Basics.lean | 9/9 | ✅ |
| Inversions + Lehmer | Inversions1.lean | 9/9 | ✅ |
| Lengths + Simples | Inversions2.lean | 7/7 | ✅ |
| Signs | Signs.lean | 7/7 | ✅ |
| Cycle Decomposition | CycleDecomposition.lean | 4/4 | ✅ |

### Chapter 6: Signed Counting and Determinants

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Alternating Sums | AlternatingSums.lean | 6/6 | ✅ |
| Inclusion-Exclusion | InclusionExclusion1.lean | 7/7 | ✅ |
| Boolean Möbius | BooleanMobiusInversion.lean | 2/2 | ✅ |
| Subtractive Methods | SubtractiveMethods.lean | 3/3 | ✅ |
| Det Basic Properties | DeterminantsBasic.lean | 10/10 | ✅ |
| Cauchy-Binet | CauchyBinet.lean | 8/8 | ✅ |
| Desnanot-Jacobi | DesnanotJacobi.lean | 11/12 | 🟡 1 exercise |
| LGV (definitions) | LGV1.lean | 7/7 | ✅ |
| LGV (weighted) | LGV2.lean | 4/5 | 🟡 1 exercise |

### Chapter 7: Symmetric Functions

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Definitions | Definitions.lean | 12/12 | ✅ |
| Monomial Symmetric | MonomialSymmetric.lean | 7/7 | ✅ |
| Schur Polynomials | SchurBasics.lean | 16/16 | ✅ |
| Littlewood-Richardson | LittlewoodRichardson.lean | 11/11 | ✅ |
| Pieri + Jacobi-Trudi | PieriJacobiTrudi.lean | 3/5 | 🟡 2 exercise |

### Appendix B: Omitted Details

| Section | File | Targets | Status |
|---------|------|--------:|--------|
| Infinite Products (part 1) | InfiniteProducts1.lean | 3/3 | ✅ |
| Infinite Products (part 2) | InfiniteProducts2.lean | 1/1 | ✅ |
| Domino Tilings | DominoTilings.lean | 2/2 | ✅ |
| Limits | Limits.lean | 2/2 | ✅ |
| Laurent Series | LaurentSeries.lean | 2/2 | ✅ |

---

## Exercise Details (4 targets, 5 sorry tactics)

These are theorems whose proofs the TeX source explicitly defers to exercises
("See Exercise ...") or leaves to the reader ("The details are LTTR").

**`thm.sf.pieri`** (Pieri rules): The TeX source says "See Exercise exe.sf.pieri".
Requires RSK row/column insertion, which is not formalized. The theorem *statements*
are in Lean with `sorry -- [exercise]` (2 sorry tactics: horizontal and vertical).
The strip partition definitions and characterization lemmas are fully proved.

**`thm.sf.jt-e`** (Jacobi-Trudi for elementary symmetric polynomials): The TeX says
"See Exercise exe.sf.jt-e" (6 points, no hint). Would follow from applying the
omega-involution to `jacobiTrudi_h` (which IS proved).

**`thm.det.cauchy`** (Cauchy determinant identity): Cited as Exercise 6.18 in
[Grinbe15]. Proved for n ≤ 8 via base cases; the general case requires a polynomial
identity where Lean's `ring` tactic times out (degree ~256 polynomials).

**`cor.lgv.catalan-hankel-det-0`** (Catalan-Hankel determinant): The TeX says "The
details are LTTR". Proved for k ≤ 7 via `native_decide`; the general case k ≥ 8
needs assembly of existing infrastructure (`catalan_unique_nipat` is proved).

---

## Notes

1. **Proof status.** Every target marked PROVED is transitively `sorry`-free.
   The 5 remaining sorries are all in exercise stubs, each tagged
   `-- [exercise]` with its TeX reference. There are no unmarked sorries.

2. **Mathlib and original work.** The formalization uses Mathlib for foundational
   infrastructure: the `PowerSeries` ring and its arithmetic, `MvPolynomial`,
   `Matrix.det` and its basic properties (transpose, triangular, row operations,
   `det_mul`), `Equiv.Perm` and the sign homomorphism, and `Nat.Partition` basics.
   The FPS definition wraps `PowerSeries` with the textbook's notation, and a few
   determinant results (Vandermonde, Cauchy-Binet) reformulate Mathlib theorems.

   The bulk of the formalization is original work, including among others:
   - **Formal power series theory**: infinite products and multipliability,
     x^n-equivalence, limits and convergence criteria, substitution into infinite
     products, the Exp-Log group isomorphism via ODE uniqueness, non-integer powers,
     Laurent and doubly-infinite power series
   - **Partition theory**: generating function identities, odd-distinct bijection,
     q-binomial coefficients (recursion, quotient formulas, q-Vandermonde,
     subspace counting, limits), pentagonal number theorem, Euler's partition
     recurrence
   - **Jacobi triple product**: two independent proofs (Borcherds' states/energy
     approach in `ℚ⟦X⟧` and the `(ℤ[z^±])[[q]]` approach), including the full
     State/excitedState bijection machinery
   - **Permutations**: inversions, Lehmer codes and their bijection with
     permutations, reduced word characterization, cycle decomposition (existence
     and uniqueness)
   - **Signed counting**: cancellation lemmas, inclusion-exclusion (size and
     weighted versions), derangement counting, Euler's totient via inclusion-exclusion,
     Boolean Möbius inversion, q-Lucas theorem
   - **Determinants**: Desnanot-Jacobi identity (via MvPolynomial + FractionRing,
     avoiding `ring` on large matrices), Jacobi's complementary minor formula,
     det(A+B) expansion, multi-row Laplace expansion
   - **LGV lemma**: full weighted version for DAGs with lattice path applications,
     non-intersecting path characterization, binomial determinant nonnegativity,
     Catalan-Hankel determinants (k ≤ 7)
   - **Symmetric functions**: monomial symmetric polynomials and the m-basis,
     Schur and skew Schur polynomials, Bender-Knuth involutions (cell-level
     parenthesis-matching formulation, row-weak/column-strict preservation,
     involutivity, content swap), Stembridge involutions (matching-based prefix
     BK, content transposition), the Littlewood-Richardson rule (Zelevinsky
     version), Jacobi-Trudi formula for h via LGV
   - **Domino tilings**: height-3 rectangle classification, tiling decomposition
     bijection, weighted set generating functions
