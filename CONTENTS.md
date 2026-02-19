# Formalization Contents

> **Updated**: 2026-02-27
>
> **Assessment policy**: A theorem is marked PROVED only if it and all its transitive
> dependencies are `sorry`-free.

## Overall Statistics

| Metric | Count |
|--------|------:|
| Target theorems | 344 |
| Chapters | 45 |
| Lean source files | 52 |
| Actual `sorry` tactics | 5 (all exercise) |
| Sorry-free Lean files | 48 of 51 |
| Targets PROVED | 340 (99%) |
| Targets EXERCISE | 4 (1%) |

## Target Theorem Status Summary

### Non-proved targets (4 exercises, 5 sorry tactics)

| Target | Blocker | Issue |
|--------|---------|-------|
| `thm.sf.pieri` | Pieri rules (needs RSK insertion) | `cleanup-pieri` |
| `thm.sf.jt-e` | Jacobi-Trudi for e (needs ω-involution) | `cleanup-jt-e` |
| `thm.det.cauchy` | Cauchy determinant (`ring` timeout n≥5) | `cleanup-cauchy` |
| `cor.lgv.catalan-hankel-det-0` | Catalan-Hankel det (general k≥8) | `cleanup-catalan` |

All other 340 targets are PROVED (sorry-free with all transitive dependencies).

---

## TeX Sources

| Chapter | Source | Lean Entry Point |
|---------|--------|------------------|
| Notations and elementary facts + Examples | `AlgebraicCombinatorics/tex/FPS/Notations.tex` | `FPS/NotationsExamples.lean` |
| Definitions: (preamble) ... Reminder: Commutative rings | `AlgebraicCombinatorics/tex/FPS/CommutativeRings.tex` | `FPS/CommutativeRings.lean` |
| Definitions: The definition of formal power ... What next? | `AlgebraicCombinatorics/tex/FPS/FPSDefinition.tex` | `FPSDefinition.lean` |
| Dividing FPSs | `AlgebraicCombinatorics/tex/FPS/DividingFPS.tex` | `DividingFPS.lean` |
| Polynomials | `AlgebraicCombinatorics/tex/FPS/Polynomials.tex` | `FPS/Polynomials.lean` |
| Substitution and evaluation of power series | `AlgebraicCombinatorics/tex/FPS/Substitution.tex` | `FPS/Substitution.lean` |
| Derivatives of FPSs | `AlgebraicCombinatorics/tex/FPS/Derivatives.tex` | `FPS/Derivatives.lean` |
| Exponentials and logarithms | `AlgebraicCombinatorics/tex/FPS/ExpLog.tex` | `FPS/ExpLog.lean` |
| Non-integer powers | `AlgebraicCombinatorics/tex/FPS/NonIntegerPowers.tex` | `FPS/NonIntegerPowers.lean` |
| Integer compositions | `AlgebraicCombinatorics/tex/FPS/IntegerCompositions.tex` | `FPS/IntegerCompositions.lean` |
| x^{n}-equivalence | `AlgebraicCombinatorics/tex/FPS/XnEquivalence.tex` | `FPS/XnEquivalence.lean` |
| Infinite products: Properties | `AlgebraicCombinatorics/tex/FPS/InfiniteProducts1.tex` | `FPS/InfiniteProducts.lean` |
| Infinite products: Product rules + Exp/Log | `AlgebraicCombinatorics/tex/FPS/InfiniteProducts2.tex` | `FPS/InfiniteProducts2.lean` |
| The generating function of a weighted set | `AlgebraicCombinatorics/tex/FPS/WeightedSets.tex` | `FPS/WeightedSets.lean` |
| Limits of FPSs | `AlgebraicCombinatorics/tex/FPS/Limits.tex` | `FPS/Limits.lean` |
| Laurent power series | `AlgebraicCombinatorics/tex/FPS/LaurentSeries.tex` | `LaurentSeries.lean` |
| Multivariate FPSs | `AlgebraicCombinatorics/tex/FPS/Multivariate.tex` | `FPS/Multivariate.lean` |
| Partition basics | `AlgebraicCombinatorics/tex/Partitions/Basics.tex` | `Partitions/Basics.lean` |
| Pentagonal number theorem + Jacobi triple product | `AlgebraicCombinatorics/tex/Partitions/PentagonalJacobi.tex` | `PentagonalJacobi.lean` |
| q-binomial coefficients: Basic properties | `AlgebraicCombinatorics/tex/Partitions/QBinomialBasic.tex` | `QBinomialBasic.lean` |
| q-binomial coefficients: Formulas + Limits | `AlgebraicCombinatorics/tex/Partitions/QBinomialFormulas.tex` | `Partitions/QBinomialFormulas.lean` |
| Basic definitions + Transpositions, cycles, involutions | `AlgebraicCombinatorics/tex/Permutations/Basics.tex` | `Permutations/Basics.lean` |
| Inversions + Lehmer codes | `AlgebraicCombinatorics/tex/Permutations/Inversions1.tex` | `Permutations/Inversions1.lean` |
| More about lengths and simples | `AlgebraicCombinatorics/tex/Permutations/Inversions2.tex` | `Permutations/Inversions2.lean` |
| Signs of permutations | `AlgebraicCombinatorics/tex/Permutations/Signs.tex` | `Permutations/Signs.lean` |
| The cycle decomposition | `AlgebraicCombinatorics/tex/Permutations/CycleDecomposition.tex` | `Permutations/CycleDecomposition.lean` |
| Cancellations in alternating sums | `AlgebraicCombinatorics/tex/SignedCounting/AlternatingSums.tex` | `SignedCounting/AlternatingSums.lean` |
| Inclusion-exclusion: Size + Weighted versions | `AlgebraicCombinatorics/tex/SignedCounting/InclusionExclusion1.tex` | `SignedCounting/InclusionExclusion1.lean` |
| Inclusion-exclusion: Boolean Möbius inversion | `AlgebraicCombinatorics/tex/SignedCounting/InclusionExclusion2.tex` | `SignedCounting/BooleanMobiusInversion.lean` |
| More subtractive methods | `AlgebraicCombinatorics/tex/SignedCounting/SubtractiveMethods.tex` | `SignedCounting/SubtractiveMethods.lean` |
| Determinants: Basic properties | `AlgebraicCombinatorics/tex/Determinants/BasicProperties.tex` | `DeterminantsBasic.lean` |
| Determinants: Cauchy–Binet + Factoring | `AlgebraicCombinatorics/tex/Determinants/CauchyBinet.tex` | `CauchyBinet.lean` |
| Determinants: Factor hunting + Desnanot–Jacobi | `AlgebraicCombinatorics/tex/Determinants/DesnanotJacobi.tex` | `DesnanotJacobi.lean` |
| LGV lemma: Definitions + k paths | `AlgebraicCombinatorics/tex/Determinants/LGV1.tex` | `Determinants/LGV1.lean` |
| LGV lemma: Weighted + Nonpermutable | `AlgebraicCombinatorics/tex/Determinants/LGV2.tex` | `Determinants/LGV2.lean` |
| (Support) Permutation images of finsets | — | `Determinants/PermFinset.lean` |
| (Support) Fin index-skipping utilities | — | `Fin/SkipTwo.lean` |
| (Support) NPartition shared definition | — | `SymmetricFunctions/NPartition.lean` |
| (Support) SSYT equivalence | — | `SymmetricFunctions/SSYTEquiv.lean` |
| (Support) Domino bridge | — | `Details/DominoBridge.lean` |
| (Support) Extra/Pfaffian | — | `Extra/Pfaffian.lean` |
| (Support) ω-involution on symmetric functions | — | `SymmetricFunctions/OmegaInvolution.lean` |
| Symmetric functions: Definitions | `AlgebraicCombinatorics/tex/SymmetricFunctions/Definitions.tex` | `SymmetricFunctions/Definitions.lean` |
| Monomial symmetric polynomials | `AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex` | `SymmetricFunctions/MonomialSymmetric.lean` |
| Schur polynomials: Basics + Skew | `AlgebraicCombinatorics/tex/SymmetricFunctions/SchurBasics.tex` | `SymmetricFunctions/SchurBasics.lean` |
| Littlewood–Richardson rule | `AlgebraicCombinatorics/tex/SymmetricFunctions/LittlewoodRichardson.tex` | `SymmetricFunctions/LittlewoodRichardson.lean` |
| Pieri rules + Jacobi–Trudi | `AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex` | `SymmetricFunctions/PieriJacobiTrudi.lean` |
| Details: Infinite products (part 1) | `AlgebraicCombinatorics/tex/Details/InfiniteProducts1.tex` | `FPS/InfiniteProducts1.lean` |
| Details: Infinite products (part 2) | `AlgebraicCombinatorics/tex/Details/InfiniteProducts2.tex` | `Details/InfiniteProducts2.lean` |
| Details: Domino tilings | `AlgebraicCombinatorics/tex/Details/DominoTilings.tex` | `Details/DominoTilings.lean` |
| Details: Limits of FPSs | `AlgebraicCombinatorics/tex/Details/Limits.tex` | `Details/Limits.lean` |
| Details: Laurent power series | `AlgebraicCombinatorics/tex/Details/LaurentSeries.tex` | `FPS/LaurentSeries.lean` |

---

## Chapter 2: Before We Start

### 2.3 Notations and Elementary Facts + 3.1 Examples

**Manifest chapter**: `ac-notations-and-elementary-facts-examples`
**Lean file**: `FPS/NotationsExamples.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.binom.binom` | PROVED |
| `prop.binom.rec` | PROVED |
| `prop.binom.0` | PROVED |
| `thm.binom.sym` | PROVED |

---

## Chapter 3: Generating Functions

### 3 Preamble — Commutative Rings

**Manifest chapter**: `ac-definitions-preamble-reminder-commutativ`
**Lean file**: `FPS/CommutativeRings.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.alg.commring` | PROVED |
| `def.alg.module` | PROVED |

### 3.2–3.6 Definition of FPS + What Next?

**Manifest chapter**: `ac-definitions-the-definition-of-formal-pow`
**Lean file**: `FPSDefinition.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.fps` | PROVED |
| `def.fps.ops` | PROVED |
| `thm.fps.ring` | PROVED |
| `def.fps.coeff` | PROVED |
| `def.infsum.essfin` | PROVED |
| `def.fps.summable` | PROVED |
| `prop.fps.summable.sub` | PROVED |
| `prop.fps.summable-sums-rule` | PROVED |
| `def.fps.x` | PROVED |
| `lem.fps.xa` | PROVED |
| `prop.fps.xk` | PROVED |
| `cor.fps.sumakxk` | PROVED |
| `prop.binom.vandermonde.NN` | PROVED |
| `thm.binom.vandermonde.CC` | PROVED |

### 3.7 Dividing FPSs

**Manifest chapter**: `ac-dividing-fpss`
**Lean file**: `DividingFPS.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.commring.inverse` | PROVED |
| `thm.commring.inverse-uni` | PROVED |
| `def.commring.fracs` | PROVED |
| `prop.commring.fracs.1` | PROVED |
| `prop.fps.invertible` | PROVED |
| `cor.fps.invertible.field` | PROVED |
| `prop.fps.invertible.1+x` | PROVED |
| `thm.fps.newton-binom` | PROVED |
| `thm.binom.upneg-n` | PROVED |
| `prop.fps.anti-newton-binom` | PROVED |
| `cor.fps.anti-newton-binom-2` | PROVED |
| `def.fps.div-by-x` | PROVED |
| `prop.fps.div-by-x-inverts` | PROVED |
| `lem.fps.g=xh` | PROVED |
| `lem.fps.first-n-coeffs-of-xna` | PROVED |
| `lem.fps.muls-of-xn` | PROVED |
| `lem.fps.prod.irlv.fg` | PROVED |
| `lem.fps.prod.irlv.mul` | PROVED |
| `lem.fps.prod.irlv.cong-mul` | PROVED |

### 3.8 Polynomials

**Manifest chapter**: `ac-polynomials`
**Lean file**: `FPS/Polynomials.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.pol` | PROVED |
| `thm.fps.pol.ring` | PROVED |
| `def.alg.ring` | PROVED |
| `def.alg.Kalg` | PROVED |
| `def.pol.subs` | PROVED |
| `thm.pol.eval.a+b` | PROVED |

### 3.9 Substitution and Evaluation

**Manifest chapter**: `ac-substitution-and-evaluation-of-power-ser`
**Lean file**: `FPS/Substitution.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.subs` | PROVED |
| `prop.fps.subs.wd` | PROVED |
| `prop.fps.subs.rules` | PROVED |
| `lem.fps.fg-coeffs-0` | PROVED |
| `def.kron-delta` | PROVED |

### 3.10 Derivatives of FPSs

**Manifest chapter**: `ac-derivatives-of-fpss`
**Lean file**: `FPS/Derivatives.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.deriv` | PROVED |
| `thm.fps.deriv.rules` | PROVED |

### 3.11.1–3.11.5 Exponentials and Logarithms

**Manifest chapter**: `ac-exponentials-and-logarithms`
**Lean file**: `FPS/ExpLog.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.exp-log` | PROVED |
| `prop.fps.exp-log-der` | PROVED |
| `lem.fps.compos-cst-term-0` | PROVED |
| `thm.fps.exp-log-inv` | PROVED |
| `def.fps.Exp-Log-maps` | PROVED |
| `lem.fps.Exp-Log-maps-wd` | PROVED |
| `lem.fps.Exp-Log-maps-inv` | PROVED |
| `lem.fps.Exp-Log-additive` | PROVED |
| `prop.fps.Exp-Log-groups` | PROVED |
| `thm.fps.Exp-Log-group-iso` | PROVED |
| `def.fps.loder.1` | PROVED |
| `prop.fps.loder.log` | PROVED |
| `prop.fps.loder.prod` | PROVED |
| `cor.fps.loder.prodk` | PROVED |
| `cor.fps.loder.inv` | PROVED |

### 3.11.5 Non-Integer Powers

**Manifest chapter**: `ac-non-integer-powers`
**Lean file**: `FPS/NonIntegerPowers.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.power-c` | PROVED |
| `thm.fps.power-c.rules` | PROVED |
| `thm.fps.gen-newton` | PROVED |
| `prop.binom.nCk-2i-qedmo.CN` | PROVED |

### 3.11 Integer Compositions

**Manifest chapter**: `ac-integer-compositions`
**Lean file**: `FPS/IntegerCompositions.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.comps` | PROVED |
| `thm.fps.comps.num-comps-n-k` | PROVED |
| `thm.fps.comps.num-comps-n` | PROVED |
| `def.fps.wcomps` | PROVED |
| `thm.fps.comps.num-wcomps-n-k` | PROVED |
| `thm.fps.comps.num-wpcomps-n-k` | PROVED |
| `prop.fps.comps.num-w2comps-n-k-id` | PROVED |

### 3.11 x^n-Equivalence

**Manifest chapter**: `ac-x-n-equivalence`
**Lean file**: `FPS/XnEquivalence.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.xneq` | PROVED |
| `thm.fps.xneq.props` | PROVED |
| `prop.fps.xneq-multiple` | PROVED |
| `prop.fps.xneq.comp` | PROVED |

### 3.11.6 Infinite Products — Properties

**Manifest chapter**: `ac-infinite-products-preamble-properties-of`
**Lean file**: `FPS/InfiniteProducts.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.determines-xn-coeff` | PROVED |
| `def.fps.xn-coeff-fin-determined` | PROVED |
| `prop.fps.summable=fin-det` | PROVED |
| `def.fps.multipliable` | PROVED |
| `prop.fps.multipliable.prod-wd` | PROVED |
| `prop.fps.multipliable.prod-wd2` | PROVED |
| `lem.fps.prod.irlv.1` | PROVED |
| `lem.fps.prod.irlv.fin` | PROVED |
| `thm.fps.1+f-mulable` | PROVED |
| `prop.fps.1-mulable` | PROVED |
| `def.fps.infprod-approx` | PROVED |
| `lem.fps.mulable.approx` | PROVED |
| `prop.fps.infprod-approx-xneq` | PROVED |
| `prop.fps.union-mulable` | PROVED |
| `prop.fps.prod-mulable` | PROVED |
| `prop.fps.div-mulable` | PROVED |
| `prop.fps.prods-mulable-subfams` | PROVED |
| `prop.fps.prods-mulable-rules.reindex` | PROVED |
| `prop.fps.prods-mulable-rules.SW1` | PROVED |
| `prop.fps.prods-mulable-rules.fubini1` | PROVED |
| `prop.fps.prods-mulable-rules.fubini` | PROVED |

### 3.11.7–3.11.10 Infinite Products — Product Rules + Exp/Log

**Manifest chapter**: `ac-infinite-products-product-rules-generali`
**Lean file**: `FPS/InfiniteProducts2.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.fps.prodrule-fin-fin` | PROVED |
| `prop.fps.prodrule-fin-inf` | PROVED |
| `def.fps.prodrule.ess-fin` | PROVED |
| `prop.fps.prodrule-inf-infN` | PROVED |
| `prop.fps.prodrule-inf-inf` | PROVED |
| `prop.fps.prodrule-fin-infJ` | PROVED |
| `lem.fps.prod.irlv.inf` | PROVED |
| `prop.gf.prod.euler-odd` | PROVED |
| `thm.gf.prod.euler-comb` | PROVED |
| `prop.fps.subs.rule-infprod` | PROVED |
| `prop.fps.Exp-Log-infsum` | PROVED |
| `prop.fps.Exp-Log-infprod` | PROVED |

> 12/12 proved.

### 3.12 Generating Function of a Weighted Set

**Manifest chapter**: `ac-the-generating-function-of-a-weighted`
**Lean file**: `FPS/WeightedSets.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.gf-ws.weighted-sets` | PROVED |
| `prop.gf-ws.iso` | PROVED |
| `def.gf-ws.djun` | PROVED |
| `prop.gf-ws.djun` | PROVED |
| `def.gf-ws.prod` | PROVED |
| `prop.gf-ws.prod` | PROVED |
| `prop.gf-ws.pow` | PROVED |
| `def.domino.shapes-and-tilings` | PROVED |
| `lem.gf.weighted-set.domino.fd` | PROVED |

> 9/9 proved. `decomposeTiling_composeTilings` was proved (the bijection inverse
> for the tiling decomposition isomorphism — a dependent-type bookkeeping issue).

### 3.13 Limits of FPSs

**Manifest chapter**: `ac-limits-of-fpss`
**Lean file**: `FPS/Limits.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.fps.lim.stab` | PROVED |
| `def.fps.lim.coeff-stab` | PROVED |
| `thm.fps.lim.lim-crit` | PROVED |
| `lem.fps.lim.xn-equiv` | PROVED |
| `prop.fps.lim.sum-prod` | PROVED |
| `cor.fps.lim.sum-prod-k` | PROVED |
| `prop.fps.lim.sum-quot` | PROVED |
| `prop.fps.lim.comp` | PROVED |
| `prop.fps.lim.deriv-lim` | PROVED |
| `thm.fps.lim.sum-lim` | PROVED |
| `thm.fps.lim.prod-lim` | PROVED |
| `cor.fps.lim.fps-as-pol` | PROVED |
| `thm.fps.lim.sum-lim-conv` | PROVED |
| `thm.fps.lim.prod-lim-conv` | PROVED |

### 3.14 Laurent Power Series

**Manifest chapter**: `ac-laurent-power-series`
**Lean file**: `LaurentSeries.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.fps.laure.binary-rep-uniq` | PROVED |
| `thm.fps.laure.balanced-tern-rep-uniq` | PROVED |
| `def.fps.laure.double` | PROVED |
| `def.fps.laure.laupol` | PROVED |
| `thm.fps.laure.laupol-ring` | PROVED |
| `prop.fps.laure.a=sumaixi` | PROVED |
| `def.fps.laure.lauser` | PROVED |
| `thm.fps.laure.lauser-ring` | PROVED |

### 3.15 Multivariate FPSs

**Manifest chapter**: `ac-multivariate-fpss`
**Lean file**: `FPS/Multivariate.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.fps.mulvar.comp-y-coeff` | PROVED |

---

## Chapter 4: Integer Partitions and q-Binomial Coefficients

### 4.1 Partition Basics

**Manifest chapter**: `ac-partition-basics`
**Lean file**: `Partitions/Basics.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.pars.parts` | PROVED |
| `def.pars.pn-pkn` | PROVED |
| `def.pars.iverson` | PROVED |
| `def.pars.floor-ceil` | PROVED |
| `prop.pars.basics` | PROVED |
| `thm.pars.main-gf` | PROVED |
| `thm.pars.main-gf-parts-n` | PROVED |
| `thm.pars.main-gf-parts-I` | PROVED |
| `def.pars.odd-dist-parts` | PROVED |
| `thm.pars.odd-dist-equal` | PROVED |
| `prop.pars.pkn=dual` | PROVED |
| `cor.pars.p0kn=dual` | PROVED |
| `thm.pars.main-gf-0n` | PROVED |
| `thm.pars.sigma1` | PROVED |
| `thm.pars.sigma1-I` | PROVED |

### 4.2–4.3 Pentagonal Number Theorem + Jacobi Triple Product

**Manifest chapter**: `ac-euler-s-pentagonal-number-theorem-jacobi`
**Lean file**: `PentagonalJacobi.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.pars.pent-num` | PROVED |
| `thm.pars.pent` | PROVED |
| `cor.pars.pn-rec` | PROVED |
| `thm.pars.jtp1` | PROVED |
| `thm.pars.jtp2` | PROVED |
| `lem.fps.fxx=gxx` | PROVED |
| `thm.pars.euler-sum-div-rec` | PROVED |

> 7/7 proved. Both JTP1 and JTP2 are sorry-free.

### 4.4.1–4.4.3 q-Binomial Coefficients — Basic Properties

**Manifest chapter**: `ac-q-binomial-coefficients-preamble-basic-p`
**Lean file**: `QBinomialBasic.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.pars.qbinom.intro-count-binom` | PROVED |
| `def.pars.qbinom.qbinom` | PROVED |
| `prop.pars.qbinom.alt-defs` | PROVED |
| `prop.pars.qbinom.0` | PROVED |
| `prop.pars.qbinom.n0` | PROVED |
| `thm.pars.qbinom.rec` | PROVED |
| `thm.pars.qbinom.quot1` | PROVED |
| `def.pars.qbinom.qint` | PROVED |
| `thm.pars.qbinom.quot2` | PROVED |
| `prop.pars.qbinom.symm` | PROVED |

### 4.4.4–4.4.6 q-Binomial Formulas + Subspaces + Limits

**Manifest chapter**: `ac-q-binomial-coefficients-q-binomial-formu`
**Lean file**: `Partitions/QBinomialFormulas.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.pars.qbinom.binom1` | PROVED |
| `lem.prodrule.sum-ai-plus-bi` | PROVED |
| `thm.pars.qbinom.binom2` | PROVED |
| `thm.pars.qbinom.subsp-count` | PROVED |
| `lem.linalg.lin-ind-via-span` | PROVED |
| `lem.pars.qbinom.lin-ind-count` | PROVED |
| `lem.count.multijection` | PROVED |
| `prop.pars.qbinom.lim1` | PROVED |

---

## Chapter 5: Permutations

### 5.1–5.2 Basic Definitions + Transpositions, Cycles, Involutions

**Manifest chapter**: `ac-basic-definitions-transpositions-cycles`
**Lean file**: `Permutations/Basics.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.perm.perm` | PROVED |
| `def.perm.Sn-iven` | PROVED |
| `prop.perm.Sf` | PROVED |
| `def.perm.notations` | PROVED |
| `def.perm.tij` | PROVED |
| `def.perm.si` | PROVED |
| `prop.perm.si.rules` | PROVED |
| `def.perm.cycs` | PROVED |
| `def.perm.invol` | PROVED |

### 5.3.1–5.3.2 Inversions + Lehmer Codes

**Manifest chapter**: `ac-inversions-length-and-lehmer-codes-pream`
**Lean file**: `Permutations/Inversions1.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.perm.invs` | PROVED |
| `prop.perm.lengths-k-small-k` | PROVED |
| `prop.perm.length.gf` | PROVED |
| `def.perm.lehmer1` | PROVED |
| `prop.perm.lehmer.l` | PROVED |
| `thm.perm.lehmer.bij` | PROVED |
| `def.perm.lehmer.lex-ord` | PROVED |
| `prop.perm.lehmer.lex-ord.total` | PROVED |
| `prop.perm.lehmer.lex` | PROVED |

### 5.3.3 More About Lengths and Simples

**Manifest chapter**: `ac-inversions-length-and-lehmer-codes-more`
**Lean file**: `Permutations/Inversions2.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.perm.len.inv` | PROVED |
| `lem.perm.len.ssl` | PROVED |
| `prop.perm.lisitij` | PROVED |
| `thm.perm.len.redword1` | PROVED |
| `cor.perm.red.sigtau` | PROVED |
| `cor.perm.generated` | PROVED |
| `prop.perm.redword-lehmer` | PROVED |

### 5.4 Signs of Permutations

**Manifest chapter**: `ac-signs-of-permutations`
**Lean file**: `Permutations/Signs.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.perm.sign` | PROVED |
| `prop.perm.sign.props` | PROVED |
| `cor.perm.sign.hom` | PROVED |
| `def.perm.even-odd` | PROVED |
| `cor.perm.altgp` | PROVED |
| `cor.perm.num-even` | PROVED |
| `prop.perm.sign.X` | PROVED |

### 5.5 The Cycle Decomposition

**Manifest chapter**: `ac-the-cycle-decomposition`
**Lean file**: `Permutations/CycleDecomposition.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.perm.dcd.main` | PROVED |
| `def.perm.cycs.cycs` | PROVED |
| `prop.perm.cycs.same` | PROVED |
| `prop.perm.cycs.sign` | PROVED |

---

## Chapter 6: Alternating Sums, Signed Counting and Determinants

### 6.1 Cancellations in Alternating Sums

**Manifest chapter**: `ac-cancellations-in-alternating-sums`
**Lean file**: `SignedCounting/AlternatingSums.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.binom.nhs` | PROVED |
| `lem.sign.cancel1` | PROVED |
| `lem.sign.cancel2` | PROVED |
| `lem.sign.cancel3` | PROVED |
| `def.root-of-unity.prim` | PROVED |
| `thm.sign.q-lucas` | PROVED |

> All 6/6 targets proved.

### 6.2.1–6.2.3 Inclusion-Exclusion — Size + Weighted Versions

**Manifest chapter**: `ac-the-principles-of-inclusion-and-exclusio`
**Lean file**: `SignedCounting/InclusionExclusion1.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.pie.1` | PROVED |
| `thm.pie.count-sur` | PROVED |
| `cor.pie.count-sur.cors` | PROVED |
| `def.pie.dera` | PROVED |
| `thm.pie.count-der` | PROVED |
| `thm.pie.euler-tot` | PROVED |
| `thm.pie.2` | PROVED |

### 6.2.4 Boolean Mobius Inversion

**Manifest chapter**: `ac-the-principles-of-inclusion-and-exclusio-28`
**Lean file**: `SignedCounting/BooleanMobiusInversion.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.pie.moeb` | PROVED |
| `lem.pie.two-sets-altsum` | PROVED |

### 6.3 More Subtractive Methods

**Manifest chapter**: `ac-more-subtractive-methods`
**Lean file**: `SignedCounting/SubtractiveMethods.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.cancel.all-even` | PROVED |
| `lem.cancel.all-even.l1` | PROVED |
| `lem.cancel.all-even.l2` | PROVED |

### 6.4.1–6.4.2 Determinants — Definition + Basic Properties

**Manifest chapter**: `ac-determinants-preamble-basic-properties`
**Lean file**: `DeterminantsBasic.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.det.det` | PROVED |
| `prop.det.xiyj` | PROVED |
| `prop.det.xi+yj` | PROVED |
| `thm.det.transp` | PROVED |
| `thm.det.triang` | PROVED |
| `thm.det.rowop` | PROVED |
| `thm.det.colop` | PROVED |
| `cor.det.sig-row-col` | PROVED |
| `thm.det.detAB` | PROVED |
| `cor.det.scale-row-col` | PROVED |

### 6.4.3–6.4.5 Cauchy–Binet + det(A+B) + Factoring

**Manifest chapter**: `ac-determinants-cauchy-binet-factoring-the`
**Lean file**: `CauchyBinet.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `thm.det.CB` | PROVED |
| `def.det.sub` | PROVED |
| `thm.det.det(A+B)` | PROVED |
| `lem.det.minors-diag` | PROVED |
| `thm.det.det(A+D)` | PROVED |
| `prop.det.x+ai` | PROVED |
| `prop.det.charpol-explicit` | PROVED |
| `prop.det.pascal-LU` | PROVED |

> 8/8 proved.

### 6.4.6–6.4.8 Factor Hunting + Laplace + Desnanot–Jacobi

**Manifest chapter**: `ac-determinants-factor-hunting-desnanot-jac`
**Lean file**: `DesnanotJacobi.lean` — **1 sorry**

| Target | Status |
|--------|--------|
| `thm.det.vander` | PROVED |
| `lem.det.vander.a.pol` | PROVED |
| `prop.det.(xi+yj)n-1` | PROVED |
| `thm.det.laplace` | PROVED |
| `prop.det.laplace.0` | PROVED |
| `def.det.adj` | PROVED |
| `thm.det.adj.inverse` | PROVED |
| `thm.det.laplace-multi` | PROVED |
| `thm.det.des-jac-1` | PROVED |
| `thm.det.des-jac-2` | PROVED |
| `thm.det.cauchy` | **EXERCISE** |
| `thm.det.jacobi-complement` | PROVED |

> 11/12 proved (+ 1 EXERCISE).
>
> `thm.det.des-jac-1` and `thm.det.des-jac-2` are both **PROVED** — the generalized
> Desnanot-Jacobi identity `desnanot_jacobi_direct` is sorry-free via the MvPolynomial
> + FractionRing approach.
>
> `thm.det.cauchy` remains EXERCISE, blocked by `desnanot_jacobi_cauchy_identity_gen`
> (sorry at line 8697) for n >= 5 — the `ring` tactic times out on the polynomial identity.
> Issue: `d1e5a002`.

### 6.5.1–6.5.5 LGV Lemma — Definitions + k Paths

**Manifest chapter**: `ac-the-lindstrom-gessel-viennot-lemma-pream`
**Lean file**: `Determinants/LGV1.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.lgv.lattice` | PROVED |
| `prop.lgv.1-paths.ct` | PROVED |
| `def.lgv.path-tups` | PROVED |
| `prop.lgv.2paths.count` | PROVED |
| `prop.lgv.jordan-2` | PROVED |
| `cor.lgv.binom-unimod` | PROVED |
| `prop.lgv.kpaths.count` | PROVED |

### 6.5.6–6.5.8 LGV — Weighted + Nonpermutable

**Manifest chapter**: `ac-the-lindstrom-gessel-viennot-lemma-the-w`
**Lean file**: `Determinants/LGV2.lean` — **1 sorry**

| Target | Status |
|--------|--------|
| `thm.lgv.kpaths.wt` | PROVED |
| `thm.lgv.kpaths.wt-dg` | PROVED |
| `cor.lgv.kpaths.wt-np` | PROVED |
| `cor.lgv.binom-det-nonneg` | PROVED |
| `cor.lgv.catalan-hankel-det-0` | **EXERCISE** |

> 4/5 proved (+ 1 EXERCISE).

---

## Chapter 7: Symmetric Functions

### 7.1 Definitions and Examples of Symmetric Polynomials

**Manifest chapter**: `ac-definitions-and-examples-of-symmetric`
**Lean file**: `SymmetricFunctions/Definitions.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.sf.PS` | PROVED |
| `prop.sf.SN-acts` | PROVED |
| `prop.sf.SN-acts-by-alg-auts` | PROVED |
| `thm.sf.S-subalg` | PROVED |
| `def.sf.ring-of-symm` | PROVED |
| `def.sf.monomial` | PROVED |
| `def.sf.ehp` | PROVED |
| `prop.sf.en=0` | PROVED |
| `thm.sf.NG` | PROVED |
| `prop.sf.e-h-FPS` | PROVED |
| `thm.sf.ftsf` | PROVED |
| `lem.sf.simples-enough` | PROVED |

### 7.2 N-Partitions and Monomial Symmetric Polynomials

**Manifest chapter**: `ac-n-partitions-and-monomial-symmetric-poly`
**Lean file**: `SymmetricFunctions/MonomialSymmetric.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.sf.Npar` | PROVED |
| `prop.sf.Npar-as-par` | PROVED |
| `def.sf.sort` | PROVED |
| `def.sf.m` | PROVED |
| `prop.sf.ehp-through-m` | PROVED |
| `thm.sf.m-basis` | PROVED |
| `prop.sf.sigma-pol-coeff` | PROVED |

### 7.3.1–7.3.3 Schur Polynomials — Basics + Skew

**Manifest chapter**: `ac-schur-polynomials-preamble-skew-young-di`
**Lean file**: `SymmetricFunctions/SchurBasics.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.sf.alternants` | PROVED |
| `def.sf.ydiag` | PROVED |
| `def.sf.ytab` | PROVED |
| `def.sf.ssyt` | PROVED |
| `def.sf.ytab.xT` | PROVED |
| `def.sf.schur` | PROVED |
| `thm.sf.schur-symm` | PROVED |
| `def.sf.par-subset` | PROVED |
| `def.sf.skew-diag` | PROVED |
| `lem.sf.skew-diag.convexity` | PROVED |
| `def.sf.skew-tab` | PROVED |
| `def.sf.skew-ssyt` | PROVED |
| `lem.sf.skew-ssyt.increase` | PROVED |
| `def.sf.ytab.skew-xT` | PROVED |
| `def.sf.skew-schur` | PROVED |
| `thm.sf.skew-schur-symm` | PROVED |

> 16/16 proved. `schur-symm` and `skew-schur-symm` are now **PROVED** —
> `benderKnuth_involutive_partition` (LR:5440) is sorry-free. SchurBasics.lean has 0
> actual `sorry` tactics, and the transitive dependency through LittlewoodRichardson.lean's
> BK involution is now clean.

### 7.3.5 The Littlewood-Richardson Rule

**Manifest chapter**: `ac-schur-polynomials-the-littlewood-richard`
**Lean file**: `SymmetricFunctions/LittlewoodRichardson.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.sf.tuple-addition` | PROVED |
| `def.sf.content` | PROVED |
| `def.sf.col-tab` | PROVED |
| `def.sf.yamanouchi` | PROVED |
| `thm.sf.lr-zy` | PROVED |
| `lem.sf.stemb-lem` | PROVED |
| `lem.sf.tab-greater-i` | PROVED |
| `def.cring.reg` | PROVED |
| `lem.cring.reg.cancel` | PROVED |
| `lem.sf.arho-reg` | PROVED |
| `lem.sf.alternant-0` | PROVED |

> 11/11 proved. The Littlewood-Richardson rule and Stembridge's lemma are fully
> sorry-free. All BK involution infrastructure, Stembridge involution, and content
> transposition are proved. Old `benderKnuthPrefix` dead code has been deleted.

### 7.3.6–7.3.7 Pieri Rules + Jacobi–Trudi

**Manifest chapter**: `ac-schur-polynomials-the-pieri-rules-the-ja`
**Lean file**: `SymmetricFunctions/PieriJacobiTrudi.lean` — **3 sorries**

| Target | Status |
|--------|--------|
| `def.sf.strips` | PROVED |
| `prop.sf.strips.entries` | PROVED |
| `thm.sf.pieri` | **EXERCISE** |
| `thm.sf.jt-h` | PROVED |
| `thm.sf.jt-e` | **EXERCISE** |

> 3/5 proved (+ 2 EXERCISE).
> `jt-h` is fully PROVED — all LGV infrastructure is sorry-free.
> `jt-e` is an EXERCISE in the TeX source (`exe.sf.jt-e`, 6-point, no hint).

#### Remaining 3 sorries (all exercise-level)

| Sorry | Line | Function | Notes |
|-------|------|----------|-------|
| 1 | 2987 | `pieri_horizontal` | EXERCISE (`exe.sf.pieri`). Needs RSK row insertion |
| 2 | 3067 | `pieri_vertical` | EXERCISE (`exe.sf.pieri`). Needs RSK column insertion |
| 3 | 3175 | `jacobiTrudi_e` | EXERCISE (`exe.sf.jt-e`). Mark as `sorry -- [exercise]` |

---

## Appendix B: Omitted Details and Proofs

### B.2 Infinite Products (Part 1)

**Manifest chapter**: `ac-details-infinite-products-part-1-part-2`
**Lean file**: `FPS/InfiniteProducts1.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `lem.fps.prod.irlv.cong-div` | PROVED |
| `lem.fps.prods-mulable-subfams-appr` | PROVED |
| `lem.fps.prods-mulable-rules.SW1.lem1` | PROVED |

### B.2 Infinite Products (Part 2)

**Manifest chapter**: `ac-details-infinite-products-part-2-part-2`
**Lean file**: `Details/InfiniteProducts2.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `lem.fps.subs.rule-infprod-fin` | PROVED |

### B.3 Domino Tilings

**Manifest chapter**: `ac-details-domino-tilings`
**Lean file**: `Details/DominoTilings.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `def.gf.weighted-set.domino.Rn3.ABC` | PROVED |
| `prop.gf.weighted-set.domino.Rn3.ABC` | PROVED |

### B.4 Limits of FPSs

**Manifest chapter**: `ac-details-limits-of-fpss`
**Lean file**: `Details/Limits.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `prop.fps.lim.sum-prod.K` | PROVED |
| `prop.fps.lim.sum-prod.L` | PROVED |

### B.5 Laurent Power Series

**Manifest chapter**: `ac-details-laurent-power-series`
**Lean file**: `FPS/LaurentSeries.lean` — **0 sorries**

| Target | Status |
|--------|--------|
| `lem.fps.laure.xa` | PROVED |
| `prop.fps.laure.xk` | PROVED |

---

## File-Level Sorry Census

| File | Sorries | Key declarations with sorry |
|------|--------:|-----|
| `PieriJacobiTrudi.lean` | 3 | `pieri_horizontal` (2620), `pieri_vertical` (2635), `jacobiTrudi_e` (2693) — all exercise |
| `DesnanotJacobi.lean` | 1 | `desnanot_jacobi_cauchy_identity_gen` (8525, exercise) |
| `Determinants/LGV2.lean` | 1 | Catalan-Hankel det (6081, exercise) |
| 48 files with 0 sorries | 0 | |
| **TOTAL** | **5** | |

All 5 sorries are tagged `-- [exercise]` and serve the 4 exercise targets listed above.

---

## Remaining Open Issues

### Exercise cleanup

**Issue `cleanup-pieri`** (2 sorries): Delete ~500 lines of dead Pieri infrastructure
and strip partial proof attempts.

**Issue `cleanup-jt-e`** (1 sorry): Delete ~30 lines of dead jt-e infrastructure.

**Issue `cleanup-catalan`** (1 sorry): Delete `discrete_ivt_even_step2` (~20 lines).

**Issue `cleanup-cauchy`** (1 sorry): Delete ~230 lines of dead `genDenomPoly9/10`
infrastructure.
