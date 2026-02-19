/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.FPS.Limits

/-!
# Detailed Proofs: Limits of Formal Power Series

This file contains detailed proofs for the theorems about limits of formal power series,
following Section `sec.details.gf.lim` (Section 7.5 Details) of the source material.

The main theorems are stated in `AlgebraicCombinatorics.FPS.Limits`. This file provides
the detailed proof arguments that follow the structure of the TeX source closely.

## Main Results

The detailed proofs cover:

* `lem.fps.lim.xn-equiv` (Lemma 7.5.4): If `f_i → f`, then for each `n`, eventually
  `f_i ≡ f (mod x^{n+1})`.
* `prop.fps.lim.sum-prod` (Proposition 7.5.5): Limits respect addition and multiplication.
* `prop.fps.lim.sum-quot` (Proposition 7.5.6): Limits respect division (when denominators
  are invertible).
  - Includes Claim 1: The limit `g` is invertible if all `g_i` are invertible.
* `thm.fps.lim.sum-lim` (Theorem 7.5.9): Infinite sum is the limit of partial sums.
* `thm.fps.lim.prod-lim` (Theorem 7.5.10): Infinite product is the limit of partial products.
* `cor.fps.lim.fps-as-pol` (Corollary 7.5.11): Each FPS is a limit of polynomials.
* `thm.fps.lim.sum-lim-conv` (Theorem 7.5.12): Converse - if partial sums converge,
  family is summable.
* `thm.fps.lim.prod-lim-conv` (Theorem 7.5.13): Converse - if partial products converge,
  family is multipliable.

## References

* Source: `AlgebraicCombinatorics/tex/Details/Limits.tex`
* Main theorems: `AlgebraicCombinatorics/FPS/Limits.lean`
-/

open scoped Polynomial

namespace Seq

variable {K : Type*}

/-!
### Detailed Proofs for Sequence Stabilization

These lemmas provide the foundational facts about sequence stabilization.
-/

/-- If a sequence stabilizes to a limit, that limit is unique.
(Used in the proof of Lemma `lem.fps.lim.xn-equiv`) -/
theorem stabilizesTo_unique' {a : ℕ → K} {lim₁ lim₂ : K}
    (h₁ : StabilizesTo a lim₁) (h₂ : StabilizesTo a lim₂) : lim₁ = lim₂ := by
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  -- Take any index ≥ max N₁ N₂
  let N := max N₁ N₂
  have h1 : a N = lim₁ := hN₁ N (le_max_left N₁ N₂)
  have h2 : a N = lim₂ := hN₂ N (le_max_right N₁ N₂)
  rw [← h1, h2]

end Seq

namespace PowerSeries

variable {K : Type*} [CommRing K]

/-!
### x^n-Equivalence Properties

The key property used in all the limit proofs is that x^n-equivalence is preserved
by arithmetic operations.
-/

/-!
x^n-equivalence is compatible with division (when denominators are invertible).
(Theorem `thm.fps.xneq.props` (e), used in `prop.fps.lim.sum-quot`)

This is a key lemma: if `f₁ ≡[x^n] f₂` and `g₁ ≡[x^n] g₂` with `g₁, g₂` invertible,
then `f₁/g₁ ≡[x^n] f₂/g₂`.

This is already proved as `xnEquiv_div` in `AlgebraicCombinatorics.FPS.Limits`.
-/

/-!
### Detailed Proof of Lemma `lem.fps.lim.xn-equiv`

**Statement:** If `lim_{i→∞} f_i = f`, then for each `n ∈ ℕ`, there exists `N ∈ ℕ`
such that all integers `i ≥ N` satisfy `f_i ≡[x^n] f`.

**Proof idea:**
1. By definition of coefficientwise stabilization, for each `k ∈ ℕ`, the sequence
   `([x^k] f_i)_{i ∈ ℕ}` stabilizes to `[x^k] f`.
2. For each `k ∈ {0, 1, ..., n}`, let `N_k` be the stabilization index.
3. Set `P = max{N_0, N_1, ..., N_n}`.
4. For any `i ≥ P`, we have `i ≥ N_k` for all `k ≤ n`, so `[x^k] f_i = [x^k] f`.
5. This means `f_i ≡[x^n] f`.

This is already proved as `exists_xnEquiv_of_coeffStabilizesTo` in the main file.
-/

/-!
### Detailed Proof of Proposition `prop.fps.lim.sum-prod`

**Statement:** If `lim_{i→∞} f_i = f` and `lim_{i→∞} g_i = g`, then:
- `lim_{i→∞} (f_i + g_i) = f + g`
- `lim_{i→∞} (f_i * g_i) = f * g`

**Proof idea for addition:**
1. By Lemma `lem.fps.lim.xn-equiv`, for each `n`, eventually `f_i ≡[x^n] f` and `g_i ≡[x^n] g`.
2. By the additivity of x^n-equivalence, eventually `f_i + g_i ≡[x^n] f + g`.
3. In particular, eventually `[x^n](f_i + g_i) = [x^n](f + g)`.
4. This holds for all `n`, so `(f_i + g_i)` coefficientwise stabilizes to `f + g`.

**Proof idea for multiplication:**
1. By Lemma `lem.fps.lim.xn-equiv`, for each `n`, eventually `f_i ≡[x^n] f` and `g_i ≡[x^n] g`.
2. By the multiplicativity of x^n-equivalence, eventually `f_i * g_i ≡[x^n] f * g`.
3. In particular, eventually `[x^n](f_i * g_i) = [x^n](f * g)`.
4. This holds for all `n`, so `(f_i * g_i)` coefficientwise stabilizes to `f * g`.
-/

/-- **Intermediate result K for prop.fps.lim.sum-prod**
(Label: prop.fps.lim.sum-prod.K)

If `lim_{i→∞} f_i = f`, then for each `n ∈ ℕ`, there exists `K ∈ ℕ` such that
all integers `i ≥ K` satisfy `f_i ≡[x^n] f`.

This is the first intermediate step in the detailed proof of Proposition `prop.fps.lim.sum-prod`.
It follows directly from Lemma `lem.fps.lim.xn-equiv` (i.e., `exists_xnEquiv_of_coeffStabilizesTo`).

The proof proceeds as follows:
1. By definition of coefficientwise stabilization, for each `k ∈ ℕ`, the sequence
   `([x^k] f_i)_{i ∈ ℕ}` stabilizes to `[x^k] f`.
2. For each `k ∈ {0, 1, ..., n}`, let `N_k` be the stabilization index.
3. Set `K = max{N_0, N_1, ..., N_n}`.
4. For any `i ≥ K`, we have `i ≥ N_k` for all `k ≤ n`, so `[x^k] f_i = [x^k] f`.
5. This means `f_i ≡[x^n] f`.

This result is used together with `prop.fps.lim.sum-prod.L` (the analogous statement for `g_i → g`)
to prove the main proposition. -/
theorem exists_xnEquiv_K
    {f : ℕ → PowerSeries K} {lf : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (n : ℕ) :
    ∃ K : ℕ, ∀ i ≥ K, f i ≡[x^n] lf :=
  exists_xnEquiv_of_coeffStabilizesTo hf n

/-- **Intermediate result L for prop.fps.lim.sum-prod**
(Label: prop.fps.lim.sum-prod.L)

If `lim_{i→∞} g_i = g`, then for each `n ∈ ℕ`, there exists `L ∈ ℕ` such that
all integers `i ≥ L` satisfy `g_i ≡[x^n] g`.

This is the second intermediate step in the detailed proof of Proposition `prop.fps.lim.sum-prod`.
It is the exact same statement as `prop.fps.lim.sum-prod.K`, but applied to the sequence `(g_i)`.

Together with `prop.fps.lim.sum-prod.K`, this allows us to set `P = max{K, L}` and conclude
that for all `i ≥ P`, both `f_i ≡[x^n] f` and `g_i ≡[x^n] g` hold simultaneously. -/
theorem exists_xnEquiv_L
    {g : ℕ → PowerSeries K} {lg : PowerSeries K}
    (hg : CoeffStabilizesTo g lg) (n : ℕ) :
    ∃ L : ℕ, ∀ i ≥ L, g i ≡[x^n] lg :=
  exists_xnEquiv_of_coeffStabilizesTo hg n

/-- **Combined intermediate result for prop.fps.lim.sum-prod**

Combining `prop.fps.lim.sum-prod.K` and `prop.fps.lim.sum-prod.L`: if `f_i → f` and `g_i → g`,
then for each `n ∈ ℕ`, there exists `P ∈ ℕ` such that for all `i ≥ P`:
- `f_i ≡[x^n] f`
- `g_i ≡[x^n] g`

This is the key step that allows us to apply the compatibility of x^n-equivalence with
arithmetic operations. -/
theorem exists_xnEquiv_both
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) (n : ℕ) :
    ∃ P : ℕ, ∀ i ≥ P, (f i ≡[x^n] lf) ∧ (g i ≡[x^n] lg) := by
  obtain ⟨K, hK⟩ := exists_xnEquiv_K hf n
  obtain ⟨L, hL⟩ := exists_xnEquiv_L hg n
  use max K L
  intro i hi
  exact ⟨hK i (le_of_max_le_left hi), hL i (le_of_max_le_right hi)⟩

/-- Limits respect addition - detailed proof.
(Proposition `prop.fps.lim.sum-prod`, label: prop.fps.lim.sum-prod)

The same argument as for multiplication, but using the additivity of x^n-equivalence. -/
theorem coeffStabilizesTo_add'
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) :
    CoeffStabilizesTo (fun i => f i + g i) (lf + lg) := by
  intro n
  -- Step 1: Get stabilization bounds for x^n-equivalence
  obtain ⟨K_f, hK_f⟩ := exists_xnEquiv_of_coeffStabilizesTo hf n
  obtain ⟨K_g, hK_g⟩ := exists_xnEquiv_of_coeffStabilizesTo hg n
  -- Step 2: Take P = max{K_f, K_g}
  let P := max K_f K_g
  use P
  intro i hi
  -- Step 3: For i ≥ P, we have f_i ≡[x^n] lf and g_i ≡[x^n] lg
  have hf_equiv : xnEquiv n (f i) lf := hK_f i (le_of_max_le_left hi)
  have hg_equiv : xnEquiv n (g i) lg := hK_g i (le_of_max_le_right hi)
  -- Step 4: By additivity, f_i + g_i ≡[x^n] lf + lg
  have h_sum := xnEquiv_add hf_equiv hg_equiv
  -- Step 5: Extract the n-th coefficient equality
  exact h_sum n (le_refl n)

/-- Limits respect multiplication - detailed proof.
(Proposition `prop.fps.lim.sum-prod`, label: prop.fps.lim.sum-prod) -/
theorem coeffStabilizesTo_mul'
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) :
    CoeffStabilizesTo (fun i => f i * g i) (lf * lg) := by
  intro n
  -- Step 1: Get stabilization bounds for x^n-equivalence
  obtain ⟨K_f, hK_f⟩ := exists_xnEquiv_of_coeffStabilizesTo hf n
  obtain ⟨K_g, hK_g⟩ := exists_xnEquiv_of_coeffStabilizesTo hg n
  -- Step 2: Take P = max{K_f, K_g}
  let P := max K_f K_g
  use P
  intro i hi
  -- Step 3: For i ≥ P, we have f_i ≡[x^n] lf and g_i ≡[x^n] lg
  have hf_equiv : xnEquiv n (f i) lf := hK_f i (le_of_max_le_left hi)
  have hg_equiv : xnEquiv n (g i) lg := hK_g i (le_of_max_le_right hi)
  -- Step 4: By multiplicativity, f_i * g_i ≡[x^n] lf * lg
  have h_prod := xnEquiv_mul hf_equiv hg_equiv
  -- Step 5: Extract the n-th coefficient equality
  exact h_prod n (le_refl n)

/-!
### Detailed Proof of Proposition `prop.fps.lim.sum-quot`

**Statement:** If `lim_{i→∞} f_i = f`, `lim_{i→∞} g_i = g`, and each `g_i` is invertible,
then `g` is invertible and `lim_{i→∞} (f_i / g_i) = f / g`.

**Proof idea:**

*Claim 1: g is invertible.*
1. The sequence `([x^0] g_i)` stabilizes to `[x^0] g`.
2. For large enough `i`, `[x^0] g_i = [x^0] g`.
3. Since `g_i` is invertible, `[x^0] g_i` is a unit in `K`.
4. Therefore `[x^0] g` is a unit, so `g` is invertible.

*Main proof:*
1. By Lemma `lem.fps.lim.xn-equiv`, eventually `f_i ≡[x^n] f` and `g_i ≡[x^n] g`.
2. By Theorem `thm.fps.xneq.props` (e), eventually `f_i/g_i ≡[x^n] f/g`.
3. In particular, eventually `[x^n](f_i/g_i) = [x^n](f/g)`.

Note: Claim 1 is already proved as `isUnit_constantCoeff_of_coeffStabilizesTo` in the main file.
-/

/-!
### Detailed Proof of Theorem `thm.fps.lim.sum-lim`

**Statement:** If the family `(f_n)_{n ∈ ℕ}` is summable, then
`lim_{i→∞} ∑_{n=0}^{i} f_n = ∑_{n ∈ ℕ} f_n`.

**Proof idea:**
1. Define `g_i = ∑_{k=0}^{i} f_k` and `g = ∑_{k ∈ ℕ} f_k`.
2. Fix `n ∈ ℕ`. By summability, only finitely many `k` have `[x^n] f_k ≠ 0`.
3. Let `m` be an upper bound for these `k`.
4. For `i ≥ m`, we have `[x^n] g_i = ∑_{k=0}^{i} [x^n] f_k = ∑_{k=0}^{m} [x^n] f_k`
   (since `[x^n] f_k = 0` for `k > m`).
5. Similarly, `[x^n] g = ∑_{k ∈ ℕ} [x^n] f_k = ∑_{k=0}^{m} [x^n] f_k`.
6. Therefore `[x^n] g_i = [x^n] g` for `i ≥ m`.
-/

/-- Infinite sum is the limit of partial sums - detailed proof.
(Theorem `thm.fps.lim.sum-lim`, label: thm.fps.lim.sum-lim)

The proof follows the tex source structure:
1. Define `g_i = ∑_{k=0}^{i} f_k` and `g = ∑_{k ∈ ℕ} f_k`.
2. Fix `n ∈ ℕ`. By summability, only finitely many `k` have `[x^n] f_k ≠ 0`.
3. Let `J` be this finite set, with upper bound `m`.
4. For `i ≥ m`:
   - `[x^n] g = ∑_{k ∈ ℕ} [x^n] f_k = ∑_{k=0}^{i} [x^n] f_k` (since terms for `k > m` are 0)
   - `[x^n] g_i = ∑_{k=0}^{i} [x^n] f_k`
5. Therefore `[x^n] g_i = [x^n] g` for `i ≥ m`.
-/
theorem coeffStabilizesTo_partial_sum'
    {f : ℕ → PowerSeries K} (hf : IsSummable f) :
    CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) (tsum' f hf) :=
  coeffStabilizesTo_partial_sum hf

/-!
### Detailed Proof of Theorem `thm.fps.lim.prod-lim`

**Statement:** If the family `(f_n)_{n ∈ ℕ}` is multipliable, then
`lim_{i→∞} ∏_{n=0}^{i} f_n = ∏_{n ∈ ℕ} f_n`.

**Proof idea:**
1. Define `g_i = ∏_{k=0}^{i} f_k` and `g = ∏_{k ∈ ℕ} f_k`.
2. Fix `n ∈ ℕ`. By multipliability, the x^n-coefficient is finitely determined.
3. Let `M` be a finite subset that determines this coefficient, with upper bound `m`.
4. For `i ≥ m`, we have `M ⊆ {0, 1, ..., i}`, so
   `[x^n](∏_{k ∈ {0,...,i}} f_k) = [x^n](∏_{k ∈ M} f_k)`.
5. By definition of the infinite product, `[x^n] g = [x^n](∏_{k ∈ M} f_k)`.
6. Therefore `[x^n] g_i = [x^n] g` for `i ≥ m`.
-/

/-- Infinite product is the limit of partial products - detailed proof.
(Theorem `thm.fps.lim.prod-lim`, label: thm.fps.lim.prod-lim)

The proof follows the tex source structure:
1. Define `g_i = ∏_{k=0}^{i} f_k` and `g = ∏_{k ∈ ℕ} f_k`.
2. Fix `n ∈ ℕ`. By multipliability, the x^n-coefficient is finitely determined.
3. Let `M` be a finite subset that determines this coefficient, with upper bound `m`.
4. For `i ≥ m`, we have `M ⊆ {0, 1, ..., i}`, so
   `[x^n](∏_{k ∈ {0,...,i}} f_k) = [x^n](∏_{k ∈ M} f_k)`.
5. By definition of the infinite product, `[x^n] g = [x^n](∏_{k ∈ M} f_k)`.
6. Therefore `[x^n] g_i = [x^n] g` for `i ≥ m`.
-/
theorem coeffStabilizesTo_partial_prod'
    {f : ℕ → PowerSeries K} (hf : IsMultipliable f) :
    CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) (tprod' f hf) :=
  coeffStabilizesTo_partial_prod hf

/-!
### Detailed Proof of Corollary `cor.fps.lim.fps-as-pol`

**Statement:** Any FPS `a = ∑_{n ∈ ℕ} a_n x^n` satisfies
`a = lim_{i→∞} ∑_{n=0}^{i} a_n x^n`.

**Proof idea:**
1. The family `(a_n x^n)_{n ∈ ℕ}` is summable (by Corollary `cor.fps.sumakxk`).
2. By Theorem `thm.fps.lim.sum-lim`, `lim_{i→∞} ∑_{n=0}^{i} a_n x^n = ∑_{n ∈ ℕ} a_n x^n = a`.

This is already proved as `coeffStabilizesTo_trunc` in the main file.
-/

/-!
### Detailed Proof of Theorem `thm.fps.lim.sum-lim-conv`

**Statement:** If the limit `lim_{i→∞} ∑_{n=0}^{i} f_n` exists, then the family
`(f_n)_{n ∈ ℕ}` is summable and the limit equals `∑_{n ∈ ℕ} f_n`.

**Proof idea:**
1. Let `g = lim_{i→∞} g_i` where `g_i = ∑_{k=0}^{i} f_k`.
2. Fix `n ∈ ℕ`. The sequence `([x^n] g_i)` stabilizes to `[x^n] g`.
3. Let `N` be the stabilization index. Set `M = {0, 1, ..., N}`.
4. For `i ∈ ℕ \ M` (i.e., `i > N`), we have:
   - `[x^n] g_i = [x^n] g` and `[x^n] g_{i-1} = [x^n] g`
   - Since `g_i = f_i + g_{i-1}`, we get `[x^n] f_i = 0`.
5. Therefore all but finitely many `k` have `[x^n] f_k = 0`.
6. This holds for all `n`, so `(f_n)` is summable.
-/

/-- If partial sums converge, the family is summable - detailed proof.
(Theorem `thm.fps.lim.sum-lim-conv`, label: thm.fps.lim.sum-lim-conv)

The proof follows the tex source structure:
1. Let `g = lim_{i→∞} g_i` where `g_i = ∑_{k=0}^{i} f_k`.
2. Fix `n ∈ ℕ`. The sequence `([x^n] g_i)` stabilizes to `[x^n] g`.
3. Let `N` be the stabilization index. Set `M = {0, 1, ..., N}`.
4. For `i ∈ ℕ \ M` (i.e., `i > N`), we have:
   - `[x^n] g_i = [x^n] g` and `[x^n] g_{i-1} = [x^n] g`
   - Since `g_i = f_i + g_{i-1}`, we get `[x^n] g_i = [x^n] f_i + [x^n] g_{i-1}`
   - Therefore `[x^n] f_i = 0`.
5. All but finitely many `k` have `[x^n] f_k = 0`.
6. This holds for all `n`, so `(f_n)` is summable.
-/
theorem isSummable_of_coeffStabilizesTo_partial_sum'
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) lim) :
    IsSummable f :=
  isSummable_of_coeffStabilizesTo_partial_sum h

/-- If partial sums converge, the limit equals the infinite sum - detailed proof.
(Theorem `thm.fps.lim.sum-lim-conv`, label: thm.fps.lim.sum-lim-conv)

Once we know the family is summable, we can apply Theorem `thm.fps.lim.sum-lim`
to conclude that the partial sums converge to the infinite sum.
Since limits are unique, the limit must equal the infinite sum.
-/
theorem tsum'_eq_of_coeffStabilizesTo_partial_sum'
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) lim)
    (hsum : IsSummable f) :
    tsum' f hsum = lim :=
  tsum'_eq_of_coeffStabilizesTo_partial_sum h

/-!
### Detailed Proof of Theorem `thm.fps.lim.prod-lim-conv`

**Statement:** If the limit `lim_{i→∞} ∏_{n=0}^{i} f_n` exists and each `f_n` has
constant term 1, then the family `(f_n)_{n ∈ ℕ}` is multipliable and the limit
equals `∏_{n ∈ ℕ} f_n`.

**Proof idea:**
1. Let `g = lim_{i→∞} g_i` where `g_i = ∏_{k=0}^{i} f_k`.
2. Fix `n ∈ ℕ`. By Lemma `lem.fps.lim.xn-equiv`, there exists `N` such that
   `g_i ≡[x^n] g` for all `i ≥ N`.
3. Set `M = {0, 1, ..., N}`.
4. *Claim 1:* For each integer `j > N`, we have `g ≡[x^n] g * f_j`.
   - Since `g_{j-1} ≡[x^n] g` and `g_j ≡[x^n] g` and `g_j = g_{j-1} * f_j`,
     we get `g ≡[x^n] g * f_j`.
5. *Claim 2:* For any finite `U ⊇ M`, we have `g ≡[x^n] ∏_{k ∈ U} f_k`.
   - By induction on `|U \ M|`.
6. For any finite `J ⊇ M`, we have `[x^n](∏_{k ∈ J} f_k) = [x^n](∏_{k ∈ M} f_k)`.
7. This shows `M` determines the x^n-coefficient.
-/

/-- If partial products converge, the family is multipliable - detailed proof.
(Theorem `thm.fps.lim.prod-lim-conv`, label: thm.fps.lim.prod-lim-conv)

The proof follows the tex source structure:
1. Let `g = lim_{i→∞} g_i` where `g_i = ∏_{k=0}^{i} f_k`.
2. Fix `n ∈ ℕ`. By Lemma `lem.fps.lim.xn-equiv`, there exists `N` such that
   `g_i ≡[x^n] g` for all `i ≥ N`.
3. Set `M = {0, 1, ..., N}`.

**Claim 1:** For each integer `j > N`, we have `g ≡[x^n] g * f_j`.
- Since `g_{j-1} ≡[x^n] g` and `g_j ≡[x^n] g` and `g_j = g_{j-1} * f_j`,
  by multiplicativity of x^n-equivalence: `g_{j-1} * f_j ≡[x^n] g * f_j`.
  Thus `g_j ≡[x^n] g * f_j`, and since `g ≡[x^n] g_j`, we get `g ≡[x^n] g * f_j`.

**Claim 2:** For any finite `U ⊇ M`, we have `g ≡[x^n] ∏_{k ∈ U} f_k`.
- By induction on `|U \ M|`:
  - Base case: `U = M`, so `∏_{k ∈ U} f_k = g_N ≡[x^n] g`.
  - Inductive step: If `U ⊃ M`, pick `u ∈ U \ M` (so `u > N`).
    By IH, `g ≡[x^n] ∏_{k ∈ U \ {u}} f_k`.
    By Claim 1, `g ≡[x^n] g * f_u`.
    Combining: `g * f_u ≡[x^n] (∏_{k ∈ U \ {u}} f_k) * f_u = ∏_{k ∈ U} f_k`.
    By transitivity, `g ≡[x^n] ∏_{k ∈ U} f_k`.

4. For any finite `J ⊇ M`, we have `[x^n](∏_{k ∈ J} f_k) = [x^n](∏_{k ∈ M} f_k)`.
5. This shows `M` determines the x^n-coefficient.
-/
theorem isMultipliable_of_coeffStabilizesTo_partial_prod'
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim)
    (hconst : ∀ i, constantCoeff (f i) = 1) :
    IsMultipliable f :=
  isMultipliable_of_coeffStabilizesTo_partial_prod h hconst

/-- If partial products converge, the limit equals the infinite product.
(Theorem `thm.fps.lim.prod-lim-conv`, label: thm.fps.lim.prod-lim-conv)

Once we know the family is multipliable, we can apply Theorem `thm.fps.lim.prod-lim`
to conclude that the partial products converge to the infinite product.
Since limits are unique, the limit must equal the infinite product.
-/
theorem tprod'_eq_of_coeffStabilizesTo_partial_prod'
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim)
    (hmult : IsMultipliable f) :
    tprod' f hmult = lim :=
  tprod'_eq_of_coeffStabilizesTo_partial_prod h (hmult.1)

end PowerSeries
