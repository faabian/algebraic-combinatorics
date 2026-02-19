/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib

/-!
# More Subtractive Methods

This file formalizes Section `sec.cancel.moresub` on more subtractive methods
in combinatorics, focusing on the technique of summing with varying signs to
achieve cancellation.

## Main definitions

* `IsAllEven`: An n-tuple `x : Fin n → Fin d` is "all-even" if each element
  of `Fin d` occurs an even number of times in the tuple.
* `signProduct`: The product `e_{x_1} * e_{x_2} * ... * e_{x_n}` for a sign tuple `e`
  and index tuple `x`.
* `signSum`: The sum of entries of a sign tuple, as an integer.
* `allEvenTuples`: The set of all-even tuples in `(Fin n → Fin d)`.
* `signTupleEquivSubset`: Equivalence between sign tuples and subsets of `[d]`.

## Main results

* `sum_signSum_pow_eq_sum_signProduct`: Sum interchange identity (Lemma `lem.cancel.all-even.l1`).
* `sum_signProduct_not_allEven`: If an n-tuple is not all-even, then the sum
  `∑_{e ∈ {1,-1}^d} ∏_i e_{x_i}` equals 0 (Lemma `lem.cancel.all-even.l2(a)`).
* `sum_signProduct_allEven`: If an n-tuple is all-even, then the sum
  `∑_{e ∈ {1,-1}^d} ∏_i e_{x_i}` equals 2^d (Lemma `lem.cancel.all-even.l2(b)`).
* `allEven_count_formula`: The number of all-even n-tuples in `[d]^n` equals
  `(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n` (Theorem `thm.cancel.all-even`).
* `sum_choose_pow_dvd_pow_two`: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is divisible by `2^d`.
* `sum_choose_pow_nonneg`: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative.

## References

* Source: `AlgebraicCombinatorics/tex/SignedCounting/SubtractiveMethods.tex`
-/

open Finset BigOperators

namespace AlgebraicCombinatorics.SubtractiveMethods

/-! ### The all-even property

An n-tuple `(x₁, x₂, ..., xₙ) ∈ [d]ⁿ` is called "all-even" if each element
of `[d]` occurs an even number of times in the tuple.
-/

/-- An n-tuple `x : Fin n → Fin d` is "all-even" if each element of `Fin d`
occurs an even number of times. For example, the 4-tuple `(1,4,4,1)` is all-even
since 1 appears twice and 4 appears twice.

Label: Definition from Theorem `thm.cancel.all-even` -/
def IsAllEven {n d : ℕ} (x : Fin n → Fin d) : Prop :=
  ∀ k : Fin d, Even ((univ.filter fun i => x i = k).card)

/-- The multiplicity of element `k` in tuple `x` -/
def multiplicity {n d : ℕ} (x : Fin n → Fin d) (k : Fin d) : ℕ :=
  (univ.filter fun i => x i = k).card

/-- A tuple is all-even iff all multiplicities are even -/
theorem isAllEven_iff_multiplicity {n d : ℕ} (x : Fin n → Fin d) :
    IsAllEven x ↔ ∀ k : Fin d, Even (multiplicity x k) := by
  rfl

instance {n d : ℕ} (x : Fin n → Fin d) : Decidable (IsAllEven x) :=
  inferInstanceAs (Decidable (∀ k : Fin d, Even ((univ.filter fun i => x i = k).card)))

/-! ### Sign tuples

We represent sign tuples as functions `e : Fin d → ZMod 2`, where
`0` represents `+1` and `1` represents `-1`. This gives us a natural
finite type structure. We then convert to ℤ when needed.
-/

/-- Convert a ZMod 2 value to a sign: 0 ↦ 1, 1 ↦ -1 -/
def toSign (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

@[simp]
theorem toSign_zero : toSign 0 = 1 := rfl

@[simp]
theorem toSign_one : toSign 1 = -1 := rfl

/-- The product `e_{x_1} * e_{x_2} * ... * e_{x_n}` for a sign tuple `e` and
index tuple `x` -/
def signProduct {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d) : ℤ :=
  ∏ i : Fin n, toSign (e (x i))

/-! ### Helper lemmas about toSign and powers -/

/-- The square of any sign is 1 -/
lemma toSign_sq (b : ZMod 2) : toSign b ^ 2 = 1 := by
  fin_cases b <;> simp [toSign]

/-- Even powers of a sign equal 1 -/
lemma toSign_pow_even (b : ZMod 2) (m : ℕ) (hm : Even m) : toSign b ^ m = 1 := by
  obtain ⟨k, hk⟩ := hm
  calc toSign b ^ m = toSign b ^ (2 * k) := by rw [hk, two_mul]
    _ = (toSign b ^ 2) ^ k := by ring
    _ = 1 ^ k := by rw [toSign_sq]
    _ = 1 := one_pow k

/-- Odd powers of a sign equal the sign itself -/
lemma toSign_pow_odd (b : ZMod 2) (m : ℕ) (hm : Odd m) : toSign b ^ m = toSign b := by
  obtain ⟨k, hk⟩ := hm
  calc toSign b ^ m = toSign b ^ (2 * k + 1) := by rw [hk, two_mul]
    _ = (toSign b ^ 2) ^ k * toSign b := by ring
    _ = 1 ^ k * toSign b := by rw [toSign_sq]
    _ = toSign b := by ring

/-- Adding 1 in ZMod 2 flips the sign -/
lemma toSign_add_one (b : ZMod 2) : toSign (b + 1) = -toSign b := by
  fin_cases b <;> decide

/-- The product can be rewritten in terms of multiplicities:
`∏_i e_{x_i} = ∏_k e_k^{m_k}` where `m_k` is the multiplicity of `k` in `x`.

Label: Equation `pf.lem.cancel.all-even.l2.e=e` -/
theorem signProduct_eq_prod_pow {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d) :
    signProduct e x = ∏ k : Fin d, (toSign (e k)) ^ (multiplicity x k) := by
  unfold signProduct multiplicity
  rw [← Finset.prod_fiberwise Finset.univ x (fun i => toSign (e (x i)))]
  congr 1
  ext k
  simp only [prod_filter]
  have h1 : ∏ a : Fin n, (if x a = k then toSign (e (x a)) else 1) =
            ∏ a : Fin n, (if x a = k then toSign (e k) else 1) := by
    apply Finset.prod_congr rfl
    intro a _
    split_ifs with h
    · rw [h]
    · rfl
  rw [h1]
  rw [Finset.prod_ite]
  simp only [prod_const_one, mul_one]
  rw [Finset.prod_const]

/-! ### Lemma `lem.cancel.all-even.l1`: Sum interchange

This lemma establishes that:
```
∑_{e ∈ {1,-1}^d} (e_1 + e_2 + ... + e_d)^n =
  ∑_{x ∈ [d]^n} ∑_{e ∈ {1,-1}^d} e_{x_1} * e_{x_2} * ... * e_{x_n}
```
-/

/-- The sum of entries of a sign tuple, as an integer -/
def signSum {d : ℕ} (e : Fin d → ZMod 2) : ℤ :=
  ∑ k : Fin d, toSign (e k)

/-- Sum interchange identity (Lemma `lem.cancel.all-even.l1`):
The sum over sign tuples of `(∑_k e_k)^n` equals the double sum
over index tuples and sign tuples of the sign product.

This follows from expanding `(∑_k e_k)^n` using the distributive law.

Label: Lemma `lem.cancel.all-even.l1` -/
theorem sum_signSum_pow_eq_sum_signProduct (n d : ℕ) :
    ∑ e : Fin d → ZMod 2, (signSum e)^n =
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
  -- Unfold the definitions
  simp only [signSum, signProduct]
  -- Expand (∑ k, toSign (e k))^n as ∑_{x : Fin n → Fin d} ∏ i, toSign (e (x i))
  -- using the product rule (generalized distributive law)
  simp_rw [Finset.sum_pow']
  -- Convert piFinset over univ to the full type
  simp only [Fintype.piFinset_univ]
  -- Interchange the order of summation
  rw [Finset.sum_comm]

/-! ### Lemma `lem.cancel.all-even.l2`: Computing the inner sums

Part (a): If the tuple is not all-even, the sum of sign products is 0.
Part (b): If the tuple is all-even, the sum of sign products is 2^d.
-/

/-! #### The involution for cancellation

We define an involution on sign tuples that flips the sign at position `k`.
This is used to show cancellation when the tuple has odd multiplicity at `k`.
-/

/-- The involution that flips the k-th sign: if `e_k = +1`, make it `-1`, and vice versa -/
def flipSign {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) : Fin d → ZMod 2 :=
  Function.update e k (e k + 1)

/-- flipSign is an involution -/
lemma flipSign_involutive {d : ℕ} (k : Fin d) : Function.Involutive (flipSign k) := by
  intro e
  ext j
  simp only [flipSign, Function.update]
  split_ifs with h
  · subst h
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc e j + 1 + 1 = e j + 2 := by ring
      _ = e j + 0 := by rw [h2]
      _ = e j := by ring
  · rfl

/-- flipSign produces a different tuple -/
lemma flipSign_ne {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) : flipSign k e ≠ e := by
  intro h
  have h1 : (flipSign k e) k = e k := by rw [h]
  simp only [flipSign, Function.update_self] at h1
  have : (1 : ZMod 2) = 0 := by
    calc (1 : ZMod 2) = (e k + 1) - e k := by ring
      _ = e k - e k := by rw [h1]
      _ = 0 := by ring
  exact one_ne_zero this

/-- flipSign at position k gives e_k + 1 at position k -/
lemma flipSign_self {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) :
    (flipSign k e) k = e k + 1 := by
  simp [flipSign]

/-- flipSign at position k leaves other positions unchanged -/
lemma flipSign_ne_self {d : ℕ} (k j : Fin d) (e : Fin d → ZMod 2) (h : j ≠ k) :
    (flipSign k e) j = e j := by
  simp [flipSign, Function.update_of_ne h]

/-- Key lemma: flipping sign k negates the sign product when k has odd multiplicity -/
lemma signProduct_flipSign {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d)
    (k : Fin d) (hk : Odd (multiplicity x k)) :
    signProduct (flipSign k e) x = -signProduct e x := by
  rw [signProduct_eq_prod_pow, signProduct_eq_prod_pow]
  -- Split the product at k
  rw [← Finset.prod_erase_mul (univ) _ (Finset.mem_univ k)]
  rw [← Finset.prod_erase_mul (univ) _ (Finset.mem_univ k)]
  have h2 : ∏ j ∈ univ.erase k, toSign ((flipSign k e) j) ^ multiplicity x j =
            ∏ j ∈ univ.erase k, toSign (e j) ^ multiplicity x j := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [flipSign_ne_self k j e (Finset.ne_of_mem_erase hj)]
  rw [h2]
  -- Now handle the k-th factor
  rw [flipSign_self, toSign_add_one]
  rw [Odd.neg_pow hk]
  ring

/-- If an n-tuple is not all-even, then the sum over all sign tuples
of the sign product is zero (Lemma `lem.cancel.all-even.l2(a)`).

The proof uses an involution argument: if some element `k` has odd
multiplicity, flipping the sign of `e_k` negates the product, so
terms cancel in pairs.

Label: Lemma `lem.cancel.all-even.l2(a)` -/
theorem sum_signProduct_not_allEven {n d : ℕ} (x : Fin n → Fin d) (hx : ¬IsAllEven x) :
    ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
  -- There exists k with odd multiplicity
  simp only [IsAllEven, not_forall] at hx
  obtain ⟨k, hk⟩ := hx
  rw [Nat.not_even_iff_odd] at hk
  -- Use the involution flipSign k
  apply Finset.sum_involution (fun e _ => flipSign k e)
  · -- signProduct e + signProduct (flipSign k e) = 0
    intro e _
    rw [signProduct_flipSign e x k hk]
    ring
  · -- flipSign k e ≠ e
    intro e _ _
    exact flipSign_ne k e
  · -- flipSign k e ∈ univ
    intro e _
    exact Finset.mem_univ _
  · -- flipSign is involutive
    intro e _
    exact flipSign_involutive k e

/-- If an n-tuple is all-even, then the sum over all sign tuples
of the sign product equals 2^d (Lemma `lem.cancel.all-even.l2(b)`).

The proof: when all multiplicities are even, each `e_k^{m_k} = 1`
(since `(±1)^{even} = 1`), so every sign product equals 1, and
there are 2^d sign tuples.

Label: Lemma `lem.cancel.all-even.l2(b)` -/
theorem sum_signProduct_allEven {n d : ℕ} (x : Fin n → Fin d) (hx : IsAllEven x) :
    ∑ e : Fin d → ZMod 2, signProduct e x = 2^d := by
  -- When all multiplicities are even, each signProduct equals 1
  have h : ∀ e : Fin d → ZMod 2, signProduct e x = 1 := by
    intro e
    rw [signProduct_eq_prod_pow]
    apply Finset.prod_eq_one
    intro k _
    apply toSign_pow_even
    exact hx k
  simp only [h, sum_const]
  have card_eq : (univ : Finset (Fin d → ZMod 2)).card = 2^d := by
    simp [ZMod.card]
  simp [card_eq]

/-! ### Theorem `thm.cancel.all-even`: The counting formula

The number of all-even n-tuples in `[d]^n` equals
`(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n`.
-/

/-- The set of all-even tuples in `(Fin n → Fin d)` -/
def allEvenTuples (n d : ℕ) : Finset (Fin n → Fin d) :=
  univ.filter IsAllEven

/-- Bijection between sign tuples and subsets of `[d]`:
A sign tuple `(e_1, ..., e_d) ∈ {1,-1}^d` corresponds to the set
`{i ∈ [d] | e_i = -1}` of positions with -1. -/
def signTupleToSubset {d : ℕ} (e : Fin d → ZMod 2) : Finset (Fin d) :=
  univ.filter fun k => e k = 1

/-- For a sign tuple corresponding to subset S, the sum of entries
equals `d - 2|S|`. -/
theorem signSum_eq_card {d : ℕ} (e : Fin d → ZMod 2) :
    signSum e = d - 2 * (signTupleToSubset e).card := by
  unfold signSum signTupleToSubset
  -- toSign can be written as 1 - 2 * (if e k = 1 then 1 else 0)
  have htoSign : ∀ k, toSign (e k) = 1 - 2 * (if e k = 1 then 1 else 0) := by
    intro k
    unfold toSign
    have hlt : (e k).val < 2 := (e k).isLt
    interval_cases h : (e k).val
    · have he : e k = 0 := Fin.ext h
      simp [he]
    · have he : e k = 1 := Fin.ext h
      simp [he]
  have heq : ∑ k : Fin d, toSign (e k) = ∑ k : Fin d, (1 - 2 * (if e k = 1 then 1 else 0)) := by
    apply sum_congr rfl
    intro k _
    exact htoSign k
  rw [heq]
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  rw [← mul_sum, sum_boole]

/-! ### Bijection between sign tuples and subsets -/

/-- Inverse of signTupleToSubset: given a subset S, produce the sign tuple
where position k has value 1 (representing -1) iff k ∈ S -/
def subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) : Fin d → ZMod 2 :=
  fun k => if k ∈ S then 1 else 0

lemma signTupleToSubset_subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) :
    signTupleToSubset (subsetToSignTuple S) = S := by
  ext k
  simp [signTupleToSubset, subsetToSignTuple]

lemma subsetToSignTuple_signTupleToSubset {d : ℕ} (e : Fin d → ZMod 2) :
    subsetToSignTuple (signTupleToSubset e) = e := by
  ext k
  simp only [subsetToSignTuple, signTupleToSubset, mem_filter, mem_univ, true_and]
  have hlt : (e k).val < 2 := (e k).isLt
  interval_cases h : (e k).val
  · have he : e k = 0 := Fin.ext h
    simp [he]
  · have he : e k = 1 := Fin.ext h
    simp [he]

/-- Equivalence between sign tuples and subsets of `[d]` -/
def signTupleEquivSubset (d : ℕ) : (Fin d → ZMod 2) ≃ Finset (Fin d) where
  toFun := signTupleToSubset
  invFun := subsetToSignTuple
  left_inv := subsetToSignTuple_signTupleToSubset
  right_inv := signTupleToSubset_subsetToSignTuple

/-- For a subset S, the sign sum of the corresponding tuple equals d - 2|S| -/
lemma signSum_subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) :
    signSum (subsetToSignTuple S) = d - 2 * S.card := by
  rw [signSum_eq_card, signTupleToSubset_subsetToSignTuple]

/-- Compute the double sum using lemma l2 -/
theorem sum_signProduct_eq_allEven_count (n d : ℕ) :
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
    (allEvenTuples n d).card * 2^d := by
  -- Split into all-even and not-all-even tuples
  have h1 : ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
      ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter IsAllEven, ∑ e : Fin d → ZMod 2, signProduct e x +
      ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter (fun x => ¬IsAllEven x), ∑ e : Fin d → ZMod 2, signProduct e x := by
    rw [← sum_filter_add_sum_filter_not (univ : Finset (Fin n → Fin d)) IsAllEven]
  rw [h1]
  -- The non-all-even part is 0
  have h2 : ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter (fun x => ¬IsAllEven x),
      ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
    apply sum_eq_zero
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact sum_signProduct_not_allEven x hx
  rw [h2, add_zero]
  -- The all-even part is |allEvenTuples| * 2^d
  have h3 : ∑ x ∈ (univ : Finset (Fin n → Fin d)).filter IsAllEven,
      ∑ e : Fin d → ZMod 2, signProduct e x =
      ∑ x ∈ allEvenTuples n d, (2 : ℤ)^d := by
    apply sum_congr
    · rfl
    intro x hx
    simp only [mem_filter, mem_univ, true_and, allEvenTuples] at hx
    exact sum_signProduct_allEven x hx
  rw [h3]
  simp [allEvenTuples, sum_const, mul_comm]

/-- Rewrite sum over sign tuples as sum over subsets -/
theorem sum_signSum_pow_eq_sum_subset (n d : ℕ) :
    ∑ e : Fin d → ZMod 2, (signSum e)^n =
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n := by
  rw [Fintype.sum_equiv (signTupleEquivSubset d)]
  intro e
  rw [signSum_eq_card]
  simp [signTupleEquivSubset]

/-- Group sum over subsets by cardinality -/
theorem sum_subset_eq_sum_choose (n d : ℕ) :
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n =
    ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  have h1 : ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ)^n =
      ∑ k ∈ range (d + 1), ∑ S ∈ (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k),
        (d - 2 * S.card : ℤ)^n := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (d + 1)) (g := fun S => S.card)]
    intro S _
    simp only [mem_range]
    have : S.card ≤ (univ : Finset (Fin d)).card := Finset.card_le_card (Finset.subset_univ S)
    simp only [card_univ, Fintype.card_fin] at this
    omega
  rw [h1]
  apply sum_congr rfl
  intro k hk
  simp only [mem_range] at hk
  have h2 : ∀ S ∈ (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k),
      (d - 2 * S.card : ℤ)^n = (d - 2*k : ℤ)^n := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    simp [hS]
  simp_rw [sum_congr rfl h2, sum_const]
  have h3 : ((univ : Finset (Finset (Fin d))).filter (fun S => S.card = k)).card = d.choose k := by
    have : (univ : Finset (Finset (Fin d))).filter (fun S => S.card = k) = powersetCard k (univ : Finset (Fin d)) := by
      ext S
      simp [mem_powersetCard]
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  rw [h3]
  ring

/-- The main counting formula (Theorem `thm.cancel.all-even`):
The number of all-even n-tuples in `(Fin n → Fin d)` equals
`(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n`.

This formula implies that `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative
and divisible by `2^d`, which is not obvious from the formula itself
due to the alternating signs when `n` is odd.

Label: Theorem `thm.cancel.all-even` -/
theorem allEven_count_formula (n d : ℕ) :
    ((allEvenTuples n d).card : ℤ) * 2^d = ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  -- Connect via l1 and l2: LHS = ∑_x ∑_e signProduct e x = ∑_e (signSum e)^n = RHS
  have h1 : ((allEvenTuples n d).card : ℤ) * 2^d =
      ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
    rw [sum_signProduct_eq_allEven_count]
  rw [h1, ← sum_signSum_pow_eq_sum_signProduct, sum_signSum_pow_eq_sum_subset, sum_subset_eq_sum_choose]

/-- Corollary: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is divisible by `2^d`. -/
theorem sum_choose_pow_dvd_pow_two (n d : ℕ) :
    (2^d : ℤ) ∣ ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  rw [← allEven_count_formula n d]
  exact dvd_mul_left ((2 : ℤ)^d) ((allEvenTuples n d).card)

/-- Corollary: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative. -/
theorem sum_choose_pow_nonneg (n d : ℕ) :
    0 ≤ ∑ k ∈ range (d + 1), d.choose k * (d - 2*k : ℤ)^n := by
  rw [← allEven_count_formula]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) d)

end AlgebraicCombinatorics.SubtractiveMethods
