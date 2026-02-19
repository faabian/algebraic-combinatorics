/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# The Principles of Inclusion and Exclusion

This file formalizes the inclusion-exclusion principles and their applications from
Section `sec.sign.pie` of the Algebraic Combinatorics notes.

## Main results

### Size version (Theorem `thm.pie.1`)
The size version of PIE states that for a finite set `U` and subsets `A₁, ..., Aₙ`:
  |{u ∈ U : u ∉ Aᵢ for all i}| = ∑_{I ⊆ [n]} (-1)^|I| |{u ∈ U : u ∈ Aᵢ for all i ∈ I}|

This is already available in Mathlib as `Finset.inclusion_exclusion_card_inf_compl`.

### Applications

* `numSurj` - The number of surjective maps from `[m]` to `[n]` (Theorem `thm.pie.count-sur`)
* `numSurj_formula` - The formula: ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m
* Corollaries about the surjection count (`cor.pie.count-sur.cors`)
* `Derangement` - Permutations with no fixed points (Definition `def.pie.dera`)
* `numDerangements_formula` - The derangement count formula (Theorem `thm.pie.count-der`)
* `totient_eq_prod_one_sub_inv` - Euler's totient formula (Theorem `thm.pie.euler-tot`)

### Weighted version (Theorem `thm.pie.2`)
The weighted version generalizes the size version by replacing cardinalities with weighted sums.
This is already available in Mathlib as `Finset.inclusion_exclusion_sum_inf_compl`.

## References

* Section `sec.sign.pie` of the Algebraic Combinatorics notes
* Mathlib's `Mathlib.Combinatorics.Enumerative.InclusionExclusion`
-/

open Finset BigOperators Nat

namespace AlgebraicCombinatorics.InclusionExclusion

/-! ### Size version of PIE (Theorem `thm.pie.1`)

The size version is already in Mathlib. We restate it here for reference.
See `Finset.inclusion_exclusion_card_inf_compl`.

For a finite set `U` and subsets `A₁, ..., Aₙ`:
  |U \ (A₁ ∪ ... ∪ Aₙ)| = ∑_{I ⊆ [n]} (-1)^|I| |⋂_{i ∈ I} Aᵢ|

where the empty intersection is taken to be `U`.
-/

/-- **Theorem `thm.pie.1`** (Size version of PIE):
For a finite set `U` and subsets `A₁, ..., Aₙ`, the number of elements in `U` that
belong to none of the `Aᵢ` equals the alternating sum over all subsets `I ⊆ [n]` of
the cardinalities of the intersections `⋂_{i ∈ I} Aᵢ`.

More precisely:
  |U ∩ A₁ᶜ ∩ A₂ᶜ ∩ ... ∩ Aₙᶜ| = ∑_{I ⊆ [n]} (-1)^|I| |⋂_{i ∈ I} Aᵢ|

where the empty intersection is taken to be `U`.

This is `Finset.inclusion_exclusion_card_inf_compl` from Mathlib. -/
theorem pie_size_version {α ι : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (A : ι → Finset α) :
    #(s.inf fun i ↦ (A i)ᶜ) = ∑ I ∈ s.powerset, (-1 : ℤ) ^ #I * #(I.inf A) :=
  Finset.inclusion_exclusion_card_inf_compl s A

/-- Alternative form of `thm.pie.1` using the complement of a union.

This states: |U \ (A₁ ∪ A₂ ∪ ... ∪ Aₙ)| = ∑_{I ⊆ [n]} (-1)^|I| |⋂_{i ∈ I} Aᵢ|

This is the more common textbook formulation. -/
theorem pie_size_version' {α ι : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (A : ι → Finset α) :
    #((s.biUnion A)ᶜ) = ∑ I ∈ s.powerset, (-1 : ℤ) ^ #I * #(I.inf A) := by
  have h : (s.biUnion A)ᶜ = s.inf fun i ↦ (A i)ᶜ := by
    rw [← sup_eq_biUnion, Finset.compl_sup]
  rw [h]
  exact Finset.inclusion_exclusion_card_inf_compl s A

/-- **Theorem `thm.pie.1`** specialized to `n` subsets indexed by `Fin n`.

For a finite type `α` (the "universe" `U`) and `n` subsets `A₀, A₁, ..., Aₙ₋₁` of `α`:
  |{u ∈ α : u ∉ Aᵢ for all i ∈ Fin n}| = ∑_{I ⊆ Fin n} (-1)^|I| |⋂_{i ∈ I} Aᵢ|

This matches the textbook formulation where `[n] = {1, 2, ..., n}` is replaced by `Fin n`. -/
theorem pie_size_version_fin {α : Type*} [DecidableEq α] [Fintype α]
    (n : ℕ) (A : Fin n → Finset α) :
    #(Finset.univ.inf fun i ↦ (A i)ᶜ) =
      ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ #I * #(I.inf A) :=
  pie_size_version Finset.univ A

/-- The "rule-breaking" interpretation of PIE: Count elements that violate all rules.

Given `n` "rules" (encoded as subsets `A₀, ..., Aₙ₋₁` where `Aᵢ` is the set of elements
satisfying rule `i`), the number of elements violating all rules equals the alternating
sum over all subsets `I` of the number of elements satisfying all rules in `I`. -/
theorem pie_rule_breaking {α : Type*} [DecidableEq α] [Fintype α]
    (n : ℕ) (satisfiesRule : Fin n → Finset α) :
    (Finset.univ.filter fun u ↦ ∀ i : Fin n, u ∉ satisfiesRule i).card =
      ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ #I *
        (Finset.univ.filter fun u ↦ ∀ i ∈ I, u ∈ satisfiesRule i).card := by
  -- The LHS is the cardinality of the intersection of complements
  have lhs_eq : (Finset.univ.filter fun u ↦ ∀ i : Fin n, u ∉ satisfiesRule i) =
      Finset.univ.inf fun i ↦ (satisfiesRule i)ᶜ := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_inf, mem_compl]
    simp only [forall_true_left]
  -- For each I, the RHS term counts elements in the intersection
  have rhs_term_eq : ∀ I ∈ Finset.univ.powerset,
      (Finset.univ.filter fun u ↦ ∀ i ∈ I, u ∈ satisfiesRule i) = I.inf satisfiesRule := by
    intro I _
    ext u
    simp only [mem_filter, mem_univ, true_and, Finset.mem_inf]
  rw [lhs_eq]
  conv_rhs =>
    congr
    · skip
    · ext I
      rw [rhs_term_eq I (by simp)]
  exact pie_size_version_fin n satisfiesRule

/-! ### Example 1: Counting surjective maps (Theorem `thm.pie.count-sur`)

The number of surjective maps from `Fin m` to `Fin n` is
  ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m
-/

/-- The number of surjective maps from `Fin m` to `Fin n`. -/
def numSurj (m n : ℕ) : ℕ := Fintype.card {f : Fin m → Fin n // Function.Surjective f}

/-! #### Helper lemmas for the surjection formula -/

/-- Count functions from `Fin m` to `Fin n` whose range avoids a given set `I`. -/
lemma card_functions_avoiding_set (m n : ℕ) (I : Finset (Fin n)) :
    Fintype.card {f : Fin m → Fin n // ∀ i ∈ I, i ∉ Set.range f} = (n - #I) ^ m := by
  classical
  let target : Finset (Fin n) := Iᶜ
  have hcard : #target = n - #I := by simp [target, card_compl]
  let e : {f : Fin m → Fin n // ∀ i ∈ I, i ∉ Set.range f} ≃ (Fin m → target) := {
    toFun := fun ⟨f, hf⟩ => fun j => ⟨f j, by
      simp only [target, mem_compl]
      intro hi
      exact hf (f j) hi ⟨j, rfl⟩⟩
    invFun := fun g => ⟨fun j => (g j).1, by
      intro i hi ⟨j, hj⟩
      have h := (g j).2
      simp only [target, mem_compl] at h
      rw [← hj] at hi
      exact h hi⟩
    left_inv := fun ⟨f, hf⟩ => rfl
    right_inv := fun g => rfl
  }
  rw [Fintype.card_congr e]
  simp [hcard]

/-- For each `i : Fin n`, the set of functions `f : Fin m → Fin n` such that `i ∉ range f`. -/
private def S_avoid (m n : ℕ) (i : Fin n) : Finset (Fin m → Fin n) :=
  univ.filter (fun f => i ∉ Set.range f)

/-- The cardinality of the intersection of `S_avoid` sets. -/
lemma card_inf_S_avoid (m n : ℕ) (t : Finset (Fin n)) :
    #(t.inf (S_avoid m n)) = (n - #t) ^ m := by
  have h1 : t.inf (S_avoid m n) = univ.filter (fun f => ∀ i ∈ t, i ∉ Set.range f) := by
    ext f
    simp only [mem_inf, S_avoid, mem_filter, mem_univ, true_and]
  rw [h1]
  have h : #(univ.filter (fun f : Fin m → Fin n => ∀ i ∈ t, i ∉ Set.range f)) =
           Fintype.card {f : Fin m → Fin n // ∀ i ∈ t, i ∉ Set.range f} := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine {
      toFun := fun ⟨f, hf⟩ => ⟨f, by simp only [mem_filter, mem_univ, true_and] at hf; exact hf⟩
      invFun := fun ⟨f, hf⟩ => ⟨f, by simp only [mem_filter, mem_univ, true_and]; exact hf⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  rw [h, card_functions_avoiding_set]

/-- **Theorem `thm.pie.count-sur`**: The number of surjective maps from `Fin m` to `Fin n`
equals `∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m`.

This is the main formula for counting surjections using inclusion-exclusion. -/
theorem numSurj_formula (m n : ℕ) :
    (numSurj m n : ℤ) = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
  -- Step 1: Relate numSurj to the PIE formula
  -- Surjective functions are those where every element of Fin n is in the range.
  -- Using PIE with S_i = {f | i ∉ range f}, surjective = ⋂_i (S_i)ᶜ
  have h1 : (numSurj m n : ℤ) = #((univ : Finset (Fin n)).inf (fun i => (S_avoid m n i)ᶜ)) := by
    unfold numSurj
    rw [← Fintype.card_coe]
    congr 1
    apply Fintype.card_congr
    refine {
      toFun := fun ⟨f, hf⟩ => ⟨f, by
        simp only [mem_inf, mem_compl, S_avoid, mem_filter, mem_univ, true_and, not_not]
        intro i _
        exact hf i⟩
      invFun := fun ⟨f, hf⟩ => ⟨f, by
        simp only [mem_inf, mem_compl, S_avoid, mem_filter, mem_univ, true_and, not_not] at hf
        intro i
        exact hf i trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  rw [h1]
  -- Step 2: Apply PIE (inclusion_exclusion_card_inf_compl)
  rw [Finset.inclusion_exclusion_card_inf_compl]
  -- Step 3: Substitute the cardinality formula for each subset
  conv_lhs =>
    arg 2
    ext t
    rw [card_inf_S_avoid]
  -- Step 4: Rewrite sum over powerset as sum over cardinalities
  rw [Finset.sum_powerset]
  have huniv : #(univ : Finset (Fin n)) = n := by simp
  rw [huniv]
  -- Step 5: Simplify each inner sum (grouping by cardinality)
  apply sum_congr rfl
  intro j hj
  have hj_le : j ≤ n := by simp only [mem_range] at hj; omega
  calc ∑ t ∈ powersetCard j (univ : Finset (Fin n)), (-1 : ℤ) ^ #t * ((n - #t) ^ m : ℕ)
      = ∑ t ∈ powersetCard j (univ : Finset (Fin n)), (-1 : ℤ) ^ j * ((n - j) ^ m : ℕ) := by
        apply sum_congr rfl
        intro t ht
        have hcard := (mem_powersetCard.1 ht).2
        simp [hcard]
      _ = #(powersetCard j (univ : Finset (Fin n))) * ((-1 : ℤ) ^ j * ((n - j) ^ m : ℕ)) := by
        rw [sum_const, nsmul_eq_mul]
      _ = (n.choose j) * ((-1 : ℤ) ^ j * ((n - j) ^ m : ℕ)) := by
        rw [card_powersetCard, huniv]
      _ = (-1 : ℤ) ^ j * (n.choose j) * ((n - j) ^ m : ℕ) := by ring
      _ = (-1 : ℤ) ^ j * (n.choose j) * (n - j : ℤ) ^ m := by
        congr 1
        have h : (n - j : ℕ) = (n : ℤ) - j := Int.ofNat_sub hj_le
        rw [← h]; simp

/-! ### Corollary `cor.pie.count-sur.cors`: Consequences of the surjection formula -/

/-- **Corollary `cor.pie.count-sur.cors` (a)**: When `m < n`, there are no surjections,
so the alternating sum equals 0. -/
theorem surjOn_alternating_sum_eq_zero (n : ℕ) (m : ℕ) (h : m < n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m = 0 := by
  -- First show that numSurj m n = 0 (no surjections from smaller to larger set)
  have h1 : numSurj m n = 0 := by
    rw [numSurj, Fintype.card_eq_zero_iff]
    constructor
    intro ⟨f, hf⟩
    have : Fintype.card (Fin n) ≤ Fintype.card (Fin m) := Fintype.card_le_of_surjective f hf
    simp only [Fintype.card_fin] at this
    omega
  -- Then use numSurj_formula
  rw [← numSurj_formula, h1]
  simp

/-- **Corollary `cor.pie.count-sur.cors` (b)**: When `m = n`, the number of surjections
equals `n!` (the surjections are precisely the permutations). -/
theorem surjOn_alternating_sum_eq_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ n = n ! := by
  -- Use the forward difference operator identity:
  -- The n-th forward difference of x^n at 0 equals n!
  have h1 : (fwdDiff (1 : ℤ))^[n] (fun (r : ℤ) ↦ r ^ n) 0 = (n ! : ℤ) := by
    have := fwdDiff_iter_eq_factorial (R := ℤ) (n := n)
    simp only [this, Pi.natCast_def]
  -- And by fwdDiff_iter_eq_sum_shift, this equals ∑ (-1)^(n-k) * C(n,k) * k^n
  have h2 : (fwdDiff (1 : ℤ))^[n] (fun (r : ℤ) ↦ r ^ n) 0 =
      ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • (k : ℤ) ^ n := by
    have := fwdDiff_iter_eq_sum_shift (1 : ℤ) (fun (r : ℤ) ↦ r ^ n) n 0
    simp only [zero_add, nsmul_eq_mul, mul_one] at this
    exact this
  rw [h2] at h1
  -- Transform the sum by substituting k → n - k and using symmetry of binomial coefficients
  have h3 : ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ n =
            ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • (k : ℤ) ^ n := by
    refine sum_bij' (fun k _ => n - k) (fun k _ => n - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [mem_range] at hk ⊢
      exact Nat.sub_lt_succ n k
    · intro k hk
      rw [mem_range] at hk ⊢
      exact Nat.sub_lt_succ n k
    · intro k hk
      rw [mem_range] at hk
      exact Nat.sub_sub_self (Nat.lt_succ_iff.mp hk)
    · intro k hk
      rw [mem_range] at hk
      exact Nat.sub_sub_self (Nat.lt_succ_iff.mp hk)
    · intro k hk
      rw [mem_range] at hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
      simp only [zsmul_eq_mul]
      congr 1
      · congr 1
        · congr 1
          · rw [Nat.sub_sub_self hk']
        · rw [choose_symm hk']
      · simp only [Int.ofNat_sub hk']
  rw [h3, h1]

/-- **Corollary `cor.pie.count-sur.cors` (c)**: The alternating sum is always nonnegative
since it counts surjections. -/
theorem surjOn_alternating_sum_nonneg (m n : ℕ) :
    0 ≤ ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
  rw [← numSurj_formula]
  exact Int.natCast_nonneg (numSurj m n)

/-! #### Helper lemmas for the divisibility proof

The proof uses the orbit-stabilizer theorem. The symmetric group `Perm (Fin n)` acts on
surjective maps `Fin m → Fin n` by post-composition. Since this action is free (the stabilizer
of any surjective map is trivial), the number of surjections is divisible by `n!`.
-/

/-- Action of `Perm (Fin n)` on functions `Fin m → Fin n` by post-composition. -/
instance permActionOnFun (m n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin m → Fin n) where
  smul σ f := σ ∘ f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Post-composition with a permutation preserves surjectivity. -/
lemma surjective_smul {m n : ℕ} (σ : Equiv.Perm (Fin n)) {f : Fin m → Fin n}
    (hf : Function.Surjective f) : Function.Surjective (σ • f) := by
  intro y
  obtain ⟨x, hx⟩ := hf (σ.symm y)
  use x
  simp only [HSMul.hSMul, SMul.smul, hx, Equiv.apply_symm_apply]

/-- Action of `Perm (Fin n)` on surjective functions `Fin m → Fin n` by post-composition. -/
instance permActionOnSurj (m n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) {f : Fin m → Fin n // Function.Surjective f} where
  smul σ f := ⟨σ • f.val, surjective_smul σ f.prop⟩
  one_smul f := by ext; simp [HSMul.hSMul, SMul.smul]
  mul_smul σ τ f := by ext; simp [HSMul.hSMul, SMul.smul]

/-- The action of `Perm (Fin n)` on surjective maps is free: the stabilizer of any
surjective map is trivial. This is because if `σ ∘ f = f` and `f` is surjective, then `σ = id`. -/
lemma stabilizer_surj_eq_bot {m n : ℕ} (f : {f : Fin m → Fin n // Function.Surjective f}) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) f = ⊥ := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    ext y
    obtain ⟨x, hx⟩ := f.prop y
    have heq : (σ • f).val = f.val := by
      simp only [Subtype.ext_iff] at h
      exact h
    simp only [HSMul.hSMul, SMul.smul] at heq
    have eq : σ (f.val x) = f.val x := congr_fun heq x
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hx, eq]
  · intro h
    simp [h]

/-- `n!` divides `numSurj m n` because the action of `Perm (Fin n)` on surjective maps
is free, so each orbit has size `n!`. -/
lemma factorial_dvd_numSurj (m n : ℕ) : n ! ∣ numSurj m n := by
  rw [numSurj]
  classical
  let G := Equiv.Perm (Fin n)
  let X := {f : Fin m → Fin n // Function.Surjective f}
  let Ω := MulAction.orbitRel.Quotient G X
  -- The class formula gives: X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.out
  have equiv := MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X
  have card_eq : Fintype.card X = ∑ ω : Ω, Fintype.card (G ⧸ MulAction.stabilizer G ω.out) := by
    rw [Fintype.card_congr equiv, Fintype.card_sigma]
  -- Since stabilizers are trivial, each quotient has size |G| = n!
  have hquot : ∀ ω : Ω, Fintype.card (G ⧸ MulAction.stabilizer G ω.out) = n ! := fun ω => by
    have hstab : MulAction.stabilizer G ω.out = ⊥ := stabilizer_surj_eq_bot ω.out
    have h1 : Nat.card G = Nat.card (G ⧸ MulAction.stabilizer G ω.out) *
              Nat.card (MulAction.stabilizer G ω.out) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (MulAction.stabilizer G ω.out) = 1 := by
      rw [hstab, Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, ⟨1⟩⟩
    have h3 : Nat.card (Equiv.Perm (Fin n)) = n ! := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rw [h2, mul_one] at h1
    simp only [Nat.card_eq_fintype_card] at h1 h3
    rw [← h1, h3]
  simp_rw [hquot] at card_eq
  rw [card_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

/-- **Corollary `cor.pie.count-sur.cors` (d)**: The alternating sum is divisible by `n!`.
This follows from the orbit-stabilizer theorem applied to the action of `Sₙ` on surjections. -/
theorem surjOn_alternating_sum_dvd_factorial (m n : ℕ) :
    (n ! : ℤ) ∣ ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
  rw [← numSurj_formula]
  exact Int.natCast_dvd_natCast.mpr (factorial_dvd_numSurj m n)

/-! ### Example 2: Derangements (Definition `def.pie.dera` and Theorem `thm.pie.count-der`)

A derangement is a permutation with no fixed points.

**Relationship to Mathlib:**
- Mathlib defines `derangements α : Set (Perm α)` in `Mathlib.Combinatorics.Derangements.Basic`
- Mathlib defines `numDerangements : ℕ → ℕ` in `Mathlib.Combinatorics.Derangements.Finite`
- Our `Derangement α` is definitionally equal to `↥(derangements α)` (the subtype)
- `Fintype.card (Derangement (Fin n))` equals `numDerangements n` (see `card_Derangement_eq`)

We provide the explicit `Derangement` type to make the connection to the textbook explicit.
The main theorems use Mathlib's `numDerangements` directly.
-/

/-- **Definition `def.pie.dera`**: A derangement of a type `α` is a permutation with no fixed points.

This is definitionally equal to `↥(derangements α)` from `Mathlib.Combinatorics.Derangements.Basic`.

**Textbook definition:** "A derangement of a set X means a permutation of X that has no fixed points."

**Examples from the textbook:**
- D₀ = 1: The identity on ∅ is a derangement (vacuously no fixed points)
- D₁ = 0: The identity on {0} fixes 0, so it's not a derangement
- D₂ = 1: Only the swap (0 1) is a derangement
- D₃ = 2: The two 3-cycles (0 1 2) and (0 2 1) are derangements -/
def Derangement (α : Type*) := {σ : Equiv.Perm α // ∀ x, σ x ≠ x}

instance {α : Type*} [DecidableEq α] [Fintype α] : Fintype (Derangement α) :=
  Subtype.fintype _

/-- A derangement is a permutation in `derangements α`.
This shows our definition matches Mathlib's `derangements` set. -/
theorem Derangement.mem_derangements {α : Type*} (σ : Derangement α) :
    σ.val ∈ derangements α := σ.prop

/-- The `Derangement` type is equivalent to the subtype of `derangements α`.
This establishes that our explicit type is equivalent to Mathlib's set-based definition. -/
def Derangement.equivDerangements (α : Type*) :
    Derangement α ≃ (derangements α : Set (Equiv.Perm α)) where
  toFun σ := ⟨σ.val, σ.mem_derangements⟩
  invFun σ := ⟨σ.val, σ.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identity is a derangement of the empty type.
This matches the textbook example: D₀ = 1, since the identity has no fixed points
when there are no elements. -/
theorem Derangement.id_of_isEmpty {α : Type*} [IsEmpty α] :
    ∃ d : Derangement α, d.val = 1 := by
  use ⟨1, fun x => (IsEmpty.false x).elim⟩

/-- The identity is NOT a derangement when the type is nonempty.
This matches the textbook example: D₁ = 0, since id(1) = 1 is a fixed point. -/
theorem Derangement.id_not_derangement {α : Type*} [Nonempty α] :
    ∀ d : Derangement α, d.val ≠ 1 := by
  intro d hd
  obtain ⟨x⟩ := ‹Nonempty α›
  have h := d.prop x
  simp [hd] at h

/-- The cardinality of `Derangement (Fin n)` equals Mathlib's `numDerangements n`. -/
theorem card_Derangement_eq (n : ℕ) :
    Fintype.card (Derangement (Fin n)) = numDerangements n := by
  unfold Derangement
  exact card_derangements_fin_eq_numDerangements

-- Basic values of the derangement count (these follow from Mathlib's `numDerangements_zero`,
-- `numDerangements_one`, etc.)

/-- `D₂ = 1`: The only derangement of `{0, 1}` is the swap.
(Mathlib already provides `numDerangements_zero` and `numDerangements_one` as `@[simp]` lemmas.) -/
theorem numDerangements_two' : numDerangements 2 = 1 := by
  native_decide

/-- `D₃ = 2`: There are exactly 2 derangements of `{0, 1, 2}` (the two 3-cycles).
This matches the textbook: "the derangements are the 3-cycles cyc_{1,2,3} and cyc_{1,3,2}". -/
theorem numDerangements_three : numDerangements 3 = 2 := by native_decide

/-- `D₄ = 9`: There are exactly 9 derangements of `{0, 1, 2, 3}`.
From the textbook table of early values. -/
theorem numDerangements_four : numDerangements 4 = 9 := by native_decide

/-- `D₅ = 44`: There are exactly 44 derangements of `{0, 1, 2, 3, 4}`.
From the textbook table of early values. -/
theorem numDerangements_five : numDerangements 5 = 44 := by native_decide

/-- **Theorem `thm.pie.count-der`**: The number of derangements of `Fin n` is
`Dₙ = ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)! = n! * ∑_{k=0}^{n} (-1)^k / k!`

This is derived from PIE by considering permutations that violate all "fixed point" rules.

Note: Mathlib's `numDerangements_sum` gives a related formula using ascending factorials. -/
theorem numDerangements_formula (n : ℕ) :
    (numDerangements n : ℤ) = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k)! := by
  rw [numDerangements_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h : k ≤ n := Finset.mem_range_succ_iff.mp hk
  -- Key identity: (k+1).ascFactorial (n-k) = (n-k)! * n.choose k
  have key : Nat.ascFactorial (k + 1) (n - k) = (n - k).factorial * n.choose k := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose']
    congr 1
    have : k + 1 + (n - k) - 1 = n := by omega
    rw [this, Nat.choose_symm h]
  rw [key]
  simp only [Int.natCast_mul]
  ring

/-- Alternative form of the derangement formula: `Dₙ = n! * ∑_{k=0}^{n} (-1)^k / k!` -/
theorem numDerangements_formula_rat (n : ℕ) :
    (numDerangements n : ℚ) = n ! * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / k ! := by
  -- Use numDerangements_formula and convert to rationals
  have h := numDerangements_formula n
  -- Convert to rationals
  have hq : (numDerangements n : ℚ) = ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k) * (n - k)! := by
    have := congrArg (Int.cast (R := ℚ)) h
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at this
    exact this
  rw [hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  -- k ∈ range (n + 1), so k ≤ n
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- Need: (-1)^k * C(n,k) * (n-k)! = n! * (-1)^k / k!
  have key : (n.choose k : ℚ) * (n - k)! = n ! / k ! := by
    rw [Nat.choose_eq_factorial_div_factorial hk_le]
    have hdiv : k ! * (n - k)! ∣ n ! := Nat.factorial_mul_factorial_dvd_factorial hk_le
    rw [Nat.cast_div hdiv (by positivity)]
    field_simp
    push_cast
    ring
  calc (-1 : ℚ) ^ k * (n.choose k) * (n - k)!
      = (-1) ^ k * ((n.choose k : ℚ) * (n - k)!) := by ring
    _ = (-1) ^ k * (n ! / k !) := by rw [key]
    _ = n ! * ((-1) ^ k / k !) := by field_simp

/-! ### Example 3: Euler's totient function (Theorem `thm.pie.euler-tot`)

Euler's totient `φ(c)` counts integers in `[1, c]` coprime to `c`.
The formula expresses this in terms of the prime factorization.

Note: `Nat.totient` is already defined in Mathlib.
-/

/-- **Theorem `thm.pie.euler-tot`**: Euler's totient formula.
For a positive integer `c` with prime factorization `p₁^{a₁} * ... * pₙ^{aₙ}`:
  φ(c) = c * ∏_{i=1}^{n} (1 - 1/pᵢ) = ∏_{i=1}^{n} (pᵢ^{aᵢ} - pᵢ^{aᵢ-1})

This is proved using PIE where rule `i` is "be divisible by pᵢ".

Note: This is essentially `Nat.totient_eq_prod_factorization` in Mathlib. -/
theorem totient_eq_prod_one_sub_inv (c : ℕ) (_hc : 0 < c) :
    (Nat.totient c : ℚ) = c * ∏ p ∈ c.primeFactors, (1 - 1 / (p : ℚ)) := by
  rw [Nat.totient_eq_mul_prod_factors]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

/-! ### Example 4: Partitions into distinct vs odd parts

This example shows that `p_dist(n) = p_odd(n)` using PIE.
This is already covered in other chapters on partitions.
-/

/-! ### Weighted version of PIE (Theorem `thm.pie.2`)

The weighted version of the Principle of Inclusion and Exclusion generalizes
the size version by replacing cardinalities with weighted sums.

For a finite set `U`, subsets `A₁, ..., Aₙ`, an additive abelian group `A`,
and a weight function `w : U → A`:

  ∑_{u ∈ U : u ∉ Aᵢ for all i ∈ [n]} w(u) = ∑_{I ⊆ [n]} (-1)^|I| ∑_{u ∈ U : u ∈ Aᵢ for all i ∈ I} w(u)

This is proved in Mathlib as `Finset.inclusion_exclusion_sum_inf_compl`.
Theorem `thm.pie.1` is obtained by setting `w(u) = 1` for all `u`.
-/

/-- **Theorem `thm.pie.2`**: The weighted version of the Principle of Inclusion and Exclusion.

For a finite type `U`, finitely many subsets `A₁, ..., Aₙ` (indexed by a finite type `ι`),
an additive abelian group `G`, and a weight function `w : U → G`:

  ∑_{u ∈ U : u ∉ Aᵢ for all i} w(u) = ∑_{I ⊆ ι} (-1)^|I| ∑_{u ∈ U : u ∈ Aᵢ for all i ∈ I} w(u)

This generalizes the size version (Theorem `thm.pie.1`) which is obtained by taking `w(u) = 1`.

The left-hand side sums `w(u)` over all elements `u` that belong to none of the subsets `Aᵢ`.
The right-hand side is an alternating sum over all subsets `I` of the index set, where we sum
`w(u)` over elements belonging to all `Aᵢ` with `i ∈ I`.
-/
theorem weighted_pie {ι U G : Type*} [Fintype ι] [DecidableEq ι] [Fintype U] [DecidableEq U]
    [AddCommGroup G] (A : ι → Finset U) (w : U → G) :
    ∑ u ∈ Finset.univ.inf fun i ↦ (A i)ᶜ, w u =
    ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ I.card • ∑ u ∈ I.inf A, w u := by
  exact Finset.inclusion_exclusion_sum_inf_compl Finset.univ A w

/-- **Theorem `thm.pie.2`** (alternative formulation with explicit index set):
The weighted PIE with an explicit finite index set `s` of "rules".

This version allows indexing by a subset `s` of a larger type `ι`, rather than requiring
a finite type for the index. -/
theorem weighted_pie' {ι U G : Type*} [DecidableEq ι] [Fintype U] [DecidableEq U]
    [AddCommGroup G] (s : Finset ι) (A : ι → Finset U) (w : U → G) :
    ∑ u ∈ s.inf fun i ↦ (A i)ᶜ, w u =
    ∑ I ∈ s.powerset, (-1 : ℤ) ^ I.card • ∑ u ∈ I.inf A, w u := by
  exact Finset.inclusion_exclusion_sum_inf_compl s A w

/-- The size version of PIE (Theorem `thm.pie.1`) follows from the weighted version
by taking `w(u) = 1` for all `u`.

This demonstrates that `thm.pie.1` is a special case of `thm.pie.2`. -/
theorem size_pie_from_weighted {ι U : Type*} [DecidableEq ι] [Fintype U] [DecidableEq U]
    (s : Finset ι) (A : ι → Finset U) :
    ((s.inf fun i ↦ (A i)ᶜ).card : ℤ) = ∑ I ∈ s.powerset, (-1 : ℤ) ^ I.card * (I.inf A).card := by
  have h := weighted_pie' (G := ℤ) s A (fun _ ↦ 1)
  simp only [sum_const, smul_eq_mul] at h
  convert h using 2 <;> ring

end AlgebraicCombinatorics.InclusionExclusion
