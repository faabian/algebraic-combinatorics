/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Permutation Images of Finsets

This file provides shared definitions and lemmas for working with the image of a finset
under a permutation.

## Main definitions

* `PermFinset.imageFinset` - The image of a finset under a permutation: `P.map ⟨σ, σ.injective⟩`
* `PermFinset.permsMapping` - The set of permutations that map one finset to another

## Main results

* `PermFinset.imageFinset_card` - The image has the same cardinality as the original set
* `PermFinset.imageFinset_compl` - The image of a complement equals the complement of the image
* `PermFinset.imageFinset_inv` - If σ maps P to Q, then σ⁻¹ maps Q to P
* `PermFinset.permsMapping_empty_of_card_ne` - If |P| ≠ |Q|, no permutation maps P to Q

## Implementation notes

These definitions are used by:
- `CauchyBinet.lean` (has local aliases `imageFinset` and `permsMapping`)
- `DesnanotJacobi.lean` (uses `PermFinset.imageFinset` and `PermFinset.permsMapping` directly)

New code should use this module.
-/

namespace PermFinset

/-- The image of a finset under a permutation. -/
def imageFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.map ⟨σ, σ.injective⟩

/-- The image has the same cardinality as the original set. -/
theorem imageFinset_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    (imageFinset σ P).card = P.card := Finset.card_map _

/-- The image of a complement equals the complement of the image. -/
lemma imageFinset_compl {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    imageFinset σ Pᶜ = (imageFinset σ P)ᶜ := by
  ext x
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_compl]
  constructor
  · intro ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    rw [← hyx] at hzx
    have heq := σ.injective hzx
    exact hy (heq ▸ hz)
  · intro hx
    use σ.symm x
    constructor
    · intro h
      apply hx
      exact ⟨σ.symm x, h, by simp⟩
    · simp

/-- If σ maps P to Q (i.e., σ '' P = Q), then σ⁻¹ maps Q to P. -/
lemma imageFinset_inv {n : ℕ} {σ : Equiv.Perm (Fin n)} {P Q : Finset (Fin n)}
    (h : imageFinset σ P = Q) : imageFinset σ⁻¹ Q = P := by
  simp only [imageFinset] at h ⊢
  rw [← h]
  ext x
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    rw [← hzy] at hyx
    have : σ⁻¹ (σ z) = z := σ.symm_apply_apply z
    rw [this] at hyx
    rw [← hyx]
    exact hz
  · intro hx
    refine ⟨σ x, ⟨x, hx, rfl⟩, ?_⟩
    exact σ.symm_apply_apply x

/-- The set of permutations that map P to Q. -/
def permsMapping {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => imageFinset σ P = Q)

/-- If |P| ≠ |Q|, no permutation maps P to Q. -/
theorem permsMapping_empty_of_card_ne {n : ℕ} (P Q : Finset (Fin n))
    (h : P.card ≠ Q.card) : permsMapping P Q = ∅ := by
  simp only [permsMapping, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  intro σ heq
  rw [← imageFinset_card σ P, heq] at h
  exact h rfl

end PermFinset

/-!
## Submatrix Determinant API

This section provides a unified API for submatrix determinants, bridging the
definitions in `CauchyBinet.lean` and `DesnanotJacobi.lean`.

### Definitions across the codebase

There are currently two styles of submatrix determinant definitions:

1. **Proof-requiring version** (`AlgebraicCombinatorics.CauchyBinet.submatrixDet`):
   Requires a proof `h : P.card = Q.card` as an argument.
   ```
   def submatrixDet A P Q (h : P.card = Q.card) :=
     (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det
   ```

2. **Total version** (`AlgebraicCombinatorics.Determinants.submatrixDet`, `AlgebraicCombinatorics.CauchyBinet.minor`):
   Uses `if h : P.card = Q.card then ... else 0` to handle cardinality mismatch.
   ```
   def submatrixDet A P Q :=
     if h : P.card = Q.card then ... else 0
   ```

### Equivalence lemmas

The following lemmas establish equivalence between these definitions:

- `PermFinset.submatrixDet_of_card_eq`: When |P| = |Q|, unfolds to the determinant
- `PermFinset.submatrixDet_eq_proof_version`: Relates to the proof-requiring style
- `AlgebraicCombinatorics.CauchyBinet.submatrixDet_eq_permFinset`: CauchyBinet version equals PermFinset
- `AlgebraicCombinatorics.CauchyBinet.minor_eq_permFinset_submatrixDet`: CauchyBinet.minor equals PermFinset
- `AlgebraicCombinatorics.Determinants.submatrixDet_eq_permFinset`: Determinants version equals PermFinset

### Migration path

New code should use `PermFinset.submatrixDet` (the total version). Existing code
can use the equivalence lemmas above to convert between styles.
-/

namespace PermFinset

open Matrix Finset

variable {R : Type*} [CommRing R]

/-- The determinant of a submatrix corresponding to row set P and column set Q.
    Returns 0 if |P| ≠ |Q|.
    
    This is the canonical "total" definition that handles cardinality mismatch gracefully,
    avoiding the need for proof terms in most applications.
    
    This definition is equivalent to:
    - `CauchyBinet.minor` (same signature and semantics)
    - `Determinants.submatrixDet` in DesnanotJacobi.lean (uses `finsetToFin` instead of
      `orderEmbOfFin`, but these are equivalent)
    - `CauchyBinet.submatrixDet` when |P| = |Q| (that version requires a proof argument) -/
noncomputable def submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) : R :=
  if h : P.card = Q.card then
    (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det
  else 0

/-- When |P| = |Q|, the submatrix determinant equals the actual determinant.
    This lemma bridges the "total" definition with the "proof-requiring" style. -/
theorem submatrixDet_of_card_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) :
    submatrixDet A P Q = (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det := by
  simp only [submatrixDet, h, ↓reduceDIte]

/-- When |P| ≠ |Q|, the submatrix determinant is 0. -/
theorem submatrixDet_of_card_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card ≠ Q.card) :
    submatrixDet A P Q = 0 := by
  simp only [submatrixDet, h, ↓reduceDIte]

/-- The submatrix determinant of the empty sets is 1. -/
@[simp]
theorem submatrixDet_empty {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    submatrixDet A ∅ ∅ = 1 := by
  simp only [submatrixDet, Finset.card_empty, ↓reduceDIte]
  exact Matrix.det_isEmpty

/-- `PermFinset.submatrixDet` equals the proof-requiring version when |P| = |Q|.
    
    Use this lemma to convert between:
    - `PermFinset.submatrixDet A P Q` (total, returns 0 when |P| ≠ |Q|)
    - `(A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin _)).det` (requires proof)
    
    This establishes the equivalence with `CauchyBinet.submatrixDet`. -/
theorem submatrixDet_eq_proof_version {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) :
    submatrixDet A P Q = (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det :=
  submatrixDet_of_card_eq A P Q h

end PermFinset
