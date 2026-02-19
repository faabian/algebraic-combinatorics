/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Skew-Symmetric Matrices

This file defines skew-symmetric matrices and proves basic properties.

A matrix A is skew-symmetric (also called antisymmetric) if A^T = -A.

## Main definitions

* `Matrix.IsSkewSymmetric`: A matrix A is skew-symmetric if A^T = -A.

## Main results

* `Matrix.IsSkewSymmetric.diag_eq_zero`: Diagonal entries of a skew-symmetric matrix are zero
  (in characteristic ≠ 2).
* `Matrix.IsSkewSymmetric.apply_neg`: For a skew-symmetric matrix, A i j = -A j i.
* `Matrix.IsSkewSymmetric.det_eq_zero_of_odd`: The determinant of an odd-dimensional
  skew-symmetric matrix is zero (in characteristic ≠ 2).

## Notes

This file provides basic infrastructure for skew-symmetric matrices. The Pfaffian of a
skew-symmetric matrix and Kasteleyn's formula for counting domino tilings would require
substantial additional infrastructure.

Note: Mathlib has `Matrix.IsSkewAdjoint J A` which is the more general notion of
A being skew-adjoint with respect to a bilinear form J (i.e., Aᵀ * J = -J * A).
Our `IsSkewSymmetric` is the special case where J = I, i.e., simply Aᵀ = -A.

## References

* [Horn-Johnson, Matrix Analysis] for skew-symmetric matrix properties
-/

/-! ## Skew-Symmetric Matrices -/

/-- A matrix A is skew-symmetric if A^T = -A. -/
def Matrix.IsSkewSymmetric {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    (A : Matrix n n R) : Prop :=
  A.transpose = -A

/-- Diagonal entries of a skew-symmetric matrix are zero (in characteristic ≠ 2). -/
theorem Matrix.IsSkewSymmetric.diag_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] [NoZeroDivisors R] [CharZero R]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (i : n) : A i i = 0 := by
  have h : A.transpose i i = (-A) i i := congrFun (congrFun hA i) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  -- h : A i i = -A i i
  -- This means 2 * A i i = 0
  have h2 : A i i = -A i i := h
  have h3 : A i i - (-A i i) = 0 := sub_eq_zero.mpr h2
  simp only [sub_neg_eq_add] at h3
  -- h3 : A i i + A i i = 0
  have h4 : (2 : R) * A i i = 0 := by rw [two_mul]; exact h3
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num : (2 : R) ≠ 0)

/-- For a skew-symmetric matrix, A i j = -A j i. -/
theorem Matrix.IsSkewSymmetric.apply_neg {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (i j : n) :
    A i j = -A j i := by
  have h : A.transpose j i = (-A) j i := congrFun (congrFun hA j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  exact h

/-- Skew-symmetry is preserved under reindexing. -/
theorem Matrix.IsSkewSymmetric.reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {R : Type*} [Ring R]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (e : n ≃ m) :
    Matrix.IsSkewSymmetric (A.reindex e e) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.reindex_apply,
             Matrix.submatrix_apply]
  have h : A.transpose (e.symm i) (e.symm j) = (-A) (e.symm i) (e.symm j) :=
    congrFun (congrFun hA (e.symm i)) (e.symm j)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  exact h

/-- Skew-symmetry is preserved under map when the map preserves negation. -/
theorem Matrix.IsSkewSymmetric.map {n : Type*} [Fintype n] [DecidableEq n]
    {R S : Type*} [Ring R] [Ring S]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A)
    (f : R → S) (hf : ∀ x, f (-x) = -f x) :
    Matrix.IsSkewSymmetric (A.map f) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply]
  have h : A.transpose i j = (-A) i j := congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h, hf]

/-- Skew-symmetry is preserved under scalar multiplication. -/
theorem Matrix.IsSkewSymmetric.smul {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (c : R) :
    Matrix.IsSkewSymmetric (c • A) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  have h : A.transpose i j = (-A) i j := congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h, mul_neg]

/-- The zero matrix is skew-symmetric. -/
theorem Matrix.IsSkewSymmetric.zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] : Matrix.IsSkewSymmetric (0 : Matrix n n R) := by
  unfold Matrix.IsSkewSymmetric
  simp only [Matrix.transpose_zero, neg_zero]

/-- The sum of skew-symmetric matrices is skew-symmetric. -/
theorem Matrix.IsSkewSymmetric.add {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A B : Matrix n n R}
    (hA : Matrix.IsSkewSymmetric A) (hB : Matrix.IsSkewSymmetric B) :
    Matrix.IsSkewSymmetric (A + B) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_add, hA, hB, neg_add]

/-- The negation of a skew-symmetric matrix is skew-symmetric. -/
theorem Matrix.IsSkewSymmetric.neg {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) :
    Matrix.IsSkewSymmetric (-A) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_neg, hA, neg_neg]

/-- The difference of two skew-symmetric matrices is skew-symmetric. -/
theorem Matrix.IsSkewSymmetric.sub {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A B : Matrix n n R}
    (hA : Matrix.IsSkewSymmetric A) (hB : Matrix.IsSkewSymmetric B) :
    Matrix.IsSkewSymmetric (A - B) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_sub, hA, hB, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

/-- The determinant of an odd-dimensional skew-symmetric matrix is zero.
    This follows from det(A) = det(Aᵀ) = det(-A) = (-1)^n det(A) = -det(A),
    hence 2 det(A) = 0, so det(A) = 0 (in characteristic ≠ 2). -/
theorem Matrix.IsSkewSymmetric.det_eq_zero_of_odd {n : ℕ} {R : Type*}
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) R)
    (hA : Matrix.IsSkewSymmetric A) : A.det = 0 := by
  have h1 : A.det = A.transpose.det := (Matrix.det_transpose A).symm
  have h2 : A.transpose.det = (-A).det := congrArg Matrix.det hA
  have h3 : (-A).det = (-1 : R) ^ (2 * n + 1) * A.det := by
    rw [Matrix.det_neg]
    simp only [Fintype.card_fin]
  have h4 : (-1 : R) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    simp only [neg_one_sq, one_pow, pow_one, one_mul]
  rw [h4] at h3
  have h5 : A.det = -A.det := by
    calc A.det = A.transpose.det := h1
    _ = (-A).det := h2
    _ = -1 * A.det := h3
    _ = -A.det := by ring
  have h6 : A.det + A.det = 0 := by
    have : A.det - (-A.det) = 0 := sub_eq_zero.mpr h5
    simp only [sub_neg_eq_add] at this
    exact this
  have h7 : (2 : R) * A.det = 0 := by rw [two_mul]; exact h6
  exact (mul_eq_zero.mp h7).resolve_left (by norm_num : (2 : R) ≠ 0)
