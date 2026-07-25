/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi

/-!
# Jacobi--Trudi with independent row and alphabet sizes

The original API in `PieriJacobiTrudi` uses one natural number both for the number
of rows of a skew partition and for the tableau alphabet.  This file starts the
compatibility-preserving generalization in which:

* `M` indexes rows and the Jacobi--Trudi matrix;
* `N` indexes tableau entries and polynomial variables.

The old definitions remain unchanged.  The `M = N` equivalences below make the
new API interoperable with them.
-/

open Finset BigOperators Matrix MvPolynomial

namespace SymmetricFunctions

variable {M N : ℕ} {R : Type*} [CommRing R]

/-- A semistandard tableau of an `M`-row skew shape with entries in `Fin N`. -/
structure SkewSSYTMN (N : ℕ) (s : SkewPartition M) where
  /-- The entries in each row, indexed by their offset from the inner shape. -/
  entries :
    (i : Fin M) → Fin (s.outer.parts i - s.inner.parts i) → Fin N
  /-- Entries weakly increase along rows. -/
  rowWeak :
    ∀ i : Fin M, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
      j ≤ k → entries i j ≤ entries i k
  /-- Entries strictly increase down adjacent rows whenever both cells exist. -/
  colStrict :
    ∀ i : Fin M, ∀ hi : i.val + 1 < M,
      ∀ k : Fin (s.outer.parts i - s.inner.parts i),
      ∀ _hcol :
        s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
          s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
      let k' := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
      ∀ hk' :
        k' <
          s.outer.parts ⟨i.val + 1, hi⟩ -
            s.inner.parts ⟨i.val + 1, hi⟩,
        entries i k < entries ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

namespace SkewSSYTMN

/-- Two generalized skew tableaux are equal when their entries are equal. -/
@[ext]
theorem ext {s : SkewPartition M} {T U : SkewSSYTMN N s}
    (h : T.entries = U.entries) : T = U := by
  cases T
  cases U
  simp only at h
  subst h
  rfl

/-- The monomial obtained by multiplying one variable for every tableau cell. -/
noncomputable def toMonomial {s : SkewPartition M} (T : SkewSSYTMN N s) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin M, ∏ k : Fin (s.outer.parts i - s.inner.parts i),
    X (T.entries i k)

end SkewSSYTMN

/-- An unrestricted filling of an `M`-row skew shape by letters in `Fin N`. -/
abbrev SkewFillingMN (N : ℕ) (s : SkewPartition M) :=
  (i : Fin M) → Fin (s.outer.parts i - s.inner.parts i) → Fin N

instance skewFillingMN_fintype (N : ℕ) (s : SkewPartition M) :
    Fintype (SkewFillingMN N s) :=
  inferInstance

/-- Row semistandardness for a generalized skew filling. -/
def isRowWeakMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  ∀ i : Fin M, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → f i j ≤ f i k

/-- Adjacent-row column strictness for a generalized skew filling. -/
def isColStrictMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  ∀ i : Fin M, ∀ hi : i.val + 1 < M,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    ∀ _hcol :
      s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
        s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    let k' := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' :
      k' <
        s.outer.parts ⟨i.val + 1, hi⟩ -
          s.inner.parts ⟨i.val + 1, hi⟩,
      f i k < f ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

/-- Semistandardness for a generalized skew filling. -/
def isSSYTFillingMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  isRowWeakMN s f ∧ isColStrictMN s f

instance isRowWeakMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isRowWeakMN s f) :=
  Fintype.decidableForallFintype

instance isColStrictMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isColStrictMN s f) :=
  Fintype.decidableForallFintype

instance isSSYTFillingMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isSSYTFillingMN s f) :=
  instDecidableAnd

/-- Turn a semistandard filling into a bundled generalized tableau. -/
def fillingToSkewSSYTMN {s : SkewPartition M} (f : SkewFillingMN N s)
    (hf : isSSYTFillingMN s f) : SkewSSYTMN N s where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- The finite collection of all generalized skew tableaux of a fixed shape. -/
noncomputable def skewSSYTMNFinset (N : ℕ) (s : SkewPartition M) :
    Finset (SkewSSYTMN N s) :=
  (Finset.univ.filter (isSSYTFillingMN s)).attach.map
    ⟨fun f => fillingToSkewSSYTMN f.1 (Finset.mem_filter.mp f.2).2,
      fun f g h => by
        apply Subtype.ext
        apply _root_.funext
        intro i
        apply _root_.funext
        intro k
        exact congrFun (congrFun (congrArg SkewSSYTMN.entries h) i) k⟩

/-- Every generalized skew tableau occurs in `skewSSYTMNFinset`. -/
theorem skewSSYTMNFinset_mem (s : SkewPartition M) (T : SkewSSYTMN N s) :
    T ∈ skewSSYTMNFinset N s := by
  simp only [skewSSYTMNFinset, Finset.mem_map, Finset.mem_attach, true_and,
    Subtype.exists]
  refine ⟨T.entries, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T.rowWeak, T.colStrict⟩
  · cases T
    rfl

/-- The skew Schur polynomial of an `M`-row shape in `N` variables. -/
noncomputable def skewSchurMN (N : ℕ) (s : SkewPartition M) :
    MvPolynomial (Fin N) R :=
  ∑ T ∈ skewSSYTMNFinset N s, T.toMonomial

/-- Complete homogeneous functions with the negative-index convention. -/
noncomputable def jacobiTrudiMatrixHMN (N : ℕ) (lam mu : Fin M → ℕ) :
    Matrix (Fin M) (Fin M) (MvPolynomial (Fin N) R) :=
  fun i j => hsymmExt (N := N) (R := R)
    ((lam i : ℤ) - (mu j : ℤ) - (i.val : ℤ) + (j.val : ℤ))

/-- At equal row and alphabet sizes, a generalized tableau is the original tableau. -/
def skewSSYTMNSelfEquiv (s : SkewPartition N) : SkewSSYTMN N s ≃ SkewSSYT s where
  toFun T :=
    { entries := T.entries
      rowWeak := T.rowWeak
      colStrict := T.colStrict }
  invFun T :=
    { entries := T.entries
      rowWeak := T.rowWeak
      colStrict := T.colStrict }
  left_inv T := by cases T; rfl
  right_inv T := by cases T; rfl

@[simp]
theorem skewSSYTMNSelfEquiv_entries (s : SkewPartition N) (T : SkewSSYTMN N s) :
    (skewSSYTMNSelfEquiv s T).entries = T.entries :=
  rfl

@[simp]
theorem skewSSYTMNSelfEquiv_toMonomial (s : SkewPartition N) (T : SkewSSYTMN N s) :
    SkewSSYT.toMonomial (R := R) (skewSSYTMNSelfEquiv s T) =
      T.toMonomial :=
  rfl

/-- The generalized skew Schur polynomial recovers the original API when `M = N`. -/
@[simp]
theorem skewSchurMN_self (s : SkewPartition N) :
    skewSchurMN (R := R) N s = skewSchur (R := R) s := by
  unfold skewSchurMN skewSchur
  apply Finset.sum_bij (fun T _ => skewSSYTMNSelfEquiv s T)
  · intro T _
    exact skewSSYTFinset_mem s (skewSSYTMNSelfEquiv s T)
  · intro T₁ _ T₂ _ h
    exact (skewSSYTMNSelfEquiv s).injective h
  · intro T hT
    refine ⟨(skewSSYTMNSelfEquiv s).symm T,
      skewSSYTMNFinset_mem s ((skewSSYTMNSelfEquiv s).symm T), ?_⟩
    exact (skewSSYTMNSelfEquiv s).apply_symm_apply T
  · intro T _
    exact (skewSSYTMNSelfEquiv_toMonomial (R := R) s T).symm

@[simp]
theorem jacobiTrudiMatrixHMN_self (lam mu : Fin N → ℕ) :
    jacobiTrudiMatrixHMN (R := R) N lam mu = jacobiTrudiMatrixH (R := R) lam mu :=
  rfl

end SymmetricFunctions
