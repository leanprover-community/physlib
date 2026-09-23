/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
/-!
# Constructions of matrix representations

## i. Overview

The matrix representations of a jet gauge group are closed under the operations by which
a model-building table combines the representations of the factors of the gauge group:
the trivial (singlet) representation, the Kronecker (tensor) product of two
representations, and the conjugate of a representation. This file provides these three
constructions; the representations of the individual factors are built in
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors`.

## ii. Key results

- `MatrixRep.trivial` : the singlet representation on `Fin 1`.
- `MatrixRep.kron` : the Kronecker product of two matrix representations.
- `MatrixRep.conj` : the conjugate of a matrix representation.

## iii. Table of contents

- A. Matrices with an identity factor
- B. The trivial representation
- C. The Kronecker product
- D. The conjugate representation

-/

@[expose] public section

open TensorProduct MvPowerSeries Kronecker

namespace LocalGaugeData

namespace MatrixRep

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-!

## A. Matrices with an identity factor

Entrywise maps that send `0` to `0` pass through a Kronecker product with an identity
factor, whether or not they are multiplicative.

-/

section KroneckerLemmas

variable {α β : Type} {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]

omit [DecidableEq ι₁] in
lemma kronecker_one_map [MulZeroOneClass α] [MulZeroOneClass β] (φ : α → β) (h0 : φ 0 = 0)
    (A : Matrix ι₁ ι₁ α) :
    (A ⊗ₖ (1 : Matrix ι₂ ι₂ α)).map φ = (A.map φ) ⊗ₖ (1 : Matrix ι₂ ι₂ β) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp [h0]

omit [DecidableEq ι₂] in
lemma one_kronecker_map [MulZeroOneClass α] [MulZeroOneClass β] (φ : α → β) (h0 : φ 0 = 0)
    (B : Matrix ι₂ ι₂ α) :
    ((1 : Matrix ι₁ ι₁ α) ⊗ₖ B).map φ = (1 : Matrix ι₁ ι₁ β) ⊗ₖ (B.map φ) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp [h0]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
lemma kronecker_map_of_mul [Mul α] [Mul β] (φ : α → β) (hφ : ∀ a b, φ (a * b) = φ a * φ b)
    (A : Matrix ι₁ ι₁ α) (B : Matrix ι₂ ι₂ α) :
    (A ⊗ₖ B).map φ = (A.map φ) ⊗ₖ (B.map φ) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, hφ]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
lemma neg_kronecker [Mul α] [HasDistribNeg α] (A : Matrix ι₁ ι₁ α) (B : Matrix ι₂ ι₂ α) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, neg_mul]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
lemma kronecker_neg [Mul α] [HasDistribNeg α] (A : Matrix ι₁ ι₁ α) (B : Matrix ι₂ ι₂ α) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, mul_neg]

end KroneckerLemmas

/-!

## B. The trivial representation

-/

/-- **The trivial representation**: the one-dimensional singlet, on which every gauge jet
  acts as the identity and the gauge algebra by zero. -/
noncomputable def trivial : MatrixRep jets (Fin 1) where
  mat _ := 1
  mat_one := rfl
  mat_mul _ _ := (Matrix.one_mul 1).symm
  act := 0
  jetAct _ := 0
  jetAct_ofConstantLie _ := by simp
  jetAct_map_cc_foldl _ _ := by simp
  mat_map_pderiv _ _ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.one_apply, Matrix.zero_mul, neg_zero, Matrix.zero_apply]
    split_ifs <;> simp
  mat_mul_jetAct _ _ := by simp

/-!

## C. The Kronecker product

-/

variable {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

/-- **The Kronecker product** of two matrix representations: the gauge jets act by the
  Kronecker product of the two matrices of jets, the gauge algebra by the Kronecker sum
  of the two action matrices. -/
noncomputable def kron (R₁ : MatrixRep jets ι₁) (R₂ : MatrixRep jets ι₂) :
    MatrixRep jets (ι₁ × ι₂) where
  mat U := R₁.mat U ⊗ₖ R₂.mat U
  mat_one := by rw [R₁.mat_one, R₂.mat_one, Matrix.one_kronecker_one]
  mat_mul U V := by rw [R₁.mat_mul, R₂.mat_mul, Matrix.mul_kronecker_mul]
  act :=
    { toFun c := R₁.act c ⊗ₖ (1 : Matrix ι₂ ι₂ ℂ) + (1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ R₂.act c
      map_add' a b := by
        rw [map_add, map_add, Matrix.add_kronecker, Matrix.kronecker_add]
        abel
      map_smul' r c := by
        simp only [map_smul, RingHom.id_apply]
        rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add] }
  jetAct a := R₁.jetAct a ⊗ₖ (1 : Matrix ι₂ ι₂ JetRing) + (1 : Matrix ι₁ ι₁ JetRing) ⊗ₖ R₂.jetAct a
  jetAct_ofConstantLie c := by
    show R₁.jetAct _ ⊗ₖ 1 + 1 ⊗ₖ R₂.jetAct _ = (R₁.act c ⊗ₖ 1 + 1 ⊗ₖ R₂.act c).map C
    rw [R₁.jetAct_ofConstantLie, R₂.jetAct_ofConstantLie, Matrix.map_add _ (map_add C),
      kronecker_one_map _ (map_zero C), one_kronecker_map _ (map_zero C)]
  jetAct_map_cc_foldl p a := by
    show (R₁.jetAct a ⊗ₖ 1 + 1 ⊗ₖ R₂.jetAct a).map _ = R₁.act _ ⊗ₖ 1 + 1 ⊗ₖ R₂.act _
    rw [Matrix.map_add _ (fun x y => by rw [JetRing.foldl_pderiv_add, map_add]),
      kronecker_one_map _ (by simp), one_kronecker_map _ (by simp),
      R₁.jetAct_map_cc_foldl, R₂.jetAct_map_cc_foldl]
  mat_map_pderiv U μ := by
    have hleib : (R₁.mat U ⊗ₖ R₂.mat U).map (fun f => pderiv μ f)
        = ((R₁.mat U).map fun f => pderiv μ f) ⊗ₖ R₂.mat U
          + R₁.mat U ⊗ₖ ((R₂.mat U).map fun f => pderiv μ f) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.add_apply]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hleib, R₁.mat_map_pderiv, R₂.mat_map_pderiv, Matrix.add_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
      neg_kronecker, kronecker_neg, neg_add]
  mat_mul_jetAct U c := by
    show R₁.mat U ⊗ₖ R₂.mat U * (R₁.jetAct _ ⊗ₖ 1 + 1 ⊗ₖ R₂.jetAct _)
      = (R₁.jetAct _ ⊗ₖ 1 + 1 ⊗ₖ R₂.jetAct _) * (R₁.mat U ⊗ₖ R₂.mat U)
    rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul, Matrix.one_mul, R₁.mat_mul_jetAct, R₂.mat_mul_jetAct]

/-!

## D. The conjugate representation

-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The iterated formal derivative commutes with conjugation. -/
lemma foldl_pderiv_star (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ρ h) (star f) = star (x.foldl (fun h ρ => pderiv ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, JetRing.pderiv_star, ih, Multiset.foldl_cons]

/-- **The conjugate representation**: the gauge jets act by the entrywise conjugate matrix
  of jets, the gauge algebra by the entrywise conjugate action matrix. -/
noncomputable def conj (R : MatrixRep jets ι) : MatrixRep jets ι where
  mat U := (R.mat U).map (starRingEnd JetRing)
  mat_one := by rw [R.mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  mat_mul U V := by rw [R.mat_mul, Matrix.map_mul]
  act :=
    { toFun c := (R.act c).map (starRingEnd ℂ)
      map_add' a b := by rw [map_add, Matrix.map_add _ (map_add _)]
      map_smul' r c := by
        simp only [map_smul, RingHom.id_apply]
        exact Matrix.map_smul _ r (fun a => by
          show star (r • a) = r • star a
          rw [star_smul, star_trivial]) _ }
  jetAct a := (R.jetAct a).map (starRingEnd JetRing)
  jetAct_ofConstantLie c := by
    show ((R.jetAct _).map _) = ((R.act c).map _).map _
    rw [R.jetAct_ofConstantLie, Matrix.map_map, Matrix.map_map]
    congr 1
    funext z
    exact JetRing.star_C z
  jetAct_map_cc_foldl p a := by
    show ((R.jetAct a).map _).map _ = (R.act _).map _
    rw [← R.jetAct_map_cc_foldl, Matrix.map_map, Matrix.map_map]
    congr 1
    funext f
    show constantCoeff (p.foldl (fun h ρ => pderiv ρ h) (star f))
      = star (constantCoeff (p.foldl (fun h ρ => pderiv ρ h) f))
    rw [foldl_pderiv_star, JetRing.constantCoeff_star]
  mat_map_pderiv U μ := by
    show ((R.mat U).map _).map _ = -((R.jetAct _).map _ * (R.mat U).map _)
    rw [← Matrix.map_mul, ← Matrix.map_neg _ (map_neg _), ← R.mat_map_pderiv, Matrix.map_map,
      Matrix.map_map]
    congr 1
    funext f
    exact JetRing.pderiv_star μ f
  mat_mul_jetAct U c := by
    show (R.mat U).map _ * (R.jetAct _).map _ = (R.jetAct _).map _ * (R.mat U).map _
    rw [← Matrix.map_mul, ← Matrix.map_mul, R.mat_mul_jetAct]

end MatrixRep

end LocalGaugeData
