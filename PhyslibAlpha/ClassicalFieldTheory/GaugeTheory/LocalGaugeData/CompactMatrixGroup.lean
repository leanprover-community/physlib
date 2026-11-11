/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# The local gauge data of a compact matrix group

The jets of gauge transformations valued in any closed subgroup of a unitary group.

## i. Overview

A compact gauge group is presented here as a closed subgroup `G` of a unitary group `U(κ)`,
together with its Lie algebra `𝔤`: the real subspace of matrices `X` whose one-parameter
subgroup `t ↦ exp (t X)` lies in `G`. This is the definition of a gauge group used in the
Yang–Mills construction of the yang-mills-group (see references). The generators `X` are
anti-hermitian; the hermitian generators of physics are `−i X`.

The Lie algebra `𝔤` is closed under the commutator, since it is a closed subspace containing
the conjugates `exp (t X) Y exp (−t X)`, and so under their derivative `X Y − Y X` at
`t = 0`. It is invariant under conjugation by `G`.

The jets are matrices of formal power series in the spacetime coordinates:

* a Lie algebra jet is a matrix of jets all of whose base-point Taylor coefficients
  `∂_s A (0)` lie in `𝔤`;
* a gauge jet is a unitary matrix of jets `U` whose value `U (0)` lies in `G` and whose
  Maurer–Cartan form `(∂_μ U) U†` is a Lie algebra jet.

The second condition is the formal version of a smooth map into `G`: a map into `U(κ)`
starting in `G` stays in `G` exactly when its Maurer–Cartan form takes values in `𝔤`. That
the gauge jets form a group rests on conjugation `A ↦ U† A U` preserving the Lie algebra
jets. Its derivative is `U† (∂_μ A − [ω_μ, A]) U` with `ω_μ = (∂_μ U) U†`, again of the same
form, so every Taylor coefficient reduces to the value `g† a g` with `g ∈ G`, `a ∈ 𝔤`.

Every structure map is the matrix one, so the package is a presentation by matrices of jets
`CompactMatrixGroup.matrixJets`, and the laws of `LocalGaugeData` and its faithfulness come
from `PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets`.

## ii. Key results

- `CompactMatrixGroup` : a closed subgroup of a unitary group with its Lie algebra.
- `CompactMatrixGroup.commutator_mem_lieAlgebra` : the Lie algebra is closed under the
  commutator.
- `CompactMatrixGroup.jetLieAlgebra` : the Lie algebra jets.
- `CompactMatrixGroup.jetGroup` : the gauge jets.
- `CompactMatrixGroup.star_mul_mul_mem_jetSubmodule` : conjugation by a gauge jet preserves
  the Lie algebra jets.
- `CompactMatrixGroup.localGaugeData` : the local gauge data of a compact matrix group.

## iii. Table of contents

- A. Compact matrix groups and their Lie algebras
- B. Taylor coefficients of matrices of jets
- C. The Lie algebra jets
- D. The gauge jets
- E. The local gauge data

## iv. References

* yang-mills-group, *OpenAI-YM-20261028*, `PublicTheory.lean`, the structure `GaugeGroup`,
  https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean#L22-L33
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015),
  Theorem 3.20.

-/

@[expose] public section

open Matrix MvPowerSeries NormedSpace

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. Compact matrix groups and their Lie algebras

-/

/-- A compact matrix group: a closed subgroup `G` of the unitary group `U(κ)`, together with
  its Lie algebra, the real subspace of matrices `X` whose one-parameter subgroup
  `t ↦ exp (t X)` lies in `G`. The generators `X` are anti-hermitian; the hermitian
  generators of physics are `−i X`. -/
structure CompactMatrixGroup (κ : Type) [Fintype κ] [DecidableEq κ] where
  /-- The group, as a subgroup of the unitary group. -/
  group : Subgroup (unitaryGroup κ ℂ)
  /-- The group is closed in the unitary group, and so compact. -/
  isClosed : IsClosed (group : Set (unitaryGroup κ ℂ))
  /-- The Lie algebra, as a real subspace of matrices. -/
  lieAlgebra : Submodule ℝ (Matrix κ κ ℂ)
  /-- The Lie algebra consists exactly of the generators of one-parameter subgroups. -/
  mem_lieAlgebra_iff : ∀ X, X ∈ lieAlgebra ↔
    ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : group => (g.1.1 : Matrix κ κ ℂ)

namespace CompactMatrixGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : CompactMatrixGroup κ)

lemma exists_val_eq_exp {X : Matrix κ κ ℂ} (hX : X ∈ G.lieAlgebra) (t : ℝ) :
    ∃ g : G.group, g.1.1 = exp (t • X) :=
  (G.mem_lieAlgebra_iff X).1 hX t

/-- The Lie algebra is invariant under the adjoint action of the group: the one-parameter
  subgroup of `g X g⁻¹` is the conjugate by `g` of that of `X`. -/
lemma conj_mem_lieAlgebra (g : G.group) {X : Matrix κ κ ℂ} (hX : X ∈ G.lieAlgebra) :
    g.1.1 * X * star g.1.1 ∈ G.lieAlgebra := by
  set U : Matrix κ κ ℂ := g.1.1
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv (UnitaryGroup.star_mul_self g.1)
  have hunit : IsUnit U := (Unitary.toUnits g.1).isUnit
  refine (G.mem_lieAlgebra_iff _).2 fun t => ?_
  obtain ⟨h, hh⟩ := G.exists_val_eq_exp hX t
  refine ⟨g * h * g⁻¹, ?_⟩
  rw [← hinv, show t • (U * X * U⁻¹) = U * (t • X) * U⁻¹ by
    rw [mul_smul_comm, smul_mul_assoc], Matrix.exp_conj _ _ hunit, ← hh, hinv]
  rfl

/-- The one-parameter subgroup of a generator is unitary, so its inverse is
  `exp (t • -X) = star (exp (t • X))`. -/
lemma exp_smul_neg_eq_star {X : Matrix κ κ ℂ} (hX : X ∈ G.lieAlgebra) (t : ℝ) :
    exp (t • -X) = star (exp (t • X)) := by
  obtain ⟨g, hg⟩ := G.exists_val_eq_exp hX t
  rw [smul_neg, Matrix.exp_neg, ← hg]
  exact Matrix.inv_eq_left_inv (UnitaryGroup.star_mul_self g.1)

/-- The Lie algebra is closed under the commutator. The conjugates
  `exp (t X) Y exp (−t X)` lie in the Lie algebra, a closed subspace, and so does their
  derivative `X Y − Y X` at `t = 0`. -/
lemma commutator_mem_lieAlgebra {X Y : Matrix κ κ ℂ} (hX : X ∈ G.lieAlgebra)
    (hY : Y ∈ G.lieAlgebra) : X * Y - Y * X ∈ G.lieAlgebra := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set f : ℝ → Matrix κ κ ℂ := fun t => exp (t • X) * Y * exp (t • -X)
  have hf : HasDerivAt f (X * Y - Y * X) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg] at h
    rw [sub_eq_add_neg]
    exact h
  have hmem : ∀ t, f t ∈ G.lieAlgebra := fun t => by
    obtain ⟨g, hg⟩ := G.exists_val_eq_exp hX t
    simp only [f, G.exp_smul_neg_eq_star hX, ← hg]
    exact G.conj_mem_lieAlgebra g hY
  refine (Submodule.closed_of_finiteDimensional G.lieAlgebra).mem_of_tendsto
    hf.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  exact G.lieAlgebra.smul_mem _ (G.lieAlgebra.sub_mem (hmem _) (hmem _))

/-- The Lie algebra, as a Lie subalgebra of matrices under the commutator. -/
def lieSubalgebra : LieSubalgebra ℝ (Matrix κ κ ℂ) where
  toSubmodule := G.lieAlgebra
  lie_mem' hX hY := by
    rw [Ring.lie_def]
    exact G.commutator_mem_lieAlgebra hX hY

@[simp]
lemma mem_lieSubalgebra {X : Matrix κ κ ℂ} : X ∈ G.lieSubalgebra ↔ X ∈ G.lieAlgebra := Iff.rfl

noncomputable instance : LieRing G.lieSubalgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.lieSubalgebra := inferInstance

end CompactMatrixGroup

/-!

## B. Taylor coefficients of matrices of jets

-/

namespace SpaceTimeAlgebra

variable {κ : Type}

/-- The base-point value `∂_s A (0)` of the iterated derivative of a matrix of jets along
  the multiset of directions `s`, taken entrywise. -/
noncomputable def taylorCoeffMatrix (s : Multiset (Fin 1 ⊕ Fin 3))
    (A : Matrix κ κ SpaceTimeAlgebra) : Matrix κ κ ℂ :=
  A.map fun f => constantCoeff (iteratedPDeriv s f)

lemma taylorCoeffMatrix_cons (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (A : Matrix κ κ SpaceTimeAlgebra) :
    taylorCoeffMatrix (μ ::ₘ s) A = taylorCoeffMatrix s (A.map (pderiv μ)) := by
  ext i j
  simp [taylorCoeffMatrix]

lemma taylorCoeffMatrix_add (s : Multiset (Fin 1 ⊕ Fin 3)) (A B : Matrix κ κ SpaceTimeAlgebra) :
    taylorCoeffMatrix s (A + B) = taylorCoeffMatrix s A + taylorCoeffMatrix s B := by
  ext i j
  simp [taylorCoeffMatrix, iteratedPDeriv_add]

lemma taylorCoeffMatrix_real_smul (s : Multiset (Fin 1 ⊕ Fin 3)) (r : ℝ)
    (A : Matrix κ κ SpaceTimeAlgebra) :
    taylorCoeffMatrix s (r • A) = r • taylorCoeffMatrix s A := by
  ext i j
  simp only [taylorCoeffMatrix, Matrix.map_apply, Matrix.smul_apply]
  rw [← algebraMap_smul ℂ r, iteratedPDeriv_smul, MvPowerSeries.constantCoeff_smul,
    algebraMap_smul]

@[simp]
lemma taylorCoeffMatrix_zero_right (s : Multiset (Fin 1 ⊕ Fin 3)) :
    taylorCoeffMatrix s (0 : Matrix κ κ SpaceTimeAlgebra) = 0 := by
  ext i j
  simp [taylorCoeffMatrix]

variable [Fintype κ] [DecidableEq κ]

@[simp]
lemma taylorCoeffMatrix_zero (A : Matrix κ κ SpaceTimeAlgebra) :
    taylorCoeffMatrix 0 A = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A := rfl

/-- Evaluation of a unitary matrix of jets at the base point, entrywise. -/
noncomputable def unitaryEval : unitaryGroup κ SpaceTimeAlgebra →* unitaryGroup κ ℂ where
  toFun U := ⟨(constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1, by
    rw [mem_unitaryGroup_iff, ← mapMatrix_constantCoeff_star, ← map_mul,
      mem_unitaryGroup_iff.mp U.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' U V := Subtype.ext (map_mul _ U.1 V.1)

@[simp]
lemma unitaryEval_val (U : unitaryGroup κ SpaceTimeAlgebra) :
    (unitaryEval U).1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1 := rfl

/-- A constant unitary matrix as a unitary matrix of jets, entrywise. -/
noncomputable def unitaryOfConstant :
    unitaryGroup κ ℂ →* unitaryGroup κ SpaceTimeAlgebra where
  toFun g := ⟨(C : ℂ →+* SpaceTimeAlgebra).mapMatrix g.1, by
    rw [mem_unitaryGroup_iff, ← mapMatrix_C_star, ← map_mul, mem_unitaryGroup_iff.mp g.2,
      map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.1 h.1)

@[simp]
lemma unitaryOfConstant_val (g : unitaryGroup κ ℂ) :
    (unitaryOfConstant g).1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix g.1 := rfl

lemma unitaryEval_unitaryOfConstant (g : unitaryGroup κ ℂ) :
    unitaryEval (unitaryOfConstant g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]

lemma map_pderiv_mapMatrix_C (μ : Fin 1 ⊕ Fin 3) (A : Matrix κ κ ℂ) :
    ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix A).map (pderiv μ) = 0 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, pderiv_C]

omit [DecidableEq κ] in
/-- The derivative of a commutator of matrices of jets. -/
lemma map_pderiv_commutator (μ : Fin 1 ⊕ Fin 3) (A B : Matrix κ κ SpaceTimeAlgebra) :
    (A * B - B * A).map (pderiv μ) = (A.map (pderiv μ) * B - B * A.map (pderiv μ))
      + (A * B.map (pderiv μ) - B.map (pderiv μ) * A) := by
  rw [map_pderiv_sub, matrix_map_pderiv_mul, matrix_map_pderiv_mul]
  abel

/-- The derivative of the conjugate `U† A U` of a matrix of jets by a unitary matrix of jets,
  in terms of the Maurer–Cartan form `ω = (∂_μ U) U†`:
  `∂_μ (U† A U) = U† (∂_μ A − (ω A − A ω)) U`. -/
lemma map_pderiv_star_mul_mul (U : unitaryGroup κ SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3)
    (A : Matrix κ κ SpaceTimeAlgebra) :
    (star U.1 * A * U.1).map (pderiv μ) = star U.1 * (A.map (pderiv μ) -
      (U.1.map (pderiv μ) * star U.1 * A - A * (U.1.map (pderiv μ) * star U.1))) * U.1 := by
  have h1 : U.1 * star U.1 = 1 := mem_unitaryGroup_iff.mp U.2
  have h2 : star U.1 * U.1 = 1 := UnitaryGroup.star_mul_self U
  rw [matrix_map_pderiv_mul, matrix_map_pderiv_mul, map_pderiv_star_of_unitary μ h1 h2]
  simp only [mul_sub, sub_mul, add_mul, neg_mul, mul_assoc, h2, mul_one]
  abel

/-- The Maurer–Cartan cocycle law for matrices:
  `∂_μ (U V) (U V)† = (∂_μ U) U† + U ((∂_μ V) V†) U†`. -/
lemma mcMatrix_mul (U V : unitaryGroup κ SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3) :
    (U * V).1.map (pderiv μ) * star (U * V).1 = U.1.map (pderiv μ) * star U.1
      + U.1 * (V.1.map (pderiv μ) * star V.1) * star U.1 := by
  have hV : V.1 * star V.1 = 1 := mem_unitaryGroup_iff.mp V.2
  rw [Submonoid.coe_mul, matrix_map_pderiv_mul, star_mul, add_mul]
  congr 1
  · rw [mul_assoc, ← mul_assoc V.1, hV, one_mul]
  · simp only [mul_assoc]

end SpaceTimeAlgebra

open SpaceTimeAlgebra

namespace CompactMatrixGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : CompactMatrixGroup κ)

/-!

## C. The Lie algebra jets

-/

/-- The real subspace of matrices of jets all of whose base-point Taylor coefficients lie in
  the Lie algebra. -/
def jetSubmodule : Submodule ℝ (Matrix κ κ SpaceTimeAlgebra) where
  carrier := {A | ∀ s, taylorCoeffMatrix s A ∈ G.lieAlgebra}
  add_mem' hA hB s := by
    rw [taylorCoeffMatrix_add]
    exact add_mem (hA s) (hB s)
  zero_mem' s := by
    rw [taylorCoeffMatrix_zero_right]
    exact G.lieAlgebra.zero_mem
  smul_mem' r A hA s := by
    rw [taylorCoeffMatrix_real_smul]
    exact G.lieAlgebra.smul_mem r (hA s)

lemma mem_jetSubmodule {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetSubmodule ↔ ∀ s, taylorCoeffMatrix s A ∈ G.lieAlgebra := Iff.rfl

/-- A matrix of jets lies in `jetSubmodule` exactly when its value lies in the Lie algebra
  and its derivatives lie in `jetSubmodule`. -/
lemma mem_jetSubmodule_iff {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetSubmodule ↔
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra ∧
        ∀ μ, A.map (pderiv μ) ∈ G.jetSubmodule := by
  refine ⟨fun hA => ⟨hA 0, fun μ s => taylorCoeffMatrix_cons μ s A ▸ hA (μ ::ₘ s)⟩,
    fun ⟨h0, hd⟩ s => ?_⟩
  induction s using Multiset.induction_on with
  | empty => exact h0
  | cons μ t _ => exact (taylorCoeffMatrix_cons μ t A).symm ▸ hd μ t

/-- An induction principle for `jetSubmodule`: a property of matrices of jets that is
  preserved by every derivative, and that forces the value into the Lie algebra, forces
  every Taylor coefficient into the Lie algebra. -/
lemma mem_jetSubmodule_of {P : Matrix κ κ SpaceTimeAlgebra → Prop}
    (h0 : ∀ A, P A → (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra)
    (hd : ∀ A, P A → ∀ μ, P (A.map (pderiv μ))) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : P A) : A ∈ G.jetSubmodule := by
  intro s
  induction s using Multiset.induction_on generalizing A with
  | empty => exact h0 A hA
  | cons μ t ih => exact (taylorCoeffMatrix_cons μ t A).symm ▸ ih (hd A hA μ)

lemma map_pderiv_mem_jetSubmodule {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetSubmodule) (μ : Fin 1 ⊕ Fin 3) : A.map (pderiv μ) ∈ G.jetSubmodule :=
  (G.mem_jetSubmodule_iff.1 hA).2 μ

/-- The Lie algebra jets are closed under the commutator: by the Leibniz rule each Taylor
  coefficient of a commutator is a sum of commutators of Taylor coefficients. -/
lemma commutator_mem_jetSubmodule {A B : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetSubmodule) (hB : B ∈ G.jetSubmodule) : A * B - B * A ∈ G.jetSubmodule := by
  intro s
  induction s using Multiset.induction_on generalizing A B with
  | empty =>
    rw [taylorCoeffMatrix_zero, map_sub, map_mul, map_mul]
    exact G.commutator_mem_lieAlgebra (hA 0) (hB 0)
  | cons μ t ih =>
    rw [taylorCoeffMatrix_cons, map_pderiv_commutator, taylorCoeffMatrix_add]
    exact add_mem (ih (G.map_pderiv_mem_jetSubmodule hA μ) hB)
      (ih hA (G.map_pderiv_mem_jetSubmodule hB μ))

/-- The Lie algebra jets: matrices of jets with every base-point Taylor coefficient in the
  Lie algebra, under the commutator. -/
def jetLieAlgebra : LieSubalgebra ℝ (Matrix κ κ SpaceTimeAlgebra) where
  toSubmodule := G.jetSubmodule
  lie_mem' hA hB := by
    rw [Ring.lie_def]
    exact G.commutator_mem_jetSubmodule hA hB

@[simp]
lemma mem_jetLieAlgebra {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔ A ∈ G.jetSubmodule := Iff.rfl

noncomputable instance : LieRing G.jetLieAlgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.jetLieAlgebra := inferInstance

/-- A constant matrix in the Lie algebra is a Lie algebra jet. -/
lemma mapMatrix_C_mem_jetSubmodule {a : Matrix κ κ ℂ} (ha : a ∈ G.lieAlgebra) :
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a ∈ G.jetSubmodule := by
  refine G.mem_jetSubmodule_iff.2 ⟨?_, fun μ => ?_⟩
  · convert ha
    ext i j
    simp [RingHom.mapMatrix_apply, constantCoeff_C]
  · rw [map_pderiv_mapMatrix_C]
    exact G.jetSubmodule.zero_mem

/-- The Lie algebra jets are closed under multiplication by a coordinate. -/
lemma X_smul_mem_jetSubmodule (μ : Fin 1 ⊕ Fin 3) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetSubmodule) : (X μ : SpaceTimeAlgebra) • A ∈ G.jetSubmodule := by
  refine G.mem_jetSubmodule_of (P := fun D => ∃ A ∈ G.jetSubmodule, ∃ B ∈ G.jetSubmodule,
      D = (X μ : SpaceTimeAlgebra) • A + B)
    ?_ ?_ ⟨A, hA, 0, G.jetSubmodule.zero_mem, (add_zero _).symm⟩
  · rintro _ ⟨A, -, B, hB, rfl⟩
    have h : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix
        ((X μ : SpaceTimeAlgebra) • A) = 0 := by
      ext i j
      simp [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [map_add, h, zero_add]
    exact hB 0
  · rintro _ ⟨A, hA, B, hB, rfl⟩ ν
    refine ⟨A.map (pderiv ν), G.map_pderiv_mem_jetSubmodule hA ν,
      (if ν = μ then A else 0) + B.map (pderiv ν),
      add_mem (by split_ifs <;> simp [hA]) (G.map_pderiv_mem_jetSubmodule hB ν), ?_⟩
    ext i j
    by_cases h : ν = μ
    · subst h
      simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_self]
      ring
    · simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_of_ne (Ne.symm h), h]

/-!

## D. The gauge jets

-/

/-- A unitary matrix of jets is a gauge jet when its value lies in the group and its
  Maurer–Cartan form `(∂_μ U) U†` is a Lie algebra jet. -/
def IsJet (U : unitaryGroup κ SpaceTimeAlgebra) : Prop :=
  unitaryEval U ∈ G.group ∧ ∀ μ, U.1.map (pderiv μ) * star U.1 ∈ G.jetSubmodule

/-- Conjugation `A ↦ U† A U` by a gauge jet preserves the Lie algebra jets. At the base
  point it is the adjoint action of the group, and the derivative of `U† A U` is again of
  this form, `U† (∂_μ A − [ω_μ, A]) U`. -/
lemma star_mul_mul_mem_jetSubmodule {U : unitaryGroup κ SpaceTimeAlgebra} (hU : G.IsJet U)
    {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetSubmodule) :
    star U.1 * A * U.1 ∈ G.jetSubmodule := by
  refine G.mem_jetSubmodule_of (P := fun D => ∃ A ∈ G.jetSubmodule, D = star U.1 * A * U.1)
    ?_ ?_ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    have h := G.conj_mem_lieAlgebra ⟨(unitaryEval U)⁻¹, inv_mem hU.1⟩ (hA 0)
    rw [taylorCoeffMatrix_zero] at h
    rw [map_mul, map_mul, mapMatrix_constantCoeff_star]
    simpa using h
  · rintro _ ⟨A, hA, rfl⟩ μ
    exact ⟨_, sub_mem (G.map_pderiv_mem_jetSubmodule hA μ)
      (G.commutator_mem_jetSubmodule (hU.2 μ) hA), map_pderiv_star_mul_mul U μ A⟩

/-- The inverse of a gauge jet is a gauge jet: its Maurer–Cartan form is
  `−U† ((∂_μ U) U†) U`. -/
lemma isJet_inv {U : unitaryGroup κ SpaceTimeAlgebra} (hU : G.IsJet U) : G.IsJet U⁻¹ := by
  refine ⟨by rw [map_inv]; exact inv_mem hU.1, fun μ => ?_⟩
  have h1 : U.1 * star U.1 = 1 := mem_unitaryGroup_iff.mp U.2
  have h2 : star U.1 * U.1 = 1 := UnitaryGroup.star_mul_self U
  rw [UnitaryGroup.inv_val, map_pderiv_star_of_unitary μ h1 h2, star_star, neg_mul,
    mul_assoc (star U.1)]
  exact neg_mem (G.star_mul_mul_mem_jetSubmodule hU (hU.2 μ))

/-- Conjugation `A ↦ U A U†` by a gauge jet preserves the Lie algebra jets. -/
lemma mul_mul_star_mem_jetSubmodule {U : unitaryGroup κ SpaceTimeAlgebra} (hU : G.IsJet U)
    {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetSubmodule) :
    U.1 * A * star U.1 ∈ G.jetSubmodule := by
  have h := G.star_mul_mul_mem_jetSubmodule (G.isJet_inv hU) hA
  rwa [UnitaryGroup.inv_val, star_star] at h

/-- The product of gauge jets is a gauge jet, by the cocycle law of the Maurer–Cartan form. -/
lemma isJet_mul {U V : unitaryGroup κ SpaceTimeAlgebra} (hU : G.IsJet U) (hV : G.IsJet V) :
    G.IsJet (U * V) := by
  refine ⟨by rw [map_mul]; exact mul_mem hU.1 hV.1, fun μ => ?_⟩
  rw [mcMatrix_mul]
  exact add_mem (hU.2 μ) (G.mul_mul_star_mem_jetSubmodule hU (hV.2 μ))

/-- The jet of a constant gauge transformation is a gauge jet. -/
lemma isJet_unitaryOfConstant {g : unitaryGroup κ ℂ} (hg : g ∈ G.group) :
    G.IsJet (unitaryOfConstant g) := by
  refine ⟨by rw [unitaryEval_unitaryOfConstant]; exact hg, fun μ => ?_⟩
  rw [unitaryOfConstant_val, map_pderiv_mapMatrix_C, zero_mul]
  exact G.jetSubmodule.zero_mem

/-- The group of gauge jets: the unitary matrices of jets with value in the group and
  Maurer–Cartan form a Lie algebra jet. These are the Taylor series of smooth maps from
  spacetime into the group. -/
def jetGroup : Subgroup (unitaryGroup κ SpaceTimeAlgebra) where
  carrier := {U | G.IsJet U}
  one_mem' := by simpa using G.isJet_unitaryOfConstant G.group.one_mem
  mul_mem' hU hV := G.isJet_mul hU hV
  inv_mem' hU := G.isJet_inv hU

@[simp]
lemma mem_jetGroup {U : unitaryGroup κ SpaceTimeAlgebra} : U ∈ G.jetGroup ↔ G.IsJet U :=
  Iff.rfl

/-!

## E. The local gauge data

-/

/-- The presentation of the jets of a compact matrix group by matrices of jets. An element
  `X` of the Lie algebra is sent to its hermitian generator `−i X`, so that the commutator
  becomes the bracket `i (a b − b a)` of hermitian generators, and the Maurer–Cartan form
  `−(∂_μ U) U†` becomes `i (∂_μ U) U†`. -/
noncomputable def matrixJets :
    LocalGaugeData.MatrixJets κ G.group G.lieSubalgebra G.jetGroup G.jetLieAlgebra where
  toMat₀ := (unitaryGroup κ ℂ).subtype.comp G.group.subtype
  toMat₀_injective := Subtype.val_injective.comp Subtype.val_injective
  toMatJ := (unitaryGroup κ SpaceTimeAlgebra).subtype.comp G.jetGroup.subtype
  toMatJ_injective := Subtype.val_injective.comp Subtype.val_injective
  toMatJ_mul_star U := mem_unitaryGroup_iff.mp U.1.2
  star_toMatJ_mul U := UnitaryGroup.star_mul_self U.1
  lie₀ :=
    { toFun a := (-Complex.I) • (a : Matrix κ κ ℂ)
      map_add' a b := smul_add _ _ _
      map_smul' r a := smul_comm _ r _ }
  lie₀_injective a b h := Subtype.ext (smul_right_injective _ (by simp) h)
  lie₀_bracket a b := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieSubalgebra.coe_bracket, Ring.lie_def,
      smul_mul_smul_comm, ← smul_sub, smul_smul]
    congr 1
    linear_combination (-Complex.I) * Complex.I_mul_I
  lieJ :=
    { toFun A := (-Complex.I) • (A : Matrix κ κ SpaceTimeAlgebra)
      map_add' A B := smul_add _ _ _
      map_smul' r A := smul_comm _ r _ }
  lieJ_injective A B h := Subtype.ext (smul_right_injective _ (by simp) h)
  lieJ_bracket A B := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieSubalgebra.coe_bracket, Ring.lie_def,
      smul_mul_smul_comm, ← smul_sub, smul_smul]
    congr 1
    linear_combination (-Complex.I) * Complex.I_mul_I
  eval :=
    { toFun U := ⟨unitaryEval U.1, U.2.1⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' U V := Subtype.ext (map_mul _ _ _) }
  toMat₀_eval _ := rfl
  ofConstant :=
    { toFun g := ⟨unitaryOfConstant g.1, G.isJet_unitaryOfConstant g.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' g h := Subtype.ext (map_mul _ _ _) }
  toMatJ_ofConstant _ := rfl
  evalLie :=
    { toFun A := ⟨(constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1, A.2 0⟩
      map_add' A B := Subtype.ext (map_add _ _ _)
      map_smul' r A := Subtype.ext (Matrix.ext fun i j => constantCoeff_real_smul r _) }
  lie₀_evalLie A := (mapMatrix_constantCoeff_smul _ _).symm
  ofConstantLie :=
    { toFun a := ⟨(C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1,
        G.mapMatrix_C_mem_jetSubmodule a.2⟩
      map_add' a b := Subtype.ext (map_add _ _ _)
      map_smul' r a := Subtype.ext (Matrix.ext fun i j => C_real_smul r _) }
  lieJ_ofConstantLie a := (mapMatrix_C_smul _ _).symm
  deriv μ :=
    { toFun A := ⟨A.1.map (pderiv μ), G.map_pderiv_mem_jetSubmodule A.2 μ⟩
      map_add' A B := Subtype.ext (Matrix.ext fun i j =>
        map_add (pderiv μ) (A.1 i j) (B.1 i j))
      map_smul' r A := Subtype.ext (Matrix.ext fun i j => pderiv_real_smul μ r _) }
  lieJ_deriv μ A := (map_pderiv_smul μ _ _).symm
  coord μ :=
    { toFun A := ⟨(X μ : SpaceTimeAlgebra) • A.1, G.X_smul_mem_jetSubmodule μ A.2⟩
      map_add' A B := Subtype.ext (smul_add _ _ _)
      map_smul' r A := Subtype.ext (smul_comm _ r _) }
  lieJ_coord μ A := smul_comm _ _ _
  adjoint :=
    { toFun U :=
        { toFun A := ⟨U.1.1 * A.1 * star U.1.1, G.mul_mul_star_mem_jetSubmodule U.2 A.2⟩
          map_add' A B := Subtype.ext (by simp [mul_add, add_mul])
          map_smul' r A := Subtype.ext (by simp) }
      map_one' := LinearMap.ext fun A => Subtype.ext (by simp)
      map_mul' U V := LinearMap.ext fun A => Subtype.ext (by simp [star_mul, mul_assoc]) }
  lieJ_adjoint U A := by simp
  adjointValue :=
    { toFun g :=
        { toFun a := ⟨g.1.1 * a.1 * star g.1.1, G.conj_mem_lieAlgebra g a.2⟩
          map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
          map_smul' r a := Subtype.ext (by simp) }
      map_one' := LinearMap.ext fun a => Subtype.ext (by simp)
      map_mul' g h := LinearMap.ext fun a => Subtype.ext (by simp [star_mul, mul_assoc]) }
  lie₀_adjointValue g a := by simp
  maurerCartan U μ := ⟨-(U.1.1.map (pderiv μ) * star U.1.1), neg_mem (U.2.2 μ)⟩
  lieJ_maurerCartan U μ := by simp

/-- The local gauge data of a compact matrix group. The gauge jets are the unitary matrices
  of jets with value in the group and Maurer–Cartan form a Lie algebra jet, the Lie algebra
  jets are the matrices of jets with every Taylor coefficient in the Lie algebra, and every
  structure map is the matrix one. -/
noncomputable def localGaugeData :
    LocalGaugeData G.group G.lieSubalgebra G.jetGroup G.jetLieAlgebra :=
  G.matrixJets.toLocalGaugeData

@[simp]
lemma localGaugeData_eval_val (U : G.jetGroup) :
    (G.localGaugeData.eval U).1.1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1.1 :=
  rfl

@[simp]
lemma localGaugeData_ofConstant_val (g : G.group) :
    (G.localGaugeData.ofConstant g).1.1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix g.1.1 := rfl

@[simp]
lemma localGaugeData_evalLie_val (A : G.jetLieAlgebra) :
    (G.localGaugeData.evalLie A).1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1 :=
  rfl

@[simp]
lemma localGaugeData_ofConstantLie_val (a : G.lieSubalgebra) :
    (G.localGaugeData.ofConstantLie a).1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1 := rfl

@[simp]
lemma localGaugeData_deriv_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieAlgebra) :
    (G.localGaugeData.deriv μ A).1 = A.1.map (pderiv μ) := rfl

@[simp]
lemma localGaugeData_mulCoord_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieAlgebra) :
    (G.localGaugeData.mulCoord μ A).1 = (X μ : SpaceTimeAlgebra) • A.1 := rfl

@[simp]
lemma localGaugeData_adjointJ_val (U : G.jetGroup) (A : G.jetLieAlgebra) :
    (G.localGaugeData.adjointJ U A).1 = U.1.1 * A.1 * star U.1.1 := rfl

@[simp]
lemma localGaugeData_adjoint_val (g : G.group) (a : G.lieSubalgebra) :
    (G.localGaugeData.adjoint g a).1 = g.1.1 * a.1 * star g.1.1 := rfl

/-- The Maurer–Cartan form of a gauge jet is `−(∂_μ U) U†`, the anti-hermitian form of
  `i (∂_μ U) U†`. -/
@[simp]
lemma localGaugeData_maurerCartan_val (U : G.jetGroup) (μ : Fin 1 ⊕ Fin 3) :
    (G.localGaugeData.maurerCartan U μ).1 = -(U.1.1.map (pderiv μ) * star U.1.1) := rfl

/-- The local gauge data of a compact matrix group is faithful. -/
instance : G.localGaugeData.Faithful := G.matrixJets.faithful

end CompactMatrixGroup
