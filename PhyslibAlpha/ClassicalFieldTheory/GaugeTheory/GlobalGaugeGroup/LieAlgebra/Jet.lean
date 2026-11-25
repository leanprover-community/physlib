/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Basic
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Matrix
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Taylor
/-!
# The Lie algebra jets of a global gauge group

The Taylor series at a point of the infinitesimal gauge transformations.

## i. Overview

An infinitesimal gauge transformation of a global gauge group `G` with Lie algebra `𝔤` is a
smooth map from spacetime into `𝔤`. Its jet at the base point is a matrix of formal power
series in the spacetime coordinates, all of whose base-point derivatives `∂_s A (0)` lie in
`𝔤`. These Lie algebra jets form a Lie algebra under the commutator, since by the Leibniz
rule each base-point derivative of a commutator is a sum of commutators of base-point
derivatives.

Membership is checked through `mem_jetLieAlgebra_of`: a property of matrices of jets that is
preserved by every derivative, and that places the value in `𝔤`, places every base-point
derivative in `𝔤`.

This is how conjugation `A ↦ U⁻¹ A U` by an invertible matrix of jets `U` is shown to
preserve the Lie algebra jets, when the value of `U` lies in the group and `(∂_μ U) U⁻¹` is a
Lie algebra jet. At the base point it is the adjoint action of the group, and the derivative
of `U⁻¹ A U` is `U⁻¹ (∂_μ A − [(∂_μ U) U⁻¹, A]) U`, again of the same form. These are the
facts that make the jet gauge group of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.GaugeJetGroup` a group.

Being a Lie algebra jet is a condition on each Taylor coefficient separately, since the
base-point derivative along `s` is `s!` times the coefficient of `x^s`. So any Taylor data in
`𝔤` give a Lie algebra jet. A matrix of jets `W` solving the linear radial system
`E W + W = B + R W − W R`, for Lie algebra jets `B` and `R` with `R` vanishing at the base
point, is a Lie algebra jet. Here `E = ∑_ρ x_ρ ∂_ρ` is the Euler operator, which multiplies
the coefficient of degree `n` by `n`, so the coefficient of `W` of degree `n` is `1/(n + 1)`
times that of `B` plus commutators of coefficients of `R` with coefficients of `W` of lower
degree. This is how the radial transport of a Lie algebra jet is shown to be a gauge jet.

## ii. Key results

- `GlobalGaugeGroup.jetLieAlgebra` : the Lie algebra jets, as a real subspace.
- `GlobalGaugeGroup.mem_jetLieAlgebra_iff` : a matrix of jets is a Lie algebra jet exactly
  when its value lies in the Lie algebra and its derivatives are Lie algebra jets.
- `GlobalGaugeGroup.mem_jetLieAlgebra_of` : the induction principle for Lie algebra jets.
- `GlobalGaugeGroup.jetLieSubalgebra` : the Lie algebra jets, as a Lie subalgebra.
- `GlobalGaugeGroup.inv_mul_mul_mem_jetLieAlgebra` : conjugation by an invertible matrix of
  jets with value in the group and `(∂_μ U) U⁻¹` a Lie algebra jet preserves the Lie algebra
  jets.
- `GlobalGaugeGroup.taylorMatrix_mem_jetLieAlgebra` : Taylor data in the Lie algebra give a
  Lie algebra jet.
- `GlobalGaugeGroup.mem_jetLieAlgebra_of_euler` : a solution of the linear radial system
  `E W + W = B + R W − W R` with `B`, `R` Lie algebra jets is a Lie algebra jet.

## iii. Table of contents

- A. The Lie algebra jets
- B. Closure properties
- C. Conjugation by invertible matrices of jets
- D. Taylor coefficients and the radial system

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The Lie algebra jets

-/

/-- The real subspace of matrices of jets all of whose base-point derivatives lie in the
  Lie algebra. -/
def jetLieAlgebra : Submodule ℝ (Matrix κ κ SpaceTimeAlgebra) where
  carrier := {A | ∀ s, derivValueMatrix s A ∈ G.lieAlgebra}
  add_mem' hA hB s := by
    rw [derivValueMatrix_add]
    exact add_mem (hA s) (hB s)
  zero_mem' s := by
    rw [derivValueMatrix_zero_right]
    exact G.lieAlgebra.zero_mem
  smul_mem' r A hA s := by
    rw [derivValueMatrix_real_smul]
    exact G.lieAlgebra.smul_mem r (hA s)

lemma mem_jetLieAlgebra {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔ ∀ s, derivValueMatrix s A ∈ G.lieAlgebra := Iff.rfl

/-- A matrix of jets is a Lie algebra jet exactly when its value lies in the Lie algebra and
  its derivatives are Lie algebra jets. -/
lemma mem_jetLieAlgebra_iff {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra ∧
        ∀ μ, A.map (pderiv μ) ∈ G.jetLieAlgebra := by
  refine ⟨fun hA => ⟨hA 0, fun μ s => derivValueMatrix_cons μ s A ▸ hA (μ ::ₘ s)⟩,
    fun ⟨h0, hd⟩ s => ?_⟩
  induction s using Multiset.induction_on with
  | empty => exact h0
  | cons μ t _ => exact (derivValueMatrix_cons μ t A).symm ▸ hd μ t

/-- An induction principle for Lie algebra jets. A property of matrices of jets that is
  preserved by every derivative, and that forces the value into the Lie algebra, forces
  every base-point derivative into the Lie algebra. -/
lemma mem_jetLieAlgebra_of {P : Matrix κ κ SpaceTimeAlgebra → Prop}
    (h0 : ∀ A, P A → (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra)
    (hd : ∀ A, P A → ∀ μ, P (A.map (pderiv μ))) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : P A) : A ∈ G.jetLieAlgebra := by
  intro s
  induction s using Multiset.induction_on generalizing A with
  | empty => exact h0 A hA
  | cons μ t ih => exact (derivValueMatrix_cons μ t A).symm ▸ ih (hd A hA μ)

/-!

## B. Closure properties

-/

lemma map_pderiv_mem_jetLieAlgebra {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (μ : Fin 1 ⊕ Fin 3) : A.map (pderiv μ) ∈ G.jetLieAlgebra :=
  (G.mem_jetLieAlgebra_iff.1 hA).2 μ

/-- The Lie algebra jets are closed under the commutator. By the Leibniz rule each
  base-point derivative of a commutator is a sum of commutators of base-point derivatives. -/
lemma commutator_mem_jetLieAlgebra {A B : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (hB : B ∈ G.jetLieAlgebra) : A * B - B * A ∈ G.jetLieAlgebra := by
  intro s
  induction s using Multiset.induction_on generalizing A B with
  | empty =>
    rw [derivValueMatrix_zero, map_sub, map_mul, map_mul]
    exact commutator_mem_lieAlgebraOfIsClosed (hA 0) (hB 0)
  | cons μ t ih =>
    rw [derivValueMatrix_cons, map_pderiv_commutator, derivValueMatrix_add]
    exact add_mem (ih (G.map_pderiv_mem_jetLieAlgebra hA μ) hB)
      (ih hA (G.map_pderiv_mem_jetLieAlgebra hB μ))

/-- The Lie algebra jets, as a Lie subalgebra of matrices of jets under the commutator. -/
def jetLieSubalgebra : LieSubalgebra ℝ (Matrix κ κ SpaceTimeAlgebra) where
  toSubmodule := G.jetLieAlgebra
  lie_mem' hA hB := by
    rw [Ring.lie_def]
    exact G.commutator_mem_jetLieAlgebra hA hB

@[simp]
lemma mem_jetLieSubalgebra {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieSubalgebra ↔ A ∈ G.jetLieAlgebra := Iff.rfl

noncomputable instance : AddCommGroup G.jetLieSubalgebra := inferInstance

noncomputable instance : Module ℝ G.jetLieSubalgebra := inferInstance

noncomputable instance : LieRing G.jetLieSubalgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.jetLieSubalgebra := inferInstance

/-- A constant matrix in the Lie algebra is a Lie algebra jet. -/
lemma mapMatrix_C_mem_jetLieAlgebra {a : Matrix κ κ ℂ} (ha : a ∈ G.lieAlgebra) :
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_iff.2 ⟨?_, fun μ => ?_⟩
  · convert ha
    ext i j
    simp [RingHom.mapMatrix_apply, constantCoeff_C]
  · rw [map_pderiv_mapMatrix_C]
    exact G.jetLieAlgebra.zero_mem

/-- The Lie algebra jets are closed under multiplication by a coordinate. -/
lemma X_smul_mem_jetLieAlgebra (μ : Fin 1 ⊕ Fin 3) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) : (X μ : SpaceTimeAlgebra) • A ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_of (P := fun D => ∃ A ∈ G.jetLieAlgebra, ∃ B ∈ G.jetLieAlgebra,
      D = (X μ : SpaceTimeAlgebra) • A + B)
    ?_ ?_ ⟨A, hA, 0, G.jetLieAlgebra.zero_mem, (add_zero _).symm⟩
  · rintro _ ⟨A, -, B, hB, rfl⟩
    have h : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix
        ((X μ : SpaceTimeAlgebra) • A) = 0 := by
      ext i j
      simp [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [map_add, h, zero_add]
    exact hB 0
  · rintro _ ⟨A, hA, B, hB, rfl⟩ ν
    refine ⟨A.map (pderiv ν), G.map_pderiv_mem_jetLieAlgebra hA ν,
      (if ν = μ then A else 0) + B.map (pderiv ν),
      add_mem (by split_ifs <;> simp [hA]) (G.map_pderiv_mem_jetLieAlgebra hB ν), ?_⟩
    ext i j
    by_cases h : ν = μ
    · subst h
      simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_self]
      ring
    · simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_of_ne (Ne.symm h), h]

/-!

## C. Conjugation by invertible matrices of jets

-/

/-- Conjugation `A ↦ U⁻¹ A U` preserves the Lie algebra jets, when the value of `U` lies in
  the group and `(∂_μ U) U⁻¹` is a Lie algebra jet. At the base point it is the adjoint
  action of the group, and the derivative of `U⁻¹ A U` is again of this form,
  `U⁻¹ (∂_μ A − [(∂_μ U) U⁻¹, A]) U`. -/
lemma inv_mul_mul_mem_jetLieAlgebra {U : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hU : unitsEval U ∈ G.group)
    (hω : ∀ μ, (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
      (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) ∈ G.jetLieAlgebra)
    {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetLieAlgebra) :
    (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) * A * U ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_of
    (P := fun D => ∃ A ∈ G.jetLieAlgebra, D = (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) * A * U)
    ?_ ?_ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    have h := conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed)
      ⟨(unitsEval U)⁻¹, inv_mem hU⟩ (hA 0)
    rw [derivValueMatrix_zero] at h
    rw [map_mul, map_mul, ← unitsEval_val, ← unitsEval_val, map_inv]
    show _ ∈ lieAlgebraOfIsClosed G.group G.isClosed
    simpa using h
  · rintro _ ⟨A, hA, rfl⟩ μ
    exact ⟨_, sub_mem (G.map_pderiv_mem_jetLieAlgebra hA μ)
      (G.commutator_mem_jetLieAlgebra (hω μ) hA),
      map_pderiv_conj_of_mul_eq_one μ U.mul_inv U.inv_mul A⟩

/-- The derivative of an inverse is a Lie algebra jet when the derivative of the matrix is. For
  an invertible matrix of jets `U` with value in the group and `(∂_μ U) U⁻¹` a Lie algebra jet,
  `(∂_μ U⁻¹) U = −U⁻¹ ((∂_μ U) U⁻¹) U` is a Lie algebra jet. -/
lemma map_pderiv_inv_mul_mem_jetLieAlgebra {U : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hU : unitsEval U ∈ G.group)
    (hω : ∀ μ, (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
      (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) ∈ G.jetLieAlgebra) (μ : Fin 1 ⊕ Fin 3) :
    (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) * (U : Matrix κ κ SpaceTimeAlgebra)
      ∈ G.jetLieAlgebra := by
  rw [map_pderiv_of_mul_eq_one μ U.mul_inv U.inv_mul, neg_mul,
    mul_assoc (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra)]
  exact neg_mem (G.inv_mul_mul_mem_jetLieAlgebra hU hω (hω μ))

/-- Conjugation `A ↦ U A U⁻¹` preserves the Lie algebra jets, when the value of `U` lies in
  the group and `(∂_μ U) U⁻¹` is a Lie algebra jet. -/
lemma mul_mul_inv_mem_jetLieAlgebra {U : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hU : unitsEval U ∈ G.group)
    (hω : ∀ μ, (U : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
      (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra) ∈ G.jetLieAlgebra)
    {A : Matrix κ κ SpaceTimeAlgebra} (hA : A ∈ G.jetLieAlgebra) :
    (U : Matrix κ κ SpaceTimeAlgebra) * A * (↑U⁻¹ : Matrix κ κ SpaceTimeAlgebra)
      ∈ G.jetLieAlgebra := by
  have h := G.inv_mul_mul_mem_jetLieAlgebra (U := U⁻¹) (by rw [map_inv]; exact inv_mem hU)
    (fun μ => by rw [inv_inv]; exact G.map_pderiv_inv_mul_mem_jetLieAlgebra hU hω μ) hA
  rwa [inv_inv] at h

/-!

## D. Taylor coefficients and the radial system

-/

/-- A matrix of jets is a Lie algebra jet exactly when each of its matrices of Taylor
  coefficients lies in the Lie algebra. -/
lemma mem_jetLieAlgebra_iff_coeff {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔ ∀ p, A.map (coeff p) ∈ G.lieAlgebra := by
  classical
  refine ⟨fun hA p => ?_, fun h s => ?_⟩
  · have h := hA (Finsupp.toMultiset p)
    rw [derivValueMatrix_eq_smul_map_coeff, Finsupp.toMultiset_toFinsupp] at h
    have hne : ((∏ ν, ((Finsupp.toMultiset p).count ν).factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)
    have h' := G.lieAlgebra.smul_mem
      ((∏ ν, ((Finsupp.toMultiset p).count ν).factorial : ℕ) : ℝ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h'
  · rw [derivValueMatrix_eq_smul_map_coeff]
    exact G.lieAlgebra.smul_mem _ (h _)

/-- The matrix of jets with base-point Taylor data in the Lie algebra is a Lie algebra jet. -/
lemma taylorMatrix_mem_jetLieAlgebra {c : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hc : ∀ s, c s ∈ G.lieAlgebra) : taylorMatrix c ∈ G.jetLieAlgebra := fun s => by
  rw [derivValueMatrix, map_constantCoeff_iteratedPDeriv_taylorMatrix]
  exact hc s

/-- The Taylor coefficient of `x^p` of the commutator `R W − W R` lies in the Lie algebra when
  `R` is a Lie algebra jet vanishing at the base point and the coefficients of `W` of degree
  less than that of `p` lie in the Lie algebra. -/
lemma map_coeff_commutator_mem_lieAlgebra {R W : Matrix κ κ SpaceTimeAlgebra}
    (hR : R ∈ G.jetLieAlgebra) (hR0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix R = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (hW : ∀ q, Finsupp.degree q < Finsupp.degree p → W.map (coeff q) ∈ G.lieAlgebra) :
    (R * W - W * R).map (coeff p) ∈ G.lieAlgebra := by
  have hsub : (R * W - W * R).map (coeff p) =
      (R * W).map (coeff p) - (W * R).map (coeff p) := by
    ext i j
    simp
  rw [hsub, map_coeff_mul, map_coeff_mul,
    Finsupp.sum_antidiagonal_swap p fun a b => W.map (coeff a) * R.map (coeff b),
    ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun x hx => ?_
  rcases eq_or_ne x.1 0 with h1 | h1
  · have hR00 : R.map (coeff x.1) = 0 := by
      rw [h1, show R.map (coeff 0) = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix R from
        Matrix.ext fun _ _ => coeff_zero_eq_constantCoeff_apply _, hR0]
    rw [hR00, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    exact zero_mem _
  · have h4 : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree p := by
      rw [← map_add, Finset.mem_antidiagonal.mp hx]
    have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
    exact commutator_mem_lieAlgebraOfIsClosed ((G.mem_jetLieAlgebra_iff_coeff.1 hR) x.1)
      (hW x.2 (by omega))

/-- A solution of a linear radial system built from Lie algebra jets is a Lie algebra jet. The
  system is `E W + W = B + R W − W R` for a matrix of jets `W`, where `B` and `R` are Lie
  algebra jets with `R` vanishing at the base point, and `E` is the Euler operator, which
  multiplies the coefficient of degree `n` by `n`. The coefficient of `W` of degree `n` is
  `1/(n + 1)` times that of `B` plus commutators with coefficients of `W` of lower degree, and
  lies in the Lie algebra by induction on `n`. -/
lemma mem_jetLieAlgebra_of_euler {W B R : Matrix κ κ SpaceTimeAlgebra}
    (hB : B ∈ G.jetLieAlgebra) (hR : R ∈ G.jetLieAlgebra)
    (hR0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix R = 0)
    (hW : ∑ ρ, (X ρ : SpaceTimeAlgebra) • W.map (pderiv ρ) + W = B + (R * W - W * R)) :
    W ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_iff_coeff.2 fun p => ?_
  induction h : Finsupp.degree p using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    -- The coefficient of `x^p` of the radial system.
    have hp : ((n : ℝ) + 1) • W.map (coeff p) =
        B.map (coeff p) + (R * W - W * R).map (coeff p) := by
      ext i j
      have := congrArg (fun M => coeff p (M i j)) hW
      simp only [Matrix.add_apply, map_add, coeff_sum_X_smul_map_pderiv, h] at this
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, Complex.real_smul]
      push_cast
      rw [← this]
      ring
    have hmem : ((n : ℝ) + 1) • W.map (coeff p) ∈ G.lieAlgebra := by
      rw [hp]
      exact add_mem ((G.mem_jetLieAlgebra_iff_coeff.1 hB) p)
        (G.map_coeff_commutator_mem_lieAlgebra hR hR0 fun q hq => ih _ (h ▸ hq) q rfl)
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h' := G.lieAlgebra.smul_mem ((n : ℝ) + 1)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h'

end GlobalGaugeGroup
