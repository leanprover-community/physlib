/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.Basic
public import Physlib.Relativity.Tensors.UnitTensor
/-!
# Invariants of a fundamental and an anti-fundamental index of `SU(N)`

## i. Overview

The invariant tensors of `SuT[N, .fund, .antiFund]` are the multiples of the Kronecker delta
`δᵃ_b`, the unit tensor `delta N` of the anti-fundamental color (A, B). The components of a
tensor with these indices form a matrix `C`, which `g` moves to `g C g⁻¹`, so the components of
an invariant tensor commute with every element of `SU(N)` and are scalar
(`SU.eq_smul_one_of_commute`).

For an equivariant map `f` out of these tensors, the invariants of `LinearMap.range f ⊔ S`, for
`S` a stable submodule, reduce to the line through `f (delta N)` (C). A family `T` of vectors
indexed by `Fin 2 → Fin N`, a fundamental index first, is the map `fundAntiFundMap T`, equivariant
exactly when `T` obeys the transformation law of the components (D), and `f (delta N)` is then
the contraction `∑ a, T ![a, a]`.

## ii. Key results

- `suTensor.delta` : the Kronecker delta.
- `suTensor.exists_eq_smul_delta_of_invariant` : the invariant tensors are its multiples.
- `suTensor.invariantReductionToDelta` : the reduction of the invariants of the span of a family
  to the delta contraction.

## iii. Table of contents

- A. The Kronecker delta
- B. The invariant tensors
- C. The invariants of an equivariant map
- D. Maps from components

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU

variable {N : ℕ}

/-!

## A. The Kronecker delta

-/

/-- The component indices of a tensor with a fundamental and an anti-fundamental index, as the
  pair of their labels. -/
def fundAntiFundIdx : ComponentIdx (S := suTensor N) ![.fund, .antiFund] ≃ (Fin 2 → Fin N) where
  toFun v := ![v 0, v 1]
  invFun v := fun | 0 => v 0 | 1 => v 1
  left_inv v := by
    funext x
    fin_cases x <;> rfl
  right_inv v := by
    funext x
    fin_cases x <;> rfl

variable (N) in
/-- The Kronecker delta `δᵃ_b`, the unit tensor of the anti-fundamental color, with a
  fundamental and an anti-fundamental index. -/
noncomputable def delta : SuT[N, .fund, .antiFund] := unitTensor (S := suTensor N) .antiFund

/-- The Kronecker delta is invariant. -/
lemma delta_invariant (g : SU N) : g • delta N = delta N :=
  actionT_fromConstPair ((suTensor N).unit .antiFund) g

/-- The components of the Kronecker delta. -/
lemma basis_repr_delta (n : Fin 2 → Fin N) :
    (Tensor.basis _).repr (delta N) (fundAntiFundIdx.symm n) = if n 0 = n 1 then 1 else 0 := by
  refine (unitTensor_basis_repr (S := suTensor N) .antiFund (fundAntiFundIdx.symm n)).trans ?_
  change (Module.Basis.tensorProduct (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))).repr
    ((1 : ℂ) • pairUnitVal N) (n 0, n 1) = _
  simp only [one_smul, pairUnitVal, map_sum, Module.Basis.tensorProduct_repr_tmul_apply,
    Pi.basisFun_repr, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq', eq_comm]

/-!

## B. The invariant tensors

-/

/-- The components of `g • t` for a tensor with a fundamental and an anti-fundamental index:
  the matrix of components `C` is moved to `g C g⁻¹`. -/
lemma basis_repr_smul_fundAntiFund (g : SU N) (t : SuT[N, .fund, .antiFund])
    (n : Fin 2 → Fin N) :
    (Tensor.basis _).repr (g • t) (fundAntiFundIdx.symm n)
      = ∑ x, ∑ y, g.1 (n 0) x * (g⁻¹).1 y (n 1)
        * (Tensor.basis _).repr t (fundAntiFundIdx.symm ![x, y]) := by
  rw [basis_repr_smul, ← fundAntiFundIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_two]
  congr 1
  change LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) _ _ *
    LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (antiFundRep N g) _ _ = _
  rw [toMatrix_fundRep, toMatrix_antiFundRep]
  rfl

/-- An invariant tensor with a fundamental and an anti-fundamental index is a multiple of the
  Kronecker delta: its matrix of components commutes with every element of `SU(N)`. -/
lemma exists_eq_smul_delta_of_invariant (t : SuT[N, .fund, .antiFund])
    (ht : ∀ g : SU N, g • t = t) : ∃ a : ℂ, t = a • delta N := by
  set C : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.of fun a b => (Tensor.basis _).repr t (fundAntiFundIdx.symm ![a, b])
  have hconj : ∀ g : SU N, g.1 * C * (g⁻¹).1 = C := fun g => by
    ext a b
    have h := basis_repr_smul_fundAntiFund g t ![a, b]
    rw [ht] at h
    simp only [Matrix.mul_apply, Finset.sum_mul, C, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans h.symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  obtain ⟨z, hz⟩ := eq_smul_one_of_commute (C := C) fun g => by
    conv_rhs => rw [← hconj g]
    simp only [Matrix.mul_assoc, val_inv_mul_val, Matrix.mul_one]
  refine ⟨z, (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)⟩
  obtain ⟨n, rfl⟩ := fundAntiFundIdx.symm.surjective φ
  rw [map_smul, Finsupp.smul_apply, basis_repr_delta, smul_eq_mul]
  have h := congrFun (congrFun hz (n 0)) (n 1)
  simp only [C, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [show (![n 0, n 1] : Fin 2 → Fin N) = n from by funext i; fin_cases i <;> rfl] at h
  rw [h, mul_ite, mul_one, mul_zero]

/-!

## C. The invariants of an equivariant map

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}
  {f : SuT[N, .fund, .antiFund] →ₗ[ℂ] B}

/-- For an equivariant map `f` out of the tensors with a fundamental and an anti-fundamental
  index, the invariants of the range of `f` reduce to the span of the image `f (delta N)` of the
  Kronecker delta. -/
noncomputable def invariantReductionToDeltaImage
    (hf : (suTensor N).IsEquivariant ![.fund, .antiFund] ρ f) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (isAdjointClosed N _) (delta N) delta_invariant
    exists_eq_smul_delta_of_invariant

/-!

## D. Maps from components

-/

/-- The linear map out of the tensors with a fundamental and an anti-fundamental index sending
  the basis tensor with labels `n` to `T n`. -/
noncomputable def fundAntiFundMap (T : (Fin 2 → Fin N) → B) :
    SuT[N, .fund, .antiFund] →ₗ[ℂ] B :=
  familyMap fundAntiFundIdx T

/-- The map of a family sends the Kronecker delta to the contraction `∑ a, T ![a, a]`. -/
lemma fundAntiFundMap_delta (T : (Fin 2 → Fin N) → B) :
    fundAntiFundMap T (delta N) = ∑ a, T ![a, a] := by
  conv_lhs => rw [← (Tensor.basis _).sum_repr (delta N)]
  rw [map_sum, ← fundAntiFundIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [fundAntiFundMap, basis_repr_delta]
  · intro b _ hb
    simp [fundAntiFundMap, basis_repr_delta, Ne.symm hb]
  · simp

/-- A linear map moving a family as `g` moves the components of a tensor with a fundamental and an
  anti-fundamental index intertwines the map of the family with the action of `g`: a factor of `g`
  on the first index and of its complex conjugate on the second, the summed index first. -/
lemma fundAntiFundMap_smul_of_law (T : (Fin 2 → Fin N) → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ l : Fin 2 → Fin N, σ (T l)
      = ∑ a : Fin 2 → Fin N, (g.1 (a 0) (l 0) * starRingEnd ℂ (g.1 (a 1) (l 1))) • T a)
    (t : SuT[N, .fund, .antiFund]) :
    σ (fundAntiFundMap T t) = fundAntiFundMap T (g • t) := by
  refine familyMap_smul_of_law _ T g (fun l => (hσ l).trans ?_) t
  refine Finset.sum_congr rfl fun a _ => congrArg (· • T a) ?_
  rw [Fin.prod_univ_two]
  change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) _ _
    * LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (antiFundRep N g) _ _
  rw [toMatrix_fundRep, toMatrix_antiFundRep, val_inv]
  rfl

/-- The map of a family is equivariant when the family moves as the components of a tensor
  with a fundamental and an anti-fundamental index. -/
lemma isEquivariant_fundAntiFundMap (T : (Fin 2 → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin 2 → Fin N), ρ g (T l)
      = ∑ a : Fin 2 → Fin N, (g.1 (a 0) (l 0) * starRingEnd ℂ (g.1 (a 1) (l 1))) • T a) :
    (suTensor N).IsEquivariant ![.fund, .antiFund] ρ (fundAntiFundMap T) :=
  ⟨fun g t => (fundAntiFundMap_smul_of_law T g (hT g) t).symm⟩

/-- For a family whose map is equivariant, the invariants of the span of the family reduce to
  the span of the delta contraction `∑ a, T ![a, a]`. -/
noncomputable def invariantReductionToDelta {T : (Fin 2 → Fin N) → B}
    (hT : (suTensor N).IsEquivariant ![.fund, .antiFund] ρ (fundAntiFundMap T)) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (isAdjointClosed N _) (delta N) delta_invariant
    exists_eq_smul_delta_of_invariant (range_familyMap _ T) _ (fundAntiFundMap_delta T)

end suTensor
