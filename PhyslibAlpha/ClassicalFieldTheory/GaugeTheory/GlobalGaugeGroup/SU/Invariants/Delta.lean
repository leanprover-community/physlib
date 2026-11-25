/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.Basic
public import Physlib.Relativity.Tensors.UnitTensor
/-!
# The Kronecker delta of `SU(N)`

Up to scale, the Kronecker delta is the only invariant tensor with a fundamental and an
anti-fundamental index.

## i. Overview

The invariant tensors of `SuT[N, .fund, .antiFund]` are the line through the Kronecker delta
`δᵃ_b`, the unit tensor `delta N` of the anti-fundamental color (A, B). The components of a
tensor with these indices form a matrix `C`, which `g` moves to `g C g⁻¹`, so the components of
an invariant tensor commute with every element of `SU(N)` and are scalar
(`SU.eq_smul_one_of_commute`).

A family `T` of vectors indexed by `Fin 2 → Fin N`, a fundamental index first, is the map
`liftComponents (T ∘ fundAntiFundIdx)`, equivariant exactly when `T` obeys the transformation law of
the components, and `f (delta N)` is then the contraction `∑ a, T ![a, a]`. The invariants of the
span of such a
family, modulo a stable submodule, reduce to the line through that contraction (C).

The invariants of `ℂᴺ ⊗ ℂᴺ` under the fundamental and the anti-fundamental representation are the
line through `∑ eᵢ ⊗ eᵢ` (D).

## ii. Key results

- `suTensor.delta` : the Kronecker delta.
- `suTensor.invariants_fund_antiFund_eq_span_delta` : the invariant tensors are the line through it.
- `suTensor.invariantReductionToDelta` : the reduction of the invariants of the span of a family
  to the delta contraction.
- `suTensor.invariants_tprod_eq_span_pairUnitVal` : the invariants of the fundamental times the
  anti-fundamental representation are the line through `∑ eᵢ ⊗ eᵢ`.

## iii. Table of contents

- A. The Kronecker delta
- B. The invariant tensors
- C. Maps from components
- D. The invariants of the tensor product

## iv. References

* None.

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies SU
open TensorSpecies.Tensor

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

/-- The components of `g • t` for a tensor with a fundamental and an anti-fundamental index.
  The matrix of components `C` is moved to `g C g⁻¹`. -/
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

/-- The invariant tensors with a fundamental and an anti-fundamental index are the line through
  the Kronecker delta. The matrix of components of an invariant tensor commutes with every element
  of `SU(N)`. -/
lemma invariants_fund_antiFund_eq_span_delta :
    ((suTensor N).tensorRep ![.fund, .antiFund]).invariants = ℂ ∙ delta N := by
  refine invariants_tensorRep_eq_span_singleton delta_invariant fun t ht => ?_
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

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-!

## C. Maps from components

-/

/-- The map of a family relabelled by `fundAntiFundIdx` sends the Kronecker delta to the
  contraction `∑ a, T ![a, a]`. -/
lemma liftComponents_delta (T : (Fin 2 → Fin N) → B) :
    liftComponents (T ∘ fundAntiFundIdx) (delta N) = ∑ a, T ![a, a] := by
  conv_lhs => rw [← (Tensor.basis _).sum_repr (delta N)]
  rw [map_sum, ← fundAntiFundIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [basis_repr_delta]
  · intro b _ hb
    simp [basis_repr_delta, Ne.symm hb]
  · simp

/-- A linear map moving a family as a group element moves the components of a tensor with a
  fundamental and an anti-fundamental index intertwines the map of the family with the action of
  that element. The element acts by one factor of itself on the first index and of its complex
  conjugate on the second, the summed index first. -/
lemma liftComponents_fundAntiFund_smul_of_law (T : (Fin 2 → Fin N) → B) {σ : B →ₗ[ℂ] B}
    (g : SU N) (hσ : ∀ l : Fin 2 → Fin N, σ (T l)
      = ∑ a : Fin 2 → Fin N, (g.1 (a 0) (l 0) * starRingEnd ℂ (g.1 (a 1) (l 1))) • T a)
    (t : SuT[N, .fund, .antiFund]) :
    σ (liftComponents (T ∘ fundAntiFundIdx) t) = liftComponents (T ∘ fundAntiFundIdx) (g • t) := by
  refine liftComponents_smul_of_law _ g (fun φ => (hσ _).trans ?_) t
  rw [← fundAntiFundIdx.sum_comp]
  refine Finset.sum_congr rfl fun ψ _ => congrArg (· • _) ?_
  rw [Fin.prod_univ_two]
  change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) _ _
    * LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (antiFundRep N g) _ _
  rw [toMatrix_fundRep, toMatrix_antiFundRep, val_inv]
  rfl

/-- The map of a family is equivariant when the family moves as the components of a tensor
  with a fundamental and an anti-fundamental index. -/
lemma isEquivariant_liftComponents_fundAntiFund (T : (Fin 2 → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin 2 → Fin N), ρ g (T l)
      = ∑ a : Fin 2 → Fin N, (g.1 (a 0) (l 0) * starRingEnd ℂ (g.1 (a 1) (l 1))) • T a) :
    (suTensor N).IsEquivariant ![.fund, .antiFund] ρ (liftComponents (T ∘ fundAntiFundIdx)) :=
  ⟨fun g t => (liftComponents_fundAntiFund_smul_of_law T g (hT g) t).symm⟩

/-- For a family whose map is equivariant, the invariants of the span of the family reduce to
  the span of the delta contraction `∑ a, T ![a, a]`. -/
noncomputable def invariantReductionToDelta {T : (Fin 2 → Fin N) → B}
    (hT : (suTensor N).IsEquivariant ![.fund, .antiFund] ρ (liftComponents (T ∘ fundAntiFundIdx))) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (hasReynolds N _) invariants_fund_antiFund_eq_span_delta
    (range_liftComponents_comp _ T) _ (liftComponents_delta T)

/-!

## D. The invariants of the tensor product

-/

/-- The Kronecker delta is the tensor of `∑ eᵢ ⊗ eᵢ`. -/
lemma delta_eq_fromPairT :
    delta N = fromPairT (S := suTensor N) (c1 := .fund) (c2 := .antiFund) (pairUnitVal N) := by
  change fromPairT (S := suTensor N) (c1 := .fund) (c2 := .antiFund) (antiFundUnit N 1) = _
  rw [antiFundUnit, unitOf_apply, one_smul]

/-- The invariants of `ℂᴺ ⊗ ℂᴺ` under the fundamental and the anti-fundamental representation are
  the line through `∑ eᵢ ⊗ eᵢ`. -/
lemma invariants_tprod_eq_span_pairUnitVal :
    ((fundRep N).tprod (antiFundRep N)).invariants = ℂ ∙ pairUnitVal N :=
  invariants_tprod_eq_span_singleton (S := suTensor N) (c1 := .fund) (c2 := .antiFund)
    (delta_eq_fromPairT (N := N) ▸ invariants_fund_antiFund_eq_span_delta)

end suTensor
