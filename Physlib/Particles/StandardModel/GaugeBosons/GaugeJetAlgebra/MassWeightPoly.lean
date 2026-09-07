/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.MassDim
/-!
# The mass-weight polynomial on the gauge-boson jet algebra

## i. Overview

The mass-weight scaling of
`Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.MassDim` records the mass
dimension of a homogeneous element in a scalar. Replacing that scalar by a formal variable
turns the scaling into a grading: the generator `∂_s A_μ^φ` is sent to `X ^ (2 + 2 |s|)`
times itself, the gauge field carrying mass weight two and each derivative two more.

The gauge-boson jet algebra is real, but the jet algebra of the Standard Model uses its
complexification `ℂ ⊗[ℝ] GaugeJetAlgebra`. So the grading is built in two steps: the
universal property of the symmetric algebra gives a real algebra map landing in
`Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra)` — a commutative target, so there is no side
condition — and the universal property of the tensor product extends it along the scalars
to `complexMassWeightPoly`, which is what the ambient theory sees.

## ii. Key results

- `GaugeJetAlgebra.massWeightPoly` : the mass-weight grading on the real jet algebra.
- `GaugeJetAlgebra.massWeightPoly_iteratedJetDeriv_ofA` : `∂_s A_μ^φ` is a monomial
  eigenvector of weight `2 + 2 |s|`.
- `GaugeJetAlgebra.complexMassWeightPoly` : the grading on the complexification.
- `GaugeJetAlgebra.complexMassWeightPoly_tmul_iteratedJetDeriv_ofA` : the generator lemma
  on the complexification.
- `GaugeJetAlgebra.complexMassWeightPoly_eval_one` : setting the variable to one recovers
  the element.

## iii. Table of contents

- A. The mass-weight polynomial of a component function
- B. The mass-weight polynomial on the real jet algebra
- C. The mass-weight polynomial on the complexification
- D. Recovering an element from its mass-weight polynomial

-/

@[expose] public section

namespace StandardModel

namespace GaugeJetAlgebra

open TensorProduct

/-!

## A. The mass-weight polynomial of a component function

-/

/-- The monomial map into polynomials over the complexified jet algebra, as a map of
  `ℝ`-modules rather than of `ℂ ⊗[ℝ] GaugeJetAlgebra`-modules. -/
noncomputable def monomialₗ (n : ℕ) :
    (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₗ[ℝ] Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra) :=
  (Polynomial.monomial n).restrictScalars ℝ

@[simp]
lemma monomialₗ_apply (n : ℕ) (x : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    monomialₗ n x = Polynomial.monomial n x := rfl

/-- A component function, viewed inside the complexified jet algebra: the generator
  `∂_s A_μ^φ` tensored with the scalar one. -/
noncomputable def ιComplex :
    GaugeBoson.JetComponentSpace →ₗ[ℝ] ℂ ⊗[ℝ] GaugeJetAlgebra :=
  Algebra.TensorProduct.includeRight.toLinearMap.comp
    (SymmetricAlgebra.ι ℝ GaugeBoson.JetComponentSpace)

@[simp]
lemma ιComplex_apply (x : GaugeBoson.JetComponentSpace) :
    ιComplex x = (1 : ℂ) ⊗ₜ[ℝ] SymmetricAlgebra.ι ℝ GaugeBoson.JetComponentSpace x := rfl

/-- The mass-weight polynomial of a component function: the linear map sending the symbol
  `∂_s A^φ` to `X ^ (2 + 2 |s|)` times itself, read off from the multiset basis of the real
  derivative symbols. -/
noncomputable def jetComponentPoly :
    GaugeBoson.JetComponentSpace →ₗ[ℝ] Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra) :=
  TensorProduct.lift (DerivAlgebraReal.basisMultiset.constr ℝ fun s =>
    (monomialₗ (2 + 2 * Multiset.card s)).comp
      (ιComplex.comp (TensorProduct.mk ℝ DerivAlgebraReal (Module.Dual ℝ GaugeBoson)
        (DerivAlgebraReal.basisMultiset s))))

/-- On the symbol `∂_s A^φ` the component map is the monomial of degree `2 + 2 |s|`: the
  gauge field contributes two and each derivative two more. -/
lemma jetComponentPoly_basisMultiset_tmul (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeBoson) :
    jetComponentPoly (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] φ) =
      Polynomial.monomial (2 + 2 * Multiset.card s)
        (ιComplex (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] φ)) := by
  rw [jetComponentPoly, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

/-!

## B. The mass-weight polynomial on the real jet algebra

-/

/-- The mass-weight polynomial on the gauge-boson jet algebra: the `ℝ`-algebra map sending
  a generator of mass weight `n` to `X ^ n` times its image in the complexification. It is
  `GaugeJetAlgebra.massWeightScale` with the scalar replaced by the formal variable `X`, and
  needs no side condition because the target is commutative. -/
noncomputable def massWeightPoly :
    GaugeJetAlgebra →ₐ[ℝ] Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra) := by
  exact SymmetricAlgebra.lift (R := ℝ) (M := GaugeBoson.JetComponentSpace)
    (A := Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra)) jetComponentPoly

/-- On a component function the mass-weight polynomial is the component-function map. -/
@[simp]
lemma massWeightPoly_ι (x : GaugeBoson.JetComponentSpace) :
    massWeightPoly (SymmetricAlgebra.ι ℝ GaugeBoson.JetComponentSpace x) =
      jetComponentPoly x := by
  rw [massWeightPoly, SymmetricAlgebra.lift_ι_apply]

/-- The generator `∂_s A_μ^φ` is a monomial eigenvector of mass weight `2 + 2 |s|`. -/
@[simp]
lemma massWeightPoly_iteratedJetDeriv_ofA (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    massWeightPoly (iteratedJetDeriv s (ofA μ φ)) =
      Polynomial.monomial (2 + 2 * Multiset.card s)
        ((1 : ℂ) ⊗ₜ[ℝ] iteratedJetDeriv s (ofA μ φ)) := by
  rw [iteratedJetDeriv_ofA, massWeightPoly_ι,
    show LagrangianTheory.dualRealJetAlgebraBasis s = DerivAlgebraReal.basisMultiset s from rfl,
    jetComponentPoly_basisMultiset_tmul, ιComplex_apply]

/-- The undifferentiated gauge field has mass weight two — mass dimension one. -/
lemma massWeightPoly_ofA (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    massWeightPoly (ofA μ φ) = Polynomial.monomial 2 ((1 : ℂ) ⊗ₜ[ℝ] ofA μ φ) := by
  have h := massWeightPoly_iteratedJetDeriv_ofA (0 : Multiset (Fin 1 ⊕ Fin 3)) μ φ
  rwa [iteratedJetDeriv_zero, LinearMap.id_apply, Multiset.card_zero, Nat.mul_zero,
    Nat.add_zero] at h

/-!

## C. The mass-weight polynomial on the complexification

-/

/-- The mass-weight polynomial on the complexified gauge-boson jet algebra: the `ℂ`-algebra
  map obtained from the real one by extending the scalars, the grading the jet algebra of
  the Standard Model sees on its gauge sector. -/
noncomputable def complexMassWeightPoly :
    (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₐ[ℂ] Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra) := by
  refine Algebra.TensorProduct.lift (R := ℝ) (S := ℂ) (A := ℂ) (B := GaugeJetAlgebra)
    (C := Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra))
    (Algebra.ofId ℂ (Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra))) massWeightPoly ?_
  intro x y
  exact Commute.all (S := Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra)) _ _

/-- On a pure tensor the complexified grading is the scalar times the real grading. -/
lemma complexMassWeightPoly_tmul (z : ℂ) (x : GaugeJetAlgebra) :
    complexMassWeightPoly (z ⊗ₜ[ℝ] x) =
      Polynomial.C (z ⊗ₜ[ℝ] (1 : GaugeJetAlgebra)) * massWeightPoly x := by
  rw [complexMassWeightPoly, Algebra.TensorProduct.lift_tmul]
  congr 1

set_option maxHeartbeats 400000 in
/-- The generator `∂_s A_μ^φ` of the complexified jet algebra, with any complex coefficient,
  is a monomial eigenvector of mass weight `2 + 2 |s|`. -/
@[simp]
lemma complexMassWeightPoly_tmul_iteratedJetDeriv_ofA (z : ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    complexMassWeightPoly (z ⊗ₜ[ℝ] iteratedJetDeriv s (ofA μ φ)) =
      Polynomial.monomial (2 + 2 * Multiset.card s)
        (z ⊗ₜ[ℝ] iteratedJetDeriv s (ofA μ φ)) := by
  rw [complexMassWeightPoly_tmul, massWeightPoly_iteratedJetDeriv_ofA,
    ← Polynomial.monomial_zero_left, Polynomial.monomial_mul_monomial, Nat.zero_add,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-!

## D. Recovering an element from its mass-weight polynomial

-/

/-- Setting the formal variable to one collapses the component map back to the component
  function it graded. The derivative monomials span, so it is enough to check this on the
  multiset basis. -/
lemma jetComponentPoly_eval_one (x : GaugeBoson.JetComponentSpace) :
    (jetComponentPoly x).eval 1 = ιComplex x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, Polynomial.eval_zero, map_zero]
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb, map_add]
  | tmul a φ =>
    have ha : a ∈ Submodule.span ℝ (Set.range DerivAlgebraReal.basisMultiset) := by
      rw [DerivAlgebraReal.basisMultiset.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      rw [jetComponentPoly_basisMultiset_tmul, Polynomial.eval_monomial, one_pow, mul_one]
    | zero => rw [TensorProduct.zero_tmul, map_zero, Polynomial.eval_zero, map_zero]
    | add b c _ _ hb hc =>
      rw [TensorProduct.add_tmul, map_add, Polynomial.eval_add, hb, hc, map_add]
    | smul c b _ hb =>
      rw [← TensorProduct.smul_tmul', map_smul, Polynomial.eval_smul, hb, map_smul]

set_option maxHeartbeats 400000 in
/-- Setting the formal variable to one recovers the original element, viewed in the
  complexification. -/
lemma massWeightPoly_eval_one (x : GaugeJetAlgebra) :
    (massWeightPoly x).eval 1 =
      Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ) (B := GaugeJetAlgebra) x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℝ (ℂ ⊗[ℝ] GaugeJetAlgebra)) 1
      fun b => Commute.one_right b).comp massWeightPoly =
      (Algebra.TensorProduct.includeRight :
        GaugeJetAlgebra →ₐ[ℝ] ℂ ⊗[ℝ] GaugeJetAlgebra) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun y => ?_)
    simp
    change Polynomial.eval₂ (RingHom.id _) 1 (jetComponentPoly y) = _
    rw [Polynomial.eval₂_id]
    simpa using jetComponentPoly_eval_one y
  exact AlgHom.congr_fun h x

/-- Setting the formal variable to one recovers the original element of the complexified
  jet algebra: the mass-weight pieces sum back to it. -/
lemma complexMassWeightPoly_eval_one (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    (complexMassWeightPoly y).eval 1 = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, Polynomial.eval_zero]
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb]
  | tmul z x =>
    rw [complexMassWeightPoly_tmul, Polynomial.eval_mul, Polynomial.eval_C,
      massWeightPoly_eval_one, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The mass-weight polynomial on the complexification is injective: an element is
  recovered from its graded pieces. -/
lemma complexMassWeightPoly_injective : Function.Injective complexMassWeightPoly := by
  intro x y h
  rw [← complexMassWeightPoly_eval_one x, ← complexMassWeightPoly_eval_one y, h]

end GaugeJetAlgebra

end StandardModel
