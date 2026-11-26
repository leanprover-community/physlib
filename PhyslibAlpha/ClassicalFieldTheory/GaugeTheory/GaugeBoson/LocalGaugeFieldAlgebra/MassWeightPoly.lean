/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.MassDim
/-!
# The mass-weight polynomial on the gauge-boson jet algebra

The mass-weight grading of the gauge-boson jet algebra, as an algebra map into polynomials.

## i. Overview

Replacing the scalar of a mass-weight scaling by a formal variable turns the scaling into a
grading. The generator `∂_s A_μ^φ` is sent to `X ^ (2 + 2 |s|)` times itself, the gauge field
carrying mass weight two and each derivative two more.

The gauge-boson jet algebra is real, but the jet algebra of the Standard Model uses its
complexification `ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G`. So the grading is built in two steps:
the universal property of the symmetric algebra gives a real algebra map landing in
`Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)`, a commutative target so that there is no
side condition, and the universal property of the tensor product extends it along the scalars
to `complexMassWeightPoly`, which is what the ambient theory sees.

Setting the formal variable to one recovers the element, and setting it to a real number `c`
on a component function gives the mass-weight scaling by `c`.

## ii. Key results

- `LocalGaugeFieldAlgebra.massWeightPoly` : the mass-weight grading on the real jet algebra.
- `LocalGaugeFieldAlgebra.massWeightPoly_iteratedJetDeriv_ofA` : `∂_s A_μ^φ` is a monomial
  eigenvector of weight `2 + 2 |s|`.
- `LocalGaugeFieldAlgebra.complexMassWeightPoly` : the grading on the complexification.
- `LocalGaugeFieldAlgebra.complexMassWeightPoly_tmul_iteratedJetDeriv_ofA` : the generator lemma
  on the complexification.
- `LocalGaugeFieldAlgebra.complexMassWeightPoly_eval_one` : setting the variable to one recovers
  the element.
- `LocalGaugeFieldAlgebra.jetComponentPoly_eval_algebraMap` : setting the variable to a real
  number `c` on a component function gives its mass-weight scaling by `c`.

## iii. Table of contents

- A. The mass-weight polynomial of a component function
- B. The mass-weight polynomial on the real jet algebra
- C. The mass-weight polynomial on the complexification
- D. Evaluating the mass-weight polynomial

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

namespace LocalGaugeFieldAlgebra

open TensorProduct

/-!

## A. The mass-weight polynomial of a component function

-/

/-- The monomial map into polynomials over the complexified jet algebra, as a map of
  `ℝ`-modules rather than of modules over the complexified jet algebra. -/
noncomputable def monomialₗ (n : ℕ) :
    (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) →ₗ[ℝ]
      Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :=
  (Polynomial.monomial n).restrictScalars ℝ

@[simp]
lemma monomialₗ_apply (n : ℕ) (x : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :
    (monomialₗ (G := G)) n x = Polynomial.monomial n x := rfl

/-- A component function, viewed inside the complexified jet algebra, the generator
  `∂_s A_μ^φ` tensored with the scalar one. -/
noncomputable def ιComplex :
    (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G :=
  Algebra.TensorProduct.includeRight.toLinearMap.comp
    (SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G))

@[simp]
lemma ιComplex_apply (x : (GaugeBoson.FieldDerivSpace G)) :
    (ιComplex (G := G)) x =
      (1 : ℂ) ⊗ₜ[ℝ] SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G) x := rfl

/-- The mass-weight polynomial of a component function, the linear map sending the symbol
  `∂_s A^φ` to `X ^ (2 + 2 |s|)` times itself, read off from the multiset basis of the real
  derivative symbols. -/
noncomputable def jetComponentPoly :
    (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ]
      Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :=
  TensorProduct.lift (SpaceTimeDerivAlgebraℝ.basisMultiset.constr ℝ fun s =>
    (monomialₗ (2 + 2 * Multiset.card s)).comp
      (ιComplex.comp (TensorProduct.mk ℝ SpaceTimeDerivAlgebraℝ
        (Module.Dual ℝ (GaugeBoson G)) (SpaceTimeDerivAlgebraℝ.basisMultiset s))))

/-- On the symbol `∂_s A^φ` the component map is the monomial of degree `2 + 2 |s|`. The
  gauge field contributes two and each derivative two more. -/
lemma jetComponentPoly_basisMultiset_tmul (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ (GaugeBoson G)) :
    (jetComponentPoly (G := G)) (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] φ) =
      Polynomial.monomial (2 + 2 * Multiset.card s)
        (ιComplex (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] φ)) := by
  rw [jetComponentPoly, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

/-!

## B. The mass-weight polynomial on the real jet algebra

-/

/-- The mass-weight polynomial on the gauge-boson jet algebra, the `ℝ`-algebra map sending
  a generator of mass weight `n` to `X ^ n` times its image in the complexification. It
  needs no side condition because the target is commutative. -/
noncomputable def massWeightPoly :
    LocalGaugeFieldAlgebra G →ₐ[ℝ]
      Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) := by
  exact SymmetricAlgebra.lift (R := ℝ) (M := (GaugeBoson.FieldDerivSpace G))
    (A := Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)) jetComponentPoly

/-- On a component function the mass-weight polynomial is the component-function map. -/
@[simp]
lemma massWeightPoly_ι (x : (GaugeBoson.FieldDerivSpace G)) :
    (massWeightPoly (G := G)) (SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G) x) =
      jetComponentPoly x := by
  rw [massWeightPoly, SymmetricAlgebra.lift_ι_apply]

/-- The generator `∂_s A_μ^φ` is a monomial eigenvector of mass weight `2 + 2 |s|`. -/
@[simp]
lemma massWeightPoly_iteratedJetDeriv_ofA (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (massWeightPoly (G := G)) (LocalGaugeFieldAlgebra.iteratedJetDeriv G s
        (LocalGaugeFieldAlgebra.ofA G μ φ)) =
      Polynomial.monomial (2 + 2 * Multiset.card s) ((1 : ℂ) ⊗ₜ[ℝ]
        LocalGaugeFieldAlgebra.iteratedJetDeriv G s
          (LocalGaugeFieldAlgebra.ofA G μ φ)) := by
  rw [LocalGaugeFieldAlgebra.iteratedJetDeriv_ofA, massWeightPoly_ι,
    jetComponentPoly_basisMultiset_tmul, ιComplex_apply]

/-!

## C. The mass-weight polynomial on the complexification

-/

/-- The mass-weight polynomial on the complexified gauge-boson jet algebra, the `ℂ`-algebra
  map obtained from the real one by extending the scalars, the grading the jet algebra of
  the Standard Model sees on its gauge sector. -/
noncomputable def complexMassWeightPoly :
    (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) →ₐ[ℂ]
      Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) := by
  refine Algebra.TensorProduct.lift (R := ℝ) (S := ℂ) (A := ℂ)
    (B := LocalGaugeFieldAlgebra G)
    (C := Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G))
    (Algebra.ofId ℂ (Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G))) massWeightPoly ?_
  intro x y
  exact Commute.all (S := Polynomial (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)) _ _

/-- On a pure tensor the complexified grading is the scalar times the real grading. -/
lemma complexMassWeightPoly_tmul (z : ℂ) (x : LocalGaugeFieldAlgebra G) :
    (complexMassWeightPoly (G := G)) (z ⊗ₜ[ℝ] x) =
      Polynomial.C (z ⊗ₜ[ℝ] (1 : LocalGaugeFieldAlgebra G)) * massWeightPoly x := by
  rw [complexMassWeightPoly, Algebra.TensorProduct.lift_tmul]
  congr 1

/-- The generator `∂_s A_μ^φ` of the complexified jet algebra, with any complex coefficient,
  is a monomial eigenvector of mass weight `2 + 2 |s|`. -/
@[simp]
lemma complexMassWeightPoly_tmul_iteratedJetDeriv_ofA (z : ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (complexMassWeightPoly (G := G)) (z ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.iteratedJetDeriv G s
        (LocalGaugeFieldAlgebra.ofA G μ φ)) =
      Polynomial.monomial (2 + 2 * Multiset.card s) (z ⊗ₜ[ℝ]
        LocalGaugeFieldAlgebra.iteratedJetDeriv G s
          (LocalGaugeFieldAlgebra.ofA G μ φ)) := by
  rw [complexMassWeightPoly_tmul, massWeightPoly_iteratedJetDeriv_ofA,
    ← Polynomial.monomial_zero_left, Polynomial.monomial_mul_monomial, Nat.zero_add,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-!

## D. Evaluating the mass-weight polynomial

-/

/-- Setting the formal variable to one collapses the component map back to the component
  function it graded. The derivative monomials span, so it is enough to check this on the
  multiset basis. -/
lemma jetComponentPoly_eval_one (x : (GaugeBoson.FieldDerivSpace G)) :
    ((jetComponentPoly (G := G)) x).eval 1 = ιComplex x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb, map_add]
  | tmul a φ =>
    have ha : a ∈ Submodule.span ℝ (Set.range SpaceTimeDerivAlgebraℝ.basisMultiset) := by
      rw [SpaceTimeDerivAlgebraℝ.basisMultiset.span_eq]
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

/-- Setting the formal variable to a real number `c` turns the component map into the
  mass-weight scaling by `c`. It is enough to check this on the multiset basis, where both
  sides are `c ^ (2 + 2 |s|)` times the symbol. -/
lemma jetComponentPoly_eval_algebraMap (c : ℝ) (x : GaugeBoson.FieldDerivSpace G) :
    ((jetComponentPoly (G := G)) x).eval (algebraMap ℝ _ c) =
      ιComplex (GaugeBoson.FieldDerivSpace.massWeightScale G c x) := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℝ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G))
      (algebraMap ℝ _ c) fun b => Commute.all _ _).toLinearMap ∘ₗ jetComponentPoly =
      ιComplex ∘ₗ GaugeBoson.FieldDerivSpace.massWeightScale G c :=
    TensorProduct.ext (SpaceTimeDerivAlgebraℝ.basisMultiset.ext fun s => LinearMap.ext fun φ => by
      change Polynomial.eval₂ (RingHom.id _) (algebraMap ℝ _ c)
        (jetComponentPoly (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] φ)) =
        ιComplex (GaugeBoson.FieldDerivSpace.massWeightScale G c
          (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] φ))
      rw [Polynomial.eval₂_id, jetComponentPoly_basisMultiset_tmul, Polynomial.eval_monomial,
        GaugeBoson.FieldDerivSpace.massWeightScale_tmul,
        SpaceTimeDerivAlgebraℝ.gradeScale_basisMultiset, ← TensorProduct.smul_tmul', smul_smul,
        ← pow_mul, ← pow_add, map_smul, ← map_pow]
      exact (mul_comm _ _).trans (Algebra.smul_def _ _).symm)
  exact LinearMap.congr_fun h x

/-- Setting the formal variable to one recovers the original element, viewed in the
  complexification. -/
lemma massWeightPoly_eval_one (x : LocalGaugeFieldAlgebra G) :
    ((massWeightPoly (G := G)) x).eval 1 =
      Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
        (B := LocalGaugeFieldAlgebra G) x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℝ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)) 1
      fun b => Commute.one_right b).comp massWeightPoly =
      (Algebra.TensorProduct.includeRight :
        LocalGaugeFieldAlgebra G →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun y => ?_)
    simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp, Function.comp_apply,
      massWeightPoly_ι, Algebra.TensorProduct.includeRight_apply]
    change Polynomial.eval₂ (RingHom.id _) 1 (jetComponentPoly y) = _
    rw [Polynomial.eval₂_id]
    simpa using jetComponentPoly_eval_one y
  exact AlgHom.congr_fun h x

/-- Setting the formal variable to one recovers the original element of the complexified
  jet algebra. The mass-weight pieces sum back to it. -/
lemma complexMassWeightPoly_eval_one (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :
    ((complexMassWeightPoly (G := G)) y).eval 1 = y := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb]
  | tmul z x =>
    rw [complexMassWeightPoly_tmul, Polynomial.eval_mul, Polynomial.eval_C,
      massWeightPoly_eval_one, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end LocalGaugeFieldAlgebra
