/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.TransformsIn
/-!
# The transformation law of the fermionic generators

## i. Overview

`FermionicAlgebra.repJetGaugeGroupI_ofField` records that the undifferentiated generator
`ψ_φ` transforms by the value of the gauge transformation at the base point. Its derivatives
do not: a jet of gauge transformations mixes `∂_s ψ_φ` with the lower generators
`∂_{s₂} ψ_φ`, weighted by the base-point Taylor coefficients `IsGaugeField.repDualCoeff` of
the gauge jet at the complementary multiset `s₁`. This file proves that all-orders Leibniz
law, in the form `StandardModel.TransformsIn` demands.

All the work is in `StandardModel.repDual_basis_tmul`, the corresponding statement on the
jet component space. The exterior algebra contributes only linearity: the generators are
the image of the component space under `ExteriorAlgebra.ι`, and a multiset sum passes
through a linear map.

The conjugate generators are the same statement for the conjugate action `repConj rep` on
the jets of the conjugate field, which is what the conjugate half of the component space
carries; so they are an instance of the same lemma, not a second proof.

## ii. Key results

- `FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField` : the transformation law of
  the derivative generators `∂_s ψ_φ`.
- `FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField` : the transformation
  law of the conjugate derivative generators `∂_s ψ̄_φ`.
- `FermionicAlgebra.transformsIn_iteratedJetDeriv_ofField`,
  `FermionicAlgebra.transformsIn_iteratedJetDeriv_ofConjField` : the same, packaged as
  `StandardModel.TransformsIn`.

## iii. Table of contents

- A. Multiset sums of generators
- B. The transformation law of the derivative generators
  - B.1. The field
  - B.2. The conjugate field

-/

@[expose] public section

namespace StandardModel

namespace FermionicAlgebra

open Matrix MatrixGroups TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. Multiset sums of generators

-/

/-- A multiset sum in the unconjugated half of the component space passes through the
  inclusion of the generators. -/
private lemma sum_inl (m : Multiset (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)) :
    ExteriorAlgebra.ι ℂ ((m.sum, 0) : JetComponentSpace V)
      = (m.map fun a => ExteriorAlgebra.ι ℂ ((a, 0) : JetComponentSpace V)).sum := by
  rw [show ExteriorAlgebra.ι ℂ ((m.sum, 0) : JetComponentSpace V)
      = ((ExteriorAlgebra.ι ℂ).comp
          (LinearMap.inl ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)
            (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)))) m.sum from rfl,
    map_multiset_sum]
  rfl

/-- A multiset sum in the conjugate half of the component space passes through the
  inclusion of the generators. -/
private lemma sum_inr (m : Multiset (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V))) :
    ExteriorAlgebra.ι ℂ ((0, m.sum) : JetComponentSpace V)
      = (m.map fun a => ExteriorAlgebra.ι ℂ ((0, a) : JetComponentSpace V)).sum := by
  rw [show ExteriorAlgebra.ι ℂ ((0, m.sum) : JetComponentSpace V)
      = ((ExteriorAlgebra.ι ℂ).comp
          (LinearMap.inr ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)
            (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)))) m.sum from rfl,
    map_multiset_sum]
  rfl

/-!

## B. The transformation law of the derivative generators

-/

variable [Module.Free ℂ V] [Module.Finite ℂ V]

/-!

### B.1. The field

-/

/-- The transformation law of the derivative generators of a matter field: a jet of gauge
  transformations mixes `∂_s ψ_φ` with the lower generators, each splitting `s = s₁ + s₂` of
  the derivative multiset contributing the base-point Taylor coefficient of the gauge jet at
  `s₁` acting on the target index of `∂_{s₂} ψ_φ`. There is no inhomogeneous term: unlike a
  gauge field, a matter field transforms linearly. -/
lemma repJetGaugeGroupI_iteratedJetDeriv_ofField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repJetGaugeGroupI rep hlin U (iteratedJetDeriv s (ofField φ)) =
      (s.antidiagonal.map fun p =>
        iteratedJetDeriv p.2 (ofField (IsGaugeField.repDualCoeff rep U⁻¹ p.1 φ))).sum := by
  rw [iteratedJetDeriv_ofField, repJetGaugeGroupI_ι,
    show JetComponentSpace.repJetGaugeGroupI rep hlin U
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace V)
      = (repDual rep hlin U (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ), 0) from by
      refine Prod.ext rfl ?_
      rw [JetComponentSpace.repJetGaugeGroupI_snd]
      exact map_zero _,
    repDual_basis_tmul, sum_inl, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, iteratedJetDeriv_ofField]

/-- The derivative generators of a matter field transform in the representation `rep`
  carried by its jets, in the sense demanded by `StandardModel.TransformsIn`. -/
theorem transformsIn_iteratedJetDeriv_ofField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    TransformsIn (repJetGaugeGroupI rep hlin) rep
      fun s => (iteratedJetDeriv s).comp (ofField (V := V)) :=
  fun U φ s => repJetGaugeGroupI_iteratedJetDeriv_ofField rep hlin U φ s

/-!

### B.2. The conjugate field

-/

/-- The transformation law of the derivative generators of the conjugate matter field. It
  is the law of the field itself for the conjugate action `repConj rep` on the jets of the
  conjugate field — the physicists' `ψ̄ ↦ ψ̄ U†` and its derivatives. -/
lemma repJetGaugeGroupI_iteratedJetDeriv_ofConjField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (φ : Module.Dual ℂ (ConjModule V))
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repJetGaugeGroupI rep hlin U (iteratedJetDeriv s (ofConjField φ)) =
      (s.antidiagonal.map fun p =>
        iteratedJetDeriv p.2
          (ofConjField (IsGaugeField.repDualCoeff (repConj rep) U⁻¹ p.1 φ))).sum := by
  rw [iteratedJetDeriv_ofConjField, repJetGaugeGroupI_ι,
    show JetComponentSpace.repJetGaugeGroupI rep hlin U
        ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace V)
      = (0, repDual (repConj rep) (repConj_smul_comm hlin) U
          (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ)) from by
      refine Prod.ext ?_ rfl
      rw [JetComponentSpace.repJetGaugeGroupI_fst]
      exact map_zero _,
    repDual_basis_tmul, sum_inr, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, iteratedJetDeriv_ofConjField]

/-- The derivative generators of the conjugate matter field transform in the conjugate
  representation `repConj rep`, in the sense demanded by
  `StandardModel.TransformsIn`. -/
theorem transformsIn_iteratedJetDeriv_ofConjField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    TransformsIn (repJetGaugeGroupI rep hlin) (repConj rep)
      fun s => (iteratedJetDeriv s).comp (ofConjField (V := V)) :=
  fun U φ s => repJetGaugeGroupI_iteratedJetDeriv_ofConjField rep hlin U φ s

end FermionicAlgebra

end StandardModel
