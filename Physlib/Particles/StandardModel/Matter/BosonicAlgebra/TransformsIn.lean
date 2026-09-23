/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.TransformsIn
/-!
# The transformation law of the bosonic generators

## i. Overview

`BosonicAlgebra.repJetGaugeGroupI_ofField` records that the undifferentiated generator
`ψ_φ` transforms by the value of the gauge transformation at the base point. Its derivatives
do not: a jet of gauge transformations mixes `∂_s ψ_φ` with the lower generators
`∂_{s₂} ψ_φ`, weighted by the base-point Taylor coefficients
`GaugeAlgebraRealization.repDualCoeff` of the gauge jet at the complementary multiset `s₁`.
This file proves that all-orders Leibniz law, in the form `LocalGaugeData.TransformsIn`
demands.

All the work is in `StandardModel.repDual_basis_tmul`, the corresponding statement on the
jet component space. The symmetric algebra contributes only linearity: the generators are
the image of the component space under `SymmetricAlgebra.ι`, and a multiset sum passes
through a linear map.

The conjugate generators are the same statement for the conjugate action
`JetComponentSpace.repConj M.repJet` on
the jets of the conjugate field, which is what the conjugate half of the component space
carries; so they are an instance of the same lemma, not a second proof.

## ii. Key results

- `BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField` : the transformation law of
  the derivative generators `∂_s ψ_φ`.
- `BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField` : the transformation
  law of the conjugate derivative generators `∂_s ψ̄_φ`.
- `BosonicAlgebra.transformsIn_iteratedJetDeriv_ofField`,
  `BosonicAlgebra.transformsIn_iteratedJetDeriv_ofConjField` : the same, packaged as
  `LocalGaugeData.TransformsIn`.

## iii. Table of contents

- A. Multiset sums of generators
- B. The transformation law of the derivative generators
  - B.1. The field
  - B.2. The conjugate field

-/

@[expose] public section

namespace StandardModel

namespace BosonicAlgebra

open Matrix MatrixGroups TensorProduct

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {M : MatterField jets}

/-!

## A. Multiset sums of generators

-/

/-- A multiset sum in the unconjugated half of the component space passes through the
  inclusion of the generators. -/
private lemma sum_inl (m : Multiset (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V)) :
    SymmetricAlgebra.ι ℂ _ ((m.sum, 0) : JetComponentSpace M)
      = (m.map fun a =>
          SymmetricAlgebra.ι ℂ _ ((a, 0) : JetComponentSpace M)).sum := by
  rw [show SymmetricAlgebra.ι ℂ (JetComponentSpace M) ((m.sum, 0) : JetComponentSpace M)
      = ((SymmetricAlgebra.ι ℂ (JetComponentSpace M)).comp
          (LinearMap.inl ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V)
            (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)))) m.sum from rfl,
    map_multiset_sum]
  rfl

/-- A multiset sum in the conjugate half of the component space passes through the
  inclusion of the generators. -/
private lemma sum_inr (m : Multiset (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V))) :
    SymmetricAlgebra.ι ℂ _ ((0, m.sum) : JetComponentSpace M)
      = (m.map fun a =>
          SymmetricAlgebra.ι ℂ _ ((0, a) : JetComponentSpace M)).sum := by
  rw [show SymmetricAlgebra.ι ℂ (JetComponentSpace M) ((0, m.sum) : JetComponentSpace M)
      = ((SymmetricAlgebra.ι ℂ (JetComponentSpace M)).comp
          (LinearMap.inr ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V)
            (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)))) m.sum from rfl,
    map_multiset_sum]
  rfl

/-!

## B. The transformation law of the derivative generators

-/


/-!

### B.1. The field

-/

/-- The transformation law of the derivative generators of a matter field: a jet of gauge
  transformations mixes `∂_s ψ_φ` with the lower generators, each splitting `s = s₁ + s₂` of
  the derivative multiset contributing the base-point Taylor coefficient of the gauge jet at
  `s₁` acting on the target index of `∂_{s₂} ψ_φ`. There is no inhomogeneous term: unlike a
  gauge field, a matter field transforms linearly. -/
lemma repJetGaugeGroupI_iteratedJetDeriv_ofField
    (U : GJ) (φ : Module.Dual ℂ M.V) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repJetGaugeGroupI M U (iteratedJetDeriv s (ofField φ)) =
      (s.antidiagonal.map fun p =>
        iteratedJetDeriv p.2
          (ofField (GaugeAlgebraRealization.repDualCoeff M.repJet U⁻¹ p.1 φ))).sum := by
  rw [iteratedJetDeriv_ofField, repJetGaugeGroupI_ι,
    show JetComponentSpace.repJet M U
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace M)
      = (JetComponentSpace.repDual M.repJet M.repJet_smul U (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ), 0) from by
      refine Prod.ext rfl ?_
      rw [JetComponentSpace.repJet_snd]
      exact map_zero _,
    JetComponentSpace.repDual_basis_tmul, sum_inl, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, iteratedJetDeriv_ofField]

/-- The derivative generators of a matter field transform in the representation `rep`
  carried by its jets, in the sense demanded by `LocalGaugeData.TransformsIn`. -/
theorem transformsIn_iteratedJetDeriv_ofField :
    LocalGaugeData.TransformsIn (repJetGaugeGroupI M) M.repJet
      fun s => (iteratedJetDeriv s).comp (ofField (M := M)) :=
  fun U φ s => repJetGaugeGroupI_iteratedJetDeriv_ofField (M := M) U φ s

/-!

### B.2. The conjugate field

-/

/-- The transformation law of the derivative generators of the conjugate matter field. It
  is the law of the field itself for the conjugate action `JetComponentSpace.repConj M.repJet` on
  the jets of the
  conjugate field — the physicists' `ψ̄ ↦ ψ̄ U†` and its derivatives. -/
lemma repJetGaugeGroupI_iteratedJetDeriv_ofConjField
    (U : GJ) (φ : Module.Dual ℂ (ConjModule M.V))
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repJetGaugeGroupI M U (iteratedJetDeriv s (ofConjField φ)) =
      (s.antidiagonal.map fun p =>
        iteratedJetDeriv p.2
          (ofConjField
            (GaugeAlgebraRealization.repDualCoeff (JetComponentSpace.repConj M.repJet) U⁻¹ p.1
              φ))).sum := by
  rw [iteratedJetDeriv_ofConjField, repJetGaugeGroupI_ι,
    show JetComponentSpace.repJet M U
        ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace M)
      = (0, JetComponentSpace.repDual (JetComponentSpace.repConj M.repJet)
          (JetComponentSpace.repConj_smul_comm M.repJet_smul) U
          (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ)) from by
      refine Prod.ext ?_ rfl
      rw [JetComponentSpace.repJet_fst]
      exact map_zero _,
    JetComponentSpace.repDual_basis_tmul, sum_inr, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, iteratedJetDeriv_ofConjField]

/-- The derivative generators of the conjugate matter field transform in the conjugate
  representation `JetComponentSpace.repConj M.repJet`, in the sense demanded by
  `LocalGaugeData.TransformsIn`. -/
theorem transformsIn_iteratedJetDeriv_ofConjField :
    LocalGaugeData.TransformsIn (repJetGaugeGroupI M) (JetComponentSpace.repConj M.repJet)
      fun s => (iteratedJetDeriv s).comp (ofConjField (M := M)) :=
  fun U φ s => repJetGaugeGroupI_iteratedJetDeriv_ofConjField (M := M) U φ s

end BosonicAlgebra

end StandardModel
