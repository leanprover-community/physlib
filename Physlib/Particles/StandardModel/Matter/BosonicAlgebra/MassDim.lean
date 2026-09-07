/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
/-!
# Mass dimension on the bosonic algebra

## i. Overview

The mass dimension of a bosonic matter field is tracked multiplicatively through the
*mass-weight scaling*: the algebra endomorphism multiplying each generator `∂_s φ_α` by
`c ^ (w + 2 |s|)`, where `w` is the mass weight of the field — twice its mass dimension,
kept integral so the same machinery serves the fermions of dimension `3/2`. A monomial of
total mass weight `n` is scaled by `c ^ n`, so the scaling records the mass-weight grading
of the algebra, and its interaction with the total derivative says that a derivative
carries mass weight two.

## ii. Key results

- `BosonicAlgebra.massWeightScale` : the mass-weight scaling.
- `BosonicAlgebra.massWeightScale_ofField` : the field carries its own mass weight.
- `BosonicAlgebra.massWeightScale_jetDeriv` : a derivative adds mass weight two.
- `BosonicAlgebra.massWeightScale_iteratedJetDeriv` : `∂_s` adds mass weight `2 |s|`.

## iii. Table of contents

- A. The mass-weight scaling
- B. The mass weight of the field and its derivatives

-/

@[expose] public section

namespace StandardModel

namespace BosonicAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The mass-weight scaling

-/

/-- **The mass-weight scaling on the bosonic algebra** of a field of mass weight `w`:
  the algebra endomorphism scaling the generator `∂_s φ_α` by `c ^ (w + 2 |s|)`, the
  functorial lift of the scaling on the jet component space. -/
noncomputable def massWeightScale (w : ℕ) (c : ℂ) : BosonicAlgebra V →ₐ[ℂ] BosonicAlgebra V :=
  SymmetricAlgebra.map (JetComponentSpace.massWeightScale w c)

@[simp]
lemma massWeightScale_ι (w : ℕ) (c : ℂ) (x : JetComponentSpace V) :
    massWeightScale w c (SymmetricAlgebra.ι ℂ _ x)
      = SymmetricAlgebra.ι ℂ _ (JetComponentSpace.massWeightScale w c x) :=
  SymmetricAlgebra.map_apply_ι _ x

/-!

## B. The mass weight of the field and its derivatives

-/

/-- The undifferentiated field carries its own mass weight. -/
@[simp]
lemma massWeightScale_ofField (w : ℕ) (c : ℂ) (φ : Module.Dual ℂ V) :
    massWeightScale w c (ofField φ) = c ^ w • ofField φ := by
  rw [ofField_apply, massWeightScale_ι, ← map_smul]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.massWeightScale_fst]
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one,
      LinearMap.id_apply, Prod.smul_fst, TensorProduct.smul_tmul']
  · rw [JetComponentSpace.massWeightScale_snd]
    simp

/-- The undifferentiated conjugate field carries the same mass weight as the field. -/
@[simp]
lemma massWeightScale_ofConjField (w : ℕ) (c : ℂ) (φ : Module.Dual ℂ (ConjModule V)) :
    massWeightScale w c (ofConjField φ) = c ^ w • ofConjField φ := by
  rw [ofConjField_apply, massWeightScale_ι, ← map_smul]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.massWeightScale_fst]
    simp
  · rw [JetComponentSpace.massWeightScale_snd]
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one,
      LinearMap.id_apply, Prod.smul_snd, TensorProduct.smul_tmul']

/-- **A total derivative adds mass weight two**: the scaling intertwines the total
  derivative up to a factor `c ^ 2`. -/
lemma massWeightScale_jetDeriv (w : ℕ) (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : BosonicAlgebra V) :
    massWeightScale w c (jetDeriv μ x) = c ^ 2 • jetDeriv μ (massWeightScale w c x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => rw [jetDeriv_algebraMap, map_zero, AlgHom.commutes, jetDeriv_algebraMap,
      smul_zero]
  | ι v =>
    rw [jetDeriv_ι, massWeightScale_ι, massWeightScale_ι, jetDeriv_ι, ← map_smul]
    exact congrArg (SymmetricAlgebra.ι ℂ _)
      (LinearMap.congr_fun (JetComponentSpace.massWeightScale_jetDeriv w c μ) v)
  | mul a b ha hb =>
    simp only [jetDeriv_mul, map_add, map_mul, ha, hb, smul_add, smul_mul_assoc,
      mul_smul_comm]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

/-- **The iterated derivative `∂_s` adds mass weight `2 |s|`.** -/
lemma massWeightScale_iteratedJetDeriv (w : ℕ) (c : ℂ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (x : BosonicAlgebra V) :
    massWeightScale w c (iteratedJetDeriv s x)
      = c ^ (2 * Multiset.card s) • iteratedJetDeriv s (massWeightScale w c x) := by
  induction s using Multiset.induction_on generalizing x with
  | empty => simp
  | cons μ s ih =>
    rw [iteratedJetDeriv_cons, LinearMap.comp_apply, massWeightScale_jetDeriv, ih,
      map_smul, LinearMap.comp_apply, smul_smul, ← pow_add]
    congr 2
    rw [Multiset.card_cons]
    ring

end BosonicAlgebra

end StandardModel
