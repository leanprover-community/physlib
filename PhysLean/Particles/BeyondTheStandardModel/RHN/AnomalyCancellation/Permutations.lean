/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic
/-!
# Permutations of SM charges with RHN.

We define the group of permutations for the SM charges with RHN.
-/

@[expose] public section

open Nat
open Finset

namespace SMRHN

open SMνCharges
open SMνACCs
open BigOperators

/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := Fin 6 → Equiv.Perm (Fin n)

variable {n : ℕ}

/-- The instance of a group on `PermGroup n` through the target space `Equiv.Perm (Fin n)`. -/
@[simp]
instance : Group (PermGroup n) := Pi.group

/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges n).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMνCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul,
      Module.End.mul_apply]
    repeat erw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    refine LinearMap.ext fun S => ?_
    rw [charges_eq_toSpecies_eq]
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

lemma repCharges_toSpecies (f : PermGroup n) (S : (SMνCharges n).Charges) (j : Fin 6) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMνCharges n).Charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  erw [repCharges_toSpecies]
  change ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [PermGroup, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma accGrav_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext (by simpa using toSpecies_sum_invariant 1 f S)

lemma accSU2_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext (by simpa using toSpecies_sum_invariant 1 f S)

lemma accSU3_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext (by simpa using toSpecies_sum_invariant 1 f S)

lemma accYY_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext (by simpa using toSpecies_sum_invariant 1 f S)

lemma accQuad_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext (toSpecies_sum_invariant 2 f S)

lemma accCube_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext (by simpa using toSpecies_sum_invariant 3 f S)

end SMRHN
