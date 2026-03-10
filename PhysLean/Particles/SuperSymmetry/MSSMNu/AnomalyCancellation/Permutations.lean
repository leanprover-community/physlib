/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic
/-!
# Permutations of MSSM charges and solutions

The three family MSSM charges has a family permutation of S₃⁶. This file defines this group
and its action on the MSSM.

-/

@[expose] public section

open Nat
open Finset

namespace MSSM

open MSSMCharges
open MSSMACCs
open BigOperators

/-- The group of family permutations is `S₃⁶`-/
@[simp]
def PermGroup := Fin 6 → Equiv.Perm (Fin 3)

/-- The type `PermGroup` has a group instances derived from the group instance of it's target. -/
@[simp]
instance : Group PermGroup := Pi.group

/-- The image of an element of `permGroup` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup) : MSSMCharges.Charges →ₗ[ℚ] MSSMCharges.Charges where
  toFun S := toSpecies.symm (fun i => toSMSpecies i S ∘ f i, Prod.snd (toSpecies S))
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    apply And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl

lemma chargeMap_toSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (chargeMap f S) = toSMSpecies j S ∘ f j := by
  erw [toSMSpecies_toSpecies_inv]

/-- The representation of `permGroup` acting on the vector space of charges. -/
@[simp]
def repCharges : Representation ℚ PermGroup (MSSMCharges).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    simp only [Module.End.mul_apply]
    rw [chargeMap_toSpecies, chargeMap_toSpecies]
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [chargeMap_toSpecies]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

lemma repCharges_toSMSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (repCharges f S) = toSMSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j S) i := by
  rw [repCharges_toSMSpecies]
  exact Equiv.sum_comp (f⁻¹ j) ((fun a => a ^ m) ∘ (toSMSpecies j) S)

lemma Hd_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hd (repCharges f S) = Hd S := rfl

lemma Hu_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hu (repCharges f S) = Hu S := rfl

lemma accGrav_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accSU2_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accSU3_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accYY_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accQuad_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accCube_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext
    (fun j => toSpecies_sum_invariant 3 f S j)
    (Hd_invariant f S)
    (Hu_invariant f S)

end MSSM
