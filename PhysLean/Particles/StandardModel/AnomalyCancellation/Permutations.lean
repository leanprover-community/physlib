/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic
/-!

# Permutations of SM with no RHN.

We define the group of permutations for the SM charges with no RHN.

-/

@[expose] public section

open Nat
open Finset

namespace SM

open SMCharges
open SMACCs
open BigOperators

/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := ∀ (_ : Fin 5), Equiv.Perm (Fin n)

variable {n : ℕ}

/-- The type `PermGroup n` inherits the instance of a group from it's
  target space `Equiv.Perm`. -/
@[simp]
instance : Group (PermGroup n) := Pi.group

/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMCharges n).Charges →ₗ[ℚ] (SMCharges n).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul,
      Module.End.mul_apply]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

/-- The species charges of a set of charges acted on by a family permutation is the permutation
  of those species charges with the corresponding part of the family permutation. -/
lemma repCharges_toSpecies (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

/-- The sum over every charge in any species to some power `m` is invariant under the group
  action. -/
lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  rw [repCharges_toSpecies]
  exact Fintype.sum_equiv (f⁻¹ j) (fun x => ((fun a => a ^ m) ∘ (toSpecies j) S ∘ ⇑(f⁻¹ j)) x)
    (fun x => ((fun a => a ^ m) ∘ (toSpecies j) S) x) (congrFun rfl)

/-- The gravitational anomaly equations is invariant under family permutations. -/
lemma accGrav_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S := accGrav_ext
  (by simpa using toSpecies_sum_invariant 1 f S)

/-- The `SU(2)` anomaly equation is invariant under family permutations. -/
lemma accSU2_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S := accSU2_ext
  (by simpa using toSpecies_sum_invariant 1 f S)

/-- The `SU(3)` anomaly equation is invariant under family permutations. -/
lemma accSU3_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

/-- The `Y²` anomaly equation is invariant under family permutations. -/
lemma accYY_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

/-- The quadratic anomaly equation is invariant under family permutations. -/
lemma accQuad_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)

/-- The cubic anomaly equation is invariant under family permutations. -/
lemma accCube_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext (fun j => toSpecies_sum_invariant 3 f S j)

end SM
