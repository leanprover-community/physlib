/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# The Brillouin zone and the action of the symmetries

The crystal momenta form the dual group of the translations. The symmetries act on it.

## i. Overview

A wave in a crystal picks up a phase when it is shifted by a lattice vector. These phases are a
character of the translation group. They determine the crystal momentum of a Bloch wave. Two
momenta that differ by a reciprocal lattice vector give the same phases. The crystal momenta
therefore form the dual group of the translations. This is the Brillouin zone.

The translations determine their dual group. A lattice automorphism `A` also acts on the dual
group. It maps a momentum `k` to `k ∘ A⁻¹`. A symmetry acts on the Brillouin zone through its
lattice automorphism.

A symmetry and its point operation have the same lattice automorphism. They act in the same way.
Shifts of the sites within the cell have a trivial lattice automorphism. They fix every momentum.

The translation group is discrete. Every character is therefore continuous.

## ii. Key results

- `BrillouinZone` : the characters of the translation group.
- `BrillouinZone.smul_apply` : the value of a transformed momentum on a lattice vector.
- `BrillouinZone.smul_lattice_apply` : transforming momentum and lattice vector together keeps the
  value.
- `BrillouinZone.pointOp_smul` : a symmetry and its point operation act in the same way.
- `BrillouinZone.shift_smul` : shifts fix every momentum.

## iii. Table of contents

- A. The Brillouin zone
- B. The action of the lattice automorphisms
- C. The action of the symmetries

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.3 and lecture L5,
  Section 5.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]
  [TopologicalSpace G] [DiscreteTopology G]

/-! ## A. The Brillouin zone -/

/-- The Brillouin zone of a crystal with translation group `G`: the circle-valued characters of
`G`. -/
abbrev BrillouinZone (G : Type*) [AddCommGroup G] [TopologicalSpace G] :=
  PontryaginDual (Multiplicative G)

/-! ## B. The action of the lattice automorphisms -/

/-- A lattice automorphism `A` maps the momentum `k` to `k ∘ A⁻¹`. -/
noncomputable instance :
    MulDistribMulAction (Multiplicative (AddAut G)) (BrillouinZone G) where
  smul A k := PontryaginDual.map
    { toMonoidHom := (AddEquiv.toMultiplicative (Multiplicative.toAdd A).symm).toMonoidHom
      continuous_toFun := continuous_of_discreteTopology } k
  one_smul k := by
    ext a
    rfl
  mul_smul A B k := by
    ext a
    rfl
  smul_one A := by
    ext a
    rfl
  smul_mul A k k' := by
    ext a
    rfl

omit [AddGroup.FG G] in
/-- The momentum `A • k` takes the value of `k` at the preimage of the lattice vector. -/
lemma BrillouinZone.smul_apply (A : Multiplicative (AddAut G)) (k : BrillouinZone G) (a : G) :
    (A • k) (Multiplicative.ofAdd a) =
      k (Multiplicative.ofAdd ((Multiplicative.toAdd A).symm a)) := rfl

/-! ## C. The action of the symmetries -/

/-- A symmetry acts on the Brillouin zone through its lattice automorphism. -/
noncomputable instance (C : Crystal G) : MulDistribMulAction (Symmetry C) (BrillouinZone G) :=
  MulDistribMulAction.compHom _
    ({ toFun := fun s => Multiplicative.ofAdd s.lattice
       map_one' := rfl
       map_mul' := fun _ _ => rfl } : Symmetry C →* Multiplicative (AddAut G))

open Symmetry

namespace BrillouinZone

/-- Transforming momentum and lattice vector together keeps the value. -/
lemma smul_lattice_apply {C : Crystal G} (s : Symmetry C) (k : BrillouinZone G) (a : G) :
    (s • k) (Multiplicative.ofAdd (s.lattice a)) = k (Multiplicative.ofAdd a) :=
  congrArg (fun x => k (Multiplicative.ofAdd x)) (s.lattice.symm_apply_apply a)

/-- A symmetry and its point operation act in the same way on the Brillouin zone. -/
lemma pointOp_smul {C : Crystal G} (s : Symmetry C) (k : BrillouinZone G) :
    pointOp C s • k = s • k := rfl

/-- Shifts fix every momentum. -/
lemma shift_smul {C : Crystal G} (b : C.UnitCell → G) (k : BrillouinZone G) :
    shift C b • k = k := by
  rw [← pointOp_smul, pointOp_shift, one_smul]

end BrillouinZone

end Physlib.CondensedMatter.Crystal
