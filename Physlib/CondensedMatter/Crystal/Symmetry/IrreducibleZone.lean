/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.BrillouinZone

/-!
# Symmetry reduction of the Brillouin zone

Crystal symmetries determine the entire band structure from a smaller part of the Brillouin zone.

## i. Overview

Consider a square lattice with one identical atom at each site. Rotating the crystal by 90 degrees
or reflecting it leaves the system unchanged. The band energies must therefore be identical at
momenta related by these symmetries. Instead of calculating the dispersion throughout the square
Brillouin zone it is enough to calculate it on a triangular region covering just one eighth.

Now consider a crystal with the same square lattice but two different atoms in its unit cell. Some
rotations or reflections may exchange the two atomic species and therefore no longer be
symmetries. The Brillouin zone still has the same shape but its irreducible region can be larger.
It is the symmetry of the crystal and not just the shape of its lattice that determines how far
the Brillouin zone can be reduced.

Every subgroup `H` of crystal symmetries defines its own irreducible Brillouin zone. The more
symmetries are used the smaller is the region needed to describe a symmetry-invariant quantity.
With no symmetries the entire Brillouin zone is needed.

## ii. Key results

- `BrillouinZone.IrreducibleZone` : the irreducible Brillouin zone for `H`.
- `BrillouinZone.littleGroup` : the symmetries in `H` that fix a point of the zone.
- `BrillouinZone.ker_pointOp_le_littleGroup` : the shifts in `H` lie in every little group.
- `BrillouinZone.orbitRel_map_pointOp` : `H` and its point operations give the same momentum orbits.
- `BrillouinZone.IrreducibleZone.equivPointOp` : the irreducible zones for `H` and its point
  operations correspond.
- `BrillouinZone.IrreducibleZone.IsRegion` : a set with one representative of each momentum orbit.
- `BrillouinZone.IrreducibleZone.exists_isRegion` : every group `H` has an irreducible zone.
- `BrillouinZone.IrreducibleZone.eq_of_eqOn` : a function invariant under `H` is determined on
  an irreducible zone.
- `BrillouinZone.IrreducibleZone.regionEquiv` : a representative region corresponds to the
  irreducible zone.
- `BrillouinZone.IrreducibleZone.extend` : extend values on an irreducible zone to an invariant
  function on all momenta.
- `BrillouinZone.IrreducibleZone.invariantFunctionsEquiv` : restriction identifies invariant
  functions with functions on an irreducible zone.

## iii. Table of contents

- A. The irreducible zone
- B. The little group
- C. Point operations
- D. Irreducible zones

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L4, Section 4.4 and lecture L5,
  Section 5.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open Symmetry

namespace BrillouinZone

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]
  [TopologicalSpace G] [DiscreteTopology G] {C : Crystal G}
  {H : Subgroup (Symmetry C)} {D : Set (BrillouinZone G)} {β : Type*}

/-! ## A. The irreducible zone -/

/-- The irreducible Brillouin zone for `H`, defined as the orbit space of the
Brillouin zone under the action of `H`. -/
abbrev IrreducibleZone (H : Subgroup (Symmetry C)) : Type _ :=
  MulAction.orbitRel.Quotient H (BrillouinZone G)

/-! ## B. The little group -/

/-- The little group of a point `k` of the zone: the symmetries in `H` that fix `k`. -/
noncomputable abbrev littleGroup (H : Subgroup (Symmetry C)) (k : BrillouinZone G) : Subgroup H :=
  MulAction.stabilizer H k

/-- A symmetry in `H` lies in the little group of `k` exactly when it fixes `k`. -/
lemma mem_littleGroup_iff {k : BrillouinZone G} (s : H) :
    s ∈ littleGroup H k ↔ (s : Symmetry C) • k = k := Iff.rfl

/-- The shifts in `H` lie in the little group of every point. -/
lemma ker_pointOp_le_littleGroup (H : Subgroup (Symmetry C)) (k : BrillouinZone G) :
    (pointOp C).ker.subgroupOf H ≤ littleGroup H k := by
  intro s hs
  rw [mem_littleGroup_iff, ← BrillouinZone.pointOp_smul]
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hs
  rw [hs, one_smul]

/-! ## C. Point operations -/

/-- `H` and the group of its point operations identify the same points of the zone. -/
lemma orbitRel_map_pointOp (H : Subgroup (Symmetry C)) (k k' : BrillouinZone G) :
    MulAction.orbitRel (H.map (pointOp C)) (BrillouinZone G) k k' ↔
      MulAction.orbitRel H (BrillouinZone G) k k' := by
  simp only [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨⟨_, s, hs, rfl⟩, h⟩
    exact ⟨⟨s, hs⟩, h⟩
  · rintro ⟨⟨s, hs⟩, h⟩
    exact ⟨⟨pointOp C s, s, hs, rfl⟩, h⟩

/-! ## D. Irreducible zones

The action on momenta induces an action on functions by precomposition through
`DomMulAct H`. Invariant functions are the fixed points of this action. -/

namespace IrreducibleZone

/-- The irreducible zones for `H` and its point operations correspond. -/
noncomputable def equivPointOp (H : Subgroup (Symmetry C)) :
    IrreducibleZone H ≃ IrreducibleZone (H.map (pointOp C)) :=
  Quotient.congr (Equiv.refl _) (by
    intro k k'
    exact (orbitRel_map_pointOp H k k').symm)

/-- A set `D` of points of the Brillouin zone is an irreducible zone for `H` if it contains
exactly one representative of each orbit under `H`. -/
def IsRegion (H : Subgroup (Symmetry C)) (D : Set (BrillouinZone G)) : Prop :=
  Set.BijOn (Quotient.mk'' : BrillouinZone G → IrreducibleZone H) D Set.univ

/-- Every group `H` of symmetries has an irreducible zone. -/
lemma exists_isRegion (H : Subgroup (Symmetry C)) :
    ∃ D : Set (BrillouinZone G), IsRegion H D := by
  have hq : Function.Surjective (Quotient.mk'' : BrillouinZone G → IrreducibleZone H) :=
    Quotient.mk'_surjective (s := MulAction.orbitRel H (BrillouinZone G))
  obtain ⟨D, _, hD⟩ := (hq.surjOn (t := Set.univ)).exists_bijOn_subset
  exact ⟨D, hD⟩

/-- Functions fixed by the symmetry action are determined by their values on an irreducible
zone. -/
lemma eq_of_eqOn (hD : IsRegion H D)
    {f g : MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β)}
    (h : Set.EqOn f.val g.val D) : f = g := by
  apply Subtype.ext
  funext k
  obtain ⟨d, hd, hdk⟩ := hD.surjOn (Set.mem_univ (Quotient.mk'' k : IrreducibleZone H))
  obtain ⟨s, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' hdk)
  have hfg := h hd
  change (DomMulAct.mk s • f.val) k = (DomMulAct.mk s • g.val) k at hfg
  simpa only [MulAction.mem_fixedPoints.mp f.property,
    MulAction.mem_fixedPoints.mp g.property] using hfg

/-- A representative region corresponds to the irreducible Brillouin zone. -/
noncomputable def regionEquiv (hD : IsRegion H D) : D ≃ IrreducibleZone H :=
  (Set.BijOn.equiv _ hD).trans (Equiv.Set.univ _)

/-- Extend a function on an irreducible zone to a symmetry-invariant function on all momenta. -/
noncomputable def extend (hD : IsRegion H D) (φ : D → β) :
    MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β) := by
  refine ⟨φ ∘ (regionEquiv hD).symm ∘ Quotient.mk'', ?_⟩
  rw [MulAction.mem_fixedPoints]
  intro s
  ext k
  apply congrArg (φ ∘ (regionEquiv hD).symm)
  exact MulAction.orbitRel.Quotient.quotient_smul_eq
    (G := H) (g := DomMulAct.mk.symm s) (a := k)

/-- The invariant extension agrees with the original function on the irreducible zone. -/
@[simp] lemma extend_apply (hD : IsRegion H D) (φ : D → β) (d : D) :
    (extend hD φ).val d = φ d := by
  change φ ((regionEquiv hD).symm (regionEquiv hD d)) = φ d
  rw [Equiv.symm_apply_apply]

/-- Restriction to an irreducible zone identifies functions fixed by the symmetry action with
functions on that zone. -/
noncomputable def invariantFunctionsEquiv (hD : IsRegion H D) :
    MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β) ≃ (D → β) where
  toFun f := D.domRestrict f.val
  invFun := extend hD
  left_inv f := by
    apply eq_of_eqOn hD
    intro k hk
    exact extend_apply hD (D.domRestrict f.val) ⟨k, hk⟩
  right_inv φ := by
    ext d
    exact extend_apply hD φ d

/-- The equivalence with functions on an irreducible zone acts by restriction. -/
@[simp] lemma invariantFunctionsEquiv_apply (hD : IsRegion H D)
    (f : MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β)) (d : D) :
    invariantFunctionsEquiv hD f d = f.val d := rfl

/-- The inverse equivalence extends a function from the irreducible zone. -/
@[simp] lemma invariantFunctionsEquiv_symm_apply (hD : IsRegion H D) (φ : D → β)
    (d : D) : ((invariantFunctionsEquiv hD).symm φ).val d = φ d :=
  congrFun ((invariantFunctionsEquiv hD).apply_symm_apply φ) d

end IrreducibleZone

end BrillouinZone

end Physlib.CondensedMatter.Crystal
