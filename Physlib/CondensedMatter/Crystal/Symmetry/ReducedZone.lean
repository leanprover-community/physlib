/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.BrillouinZone

/-!
# The reduced zone

The part of the Brillouin zone that is left after using the symmetries of a crystal.

## i. Overview

The translations of a crystal determine its Brillouin zone. A crystal usually has more symmetry
than the translations. Rotations and reflections turn the Brillouin zone into itself. Parts of the
zone that are related by such a symmetry carry the same physics. The zone can therefore be
reduced further.

A square lattice is the standard example. Its Brillouin zone is a square. The point group has
eight elements. It consists of four rotations and four reflections. A band structure with these
symmetries needs to be known on an eighth of the square only. This eighth is an irreducible zone.

## ii. Key results

- `Symmetry.ReducedZone` : the Brillouin zone reduced by a group `H` of symmetries.
- `Symmetry.littleGroup` : the symmetries in `H` that fix a point of the zone.
- `Symmetry.ker_pointOp_le_littleGroup` : the shifts in `H` lie in every little group.
- `Symmetry.orbitRel_map_pointOp` : `H` and its point operations are invariant for the same
  functions.
- `Symmetry.ReducedZone.equivMapPointOp` : the zones reduced by `H` and by its point operations
  correspond.
- `Symmetry.IsIrreducibleZone` : a set of points that contains each point of the reduced zone once.
- `Symmetry.exists_isIrreducibleZone` : every group `H` has an irreducible zone.
- `Symmetry.IsIrreducibleZone.eq_of_forall_mem` : a function invariant under `H` is determined on
  an irreducible zone.
- `Symmetry.IsIrreducibleZone.equiv` : an irreducible zone corresponds to the reduced zone.

## iii. Table of contents

- A. The reduced zone
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

namespace Symmetry

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]
  [TopologicalSpace G] [DiscreteTopology G] {C : Crystal G}

/-! ## A. The reduced zone -/

/-- The Brillouin zone reduced by a group `H` of symmetries. Points that `H` maps to each other
are identified. -/
abbrev ReducedZone (H : Subgroup (Symmetry C)) :=
  MulAction.orbitRel.Quotient H (BrillouinZone G)

/-! ## B. The little group -/

/-- The little group of a point `k` of the zone: the symmetries in `H` that fix `k`. -/
noncomputable abbrev littleGroup (H : Subgroup (Symmetry C)) (k : BrillouinZone G) : Subgroup H :=
  MulAction.stabilizer H k

/-- A symmetry in `H` lies in the little group of `k` exactly when it fixes `k`. -/
lemma mem_littleGroup_iff {H : Subgroup (Symmetry C)} {k : BrillouinZone G} (s : H) :
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

/-- The zone reduced by `H` corresponds to the zone reduced by its point operations. -/
noncomputable def ReducedZone.equivMapPointOp (H : Subgroup (Symmetry C)) :
    ReducedZone H ≃ ReducedZone (H.map (pointOp C)) :=
  Quotient.congr (Equiv.refl _) fun k k' => (orbitRel_map_pointOp H k k').symm

/-! ## D. Irreducible zones -/

/-- A set `D` of points of the Brillouin zone is an irreducible zone for `H` if it contains
exactly one point of each set of points that `H` maps to each other. -/
def IsIrreducibleZone (H : Subgroup (Symmetry C)) (D : Set (BrillouinZone G)) : Prop :=
  (∀ k, ∃ d ∈ D, MulAction.orbitRel H (BrillouinZone G) d k) ∧
    ∀ d ∈ D, ∀ d' ∈ D, MulAction.orbitRel H (BrillouinZone G) d d' → d = d'

/-- Every group `H` of symmetries has an irreducible zone. -/
lemma exists_isIrreducibleZone (H : Subgroup (Symmetry C)) :
    ∃ D : Set (BrillouinZone G), IsIrreducibleZone H D := by
  refine ⟨Set.range fun q : ReducedZone H => Quotient.out q, ?_, ?_⟩
  · intro k
    exact ⟨Quotient.out (Quotient.mk'' k : ReducedZone H), ⟨_, rfl⟩,
      Quotient.exact' (Quotient.out_eq' (Quotient.mk'' k : ReducedZone H))⟩
  · rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ h
    have : q = q' := by
      rw [← Quotient.out_eq' q, ← Quotient.out_eq' q']
      exact Quotient.sound' h
    rw [this]

namespace IsIrreducibleZone

variable {H : Subgroup (Symmetry C)} {D : Set (BrillouinZone G)}

/-- A function that is invariant under `H` is determined by its values on an irreducible zone. -/
lemma eq_of_forall_mem {β : Type*} {f g : BrillouinZone G → β} (hD : IsIrreducibleZone H D)
    (hf : ∀ (s : H) k, f ((s : Symmetry C) • k) = f k)
    (hg : ∀ (s : H) k, g ((s : Symmetry C) • k) = g k) (h : ∀ d ∈ D, f d = g d) : f = g := by
  funext k
  obtain ⟨d, hd, hdk⟩ := hD.1 k
  obtain ⟨s, rfl⟩ := MulAction.orbitRel_apply.1 hdk
  rw [← hf s k, ← hg s k]
  exact h _ hd

/-- An irreducible zone corresponds to the zone reduced by `H`. -/
noncomputable def equiv (hD : IsIrreducibleZone H D) : D ≃ ReducedZone H :=
  Equiv.ofBijective (fun d => Quotient.mk'' (d : BrillouinZone G))
    ⟨fun d d' h => Subtype.ext (hD.2 _ d.2 _ d'.2 (Quotient.exact' h)), fun q => by
      obtain ⟨d, hd, h⟩ := hD.1 (Quotient.out q)
      exact ⟨⟨d, hd⟩, by rw [← Quotient.out_eq' q]; exact Quotient.sound' h⟩⟩

end IsIrreducibleZone

end Symmetry

end Physlib.CondensedMatter.Crystal
