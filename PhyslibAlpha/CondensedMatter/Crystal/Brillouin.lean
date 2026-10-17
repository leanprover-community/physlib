/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Symmetry
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!

# Symmetries of a crystal acting on its Brillouin zone

The symmetries of a crystal act on the crystal momenta, the translations trivially.

## i. Overview

The crystal momenta of a crystal with translation group `G` are the characters of `G`: the
Brillouin zone. A symmetry `s = (A, σ, b)` sends a plane wave of momentum `χ` to a plane wave of
momentum `χ ∘ A⁻¹`, so the symmetries act on the Brillouin zone through their linear parts. This
is an action of the whole group `CellSymmetry G F` of the crystal, for any number of sites per
cell. Translations have the trivial linear part and act trivially, so the action descends to the
point group, the quotient by the translations.

The stabilizer of a momentum `χ` in the group of symmetries is the *little group* of `χ`. It
contains all translations. Its image in the point group is the *little co-group*. At a generic
momentum the little co-group is trivial, and at a high-symmetry momentum it is large. The orbits of
the point group in the Brillouin zone are the classes of equivalent momenta. The orbit space is the
irreducible Brillouin zone: a band structure of a symmetric crystal is a function on it.

## ii. Key results

- `BrillouinZone` : the group of characters of the translations.
- `CellSymmetry.instMulActionBrillouinZone` : the action of the symmetries on crystal momenta.
- `PeriodicGraph.pointAction` : the action of the point group on the Brillouin zone.
- `PeriodicGraph.littleGroup` : the stabilizer of a momentum among the bond-preserving symmetries.
- `PeriodicGraph.IrreducibleZone` : the orbit space of the Brillouin zone under the point group.

## iii. Table of contents

- A. The action of the symmetries
- B. The point group and the little groups
- C. The irreducible zone

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. The action of the symmetries -/

variable {G F : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- The Brillouin zone of a crystal with translation group `G`: the crystal momenta, which are the
characters of `G`. -/
abbrev BrillouinZone (G : Type*) [AddCommGroup G] [TopologicalSpace G] :=
  PontryaginDual (Multiplicative G)

/-- A lattice automorphism acts on a character by precomposition. -/
noncomputable def dualMap (A : G ≃+ G) (χ : BrillouinZone G) : BrillouinZone G where
  toFun x := χ (Multiplicative.ofAdd (A (Multiplicative.toAdd x)))
  map_one' := by
    change χ (Multiplicative.ofAdd (A 0)) = 1
    rw [map_zero]; exact map_one χ
  map_mul' x y := by
    change χ (Multiplicative.ofAdd (A (Multiplicative.toAdd x + Multiplicative.toAdd y))) = _
    rw [map_add, ofAdd_add, map_mul]
  continuous_toFun := continuous_of_discreteTopology

lemma dualMap_apply (A : G ≃+ G) (χ : BrillouinZone G) (a : G) :
    dualMap A χ (Multiplicative.ofAdd a) = χ (Multiplicative.ofAdd (A a)) := rfl

lemma dualMap_refl (χ : BrillouinZone G) : dualMap (AddEquiv.refl G) χ = χ := rfl

lemma dualMap_trans (A B : G ≃+ G) (χ : BrillouinZone G) :
    dualMap B (dualMap A χ) = dualMap (B.trans A) χ := rfl

/-- The symmetries of a crystal act on the crystal momenta: a symmetry with linear part `A` sends
`χ` to `χ ∘ A⁻¹`. -/
noncomputable instance : MulAction (CellSymmetry G F) (BrillouinZone G) where
  smul s χ := dualMap s.linear.symm χ
  one_smul χ := rfl
  mul_smul s t χ := by
    change dualMap (s * t).linear.symm χ = dualMap s.linear.symm (dualMap t.linear.symm χ)
    rw [dualMap_trans]
    rfl

lemma smul_apply (s : CellSymmetry G F) (χ : BrillouinZone G) (a : G) :
    (s • χ) (Multiplicative.ofAdd a) = χ (Multiplicative.ofAdd (s.linear.symm a)) := rfl

/-- Translations act trivially on crystal momenta. -/
lemma translation_smul_brillouin (a : G) (χ : BrillouinZone G) :
    (CellSymmetry.translation a : CellSymmetry G F) • χ = χ := rfl
/-! ## B. The point group and the little groups -/

namespace PeriodicGraph

variable [Finite F] (g : PeriodicGraph (Crystal.ofUnitCell G F))

/-- The bond-preserving symmetries act on the Brillouin zone by permutations. -/
noncomputable def symmetryAction : g.symmetries →* Equiv.Perm (BrillouinZone G) :=
  MulAction.toPermHom g.symmetries (BrillouinZone G)

lemma translations_le_ker_symmetryAction :
    (CellSymmetry.translations G F).subgroupOf g.symmetries ≤ (symmetryAction g).ker := by
  rintro ⟨s, hs⟩ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker]
  ext χ : 1
  exact translation_smul_brillouin a χ

/-- **The point group acts on the Brillouin zone.** -/
noncomputable def pointAction : g.pointGroup →* Equiv.Perm (BrillouinZone G) :=
  QuotientGroup.lift _ (symmetryAction g) (translations_le_ker_symmetryAction g)

noncomputable instance : MulAction g.pointGroup (BrillouinZone G) :=
  MulAction.compHom _ (pointAction g)

lemma mk_smul (s : g.symmetries) (χ : BrillouinZone G) :
    (QuotientGroup.mk s : g.pointGroup) • χ = s • χ := rfl

/-- The little group of a momentum: the bond-preserving symmetries that fix it. It contains all
translations. -/
noncomputable def littleGroup (χ : BrillouinZone G) : Subgroup g.symmetries :=
  MulAction.stabilizer g.symmetries χ

/-- The little co-group of a momentum: the elements of the point group that fix it. -/
noncomputable def littleCoGroup (χ : BrillouinZone G) : Subgroup g.pointGroup :=
  MulAction.stabilizer g.pointGroup χ

lemma mem_littleGroup (χ : BrillouinZone G) (s : g.symmetries) :
    s ∈ g.littleGroup χ ↔ s • χ = χ := MulAction.mem_stabilizer_iff

lemma translation_mem_littleGroup (χ : BrillouinZone G) (a : G) :
    (⟨CellSymmetry.translation a, g.translation_mem_symmetries a⟩ : g.symmetries) ∈
      g.littleGroup χ :=
  (g.mem_littleGroup χ _).2 (translation_smul_brillouin a χ)

/-- The little group is the preimage of the little co-group. -/
lemma littleGroup_eq_comap (χ : BrillouinZone G) :
    g.littleGroup χ = (g.littleCoGroup χ).comap (QuotientGroup.mk' _) := by
  ext s
  simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply, littleGroup, littleCoGroup,
    MulAction.mem_stabilizer_iff]
  rfl

/-! ## C. The irreducible zone -/

/-- The irreducible Brillouin zone: the momenta modulo the point group. -/
abbrev IrreducibleZone := MulAction.orbitRel.Quotient g.pointGroup (BrillouinZone G)

/-- Momenta in the same orbit of the point group are identified in the irreducible zone. -/
lemma irreducibleZone_mk_eq_iff (χ ψ : BrillouinZone G) :
    (Quotient.mk (MulAction.orbitRel g.pointGroup (BrillouinZone G)) χ : g.IrreducibleZone) =
      Quotient.mk _ ψ ↔ ∃ p : g.pointGroup, p • ψ = χ := by
  rw [Quotient.eq]
  exact Iff.rfl

end PeriodicGraph

end CondensedMatter.Crystal
