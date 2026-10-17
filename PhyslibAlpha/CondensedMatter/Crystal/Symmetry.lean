/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Graph
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Abel

/-!

# Symmetries of a crystal graph

## i. Overview

The symmetries of a crystal that map translated copies of the unit cell onto translated copies
are described by finite data. A symmetry `(A, σ, b)` consists of an automorphism `A` of the
translation group, a permutation `σ` of the site labels of the unit cell, and for each label `i`
a cell offset `b i`. It sends the site `i` of cell `n` to the site `σ i` of cell `A n + b i`.
Composing two symmetries composes these data, so they form a group `CellSymmetry G F`.
Translations by `a` are the symmetries with `A = 1`, `σ = 1` and `b = a`. Conjugating a
translation by a symmetry gives the translation by `A a`, so the translations form a normal
subgroup. The quotient is the abstract point group, which need not be a subgroup: a screw axis or
glide plane of a non-symmorphic crystal is a symmetry whose offsets cannot be removed.

A symmetry preserves the bonds of a periodic graph exactly when the relation "site `i` in the
reference cell is bonded to site `j` in the cell `d`" is carried to the same relation for the
transformed data, namely `(σ i, σ j, A d + b j - b i)`. This is a finite condition on the bond
data of one unit cell. Bond-preserving symmetries form a subgroup `PeriodicGraph.symmetries` and
act by automorphisms of the bond graph. Conversely, every graph automorphism that normalises the
translations arises this way.

The graph alone knows nothing of physical lengths and angles. A square lattice has the symmetry
group `ℤ² ⋊ D₄` as a graph, whether or not its two lattice constants are equal. The geometric
point group is the subgroup of these symmetries compatible with a chosen `Geometry`.

## ii. Key results

- `CellSymmetry` : the group of symmetries `(A, σ, b)` of the translation structure.
- `CellSymmetry.translations` : the normal subgroup of translations.
- `PeriodicGraph.symmetries` : the subgroup preserving the bonds of a periodic graph.
- `PeriodicGraph.mem_symmetries_iff` : a finite criterion on the bond data of one unit cell.
- `PeriodicGraph.exists_symmetry_of_equivariant` : every graph automorphism normalising the
  translations is such a symmetry.

## iii. Table of contents

- A. The group of cell symmetries
- B. Translations form a normal subgroup
- C. Bond-preserving symmetries

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. The group of cell symmetries -/

/-- A symmetry of the translation structure of a crystal with unit-cell labels `F` and cell
translations `G`: `(A, σ, b)` sends site `i` of cell `n` to site `σ i` of cell `A n + b i`. -/
@[ext] structure CellSymmetry (G F : Type*) [AddCommGroup G] where
  /-- The action on cell indices. -/
  linear : G ≃+ G
  /-- The permutation of the labels within a unit cell. -/
  perm : Equiv.Perm F
  /-- The cell offset accompanying each label. -/
  shift : F → G

namespace CellSymmetry

variable {G F : Type*} [AddCommGroup G]

instance : Mul (CellSymmetry G F) where
  mul s t := ⟨t.linear.trans s.linear, t.perm.trans s.perm,
    fun i => s.linear (t.shift i) + s.shift (t.perm i)⟩

instance : One (CellSymmetry G F) := ⟨⟨AddEquiv.refl G, Equiv.refl F, fun _ => 0⟩⟩

instance : Inv (CellSymmetry G F) where
  inv s := ⟨s.linear.symm, s.perm.symm, fun j => -s.linear.symm (s.shift (s.perm.symm j))⟩

@[simp] lemma linear_mul (s t : CellSymmetry G F) (x : G) :
    (s * t).linear x = s.linear (t.linear x) := rfl
@[simp] lemma perm_mul (s t : CellSymmetry G F) (i : F) :
    (s * t).perm i = s.perm (t.perm i) := rfl
@[simp] lemma shift_mul (s t : CellSymmetry G F) (i : F) :
    (s * t).shift i = s.linear (t.shift i) + s.shift (t.perm i) := rfl
@[simp] lemma linear_one (x : G) : (1 : CellSymmetry G F).linear x = x := rfl
@[simp] lemma perm_one (i : F) : (1 : CellSymmetry G F).perm i = i := rfl
@[simp] lemma shift_one (i : F) : (1 : CellSymmetry G F).shift i = 0 := rfl
@[simp] lemma linear_inv (s : CellSymmetry G F) (x : G) : (s⁻¹).linear x = s.linear.symm x := rfl
@[simp] lemma perm_inv (s : CellSymmetry G F) (i : F) : (s⁻¹).perm i = s.perm.symm i := rfl
@[simp] lemma shift_inv (s : CellSymmetry G F) (j : F) :
    (s⁻¹).shift j = -s.linear.symm (s.shift (s.perm.symm j)) := rfl

instance : Group (CellSymmetry G F) where
  mul_assoc s t u := by ext <;> simp [add_assoc]
  one_mul s := by ext <;> simp
  mul_one s := by ext <;> simp
  inv_mul_cancel s := by ext <;> simp

instance : SMul (CellSymmetry G F) (CellSite G F) where
  smul s x := ⟨s.linear x.cell + s.shift x.label, s.perm x.label⟩

lemma smul_def (s : CellSymmetry G F) (x : CellSite G F) :
    s • x = ⟨s.linear x.cell + s.shift x.label, s.perm x.label⟩ := rfl

/-- The site `σ i` of cell `A n + b i` to which a symmetry sends the site `i` of cell `n`. -/
instance : MulAction (CellSymmetry G F) (CellSite G F) where
  one_smul x := by
    rw [smul_def]
    simp
  mul_smul s t x := by
    simp only [smul_def, linear_mul, perm_mul, shift_mul, map_add, add_assoc]

/-! ## B. Translations form a normal subgroup -/

/-- Translation by `a`: it moves every cell by `a` and fixes the labels. -/
def translation (a : G) : CellSymmetry G F := ⟨AddEquiv.refl G, Equiv.refl F, fun _ => a⟩

@[simp] lemma translation_smul (a : G) (x : CellSite G F) :
    (translation a : CellSymmetry G F) • x = a +ᵥ x := by
  change CellSite.mk (x.cell + a) x.label = CellSite.mk (a + x.cell) x.label
  rw [add_comm]

lemma translation_mul (a b : G) :
    (translation a : CellSymmetry G F) * translation b = translation (a + b) := by
  ext <;> simp [translation, add_comm]

/-- Conjugating a translation by a symmetry gives the translation by the transformed vector. -/
lemma mul_translation_mul_inv (s : CellSymmetry G F) (a : G) :
    s * translation a * s⁻¹ = translation (s.linear a) := by
  ext j <;> simp [translation, add_comm]

/-- The subgroup of translations. -/
def translations (G F : Type*) [AddCommGroup G] : Subgroup (CellSymmetry G F) where
  carrier := {s : CellSymmetry G F | ∃ a, s = translation a}
  one_mem' := ⟨0, by ext <;> simp [translation]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, translation_mul a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    refine inv_eq_of_mul_eq_one_right ?_
    rw [translation_mul, add_neg_cancel]
    ext <;> simp [translation]

instance : (translations G F).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ s
    exact ⟨s.linear a, mul_translation_mul_inv s a⟩

/-- The abstract point group of a crystal: cell symmetries modulo translations. -/
abbrev PointGroup (G F : Type*) [AddCommGroup G] := CellSymmetry G F ⧸ translations G F

end CellSymmetry

/-! ## C. Bond-preserving symmetries -/

namespace PeriodicGraph

variable {G F : Type*} [AddCommGroup G] [Finite F]

/-- Site `i` of the reference cell is bonded to site `j` of the cell `d`. -/
def Bonded (g : PeriodicGraph (Crystal.ofUnitCell G F)) (i j : F) (d : G) : Prop :=
  g.toSimpleGraph.Adj ⟨0, i⟩ ⟨d, j⟩

/-- Bonds between any two cells are the translates of bonds to the reference cell. -/
lemma adj_iff_bonded (g : PeriodicGraph (Crystal.ofUnitCell G F)) (n m : G) (i j : F) :
    g.toSimpleGraph.Adj ⟨n, i⟩ ⟨m, j⟩ ↔ g.Bonded i j (m - n) := by
  have h := g.adj_vadd (-n) ⟨n, i⟩ ⟨m, j⟩
  have h1 : (-n +ᵥ (⟨n, i⟩ : CellSite G F)) = ⟨0, i⟩ := by
    change CellSite.mk (-n + n) i = _
    simp
  have h2 : (-n +ᵥ (⟨m, j⟩ : CellSite G F)) = ⟨m - n, j⟩ := by
    change CellSite.mk (-n + m) j = _
    rw [neg_add_eq_sub]
  change (g.toSimpleGraph.Adj (-n +ᵥ (⟨n, i⟩ : CellSite G F)) (-n +ᵥ (⟨m,
    j⟩ : CellSite G F))) ↔ _ at h
  rw [h1, h2] at h
  exact h.symm

/-- A symmetry preserves the bonds of the graph. -/
def symmetries (g : PeriodicGraph (Crystal.ofUnitCell G F)) : Subgroup (CellSymmetry G F) where
  carrier := {s : CellSymmetry G F | ∀ x y : CellSite G F, g.toSimpleGraph.Adj (s • x) (s • y) ↔
    g.toSimpleGraph.Adj x y}
  one_mem' x y := by simp
  mul_mem' {s t} hs ht x y := by
    rw [mul_smul, mul_smul, hs, ht]
  inv_mem' {s} hs x y := by
    rw [← hs (s⁻¹ • x) (s⁻¹ • y), smul_inv_smul, smul_inv_smul]

/-- **A finite criterion for bond-preserving symmetries.** The data `(A, σ, b)` is a symmetry of
the crystal graph exactly when site `i` is bonded to site `j` in the cell `d` if and only if site
`σ i` is bonded to site `σ j` in the cell `A d + b j - b i`. -/
lemma mem_symmetries_iff (g : PeriodicGraph (Crystal.ofUnitCell G F)) (s : CellSymmetry G F) :
    s ∈ g.symmetries ↔ ∀ i j d, g.Bonded i j d ↔
      g.Bonded (s.perm i) (s.perm j) (s.linear d + s.shift j - s.shift i) := by
  constructor
  · intro h i j d
    have := h ⟨0, i⟩ ⟨d, j⟩
    rw [CellSymmetry.smul_def, CellSymmetry.smul_def, adj_iff_bonded] at this
    simp only [map_zero, zero_add] at this
    exact this.symm
  · intro h x y
    rw [CellSymmetry.smul_def, CellSymmetry.smul_def, adj_iff_bonded, adj_iff_bonded,
      h x.label y.label (y.cell - x.cell)]
    have : s.linear y.cell + s.shift y.label - (s.linear x.cell + s.shift x.label) =
        s.linear (y.cell - x.cell) + s.shift y.label - s.shift x.label := by
      rw [map_sub]; abel
    rw [this]

/-- A bond-preserving symmetry is an automorphism of the bond graph. -/
def symmetryIso (g : PeriodicGraph (Crystal.ofUnitCell G F)) (s : g.symmetries) :
    g.toSimpleGraph ≃g g.toSimpleGraph where
  toEquiv := MulAction.toPerm (s : CellSymmetry G F)
  map_rel_iff' := (s.2 _ _)

/-- Translations are bond-preserving symmetries. -/
lemma translation_mem_symmetries (g : PeriodicGraph (Crystal.ofUnitCell G F)) (a : G) :
    CellSymmetry.translation a ∈ g.symmetries := by
  intro x y
  rw [CellSymmetry.translation_smul, CellSymmetry.translation_smul]
  exact g.adj_vadd a x y

/-- The point group of a periodic graph: its bond-preserving symmetries modulo translations. -/
abbrev pointGroup (g : PeriodicGraph (Crystal.ofUnitCell G F)) :=
  g.symmetries ⧸ (CellSymmetry.translations G F).subgroupOf g.symmetries

/-- **Every automorphism of the bond graph that normalises the translations is a cell symmetry.**
If `φ` is a graph automorphism and `A` an automorphism of the translation group with
`φ (a +ᵥ x) = A a +ᵥ φ x`, then `φ` acts as a bond-preserving cell symmetry with linear part `A`. -/
lemma exists_symmetry_of_equivariant (g : PeriodicGraph (Crystal.ofUnitCell G F))
    (φ : g.toSimpleGraph ≃g g.toSimpleGraph) (A : G ≃+ G)
    (hφ : ∀ (a : G) (x : CellSite G F), φ (a +ᵥ x) = A a +ᵥ φ x) :
    ∃ s ∈ g.symmetries, s.linear = A ∧ ∀ x, s • x = φ x := by
  classical
  let f : F → F := fun i => (φ ⟨0, i⟩).label
  have hφx : ∀ n i, φ ⟨n, i⟩ = ⟨A n + (φ ⟨0, i⟩).cell, (φ ⟨0, i⟩).label⟩ := by
    intro n i
    have : (⟨n, i⟩ : CellSite G F) = n +ᵥ (⟨0, i⟩ : CellSite G F) := by
      change CellSite.mk n i = CellSite.mk (n + 0) i
      simp
    rw [this, hφ]
    rfl
  have hinj : Function.Injective f := by
    intro i j hij
    have e : φ ⟨A.symm ((φ ⟨0, j⟩).cell - (φ ⟨0, i⟩).cell), i⟩ = φ ⟨0, j⟩ := by
      rw [hφx]
      refine CellSite.ext ?_ hij
      simp
    exact (congrArg CellSite.label (φ.injective e))
  let σ : Equiv.Perm F := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  let s : CellSymmetry G F := ⟨A, σ, fun i => (φ ⟨0, i⟩).cell⟩
  have hs : ∀ x, s • x = φ x := by
    rintro ⟨n, i⟩
    rw [hφx]
    rfl
  refine ⟨s, fun x y => ?_, rfl, hs⟩
  rw [hs, hs]
  exact φ.map_rel_iff

end PeriodicGraph

end CondensedMatter.Crystal
