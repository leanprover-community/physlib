/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Cubic

/-!

# The point group of a crystal with several sites per cell

The point group of a crystal with several sites per cell is compared with the point group of a
Bravais lattice, the lattice of differences of its bonds.

## i. Overview

For a graph given by a list of bonds, the displacements `d` for which site `i` of the reference
cell is bonded to site `j` of the cell `d` form a finite set `E i j`. A cell symmetry `(A, σ, b)`
preserves the bonds exactly when it maps each `E i j` onto `E (σ i) (σ j)` by
`d ↦ A d + b j - b i`, a finite condition.

If site `i` is bonded to site `j` in the cells `d₁` and `d₂`, the difference `d₁ - d₂` is a
translation between two sites with the same label. A symmetry maps both bonds to bonds with
common labels, so its linear part maps these differences to differences. When the differences are
the neighbours of a Bravais lattice, for instance the face-centred cubic lattice for diamond or the
triangular lattice for the honeycomb, the linear parts of the symmetries lie in the point group
of that lattice. If moreover only translations have the identity as linear part, and every point
operation of the lattice lifts to a symmetry, the two point groups are isomorphic. Both conditions
reduce to finite checks.

## ii. Key results

- `PeriodicGraph.bondDisplacements` : the finite sets `E i j` of a bond list.
- `PeriodicGraph.mem_symmetries_ofBonds_iff` : the finite criterion for symmetries.
- `PeriodicGraph.bondDifferences` : the differences `d₁ - d₂` of displacements in a common `E i j`.
- `PeriodicGraph.linear_mem_bondDifferences_iff` : linear parts of symmetries preserve them.
- `PeriodicGraph.pointGroupMulEquivOfLift` : the point group is that of the lattice of
  differences, when the linear part is injective modulo translations and every point operation
  lifts.
- `PeriodicGraph.mem_translations_of_linear_eq` and `PeriodicGraph.lift_of_admissible` : the
  finite checks of these two conditions.

## iii. Table of contents

- A. Bonded displacements of a bond list
- B. Differences of bonds
- C. Comparison of point groups
- D. Finite checks

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

namespace PeriodicGraph

variable {G F : Type*} [AddCommGroup G] [DecidableEq G] [Fintype F] [DecidableEq F]

/-! ## A. Bonded displacements of a bond list -/

/-- The displacements `d` such that site `i` of the reference cell is bonded to site `j` of the
cell `d`, in the graph of a bond list. -/
def bondDisplacements (bonds : List (Bond G F)) (i j : F) : Finset G :=
  (((bonds.filter fun b => b.source = i ∧ b.target = j).map Bond.displacement ++
    (bonds.filter fun b => b.source = j ∧ b.target = i).map fun b =>
      -b.displacement).toFinset).filter fun d => d ≠ 0 ∨ i ≠ j

lemma bonded_ofBonds_iff (bonds : List (Bond G F)) (i j : F) (d : G) :
    (ofBonds bonds).Bonded i j d ↔ d ∈ bondDisplacements bonds i j := by
  change ((⟨0, i⟩ : CellSite G F) ≠ ⟨d, j⟩ ∧ ∃ b ∈ bonds,
    b.Links ⟨0, i⟩ ⟨d, j⟩ ∨ b.Links ⟨d, j⟩ ⟨0, i⟩) ↔ _
  simp only [bondDisplacements, Finset.mem_filter, List.mem_toFinset, List.mem_append,
    List.mem_map, List.mem_filter, decide_eq_true_eq, Bond.Links, ne_eq, CellSite.mk.injEq,
    zero_add, not_and_or]
  constructor
  · rintro ⟨h0, b, hb, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, h⟩⟩
    · exact ⟨Or.inl ⟨b, ⟨hb, rfl, rfl⟩, rfl⟩, h0.imp (fun h => (Ne.symm h)) id⟩
    · exact ⟨Or.inr ⟨b, ⟨hb, rfl, rfl⟩, (neg_eq_of_add_eq_zero_left h.symm)⟩,
        h0.imp (fun h => (Ne.symm h)) id⟩
  · rintro ⟨⟨b, ⟨hb, rfl, rfl⟩, rfl⟩ | ⟨b, ⟨hb, rfl, rfl⟩, rfl⟩, h0⟩
    · exact ⟨h0.imp (fun h => (Ne.symm h)) id, b, hb, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨h0.imp (fun h => (Ne.symm h)) id, b, hb, Or.inr ⟨rfl, rfl, (neg_add_cancel _).symm⟩⟩

/-- **A finite criterion for the symmetries of the graph of a bond list**: `(A, σ, b)` is a
symmetry exactly when `d ↦ A d + b j - b i` maps `E i j` onto `E (σ i) (σ j)` for all labels. -/
lemma mem_symmetries_ofBonds_iff (bonds : List (Bond G F)) (s : CellSymmetry G F) :
    s ∈ (ofBonds bonds).symmetries ↔ ∀ i j, (bondDisplacements bonds i j).image
      (fun d => s.linear d + s.shift j - s.shift i) =
        bondDisplacements bonds (s.perm i) (s.perm j) := by
  simp only [mem_symmetries_iff, bonded_ofBonds_iff]
  refine ⟨fun h i j => Finset.ext fun e => ⟨fun he => ?_, fun he => ?_⟩, fun h i j d => ?_⟩
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact (h i j d).1 hd
  · refine Finset.mem_image.mpr ⟨s.linear.symm (e - (s.shift j - s.shift i)), ?_, ?_⟩
    · refine (h i j _).2 ?_
      simpa [sub_add_cancel, add_sub_assoc] using he
    · simp [add_sub_assoc]
  · rw [← h i j]
    refine ⟨fun hd => Finset.mem_image_of_mem _ hd, fun he => ?_⟩
    obtain ⟨d', hd', he'⟩ := Finset.mem_image.mp he
    have e : s.linear d' = s.linear d := add_right_cancel (b := s.shift j - s.shift i)
      (by simpa only [add_sub_assoc] using he')
    rwa [← s.linear.injective e]

/-! ## B. Differences of bonds -/

/-- The nonzero differences `d₁ - d₂` of two displacements in a common `E i j`: translations
between two sites with the same label that are bonded to a common site. -/
def bondDifferences (bonds : List (Bond G F)) : Finset G :=
  ((Finset.univ : Finset (F × F)).biUnion fun p =>
    (bondDisplacements bonds p.1 p.2 ×ˢ bondDisplacements bonds p.1 p.2).image
      fun q => q.1 - q.2).erase 0

lemma mem_bondDifferences (bonds : List (Bond G F)) (e : G) :
    e ∈ bondDifferences bonds ↔ e ≠ 0 ∧ ∃ i j, ∃ d₁ ∈ bondDisplacements bonds i j,
      ∃ d₂ ∈ bondDisplacements bonds i j, e = d₁ - d₂ := by
  simp only [bondDifferences, Finset.mem_erase, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_product, Prod.exists]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨i, j, d₁, d₂, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨i, j, d₁, h₁, d₂, h₂, rfl⟩
  · rintro ⟨i, j, d₁, h₁, d₂, h₂, rfl⟩
    exact ⟨i, j, d₁, d₂, ⟨h₁, h₂⟩, rfl⟩

lemma linear_mem_bondDifferences {bonds : List (Bond G F)} {s : CellSymmetry G F}
    (hs : s ∈ (ofBonds bonds).symmetries) {e : G} (he : e ∈ bondDifferences bonds) :
    s.linear e ∈ bondDifferences bonds := by
  rw [mem_bondDifferences] at he ⊢
  obtain ⟨h0, i, j, d₁, h₁, d₂, h₂, rfl⟩ := he
  have h := (mem_symmetries_ofBonds_iff bonds s).1 hs i j
  have m₁ := Finset.mem_image_of_mem (fun d => s.linear d + s.shift j - s.shift i) h₁
  have m₂ := Finset.mem_image_of_mem (fun d => s.linear d + s.shift j - s.shift i) h₂
  rw [h] at m₁ m₂
  refine ⟨fun h' => h0 ?_, s.perm i, s.perm j, _, m₁, _, m₂, ?_⟩
  · rw [← map_zero s.linear] at h'
    exact s.linear.injective h'
  · rw [map_sub]
    abel

/-- **The linear part of a symmetry preserves the differences of bonds.** -/
lemma linear_mem_bondDifferences_iff {bonds : List (Bond G F)} {s : CellSymmetry G F}
    (hs : s ∈ (ofBonds bonds).symmetries) (e : G) :
    s.linear e ∈ bondDifferences bonds ↔ e ∈ bondDifferences bonds := by
  refine ⟨fun he => ?_, linear_mem_bondDifferences hs⟩
  have h := linear_mem_bondDifferences ((ofBonds bonds).symmetries.inv_mem hs) he
  change s.linear.symm (s.linear e) ∈ _ at h
  rwa [AddEquiv.symm_apply_apply] at h

/-! ## C. Comparison of point groups -/

variable {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F] {bonds : List (Bond (Fin n → ℤ) F)}
  {bonds' : List (Bond (Fin n → ℤ) Unit)}

/-- The linear part of a symmetry, as an element of the point stabilizer of the lattice of
differences. -/
def linearToLattice (hΔ : bondDifferences bonds = bondNeighbors bonds') :
    (ofBonds bonds).symmetries →* (ofBonds bonds').pointStabilizer :=
  ((linearHom (Fin n → ℤ) F).comp (ofBonds bonds).symmetries.subtype).codRestrict _ fun s d => by
    rw [bonded_ofBonds_unit, bonded_ofBonds_unit, ← hΔ]
    exact linear_mem_bondDifferences_iff s.2 d

lemma ker_linearToLattice (hΔ : bondDifferences bonds = bondNeighbors bonds')
    (hker : ∀ s ∈ (ofBonds bonds).symmetries, s.linear = AddEquiv.refl _ →
      s ∈ CellSymmetry.translations (Fin n → ℤ) F) :
    (linearToLattice hΔ).ker =
      (CellSymmetry.translations (Fin n → ℤ) F).subgroupOf (ofBonds bonds).symmetries := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact hker s s.2
      (congrArg (fun A : (ofBonds bonds').pointStabilizer => Multiplicative.toAdd A.1) h)
  · rintro ⟨a, ha⟩
    refine Subtype.ext ?_
    change Multiplicative.ofAdd (s : CellSymmetry (Fin n → ℤ) F).linear = 1
    rw [ha]
    rfl

/-- **The point group of a crystal with several sites per cell is the point group of its lattice
of differences**, if only translations have the identity as linear part and every point
operation of the lattice lifts to a symmetry. -/
noncomputable def pointGroupMulEquivOfLift (hΔ : bondDifferences bonds = bondNeighbors bonds')
    (hker : ∀ s ∈ (ofBonds bonds).symmetries, s.linear = AddEquiv.refl _ →
      s ∈ CellSymmetry.translations (Fin n → ℤ) F)
    (hlift : Function.Surjective (linearToLattice hΔ)) :
    (ofBonds bonds).pointGroup ≃* (ofBonds bonds').pointGroup :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_linearToLattice hΔ hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hlift)).trans (pointGroupEquiv _).symm

/-! ## D. Finite checks -/

/-- The candidates for the cell offsets of a symmetry, relative to the label `i₀`. -/
def shiftCandidates (bonds : List (Bond (Fin n → ℤ) F)) (i₀ : F) : Finset (Fin n → ℤ) :=
  insert 0 (((Finset.univ : Finset (F × F)).biUnion fun p =>
    bondDisplacements bonds p.1 p.2).biUnion fun e =>
      ((Finset.univ : Finset F).biUnion fun i => bondDisplacements bonds i₀ i).image (e - ·))

/-- **Only translations have the identity as linear part**, if every label is bonded to `i₀` and
this holds for the finitely many candidate offsets. -/
lemma mem_translations_of_linear_eq (i₀ : F)
    (hconn : ∀ i, i = i₀ ∨ (bondDisplacements bonds i₀ i).Nonempty)
    (h : ∀ σ : Equiv.Perm F, ∀ r ∈ Fintype.piFinset fun _ => shiftCandidates bonds i₀,
      r i₀ = 0 → (∀ i j, (bondDisplacements bonds i j).image (fun d => d + r j - r i) =
        bondDisplacements bonds (σ i) (σ j)) → σ = 1 ∧ r = 0)
    (s : CellSymmetry (Fin n → ℤ) F) (hs : s ∈ (ofBonds bonds).symmetries)
    (hL : s.linear = AddEquiv.refl _) : s ∈ CellSymmetry.translations (Fin n → ℤ) F := by
  have hc := (mem_symmetries_ofBonds_iff bonds s).1 hs
  simp only [hL, AddEquiv.refl_apply] at hc
  set r : F → Fin n → ℤ := fun i => s.shift i - s.shift i₀
  have hr : ∀ i j, (bondDisplacements bonds i j).image (fun d => d + r j - r i) =
      bondDisplacements bonds (s.perm i) (s.perm j) := fun i j => by
    rw [← hc i j]
    congr 1
    funext d
    simp only [r]
    abel
  have hmem : r ∈ Fintype.piFinset fun _ => shiftCandidates bonds i₀ := by
    rw [Fintype.mem_piFinset]
    intro i
    rcases hconn i with rfl | ⟨d₀, hd₀⟩
    · simp [r, shiftCandidates]
    · have he : d₀ + r i - r i₀ ∈ bondDisplacements bonds (s.perm i₀) (s.perm i) :=
        hr i₀ i ▸ Finset.mem_image_of_mem _ hd₀
      simp only [shiftCandidates, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and, Finset.mem_image, Prod.exists]
      refine Or.inr ⟨_, ⟨s.perm i₀, s.perm i, he⟩, d₀, ⟨i, hd₀⟩, ?_⟩
      simp [r]
  obtain ⟨hσ, h0⟩ := h s.perm r hmem (by simp [r]) hr
  refine ⟨s.shift i₀, CellSymmetry.ext ?_ hσ (funext fun i => sub_eq_zero.mp (congrFun h0 i))⟩
  rw [hL]
  rfl

/-- **Every point operation of the lattice of differences lifts to a symmetry**, if every
admissible tuple of neighbours does, with a permutation and offsets `b i ∈ T i`. -/
lemma lift_of_admissible (hΔ : bondDifferences bonds = bondNeighbors bonds')
    (hN : ∀ j, (Pi.single j 1 : Fin n → ℤ) ∈ bondNeighbors bonds') (T : F → Finset (Fin n → ℤ))
    (h : ∀ w : Fin n → bondNeighbors bonds', Admissible (bondNeighbors bonds') (fun j => w j) →
      ∃ σ : Equiv.Perm F, ∃ b ∈ Fintype.piFinset T, ∀ i j, (bondDisplacements bonds i j).image
        (fun d => act (fun j => w j) d + b j - b i) = bondDisplacements bonds (σ i) (σ j)) :
    Function.Surjective (linearToLattice hΔ) := by
  intro A
  set v := (pointStabilizerEquiv hN (bonded_ofBonds_unit bonds') A).1
  have hv : Admissible (bondNeighbors bonds') v :=
    (pointStabilizerEquiv hN (bonded_ofBonds_unit bonds') A).2
  have hA : ∀ d, (Multiplicative.toAdd A.1 : AddAut (Fin n → ℤ)) d = act v d :=
    apply_eq_act _
  obtain ⟨σ, b, -, hb⟩ := h (fun j => ⟨v j, hv.mem j⟩) hv
  have hs : (⟨Multiplicative.toAdd A.1, σ, b⟩ : CellSymmetry (Fin n → ℤ) F) ∈
      (ofBonds bonds).symmetries := by
    rw [mem_symmetries_ofBonds_iff]
    intro i j
    simp only [hA]
    exact hb i j
  exact ⟨⟨_, hs⟩, Subtype.ext rfl⟩

end PeriodicGraph

end CondensedMatter.Crystal
