/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Analysis.SpecificLimits.Basic
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Invariant

/-!

# Boxes of a lattice are asymptotically translation invariant

The cubes `{0, …, n-1}^d` of the lattice `ℤ^d` satisfy the Følner condition for the translations.

## i. Overview

A translation by `h` moves the cube `B_n = {0, …, n-1}^d` to a cube that overlaps `B_n` in
`∏_j (n - |h_j|)` points, so the fraction of points not shared is `1 - ∏_j (1 - |h_j|/n)`, which
tends to zero. This is the Følner condition (`ProbabilisticTheory.IsRightFolner`) that makes the
averages of a state over the translations by the elements of `B_n` invariant in the limit.

## ii. Key results

- `box` : the cube `{0, …, m-1}^d` of `ℤ^d`.
- `card_box` : it has `m ^ d` points.
- `isRightFolner_boxes` : the cubes are asymptotically invariant under translations along any
  ultrafilter finer than the filter of large cubes.

## iii. Table of contents

- A. Cubes and their translates
- B. The Følner property

## iv. References

* F. Greenleaf, Invariant Means on Topological Groups.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace Crystal

open Finset Filter Topology ProbabilisticTheory

/-! ## A. Cubes and their translates -/

/-- The cube `{0, …, m-1}^d` of the lattice `ℤ^d`. -/
def box (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) m

lemma card_box (d m : ℕ) : (box d m).card = m ^ d := by
  simp [box, Fintype.card_piFinset]

lemma image_add_box (d m : ℕ) (h : Fin d → ℤ) :
    (box d m).image (· + h) = Fintype.piFinset fun j => Finset.Ico (h j) (m + h j) := by
  ext x
  simp only [box, mem_image, Fintype.mem_piFinset, mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    have := hy j
    simp only [Pi.add_apply]
    omega
  · intro hx
    refine ⟨x - h, fun j => ?_, by simp⟩
    have := hx j
    simp only [Pi.sub_apply]
    omega

lemma card_image_add_box (d m : ℕ) (h : Fin d → ℤ) : ((box d m).image (· + h)).card = m ^ d := by
  rw [card_image_of_injective _ (add_left_injective h), card_box]

/-- The overlap of the cube with its translate. -/
lemma card_inter_box (d m : ℕ) (h : Fin d → ℤ) :
    ((box d m).image (· + h) ∩ box d m).card =
      ∏ j, (Finset.Ico (h j) (m + h j) ∩ Finset.Ico (0 : ℤ) m).card := by
  rw [image_add_box, box, ← Fintype.piFinset_inter, Fintype.card_piFinset]

/-! ## B. The Følner property -/

lemma card_Ico_inter (m : ℕ) (a : ℤ) (ha : |a| ≤ m) :
    (Finset.Ico a (m + a) ∩ Finset.Ico (0 : ℤ) m).card = m - a.natAbs := by
  rw [Finset.Ico_inter_Ico, Int.card_Ico]
  rw [abs_le] at ha
  omega

/-- The number of points of the cube not shared with its translate. -/
lemma card_sdiff_add_card_sdiff (d m : ℕ) (h : Fin d → ℤ) :
    (((box d m).image (· + h) \ box d m).card + (box d m \ (box d m).image (· + h)).card : ℝ) =
      2 * ((m : ℝ) ^ d - ∏ j, ((Finset.Ico (h j) (m + h j) ∩ Finset.Ico (0 : ℤ) m).card : ℝ)) := by
  have h1 := Finset.card_sdiff_add_card_inter ((box d m).image (· + h)) (box d m)
  have h2 := Finset.card_sdiff_add_card_inter (box d m) ((box d m).image (· + h))
  rw [Finset.inter_comm, card_inter_box] at h2
  rw [card_inter_box, card_image_add_box] at h1
  have h1' : (((box d m).image (· + h) \ box d m).card : ℝ) + (∏ j, ((Finset.Ico (h j) (m + h j) ∩
      Finset.Ico (0 : ℤ) m).card : ℝ)) = (m : ℝ) ^ d := by exact_mod_cast h1
  have h2' : ((box d m \ (box d m).image (· + h)).card : ℝ) + (∏ j, ((Finset.Ico (h j) (m + h j) ∩
      Finset.Ico (0 : ℤ) m).card : ℝ)) = (m : ℝ) ^ d := by
    rw [card_box] at h2; exact_mod_cast h2
  linarith

/-- **The cubes are asymptotically invariant under translation**: the fraction of the points of
`{0, …, n}^d` that are not shared with a fixed translate tends to zero. -/
lemma tendsto_box_sdiff (d : ℕ) (h : Fin d → ℤ) :
    Tendsto (fun n : ℕ => (((box d (n + 1)).image (· + h) \ box d (n + 1)).card +
      (box d (n + 1) \ (box d (n + 1)).image (· + h)).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d)
      atTop (𝓝 0) := by
  have hprod : Tendsto (fun n : ℕ => ∏ j, (((Finset.Ico (h j) ((n + 1 : ℕ) + h j) ∩
      Finset.Ico (0 : ℤ) (n + 1 : ℕ)).card : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (∏ _j : Fin d, 1)) := by
    refine tendsto_finsetProd _ fun j _ => ?_
    have h1 : Tendsto (fun n : ℕ => 1 - ((h j).natAbs : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop (by
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (h j).natAbs] with n hn
    have hab : |h j| ≤ ((n + 1 : ℕ) : ℤ) := by
      calc |h j| = ((h j).natAbs : ℤ) := Int.abs_eq_natAbs _
        _ ≤ _ := by exact_mod_cast (by omega : (h j).natAbs ≤ n + 1)
    rw [card_Ico_inter _ _ hab]
    have hle : (h j).natAbs ≤ n + 1 := by omega
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Nat.cast_sub hle, sub_div, div_self hpos.ne']
  simp only [Finset.prod_const_one] at hprod
  have key : Tendsto (fun n : ℕ => 2 * (1 - ∏ j, (((Finset.Ico (h j) ((n + 1 : ℕ) + h j) ∩
      Finset.Ico (0 : ℤ) (n + 1 : ℕ)).card : ℝ) / ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 (2 * (1 - 1))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hprod)
  rw [sub_self, mul_zero] at key
  refine key.congr fun n => ?_
  rw [card_sdiff_add_card_sdiff, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
  field_simp

/-- The cubes `{0, …, n}^d`, as finite sets of the translation group. -/
def boxes (d n : ℕ) : Finset (Multiplicative (Fin d → ℤ)) :=
  (box d (n + 1)).map Multiplicative.ofAdd.toEmbedding

lemma image_mul_boxes (d n : ℕ) (h : Multiplicative (Fin d → ℤ)) :
    (boxes d n).image (· * h) =
      ((box d (n + 1)).image (· + Multiplicative.toAdd h)).map
        Multiplicative.ofAdd.toEmbedding := by
  ext x
  simp only [boxes, Finset.mem_image, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y + Multiplicative.toAdd h, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd y, ⟨y, hy, rfl⟩, rfl⟩

/-- **The cubes are a Følner family** for the translations of `ℤ^d`, along any ultrafilter on
`ℕ` finer than the filter of large cubes. -/
lemma isRightFolner_boxes (d : ℕ) (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    IsRightFolner (boxes d) 𝒰 := by
  intro h
  refine ((tendsto_box_sdiff d (Multiplicative.toAdd h)).mono_left h𝒰).congr fun n => ?_
  rw [image_mul_boxes, boxes, ← Finset.map_sdiff, ← Finset.map_sdiff, Finset.card_map,
    Finset.card_map, Finset.card_map, card_box]
  push_cast
  rfl

end Crystal

end CondensedMatter

end
