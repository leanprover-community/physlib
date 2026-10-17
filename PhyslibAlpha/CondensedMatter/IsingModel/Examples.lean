/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.IsingModel.Basic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Basic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.ThreeDimensional
public import Mathlib.Analysis.SpecificLimits.Basic

/-!

# Classical Ising models on standard crystals

## i. Overview

Uniform exchange and field parameters turn the existing crystal bond graphs into classical
Ising models. The hypercubic model works in arbitrary dimension; the square lattice is its
two-dimensional specialization. Honeycomb uses the same energy definition with its three
bonds per site. Geometry plays no role in either construction.

The main result concerns the ferromagnetic ground state of any crystal in `d` dimensions,
with any number of sites per unit cell. Take a hypercube of `n + 1` unit cells along each
lattice vector. Spins near its surface miss some of their neighbors, but they form a vanishing
fraction of the sample as it grows. The ground-state energy per spin therefore converges to
`-(J / 2) z̄ - |h|`, where `z̄` is the mean coordination of one unit cell: every spin
contributes `-J` for half of its `z̄` bonds, and the aligned field contributes `-|h|`.
The square lattice (`z̄ = 4`) and the honeycomb lattice (`z̄ = 3`) are instances.

## ii. Key results

- `IsingModel.hypercubic`, `IsingModel.square`, `IsingModel.honeycomb` : uniform Ising models on
  the standard bond graphs.
- `IsingModel.Hypercube.tendsto_averageCoordination` : surface spins form a vanishing fraction of a
  growing hypercube of cells.
- `IsingModel.tendsto_groundEnergyDensity_hypercube` : the ferromagnetic ground-state energy per
  spin of any crystal converges to `-(J / 2) z̄ - |h|`.
- `IsingModel.tendsto_groundEnergyDensity_square`, `..._honeycomb` : the square and honeycomb
  lattices.
- `IsingModel.tendsto_groundEnergyDensity_of_card` : the density for a crystal in which every
  site has `q` neighbours, with the diamond, fcc, bcc and hcp lattices as instances.

## iii. Table of contents

- A. Ising models on the standard crystals
- B. Hypercubes of unit cells in an arbitrary crystal
- C. Ground-state energy density of a ferromagnetic crystal
- D. Regular crystals

## iv. References

* E. Ising, Beitrag zur Theorie des Ferromagnetismus.

-/

@[expose] public section

namespace CondensedMatter.IsingModel

/-! ## A. Ising models on the standard crystals -/

/-- Uniform classical Ising interactions on the hypercubic bond graph in arbitrary dimension. -/
def hypercubic (d : ℕ) (J h : ℝ) : IsingModel (Crystal.hypercubicGraph d).toSimpleGraph :=
  ⟨J, h⟩

/-- The square-lattice model, specializing the hypercubic construction to two dimensions. -/
def square (J h : ℝ) : IsingModel Crystal.squareGraph.toSimpleGraph :=
  hypercubic 2 J h

/-- The honeycomb classical Ising model, using the crystal's existing bonds. -/
def honeycomb (J h : ℝ) : IsingModel Crystal.honeycombGraph.toSimpleGraph :=
  ⟨J, h⟩

/-! ## B. Hypercubes of unit cells in an arbitrary crystal -/

namespace Hypercube

open scoped Classical

variable {d : ℕ} {F : Type*} [Fintype F]

/-- The cells `{0, …, n}^d` of a hypercube of side `n + 1` unit cells. -/
def cells (d n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc 0 (n : ℤ)

lemma mem_cells {d n : ℕ} (c : Fin d → ℤ) :
    c ∈ cells d n ↔ ∀ i, 0 ≤ c i ∧ c i ≤ n := by
  simp [cells, Fintype.mem_piFinset]

lemma card_cells (d n : ℕ) : (cells d n).card = (n + 1) ^ d := by
  simp [cells, Fintype.card_piFinset]

/-- The cells at least `R` unit cells away from every face of the hypercube. -/
def interior (d n R : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (R : ℤ) (n - R)

lemma mem_interior {d n R : ℕ} (c : Fin d → ℤ) :
    c ∈ interior d n R ↔ ∀ i, (R : ℤ) ≤ c i ∧ c i ≤ n - R := by
  simp [interior, Fintype.mem_piFinset]

/-- The interior of a hypercube of side `n + 1` is a hypercube of side `n + 1 - 2 R`. -/
lemma card_interior (d n R : ℕ) : (interior d n R).card = (n + 1 - 2 * R) ^ d := by
  have : ((n : ℤ) - R + 1 - R).toNat = n + 1 - 2 * R := by omega
  simp [interior, Fintype.card_piFinset, this]

lemma interior_subset {d n R : ℕ} : interior d n R ⊆ cells d n := by
  intro c hc
  rw [mem_interior] at hc
  rw [mem_cells]
  intro i
  have := hc i
  omega

/-- All sites of the crystal with unit cell labels `F` that lie in the cells `B`. -/
def region (B : Finset (Fin d → ℤ)) : Finset (Crystal.ofUnitCell (Fin d → ℤ) F).Site :=
  (B ×ˢ Finset.univ).map ⟨fun p => ⟨p.1, p.2⟩,
    fun _ _ h => Prod.ext (congrArg Crystal.CellSite.cell h) (congrArg Crystal.CellSite.label h)⟩

lemma mem_region {B : Finset (Fin d → ℤ)} (x : (Crystal.ofUnitCell (Fin d → ℤ) F).Site) :
    x ∈ region B ↔ x.cell ∈ B :=
  ⟨fun h => by obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp h; exact (Finset.mem_product.mp hp).1,
    fun h => Finset.mem_map.mpr
      ⟨(x.cell, x.label), Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩⟩

lemma sum_region {M : Type*} [AddCommMonoid M] {B : Finset (Fin d → ℤ)}
    (f : (Crystal.ofUnitCell (Fin d → ℤ) F).Site → M) :
    ∑ x ∈ region B, f x = ∑ c ∈ B, ∑ i : F, f ⟨c, i⟩ := by
  rw [region, Finset.sum_map, Finset.sum_product]
  rfl

lemma card_region (B : Finset (Fin d → ℤ)) :
    (region (F := F) B).card = B.card * Fintype.card F := by
  simp [region]

/-- Every hypercube contains at least one site if the unit cell does. -/
lemma region_cells_nonempty [Nonempty F] (d n : ℕ) :
    (region (F := F) (cells d n)).Nonempty := by
  rw [← Finset.card_pos, card_region]
  rw [card_cells]
  exact Nat.mul_pos (by positivity) Fintype.card_pos

variable (g : Crystal.PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ) F))

/-- Bonds have a finite range: there is a distance `R`, in units of the cell spacing, beyond
which no two sites are connected. This holds because the coordination is finite and every
site is a translate of one of finitely many reference sites. -/
lemma exists_range :
    ∃ R : ℕ, ∀ x y : (Crystal.ofUnitCell (Fin d → ℤ) F).Site,
      g.toSimpleGraph.Adj x y → ∀ k, |y.cell k - x.cell k| ≤ R := by
  refine ⟨∑ i : F, ∑ z ∈ g.neighbors ⟨0, i⟩, ∑ k, (z.cell k).natAbs, ?_⟩
  intro x y hxy k
  set z : (Crystal.ofUnitCell (Fin d → ℤ) F).Site := (-x.cell) +ᵥ y with hz
  have hx : (-x.cell) +ᵥ x =
      (⟨0, x.label⟩ : (Crystal.ofUnitCell (Fin d → ℤ) F).Site) := by
    change Crystal.CellSite.mk (-x.cell + x.cell) x.label = _
    simp
  have hzn : z ∈ g.neighbors ⟨0, x.label⟩ := by
    rw [g.mem_neighbors, ← hx]
    exact (g.adj_vadd _ _ _).mpr hxy
  have h1 : (z.cell k).natAbs ≤ ∑ k', (z.cell k').natAbs :=
    Finset.single_le_sum (f := fun k' => (z.cell k').natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  have h2 := Finset.single_le_sum (f := fun z : (Crystal.ofUnitCell (Fin d → ℤ) F).Site =>
    ∑ k', (z.cell k').natAbs) (fun _ _ => Nat.zero_le _) hzn
  have h3 := Finset.single_le_sum (f := fun i : F =>
    ∑ z ∈ g.neighbors ⟨0, i⟩, ∑ k', (z.cell k').natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ x.label)
  have h4 : |y.cell k - x.cell k| = ((z.cell k).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    change _ = |-x.cell k + y.cell k|
    rw [neg_add_eq_sub]
  rw [h4]
  exact_mod_cast h1.trans (h2.trans h3)

/-- Sites in the interior of a hypercube have all their neighbors in the sample, once
the interior is at least the bond range away from the surface. -/
lemma neighbors_subset_region {n R : ℕ}
    (hR : ∀ x y : (Crystal.ofUnitCell (Fin d → ℤ) F).Site,
      g.toSimpleGraph.Adj x y → ∀ k, |y.cell k - x.cell k| ≤ R)
    {x : (Crystal.ofUnitCell (Fin d → ℤ) F).Site} (hx : x.cell ∈ interior d n R) :
    g.neighbors x ⊆ region (cells d n) := by
  intro y hy
  rw [g.mem_neighbors] at hy
  rw [mem_region, mem_cells]
  intro k
  have h1 := abs_le.mp (hR x y hy k)
  have h2 := (mem_interior x.cell).mp hx k
  omega

/-- The mean number of neighbors per site of a crystal with unit cell `F`: the coordination
averaged over the sites of one unit cell. -/
noncomputable def meanCoordination : ℝ :=
  (∑ i : F, ((g.neighbors ⟨0, i⟩).card : ℝ)) / Fintype.card F

/-- Summing the coordination over the sites of a set of cells counts every unit-cell
coordination once per cell. -/
lemma sum_card_neighbors_region (B : Finset (Fin d → ℤ)) :
    ∑ x ∈ region B, (g.neighbors x).card =
      B.card * ∑ i : F, (g.neighbors ⟨0, i⟩).card := by
  rw [sum_region]
  have : ∀ (c : Fin d → ℤ) (i : F),
      (g.neighbors ⟨c, i⟩).card = (g.neighbors ⟨0, i⟩).card :=
    fun c i => Crystal.PeriodicGraph.card_neighbors_cell g c i
  simp only [this, Finset.sum_const, smul_eq_mul]

/-- The ordered bonds inside a region number at most the total coordination of its sites. -/
lemma bondCountBetween_le (Λ : Finset (Crystal.ofUnitCell (Fin d → ℤ) F).Site) :
    g.toSimpleGraph.bondCountBetween Λ Λ ≤ ∑ x ∈ Λ, (g.neighbors x).card := by
  refine Finset.sum_le_sum fun x _ => Finset.card_le_card fun y hy => ?_
  rw [g.mem_neighbors]
  exact (Finset.mem_filter.mp hy).2

/-- Every site in the interior of the hypercube has all its bonds inside the hypercube. -/
lemma sum_interior_le_bondCountBetween {n R : ℕ}
    (hR : ∀ x y : (Crystal.ofUnitCell (Fin d → ℤ) F).Site,
      g.toSimpleGraph.Adj x y → ∀ k, |y.cell k - x.cell k| ≤ R) :
    ∑ x ∈ region (F := F) (interior d n R), (g.neighbors x).card ≤
      g.toSimpleGraph.bondCountBetween (region (cells d n)) (region (cells d n)) := by
  calc ∑ x ∈ region (F := F) (interior d n R), (g.neighbors x).card
      ≤ ∑ x ∈ region (F := F) (interior d n R),
          ((region (cells d n)).filter (g.toSimpleGraph.Adj x)).card := by
        refine Finset.sum_le_sum fun x hx => Finset.card_le_card fun y hy => ?_
        exact Finset.mem_filter.mpr
          ⟨neighbors_subset_region g hR ((mem_region x).mp hx) hy, (g.mem_neighbors x y).mp hy⟩
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        exact (mem_region x).mpr (interior_subset ((mem_region x).mp hx))

variable [Nonempty F]

/-- The average coordination of hypercubes converges to the mean coordination of the
crystal: the sites near the surface, whose neighbors are cut off, become a vanishing fraction
of the sample. -/
lemma tendsto_averageCoordination :
    Filter.Tendsto
      (fun n : ℕ => (g.toSimpleGraph.bondCountBetween (region (cells d n))
        (region (cells d n)) : ℝ) / (region (F := F) (cells d n)).card)
      Filter.atTop (nhds (meanCoordination g)) := by
  obtain ⟨R, hR⟩ := exists_range g
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  -- the fraction of sites in the interior tends to one
  have hfrac : Filter.Tendsto
      (fun n : ℕ => (((n + 1 - 2 * R : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ d)
      Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (2 * R : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * R : ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).pow d
    simp only [sub_zero, one_pow] at h1
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (2 * R)] with n hn
    congr 1
    rw [Nat.cast_sub (by omega)]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hlim := hfrac.mul_const (meanCoordination g)
  rw [one_mul] at hlim
  set S : ℕ := ∑ i : F, (g.neighbors ⟨0, i⟩).card with hS
  have hz : meanCoordination g = (S : ℝ) / Fintype.card F := by
    simp [meanCoordination, hS]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun n => ?_) (fun n => ?_)
  all_goals
    have hcard : ((region (F := F) (cells d n)).card : ℝ) =
        ((n : ℝ) + 1) ^ d * Fintype.card F := by
      rw [card_region, card_cells]; push_cast; ring
    have hpos : (0 : ℝ) < (region (F := F) (cells d n)).card := by
      exact_mod_cast Finset.card_pos.mpr (region_cells_nonempty d n)
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  · rw [le_div_iff₀ hpos]
    have h := sum_interior_le_bondCountBetween (n := n) g hR
    rw [sum_card_neighbors_region, card_interior] at h
    have h' : ((n + 1 - 2 * R : ℕ) : ℝ) ^ d * S ≤
        (g.toSimpleGraph.bondCountBetween (region (cells d n)) (region (cells d n)) : ℝ) := by
      exact_mod_cast h
    rw [hcard, hz]
    calc _ = ((n + 1 - 2 * R : ℕ) : ℝ) ^ d * S := by
          push_cast; rw [div_pow]; field_simp
      _ ≤ _ := h'
  · rw [div_le_iff₀ hpos]
    have h := (bondCountBetween_le g (region (F := F) (cells d n))).trans
      (sum_card_neighbors_region g (cells d n)).le
    rw [card_cells] at h
    have h' : (g.toSimpleGraph.bondCountBetween (region (cells d n)) (region (cells d n)) :
        ℝ) ≤ (((n + 1) ^ d * S : ℕ) : ℝ) := by exact_mod_cast h
    rw [hcard, hz]
    calc _ ≤ _ := h'
      _ = _ := by push_cast; field_simp

end Hypercube

/-! ## C. Ground-state energy density of a ferromagnetic crystal -/

section Ferromagne

open Hypercube

variable {d : ℕ} {F : Type*} [Fintype F] [Nonempty F]
  {g : Crystal.PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ) F)}

/-- The ground-state energy per spin of a ferromagnetic Ising model on any crystal, in
hypercubes of growing size, converges to `-(J / 2) z̄ - |h|`, where `z̄` is the mean
coordination. Each spin carries the energy `-J` for half of its bonds; the missing bonds
at the surface of the sample do not contribute in the limit. The field may have either
sign, and the lattice may have several sites per unit cell. -/
lemma tendsto_groundEnergyDensity_hypercube (I : IsingModel g.toSimpleGraph) (hJ : 0 ≤ I.J) :
    Filter.Tendsto (fun n : ℕ => I.groundEnergyDensity (region (cells d n)))
      Filter.atTop (nhds (-(I.J / 2) * meanCoordination g - |I.h|)) :=
  I.tendsto_groundEnergyDensity hJ _ (fun n => region_cells_nonempty d n) _
    (tendsto_averageCoordination g)

end Ferromagne

/-- The honeycomb lattice has three neighbors per site. -/
lemma meanCoordination_honeycomb : Hypercube.meanCoordination Crystal.honeycombGraph = 3 := by
  have h : ∑ i : Crystal.HoneycombLabel,
      (Crystal.honeycombGraph.neighbors ⟨0, i⟩).card = 6 := by
    decide +kernel
  have h2 : Fintype.card Crystal.HoneycombLabel = 2 := rfl
  rw [Hypercube.meanCoordination, h2]
  rw [← Nat.cast_sum, h]
  norm_num


/-- The ground-state energy per spin of the ferromagnetic honeycomb Ising model converges to
`-3 J / 2 - |h|` as the sample grows. -/
lemma tendsto_groundEnergyDensity_honeycomb (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (honeycomb J h).groundEnergyDensity
        (Hypercube.region (Hypercube.cells 2 n)))
      Filter.atTop (nhds (-(3 * J / 2) - |h|)) := by
  have : Nonempty Crystal.HoneycombLabel := ⟨.A⟩
  have := tendsto_groundEnergyDensity_hypercube (honeycomb J h) hJ
  rw [meanCoordination_honeycomb] at this
  convert this using 2
  simp only [honeycomb]
  ring

/-- The square lattice has four neighbors per site. -/
lemma meanCoordination_square : Hypercube.meanCoordination Crystal.squareGraph = 4 := by
  have h : ∑ i : Unit, (Crystal.squareGraph.neighbors ⟨0, i⟩).card = 4 := by
    decide +kernel
  rw [Hypercube.meanCoordination, ← Nat.cast_sum, h]
  norm_num

/-- The ground-state energy per spin of the ferromagnetic square-lattice Ising model
converges to `-2 J - |h|` as the sample grows. -/
lemma tendsto_groundEnergyDensity_square (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (square J h).groundEnergyDensity
        (Hypercube.region (Hypercube.cells 2 n)))
      Filter.atTop (nhds (-(2 * J) - |h|)) := by
  have := tendsto_groundEnergyDensity_hypercube (square J h) hJ
  rw [meanCoordination_square] at this
  convert this using 2
  simp only [square, hypercubic]
  ring

/-! ## D. Regular crystals -/

section Regular

variable {d : ℕ} {F : Type*} [Fintype F] [Nonempty F]
  {g : Crystal.PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ) F)}

/-- If every site has `q` neighbors, the mean coordination is `q`. -/
lemma meanCoordination_of_card {q : ℕ} (h : ∀ x, (g.neighbors x).card = q) :
    Hypercube.meanCoordination g = q := by
  have hF : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Hypercube.meanCoordination, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The ferromagnetic ground-state energy density of a `q`-regular crystal** converges to
`-q J / 2 - |h|`. -/
lemma tendsto_groundEnergyDensity_of_card {q : ℕ} (h : ∀ x, (g.neighbors x).card = q)
    (I : IsingModel g.toSimpleGraph) (hJ : 0 ≤ I.J) :
    Filter.Tendsto (fun n : ℕ => I.groundEnergyDensity (Hypercube.region (Hypercube.cells d n)))
      Filter.atTop (nhds (-(q * I.J / 2) - |I.h|)) := by
  have := tendsto_groundEnergyDensity_hypercube I hJ
  rw [meanCoordination_of_card h] at this
  convert this using 2
  ring

/-- The diamond lattice has four neighbors per site. -/
lemma tendsto_groundEnergyDensity_diamond (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (⟨J, h⟩ : IsingModel Crystal.diamondGraph.toSimpleGraph
        ).groundEnergyDensity (Hypercube.region (Hypercube.cells 3 n)))
      Filter.atTop (nhds (-(4 * J / 2) - |h|)) := by
  have : Nonempty Crystal.DiamondLabel := ⟨.A⟩
  exact_mod_cast tendsto_groundEnergyDensity_of_card (q := 4) Crystal.diamond_neighbors_card
    ⟨J, h⟩ hJ

/-- The face-centred cubic lattice has twelve neighbors per site. -/
lemma tendsto_groundEnergyDensity_fcc (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (⟨J, h⟩ : IsingModel Crystal.fccGraph.toSimpleGraph
        ).groundEnergyDensity (Hypercube.region (Hypercube.cells 3 n)))
      Filter.atTop (nhds (-(12 * J / 2) - |h|)) := by
  exact_mod_cast tendsto_groundEnergyDensity_of_card (q := 12) Crystal.fcc_neighbors_card
    ⟨J, h⟩ hJ

/-- The body-centred cubic lattice has eight neighbors per site. -/
lemma tendsto_groundEnergyDensity_bcc (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (⟨J, h⟩ : IsingModel Crystal.bccGraph.toSimpleGraph
        ).groundEnergyDensity (Hypercube.region (Hypercube.cells 3 n)))
      Filter.atTop (nhds (-(8 * J / 2) - |h|)) := by
  exact_mod_cast tendsto_groundEnergyDensity_of_card (q := 8) Crystal.bcc_neighbors_card
    ⟨J, h⟩ hJ

/-- The hexagonal close-packed crystal has twelve neighbors per site. -/
lemma tendsto_groundEnergyDensity_hcp (J h : ℝ) (hJ : 0 ≤ J) :
    Filter.Tendsto (fun n : ℕ => (⟨J, h⟩ : IsingModel Crystal.hcpGraph.toSimpleGraph
        ).groundEnergyDensity (Hypercube.region (Hypercube.cells 3 n)))
      Filter.atTop (nhds (-(12 * J / 2) - |h|)) := by
  have : Nonempty Crystal.HcpLabel := ⟨.A⟩
  exact_mod_cast tendsto_groundEnergyDensity_of_card (q := 12) Crystal.hcp_neighbors_card
    ⟨J, h⟩ hJ

end Regular

end CondensedMatter.IsingModel
