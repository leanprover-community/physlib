/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Graph
public import Mathlib.Topology.Algebra.Ring.Real

/-!

# Classical Ising interactions on a graph

## i. Overview

A classical Ising configuration assigns an up or down spin to every vertex of a graph.
Edges specify which spins interact. `IsingModel` adds a uniform exchange coupling `J`
and longitudinal field `h`, both in a fixed energy unit, to this connectivity.

The energy of a finite region is
`-J ∑ {x,y} σ(x) σ(y) - h ∑ x σ(x)`, where the first sum runs over its internal graph edges
and each spin has value ±1. We implement the edge sum as half the sum over ordered adjacent pairs:
symmetry counts each undirected edge twice and the simple graph excludes self-interactions.
Positive `J` favors alignment (ferromagnetism), negative `J` favors opposite spins,
and positive `h` favors up spins.

Joining disjoint regions changes their combined energy only through bonds connecting the
regions. Each crossing bond contributes at most `|J|` in absolute value. If sites have at
most `q` neighbors, the absolute energy is bounded by `(|J| q / 2 + |h|) |Λ|`. These bounds
control boundary corrections and energy growth with volume.

For ferromagnetic exchange `J ≥ 0`, uniform polarization aligned with the field attains
the least energy on every finite region. Its energy per site converges whenever the
average internal coordination converges. These results apply to arbitrary graphs;
crystal translations supply an additional symmetry.

## ii. Key results

- `IsingModel` : the nearest-neighbour Ising model on a graph, with uniform coupling and field.
- `IsingModel.energy` : the energy of a finite region.
- `IsingModel.abs_energy_union_sub_le` : the failure of additivity is bounded by the crossing bonds.
- `IsingModel.abs_energy_le_of_degree_le` : the energy grows at most linearly with the volume.
- `IsingModel.groundEnergy_eq` : the ferromagnetic ground-state energy of a region.
- `IsingModel.tendsto_groundEnergyDensity` : the ground-state energy density converges when the
  average internal coordination does.
- `IsingModel.energy_translate` : the energy is invariant under crystal translations.

## iii. Table of contents

- A. Spin configurations
- B. Finite-region energy and locality
- C. Boundary interactions
- D. Energy growth with volume
- E. Ferromagnetic ground states
- F. Ground-state energy per site
- G. Crystal translation symmetry

## iv. References

* E. Ising, Beitrag zur Theorie des Ferromagnetismus.

-/

@[expose] public section

namespace CondensedMatter

/-- A classical nearest-neighbor Ising model on the specified undirected graph. -/
structure IsingModel {X : Type*} (graph : SimpleGraph X) where
  /-- Uniform exchange coupling; positive values favor aligned spins. -/
  J : ℝ
  /-- Uniform longitudinal field; positive values favor up spins. -/
  h : ℝ

namespace IsingModel

/-! ## A. Spin configurations -/

open scoped Classical

variable {X : Type*} {g : SimpleGraph X}

/-- Up or down spins at every site of the crystal. -/
abbrev Configuration (_I : IsingModel g) := X → Bool

/-- The dimensionless spin value, with `true` denoting up. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Every Ising spin has unit magnitude. -/
@[simp] lemma abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> norm_num [spin]

/-! ## B. Finite-region energy and locality -/

/-- The exchange contribution of an ordered pair; nonadjacent sites contribute zero. -/
noncomputable def pairSpin (I : IsingModel g) (σ : I.Configuration) (x y : X) : ℝ :=
  if g.Adj x y then spin (σ x) * spin (σ y) else 0

/-- Energy of the spins and internal edges of a finite region. The factor `1/2` counts each
undirected graph edge once. Spins outside the region do not contribute. -/
noncomputable def energy (I : IsingModel g) (Λ : Finset X)
    (σ : I.Configuration) : ℝ :=
  -(I.J / 2) * (∑ x ∈ Λ, ∑ y ∈ Λ, I.pairSpin σ x y) - I.h * ∑ x ∈ Λ, spin (σ x)

/-- A region's energy depends only on the spin configuration inside that region. -/
lemma energy_congr (I : IsingModel g) (Λ : Finset X) {σ τ : I.Configuration}
    (hστ : ∀ x ∈ Λ, σ x = τ x) : I.energy Λ σ = I.energy Λ τ := by
  unfold energy
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp [pairSpin, hστ x hx, hστ y hy]
  · congr 1
    exact Finset.sum_congr rfl fun x hx => congrArg spin (hστ x hx)

/-! ## C. Boundary interactions

Combining disjoint regions adds precisely the exchange interactions across their common
boundary. The number of crossing bonds bounds this correction independently of the spin
configuration.
-/

/-- The exchange contribution is symmetric in the endpoints of a bond. -/
lemma pairSpin_comm (I : IsingModel g) (σ : I.Configuration) (x y : X) :
    I.pairSpin σ x y = I.pairSpin σ y x := by
  simp only [pairSpin, g.adj_comm x y, mul_comm]

/-- Joining disjoint regions adds exactly their crossing exchange interactions. -/
lemma energy_union [DecidableEq X] (I : IsingModel g) (Λ M : Finset X)
    (hΛM : Disjoint Λ M) (σ : I.Configuration) :
    I.energy (Λ ∪ M) σ = I.energy Λ σ + I.energy M σ -
      I.J * ∑ x ∈ Λ, ∑ y ∈ M, I.pairSpin σ x y := by
  have hc : (∑ x ∈ M, ∑ y ∈ Λ, I.pairSpin σ x y) =
      ∑ x ∈ Λ, ∑ y ∈ M, I.pairSpin σ x y := by
    rw [Finset.sum_comm]
    simp only [I.pairSpin_comm σ]
  simp only [energy, Finset.sum_union hΛM, Finset.sum_add_distrib, hc]
  ring

/-- An ordered bond contributes at most one in absolute spin units. -/
lemma abs_pairSpin (I : IsingModel g) (σ : I.Configuration) (x y : X) :
    |I.pairSpin σ x y| = if g.Adj x y then 1 else 0 := by
  unfold pairSpin
  split <;> simp_all [abs_mul]

/-- The total exchange spin sum is bounded by the number of connections between the regions. -/
lemma abs_sum_pairSpin_le (I : IsingModel g) (Λ M : Finset X)
    (σ : I.Configuration) :
    |∑ x ∈ Λ, ∑ y ∈ M, I.pairSpin σ x y| ≤ g.bondCountBetween Λ M := by
  calc
    _ ≤ ∑ x ∈ Λ, ∑ y ∈ M, |I.pairSpin σ x y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ = g.bondCountBetween Λ M := by
      simp only [abs_pairSpin, SimpleGraph.bondCountBetween, Finset.card_filter,
        ← Nat.coe_castAddMonoidHom, map_sum, apply_ite]
      simp only [Nat.coe_castAddMonoidHom, Nat.cast_one, Nat.cast_zero]

/-- Failure of energy additivity is controlled solely by the bonds crossing the boundary. -/
lemma abs_energy_union_sub_le [DecidableEq X] (I : IsingModel g)
    (Λ M : Finset X) (hΛM : Disjoint Λ M) (σ : I.Configuration) :
    |I.energy (Λ ∪ M) σ - I.energy Λ σ - I.energy M σ| ≤
      |I.J| * g.bondCountBetween Λ M := by
  rw [I.energy_union Λ M hΛM σ]
  have he : I.energy Λ σ + I.energy M σ -
      I.J * (∑ x ∈ Λ, ∑ y ∈ M, I.pairSpin σ x y) - I.energy Λ σ - I.energy M σ =
      -(I.J * ∑ x ∈ Λ, ∑ y ∈ M, I.pairSpin σ x y) := by ring
  rw [he, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left (I.abs_sum_pairSpin_le Λ M σ) (abs_nonneg _)

/-! ## D. Energy growth with volume

A bounded coordination number ensures that the energy of every spin configuration grows
at most linearly with the number of sites. The bound holds for either sign of exchange
coupling and field.
-/

/-- The absolute energy is bounded by the internal bond count and the number of spins. -/
lemma abs_energy_le (I : IsingModel g) (Λ : Finset X) (σ : I.Configuration) :
    |I.energy Λ σ| ≤ |I.J| / 2 * g.bondCountBetween Λ Λ + |I.h| * Λ.card := by
  have hs : |∑ x ∈ Λ, spin (σ x)| ≤ (Λ.card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ Λ, |spin (σ x)| := Finset.abs_sum_le_sum_abs _ _
      _ = Λ.card := by simp
  calc
    _ ≤ |-(I.J / 2) * (∑ x ∈ Λ, ∑ y ∈ Λ, I.pairSpin σ x y)| +
        |I.h * ∑ x ∈ Λ, spin (σ x)| := by
      unfold energy
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (-(I.J / 2) * (∑ x ∈ Λ, ∑ y ∈ Λ, I.pairSpin σ x y))
        (-(I.h * ∑ x ∈ Λ, spin (σ x)))
    _ ≤ |I.J| / 2 * g.bondCountBetween Λ Λ + |I.h| * Λ.card := by
      simp only [abs_mul, abs_neg, abs_div, abs_two]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (I.abs_sum_pairSpin_le Λ Λ σ)
          (div_nonneg (abs_nonneg I.J) (by norm_num : (0 : ℝ) ≤ 2)))
        (mul_le_mul_of_nonneg_left hs (abs_nonneg _))

/-- A coordination bound gives a uniform energy bound proportional to the region's volume. -/
lemma abs_energy_le_of_degree_le [g.LocallyFinite] (I : IsingModel g) (Λ : Finset X)
    (σ : I.Configuration) (q : ℕ) (hq : ∀ x ∈ Λ, (g.neighborFinset x).card ≤ q) :
    |I.energy Λ σ| ≤ (|I.J| * q / 2 + |I.h|) * Λ.card := by
  have hc : (g.bondCountBetween Λ Λ : ℝ) ≤ q * Λ.card := by
    exact_mod_cast g.bondCountBetween_le Λ Λ q hq
  calc
    _ ≤ |I.J| / 2 * g.bondCountBetween Λ Λ + |I.h| * Λ.card := I.abs_energy_le Λ σ
    _ ≤ |I.J| / 2 * (q * Λ.card) + |I.h| * Λ.card :=
      add_le_add (mul_le_mul_of_nonneg_left hc
        (div_nonneg (abs_nonneg I.J) (by norm_num : (0 : ℝ) ≤ 2))) le_rfl
    _ = _ := by ring

/-! ## E. Ferromagnetic ground states

For nonnegative exchange coupling, uniform polarization simultaneously minimizes every
bond interaction. Alignment with the field also minimizes every one-site contribution.
The minimum energy therefore depends only on the internal connections and the volume.
-/

/-- A configuration minimizing the energy of the finite region `Λ`.
Only interactions internal to the region enter this definition. -/
def IsGroundState (I : IsingModel g) (Λ : Finset X) (σ : I.Configuration) : Prop :=
  ∀ τ, I.energy Λ σ ≤ I.energy Λ τ

/-- Uniform spins aligned with the field; at zero field the up orientation is chosen. -/
noncomputable def polarized (I : IsingModel g) : I.Configuration :=
  fun _ => decide (0 ≤ I.h)

/-- The least finite-region energy over all spin configurations. -/
noncomputable def groundEnergy (I : IsingModel g) (Λ : Finset X) : ℝ :=
  sInf (Set.range (I.energy Λ))

/-- An energy-minimizing configuration attains the least energy. -/
lemma groundEnergy_eq_of_isGroundState (I : IsingModel g) (Λ : Finset X)
    {σ : I.Configuration} (hσ : I.IsGroundState Λ σ) :
    I.groundEnergy Λ = I.energy Λ σ := by
  exact (show IsLeast (Set.range (I.energy Λ)) (I.energy Λ σ) from
    ⟨⟨σ, rfl⟩, by rintro _ ⟨τ, rfl⟩; exact hσ τ⟩).csInf_eq

/-- Uniform field-aligned polarization has saturated exchange and field contributions. -/
lemma energy_polarized (I : IsingModel g) (Λ : Finset X) :
    I.energy Λ I.polarized =
      -(I.J / 2) * g.bondCountBetween Λ Λ - |I.h| * Λ.card := by
  have hp : ∀ x y, I.pairSpin I.polarized x y = if g.Adj x y then 1 else 0 := by
    intro x y
    unfold pairSpin polarized
    split <;> cases hc : decide (0 ≤ I.h) <;> norm_num [spin]
  have hc : (∑ x ∈ Λ, ∑ y ∈ Λ, if g.Adj x y then (1 : ℝ) else 0) =
      g.bondCountBetween Λ Λ := by
    simp only [SimpleGraph.bondCountBetween, Finset.card_filter,
      ← Nat.coe_castAddMonoidHom, map_sum, apply_ite]
    simp only [Nat.coe_castAddMonoidHom, Nat.cast_one, Nat.cast_zero]
  unfold energy
  simp only [hp, hc]
  by_cases hh : 0 ≤ I.h
  · simp [polarized, hh, spin, abs_of_nonneg hh]
  · simp [polarized, hh, spin, abs_of_neg (lt_of_not_ge hh)]

/-- Ferromagnetic energies cannot lie below the saturated exchange and field contributions. -/
lemma energy_lower_bound (I : IsingModel g) (hJ : 0 ≤ I.J) (Λ : Finset X)
    (σ : I.Configuration) :
    -(I.J / 2) * g.bondCountBetween Λ Λ - |I.h| * Λ.card ≤ I.energy Λ σ := by
  have hb := neg_abs_le (I.energy Λ σ)
  have he := neg_le_neg (I.abs_energy_le Λ σ)
  rw [abs_of_nonneg hJ] at he
  linarith

/-- Uniform field-aligned polarization is a ground state on every finite ferromagnetic region. -/
lemma isGroundState_polarized (I : IsingModel g) (hJ : 0 ≤ I.J) (Λ : Finset X) :
    I.IsGroundState Λ I.polarized := by
  intro σ
  rw [I.energy_polarized]
  exact I.energy_lower_bound hJ Λ σ

/-- The exact ferromagnetic minimum counts internal bonds and field-aligned spins. -/
lemma groundEnergy_eq (I : IsingModel g) (hJ : 0 ≤ I.J) (Λ : Finset X) :
    I.groundEnergy Λ = -(I.J / 2) * g.bondCountBetween Λ Λ - |I.h| * Λ.card := by
  rw [I.groundEnergy_eq_of_isGroundState Λ (I.isGroundState_polarized hJ Λ), I.energy_polarized]

/-! ## F. Ground-state energy per site

The average internal coordination counts neighbors that remain in the region, averaged
over its sites. If this average converges along nonempty regions, the ferromagnetic
minimum energy per site converges with it. No regular degree, periodicity or prescribed
shape of region is required.
-/

/-- The minimum finite-region energy divided by the number of sites. -/
noncomputable def groundEnergyDensity (I : IsingModel g) (Λ : Finset X) : ℝ :=
  I.groundEnergy Λ / Λ.card

/-- The ferromagnetic minimum per site is determined by average internal coordination. -/
lemma groundEnergyDensity_eq (I : IsingModel g) (hJ : 0 ≤ I.J) (Λ : Finset X)
    (hΛ : Λ.Nonempty) :
    I.groundEnergyDensity Λ =
      -(I.J / 2) * ((g.bondCountBetween Λ Λ : ℝ) / Λ.card) - |I.h| := by
  have hn : (Λ.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hΛ
  rw [groundEnergyDensity, I.groundEnergy_eq hJ]
  field_simp

/-- Convergent average internal coordination gives a ferromagnetic ground-state energy density.
The statement applies to any sequence of nonempty finite regions on any graph. -/
lemma tendsto_groundEnergyDensity (I : IsingModel g) (hJ : 0 ≤ I.J)
    (Λ : ℕ → Finset X) (hΛ : ∀ n, (Λ n).Nonempty) (z : ℝ)
    (hz : Filter.Tendsto
      (fun n => (g.bondCountBetween (Λ n) (Λ n) : ℝ) / (Λ n).card)
      Filter.atTop (nhds z)) :
    Filter.Tendsto (fun n => I.groundEnergyDensity (Λ n))
      Filter.atTop (nhds (-(I.J / 2) * z - |I.h|)) := by
  simp_rw [I.groundEnergyDensity_eq hJ _ (hΛ _)]
  exact (hz.const_mul (-(I.J / 2))).sub tendsto_const_nhds

/-! ## G. Crystal translation symmetry -/

section CrystalTranslations

variable {G : Type*} [AddGroup G] {C : Crystal G} {g : Crystal.PeriodicGraph C}

/-- Transport a configuration along a crystal translation. -/
def translate (I : IsingModel g.toSimpleGraph) (a : G) (σ : I.Configuration) : I.Configuration :=
  fun x => σ (-a +ᵥ x)

/-- A transported spin has the same value at the transported site. -/
@[simp] lemma translate_apply (I : IsingModel g.toSimpleGraph) (a : G)
    (σ : I.Configuration) (x : C.Site) : I.translate a σ (a +ᵥ x) = σ x := by
  simp [translate, ← add_vadd]

/-- Translate a finite region by the existing bijective action on crystal sites. -/
def translateRegion (a : G) (Λ : Finset C.Site) : Finset C.Site :=
  Λ.map (AddAction.toPerm a).toEmbedding

/-- Exchange contributions are unchanged by translating both spins and sites. -/
lemma pairSpin_translate (I : IsingModel g.toSimpleGraph) (a : G) (σ : I.Configuration)
    (x y : C.Site) :
    I.pairSpin (I.translate a σ) (a +ᵥ x) (a +ᵥ y) = I.pairSpin σ x y := by
  unfold pairSpin
  rw [g.adj_vadd a x y, I.translate_apply, I.translate_apply]

/-- Uniform Ising interactions inherit the crystal's translation symmetry. Translating the
region as well as its configuration preserves its energy. -/
lemma energy_translate (I : IsingModel g.toSimpleGraph) (a : G)
    (Λ : Finset C.Site) (σ : I.Configuration) :
    I.energy (translateRegion a Λ) (I.translate a σ) = I.energy Λ σ := by
  simp [energy, translateRegion, Finset.sum_map, pairSpin_translate,
    show ∀ x : C.Site, (AddAction.toPerm a) x = (a +ᵥ x) from fun _ => rfl]

end CrystalTranslations

end IsingModel
end CondensedMatter
