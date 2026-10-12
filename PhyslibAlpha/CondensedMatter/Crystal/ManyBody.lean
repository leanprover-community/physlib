/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.QuasiLocal
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.GNS
public import PhyslibAlpha.ProbabilisticTheory.Representation.SectorReduction

/-!

# Symmetry reduction of a many-body dynamics on an infinite crystal

The dynamics of an infinite crystal in a symmetric state is reduced by the sectors of total
momentum, and the point symmetries relate the sectors in an orbit.

## i. Overview

Take the quasi-local algebra `𝔄` of an infinite crystal, with its action of the cell symmetries
by `*`-automorphisms, and a state `ω` invariant under a subgroup `H` of the cell symmetries that
contains the translations. The GNS construction represents `H` unitarily on the Hilbert space of
`ω`. The translations are a subgroup of `H` acting by `π`, and `H` acts by `ρ`; a symmetry `s`
carries the translation by `a` to the translation by `A a`, which is the covariance required by
the sector reduction of `SectorReduction`.

Let a group `Δ`, such as the time translations, act on `𝔄` by `*`-automorphisms preserving `ω`
and commuting with `H`: a translation invariant dynamics with the point symmetries. It acts on
the GNS space by unitaries commuting with `π` and `ρ`. Therefore each unitary of the dynamics is
reduced by the sectors of total momentum, and its restrictions to the sector of the momenta in `S`
and to the sector of the momenta in `s • S` are unitarily equivalent, with the same spectrum, for
every symmetry `s` in `H`. The statement is about arbitrary interacting many-body dynamics: it
uses nothing but the symmetry.

## ii. Key results

- `manyBodyRep` : the unitary representation of the symmetries on the GNS space.
- `manyBodyRep_covariant` : the translations and the symmetries are covariant.
- `spectrum_sectorOp_eq_manyBody` : the symmetry reduction of the spectrum of an invariant dynamics
  to the sectors of total momentum.

## iii. Table of contents

- A. The representation on the GNS space
- B. The symmetry reduction

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 2.3.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter.Crystal

open ProbabilisticTheory ProbabilisticTheory.QuasiLocal ProbabilisticTheory.QuantumMechanics
open CondensedMatter.QuasiLocal

variable {G F : Type*} [AddCommGroup G] [DecidableEq (CellSite G F)]
variable [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]
variable {Ω₀ : Type*} [Fintype Ω₀] [DecidableEq Ω₀]
variable (H : Subgroup (CellSymmetry G F))
variable (ω : AlgState (crystalAlgebra Ω₀ G F))
variable (hω : ∀ (s : H) (a : crystalAlgebra Ω₀ G F), ω (cellSymmetryAction Ω₀ s a) = ω a)

/-! ## A. The representation on the GNS space -/

/-- **The unitary representation of the symmetries on the GNS space** of an invariant state. -/
def manyBodyRep : H →* unitary (ω.GNS →L[ℂ] ω.GNS) :=
  AlgState.gnsRep (α := (cellSymmetryAction Ω₀).comp H.subtype) hω

variable (htrans : ∀ a : G, CellSymmetry.translation a ∈ H)

/-- The translations as elements of the symmetry subgroup. -/
def translationIn : Multiplicative G →* H :=
  (translationHom G F).codRestrict H fun _a => htrans _

include htrans in
/-- The translation representation on the GNS space. -/
def manyBodyTranslation : Multiplicative G →* unitary (ω.GNS →L[ℂ] ω.GNS) :=
  (manyBodyRep H ω hω).comp (translationIn H htrans)

include htrans in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
lemma manyBodyTranslation_apply (a : Multiplicative G) :
    manyBodyTranslation H ω hω htrans a = manyBodyRep H ω hω (translationIn H htrans a) := rfl

/-- The action of a symmetry on the lattice of translations, through its linear part. -/
def linearAut : H →* MulAut (Multiplicative G) where
  toFun s := AddEquiv.toMultiplicative (s : CellSymmetry G F).linear
  map_one' := rfl
  map_mul' _s _t := rfl

include htrans in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
/-- **The translations and the symmetries are covariant on the GNS space.** -/
lemma manyBodyRep_covariant :
    UnitaryRep.IsCovariantRep (linearAut H) (manyBodyTranslation H ω hω htrans)
      (manyBodyRep H ω hω) := by
  refine UnitaryRep.isCovariantRep_comp (linearAut H) (manyBodyRep H ω hω)
    (translationIn H htrans) fun s a => Subtype.ext ?_
  change (s : CellSymmetry G F) * CellSymmetry.translation (Multiplicative.toAdd a) =
    CellSymmetry.translation ((s : CellSymmetry G F).linear (Multiplicative.toAdd a)) *
      (s : CellSymmetry G F)
  rw [← CellSymmetry.mul_translation_mul_inv (s : CellSymmetry G F) (Multiplicative.toAdd a),
    mul_assoc, inv_mul_cancel, mul_one]

/-! ## B. The symmetry reduction -/

section Dynamics

variable (τ : crystalAlgebra Ω₀ G F ≃⋆ₐ[ℂ] crystalAlgebra Ω₀ G F)
  (hτ : ∀ a, ω (τ a) = ω a)
  (hcomm : ∀ s : H, τ * cellSymmetryAction Ω₀ s = cellSymmetryAction Ω₀ s * τ)

include hcomm in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
/-- A dynamics commuting with a symmetry is implemented by an operator commuting with the
unitary implementing the symmetry. -/
lemma commute_manyBodyRep (s : H) :
    Commute ((manyBodyRep H ω hω s : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS)
      (AlgState.gnsAut τ hτ) :=
  (AlgState.gnsAut_commute (hω s) hτ (hcomm s).symm)

include hcomm htrans in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
/-- A dynamics commuting with the symmetries commutes with the translation representation. -/
lemma commute_manyBodyTranslation (a : Multiplicative G) :
    Commute ((manyBodyTranslation H ω hω htrans a : unitary (ω.GNS →L[ℂ] ω.GNS)) :
      ω.GNS →L[ℂ] ω.GNS) (AlgState.gnsAut τ hτ) :=
  commute_manyBodyRep H ω hω τ hτ hcomm (translationIn H htrans a)

variable [Countable G]

include hcomm htrans in
/-- **Symmetry reduction of a many-body dynamics on an infinite crystal.** Let `ω` be a state of the
quasi-local algebra invariant under a group `H` of cell symmetries containing the translations,
and `τ` an automorphism preserving `ω` and commuting with `H`: a time evolution. Then the unitary
implementing `τ` is reduced by the sectors of total momentum, and its restriction to the sector of
the momenta in a set `S` has the same spectrum as its restriction to the sector of the momenta in
the image of `S` under any symmetry `s` in `H`. -/
lemma spectrum_sectorOp_eq_manyBody (s : H)
    {S : Set (PontryaginDual (Multiplicative G))} (hS : MeasurableSet S) :
    spectrum ℂ (UnitaryRep.sectorOp
        (commute_manyBodyTranslation H ω hω htrans τ hτ hcomm) S) =
      spectrum ℂ (UnitaryRep.sectorOp
        (commute_manyBodyTranslation H ω hω htrans τ hτ hcomm)
        (UnitaryRep.dualAct (linearAut H) s '' S)) :=
  UnitaryRep.spectrum_sectorOp_eq (manyBodyRep_covariant H ω hω htrans)
    (commute_manyBodyTranslation H ω hω htrans τ hτ hcomm)
    (commute_manyBodyRep H ω hω τ hτ hcomm) s hS

end Dynamics

end CondensedMatter.Crystal

end
