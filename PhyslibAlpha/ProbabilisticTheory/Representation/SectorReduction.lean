/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.PointCovariance

/-!

# Symmetry reduction of translation-invariant operators to momentum sectors

A bounded operator commuting with the translations and a covariant point group is reduced by the
momentum sectors, and the symmetry relates its restrictions to sectors in one orbit.

## i. Overview

Let `π` represent the translations `G` and `ρ` a covariant representation of a group `P` acting on
`G`, so that together they represent `G ⋊ P`. The *sector* of a set `S` of characters is the range
of the spectral projection `P(S)` of `π`: the vectors whose total momentum lies in `S`. A bounded
operator `T` commuting with all `π(g)` commutes with every `P(S)`, and so restricts to each
sector. If `T` also commutes with `ρ`, then `ρ(p)` restricts to a unitary equivalence of the
sector of `S` and the sector of `p • S` which intertwines the restrictions of `T`. In particular
the spectrum of `T` on the sector of `S` is the spectrum of `T` on the sector of `p • S`.

For a single momentum, this says that the fibre Hamiltonians at momenta related by the point group
are unitarily equivalent, so the spectrum is determined by the momenta in an irreducible zone. The
statement makes no assumption on the nature of `T`: it applies to one particle, to many particles,
to spins, to anything with a unitary representation of the symmetry group. For a self-adjoint
generator `H` of an unbounded dynamics, `T` is the unitary group `e^{itH}`.

## ii. Key results

- `UnitaryRep.sector` : the range of a spectral projection.
- `UnitaryRep.sectorEquiv` : the isometric equivalence of the sectors of `S` and `p • S`.
- `UnitaryRep.spectrum_sectorOp_eq` : the spectra of an invariant operator on the two sectors
  agree.

## iii. Table of contents

- A. Sectors
- B. The equivalence of sectors
- C. Invariant operators

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {P : Type*} [Group P] {φ : P →* MulAut (Multiplicative G)}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {π : Multiplicative G →* unitary (H →L[ℂ] H)} {ρ : P →* unitary (H →L[ℂ] H)}
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))] [Countable G]

/-! ## A. Sectors -/

variable (π) in
/-- The sector of a set of characters: the vectors of total momentum in the set, the range of the
spectral projection. -/
def sector (S : Set (PontryaginDual (Multiplicative G))) : Submodule ℂ H :=
  LinearMap.range (projection π S).toLinearMap

omit [Countable G] in
lemma mem_sector_iff (S : Set (PontryaginDual (Multiplicative G))) (x : H) :
    x ∈ sector π S ↔ ∃ y, projection π S y = x := Iff.rfl

/-! ## B. The equivalence of sectors -/

omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [Countable G] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma dualAct_image_image (p : P) (S : Set (PontryaginDual (Multiplicative G))) :
    dualAct φ p⁻¹ '' (dualAct φ p '' S) = S := by
  rw [Set.image_image]
  have : ∀ ψ, dualAct φ p⁻¹ (dualAct φ p ψ) = ψ := fun ψ => by
    rw [← dualAct_mul, inv_mul_cancel, dualAct_one]
  simp [this]

omit [Countable G] in
lemma measurableSet_dualAct_image (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) : MeasurableSet (dualAct φ p '' S) := by
  have hl : Function.LeftInverse (dualAct φ p⁻¹) (dualAct φ p) := fun ψ => by
    rw [← dualAct_mul, inv_mul_cancel, dualAct_one]
  have hr : Function.RightInverse (dualAct φ p⁻¹) (dualAct φ p) := fun ψ => by
    rw [← dualAct_mul, mul_inv_cancel, dualAct_one]
  have : dualAct φ p '' S = dualAct φ p⁻¹ ⁻¹' S := congrFun
    (Set.image_eq_preimage_of_inverse hl hr) S
  rw [this]
  exact measurable_dualAct φ p⁻¹ hS

section Equiv

local notation "𝓡" p => (((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H))

lemma rho_inv_rho (p : P) (x : H) : (𝓡 p⁻¹) ((𝓡 p) x) = x := by
  have h : ρ p⁻¹ * ρ p = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h2 := congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H) x) h
  exact h2

lemma rho_rho_inv (p : P) (x : H) : (𝓡 p) ((𝓡 p⁻¹) x) = x := by
  simpa using rho_inv_rho (ρ := ρ) p⁻¹ x

lemma norm_rho (p : P) (x : H) : ‖(𝓡 p) x‖ = ‖x‖ := by
  have h1 : ‖(𝓡 p) x‖ ^ 2 = ‖x‖ ^ 2 := by
    have : ⟪(𝓡 p) x, (𝓡 p) x⟫_ℂ = ⟪x, x⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      have h2 : ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H).adjoint ((𝓡 p) x) = x := by
        have := rho_inv_rho (ρ := ρ) p x
        have h3 : ((ρ p⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
            ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H).adjoint := by
          rw [map_inv]; exact ContinuousLinearMap.star_eq_adjoint _
        rwa [h3] at this
      rw [h2]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
    exact_mod_cast this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

variable (hcov : IsCovariantRep φ π ρ)

include hcov in
lemma rho_projection_apply (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) (y : H) :
    (𝓡 p) (projection π S y) = projection π (dualAct φ p '' S) ((𝓡 p) y) :=
  congrArg (fun T : H →L[ℂ] H => T y) (rho_mul_projection hcov p hS)

include hcov in
lemma rho_mem_sector (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) {x : H} (hx : x ∈ sector π S) :
    (𝓡 p) x ∈ sector π (dualAct φ p '' S) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(𝓡 p) y, (rho_projection_apply hcov p hS y).symm⟩

include hcov in
lemma rho_inv_mem_sector (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) {y : H} (hy : y ∈ sector π (dualAct φ p '' S)) :
    (𝓡 p⁻¹) y ∈ sector π S := by
  obtain ⟨z, rfl⟩ := hy
  have := rho_projection_apply hcov p⁻¹ (measurableSet_dualAct_image (φ := φ) p hS) z
  rw [dualAct_image_image] at this
  exact ⟨(𝓡 p⁻¹) z, this.symm⟩

/-- **The equivalence of sectors**: `ρ(p)` is an isometric equivalence of the sector of `S` onto
the sector of `p • S`. -/
def sectorEquiv (p : P) {S : Set (PontryaginDual (Multiplicative G))} (hS : MeasurableSet S) :
    sector π S ≃ₗᵢ[ℂ] sector π (dualAct φ p '' S) where
  toFun x := ⟨(𝓡 p) x.1, rho_mem_sector hcov p hS x.2⟩
  invFun y := ⟨(𝓡 p⁻¹) y.1, rho_inv_mem_sector hcov p hS y.2⟩
  map_add' _x _y := Subtype.ext (map_add _ _ _)
  map_smul' _c _x := Subtype.ext (map_smul _ _ _)
  left_inv x := Subtype.ext (rho_inv_rho p x.1)
  right_inv y := Subtype.ext (rho_rho_inv p y.1)
  norm_map' x := norm_rho p x.1

lemma coe_sectorEquiv (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) (x : sector π S) :
    ((sectorEquiv hcov p hS x : sector π (dualAct φ p '' S)) : H) = (𝓡 p) x.1 := rfl

end Equiv

/-! ## C. Invariant operators -/

section Invariant

variable {T : H →L[ℂ] H}

/-- An operator commuting with the translations restricts to each sector. -/
def sectorOp (hT : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)
    (S : Set (PontryaginDual (Multiplicative G))) : Module.End ℂ (sector π S) :=
  LinearMap.restrict T.toLinearMap (fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨T y, by
      have := congrArg (fun A : H →L[ℂ] H => A y) (projection_commute π hT S).eq
      exact this⟩)

omit [Countable G] in
lemma coe_sectorOp (hT : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)
    (S : Set (PontryaginDual (Multiplicative G))) (x : sector π S) :
    ((sectorOp hT S x : sector π S) : H) = T x.1 := rfl

variable (hcov : IsCovariantRep φ π ρ)
  (hTπ : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)
  (hTρ : ∀ p, Commute ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)

include hcov hTρ in
/-- **The equivalence of sectors intertwines the restrictions of an invariant operator.** -/
lemma sectorEquiv_sectorOp (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) (x : sector π S) :
    sectorEquiv hcov p hS (sectorOp hTπ S x) = sectorOp hTπ (dualAct φ p '' S)
      (sectorEquiv hcov p hS x) :=
  Subtype.ext (by
    have := congrArg (fun A : H →L[ℂ] H => A x.1) (hTρ p).eq
    exact this)

include hcov hTρ in
/-- **Symmetry reduction.** The spectrum of an operator invariant under the translations and the
covariant point group, restricted to the sector of the characters in `S`, is its spectrum on the
sector of the characters in `p • S`. -/
lemma spectrum_sectorOp_eq (p : P) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) :
    spectrum ℂ (sectorOp hTπ S) = spectrum ℂ (sectorOp hTπ (dualAct φ p '' S)) := by
  let e := (sectorEquiv hcov p hS).toLinearEquiv
  let c : Module.End ℂ (sector π S) ≃ₐ[ℂ] Module.End ℂ (sector π (dualAct φ p '' S)) :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.conj e) (LinearEquiv.conj_id e) (fun f g =>
      LinearEquiv.conj_comp e g f)
  have hc : c (sectorOp hTπ S) = sectorOp hTπ (dualAct φ p '' S) := by
    refine LinearMap.ext fun y => ?_
    change e (sectorOp hTπ S (e.symm y)) = _
    have := sectorEquiv_sectorOp hcov hTπ hTρ p hS (e.symm y)
    simpa [e] using this
  rw [← hc, AlgEquiv.spectrum_eq]

end Invariant

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
