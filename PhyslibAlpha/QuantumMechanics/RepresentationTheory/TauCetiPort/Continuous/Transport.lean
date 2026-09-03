/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.MatrixCoefficient
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Irreducible

/-!
# Transporting a continuous representation along a continuous linear equivalence

A continuous linear equivalence `e : V ≃L[𝕜] W` carries a continuous representation on `V` to one
on `W` by conjugating every action operator, `π g ↦ e ∘ π g ∘ e⁻¹`, that is, by applying Mathlib's
continuous algebra equivalence `ContinuousLinearEquiv.conjContinuousAlgEquiv`. This file builds
that transport and records what it preserves: continuity of the operator-valued action, and — for
an equivalence that is moreover isometric, so that inner products are available — unitarity and,
the point of the construction, the matrix coefficients, which are unchanged once the defining
vectors are moved along `e`.

The transport is what lets a statement about representations on the standard models
`EuclideanSpace 𝕜 (Fin n)` be applied to a representation on an arbitrary finite-dimensional
inner product space: `stdOrthonormalBasis` supplies the isometry `(stdOrthonormalBasis 𝕜 V).repr`,
so nothing is lost by pinning a model.

## Main definitions

* `TauCeti.ContRepresentation.congr`: the transported representation `e ∘ π · ∘ e⁻¹`.
* `ContRepresentation.congrEquiv`: the equivalence of continuous representations `π ≃ congr e π`
  witnessed by `e` itself, which is what carries a statement about the transport back to `π`.

## Main statements

* `TauCeti.ContRepresentation.continuous_congr`,
  `TauCeti.ContRepresentation.isIrreducible_congr` and
  `TauCeti.ContRepresentation.IsUnitary.congr`: the transport preserves continuity,
  irreducibility, and unitarity.
* `TauCeti.ContRepresentation.congr_refl` and `TauCeti.ContRepresentation.congr_congr`: the
  transport is functorial, so "transportable onto" is an equivalence relation on representations
  (symmetry is `simp` from these two).
* `TauCeti.ContRepresentation.matrixCoeff_congr`: the matrix coefficients of the transport at the
  transported vectors are those of the original representation.
* `TauCeti.ContRepresentation.matrixCoeff_congr_adjoint`: the same for an equivalence that is not
  isometric, where the second vector moves along the adjoint of `e⁻¹` instead of along `e`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Congr

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Transport along a continuous linear equivalence.** The representation on `W` obtained from a
representation on `V` by conjugating each action operator with `e : V ≃L[𝕜] W`. -/
noncomputable def congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ContRepresentation 𝕜 G W :=
  .ofMonoidHom
    { toFun g := e.conjContinuousAlgEquiv (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, map_mul] }

omit [TopologicalSpace G] in
/-- The action operators of a transported representation. -/
theorem congr_apply (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) (g : G) (x : W) :
    congr e π g x = e (π g (e.symm x)) :=
  (rfl)

omit [TopologicalSpace G] in
/-- The operator-valued function underlying a transported representation. -/
@[simp]
theorem coe_congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ⇑(congr e π) = fun g ↦ e.conjContinuousAlgEquiv (π g) := by
  funext g
  apply ContinuousLinearMap.ext
  intro x
  exact congr_apply e π g x

/-- Transport preserves continuity of the operator-valued action: conjugation by `e` is the
continuous algebra equivalence `ContinuousLinearEquiv.conjContinuousAlgEquiv`. -/
theorem continuous_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V} (hπ : Continuous π) :
    Continuous (congr e π) :=
  (map_continuous e.conjContinuousAlgEquiv).comp hπ

omit [TopologicalSpace G] in
/-- Transport preserves irreducibility: `e` is an equivariant linear equivalence from `π` to its
transport, and irreducibility is invariant under such an equivalence. -/
theorem isIrreducible_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : π.toRepresentation.IsIrreducible) : (congr e π).toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv (e : V ≃ₗ[𝕜] W)
    (fun g v ↦ by simp [_root_.ContRepresentation.toMonoidHom_apply]) hπ

omit [TopologicalSpace G] in
/-- Transport along the identity changes nothing. -/
@[simp]
theorem congr_refl (π : ContRepresentation 𝕜 G V) :
    congr (ContinuousLinearEquiv.refl 𝕜 V) π = π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

omit [TopologicalSpace G] in
/-- Transporting twice is transporting along the composite. -/
@[simp]
theorem congr_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : V ≃L[𝕜] W)
    (f : W ≃L[𝕜] X) (π : ContRepresentation 𝕜 G V) :
    congr f (congr e π) = congr (e.trans f) π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

end Congr

section CongrIsometry

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

omit [TopologicalSpace G] in
/-- Transport along a linear isometry equivalence preserves unitarity: `e` and `e⁻¹` preserve the
inner product, so the conjugated operators do exactly when the original ones do. -/
theorem IsUnitary.congr {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π) (e : V ≃ₗᵢ[𝕜] W) :
    IsUnitary (ContRepresentation.congr e.toContinuousLinearEquiv π) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by simp [hπ.norm_map]

/-- **Transport along a linear isometry equivalence does not change matrix coefficients.** The
matrix coefficient of the transported representation at the transported vectors is the matrix
coefficient of the original. -/
@[simp]
theorem matrixCoeff_congr (e : V ≃ₗᵢ[𝕜] W) {π : ContRepresentation 𝕜 G V} (hπ : Continuous π)
    (v w : V) :
    matrixCoeff (congr e.toContinuousLinearEquiv π) (continuous_congr _ hπ) (e v) (e w) =
      matrixCoeff π hπ v w := by
  ext g
  simp

end CongrIsometry

section CongrAdjoint

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- **Transport along an arbitrary continuous linear equivalence moves matrix coefficients along
`e` and along the adjoint of `e⁻¹`.** For an `e` that is not isometric the second vector has to be
moved by `(e⁻¹)†` rather than by `e`, since it is paired with the transported vector rather than
transported itself.

This is `TauCeti.ContRepresentation.matrixCoeff_congr` with the isometry hypothesis dropped: for a
linear isometry equivalence `(e⁻¹)† = e`, and the two statements agree. It is what says that being
a matrix coefficient depends only on the *equivalence class* of a representation, so a
representation may be replaced by any conjugate of it — for instance by a unitary one. -/
@[simp]
theorem matrixCoeff_congr_adjoint (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous π) (v w : V) :
    matrixCoeff (congr e π) (continuous_congr e hπ) (e v)
        (ContinuousLinearMap.adjoint (e.symm : W →L[𝕜] V) w) = matrixCoeff π hπ v w := by
  ext g
  rw [matrixCoeff_apply, matrixCoeff_apply, congr_apply, ContinuousLinearMap.adjoint_inner_right]
  simp

end CongrAdjoint

end ContRepresentation

end TauCeti

namespace ContRepresentation

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The transport of a representation is equivalent to it**, along `e` itself: `e` intertwines
`π` with `TauCeti.ContRepresentation.congr e π` by the very definition of the transported action.

This is the bundled form of that observation, and it is what carries a statement about the
transport back to `π`: an `Equiv` is an isomorphism in the category of continuous representations,
so `π` and `congr e π` have the same subrepresentation lattice, the same irreducible constituents
and the same character. It lives in the root `ContRepresentation` namespace, rather than beside
`congr` in `TauCeti.ContRepresentation`, so that the dot notation `π.congrEquiv e` elaborates;
`congrEquiv_apply` and `congrEquiv_symm_apply` evaluate it and its inverse as `e` and `e.symm`. -/
noncomputable def congrEquiv (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) :
    π.Equiv (TauCeti.ContRepresentation.congr e π) :=
  .mk e fun g ↦ ContinuousLinearMap.ext fun v ↦ by simp

@[simp]
theorem congrEquiv_toContinuousLinearEquiv (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) :
    (π.congrEquiv e).toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem congrEquiv_apply (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) (v : V) :
    π.congrEquiv e v = e v :=
  (rfl)

@[simp]
theorem congrEquiv_symm_apply (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) (w : W) :
    (π.congrEquiv e).symm w = e.symm w :=
  (rfl)

end ContRepresentation
