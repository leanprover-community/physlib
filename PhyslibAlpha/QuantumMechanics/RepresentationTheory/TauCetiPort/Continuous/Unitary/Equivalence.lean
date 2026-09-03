/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Schur
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Transport

/-!
# Equivalent irreducible unitary representations are unitarily equivalent

An equivalence of continuous representations is a linear equivalence intertwining the actions; it
need not respect the inner products. For irreducible *unitary* representations it can always be
rescaled to one that does, so the two notions of equivalence coincide and nothing is lost by
asking for equivalences that are isometries -- which is what the matrix coefficients need, since
they are only invariant under isometric transport
(`TauCeti.ContRepresentation.matrixCoeff_congr`).

The argument is Schur's lemma applied to `T† ∘ T`. If `T` intertwines `π` with `ρ` then, both
representations being unitary, the adjoint `T†` intertwines `ρ` with `π`; hence `T† ∘ T` is a
self-intertwiner of the irreducible `π`, so over an algebraically closed field it is a scalar `c`.
Pairing with a vector shows `c` is a positive real, `‖T v‖ = √c ‖v‖`, and `T / √c` is the isometry
wanted.

## Main statements

* `TauCeti.ContRepresentation.exists_linearIsometryEquiv_congr_eq`: an equivalence between
  finite-dimensional irreducible unitary continuous representations can be replaced by a linear
  isometry equivalence transporting one onto the other.

The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

variable {𝕜 G V W : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceUnitaryEquivalenceDomain : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

local instance instCompleteSpaceUnitaryEquivalenceCodomain : CompleteSpace W :=
  FiniteDimensional.complete 𝕜 W

/-- **Equivalent irreducible unitary representations are unitarily equivalent.** An equivalence
`φ` of continuous representations is only a linear equivalence; rescaling it by the square root of
the scalar Schur's lemma extracts from `φ† ∘ φ` makes it an isometry, which then transports `π`
onto `ρ` in the sense of `TauCeti.ContRepresentation.congr`. -/
theorem exists_linearIsometryEquiv_congr_eq {π : ContRepresentation 𝕜 G V}
    {ρ : ContRepresentation 𝕜 G W} (hπu : IsUnitary π) (hρu : IsUnitary ρ)
    (hirr : π.toRepresentation.IsIrreducible) (φ : _root_.ContRepresentation.Equiv π ρ) :
    ∃ e : V ≃ₗᵢ[𝕜] W, congr e.toContinuousLinearEquiv π = ρ := by
  set T : V →L[𝕜] W := φ.toContinuousLinearEquiv.toContinuousLinearMap
  have hT : ∀ g : G, T ∘L π g = ρ g ∘L T := fun g ↦ φ.isIntertwining g
  have hTapp : ∀ (g : G) (v : V), T (π g v) = ρ g (T v) := fun g v ↦ by
    simpa using congrArg (fun f : V →L[𝕜] W ↦ f v) (hT g)
  -- the adjoint intertwines the other way, so `T† ∘ T` is a self-intertwiner of `π`
  have hadj : ∀ g : G, (ContinuousLinearMap.adjoint T) ∘L ρ g
      = π g ∘L ContinuousLinearMap.adjoint T := by
    intro g
    have h := congrArg ContinuousLinearMap.adjoint (hT g⁻¹)
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hπu.adjoint_eq_inv, hρu.adjoint_eq_inv, inv_inv] at h
    exact h.symm
  have hS : ∀ g : G, ((ContinuousLinearMap.adjoint T).comp T) ∘L π g
      = π g ∘L ((ContinuousLinearMap.adjoint T).comp T) := by
    intro g
    rw [ContinuousLinearMap.comp_assoc, hT g, ← ContinuousLinearMap.comp_assoc, hadj g,
      ContinuousLinearMap.comp_assoc]
  -- Schur's lemma: the self-intertwiner is a scalar
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_irreducible π hirr
    { toContinuousLinearMap := (ContinuousLinearMap.adjoint T).comp T, isIntertwining' := hS }
  have hcS : ∀ v : V, ContinuousLinearMap.adjoint T (T v) = c • v := fun v ↦ by
    simpa using congrArg (fun f : ContIntertwiningMap π π ↦ f.toContinuousLinearMap v) hc
  have hinner : ∀ v : V, ((‖T v‖ : ℝ) : 𝕜) ^ 2 = (starRingEnd 𝕜) c * ((‖v‖ : ℝ) : 𝕜) ^ 2 := by
    intro v
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K,
      ← ContinuousLinearMap.adjoint_inner_left T v (T v), hcS v, inner_smul_left]
  -- the scalar is a positive real, because `T` is injective and the carrier is nonzero
  have _ : Nontrivial V := Representation.IsIrreducible.nontrivial hirr
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  set a : ℝ := ‖T v₀‖ ^ 2 / ‖v₀‖ ^ 2 with ha
  have hv₀norm : (0 : ℝ) < ‖v₀‖ := norm_pos_iff.2 hv₀
  have hTinj : Function.Injective T := φ.toContinuousLinearEquiv.injective
  have hTv₀ : (0 : ℝ) < ‖T v₀‖ := norm_pos_iff.2 fun h ↦ hv₀ (hTinj (by simpa using h))
  have hapos : 0 < a := div_pos (by positivity) (by positivity)
  have hca : (starRingEnd 𝕜) c = ((a : ℝ) : 𝕜) := by
    have hne : ((‖v₀‖ : ℝ) : 𝕜) ≠ 0 := by simpa using hv₀norm.ne'
    rw [ha]
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hne)]
    exact (hinner v₀).symm
  have hnorm : ∀ v : V, ‖T v‖ = Real.sqrt a * ‖v‖ := by
    intro v
    have h : ‖T v‖ ^ 2 = a * ‖v‖ ^ 2 := by
      have h' := hinner v
      rw [hca] at h'
      exact_mod_cast h'
    rw [← Real.sqrt_sq (norm_nonneg (T v)), h, Real.sqrt_mul hapos.le,
      Real.sqrt_sq (norm_nonneg v)]
  -- rescaling by `1/√a` turns `T` into an isometry, which still intertwines
  have hsqrt : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.2 hapos
  set b : 𝕜 := ((Real.sqrt a : ℝ) : 𝕜)⁻¹ with hb
  have hbne : b ≠ 0 := inv_ne_zero (by simpa using hsqrt.ne')
  have hbnorm : ‖b‖ = (Real.sqrt a)⁻¹ := by
    rw [hb, norm_inv, RCLike.norm_ofReal, abs_of_pos hsqrt]
  let L : V ≃ₗ[𝕜] W :=
    φ.toContinuousLinearEquiv.toLinearEquiv.trans (LinearEquiv.smulOfNeZero 𝕜 W b hbne)
  have hL : ∀ v : V, L v = b • T v := fun _ ↦ rfl
  have hLnorm : ∀ v : V, ‖L v‖ = ‖v‖ := by
    intro v
    rw [hL, norm_smul, hbnorm, hnorm v, ← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
  set e : V ≃ₗᵢ[𝕜] W := ⟨L, hLnorm⟩
  -- `e` is `L` with its norm bundled, so it acts as `L` does
  have he : ∀ v : V, e v = b • T v := hL
  have key : ∀ (g : G) (v : V), e (π g v) = ρ g (e v) := fun g v ↦ by
    rw [he, he, hTapp, map_smul]
  refine ⟨e, DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun x ↦ ?_⟩
  rw [congr_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, key g (e.symm x), e.apply_symm_apply]

end ContRepresentation

end TauCeti
