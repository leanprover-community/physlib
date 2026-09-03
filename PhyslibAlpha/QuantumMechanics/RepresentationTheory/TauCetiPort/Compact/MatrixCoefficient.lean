/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.MeasureTheory.Group.Conjugation
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Haar
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.MatrixCoefficient
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Matrix coefficients in `L²` of a compact group

A matrix coefficient `g ↦ ⟪π g v, w⟫` of a continuous representation of a compact group is a
continuous function on a probability space, hence square integrable. This file records its image
in `L²(G)` for normalized Haar measure, and the identities that turn `L²`-statements about matrix
coefficients into integrals.

The `L²` picture is what the Schur orthogonality relations are stated in: they compute the inner
product of two matrix coefficients, and `inner_matrixCoeffLp` below rewrites that inner product as
the Haar integral the orthogonality argument evaluates.

## Main definitions

* `TauCeti.ContRepresentation.matrixCoeffLp`: the matrix coefficient `g ↦ ⟪π g v, w⟫` as an element
  of `Lp 𝕜 2 (haarProb G)`.
* `TauCeti.ContRepresentation.matrixCoeffLpₛₗ`: the matrix coefficients of a fixed representation
  bundled as a sesquilinear map `V →ₗ⋆[𝕜] V →ₗ[𝕜] Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.ContRepresentation.inner_matrixCoeffLp`: the `L²` inner product of two matrix
  coefficients is the Haar integral of their pointwise product, in Mathlib's convention
  `⟪F, H⟫ = ∫ H · conj F`.
* `TauCeti.ContRepresentation.norm_matrixCoeffLp_sq`: the squared `L²` norm is the Haar integral of
  the squared modulus.
* `TauCeti.ContRepresentation.norm_matrixCoeffLp_le`: for a unitary representation the `L²` norm is
  at most `‖v‖ * ‖w‖`, because normalized Haar measure has total mass one.
* `TauCeti.ContRepresentation.matrixCoeffLp_eq_zero_iff`: passing to `L²` loses no information,
  since Haar measure is positive on nonempty open sets.
* `TauCeti.ContRepresentation.matrixCoeffLp_map_map`: moving both defining vectors by `π h`
  reparametrizes the matrix coefficient by a conjugation.

This is the second half of the Layer 3 milestone of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), whose first half is the
uniform-norm algebra in `TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`. The
mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- The matrix coefficient `g ↦ ⟪π g v, w⟫` as an element of `L²(G)` for normalized Haar measure.

A matrix coefficient is continuous and `G` is compact, so `ContinuousMap.toLp` applies; the
normalization of Haar measure to a probability measure is what makes the resulting `L²` norms
comparable to the uniform norm without a measure-dependent constant. -/
noncomputable def matrixCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem matrixCoeffLp_def (v w : V) :
    matrixCoeffLp π hπ v w = ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w) :=
  (rfl)

/-- A matrix coefficient in `L²` is represented, almost everywhere, by the function it comes
from. -/
theorem coeFn_matrixCoeffLp (v w : V) :
    matrixCoeffLp π hπ v w =ᵐ[haarProb G] fun g ↦ ⟪π g v, w⟫_𝕜 := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G)
    (matrixCoeff π hπ v w)] with g hg
  rw [matrixCoeffLp_def, hg, matrixCoeff_apply]

/-! ### Sesquilinearity in the defining vectors

Passing to `L²` is linear, so the sesquilinearity of `matrixCoeff` transfers verbatim. -/

@[simp]
theorem matrixCoeffLp_zero_left (w : V) : matrixCoeffLp π hπ 0 w = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_zero_right (v : V) : matrixCoeffLp π hπ v 0 = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_left (v₁ v₂ w : V) :
    matrixCoeffLp π hπ (v₁ + v₂) w = matrixCoeffLp π hπ v₁ w + matrixCoeffLp π hπ v₂ w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_right (v w₁ w₂ : V) :
    matrixCoeffLp π hπ v (w₁ + w₂) = matrixCoeffLp π hπ v w₁ + matrixCoeffLp π hπ v w₂ := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_left (c : 𝕜) (v w : V) :
    matrixCoeffLp π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeffLp π hπ v (c • w) = c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

/-- The `L²` matrix coefficients of a fixed representation, bundled as a sesquilinear map:
conjugate linear in the first vector, linear in the second, exactly as Mathlib's `innerₛₗ`.

This is `matrixCoeffₛₗ` postcomposed with the linear map `ContinuousMap.toLp`, so the
sesquilinearity is inherited rather than reproved; bundling supplies the remaining additive
identities (`map_neg`, `map_sub`, `map_sum`) through the `LinearMap` API. -/
noncomputable def matrixCoeffLpₛₗ : V →ₗ⋆[𝕜] V →ₗ[𝕜] Lp 𝕜 2 (haarProb G) :=
  (matrixCoeffₛₗ π hπ).compr₂ₛₗ (ContinuousMap.toLp 2 (haarProb G) 𝕜).toLinearMap

@[simp]
theorem matrixCoeffLpₛₗ_apply_apply (v w : V) :
    matrixCoeffLpₛₗ π hπ v w = matrixCoeffLp π hπ v w := by
  rw [matrixCoeffLpₛₗ, LinearMap.compr₂ₛₗ_apply, ContinuousLinearMap.coe_coe,
    matrixCoeffₛₗ_apply_apply, matrixCoeffLp_def]

/-! ### Passing to `L²` loses no information

Haar measure is positive on nonempty open sets, so two continuous functions agreeing almost
everywhere agree. -/

/-- A matrix coefficient vanishes in `L²` exactly when the continuous function it comes from is
the zero function: `ContinuousMap.toLp` is injective for a measure that is positive on nonempty
open sets, and normalized Haar measure is one. -/
theorem matrixCoeffLp_eq_zero_iff (v w : V) :
    matrixCoeffLp π hπ v w = 0 ↔ matrixCoeff π hπ v w = 0 := by
  rw [matrixCoeffLp_def, ← map_zero (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜),
    ContinuousMap.toLp_inj]

/-- A matrix coefficient vanishes in `L²` exactly when it vanishes identically. -/
theorem matrixCoeffLp_eq_zero_iff_forall (v w : V) :
    matrixCoeffLp π hπ v w = 0 ↔ ∀ g : G, ⟪π g v, w⟫_𝕜 = 0 := by
  rw [matrixCoeffLp_eq_zero_iff]
  constructor
  · intro h g
    rw [← matrixCoeff_apply π hπ v w g, h, ContinuousMap.zero_apply]
  · intro h
    ext g
    simpa using h g

/-! ### The inner product as a Haar integral -/

/-- The `L²` inner product of two matrix coefficients is the Haar integral of their pointwise
product. Mathlib's inner product is conjugate linear in its first argument and unfolds as
`⟪F, H⟫ = ∫ H · conj F`, which is where the conjugation sits below; this placement is what the
Schur orthogonality relations are stated against. -/
theorem inner_matrixCoeffLp (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (v w : V)
    (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = ∫ g, ⟪ρ g v', w'⟫_𝕜 * (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 ∂(haarProb G) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, ContinuousMap.inner_toLp]
  simp

/-- The squared `L²` norm of a matrix coefficient is the Haar integral of its squared modulus. -/
theorem norm_matrixCoeffLp_sq (v w : V) :
    ‖matrixCoeffLp π hπ v w‖ ^ 2 = ∫ g, ‖⟪π g v, w⟫_𝕜‖ ^ 2 ∂(haarProb G) := by
  have h := inner_matrixCoeffLp π hπ π hπ v w v w
  rw [inner_self_eq_norm_sq_to_K] at h
  have hpt : ∀ g : G,
      ⟪π g v, w⟫_𝕜 * (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 = ((‖⟪π g v, w⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    intro g
    rw [RCLike.mul_conj]
    push_cast
    ring
  simp_rw [hpt, integral_ofReal] at h
  exact_mod_cast h

/-! ### Bounds from the normalization of Haar measure -/

/-- The `L²` norm of a matrix coefficient of a unitary representation is at most the product of the
norms of its defining vectors, with no constant: normalized Haar measure has total mass one, so
`ContinuousMap.toLp` is a contraction from the uniform norm, where `norm_matrixCoeff_le` is the
matching bound. -/
theorem norm_matrixCoeffLp_le (hunitary : IsUnitary π) (v w : V) :
    ‖matrixCoeffLp π hπ v w‖ ≤ ‖v‖ * ‖w‖ := by
  have hmass : measureUnivNNReal (haarProb G) = 1 :=
    ENNReal.coe_inj.1 (by simp [coe_measureUnivNNReal])
  have hop : ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ ≤ 1 := by
    simpa [hmass] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := 2) (𝕜 := 𝕜) (haarProb G)
  rw [matrixCoeffLp_def]
  calc ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)‖
      ≤ ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ * ‖matrixCoeff π hπ v w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (‖v‖ * ‖w‖) :=
        mul_le_mul hop (norm_matrixCoeff_le π hπ hunitary v w) (norm_nonneg _) zero_le_one
    _ = ‖v‖ * ‖w‖ := one_mul _

/-! ### The trivial representation, and subrepresentations -/

/-- The matrix coefficients of the trivial representation are constants, and normalized Haar
measure gives a constant its own norm. This is the sanity check that `matrixCoeffLp` carries the
probability normalization rather than an unnormalized one. -/
theorem norm_matrixCoeffLp_trivial (v w : V) :
    ‖matrixCoeffLp (ContRepresentation.trivial 𝕜 G V) continuous_const v w‖ = ‖⟪v, w⟫_𝕜‖ := by
  have h : ‖matrixCoeffLp (ContRepresentation.trivial 𝕜 G V) continuous_const v w‖ ^ 2
      = ‖⟪v, w⟫_𝕜‖ ^ 2 := by
    simpa using norm_matrixCoeffLp_sq (ContRepresentation.trivial 𝕜 G V) continuous_const v w
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- A matrix coefficient of an invariant submodule is the matrix coefficient of the ambient
representation at the underlying vectors, so passing to a subrepresentation creates no new
elements of `L²(G)`. -/
@[simp]
theorem matrixCoeffLp_subrepresentation {U : Submodule 𝕜 V} (hU : ∀ g, ∀ v ∈ U, π g v ∈ U)
    (v w : U) :
    matrixCoeffLp (subrepresentation π U hU) (continuous_subrepresentation hπ) v w
      = matrixCoeffLp π hπ (v : V) (w : V) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, matrixCoeff_subrepresentation]

/-! ### Moving both defining vectors -/

/-- **Simultaneously moving the two vectors conjugates the argument of a matrix coefficient.** -/
theorem matrixCoeffLp_map_map (hunitary : IsUnitary π) (h : G) (v w : V) :
    matrixCoeffLp π hπ (π h v) (π h w) = conjLpₗᵢ 𝕜 h⁻¹ (matrixCoeffLp π hπ v w) := by
  have hcoeff : matrixCoeff π hπ (π h v) (π h w) =
      (matrixCoeff π hπ v w).comp
        ⟨fun g ↦ h⁻¹ * g * (h⁻¹)⁻¹, (continuous_const.mul continuous_id).mul continuous_const⟩ := by
    ext g
    calc
      matrixCoeff π hπ (π h v) (π h w) g =
          matrixCoeff π hπ (π h v) w (h⁻¹ * g) := by
        simpa using (matrixCoeff_apply_mul_left hπ hunitary (π h v) w h⁻¹ g).symm
      _ = matrixCoeff π hπ v w ((h⁻¹ * g) * h) :=
        (matrixCoeff_apply_mul_right π hπ v w (h⁻¹ * g) h).symm
      _ = matrixCoeff π hπ v w (h⁻¹ * g * (h⁻¹)⁻¹) := by simp
  rw [matrixCoeffLp_def, matrixCoeffLp_def, conjLpₗᵢ_apply]
  calc
    ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ (π h v) (π h w)) =
        ContinuousMap.toLp 2 (haarProb G) 𝕜 ((matrixCoeff π hπ v w).comp
          ⟨fun g ↦ h⁻¹ * g * (h⁻¹)⁻¹,
            (continuous_const.mul continuous_id).mul continuous_const⟩) := congrArg _ hcoeff
    _ = Lp.compMeasurePreserving (fun g ↦ h⁻¹ * g * (h⁻¹)⁻¹)
          (measurePreserving_conj (haarProb G) h⁻¹)
          (ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)) :=
      (Lp.compMeasurePreserving_toLp 𝕜 (matrixCoeff π hπ v w)
        ⟨fun g ↦ h⁻¹ * g * (h⁻¹)⁻¹,
          (continuous_const.mul continuous_id).mul continuous_const⟩
        (measurePreserving_conj (haarProb G) h⁻¹)).symm

end CompactGroup

end ContRepresentation

end TauCeti
