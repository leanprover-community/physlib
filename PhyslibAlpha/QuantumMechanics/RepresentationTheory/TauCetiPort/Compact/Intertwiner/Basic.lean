/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Analysis.Normed.Module.Trace
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Averaging
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.MatrixCoefficient
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.LinHom
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Averaging an operator into an intertwiner

Given continuous representations `π` on `V` and `ρ` on `W` of a compact group `G`, any continuous
linear map `T : V →L[𝕜] W` can be averaged against normalized Haar measure into

`averageOperator π hπ ρ hρ T = ∫ g, ρ g⁻¹ ∘ T ∘ π g ∂(haarProb G)`,

which *is* an intertwiner: `averageOperator … ∘ π g = ρ g ∘ averageOperator …`. This is the tool the
Schur orthogonality relations run on, and it is the exact analogue for compact groups of the finite
average `|G|⁻¹ ∑ g, ρ g⁻¹ ∘ T ∘ π g` behind Mathlib's Maschke theorem
(`LinearMap.sumOfConjugates`), with the Haar integral in place of the finite sum.

The target `W` is not assumed complete. `averageOperator` is `TauCeti.haarAverage` of a continuous
family valued in the operator space `V →L[𝕜] W`, so it inherits that average's convention: it is the
displayed Haar integral when that space is complete, and the Bochner integral's junk value `0`
otherwise. `[CompleteSpace W]` is what supplies completeness of `V →L[𝕜] W`, so the statements that
read the average's actual value, from `TauCeti.ContRepresentation.averageOperator_apply` onwards,
carry it.

The construction is a projection onto the intertwiners: it is linear in `T`, it fixes every
intertwiner, and — when `V = W` and `π = ρ` and `V` is finite-dimensional — it preserves the trace.
That last fact is what pins the constant `d⁻¹` in the first Schur orthogonality relation.

## Main definitions

* `TauCeti.ContRepresentation.averageOperator`: the Haar average `∫ g, ρ g⁻¹ ∘ T ∘ π g`.
* `TauCeti.ContRepresentation.averageOperatorₗ`: the same, bundled as a linear map in `T`.
* `TauCeti.ContRepresentation.averageIntertwiner`: the average packaged as a term of Mathlib's
  `ContIntertwiningMap π ρ`.

## Main statements

* `TauCeti.ContRepresentation.averageOperator_comp`: the average intertwines `π` with `ρ`.
* `TauCeti.ContRepresentation.averageOperator_eq_self`: the average fixes an operator that already
  intertwines, so `averageOperator` is idempotent
  (`TauCeti.ContRepresentation.averageOperator_averageOperator`).
* `TauCeti.ContRepresentation.trace_averageOperator`: averaging a self-map of a finite-dimensional
  representation preserves the trace.
* `TauCeti.ContRepresentation.inner_matrixCoeffLp_eq_inner_averageOperator`: the `L²` inner product
  of two matrix coefficients is a matrix entry of the average of a **rank-one** operator. This is
  the identity that turns Schur orthogonality into a statement about intertwiners.
* `TauCeti.ContRepresentation.schur_orthogonality_distinct`: **the second Schur orthogonality
  relation.** If there is no nonzero continuous intertwiner `π → ρ`, every matrix coefficient of `π`
  is `L²`-orthogonal to every matrix coefficient of `ρ`.

This is the intertwiner half of Layer 4 of the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose orthogonality statements are pinned in its `Suggested.lean`. Schur's lemma itself is not used
here: `schur_orthogonality_distinct` takes the vanishing of the intertwiner space as a hypothesis,
which is precisely what Schur's lemma supplies for inequivalent irreducibles.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace W] in
/-- An action operator composed with the action of the inverse group element is the identity. -/
private theorem comp_inv_self (g : G) : (ρ g).comp (ρ g⁻¹) = ContinuousLinearMap.id 𝕜 W := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
  rfl

include hπ hρ

omit [CompleteSpace W] in
/-- The integrand `g ↦ ρ g⁻¹ ∘ T ∘ π g` of the averaging construction, as a continuous map on the
group. Continuity is where the two continuity hypotheses on the representations are used. -/
private noncomputable def conjFamily (T : V →L[𝕜] W) : C(G, V →L[𝕜] W) where
  toFun g := (ρ g⁻¹).comp (T.comp (π g))
  continuous_toFun :=
    (hρ.comp continuous_inv).clm_comp (Continuous.clm_comp continuous_const hπ)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W] in
/-- The integrand of the averaging construction, evaluated at a group element and a vector. This
is the unfolding lemma that keeps the proofs below from reaching through `conjFamily`'s
definition. -/
@[simp]
private theorem conjFamily_apply_apply (T : V →L[𝕜] W) (g : G) (v : V) :
    conjFamily π hπ ρ hρ T g v = ρ g⁻¹ (T (π g v)) :=
  rfl

omit [CompleteSpace W] in
/-- The **Haar average of an operator over a pair of representations**,
`∫ g, ρ g⁻¹ ∘ T ∘ π g ∂(haarProb G)`.

On a complete `W` this is always defined — the integrand is continuous and Haar measure is
finite — and it always intertwines `π` with `ρ`
(`TauCeti.ContRepresentation.averageOperator_comp`). `W` is not assumed complete. The average is
taken in the operator space `V →L[𝕜] W`, so it is `TauCeti.haarAverage`'s junk value `0` unless that
space is complete, which `[CompleteSpace W]` supplies; that is why the results below that read the
average's actual value carry it. -/
noncomputable def averageOperator (T : V →L[𝕜] W) : V →L[𝕜] W :=
  haarAverage G (𝕜 := 𝕜) (conjFamily π hπ ρ hρ T)

/-- The average of an operator, evaluated at a vector. -/
theorem averageOperator_apply (T : V →L[𝕜] W) (v : V) :
    averageOperator π hπ ρ hρ T v = ∫ g, ρ g⁻¹ (T (π g v)) ∂haarProb G := by
  have h := (ContinuousLinearMap.apply 𝕜 W v).haarAverage_comp_comm (G := G)
    (conjFamily π hπ ρ hρ T)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [averageOperator, ← h, haarAverage_apply]
  rfl

/-! ### Linearity in the averaged operator -/

omit [CompleteSpace W] in
@[simp]
theorem averageOperator_zero : averageOperator π hπ ρ hρ 0 = 0 := by
  have hzero : conjFamily π hπ ρ hρ 0 = 0 := by
    ext g v
    simp
  rw [averageOperator, hzero, map_zero]

omit [CompleteSpace W] in
@[simp]
theorem averageOperator_add (T₁ T₂ : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (T₁ + T₂)
      = averageOperator π hπ ρ hρ T₁ + averageOperator π hπ ρ hρ T₂ := by
  have hadd : conjFamily π hπ ρ hρ (T₁ + T₂)
      = conjFamily π hπ ρ hρ T₁ + conjFamily π hπ ρ hρ T₂ := by
    ext g v
    simp
  rw [averageOperator, averageOperator, averageOperator, hadd, map_add]

omit [CompleteSpace W] in
@[simp]
theorem averageOperator_smul (c : 𝕜) (T : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (c • T) = c • averageOperator π hπ ρ hρ T := by
  have hsmul : conjFamily π hπ ρ hρ (c • T) = c • conjFamily π hπ ρ hρ T := by
    ext g v
    simp
  rw [averageOperator, averageOperator, hsmul, map_smul]

omit [CompleteSpace W] in
/-- Haar averaging over a pair of representations, bundled as a linear map in the averaged
operator. Bundling supplies the remaining additive identities (`map_neg`, `map_sub`, `map_sum`)
through the `LinearMap` API. -/
noncomputable def averageOperatorₗ : (V →L[𝕜] W) →ₗ[𝕜] V →L[𝕜] W where
  toFun := averageOperator π hπ ρ hρ
  map_add' := averageOperator_add π hπ ρ hρ
  map_smul' := averageOperator_smul π hπ ρ hρ

omit [CompleteSpace W] in
@[simp]
theorem averageOperatorₗ_apply (T : V →L[𝕜] W) :
    averageOperatorₗ π hπ ρ hρ T = averageOperator π hπ ρ hρ T :=
  (rfl)

/-! ### The average is an intertwiner

The proof is the same shape as the invariance half of Weyl's unitarian trick: conjugation by a
fixed pair of action operators is a continuous *linear* map on operators, so it commutes with Haar
averaging, and on the integrand it acts as right translation of the group variable, which the Haar
average does not see. -/

omit hπ hρ [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace W] in
/-- Conjugation `S ↦ ρ g⁻¹ ∘ S ∘ π g`, packaged as a continuous linear map on operators. It is the
action operator at `g⁻¹` of the Hom representation of
`TauCeti/RepresentationTheory/Continuous/LinHom.lean`, which is what makes it linear. -/
private noncomputable def conjAction (g : G) : (V →L[𝕜] W) →L[𝕜] V →L[𝕜] W :=
  ContRepresentation.linHom π ρ g⁻¹

omit hπ hρ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace W] in
/-- `conjAction` is conjugation, unfolded. -/
private theorem conjAction_apply (g : G) (S : V →L[𝕜] W) :
    conjAction π ρ g S = (ρ g⁻¹).comp (S.comp (π g)) := by
  rw [conjAction, ContRepresentation.linHom_apply, inv_inv]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W] in
/-- Conjugating the integrand by the action at `g` translates its group variable on the right by
`g`: `ρ g⁻¹ ∘ (ρ h⁻¹ ∘ T ∘ π h) ∘ π g = ρ (h * g)⁻¹ ∘ T ∘ π (h * g)`. -/
private theorem conjAction_comp_conjFamily (T : V →L[𝕜] W) (g : G) :
    (conjAction π ρ g : C(V →L[𝕜] W, V →L[𝕜] W)).comp (conjFamily π hπ ρ hρ T)
      = (conjFamily π hπ ρ hρ T).comp (ContinuousMap.mulRight g) := by
  ext h v
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, conjAction_apply,
    ContinuousLinearMap.comp_apply, conjFamily_apply_apply, ContinuousMap.coe_mulRight,
    mul_inv_rev, map_mul ρ, map_mul π, mul_apply_eq_comp]

/-- The averaged operator is fixed by conjugation: `ρ g⁻¹ ∘ A ∘ π g = A`. -/
private theorem conjAction_averageOperator (T : V →L[𝕜] W) (g : G) :
    conjAction π ρ g (averageOperator π hπ ρ hρ T) = averageOperator π hπ ρ hρ T := by
  rw [averageOperator, ← ContinuousLinearMap.haarAverage_comp_comm,
    conjAction_comp_conjFamily π hπ ρ hρ T g, haarAverage_comp_mulRight]

/-- **The Haar average of an operator intertwines the two representations.** -/
theorem averageOperator_comp (T : V →L[𝕜] W) (g : G) : (averageOperator π hπ ρ hρ T).comp (π g)
      = (ρ g).comp (averageOperator π hπ ρ hρ T) := by
  have h := conjAction_averageOperator π hπ ρ hρ T g
  rw [conjAction_apply] at h
  calc (averageOperator π hπ ρ hρ T).comp (π g)
      = (ContinuousLinearMap.id 𝕜 W).comp ((averageOperator π hπ ρ hρ T).comp (π g)) := by
        rw [ContinuousLinearMap.id_comp]
    _ = ((ρ g).comp (ρ g⁻¹)).comp ((averageOperator π hπ ρ hρ T).comp (π g)) := by
        rw [comp_inv_self ρ g]
    _ = (ρ g).comp ((ρ g⁻¹).comp ((averageOperator π hπ ρ hρ T).comp (π g))) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (ρ g).comp (averageOperator π hπ ρ hρ T) := by rw [h]

/-- The intertwining identity, applied to a vector, in the shape of Mathlib's
`ContIntertwiningMap.isIntertwining`. -/
theorem averageOperator_isIntertwining (T : V →L[𝕜] W) (g : G) (v : V) :
    averageOperator π hπ ρ hρ T (π g v) = ρ g (averageOperator π hπ ρ hρ T v) :=
  congrArg (fun S : V →L[𝕜] W ↦ S v) (averageOperator_comp π hπ ρ hρ T g)

/-- The Haar average of an operator, packaged as a term of Mathlib's `ContIntertwiningMap`. -/
noncomputable def averageIntertwiner (T : V →L[𝕜] W) : ContIntertwiningMap π ρ where
  __ := averageOperator π hπ ρ hρ T
  isIntertwining' g := averageOperator_comp π hπ ρ hρ T g

@[simp]
theorem toContinuousLinearMap_averageIntertwiner (T : V →L[𝕜] W) :
    (averageIntertwiner π hπ ρ hρ T).toContinuousLinearMap = averageOperator π hπ ρ hρ T :=
  (rfl)

/-- The bundled average, evaluated at a vector. -/
@[simp]
theorem averageIntertwiner_apply (T : V →L[𝕜] W) (v : V) :
    averageIntertwiner π hπ ρ hρ T v = averageOperator π hπ ρ hρ T v :=
  (rfl)

/-! ### Averaging is a projection onto the intertwiners -/

/-- **Averaging fixes an operator that already intertwines.** The integrand is then constant, and
normalized Haar measure has total mass one. -/
theorem averageOperator_eq_self (T : V →L[𝕜] W) (hT : ∀ g : G, T.comp (π g) = (ρ g).comp T) :
    averageOperator π hπ ρ hρ T = T := by
  have hT_apply (g : G) (v : V) : T (π g v) = ρ g (T v) :=
    congrArg (fun S : V →L[𝕜] W ↦ S v) (hT g)
  have hconst : conjFamily π hπ ρ hρ T = ContinuousMap.const G T := by
    ext g v
    rw [conjFamily_apply_apply, hT_apply g v]
    exact Representation.inv_self_apply ρ.toRepresentation g (T v)
  rw [averageOperator, hconst, haarAverage_const]

/-- Averaging fixes every continuous intertwiner. -/
@[simp]
theorem averageOperator_toContinuousLinearMap (f : ContIntertwiningMap π ρ) :
    averageOperator π hπ ρ hρ f.toContinuousLinearMap = f.toContinuousLinearMap :=
  averageOperator_eq_self π hπ ρ hρ _ f.isIntertwining'

/-- Averaging is idempotent: it is a projection of the operators onto the intertwiners. -/
@[simp]
theorem averageOperator_averageOperator (T : V →L[𝕜] W) :
    averageOperator π hπ ρ hρ (averageOperator π hπ ρ hρ T) = averageOperator π hπ ρ hρ T :=
  averageOperator_eq_self π hπ ρ hρ _ (averageOperator_comp π hπ ρ hρ T)

end CompactGroup

section SelfAverage

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- Averaging the identity over a single representation returns the identity. -/
@[simp]
theorem averageOperator_id :
    averageOperator π hπ π hπ (ContinuousLinearMap.id 𝕜 V) = ContinuousLinearMap.id 𝕜 V :=
  averageOperator_eq_self π hπ π hπ _ fun g ↦ by
    rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

end SelfAverage

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis on the trace results below: a finite-dimensional
normed space over an `RCLike` field is already complete. Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance instead. -/
local instance completeSpace_of_finiteDimensional : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [FiniteDimensional 𝕜 V] in
/-- Conjugation does not change the trace, so each value of the integrand has the trace of `T`.
The conjugating unit is the action of `g⁻¹`, viewed through `Representation.asGroupHom`. -/
private theorem trace_conjFamily (T : V →L[𝕜] V) (g : G) :
    LinearMap.trace 𝕜 V (conjFamily π hπ π hπ T g : V →ₗ[𝕜] V)
      = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  have hconj : ((conjFamily π hπ π hπ T g : V →L[𝕜] V) : V →ₗ[𝕜] V)
      = ↑(π.toRepresentation.asGroupHom g⁻¹) * (T : V →ₗ[𝕜] V)
        * ↑(π.toRepresentation.asGroupHom g⁻¹)⁻¹ := by
    ext v
    simp [← map_inv, Representation.asGroupHom_apply,
      ContRepresentation.toMonoidHom_apply]
  rw [hconj, LinearMap.trace_conj]

/-- **Averaging preserves the trace.** In finite dimensions each conjugate `π g⁻¹ ∘ T ∘ π g` has the
trace of `T`, and averaging a constant returns that constant. This is what fixes the normalizing
factor `(dim V)⁻¹` in the first Schur orthogonality relation. -/
theorem trace_averageOperator (T : V →L[𝕜] V) :
    LinearMap.trace 𝕜 V (averageOperator π hπ π hπ T : V →ₗ[𝕜] V)
      = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  have hconst : (traceCLM 𝕜 V : C(V →L[𝕜] V, 𝕜)).comp (conjFamily π hπ π hπ T)
      = ContinuousMap.const G (LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V)) :=
    ContinuousMap.ext fun g ↦ by
      rw [ContinuousMap.comp_apply]
      exact (traceCLM_apply _).trans (trace_conjFamily π hπ T g)
  have h := (traceCLM 𝕜 V).haarAverage_comp_comm (G := G) (conjFamily π hπ π hπ T)
  rw [hconst, haarAverage_const] at h
  rw [← traceCLM_apply, averageOperator, ← h]

end Trace

section Orthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ hρ

/-- A matrix entry of the averaged operator is the Haar integral of the matrix entries of the
integrand. -/
theorem inner_averageOperator (T : V →L[𝕜] W) (v : V) (w : W) :
    ⟪w, averageOperator π hπ ρ hρ T v⟫_𝕜 = ∫ g, ⟪w, ρ g⁻¹ (T (π g v))⟫_𝕜 ∂haarProb G := by
  have h := ((innerSL 𝕜 w).comp (ContinuousLinearMap.apply 𝕜 W v)).haarAverage_comp_comm
    (G := G) (conjFamily π hπ ρ hρ T)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  rw [averageOperator, ← innerSL_apply_apply, ← h, haarAverage_apply]
  rfl

/-- For a **unitary** `ρ` the inverse action can be moved to the other side of the inner product,
which is the form the matrix-coefficient computation needs. -/
theorem inner_averageOperator_of_isUnitary (hunitary : IsUnitary ρ) (T : V →L[𝕜] W)
    (v : V) (w : W) :
    ⟪w, averageOperator π hπ ρ hρ T v⟫_𝕜 = ∫ g, ⟪ρ g w, T (π g v)⟫_𝕜 ∂haarProb G := by
  rw [inner_averageOperator π hπ ρ hρ T v w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  rw [hunitary.inner_map_right g⁻¹ w (T (π g v)), inv_inv]

/-- **The `L²` inner product of two matrix coefficients is a matrix entry of an averaged rank-one
operator.** For the rank-one operator `InnerProductSpace.rankOne 𝕜 w' w = ⟪w, ·⟫ • w'` the
integrand `⟪ρ g v', T (π g v)⟫` is exactly the pointwise product
`⟪ρ g v', w'⟫ · conj ⟪π g v, w⟫` computed by
`TauCeti.ContRepresentation.inner_matrixCoeffLp`.

This is the identity that reduces Schur orthogonality to a statement about the intertwiner space:
the operator on the right is an intertwiner `π → ρ` by
`TauCeti.ContRepresentation.averageOperator_comp`. -/
theorem inner_matrixCoeffLp_eq_inner_averageOperator (hunitary : IsUnitary ρ)
    (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = ⟪v', averageOperator π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w) v⟫_𝕜 := by
  rw [inner_matrixCoeffLp π hπ ρ hρ v w v' w',
    inner_averageOperator_of_isUnitary π hπ ρ hρ hunitary _ v v']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  rw [InnerProductSpace.inner_right_rankOne_apply, inner_conj_symm w (π g v)]

/-- **Schur orthogonality for inequivalent representations.** If the only continuous intertwiner
`π → ρ` is zero, then every matrix coefficient of `π` is `L²`-orthogonal to every matrix
coefficient of `ρ`.

Schur's lemma is not invoked here; it is what supplies the hypothesis for a pair of inequivalent
irreducibles. Only `ρ` is required to be unitary: unitarity of `ρ` is what lets the inverse action
be moved across the inner product, and nothing in the argument constrains `π`. -/
theorem schur_orthogonality_distinct (hunitary : IsUnitary ρ)
    (hdistinct : ∀ f : ContIntertwiningMap π ρ, f.toContinuousLinearMap = 0) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜 = 0 := by
  have hzero : averageOperator π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w) = 0 := by
    simpa using hdistinct (averageIntertwiner π hπ ρ hρ (InnerProductSpace.rankOne 𝕜 w' w))
  rw [inner_matrixCoeffLp_eq_inner_averageOperator π hπ ρ hρ hunitary v w v' w', hzero]
  simp

end Orthogonality

end ContRepresentation

end TauCeti
