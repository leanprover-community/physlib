/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.AddGroup
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
import PhyslibAlpha.Mathematics.TauCeti.Analysis.Normed.Operator.Dense

/-!
# The GNS translation representation of a positive-definite function

A positive-definite function on an additive commutative group has a canonical Hilbert space,
obtained from its translation-invariant positive-definite kernel.

## i. Overview

A positive-definite function on an additive commutative group has a canonical Hilbert space,
obtained from its translation-invariant positive-definite kernel. Translation of the kernel
vectors extends uniquely to a unitary operator. These operators form a group representation,
and the original function is a matrix coefficient of its vector at zero.

The translation action is part of the GNS/Kolmogorov decomposition of a positive-definite
function. Its later use in LCA Bochner theory requires spectral measures and Pontryagin duality.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* W. Rudin, *Fourier Analysis on Groups* (1962), Chapter 1.
-/

public section

/-! ## A. Development -/

noncomputable section

open InnerProductSpace Filter

namespace TauCeti

namespace IsPositiveDefiniteSub

variable {G : Type*} [AddCommGroup G] {F : G → ℂ} (hF : IsPositiveDefiniteSub F)

/-- The canonical Hilbert space of the translation-invariant kernel `K(a,b) = F(a-b)`. -/
abbrev gnsSpace := Matrix.PosSemidef.KolmogorovSpace hF.posSemidef

/-- The vector in the GNS space corresponding to a group element. -/
def gnsVector (a : G) : hF.gnsSpace := hF.posSemidef.kolmogorovFeature a

/-- The inner product of two GNS vectors is the original positive-definite kernel. -/
@[simp]
lemma inner_gnsVector (a b : G) : ⟪hF.gnsVector a, hF.gnsVector b⟫_ℂ = F (a - b) :=
  hF.posSemidef.inner_kolmogorovFeature a b

/-- Squared distances between GNS vectors are controlled by the real part of the function. -/
@[simp]
lemma norm_gnsVector_sub_sq (a b : G) :
    ‖hF.gnsVector a - hF.gnsVector b‖ ^ 2 =
      2 * ((F 0).re - (F (a - b)).re) := by
  rw [gnsVector, gnsVector, Matrix.PosSemidef.norm_kolmogorovFeature_sub_sq]
  simp only [sub_self]
  -- The generic Kolmogorov formula uses `RCLike.re`; here the scalar field is `ℂ`.
  change (F 0).re - 2 * (F (a - b)).re + (F 0).re =
    2 * ((F 0).re - (F (a - b)).re)
  ring

/-- The GNS vectors span a dense subspace. -/
lemma gnsVector_dense :
    (Submodule.span ℂ (Set.range hF.gnsVector)).topologicalClosure = ⊤ :=
  hF.posSemidef.kolmogorovFeature_dense

private lemma translated_gnsVector_dense (g : G) :
    (Submodule.span ℂ (Set.range fun a : G => hF.gnsVector (g + a))).topologicalClosure = ⊤ := by
  have hrange : Set.range (fun a : G => hF.gnsVector (g + a)) = Set.range hF.gnsVector := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨g + a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨-g + a, by simp⟩
  rw [hrange]
  exact hF.gnsVector_dense

/-- Translation by `g` is a unitary operator on the canonical GNS Hilbert space. Its action on
the dense family of kernel vectors is `v(a) ↦ v(g+a)`. -/
def gnsTranslation (g : G) : hF.gnsSpace ≃ₗᵢ[ℂ] hF.gnsSpace :=
  hF.posSemidef.kolmogorovEquiv (fun a => hF.gnsVector (g + a))
    (by
      intro a b
      simp only [hF.inner_gnsVector, add_sub_add_left_eq_sub])
    (hF.translated_gnsVector_dense g)

/-- Translation acts on the canonical GNS vectors by addition. -/
@[simp]
lemma gnsTranslation_gnsVector (g a : G) :
    hF.gnsTranslation g (hF.gnsVector a) = hF.gnsVector (g + a) :=
  by simpa only [gnsTranslation, gnsVector] using
    hF.posSemidef.kolmogorovEquiv_apply _ _ _ a

/-- The translation at zero is the identity operator. -/
@[simp]
lemma gnsTranslation_zero : hF.gnsTranslation 0 = LinearIsometryEquiv.refl ℂ hF.gnsSpace := by
  apply LinearIsometryEquiv.toLinearIsometry_injective
  have hinner : ∀ a b, ⟪hF.gnsVector a, hF.gnsVector b⟫_ℂ = F (a - b) :=
    hF.inner_gnsVector
  exact (hF.posSemidef.kolmogorovIsometry_unique _ hinner _
    (by intro a; simpa only [gnsVector, zero_add,
      LinearIsometryEquiv.coe_toLinearIsometry] using hF.gnsTranslation_gnsVector 0 a)).trans
    (hF.posSemidef.kolmogorovIsometry_unique _ hinner _ (by intro a; rfl)).symm

/-- GNS translations compose according to the group law. -/
@[simp]
lemma gnsTranslation_add (g k : G) :
    hF.gnsTranslation (g + k) = (hF.gnsTranslation k).trans (hF.gnsTranslation g) := by
  apply LinearIsometryEquiv.toLinearIsometry_injective
  have hinner : ∀ a b,
      ⟪hF.gnsVector ((g + k) + a), hF.gnsVector ((g + k) + b)⟫_ℂ = F (a - b) := by
    intro a b
    simp only [hF.inner_gnsVector, add_sub_add_left_eq_sub]
  exact (hF.posSemidef.kolmogorovIsometry_unique _ hinner _
    (by intro a; simpa only [gnsVector,
      LinearIsometryEquiv.coe_toLinearIsometry] using hF.gnsTranslation_gnsVector (g + k) a)).trans
    (hF.posSemidef.kolmogorovIsometry_unique _ hinner _
      (by
        intro a
        -- Uniqueness uses the Kolmogorov feature map, which `gnsVector` wraps definitionally.
        simp only [LinearIsometryEquiv.coe_toLinearIsometry,
          LinearIsometryEquiv.trans_apply,
          show hF.posSemidef.kolmogorovFeature a = hF.gnsVector a from rfl,
          hF.gnsTranslation_gnsVector, add_assoc])).symm

/-- The GNS representation as a homomorphism from the multiplicative copy of `G` to the
unitary operators on its canonical Hilbert space. -/
def gnsRepresentation : Multiplicative G →* (hF.gnsSpace ≃ₗᵢ[ℂ] hF.gnsSpace) :=
  MonoidHom.mk' (fun g => hF.gnsTranslation (Multiplicative.toAdd g)) (by
    intro g k
    rw [toAdd_mul, LinearIsometryEquiv.mul_def]
    exact hF.gnsTranslation_add (Multiplicative.toAdd g) (Multiplicative.toAdd k))

/-- The representation operator at `g` is translation by `g`. -/
@[simp]
lemma gnsRepresentation_ofAdd (g : G) :
    hF.gnsRepresentation (Multiplicative.ofAdd g) = hF.gnsTranslation g := by
  simp [gnsRepresentation]

/-- The representation translates each GNS vector. -/
lemma gnsRepresentation_gnsVector (g a : G) :
    hF.gnsRepresentation (Multiplicative.ofAdd g) (hF.gnsVector a) =
      hF.gnsVector (g + a) :=
  by simpa only [hF.gnsRepresentation_ofAdd] using hF.gnsTranslation_gnsVector g a

/-- A positive-definite function is a matrix coefficient of its canonical unitary
representation. -/
lemma eq_inner_gnsRepresentation (g : G) :
    F g = ⟪hF.gnsRepresentation (Multiplicative.ofAdd g) (hF.gnsVector 0),
      hF.gnsVector 0⟫_ℂ := by
  simp only [hF.gnsRepresentation_gnsVector, add_zero, hF.inner_gnsVector, sub_zero]

/-- Continuity of a positive-definite function at zero makes its canonical feature map
continuous. This is the regularity needed for a strongly continuous representation. -/
lemma continuous_gnsVector [TopologicalSpace G] [IsTopologicalAddGroup G]
    (hcont : ContinuousAt F 0) : Continuous hF.gnsVector := by
  rw [continuous_iff_continuousAt]
  intro a
  have hsub : ContinuousAt (fun b : G => b - a) a := by fun_prop
  have hsub0 : Tendsto (fun b : G => b - a) (nhds a) (nhds 0) := by
    convert hsub.tendsto using 1
    simp
  have hcomp : ContinuousAt (fun b : G => F (b - a)) a := by
    simpa only [ContinuousAt, sub_self, Function.comp_def] using hcont.tendsto.comp hsub0
  have hrhs : ContinuousAt (fun b : G =>
      2 * ((F 0).re - (F (b - a)).re)) a := by
    exact (continuousAt_const.sub (Complex.continuous_re.continuousAt.comp hcomp)).const_mul 2
  have hsq : Tendsto (fun b : G => ‖hF.gnsVector b - hF.gnsVector a‖ ^ 2)
      (nhds a) (nhds 0) := by
    simp only [hF.norm_gnsVector_sub_sq]
    simpa using hrhs.tendsto
  have hsqrt : Tendsto (fun b : G => ‖hF.gnsVector b - hF.gnsVector a‖)
      (nhds a) (nhds 0) := by
    have := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using this
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hsqrt

private lemma continuous_gnsTranslation_gnsVector [TopologicalSpace G] [IsTopologicalAddGroup G]
    (hcont : ContinuousAt F 0) (a : G) :
    Continuous (fun g : G => hF.gnsTranslation g (hF.gnsVector a)) := by
  simpa [Function.comp_def] using
    (hF.continuous_gnsVector hcont).comp (continuous_id.add continuous_const)

/-- The GNS translation representation is strongly continuous: every vector has a continuous
orbit. -/
lemma continuous_gnsTranslation_apply [TopologicalSpace G] [IsTopologicalAddGroup G]
    (hcont : ContinuousAt F 0) (x : hF.gnsSpace) :
    Continuous (fun g : G => hF.gnsTranslation g x) := by
  have hdense : Dense (Submodule.span ℂ (Set.range hF.gnsVector) : Set hF.gnsSpace) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hF.gnsVector_dense
  have hspan : ∀ y ∈ Submodule.span ℂ (Set.range hF.gnsVector),
      Continuous (fun g : G => hF.gnsTranslation g y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩
      exact hF.continuous_gnsTranslation_gnsVector hcont a
    | zero => simpa using (continuous_const : Continuous fun _ : G => (0 : hF.gnsSpace))
    | add y z _ _ hy hz =>
      have heq : (fun g : G => hF.gnsTranslation g (y + z)) =
          (fun g => hF.gnsTranslation g y) + (fun g => hF.gnsTranslation g z) := by
        funext g
        simp
      rw [heq]
      exact hy.add hz
    | smul c y _ hy =>
      have heq : (fun g : G => hF.gnsTranslation g (c • y)) =
          c • (fun g => hF.gnsTranslation g y) := by
        funext g
        simp
      rw [heq]
      exact hy.const_smul c
  rw [continuous_iff_continuousAt]
  intro g
  let T (b : G) : hF.gnsSpace →L[ℂ] hF.gnsSpace :=
    (hF.gnsTranslation b).toLinearIsometry.toContinuousLinearMap
  have hbound : ∀ᶠ b : G in nhds g, ‖T b‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun b =>
      (hF.gnsTranslation b).toLinearIsometry.norm_toContinuousLinearMap_le
  have htendsto : ∀ y ∈ Submodule.span ℂ (Set.range hF.gnsVector),
      Tendsto (fun b => T b y) (nhds g) (nhds (T g y)) := by
    intro y hy
    simpa only [T, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using (hspan y hy).continuousAt.tendsto
  simpa only [ContinuousAt, T, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] using
      (ContinuousLinearMap.tendsto_apply_of_dense hdense hbound htendsto x)

/-- The canonical unitary representation has continuous orbits. -/
lemma continuous_gnsRepresentation_apply [TopologicalSpace G] [IsTopologicalAddGroup G]
    (hcont : ContinuousAt F 0) (x : hF.gnsSpace) :
    Continuous (fun g : Multiplicative G => hF.gnsRepresentation g x) := by
  have heq : (fun g : Multiplicative G => hF.gnsRepresentation g x) =
      (fun g => hF.gnsTranslation g.toAdd x) := by
    funext g
    simpa only [ofAdd_toAdd] using
      congrArg (fun T => T x) (hF.gnsRepresentation_ofAdd g.toAdd)
  rw [heq]
  exact (hF.continuous_gnsTranslation_apply hcont x).comp continuous_toAdd

end IsPositiveDefiniteSub

end TauCeti

end
