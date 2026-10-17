/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.States.Mixed.MState

public import Mathlib.Topology.Order.Hom.Basic

/-! # Classes of Matrix Maps

The bundled `MatrixMap`s: `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap`.
These are defined over the bare minimum rings (`Semiring` or `RCLike`, respectively).

The combinations `PTPMap` (positive trace-preserving), `CPTPMap`, and `CPUMap`
(CP unital maps) take ℂ as the default class.

The majority of quantum theory revolves around `CPTPMap`s, so those are explored more
thoroughly in their file CPTP.lean.
-/

@[expose] public section


variable (dIn dOut R : Type*) (𝕜 : Type := ℂ)
variable [Semiring R] [RCLike 𝕜]

/-- Hermitian-preserving linear maps. -/
structure HPMap extends MatrixMap dIn dOut 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap

/-- Unital linear maps. -/
structure UnitalMap [DecidableEq dIn] [DecidableEq dOut]
    extends MatrixMap dIn dOut R where
  unital : MatrixMap.Unital toLinearMap

/-- Trace-preserving linear maps. -/
structure TPMap [Fintype dIn] [Fintype dOut] extends MatrixMap dIn dOut R where
  TP : MatrixMap.IsTracePreserving toLinearMap

--Mark this as [simp] so that simp lemmas requiring `IsTracePreserving` can pick it up.
--In theory this could be making "IsTracePreserving" a typeclass ... or more realistically,
--defining a `TracePreservingClass` similar to `AddHomClass`
attribute [simp] TPMap.TP

/-- Positive linear maps. -/
structure PMap [Fintype dIn] [Fintype dOut]
    extends HPMap dIn dOut 𝕜 where
  pos : MatrixMap.IsPositive toLinearMap
  HP := pos.IsHermitianPreserving

/-- Completely positive linear maps. -/
structure CPMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn]
    extends PMap dIn dOut 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
  pos := cp.IsPositive

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap [Fintype dIn] [Fintype dOut]
  extends PMap dIn dOut 𝕜, TPMap dIn dOut 𝕜

/-- Positive unital maps. These are important because they are the
  dual to `PTPMap`: they are the most general way to map *observables*. -/
structure PUMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
  extends PMap dIn dOut 𝕜, UnitalMap dIn dOut 𝕜

attribute [simp] PTPMap.TP

/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn]
  extends PTPMap dIn dOut (𝕜 := 𝕜), CPMap dIn dOut 𝕜 where

/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPMap`: they are the physically realizable ways to map *observables*. -/
structure CPUMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
  extends CPMap dIn dOut 𝕜, PUMap dIn dOut 𝕜

variable {dIn dOut R} {𝕜 : Type} [RCLike 𝕜]

/-!

## Hermitian-preserving maps

-/

--Hermitian-presering maps: continuous linear maps on HermitianMats.
namespace HPMap
variable {Λ₁ Λ₂ : HPMap dIn dOut 𝕜}
variable {CΛ₁ CΛ₂ : HPMap dIn dOut ℂ}

abbrev map (M : HPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
lemma ext (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]

/-- Two maps are equal if they agree on all Hermitian inputs. -/
theorem funext_hermitian (h : ∀ M : HermitianMat dIn ℂ, CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  ext M : 2
  have hH := h (realPart M)
  have hA := h (imaginaryPart M)
  convert congr($hH + Complex.I • $hA)
  <;> rw (occs := [1]) [← realPart_add_I_smul_imaginaryPart M, map_add, map_smul]
  <;> rfl

/-- Two maps are equal if they agree on all positive inputs. -/
theorem funext_pos [Fintype dIn] (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  classical
  open scoped HermitianMat in
  apply funext_hermitian
  intro M
  rw [← M.posPart_add_negPart]
  simp [HermitianMat.posPart_nonneg, HermitianMat.negPart_nonneg, h]

/-- Two maps are equal if they agree on all positive inputs with trace one -/
theorem funext_pos_trace [Fintype dIn]
  (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → M.trace = 1 → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  apply funext_pos
  intro M hM'
  rcases hM'.eq_or_lt with rfl | hM
  · simp
  have h_tr : 0 < M.trace := M.trace_pos hM
  have := h (M.trace⁻¹ • M) ?_ ?_
  · simp only [HermitianMat.mat_smul, LinearMap.map_smul_of_tower] at this
    convert congr(M.trace • $this)
    · rw [smul_smul]
      field_simp
      simp
    · rw [smul_smul]
      field_simp
      simp
  · apply smul_nonneg (by positivity) hM'
  · simp [field]

/-- Two maps are equal if they agree on all `MState`s. -/
theorem funext_mstate [Fintype dIn] [DecidableEq dIn] {Λ₁ Λ₂ : HPMap dIn dOut ℂ}
  (h : ∀ ρ : MState dIn, Λ₁.map ρ.m = Λ₂.map ρ.m) :
    Λ₁ = Λ₂ :=
  funext_pos_trace fun M hM_pos hM_tr ↦ h ⟨M, hM_pos, hM_tr⟩

/-- Hermitian-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (HPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective x y h := funext_hermitian fun M ↦
    by simpa using congrFun h M

lemma apply_hermitianMat_eq (Λ : HPMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = ⟨Λ.map ρ.1, Λ.HP ρ.2⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
instance [Fintype dIn] : ContinuousLinearMapClass
    (HPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq]
  map_continuous f := .subtype_mk (by fun_prop) _

end HPMap

variable [Fintype dIn] [Fintype dOut]

/-!

## Positive-preserving maps

-/

--Positive-preserving maps: continuous linear order-preserving maps on HermitianMats.
namespace PMap

@[ext]
lemma ext {Λ₁ Λ₂ : PMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PMap.mk.injEq]
  exact HPMap.ext h

lemma injective_toHPMap : (PMap.toHPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toHPMap
  coe_injective := DFunLike.coe_injective.comp injective_toHPMap

lemma apply_hermitianMat_eq (Λ : PMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = ⟨Λ.map ρ.1, Λ.HP ρ.2⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass : LinearMapClass (PMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq]

instance instContinuousOrderHomClass : ContinuousOrderHomClass (PMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPMap
  map_monotone f x y h := by
    have h1 := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact h1

/-- Positive-presering maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end PMap

namespace CPMap

def of_kraus_CPMap {κ : Type*} [Fintype κ] [DecidableEq dIn] (M : κ → Matrix dOut dIn 𝕜) : CPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.of_kraus_isCompletelyPositive M

end CPMap

/-!

## Positive trace-preserving maps

-/
--Positive trace-preserving maps:
--  * Continuous linear order-preserving maps on HermitianMats.
--  * Continuous maps on MStates.
namespace PTPMap

@[ext]
lemma ext {Λ₁ Λ₂ : PTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PTPMap.mk.injEq]
  exact PMap.ext h

lemma injective_toPMap : (PTPMap.toPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PTPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toPMap
  coe_injective := DFunLike.coe_injective.comp injective_toPMap

lemma apply_hermitianMat_eq_toPMap (Λ : PTPMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl

instance instLinearMapClass : LinearMapClass (PTPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := by simp [apply_hermitianMat_eq_toPMap]
  map_smulₛₗ f c x := by simp [apply_hermitianMat_eq_toPMap]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this

/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
noncomputable instance instMFunLike [DecidableEq dIn] [DecidableEq dOut] :
    FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.psd)) (by
      rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
      exact Λ.TP ρ)
  coe_injective x y h := injective_toPMap <| PMap.injective_toHPMap <|
    HPMap.funext_mstate fun ρ ↦ by
      have := congr($h ρ);
      rwa [MState.ext_iff, HermitianMat.ext_iff] at this

lemma apply_mstate_eq [DecidableEq dIn] [DecidableEq dOut] (Λ : PTPMap dIn dOut ℂ) (ρ : MState dIn) :
    Λ ρ = MState.mk
      (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.psd)) (by
        rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
        exact Λ.TP ρ) := rfl

instance instMContinuousMapClass [DecidableEq dIn] [DecidableEq dOut] :
    ContinuousMapClass (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  map_continuous f := by
    rw [continuous_induced_rng]
    exact (map_continuous f.toHPMap).comp MState.Continuous_HermitianMat

-- @[norm_cast]
lemma val_apply_MState [DecidableEq dIn] (M : PTPMap dIn dOut) (ρ : MState dIn) :
    (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
  rfl

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.
lemma nonemptyOut (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] [DecidableEq dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.TP M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end PTPMap

/-!

## Completely positive trace-preserving linear maps

-/

namespace CPTPMap
variable [DecidableEq dIn]

/-- Two `CPTPMap`s are equal if their `MatrixMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h

lemma injective_toPTPMap : (CPTPMap.toPTPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

-- /-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
-- instance instFunLike : FunLike (CPTPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   coe :=  DFunLike.coe ∘ toPTPMap
--   coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance instLinearMapClass : LinearMapClass (CPTPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_add f x y := by simp [instFunLike]
--   map_smulₛₗ f c x := by simp [instFunLike]

-- instance instContinuousOrderHomClass : ContinuousOrderHomClass (CPTPMap dIn dOut 𝕜)
--     (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_continuous f := ContinuousMapClass.map_continuous f.toPMap
--   map_monotone f x y h := by
    -- simpa using f.pos h

-- /-- PTP maps also preserve positivity on Hermitian matrices. -/
-- @[simp]
-- theorem pos_Hermitian (M : CPTPMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
--   simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `CPTPMap`s are functions from `MState`s to `MState`s. -/
noncomputable instance instMFunLike [DecidableEq dOut] : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe := DFunLike.coe ∘ toPTPMap
  coe_injective := DFunLike.coe_injective.comp injective_toPTPMap

lemma apply_mState_eq_toPTPMap [DecidableEq dOut] (Λ : CPTPMap dIn dOut) (ρ : MState dIn) :
    Λ ρ = Λ.toPTPMap ρ := rfl

-- @[norm_cast]
-- theorem val_apply_MState [DecidableEq dOut] (M : CPTPMap dIn dOut) (ρ : MState dIn) :
--     (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
--   rfl

@[simp]
lemma IsTracePreserving (Λ : CPTPMap dIn dOut 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP

def of_kraus_CPTPMap {κ : Type*} [Fintype κ]
  (M : κ → Matrix dOut dIn 𝕜)
  (hTP : (∑ k, (M k).conjTranspose * (M k)) = 1) : CPTPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.of_kraus_isCompletelyPositive M
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving M M hTP

end CPTPMap

namespace PUMap
variable [DecidableEq dIn] [DecidableEq dOut]

@[ext]
lemma ext {Λ₁ Λ₂ : PUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PUMap.mk.injEq]
  exact PMap.ext h

lemma injective_toPMap : (PUMap.toPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [PUMap.mk.injEq]

/-- `PUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PUMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ := Λ.toPMap
  coe_injective := (DFunLike.coe_injective (F := PMap dIn dOut ℂ)).comp injective_toPMap

lemma apply_hermitianMat_eq_toPMap (Λ : PUMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl

instance instLinearMapClass : LinearMapClass (PUMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq_toPMap]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this

instance instOneHomClass : OneHomClass (PUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_one f := HermitianMat.ext (f.unital)

/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PUMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end PUMap

namespace CPUMap
variable [DecidableEq dIn] [DecidableEq dOut]

@[ext]
lemma ext {Λ₁ Λ₂ : CPUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPUMap.mk.injEq, CPMap.mk.injEq]
  exact PMap.ext h

lemma injective_toPMap : (CPMap.toPMap ∘ CPUMap.toCPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [CPUMap.mk.injEq, CPMap.mk.injEq]

/-- `CPUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (CPUMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ := Λ.toPMap
  coe_injective := (DFunLike.coe_injective (F := PMap dIn dOut ℂ)).comp injective_toPMap

lemma apply_hermitianMat_eq_toPMap (Λ : CPUMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl

instance instLinearMapClass : LinearMapClass (CPUMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq_toPMap]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this

instance instOneHomClass : OneHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_one f := HermitianMat.ext (f.unital)

/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end CPUMap

--Tests to make sure that our `simp`s and classes are all working like we want them too

section test
variable [DecidableEq dIn] [DecidableEq dOut]

#guard_msgs in
example (M : HPMap dIn dOut ℂ) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : PTPMap dIn dOut ℂ) : (M.toHPMap (Real.pi • 1)) = Real.pi • M.toHPMap 1 := by simp

#guard_msgs in
example (M : CPTPMap dIn dOut 𝕜) (ρ : Matrix dIn dIn 𝕜) : (M.map ρ).trace = ρ.trace := by simp

#guard_msgs in
example (M : CPUMap dIn dOut ℂ) (T : HermitianMat dIn ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp

end test
