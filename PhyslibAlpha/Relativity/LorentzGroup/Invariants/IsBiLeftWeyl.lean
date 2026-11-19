/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.AdjointClosed
/-!
# Lorentz invariants of two Weyl indices of the same kind

Up to scale, the `ε` metric is the only Lorentz invariant of two Weyl indices of the same kind.

## i. Overview

Let `k` be one of the four Weyl colours and `f : ℂT[k, k] →ₗ[ℂ] B` a Lorentz-equivariant linear
map. Every Lorentz invariant in the range of `f` is a multiple of `f (metricTensor k)`, the
image of the `ε` metric of that colour, the shape of a Majorana or Dirac mass term. That is
`exists_smul_map_metricTensor_add_of_invariant`, stated modulo a
Lorentz-stable submodule `S`, and packaged for the reductions of the Standard Model as
`invariantReductionToMetricTensor`. The families with two left-handed,
two right-handed, two dual left-handed and two dual right-handed indices are `IsBiLeftWeyl`,
`IsBiRightWeyl`, `IsBiDualLeftWeyl` and `IsBiDualRightWeyl` (A).

By `TensorSpecies.IsEquivariant.invariantReductionToSpan` it is enough to show that the invariant
tensors of `ℂT[k, k]` are the multiples of `metricTensor k` (B). A tensor with two indices is
`fromPairT` of an element of the tensor square of the Weyl representation of colour `k`, and the
invariants of that tensor square are the line through the metric,
`Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal` and its three siblings.

## ii. Key results

- `IsBiLeftWeyl` : a family with two left-handed Weyl indices `T^{α₁ α₂}`: an equivariant linear map
  out of `ℂT[.upL, .upL]`
- `IsBiRightWeyl` : a family with two right-handed Weyl indices `T^{α̇₁ α̇₂}`: an equivariant linear
  map out of `ℂT[.upR, .upR]`
- `IsBiDualLeftWeyl` : a family with two dual left-handed Weyl indices `T_{α₁ α₂}`: an equivariant
  linear map out of `ℂT[.downL, .downL]`
- `IsBiDualRightWeyl` : a family with two dual right-handed Weyl indices `T_{α̇₁ α̇₂}`: an
  equivariant linear map out of `ℂT[.downR, .downR]`
- `invariantReductionToMetricTensor` : the reduction of the invariants of the range of `f` to the
  span of `f (metricTensor k)`
- `exists_smul_map_metricTensor_add_of_invariant` : for a Weyl colour `k` and an equivariant map `f`
  out of `ℂT[k, k]`, every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable
  submodule, is a multiple of the image `f (metricTensor k)` of the metric plus an element of `S`

## iii. Table of contents

- A. Families with two Weyl indices of the same kind
- B. The invariant tensors with two Weyl indices of the same kind
- C. The classification of the invariants
- D. Maps from components

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Families with two Weyl indices of the same kind

-/

/-- A family with two left-handed Weyl indices `T^{α₁ α₂}`, an equivariant linear map out of
  `ℂT[.upL, .upL]`. -/
abbrev IsBiLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upL, .upL] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upL, .upL] repLorentz f

/-- A family with two right-handed Weyl indices `T^{α̇₁ α̇₂}`, an equivariant linear map out of
  `ℂT[.upR, .upR]`. -/
abbrev IsBiRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upR, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upR, .upR] repLorentz f

/-- A family with two dual left-handed Weyl indices `T_{α₁ α₂}`, an equivariant linear map out
  of `ℂT[.downL, .downL]`. -/
abbrev IsBiDualLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downL, .downL] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentz f

/-- A family with two dual right-handed Weyl indices `T_{α̇₁ α̇₂}`, an equivariant linear map
  out of `ℂT[.downR, .downR]`. -/
abbrev IsBiDualRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downR, .downR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downR, .downR] repLorentz f

/-!

## B. The invariant tensors with two Weyl indices of the same kind

-/

section InvariantTensors

variable {k : complexLorentzTensor.Color}

/-- The invariant tensors with two Weyl indices of the same colour are the multiples of the
  metric of that colour. A tensor with two indices comes from the tensor square of the Weyl
  representation, whose invariants are the line through the metric. -/
lemma exists_eq_smul_metricTensor_of_invariant
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR) (t : ℂT[k, k])
    (ht : ∀ g : SL(2,ℂ), g • t = t) : ∃ a : ℂ, t = a • metricTensor k := by
  rcases hk with rfl | rfl | rfl | rfl
  · obtain ⟨a, ha⟩ := Tensor.exists_eq_smul_fromPairT_of_invariant (S := complexLorentzTensor)
      (c1 := .upL) (c2 := .upL) Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal ht
    exact ⟨a, ha.trans (congrArg (a • fromPairT ·) Fermion.LeftHandedWeyl.metric_apply_one.symm)⟩
  · obtain ⟨a, ha⟩ := Tensor.exists_eq_smul_fromPairT_of_invariant (S := complexLorentzTensor)
      (c1 := .downL) (c2 := .downL) Fermion.DualLeftHandedWeyl.invariants_tprod_eq_span_metricVal ht
    exact ⟨a, ha.trans
      (congrArg (a • fromPairT ·) Fermion.DualLeftHandedWeyl.metric_apply_one.symm)⟩
  · obtain ⟨a, ha⟩ := Tensor.exists_eq_smul_fromPairT_of_invariant (S := complexLorentzTensor)
      (c1 := .upR) (c2 := .upR) Fermion.RightHandedWeyl.invariants_tprod_eq_span_metricVal ht
    exact ⟨a, ha.trans (congrArg (a • fromPairT ·) Fermion.RightHandedWeyl.metric_apply_one.symm)⟩
  · obtain ⟨a, ha⟩ := Tensor.exists_eq_smul_fromPairT_of_invariant (S := complexLorentzTensor)
      (c1 := .downR) (c2 := .downR)
      Fermion.DualRightHandedWeyl.invariants_tprod_eq_span_metricVal ht
    exact ⟨a, ha.trans
      (congrArg (a • fromPairT ·) Fermion.DualRightHandedWeyl.metric_apply_one.symm)⟩

end InvariantTensors

/-!

## C. The classification of the invariants

-/

section Reduction

variable {k : complexLorentzTensor.Color} {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[k, k] →ₗ[ℂ] B}

/-- For a Weyl colour `k` and an equivariant map `f` out of `ℂT[k, k]`, the Lorentz invariants
  of the range of `f` reduce to the span of the image `f (metricTensor k)` of the metric. -/
noncomputable def invariantReductionToMetricTensor
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR)
    (hf : complexLorentzTensor.IsEquivariant ![k, k] repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (complexLorentzTensor.isAdjointClosed _)
    (metricTensor k) (fun g => metricTensor_invariant g)
    (exists_eq_smul_metricTensor_of_invariant hk)

/-- For a Weyl colour `k` and an equivariant map `f` out of `ℂT[k, k]`, every Lorentz invariant
  of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a multiple of the image
  `f (metricTensor k)` of the metric plus an element of `S`. -/
lemma exists_smul_map_metricTensor_add_of_invariant
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR)
    (hf : complexLorentzTensor.IsEquivariant ![k, k] repLorentz f) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f (metricTensor k) + y :=
  (invariantReductionToMetricTensor hk hf).reduce S hS x hx hinv

end Reduction

/-- The Lorentz invariants of the range of a family with two left-handed Weyl indices reduce to
  the span of the image of `εL`. -/
noncomputable def IsBiLeftWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.upL, .upL] →ₗ[ℂ] B}
    (hf : IsBiLeftWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inl rfl) hf

/-- The Lorentz invariants of the range of a family with two right-handed Weyl indices reduce to
  the span of the image of `εR`. -/
noncomputable def IsBiRightWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.upR, .upR] →ₗ[ℂ] B}
    (hf : IsBiRightWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inr (Or.inl rfl))) hf

/-- The Lorentz invariants of the range of a family with two dual left-handed Weyl indices
  reduce to the span of the image of `εL'`. -/
noncomputable def IsBiDualLeftWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.downL, .downL] →ₗ[ℂ] B}
    (hf : IsBiDualLeftWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inl rfl)) hf

/-- The Lorentz invariants of the range of a family with two dual right-handed Weyl indices
  reduce to the span of the image of `εR'`. -/
noncomputable def IsBiDualRightWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.downR, .downR] →ₗ[ℂ] B}
    (hf : IsBiDualRightWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inr (Or.inr rfl))) hf

/-!

## D. Maps from components

A family of vectors `T a b` indexed by two basis indices is the linear map
`ofPairComponents T` sending `e_a ⊗ e_b` to `T a b`, and it is equivariant when the vectors are
moved as the basis tensors are.

-/

section PairComponents

variable {k k' : complexLorentzTensor.Color} {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The linear map out of `ℂT[k, k']` sending the basis tensor `e_a ⊗ e_b` to `T a b`. -/
noncomputable def ofPairComponents (T : basisIdx k → basisIdx k' → B) :
    ℂT[k, k'] →ₗ[ℂ] B :=
  (Tensor.basis ![k, k']).constr ℂ fun φ => T (φ 0) (φ 1)

/-- The range of `ofPairComponents T` is the span of the vectors `T a b`. -/
lemma range_ofPairComponents (T : basisIdx k → basisIdx k' → B) :
    LinearMap.range (ofPairComponents T)
      = Submodule.span ℂ (Set.range fun m : basisIdx k × basisIdx k' => T m.1 m.2) := by
  rw [ofPairComponents, Module.Basis.constr_range]
  exact congrArg _ ((piFinTwoEquiv fun j : Fin 2 => basisIdx (![k, k'] j)).surjective.range_comp
    fun m => T m.1 m.2)

/-- The image of `ofPairComponents T` lies in every submodule containing the vectors
  `T a b`. -/
lemma ofPairComponents_mem (T : basisIdx k → basisIdx k' → B) {M : Submodule ℂ B}
    (hT : ∀ a b, T a b ∈ M) (t : ℂT[k, k']) : ofPairComponents T t ∈ M := by
  have h : LinearMap.range (ofPairComponents T) ≤ M := by
    rw [range_ofPairComponents, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hT m.1 m.2
  exact h (LinearMap.mem_range_self _ t)

/-- A linear map applied after `ofPairComponents T` is `ofPairComponents` of its values on the
  components. -/
lemma map_ofPairComponents {B' : Type*} [AddCommGroup B'] [Module ℂ B'] (σ : B →ₗ[ℂ] B')
    (T : basisIdx k → basisIdx k' → B) (t : ℂT[k, k']) :
    σ (ofPairComponents T t) = ofPairComponents (fun a b => σ (T a b)) t :=
  LinearMap.congr_fun (show σ ∘ₗ ofPairComponents T = ofPairComponents (fun a b => σ (T a b)) from
    (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by
      simp [ofPairComponents]) t

/-- `ofPairComponents` of a sum of families is the sum of the maps. -/
lemma ofPairComponents_sum {ι : Type*} (s : Finset ι)
    (T : ι → basisIdx k → basisIdx k' → B) :
    ofPairComponents (fun a b => ∑ i ∈ s, T i a b) = ∑ i ∈ s, ofPairComponents (T i) :=
  (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by
    simp [ofPairComponents, LinearMap.sum_apply]

/-- `ofPairComponents` of a difference of families is the difference of the maps. -/
lemma ofPairComponents_sub (T T' : basisIdx k → basisIdx k' → B) :
    ofPairComponents (fun a b => T a b - T' a b) = ofPairComponents T - ofPairComponents T' :=
  (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by simp [ofPairComponents]

/-- `ofPairComponents T` is equivariant when each index of `T a b` is moved by the matrix of `g`
  in its colour, the summed index first in each factor. -/
lemma isEquivariant_ofPairComponents {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : basisIdx k → basisIdx k' → B)
    (hT : ∀ (g : SL(2,ℂ)) a b, repLorentz g (T a b)
      = ∑ x, ∑ y, (LinearMap.toMatrix (complexLorentzTensor.basis k)
          (complexLorentzTensor.basis k) (complexLorentzTensor.rep k g) x a *
        LinearMap.toMatrix (complexLorentzTensor.basis k') (complexLorentzTensor.basis k')
          (complexLorentzTensor.rep k' g) y b) • T x y) :
    complexLorentzTensor.IsEquivariant ![k, k'] repLorentz (ofPairComponents T) :=
  isEquivariant_constr _ fun g φ => (hT g (φ 0) (φ 1)).trans <| by
    rw [← (piFinTwoEquiv fun j : Fin 2 => basisIdx (![k, k'] j)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.prod_univ_two]
    rfl

end PairComponents

end Lorentz
