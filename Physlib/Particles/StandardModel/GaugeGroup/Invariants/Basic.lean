/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.QuadFundamental
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.FundamentalAntiFundamental
/-!
# Families of colour and isospin components and their invariants

## i. Overview

The invariant tensors of `SU(N)` are classified in `LocalGaugeData.SU.Invariants`, for
equivariant maps out of the tensors of `suTensor N`. Here those results are applied to the
Standard Model. A family `T : ι → B` of components, indexed by colour or isospin labels and moved
by the colour factor `repGauge (U, 1, 1)` or the isospin factor `repGauge (1, V, 1)` of the gauge
group, is turned into a linear map out of the tensors of `SU(3)` or `SU(2)`, and its transformation
law is exactly the equivariance of that map (A).

A law is named by how the members of the family move as vectors of `B`. Under a fundamental law
`f (T l) = ∑ a, U a l • T a`, so `T l` moves like the standard basis vector `e_l` of `ℂⁿ`; an
anti-fundamental law has `conj U` in place of `U`. The component symbols of a field are values of
an equivariant map on dual vectors, so they obey the dual of the field's law: the symbols of a
doublet or triplet field form an anti-fundamental family, and those of its conjugate a fundamental
one.

For a family with a fundamental and an anti-fundamental index the invariants reduce to the delta
contraction (B). For two fundamental or two anti-fundamental indices of `SU(2)` they reduce to the
epsilon contraction (C), and for four fundamental indices of `SU(2)` to the two epsilon pairings
(D). The contractions are written out on the components, and the maps `…Mat` record the laws a
single linear map obeys, for the reductions over the whole gauge group.

## ii. Key results

- `StandardModel.IsSU3FundamentalAntiFundamental.invariantReductionToSpan` : the colour invariants
  of a family with one fundamental and one anti-fundamental colour index.
- `StandardModel.IsSU2FundamentalAntiFundamental.invariantReductionToSpan` : its isospin twin.
- `StandardModel.IsSU2BiFundamental.invariantReductionToSpan`,
  `StandardModel.IsSU2BiAntiFundamental.invariantReductionToSpan` : two isospin indices of the
  same kind.
- `StandardModel.IsSU2QuadFundamental.reducesInvariantsTo_span_epsilonContractions` : four
  fundamental isospin indices.

## iii. Table of contents

- A. The factors of the gauge group
- B. One fundamental and one anti-fundamental index
- C. Two isospin indices of the same kind
- D. Four fundamental isospin indices

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups suTensor TensorSpecies

/-!

## A. The factors of the gauge group

-/

/-- The colour factor `SU(3)` of the gauge group. -/
def GaugeGroupI.ofSU3 : SU 3 →* GaugeGroupI := MonoidHom.inl _ _

/-- The isospin factor `SU(2)` of the gauge group. -/
def GaugeGroupI.ofSU2 : SU 2 →* GaugeGroupI := (MonoidHom.inr _ _).comp (MonoidHom.inl _ _)

@[simp]
lemma GaugeGroupI.ofSU3_apply (U : SU 3) : GaugeGroupI.ofSU3 U = (U, 1, 1) := rfl

@[simp]
lemma GaugeGroupI.ofSU2_apply (V : SU 2) : GaugeGroupI.ofSU2 V = (1, V, 1) := rfl

namespace Family

/-- A sum over pairs of indices is a double sum. -/
lemma sum_pi_two {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin n) → M) :
    ∑ d : Fin 2 → Fin n, F d = ∑ x : Fin n, ∑ y : Fin n, F ![x, y] :=
  sum_fin_two_arrow F

end Family

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repGauge : Representation ℂ GaugeGroupI B}

/-!

## B. One fundamental and one anti-fundamental index

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  fundamental and one anti-fundamental index: a factor of `U` for the first index and a factor of
  `conj U` for the second, the summed index first. -/
def IsSU3FundamentalAntiFundamentalMat (U : SU 3) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 3) → B) :
    Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * starRingEnd ℂ (U.1 (a 1) (l 1))) • T a

/-- A family `T^a{}_b` with one fundamental and one anti-fundamental colour index: its map out of
  the tensors of `SU(3)` is equivariant for the colour factor of the gauge group. -/
abbrev IsSU3FundamentalAntiFundamental (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 3) → B) : Prop :=
  (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
    (fundAntiFundMap T)

/-- The linear map `f` moves the components of `T` as `V ∈ SU(2)` moves a tensor with one
  fundamental and one anti-fundamental index. -/
def IsSU2FundamentalAntiFundamentalMat (V : SU 2) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 2) → B) :
    Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (V.1 (a 0) (l 0) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a

/-- A family `T^a{}_b` with one fundamental and one anti-fundamental isospin index: its map out
  of the tensors of `SU(2)` is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2FundamentalAntiFundamental (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 2) → B) : Prop :=
  (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
    (fundAntiFundMap T)

namespace IsSU3FundamentalAntiFundamental

variable {T : (Fin 2 → Fin 3) → B}

/-- A family obeying the law for every colour rotation is such a family. -/
lemma of_law (hT : ∀ U : SU 3, IsSU3FundamentalAntiFundamentalMat U (repGauge (U, 1, 1)) T) :
    IsSU3FundamentalAntiFundamental B repGauge T :=
  isEquivariant_fundAntiFundMap T hT

/-- A finite sum of such families is such a family. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 3) → B}
    (hT : ∀ i, IsSU3FundamentalAntiFundamental B repGauge (T i)) :
    IsSU3FundamentalAntiFundamental B repGauge (fun l => ∑ i, T i l) := by
  rw [IsSU3FundamentalAntiFundamental, fundAntiFundMap, familyMap_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

/-- The delta contraction `∑ a, T ![a, a]`. -/
def deltaContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

lemma deltaContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sum_mem fun _ _ => Submodule.subset_span ⟨_, rfl⟩

/-- Any map moving the components by an element of `SU(3)` fixes the delta contraction. -/
lemma map_deltaContraction {U : SU 3} {f : B →ₗ[ℂ] B}
    (hf : IsSU3FundamentalAntiFundamentalMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction, ← fundAntiFundMap_delta, fundAntiFundMap_smul_of_law T U hf,
    delta_invariant]

/-- The delta contraction is colour invariant. -/
lemma repGauge_deltaContraction (hT : IsSU3FundamentalAntiFundamental B repGauge T)
    (U : SU 3) : repGauge (U, 1, 1) (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction, ← fundAntiFundMap_delta]
  exact hT.rep_map_of_invariant delta_invariant U

/-- The colour invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan (hT : IsSU3FundamentalAntiFundamental B repGauge T) :
    InvariantReductionToSpan (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToDelta hT

end IsSU3FundamentalAntiFundamental

namespace IsSU2FundamentalAntiFundamental

variable {T : (Fin 2 → Fin 2) → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ V : SU 2, IsSU2FundamentalAntiFundamentalMat V (repGauge (1, V, 1)) T) :
    IsSU2FundamentalAntiFundamental B repGauge T :=
  isEquivariant_fundAntiFundMap T hT

/-- A finite sum of such families is such a family. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2FundamentalAntiFundamental B repGauge (T i)) :
    IsSU2FundamentalAntiFundamental B repGauge (fun l => ∑ i, T i l) := by
  rw [IsSU2FundamentalAntiFundamental, fundAntiFundMap, familyMap_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

/-- The delta contraction `T ![0, 0] + T ![1, 1]`. -/
def deltaContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 0] + T ![1, 1]

omit [Module ℂ B] in
lemma deltaContraction_eq_sum (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T = ∑ a : Fin 2, T ![a, a] := by
  rw [deltaContraction, Fin.sum_univ_two]

lemma deltaContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T ∈ Submodule.span ℂ (Set.range T) :=
  add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- Any map moving the components by an element of `SU(2)` fixes the delta contraction. -/
lemma map_deltaContraction {V : SU 2} {f : B →ₗ[ℂ] B}
    (hf : IsSU2FundamentalAntiFundamentalMat V f T) :
    f (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction_eq_sum, ← fundAntiFundMap_delta, fundAntiFundMap_smul_of_law T V hf,
    delta_invariant]

/-- The delta contraction is isospin invariant. -/
lemma repGauge_deltaContraction (hT : IsSU2FundamentalAntiFundamental B repGauge T)
    (V : SU 2) : repGauge (1, V, 1) (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction_eq_sum, ← fundAntiFundMap_delta]
  exact hT.rep_map_of_invariant delta_invariant V

/-- The isospin invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan (hT : IsSU2FundamentalAntiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (isAdjointClosed 2 _) (delta 2) delta_invariant
    exists_eq_smul_delta_of_invariant (range_familyMap _ T) (deltaContraction T)
    (by rw [fundAntiFundMap_delta, deltaContraction_eq_sum])

/-- The isospin invariants of the component span reduce to the line through the delta
  contraction. -/
lemma reducesInvariantsTo_span_deltaContraction
    (hT : IsSU2FundamentalAntiFundamental B repGauge T) :
    ReducesInvariantsTo (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ deltaContraction T) :=
  (invariantReductionToSpan hT).reducesInvariantsTo

end IsSU2FundamentalAntiFundamental

/-!

## C. Two isospin indices of the same kind

-/

/-- The linear map `f` moves the components of `T` as `V ∈ SU(2)` moves a tensor with two
  fundamental indices: one factor of `V` per index. -/
def IsSU2BiFundamentalMat (V : SU 2) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2, f (T l) = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, V.1 (a i) (l i)) • T a

/-- The linear map `f` moves the components of `T` as `V ∈ SU(2)` moves a tensor with two
  anti-fundamental indices: one factor of `conj V` per index. -/
def IsSU2BiAntiFundamentalMat (V : SU 2) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2, f (T l) = ∑ a : Fin 2 → Fin 2,
    (starRingEnd ℂ (V.1 (a 0) (l 0)) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a

/-- A family `T^{ab}` with two fundamental isospin indices: its map out of the tensors of `SU(2)`
  is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2BiFundamental (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 2) → B) : Prop :=
  (suTensor 2).IsEquivariant (fun _ => .fund) (repGauge.comp GaugeGroupI.ofSU2) (fundMap T)

/-- A family `T_{ab}` with two anti-fundamental isospin indices: its map out of the tensors of
  `SU(2)` is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2BiAntiFundamental (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 2) → B) : Prop :=
  (suTensor 2).IsEquivariant (fun _ => .antiFund) (repGauge.comp GaugeGroupI.ofSU2)
    (antiFundMap T)

namespace IsSU2BiFundamental

variable {T : (Fin 2 → Fin 2) → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ V : SU 2, IsSU2BiFundamentalMat V (repGauge (1, V, 1)) T) :
    IsSU2BiFundamental B repGauge T :=
  isEquivariant_fundMap T hT

/-- A finite sum of such families is such a family. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2BiFundamental B repGauge (T i)) :
    IsSU2BiFundamental B repGauge (fun l => ∑ i, T i l) := by
  rw [IsSU2BiFundamental, fundMap, familyMap_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

/-- The epsilon contraction `T ![0, 1] - T ![1, 0]`. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

lemma epsilonContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- Any map moving the components by an element of `SU(2)` fixes the epsilon contraction. -/
lemma map_epsilonContraction {V : SU 2} {f : B →ₗ[ℂ] B} (hf : IsSU2BiFundamentalMat V f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  rw [epsilonContraction, ← fundMap_epsilonFund, fundMap_smul_of_law T V hf,
    epsilonFund_invariant]

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction (hT : IsSU2BiFundamental B repGauge T) (V : SU 2) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T := by
  rw [epsilonContraction, ← fundMap_epsilonFund]
  exact hT.rep_map_of_invariant epsilonFund_invariant V

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan (hT : IsSU2BiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToEpsilonFund hT

end IsSU2BiFundamental

namespace IsSU2BiAntiFundamental

variable {T : (Fin 2 → Fin 2) → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ V : SU 2, IsSU2BiAntiFundamentalMat V (repGauge (1, V, 1)) T) :
    IsSU2BiAntiFundamental B repGauge T :=
  isEquivariant_antiFundMap T fun V l => (hT V l).trans <|
    Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]

/-- A finite sum of such families is such a family. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2BiAntiFundamental B repGauge (T i)) :
    IsSU2BiAntiFundamental B repGauge (fun l => ∑ i, T i l) := by
  rw [IsSU2BiAntiFundamental, antiFundMap, familyMap_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

/-- Any map moving the components by an element of `SU(2)` in the anti-fundamental fixes the
  epsilon contraction. -/
lemma map_epsilonContraction {V : SU 2} {f : B →ₗ[ℂ] B} (hf : IsSU2BiAntiFundamentalMat V f T) :
    f (IsSU2BiFundamental.epsilonContraction T) = IsSU2BiFundamental.epsilonContraction T := by
  rw [IsSU2BiFundamental.epsilonContraction, ← antiFundMap_epsilonAntiFund,
    antiFundMap_smul_of_law T V (fun l => (hf l).trans <|
      Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]), epsilonAntiFund_invariant]

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction (hT : IsSU2BiAntiFundamental B repGauge T) (V : SU 2) :
    repGauge (1, V, 1) (IsSU2BiFundamental.epsilonContraction T)
      = IsSU2BiFundamental.epsilonContraction T := by
  rw [IsSU2BiFundamental.epsilonContraction, ← antiFundMap_epsilonAntiFund]
  exact hT.rep_map_of_invariant epsilonAntiFund_invariant V

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan (hT : IsSU2BiAntiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToEpsilonAntiFund hT

end IsSU2BiAntiFundamental

/-!

## D. Four fundamental isospin indices

-/

/-- The linear map `f` moves the components of `T` as `V ∈ SU(2)` moves a tensor with four
  fundamental indices: one factor of `V` per index. -/
def IsSU2QuadFundamentalMat (V : SU 2) (f : B →ₗ[ℂ] B) (T : (Fin 4 → Fin 2) → B) : Prop :=
  ∀ l : Fin 4 → Fin 2, f (T l) = ∑ a : Fin 4 → Fin 2, (∏ i : Fin 4, V.1 (a i) (l i)) • T a

/-- A family `T^{abcd}` with four fundamental isospin indices: its map out of the tensors of
  `SU(2)` is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2QuadFundamental (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 4 → Fin 2) → B) : Prop :=
  (suTensor 2).IsEquivariant (fun _ => .fund) (repGauge.comp GaugeGroupI.ofSU2) (fundMap T)

namespace IsSU2QuadFundamental

variable {T : (Fin 4 → Fin 2) → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ V : SU 2, IsSU2QuadFundamentalMat V (repGauge (1, V, 1)) T) :
    IsSU2QuadFundamental B repGauge T :=
  isEquivariant_fundMap T hT

/-- A sum over families of four fundamental indices is a fourfold sum. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 2) → M) :
    ∑ d : Fin 4 → Fin 2, F d
      = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ w : Fin 2, F ![x, y, z, w] :=
  sum_fin_four_arrow F

/-- The contraction pairing the first index with the second and the third with the
  fourth. -/
def epsilonContraction₁₂ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 1, 0, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 0, 1, 0]

/-- The contraction pairing the first index with the third and the second with the
  fourth. -/
def epsilonContraction₁₃ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 0, 1, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 1, 0, 0]

/-- The isospin invariants of the component span reduce to the span of the two epsilon
  contractions. -/
lemma reducesInvariantsTo_span_epsilonContractions (hT : IsSU2QuadFundamental B repGauge T) :
    ReducesInvariantsTo (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T))
      (Submodule.span ℂ {epsilonContraction₁₂ T, epsilonContraction₁₃ T}) :=
  suTensor.reducesInvariantsTo_span_epsilonContractions hT

end IsSU2QuadFundamental

end StandardModel
