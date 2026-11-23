/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.LeviCivitaPairing
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.Delta
/-!
# Families of colour and isospin components and their invariants

Families of components moved by the colour or isospin factor, and the contractions their invariants
reduce to.

## i. Overview

The invariant tensors of `SU(N)` are classified in `GlobalGaugeGroup.SU.Invariants`,
for equivariant maps out of the tensors of `suTensor N`. Here those results are applied to the
Standard Model. A family `T : ι → B` of components, indexed by colour or isospin labels and moved by
the colour factor `repGauge (U, 1, 1)` or the isospin factor `repGauge (1, V, 1)` of the gauge
group, is turned into the linear map `liftComponents` out of the tensors of `SU(3)` or `SU(2)` with
an explicit list of colours, and its transformation law is exactly the equivariance of that map
for the restriction of `repGauge` along the factor (A).

A law is named by how the members of the family move as vectors of `B`. Under a fundamental law
`f (T l) = ∑ a, U a l • T a`, so `T l` moves like the standard basis vector `e_l` of `ℂⁿ`; an
anti-fundamental law has `conj U` in place of `U`. The component symbols of a field are values of
an equivariant map on dual vectors, so they obey the dual of the field's law. The symbols of a
doublet or triplet field form an anti-fundamental family, and those of its conjugate a fundamental
one.

For a family with a fundamental and an anti-fundamental index the invariants reduce to the delta
contraction (B). For two fundamental or two anti-fundamental indices of `SU(2)` they reduce to the
epsilon contraction (C), and for four fundamental indices of `SU(2)` to the two epsilon pairings
(D). The contractions are written out on the components, and the lemmas `map_…Contraction` take
the law a single linear map obeys, for the reductions over the whole gauge group. The lemmas of
each family live in a namespace named after its representation, `ColourFundAntiFund`,
`IsospinFundAntiFund`, `IsospinFundFund`, `IsospinAntiFundAntiFund` and `IsospinQuadFund`.

## ii. Key results

- `StandardModel.ColourFundAntiFund.invariantReductionToSpan` : the colour invariants of a family
  with one fundamental and one anti-fundamental colour index.
- `StandardModel.IsospinFundAntiFund.invariantReductionToSpan` : its isospin twin.
- `StandardModel.IsospinFundFund.invariantReductionToSpan`,
  `StandardModel.IsospinAntiFundAntiFund.invariantReductionToSpan` : two isospin indices of the
  same kind.
- `StandardModel.IsospinQuadFund.reducesInvariantsTo_span_epsilonContractions` : four fundamental
  isospin indices.

## iii. Table of contents

- A. The factors of the gauge group
- B. One fundamental and one anti-fundamental index
- C. Two isospin indices of the same kind
- D. Four fundamental isospin indices

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups suTensor TensorSpecies

/-!

## A. The factors of the gauge group

The colour and isospin factors as homomorphisms into `GaugeGroupI`, along which the
representation of the gauge group is restricted.

-/

/-- The colour factor `SU(3)` of the gauge group. -/
def GaugeGroupI.ofSU3 : SU 3 →* GaugeGroupI := MonoidHom.inl _ _

/-- The isospin factor `SU(2)` of the gauge group. -/
def GaugeGroupI.ofSU2 : SU 2 →* GaugeGroupI := (MonoidHom.inr _ _).comp (MonoidHom.inl _ _)

/-- The colour factor sends `U` to `(U, 1, 1)`. -/
@[simp]
lemma GaugeGroupI.ofSU3_apply (U : SU 3) : GaugeGroupI.ofSU3 U = (U, 1, 1) := rfl

/-- The isospin factor sends `V` to `(1, V, 1)`. -/
@[simp]
lemma GaugeGroupI.ofSU2_apply (V : SU 2) : GaugeGroupI.ofSU2 V = (1, V, 1) := rfl

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repGauge : Representation ℂ GaugeGroupI B}

/-!

## B. One fundamental and one anti-fundamental index

The invariants reduce to the delta contraction, for colour and for isospin.

-/

namespace ColourFundAntiFund

variable {T : (Fin 2 → Fin 3) → B}

/-- A family `T^a{}_b` with one fundamental and one anti-fundamental colour index: when every
  colour rotation `U` moves its members by a factor of `U` for the first index and of `conj U`
  for the second, the summed index first, its map out of the tensors of `SU(3)` is equivariant
  for the colour factor of the gauge group. -/
lemma of_law (hT : ∀ (U : SU 3) (l : Fin 2 → Fin 3), repGauge (U, 1, 1) (T l)
    = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * starRingEnd ℂ (U.1 (a 1) (l 1))) • T a) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ fundAntiFundIdx)) :=
  isEquivariant_liftComponents_fundAntiFund T hT

/-- The map of a finite sum of families is equivariant when the map of each family is. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 3) → B}
    (hT : ∀ i, (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T i ∘ fundAntiFundIdx))) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun l => ∑ i, T i l) ∘ fundAntiFundIdx)) :=
  isEquivariant_liftComponents_sum _ fun i _ => hT i

/-- The delta contraction `∑ a, T ![a, a]`. -/
def deltaContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sum_mem fun _ _ => Submodule.subset_span ⟨_, rfl⟩

/-- Any map moving the components by an element of `SU(3)` fixes the delta contraction. -/
lemma map_deltaContraction {U : SU 3} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * starRingEnd ℂ (U.1 (a 1) (l 1))) • T a) :
    f (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction, ← liftComponents_delta, liftComponents_fundAntiFund_smul_of_law T U hf,
    delta_invariant]

/-- The delta contraction is colour invariant. -/
lemma repGauge_deltaContraction
    (hT : (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ fundAntiFundIdx)))
    (U : SU 3) : repGauge (U, 1, 1) (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction, ← liftComponents_delta]
  exact hT.rep_map_of_invariant delta_invariant U

/-- The colour invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan
    (hT : (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ fundAntiFundIdx))) :
    InvariantReductionToSpan (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToDelta hT

end ColourFundAntiFund

namespace IsospinFundAntiFund

variable {T : (Fin 2 → Fin 2) → B}

/-- A family `T^a{}_b` with one fundamental and one anti-fundamental isospin index: when every
  isospin rotation moves its members as the components of such a tensor, its map out of the
  tensors of `SU(2)` is equivariant for the isospin factor of the gauge group. -/
lemma of_law (hT : ∀ (V : SU 2) (l : Fin 2 → Fin 2), repGauge (1, V, 1) (T l)
    = ∑ a : Fin 2 → Fin 2, (V.1 (a 0) (l 0) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ fundAntiFundIdx)) :=
  isEquivariant_liftComponents_fundAntiFund T hT

/-- The map of a finite sum of families is equivariant when the map of each family is. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T i ∘ fundAntiFundIdx))) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l => ∑ i, T i l) ∘ fundAntiFundIdx)) :=
  isEquivariant_liftComponents_sum _ fun i _ => hT i

/-- The delta contraction `T ![0, 0] + T ![1, 1]`. -/
def deltaContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 0] + T ![1, 1]

omit [Module ℂ B] in
/-- The delta contraction is the trace `∑ a, T ![a, a]`. -/
lemma deltaContraction_eq_sum (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T = ∑ a : Fin 2, T ![a, a] := by
  rw [deltaContraction, Fin.sum_univ_two]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T ∈ Submodule.span ℂ (Set.range T) :=
  add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- Any map moving the components by an element of `SU(2)` fixes the delta contraction. -/
lemma map_deltaContraction {V : SU 2} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (V.1 (a 0) (l 0) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a) :
    f (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction_eq_sum, ← liftComponents_delta,
    liftComponents_fundAntiFund_smul_of_law T V hf, delta_invariant]

/-- The delta contraction is isospin invariant. -/
lemma repGauge_deltaContraction
    (hT : (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ fundAntiFundIdx)))
    (V : SU 2) : repGauge (1, V, 1) (deltaContraction T) = deltaContraction T := by
  rw [deltaContraction_eq_sum, ← liftComponents_delta]
  exact hT.rep_map_of_invariant delta_invariant V

/-- The isospin invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan
    (hT : (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ fundAntiFundIdx))) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (hasReynolds 2 _) invariants_fund_antiFund_eq_span_delta
    (range_liftComponents_comp _ T) (deltaContraction T)
    (by rw [liftComponents_delta, deltaContraction_eq_sum])

/-- The isospin invariants of the component span reduce to the line through the delta
  contraction. -/
lemma reducesInvariantsTo_span_deltaContraction
    (hT : (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ fundAntiFundIdx))) :
    ReducesInvariantsTo (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ deltaContraction T) :=
  (invariantReductionToSpan hT).reducesInvariantsTo

end IsospinFundAntiFund

/-!

## C. Two isospin indices of the same kind

Two fundamental or two anti-fundamental isospin indices have the epsilon contraction alone as
invariant.

-/

namespace IsospinFundFund

variable {T : (Fin 2 → Fin 2) → B}

/-- A family `T^{ab}` with two fundamental isospin indices: when every isospin rotation `V` moves
  its members by one factor of `V` per index, its map out of the tensors of `SU(2)` is equivariant
  for the isospin factor of the gauge group. -/
lemma of_law (hT : ∀ (V : SU 2) (l : Fin 2 → Fin 2), repGauge (1, V, 1) (T l)
    = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, V.1 (a i) (l i)) • T a) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T) :=
  isEquivariant_liftComponents_fund T hT

/-- The map of a finite sum of families is equivariant when the map of each family is. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund)
      (repGauge.comp GaugeGroupI.ofSU2) (liftComponents (T i))) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents fun l => ∑ i, T i l) :=
  isEquivariant_liftComponents_sum _ fun i _ => hT i

/-- The epsilon contraction `T ![0, 1] - T ![1, 0]`. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

/-- Any map moving the components by an element of `SU(2)` fixes the epsilon contraction. -/
lemma map_epsilonContraction {V : SU 2} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, V.1 (a i) (l i)) • T a) :
    f (epsilonContraction T) = epsilonContraction T := by
  rw [epsilonContraction, ← liftComponents_epsilonFund, liftComponents_fund_smul_of_law T V hf,
    epsilonFund_invariant]

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction
    (hT : (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T)) (V : SU 2) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T := by
  rw [epsilonContraction, ← liftComponents_epsilonFund]
  exact hT.rep_map_of_invariant epsilonFund_invariant V

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan
    (hT : (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T)) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToEpsilonFund hT

end IsospinFundFund

namespace IsospinAntiFundAntiFund

variable {T : (Fin 2 → Fin 2) → B}

/-- A family `T_{ab}` with two anti-fundamental isospin indices: when every isospin rotation `V`
  moves its members by one factor of `conj V` per index, its map out of the tensors of `SU(2)` is
  equivariant for the isospin factor of the gauge group. -/
lemma of_law (hT : ∀ (V : SU 2) (l : Fin 2 → Fin 2), repGauge (1, V, 1) (T l)
    = ∑ a : Fin 2 → Fin 2,
        (starRingEnd ℂ (V.1 (a 0) (l 0)) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .antiFund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T) :=
  isEquivariant_liftComponents_antiFund T fun V l => (hT V l).trans <|
    Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]

/-- The map of a finite sum of families is equivariant when the map of each family is. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, (suTensor 2).IsEquivariant (fun _ : Fin 2 => .antiFund)
      (repGauge.comp GaugeGroupI.ofSU2) (liftComponents (T i))) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .antiFund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents fun l => ∑ i, T i l) :=
  isEquivariant_liftComponents_sum _ fun i _ => hT i

/-- Any map moving the components by an element of `SU(2)` in the anti-fundamental fixes the
  epsilon contraction. -/
lemma map_epsilonContraction {V : SU 2} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2,
        (starRingEnd ℂ (V.1 (a 0) (l 0)) * starRingEnd ℂ (V.1 (a 1) (l 1))) • T a) :
    f (IsospinFundFund.epsilonContraction T) = IsospinFundFund.epsilonContraction T := by
  rw [IsospinFundFund.epsilonContraction, ← liftComponents_epsilonAntiFund,
    liftComponents_antiFund_smul_of_law T V (fun l => (hf l).trans <|
      Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]), epsilonAntiFund_invariant]

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction
    (hT : (suTensor 2).IsEquivariant (fun _ : Fin 2 => .antiFund)
      (repGauge.comp GaugeGroupI.ofSU2) (liftComponents T)) (V : SU 2) :
    repGauge (1, V, 1) (IsospinFundFund.epsilonContraction T)
      = IsospinFundFund.epsilonContraction T := by
  rw [IsospinFundFund.epsilonContraction, ← liftComponents_epsilonAntiFund]
  exact hT.rep_map_of_invariant epsilonAntiFund_invariant V

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan
    (hT : (suTensor 2).IsEquivariant (fun _ : Fin 2 => .antiFund)
      (repGauge.comp GaugeGroupI.ofSU2) (liftComponents T)) :
    InvariantReductionToSpan (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) :=
  invariantReductionToEpsilonAntiFund hT

end IsospinAntiFundAntiFund

/-!

## D. Four fundamental isospin indices

The invariants reduce to the two ways of pairing the four indices by epsilon.

-/

namespace IsospinQuadFund

variable {T : (Fin 4 → Fin 2) → B}

/-- A family `T^{abcd}` with four fundamental isospin indices: when every isospin rotation `V`
  moves its members by one factor of `V` per index, its map out of the tensors of `SU(2)` is
  equivariant for the isospin factor of the gauge group. -/
lemma of_law (hT : ∀ (V : SU 2) (l : Fin 4 → Fin 2), repGauge (1, V, 1) (T l)
    = ∑ a : Fin 4 → Fin 2, (∏ i : Fin 4, V.1 (a i) (l i)) • T a) :
    (suTensor 2).IsEquivariant (fun _ : Fin 4 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T) :=
  isEquivariant_liftComponents_fund T hT

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
lemma reducesInvariantsTo_span_epsilonContractions
    (hT : (suTensor 2).IsEquivariant (fun _ : Fin 4 => .fund) (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents T)) :
    ReducesInvariantsTo (fun V : SU 2 => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T))
      (Submodule.span ℂ {epsilonContraction₁₂ T, epsilonContraction₁₃ T}) :=
  suTensor.reducesInvariantsTo_span_epsilonContractions hT

end IsospinQuadFund

end StandardModel
