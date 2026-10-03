/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.AdjointMatrix
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.Adjoint
/-!
# Families of adjoint components and their invariants

## i. Overview

The Standard Model labels the adjoint indices of `su(3)` by the eight Gell-Mann matrices
`gellMannMatrix`, and those of `su(2)` by the three Pauli matrices, and moves them by the adjoint
matrices `su3AdjointMatrix` and `su2AdjointMatrix`. These are the generalized Gell-Mann matrices of
`LocalGaugeData.SU.GellMann` for `N = 3` and `N = 2` under a relabelling, `su3Label` and
`su2Label`, and the adjoint matrices are the matrices of the adjoint action in those bases (A).

A family with one adjoint index has no invariant in its span, and a family with two adjoint
indices of the same factor has its invariants reduced to the trace contraction `∑ a, T ![a, a]`
(C for colour, D for isospin): the invariant tensors of `SuT[N, .adj]` and `SuT[N, .adj, .adj]` of
`LocalGaugeData.SU.Invariants.Adjoint`, read on the components through the relabelled
component maps of B.

## ii. Key results

- `StandardModel.su3Label`, `StandardModel.su2Label` : the Gell-Mann and Pauli labels as
  generalized Gell-Mann labels.
- `StandardModel.IsSU3Adjoint.reducesInvariantsTo_bot` : one colour adjoint index carries no
  invariant, and its isospin twin.
- `StandardModel.IsSU3BiAdjoint.reducesInvariantsTo_span_traceContraction` : two colour adjoint
  indices reduce to the trace contraction, and its isospin twin.

## iii. Table of contents

- A. The Gell-Mann labels
- B. Relabelled adjoint families
- C. The colour adjoint families
- D. The isospin adjoint families

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups suTensor TensorSpecies PauliMatrix

/-!

## A. The Gell-Mann labels

-/

/-- The labels of the Gell-Mann matrices of `su(3)` as generalized Gell-Mann labels: the
  symmetric and antisymmetric matrices of the planes `(0, 1)`, `(0, 2)` and `(1, 2)`, and the two
  diagonal matrices. -/
def su3LabelFun : Fin 8 → GellMann.Index 3
  | 0 => .inl ⟨(0, 1), by decide⟩
  | 1 => .inr (.inl ⟨(0, 1), by decide⟩)
  | 2 => .inr (.inr 0)
  | 3 => .inl ⟨(0, 2), by decide⟩
  | 4 => .inr (.inl ⟨(0, 2), by decide⟩)
  | 5 => .inl ⟨(1, 2), by decide⟩
  | 6 => .inr (.inl ⟨(1, 2), by decide⟩)
  | 7 => .inr (.inr 1)

/-- The relabelling of the Gell-Mann matrices of `su(3)` by generalized Gell-Mann labels. -/
noncomputable def su3Label : Fin 8 ≃ GellMann.Index 3 :=
  Equiv.ofBijective su3LabelFun ⟨by decide, by decide⟩

/-- The labels of the Pauli matrices of `su(2)` as generalized Gell-Mann labels. -/
def su2LabelFun : Fin 3 → GellMann.Index 2
  | 0 => .inl ⟨(0, 1), by decide⟩
  | 1 => .inr (.inl ⟨(0, 1), by decide⟩)
  | 2 => .inr (.inr 0)

/-- The relabelling of the Pauli matrices of `su(2)` by generalized Gell-Mann labels. -/
noncomputable def su2Label : Fin 3 ≃ GellMann.Index 2 :=
  Equiv.ofBijective su2LabelFun ⟨by decide, by decide⟩

@[simp]
lemma su3Label_apply (a : Fin 8) : su3Label a = su3LabelFun a := rfl

@[simp]
lemma su2Label_apply (i : Fin 3) : su2Label i = su2LabelFun i := rfl

/-- The Gell-Mann matrices of `su(3)` are the generalized Gell-Mann matrices. -/
lemma gellMannMatrix_eq_matrix (a : Fin 8) :
    gellMannMatrix a = GellMann.matrix (su3Label a) := by
  rw [su3Label_apply]
  fin_cases a <;> simp only [Fin.reduceFinMk, Fin.isValue] <;>
    simp only [gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three,
      gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [su3LabelFun, GellMann.matrix, GellMann.diagNorm, GellMann.diagProfile]
  all_goals rw [div_mul_eq_div_div, div_self sqrt_two_ne_zero, one_div]

/-- The Pauli matrices are the generalized Gell-Mann matrices of `su(2)`. -/
lemma pauliMatrix_inr_eq_matrix (i : Fin 3) :
    pauliMatrix (Sum.inr i) = GellMann.matrix (su2Label i) := by
  rw [su2Label_apply]
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue] <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [su2LabelFun, GellMann.matrix, pauliMatrix, GellMann.diagNorm, GellMann.diagProfile]

/-- A complex number fixed by conjugation is the image of its real part. -/
lemma ofReal_half_re_trace {z : ℂ} (hz : star (z / 2) = z / 2) :
    ((2⁻¹ * z.re : ℝ) : ℂ) = z / 2 := by
  rw [← Complex.conj_eq_iff_re.1 hz]
  congr 1
  simp
  ring

/-- The adjoint matrix of `SU(3)` is the matrix of the adjoint action in the Gell-Mann
  basis. -/
lemma su3AdjointMatrix_eq_adjMatrix (U : SU 3) (a b : Fin 8) :
    ((su3AdjointMatrix U a b : ℝ) : ℂ) = adjMatrix U (su3Label a) (su3Label b) := by
  have hreal := star_adjMatrix_apply U (su3Label a) (su3Label b)
  simp only [adjMatrix_apply, val_inv, ← gellMannMatrix_eq_matrix] at hreal ⊢
  rw [su3AdjointMatrix_apply, ofReal_half_re_trace hreal]

/-- The adjoint matrix of `SU(2)` is the matrix of the adjoint action in the Pauli basis. -/
lemma su2AdjointMatrix_eq_adjMatrix (U : SU 2) (i j : Fin 3) :
    ((su2AdjointMatrix U i j : ℝ) : ℂ) = adjMatrix U (su2Label i) (su2Label j) := by
  have hreal := star_adjMatrix_apply U (su2Label i) (su2Label j)
  simp only [adjMatrix_apply, val_inv, ← pauliMatrix_inr_eq_matrix] at hreal ⊢
  rw [su2AdjointMatrix_apply, ofReal_half_re_trace hreal]

/-!

## B. Relabelled adjoint families

A family indexed by the Standard Model labels of the adjoint index and moved by the Standard Model
adjoint matrices is, after relabelling, a family moved by the matrices of the adjoint action.

-/

section Relabel

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {N : ℕ} {ι : Type} [Fintype ι] (e : ι ≃ GellMann.Index N)
  {M : SU N → Matrix ι ι ℝ} (hM : ∀ U a b, ((M U a b : ℝ) : ℂ) = adjMatrix U (e a) (e b))

include hM in
/-- A linear map moving a family with one adjoint label by the Standard Model adjoint matrix of
  `U` intertwines the map of the relabelled family with the action of `U`. -/
lemma adjMap_smul_of_relabel_law (T : ι → B) {f : B →ₗ[ℂ] B} {U : SU N}
    (hf : ∀ l, f (T l) = ∑ a, ((M U a l : ℝ) : ℂ) • T a) (t : SuT[N, .adj]) :
    f (adjMap (T ∘ e.symm) t) = adjMap (T ∘ e.symm) (U • t) := by
  refine adjMap_smul_of_law _ U (fun a => ?_) t
  obtain ⟨l, rfl⟩ := e.surjective a
  simp only [Function.comp_apply, Equiv.symm_apply_apply, hf l, ← e.sum_comp, hM]

include hM in
/-- A linear map moving a family with two adjoint labels by the Standard Model adjoint matrix of
  `U` on each label intertwines the map of the relabelled family with the action of `U`. -/
lemma adjPairMap_smul_of_relabel_law (T : (Fin 2 → ι) → B) {f : B →ₗ[ℂ] B} {U : SU N}
    (hf : ∀ l, f (T l) = ∑ a : Fin 2 → ι, (∏ i : Fin 2, ((M U (a i) (l i) : ℝ) : ℂ)) • T a)
    (t : SuT[N, .adj, .adj]) :
    f (adjPairMap (fun n => T (e.symm ∘ n)) t) = adjPairMap (fun n => T (e.symm ∘ n)) (U • t) := by
  refine adjPairMap_smul_of_law _ U (fun l => ?_) t
  rw [hf, ← (Equiv.piCongrRight fun _ : Fin 2 => e).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_two, hM, hM]
  simp [Function.comp_def, Pi.map]

/-- The map of the relabelled family sends twice the unit tensor to the trace contraction. -/
lemma adjPairMap_relabel_two_smul_adjUnitTensor (T : (Fin 2 → ι) → B) :
    adjPairMap (fun n => T (e.symm ∘ n)) ((2 : ℂ) • adjUnitTensor N) = ∑ a : ι, T ![a, a] := by
  rw [adjPairMap_two_smul_adjUnitTensor, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => congrArg T ?_
  funext i
  fin_cases i <;> simp

end Relabel

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repGauge : Representation ℂ GaugeGroupI B}

/-!

## C. The colour adjoint families

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  adjoint index: one factor of the adjoint matrix, the summed index first. -/
def IsSU3AdjointMat (U : SU 3) (f : B →ₗ[ℂ] B) (T : Fin 8 → B) : Prop :=
  ∀ l : Fin 8, f (T l) = ∑ a : Fin 8, ((su3AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T^a` with one `su(3)` adjoint index: the map of the relabelled family out of the
  tensors of `SU(3)` is equivariant for the colour factor of the gauge group. -/
abbrev IsSU3Adjoint (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 8 → B) : Prop :=
  (suTensor 3).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU3) (adjMap (T ∘ su3Label.symm))

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  adjoint indices: one factor of the adjoint matrix per index, the summed index first. -/
def IsSU3BiAdjointMat (U : SU 3) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 8) → B) : Prop :=
  ∀ l : Fin 2 → Fin 8,
    f (T l) = ∑ a : Fin 2 → Fin 8, (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T^{ab}` with two `su(3)` adjoint indices: the map of the relabelled family out of
  the tensors of `SU(3)` is equivariant for the colour factor of the gauge group. -/
abbrev IsSU3BiAdjoint (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 8) → B) : Prop :=
  (suTensor 3).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU3)
    (adjPairMap fun n => T (su3Label.symm ∘ n))

namespace IsSU3Adjoint

variable {T : Fin 8 → B}

/-- A family obeying the law for every colour rotation is such a family. -/
lemma of_law (hT : ∀ U : SU 3, IsSU3AdjointMat U (repGauge (U, 1, 1)) T) :
    IsSU3Adjoint B repGauge T :=
  ⟨fun U t => (adjMap_smul_of_relabel_law su3Label su3AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The span of the components is stable under the colour factor. -/
lemma isStableUnder_span (hT : IsSU3Adjoint B repGauge T) :
    IsStableUnder (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [adjMap, range_familyMap, Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

/-- A colour invariant of the span of the components joined with a stable submodule lies in
  that submodule: an adjoint index contributes nothing to the invariants. -/
lemma reducesInvariantsTo_bot (hT : IsSU3Adjoint B repGauge T) :
    ReducesInvariantsTo (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) ⊥ := by
  have h := reducesInvariantsTo_bot_span_of_adjMap hT
  rwa [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

end IsSU3Adjoint

namespace IsSU3BiAdjoint

variable {T : (Fin 2 → Fin 8) → B}

/-- A family obeying the law for every colour rotation is such a family. -/
lemma of_law (hT : ∀ U : SU 3, IsSU3BiAdjointMat U (repGauge (U, 1, 1)) T) :
    IsSU3BiAdjoint B repGauge T :=
  ⟨fun U t =>
    (adjPairMap_smul_of_relabel_law su3Label su3AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The trace contraction `∑ a, T ![a, a]` of the two adjoint indices. -/
def traceContraction (T : (Fin 2 → Fin 8) → B) : B := ∑ a : Fin 8, T ![a, a]

lemma traceContraction_mem_span (T : (Fin 2 → Fin 8) → B) :
    traceContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sum_mem fun _ _ => Submodule.subset_span ⟨_, rfl⟩

/-- Any map moving the components by the adjoint matrix of an element of `SU(3)` fixes the
  trace contraction. -/
lemma map_traceContraction {U : SU 3} {f : B →ₗ[ℂ] B} (hf : IsSU3BiAdjointMat U f T) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, ← adjPairMap_relabel_two_smul_adjUnitTensor su3Label,
    adjPairMap_smul_of_relabel_law su3Label su3AdjointMatrix_eq_adjMatrix T hf, smul_comm,
    adjUnitTensor_invariant]

/-- The range of the map of the relabelled family is the span of the components. -/
lemma range_adjPairMap (T : (Fin 2 → Fin 8) → B) :
    LinearMap.range (adjPairMap fun n => T (su3Label.symm ∘ n))
      = Submodule.span ℂ (Set.range T) := by
  rw [adjPairMap, range_familyMap]
  exact congrArg _ ((Equiv.piCongrRight fun _ : Fin 2 => su3Label.symm).surjective.range_comp T)

/-- The span of the components is stable under the colour factor. -/
lemma isStableUnder_span (hT : IsSU3BiAdjoint B repGauge T) :
    IsStableUnder (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_adjPairMap] at h

/-- The colour invariants of the span of the components reduce to the line through the trace
  contraction. -/
lemma reducesInvariantsTo_span_traceContraction (hT : IsSU3BiAdjoint B repGauge T) :
    ReducesInvariantsTo (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) :=
  (hT.invariantReductionToSpanOfEq (isAdjointClosed 3 _) ((2 : ℂ) • adjUnitTensor 3)
    (fun g => by rw [smul_comm, adjUnitTensor_invariant])
    (fun t ht => by
      obtain ⟨a, rfl⟩ := exists_eq_smul_adjUnitTensor_of_invariant t ht
      exact ⟨a / 2, by rw [smul_smul, div_mul_cancel₀ a two_ne_zero]⟩)
    (range_adjPairMap T) (traceContraction T)
    (adjPairMap_relabel_two_smul_adjUnitTensor su3Label T)).reducesInvariantsTo

end IsSU3BiAdjoint

/-!

## D. The isospin adjoint families

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with one
  adjoint index: one factor of the adjoint matrix, the summed index first. -/
def IsSU2AdjointMat (U : SU 2) (f : B →ₗ[ℂ] B) (T : Fin 3 → B) : Prop :=
  ∀ l : Fin 3, f (T l) = ∑ a : Fin 3, ((su2AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T^a` with one `su(2)` adjoint index: the map of the relabelled family out of the
  tensors of `SU(2)` is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2Adjoint (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 3 → B) : Prop :=
  (suTensor 2).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU2) (adjMap (T ∘ su2Label.symm))

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  adjoint indices: one factor of the adjoint matrix per index, the summed index first. -/
def IsSU2BiAdjointMat (U : SU 2) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a

/-- A family `T^{ab}` with two `su(2)` adjoint indices: the map of the relabelled family out of
  the tensors of `SU(2)` is equivariant for the isospin factor of the gauge group. -/
abbrev IsSU2BiAdjoint (B : Type*) [AddCommGroup B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : (Fin 2 → Fin 3) → B) : Prop :=
  (suTensor 2).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU2)
    (adjPairMap fun n => T (su2Label.symm ∘ n))

namespace IsSU2Adjoint

variable {T : Fin 3 → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ U : SU 2, IsSU2AdjointMat U (repGauge (1, U, 1)) T) :
    IsSU2Adjoint B repGauge T :=
  ⟨fun U t => (adjMap_smul_of_relabel_law su2Label su2AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The span of the components is stable under the isospin factor. -/
lemma isStableUnder_span (hT : IsSU2Adjoint B repGauge T) :
    IsStableUnder (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [adjMap, range_familyMap, Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

/-- A isospin invariant of the span of the components joined with a stable submodule lies in
  that submodule: an adjoint index contributes nothing to the invariants. -/
lemma reducesInvariantsTo_bot (hT : IsSU2Adjoint B repGauge T) :
    ReducesInvariantsTo (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) ⊥ := by
  have h := reducesInvariantsTo_bot_span_of_adjMap hT
  rwa [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

end IsSU2Adjoint

namespace IsSU2BiAdjoint

variable {T : (Fin 2 → Fin 3) → B}

/-- A family obeying the law for every isospin rotation is such a family. -/
lemma of_law (hT : ∀ U : SU 2, IsSU2BiAdjointMat U (repGauge (1, U, 1)) T) :
    IsSU2BiAdjoint B repGauge T :=
  ⟨fun U t =>
    (adjPairMap_smul_of_relabel_law su2Label su2AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The trace contraction `∑ a, T ![a, a]` of the two adjoint indices. -/
def traceContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

lemma traceContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    traceContraction T ∈ Submodule.span ℂ (Set.range T) :=
  sum_mem fun _ _ => Submodule.subset_span ⟨_, rfl⟩

/-- Any map moving the components by the adjoint matrix of an element of `SU(2)` fixes the
  trace contraction. -/
lemma map_traceContraction {U : SU 2} {f : B →ₗ[ℂ] B} (hf : IsSU2BiAdjointMat U f T) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, ← adjPairMap_relabel_two_smul_adjUnitTensor su2Label,
    adjPairMap_smul_of_relabel_law su2Label su2AdjointMatrix_eq_adjMatrix T hf, smul_comm,
    adjUnitTensor_invariant]

/-- The range of the map of the relabelled family is the span of the components. -/
lemma range_adjPairMap (T : (Fin 2 → Fin 3) → B) :
    LinearMap.range (adjPairMap fun n => T (su2Label.symm ∘ n))
      = Submodule.span ℂ (Set.range T) := by
  rw [adjPairMap, range_familyMap]
  exact congrArg _ ((Equiv.piCongrRight fun _ : Fin 2 => su2Label.symm).surjective.range_comp T)

/-- The span of the components is stable under the isospin factor. -/
lemma isStableUnder_span (hT : IsSU2BiAdjoint B repGauge T) :
    IsStableUnder (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_adjPairMap] at h

/-- The isospin invariants of the span of the components reduce to the line through the trace
  contraction. -/
lemma reducesInvariantsTo_span_traceContraction (hT : IsSU2BiAdjoint B repGauge T) :
    ReducesInvariantsTo (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) :=
  (hT.invariantReductionToSpanOfEq (isAdjointClosed 2 _) ((2 : ℂ) • adjUnitTensor 2)
    (fun g => by rw [smul_comm, adjUnitTensor_invariant])
    (fun t ht => by
      obtain ⟨a, rfl⟩ := exists_eq_smul_adjUnitTensor_of_invariant t ht
      exact ⟨a / 2, by rw [smul_smul, div_mul_cancel₀ a two_ne_zero]⟩)
    (range_adjPairMap T) (traceContraction T)
    (adjPairMap_relabel_two_smul_adjUnitTensor su2Label T)).reducesInvariantsTo

end IsSU2BiAdjoint

end StandardModel
