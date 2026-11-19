/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.AdjointMatrix
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.AdjUnit
/-!
# Families of adjoint components and their invariants

Families of components with colour or isospin adjoint indices, and the trace contraction their
invariants reduce to.

## i. Overview

The Standard Model labels the adjoint indices of `su(3)` by the eight Gell-Mann matrices
`gellMannMatrix`, and those of `su(2)` by the three Pauli matrices, and moves them by the adjoint
matrices `su3AdjointMatrix` and `su2AdjointMatrix`. These are the generalized Gell-Mann matrices
`GellMann.matrix` of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.GellMann` for `N = 3` and
`N = 2` under a relabelling, `su3Label` and `su2Label`, and the adjoint matrices are the matrices
of the adjoint action in those bases (A).

A family with one adjoint index has no invariant in its span, and a family with two adjoint
indices of the same factor has its invariants reduced to the trace contraction `∑ a, T ![a, a]`
(C for colour, D for isospin). These are the invariant tensors of `SuT[N, .adj]` and
`SuT[N, .adj, .adj]` of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.AdjUnit`, read on
the components through the relabellings `relabelAdjIdx` and `relabelAdjPairIdx` of B. The lemmas
of each family live in a namespace named after its representation, `ColourAdj`, `ColourAdjAdj`,
`IsospinAdj` and `IsospinAdjAdj`.

The hypercharge factor is abelian, so its adjoint action on `u(1)` is trivial: a family with two
`u(1)` adjoint indices is moved by a hypercharge rotation not at all, and its trace contraction,
its one component, is fixed by every map that fixes the components (E).

## ii. Key results

- `StandardModel.su3Label`, `StandardModel.su2Label` : the Gell-Mann and Pauli labels as
  generalized Gell-Mann labels.
- `StandardModel.ColourAdj.reducesInvariantsTo_bot` : one colour adjoint index carries no
  invariant, and its isospin twin.
- `StandardModel.ColourAdjAdj.reducesInvariantsTo_span_traceContraction` : two colour adjoint
  indices reduce to the trace contraction, and its isospin twin.

## iii. Table of contents

- A. The Gell-Mann labels
- B. Relabelled adjoint families
- C. The colour adjoint families
- D. The isospin adjoint families
- E. The hypercharge adjoint families

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups suTensor TensorSpecies PauliMatrix
open TensorSpecies.Tensor (ComponentIdx)

/-!

## A. The Gell-Mann labels

The Gell-Mann and Pauli matrices are the generalized Gell-Mann matrices up to a relabelling, so
the Standard Model adjoint matrices are the matrices of the adjoint action.

-/

/-- The labels of the Gell-Mann matrices of `su(3)` as generalized Gell-Mann labels. They are the
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

/-- The relabelling of the Gell-Mann matrices is `su3LabelFun`. -/
@[simp]
lemma su3Label_apply (a : Fin 8) : su3Label a = su3LabelFun a := rfl

/-- The relabelling of the Pauli matrices is `su2LabelFun`. -/
@[simp]
lemma su2Label_apply (i : Fin 3) : su2Label i = su2LabelFun i := rfl

/-- The Gell-Mann matrices of `su(3)` are the generalized Gell-Mann matrices. -/
lemma gellMannMatrix_eq_matrix (a : Fin 8) :
    gellMannMatrix a = GellMann.matrix (su3Label a) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  rw [su3Label_apply]
  fin_cases a <;> simp only [Fin.reduceFinMk, Fin.isValue] <;>
    simp only [gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three,
      gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [su3LabelFun, GellMann.matrix, GellMann.diagNorm, GellMann.diagProfile]
  all_goals rw [div_mul_eq_div_div, div_self h2, one_div]

/-- The Pauli matrices are the generalized Gell-Mann matrices of `su(2)`. -/
lemma pauliMatrix_inr_eq_matrix (i : Fin 3) :
    pauliMatrix (Sum.inr i) = GellMann.matrix (su2Label i) := by
  rw [su2Label_apply]
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue] <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [su2LabelFun, GellMann.matrix, pauliMatrix, GellMann.diagNorm, GellMann.diagProfile]

/-- Half a complex number whose half is fixed by conjugation is the image of half its real
  part. -/
private lemma ofReal_inv_two_mul_re {z : ℂ} (hz : star (z / 2) = z / 2) :
    ((2⁻¹ * z.re : ℝ) : ℂ) = z / 2 := by
  rw [← Complex.conj_eq_iff_re.1 hz]
  congr 1
  simp only [Complex.div_ofNat_re]
  ring

/-- The adjoint matrix of `SU(3)` is the matrix of the adjoint action in the Gell-Mann
  basis. -/
lemma su3AdjointMatrix_eq_adjMatrix (U : SU 3) (a b : Fin 8) :
    ((su3AdjointMatrix U a b : ℝ) : ℂ) = adjMatrix U (su3Label a) (su3Label b) := by
  have hreal := star_adjMatrix_apply U (su3Label a) (su3Label b)
  simp only [adjMatrix_apply, val_inv, ← gellMannMatrix_eq_matrix] at hreal ⊢
  rw [su3AdjointMatrix_apply, ofReal_inv_two_mul_re hreal]

/-- The adjoint matrix of `SU(2)` is the matrix of the adjoint action in the Pauli basis. -/
lemma su2AdjointMatrix_eq_adjMatrix (U : SU 2) (i j : Fin 3) :
    ((su2AdjointMatrix U i j : ℝ) : ℂ) = adjMatrix U (su2Label i) (su2Label j) := by
  have hreal := star_adjMatrix_apply U (su2Label i) (su2Label j)
  simp only [adjMatrix_apply, val_inv, ← pauliMatrix_inr_eq_matrix] at hreal ⊢
  rw [su2AdjointMatrix_apply, ofReal_inv_two_mul_re hreal]

/-!

## B. Relabelled adjoint families

A family indexed by the Standard Model labels of the adjoint index and moved by the Standard Model
adjoint matrices is, after relabelling, a family moved by the matrices of the adjoint action.

-/

section Relabel

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {N : ℕ} {ι : Type} [Fintype ι] (e : ι ≃ GellMann.Index N)

/-- The component indices of a tensor with one adjoint index of `SU(N)`, as a label in `ι`
  through the relabelling `e` of the Gell-Mann labels. -/
noncomputable def relabelAdjIdx : ComponentIdx (S := suTensor N) ![.adj] ≃ ι :=
  adjIdx.trans e.symm

/-- The component indices of a tensor with two adjoint indices of `SU(N)`, as a pair of labels in
  `ι` through the relabelling `e` of the Gell-Mann labels. -/
noncomputable def relabelAdjPairIdx : ComponentIdx (S := suTensor N) ![.adj, .adj] ≃ (Fin 2 → ι) :=
  adjPairIdx.trans (Equiv.piCongrRight fun _ => e.symm)

variable {M : SU N → Matrix ι ι ℝ} (hM : ∀ U a b, ((M U a b : ℝ) : ℂ) = adjMatrix U (e a) (e b))

include hM in
/-- A linear map moving a family with one adjoint label by the Standard Model adjoint matrix of
  `U` intertwines the map of the relabelled family with the action of `U`. -/
lemma liftComponents_relabelAdj_smul_of_law (T : ι → B) {f : B →ₗ[ℂ] B} {U : SU N}
    (hf : ∀ l, f (T l) = ∑ a, ((M U a l : ℝ) : ℂ) • T a) (t : SuT[N, .adj]) :
    f (liftComponents (T ∘ relabelAdjIdx e) t) = liftComponents (T ∘ relabelAdjIdx e) (U • t) := by
  refine liftComponents_adj_smul_of_law (T ∘ e.symm) U (fun a => ?_) t
  obtain ⟨l, rfl⟩ := e.surjective a
  simp only [Function.comp_apply, Equiv.symm_apply_apply, hf l, ← e.sum_comp, hM]

include hM in
/-- A linear map moving a family with two adjoint labels by the Standard Model adjoint matrix of
  `U` on each label intertwines the map of the relabelled family with the action of `U`. -/
lemma liftComponents_relabelAdjPair_smul_of_law (T : (Fin 2 → ι) → B) {f : B →ₗ[ℂ] B} {U : SU N}
    (hf : ∀ l, f (T l) = ∑ a : Fin 2 → ι, (∏ i : Fin 2, ((M U (a i) (l i) : ℝ) : ℂ)) • T a)
    (t : SuT[N, .adj, .adj]) :
    f (liftComponents (T ∘ relabelAdjPairIdx e) t)
      = liftComponents (T ∘ relabelAdjPairIdx e) (U • t) := by
  refine liftComponents_adjPair_smul_of_law (fun n => T (e.symm ∘ n)) U (fun l => ?_) t
  rw [hf, ← (Equiv.piCongrRight fun _ : Fin 2 => e).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_two, hM, hM]
  simp [Function.comp_def, Pi.map]

/-- The map of the relabelled family sends twice the unit tensor to the trace contraction. -/
lemma liftComponents_relabelAdjPair_two_smul_adjUnitTensor (T : (Fin 2 → ι) → B) :
    liftComponents (T ∘ relabelAdjPairIdx e) ((2 : ℂ) • adjUnitTensor N) = ∑ a : ι, T ![a, a] := by
  rw [show T ∘ relabelAdjPairIdx e = (fun n => T (e.symm ∘ n)) ∘ adjPairIdx from rfl,
    liftComponents_two_smul_adjUnitTensor, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => congrArg T ?_
  funext i
  fin_cases i <;> simp

end Relabel

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repGauge : Representation ℂ GaugeGroupI B}

/-!

## C. The colour adjoint families

A family with one colour adjoint index has no invariant, and one with two has the trace
contraction alone.

-/

namespace ColourAdj

variable {T : Fin 8 → B}

/-- A family `T^a` with one `su(3)` adjoint index: when every colour rotation `U` moves its
  members by the adjoint matrix of `U`, the summed index first, the map of the relabelled family
  out of the tensors of `SU(3)` is equivariant for the colour factor of the gauge group. -/
lemma of_law (hT : ∀ (U : SU 3) (l : Fin 8),
    repGauge (U, 1, 1) (T l) = ∑ a : Fin 8, ((su3AdjointMatrix U a l : ℝ) : ℂ) • T a) :
    (suTensor 3).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjIdx su3Label)) :=
  ⟨fun U t =>
    (liftComponents_relabelAdj_smul_of_law su3Label su3AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The span of the components is stable under the colour factor. -/
lemma isStableUnder_span
    (hT : (suTensor 3).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjIdx su3Label))) :
    IsStableUnder (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_liftComponents_comp] at h

/-- A colour invariant of the span of the components joined with a stable submodule lies in
  that submodule. An adjoint index contributes nothing to the invariants. -/
lemma reducesInvariantsTo_bot
    (hT : (suTensor 3).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjIdx su3Label))) :
    ReducesInvariantsTo (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) ⊥ := by
  have h := reducesInvariantsTo_bot_span_adj (T := T ∘ su3Label.symm) hT
  rwa [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

end ColourAdj

namespace ColourAdjAdj

variable {T : (Fin 2 → Fin 8) → B}

/-- A family `T^{ab}` with two `su(3)` adjoint indices: when every colour rotation `U` moves its
  members by one factor of the adjoint matrix of `U` per index, the summed index first, the map
  of the relabelled family out of the tensors of `SU(3)` is equivariant for the colour factor of
  the gauge group. -/
lemma of_law (hT : ∀ (U : SU 3) (l : Fin 2 → Fin 8), repGauge (U, 1, 1) (T l)
    = ∑ a : Fin 2 → Fin 8, (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a) :
    (suTensor 3).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjPairIdx su3Label)) :=
  ⟨fun U t => (liftComponents_relabelAdjPair_smul_of_law su3Label su3AdjointMatrix_eq_adjMatrix T
    (hT U) t).symm⟩

/-- The trace contraction `∑ a, T ![a, a]` of the two adjoint indices. -/
def traceContraction (T : (Fin 2 → Fin 8) → B) : B := ∑ a : Fin 8, T ![a, a]

/-- Any map moving the components by the adjoint matrix of an element of `SU(3)` fixes the
  trace contraction. -/
lemma map_traceContraction {U : SU 3} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 8, f (T l)
    = ∑ a : Fin 2 → Fin 8, (∏ i : Fin 2, ((su3AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, ← liftComponents_relabelAdjPair_two_smul_adjUnitTensor su3Label,
    liftComponents_relabelAdjPair_smul_of_law su3Label su3AdjointMatrix_eq_adjMatrix T hf,
    smul_comm, adjUnitTensor_invariant]

/-- The span of the components is stable under the colour factor. -/
lemma isStableUnder_span
    (hT : (suTensor 3).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjPairIdx su3Label))) :
    IsStableUnder (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_liftComponents_comp] at h

/-- The colour invariants of the span of the components reduce to the line through the trace
  contraction. -/
lemma reducesInvariantsTo_span_traceContraction
    (hT : (suTensor 3).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents (T ∘ relabelAdjPairIdx su3Label))) :
    ReducesInvariantsTo (fun U : SU 3 => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) :=
  (hT.invariantReductionToSpanOfEq (hasReynolds 3 _)
    invariants_adj_adj_eq_span_two_smul_adjUnitTensor (range_liftComponents_comp _ T)
    (traceContraction T)
    (liftComponents_relabelAdjPair_two_smul_adjUnitTensor su3Label T)).reducesInvariantsTo

end ColourAdjAdj

/-!

## D. The isospin adjoint families

The isospin twins of the families of section C.

-/

namespace IsospinAdj

variable {T : Fin 3 → B}

/-- A family `T^a` with one `su(2)` adjoint index: when every isospin rotation `U` moves its
  members by the adjoint matrix of `U`, the summed index first, the map of the relabelled family
  out of the tensors of `SU(2)` is equivariant for the isospin factor of the gauge group. -/
lemma of_law (hT : ∀ (U : SU 2) (l : Fin 3),
    repGauge (1, U, 1) (T l) = ∑ a : Fin 3, ((su2AdjointMatrix U a l : ℝ) : ℂ) • T a) :
    (suTensor 2).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjIdx su2Label)) :=
  ⟨fun U t =>
    (liftComponents_relabelAdj_smul_of_law su2Label su2AdjointMatrix_eq_adjMatrix T (hT U) t).symm⟩

/-- The span of the components is stable under the isospin factor. -/
lemma isStableUnder_span
    (hT : (suTensor 2).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjIdx su2Label))) :
    IsStableUnder (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_liftComponents_comp] at h

/-- An isospin invariant of the span of the components joined with a stable submodule lies in
  that submodule. An adjoint index contributes nothing to the invariants. -/
lemma reducesInvariantsTo_bot
    (hT : (suTensor 2).IsEquivariant ![.adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjIdx su2Label))) :
    ReducesInvariantsTo (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) ⊥ := by
  have h := reducesInvariantsTo_bot_span_adj (T := T ∘ su2Label.symm) hT
  rwa [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at h

end IsospinAdj

namespace IsospinAdjAdj

variable {T : (Fin 2 → Fin 3) → B}

/-- A family `T^{ab}` with two `su(2)` adjoint indices: when every isospin rotation `U` moves its
  members by one factor of the adjoint matrix of `U` per index, the summed index first, the map
  of the relabelled family out of the tensors of `SU(2)` is equivariant for the isospin factor of
  the gauge group. -/
lemma of_law (hT : ∀ (U : SU 2) (l : Fin 2 → Fin 3), repGauge (1, U, 1) (T l)
    = ∑ a : Fin 2 → Fin 3, (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a) :
    (suTensor 2).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjPairIdx su2Label)) :=
  ⟨fun U t => (liftComponents_relabelAdjPair_smul_of_law su2Label su2AdjointMatrix_eq_adjMatrix T
    (hT U) t).symm⟩

/-- The trace contraction `∑ a, T ![a, a]` of the two adjoint indices. -/
def traceContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- Any map moving the components by the adjoint matrix of an element of `SU(2)` fixes the
  trace contraction. -/
lemma map_traceContraction {U : SU 2} {f : B →ₗ[ℂ] B} (hf : ∀ l : Fin 2 → Fin 3, f (T l)
    = ∑ a : Fin 2 → Fin 3, (∏ i : Fin 2, ((su2AdjointMatrix U (a i) (l i) : ℝ) : ℂ)) • T a) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, ← liftComponents_relabelAdjPair_two_smul_adjUnitTensor su2Label,
    liftComponents_relabelAdjPair_smul_of_law su2Label su2AdjointMatrix_eq_adjMatrix T hf,
    smul_comm, adjUnitTensor_invariant]

/-- The span of the components is stable under the isospin factor. -/
lemma isStableUnder_span
    (hT : (suTensor 2).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjPairIdx su2Label))) :
    IsStableUnder (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) := by
  have h := hT.isStableUnder_range
  rwa [range_liftComponents_comp] at h

/-- The isospin invariants of the span of the components reduce to the line through the trace
  contraction. -/
lemma reducesInvariantsTo_span_traceContraction
    (hT : (suTensor 2).IsEquivariant ![.adj, .adj] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents (T ∘ relabelAdjPairIdx su2Label))) :
    ReducesInvariantsTo (fun U : SU 2 => repGauge ((1, U, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range T)) (ℂ ∙ traceContraction T) :=
  (hT.invariantReductionToSpanOfEq (hasReynolds 2 _)
    invariants_adj_adj_eq_span_two_smul_adjUnitTensor (range_liftComponents_comp _ T)
    (traceContraction T)
    (liftComponents_relabelAdjPair_two_smul_adjUnitTensor su2Label T)).reducesInvariantsTo

end IsospinAdjAdj

/-!

## E. The hypercharge adjoint families

The hypercharge factor is abelian, so its adjoint action on `u(1)` is trivial, and there is no
tensor species to relabel. A family `T : (Fin 2 → Fin 1) → B` with two `u(1)` adjoint indices is
moved by a hypercharge rotation by one factor of the `1 × 1` adjoint matrix `1` per index, which is
to say not at all, so its law is stated directly as `∀ l, f (T l) = T l`. The trace contraction
is the one component of the family, and every map fixing the components fixes it.

-/

namespace HyperchargeAdjAdj

/-- The trace contraction: the Kronecker contraction of the two `u(1)` indices, which is the one
  component of the family. -/
def traceContraction (T : (Fin 2 → Fin 1) → B) : B := ∑ a : Fin 1, T ![a, a]

/-- Any map fixing the components fixes the trace contraction. -/
lemma map_traceContraction {T : (Fin 2 → Fin 1) → B} {f : B →ₗ[ℂ] B}
    (hf : ∀ l : Fin 2 → Fin 1, f (T l) = T l) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, map_sum]
  exact Finset.sum_congr rfl fun a _ => hf _

end HyperchargeAdjAdj

end StandardModel
