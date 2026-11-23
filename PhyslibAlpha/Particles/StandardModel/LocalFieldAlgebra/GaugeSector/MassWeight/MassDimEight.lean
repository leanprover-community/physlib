/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeSector.MassWeight.MassDimLTEight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.InvariantReduction
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Invariants.Adjoint
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.ContractionTensor
public import Mathlib.RepresentationTheory.Invariants
/-!
# Products of two field strengths as bi-adjoint gauge tensors

The gauge and Lorentz invariants of the gauge sector at mass weight eight, the kinetic and theta
terms of the three gauge groups.

## i. Overview

A single field-strength symbol of the gauge sector carries one adjoint index of the gauge
algebra, so a product of two of them carries two. Restricting the value index to one
factor of the gauge group turns such a product into a family indexed by two adjoint
indices of that factor, and the gauge transformation law `repGauge_F` says exactly that
the maps of these families out of the tensors with two adjoint indices are equivariant
(`ColourAdjAdj.of_law`, `IsospinAdjAdj.of_law`), and for hypercharge the family is fixed
outright. The gauge invariant these laws supply is the trace contraction,
the Kronecker contraction of the two adjoint indices, the familiar kinetic pairing of two
field strengths; it has mass weight eight and is fixed by the whole gauge group.

Conversely every twice-derived field strength and every product of two underived ones,
sorted by gauge factor, is a component of a gluon or `W`-boson pair family, a hypercharge
invariant, or a family carrying an unpaired adjoint index of a non-abelian factor, which
contributes nothing by `ColourAdj.reducesInvariantsTo_bot` and
`IsospinAdj.reducesInvariantsTo_bot`. Putting the two
directions together classifies the gauge invariants of mass weight eight modulo any
gauge-stable submodule. Such an invariant is a combination of the three underived trace
contractions and the twice-derived hypercharge field strengths. Both shapes carry four
covector indices and no others, so both are quadruple Lorentz tensors, and the Lorentz
classification cuts the combinations down further, to the four Lorentz contractions of
each of the four families. All four families are antisymmetric in their last two slots, by
`F_antisymm`, and that leaves two contractions of each, eight spanning generators in all
(`lorentzContractionEightSpan_eq`).

Both classifications are reductions in the sense of `ReducesInvariantsTo`, stated modulo
any stable submodule. The converse is that each span consists of invariants of mass weight
eight already, the gauge one because its generators are fixed by the gauge group and carry
the right mass weight, and the Lorentz one because it sits inside the gauge span and is
spanned by contractions that `RankFour` shows to be Lorentz invariant. Section J composes
the two reductions and puts the two directions together as the equivalences
`mem_massWeightSubmodule_eight_sup_and_invariant_iff` and
`mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`, the second also with the
eight generators, `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_reduced`.

## ii. Key results

- `lorentzContractionEightSpan_eq` : the Lorentz contraction span is spanned by eight of its
  sixteen generators, for each family the `(0,2)(1,3)` metric contraction and the Levi-Civita
  contraction.
- `mem_massWeightSubmodule_eight_sup_and_invariant_iff` : the gauge classification of mass weight
  eight as an equivalence.
- `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff` : the gauge and Lorentz
  classification of mass weight eight as an equivalence, with the four Lorentz contractions of
  the four families of section H.
- `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_reduced` : the same
  equivalence with the eight generators of `lorentzContractionEightSpan_eq`.

## iii. Table of contents

- A. Spans and stability
- B. The gauge transformation of the gauge-factor field strengths
- C. Products of two underived field strengths as bi-adjoint families
- D. The families of mass weight eight
- E. Mass weight eight inside the family spans
- F. The unpaired non-abelian adjoint indices
- G. The gauge invariants of mass weight eight
- H. The Lorentz classification of the mass-weight eight invariants
- I. The Lorentz contraction span as invariants of mass weight eight
- J. The classifications as equivalences

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open Matrix MatrixGroups Lorentz
open LocalCovFieldAlgebra

namespace GaugeSector

/-!

## A. Spans and stability

Every subspace in this file is spanned by a finite family. Where a classifier supplies or
consumes it, it is written `Submodule.span ℂ (Set.range T)`; where a family of lines is
collected, it is the join `⨆ i, ℂ ∙ T i`, and `Submodule.span_range_eq_iSup` passes between
the two. A join of lines lies in a submodule as soon as its generators do, and a linear map
fixing each generator fixes it pointwise; a linear map moving each generator to a
combination of the generators carries the span into itself.

The classification runs through `ReducesInvariantsTo`. Each bi-adjoint family's span
reduces, for its factor of the gauge group, to the line through its trace contraction, and
each adjoint family's span to `⊥`; `ReducesInvariantsTo.iSup` joins the families of one
kind, and `ReducesInvariantsTo.sup` joins the kinds.

-/

/-- A span lies in a submodule as soon as its generators do. -/
lemma iSup_span_singleton_le {ι : Sort*} (T : ι → fieldData.LocalCovFieldAlgebra)
    {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hV : ∀ i, T i ∈ V) : (⨆ i, ℂ ∙ T i) ≤ V :=
  iSup_le fun i => (Submodule.span_singleton_le_iff_mem _ _).2 (hV i)

/-- A generator of a family with three indices lies in its span. -/
lemma mem_iSup_span₃ {α β γ : Sort*} (T : α → β → γ → fieldData.LocalCovFieldAlgebra)
    (a : α) (b : β) (c : γ) :
    T a b c ∈ ⨆ (a) (b) (c), ℂ ∙ T a b c :=
  Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _)))

/-- A linear map moving each generator to a combination of the generators carries the span
  into itself; the transformation laws of this file all have this shape. -/
lemma span_stable_of_map_eq_sum {ι : Type} [Fintype ι] (T : ι → fieldData.LocalCovFieldAlgebra)
    (f : fieldData.LocalCovFieldAlgebra →ₗ[ℂ] fieldData.LocalCovFieldAlgebra)
    {c : ι → ι → ℂ} (hf : ∀ l, f (T l) = ∑ a, c a l • T a) :
    ∀ y ∈ Submodule.span ℂ (Set.range T), f y ∈ Submodule.span ℂ (Set.range T) :=
  isStableUnder_span_range_of_sum (σ := fun _ : Unit => f) (fun _ l => ⟨_, hf l⟩) ()

/-- A linear map fixing each generator fixes the span pointwise. -/
lemma map_eq_self_of_mem_iSup_span {ι : Sort*} (T : ι → fieldData.LocalCovFieldAlgebra)
    (f : fieldData.LocalCovFieldAlgebra →ₗ[ℂ] fieldData.LocalCovFieldAlgebra)
    (hf : ∀ i, f (T i) = T i) : ∀ y ∈ ⨆ i, ℂ ∙ T i, f y = y := fun _ hy =>
  LinearMap.mem_eqLocus.1 (iSup_span_singleton_le T (V := LinearMap.eqLocus f LinearMap.id)
    (fun i => LinearMap.mem_eqLocus.2 (hf i)) hy)

/-- The product of two lines lies in a submodule as soon as the product of the two
  generators does. -/
lemma span_singleton_mul_span_singleton_le {a b : fieldData.LocalCovFieldAlgebra}
    {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hab : a * b ∈ V) :
    (ℂ ∙ a) * (ℂ ∙ b) ≤ V := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact (Submodule.span_singleton_le_iff_mem _ _).2 hab

/-- The product of two spans lies in a submodule as soon as the products of their
  generators do. -/
lemma iSup_span_mul_iSup_span_le {α β γ α' β' γ' : Sort*}
    (T : α → β → γ → fieldData.LocalCovFieldAlgebra)
    (T' : α' → β' → γ' → fieldData.LocalCovFieldAlgebra)
    {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hV : ∀ a b c a' b' c', T a b c * T' a' b' c' ∈ V) :
    (⨆ (a) (b) (c), ℂ ∙ T a b c) * (⨆ (a) (b) (c), ℂ ∙ T' a b c) ≤ V := by
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun _ => ?_
  exact span_singleton_mul_span_singleton_le (hV _ _ _ _ _ _)

/-- A product of two combinations is a combination indexed by pairs. -/
lemma sum_mul_sum_eq_sum_pi_two {k : ℕ} (c₀ c₁ : Fin k → ℂ)
    (X Y : Fin k → fieldData.LocalCovFieldAlgebra) :
    (∑ a, c₀ a • X a) * ∑ b, c₁ b • Y b
      = ∑ d : Fin 2 → Fin k, (c₀ (d 0) * c₁ (d 1)) • (X (d 0) * Y (d 1)) := by
  rw [Fintype.sum_mul_sum, Physlib.Fin.sum_fin_two_arrow]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A multiplicative map moving a family by a matrix and fixing a vector moves the
  products of the family with that vector by the same matrix. -/
lemma map_mul_fixed_eq_sum {k : ℕ}
    {f : fieldData.LocalCovFieldAlgebra →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hf : ∀ x y, f (x * y) = f x * f y)
    {c : Fin k → Fin k → ℂ} {T : Fin k → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ l, f (T l) = ∑ a, c a l • T a) {v : fieldData.LocalCovFieldAlgebra}
    (hv : f v = v) (l : Fin k) : f (T l * v) = ∑ a, c a l • (T a * v) := by
  rw [hf, hT, hv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- The mirror of `map_mul_fixed_eq_sum` with the fixed vector on the left. -/
lemma map_fixed_mul_eq_sum {k : ℕ}
    {f : fieldData.LocalCovFieldAlgebra →ₗ[ℂ] fieldData.LocalCovFieldAlgebra}
    (hf : ∀ x y, f (x * y) = f x * f y)
    {c : Fin k → Fin k → ℂ} {T : Fin k → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ l, f (T l) = ∑ a, c a l • T a) {v : fieldData.LocalCovFieldAlgebra}
    (hv : f v = v) (l : Fin k) : f (v * T l) = ∑ a, c a l • (v * T a) := by
  rw [hf, hT, hv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_smul_comm _ _ _

/-!

## B. The gauge transformation of the gauge-factor field strengths

The gauge law `repGauge_F` moves the field-strength symbol by the coadjoint action of
the gauge group on its argument, which on the standard basis coordinates is the adjoint
matrix. That matrix is block diagonal, so the gluon field strengths transform among
themselves by the `su(3)` adjoint matrix of the colour factor, the `W`-boson field
strengths by the `su(2)` adjoint matrix of the isospin factor, and the hypercharge field
strength is fixed. The colour factor alone fixes the `W`-boson field strengths as well.

-/

/-- The field-strength symbol evaluated on a standard-basis coordinate transforms under
  the gauge group through the column of `adjointMatrix` indexed by that coordinate. -/
lemma repGauge_F_coord (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    repGaugeGroupI g (gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord c))
      = ∑ b, ((GaugeAlgebra.adjointMatrix g b c : ℝ) : ℂ) •
          gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord b) := by
  rw [repGauge_F g l μ ν,
    show GaugeAlgebra.adjointMap g⁻¹
      = (GaugeAlgebra.adjoint g⁻¹ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra) from rfl,
    GaugeAlgebra.adjoint_dualMap_coord, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, GaugeAlgebra.adjointMatrix_inv_apply, Complex.coe_smul]

/-- The gluon field strength transforms in the adjoint representation of the `su(3)`
  factor of the gauge group. -/
lemma repGauge_gluonField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8) :
    repGaugeGroupI g (gluonField l μ ν c)
      = ∑ a : Fin 8, ((su3AdjointMatrix (GaugeGroupI.toSU3 g) a c : ℝ) : ℂ) •
          gluonField l μ ν a := by
  rw [gluonField, repGauge_F_coord g l μ ν (Sum.inl c), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [gluonField]

/-- The `W`-boson field strength transforms in the adjoint representation of the `su(2)`
  factor of the gauge group. -/
lemma repGauge_wField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 3) :
    repGaugeGroupI g (wField l μ ν c)
      = ∑ i : Fin 3, ((su2AdjointMatrix (GaugeGroupI.toSU2 g) i c : ℝ) : ℂ) •
          wField l μ ν i := by
  rw [wField, repGauge_F_coord g l μ ν (Sum.inr (Sum.inl c)), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [wField]

/-- The hypercharge field strength is gauge invariant, the adjoint action of the gauge
  group on the `u(1)` factor of the gauge algebra is trivial. -/
lemma repGauge_hyperchargeField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGaugeGroupI g (hyperchargeField l μ ν) = hyperchargeField l μ ν := by
  rw [hyperchargeField, repGauge_F_coord g l μ ν (Sum.inr (Sum.inr 0)),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-- The `W`-boson field strengths are fixed by the colour factor of the gauge group, since the
  `su(2)` block of the adjoint matrix reads the isospin factor alone. -/
lemma repGauge_su3_wField (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (i : Fin 3) :
    repGaugeGroupI (U, 1, 1) (wField l μ ν i) = wField l μ ν i := by
  rw [repGauge_wField (U, 1, 1) l μ ν i]
  have hM : ∀ j : Fin 3, su2AdjointMatrix (GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI)) j i
      = if j = i then 1 else 0 := by
    intro j
    rw [show su2AdjointMatrix (GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI)) j i
        = GaugeAlgebra.adjointMatrix (1 : GaugeGroupI) (Sum.inr (Sum.inl j))
          (Sum.inr (Sum.inl i)) from rfl, GaugeAlgebra.adjointMatrix_one, Matrix.one_apply]
    simp
  simp only [hM]
  simp

/-- The gluon field strengths at fixed derivative slots and covector indices form a family
  of one `su(3)` adjoint index. -/
lemma isEquivariant_colourAdj_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    (suTensor 3).IsEquivariant ![.adj] (repGaugeGroupI.comp GaugeGroupI.ofSU3)
      (liftComponents ((gluonField l μ ν) ∘ relabelAdjIdx su3Label)) :=
  ColourAdj.of_law fun U c => repGauge_gluonField (U, 1, 1) l μ ν c

/-- The `W`-boson field strengths at fixed derivative slots and covector indices form a
  family of one `su(2)` adjoint index. -/
lemma isEquivariant_isospinAdj_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    (suTensor 2).IsEquivariant ![.adj] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((wField l μ ν) ∘ relabelAdjIdx su2Label)) :=
  IsospinAdj.of_law fun U c => repGauge_wField (1, U, 1) l μ ν c

/-!

## C. Products of two underived field strengths as bi-adjoint families

A product of two underived field strengths of one gauge factor, at the four covector
indices `p`, is a family indexed by the two adjoint indices of that factor, and by section
B and the multiplicativity of the gauge action it obeys the transformation law of a tensor
with two adjoint indices (`repGaugeGroupI_gluonPair_eq_sum`, `repGaugeGroupI_wPair_eq_sum`,
`repGaugeGroupI_hyperchargePair`), at every gauge element and not only at those of its own
factor. Its trace contraction, the Kronecker contraction of the two adjoint indices, is fixed by the
whole
gauge group and has mass weight eight, the sum of the mass weights of its two factors; so
is the twice-derived hypercharge field strength, the other shape of mass weight eight.

-/

/-- The index of a product of two underived field strengths, the two covector indices of
  the first factor followed by the two of the second, read as one family of four
  four-vector indices so that the Lorentz classification applies to it. -/
abbrev EightIdx : Type := Fin 4 → Fin 1 ⊕ Fin 3

/-- The product of two underived gluon field strengths at the covector indices `p`, indexed
  by the two `su(3)` adjoint indices it carries. -/
noncomputable def gluonPair (p : EightIdx) (a : Fin 2 → Fin 8) : fieldData.LocalCovFieldAlgebra :=
  gluonField ![] (p 0) (p 1) (a 0) * gluonField ![] (p 2) (p 3) (a 1)

/-- The product of two underived `W`-boson field strengths at the covector indices `p`,
  indexed by the two `su(2)` adjoint indices it carries. -/
noncomputable def wPair (p : EightIdx) (a : Fin 2 → Fin 3) : fieldData.LocalCovFieldAlgebra :=
  wField ![] (p 0) (p 1) (a 0) * wField ![] (p 2) (p 3) (a 1)

/-- The product of two underived hypercharge field strengths at the covector indices `p`,
  indexed by the two `u(1)` adjoint indices it carries. -/
noncomputable def hyperchargePair (p : EightIdx)
    (_ : Fin 2 → Fin 1) : fieldData.LocalCovFieldAlgebra :=
  hyperchargeField ![] (p 0) (p 1) * hyperchargeField ![] (p 2) (p 3)

/-- The twice-derived hypercharge field strength at the derivative slots `d 0`, `d 1` and
  the covector indices `d 2`, `d 3`. -/
noncomputable def hyperchargeDeriv (d : EightIdx) : fieldData.LocalCovFieldAlgebra :=
  hyperchargeField ![d 0, d 1] (d 2) (d 3)

/-- A gauge transformation moves a gluon pair as the `SU(3)` factor of that gauge group
  element moves a tensor with two `su(3)` adjoint indices. -/
lemma repGaugeGroupI_gluonPair_eq_sum (p : EightIdx) (g : GaugeGroupI) (l : Fin 2 → Fin 8) :
    repGaugeGroupI g (gluonPair p l) = ∑ a : Fin 2 → Fin 8,
      (∏ i : Fin 2, ((su3AdjointMatrix (GaugeGroupI.toSU3 g) (a i) (l i) : ℝ) : ℂ)) •
        gluonPair p a := by
  simp only [gluonPair, repGaugeGroupI_mul, repGauge_gluonField, sum_mul_sum_eq_sum_pi_two,
    Fin.prod_univ_two]

/-- A gluon pair is a bi-adjoint `su(3)` tensor. -/
lemma isEquivariant_colourAdjAdj_gluonPair (p : EightIdx) :
    (suTensor 3).IsEquivariant ![.adj, .adj] (repGaugeGroupI.comp GaugeGroupI.ofSU3)
      (liftComponents ((gluonPair p) ∘ relabelAdjPairIdx su3Label)) :=
  ColourAdjAdj.of_law fun U => repGaugeGroupI_gluonPair_eq_sum p (U, 1, 1)

/-- A gauge transformation moves a `W`-boson pair as the `SU(2)` factor of that gauge group
  element moves a tensor with two `su(2)` adjoint indices. -/
lemma repGaugeGroupI_wPair_eq_sum (p : EightIdx) (g : GaugeGroupI) (l : Fin 2 → Fin 3) :
    repGaugeGroupI g (wPair p l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((su2AdjointMatrix (GaugeGroupI.toSU2 g) (a i) (l i) : ℝ) : ℂ)) •
        wPair p a := by
  simp only [wPair, repGaugeGroupI_mul, repGauge_wField, sum_mul_sum_eq_sum_pi_two,
    Fin.prod_univ_two]

/-- A `W`-boson pair is a bi-adjoint `su(2)` tensor. -/
lemma isEquivariant_isospinAdjAdj_wPair (p : EightIdx) :
    (suTensor 2).IsEquivariant ![.adj, .adj] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((wPair p) ∘ relabelAdjPairIdx su2Label)) :=
  IsospinAdjAdj.of_law fun U => repGaugeGroupI_wPair_eq_sum p (1, U, 1)

/-- A gauge transformation fixes a hypercharge pair, which is the `u(1)` bi-adjoint law. -/
lemma repGaugeGroupI_hyperchargePair (p : EightIdx) (g : GaugeGroupI) (l : Fin 2 → Fin 1) :
    repGaugeGroupI g (hyperchargePair p l) = hyperchargePair p l := by
  simp only [hyperchargePair, repGaugeGroupI_mul, repGauge_hyperchargeField]

/-- The gluon trace contraction at the covector indices `p`, the Kronecker contraction of
  the two colour indices of the gluon pair. -/
noncomputable def gluonTrace (p : EightIdx) : fieldData.LocalCovFieldAlgebra :=
  ColourAdjAdj.traceContraction (gluonPair p)

/-- The `W`-boson trace contraction at the covector indices `p`. -/
noncomputable def wTrace (p : EightIdx) : fieldData.LocalCovFieldAlgebra :=
  IsospinAdjAdj.traceContraction (wPair p)

/-- The hypercharge trace contraction at the covector indices `p`. -/
noncomputable def hyperchargeTrace (p : EightIdx) : fieldData.LocalCovFieldAlgebra :=
  HyperchargeAdjAdj.traceContraction (hyperchargePair p)

/-- The gluon trace contraction is the kinetic pairing of two gluon field strengths. -/
lemma gluonTrace_eq (p : EightIdx) :
    gluonTrace p
      = ∑ a : Fin 8, gluonField ![] (p 0) (p 1) a * gluonField ![] (p 2) (p 3) a := by
  simp [gluonTrace, ColourAdjAdj.traceContraction, gluonPair]

/-- The `W`-boson trace contraction is the kinetic pairing of two `W`-boson field
  strengths. -/
lemma wTrace_eq (p : EightIdx) :
    wTrace p = ∑ i : Fin 3, wField ![] (p 0) (p 1) i * wField ![] (p 2) (p 3) i := by
  simp [wTrace, IsospinAdjAdj.traceContraction, wPair]

/-- The hypercharge trace contraction is the product of the two hypercharge field
  strengths, the `u(1)` factor being one dimensional. -/
lemma hyperchargeTrace_eq (p : EightIdx) :
    hyperchargeTrace p
      = hyperchargeField ![] (p 0) (p 1) * hyperchargeField ![] (p 2) (p 3) := by
  simp [hyperchargeTrace, HyperchargeAdjAdj.traceContraction, hyperchargePair]

/-- The gluon trace contraction is fixed by the whole gauge group. -/
lemma repGauge_gluonTrace (g : GaugeGroupI) (p : EightIdx) :
    repGaugeGroupI g (gluonTrace p) = gluonTrace p :=
  ColourAdjAdj.map_traceContraction (repGaugeGroupI_gluonPair_eq_sum p g)

/-- The `W`-boson trace contraction is fixed by the whole gauge group. -/
lemma repGauge_wTrace (g : GaugeGroupI) (p : EightIdx) :
    repGaugeGroupI g (wTrace p) = wTrace p :=
  IsospinAdjAdj.map_traceContraction (repGaugeGroupI_wPair_eq_sum p g)

/-- The hypercharge trace contraction is fixed by the whole gauge group. -/
lemma repGauge_hyperchargeTrace (g : GaugeGroupI) (p : EightIdx) :
    repGaugeGroupI g (hyperchargeTrace p) = hyperchargeTrace p :=
  HyperchargeAdjAdj.map_traceContraction (repGaugeGroupI_hyperchargePair p g)

/-- The twice-derived hypercharge field strength is fixed by the whole gauge group. -/
lemma repGauge_hyperchargeDeriv (g : GaugeGroupI) (d : EightIdx) :
    repGaugeGroupI g (hyperchargeDeriv d) = hyperchargeDeriv d :=
  repGauge_hyperchargeField g _ _ _

/-- Every field-strength symbol lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma F_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : gaugeFieldStrength l μ ν φ ∈ derivSubmodule n := by
  rw [derivSubmodule]
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))

/-- A field-strength symbol with `n` covariant derivatives has mass weight `2 * (2 + n)`. -/
lemma F_mem_massWeightSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : gaugeFieldStrength l μ ν φ ∈ massWeightSubmodule (2 * (2 +
      n)) :=
  derivSubmodule_le_massWeightSubmodule n (F_mem_derivSubmodule l μ ν φ)

/-- A product of two underived field-strength symbols has mass weight eight. -/
lemma F_mul_F_mem_massWeightSubmodule_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3)
    (φ φ' : Module.Dual ℝ GaugeAlgebra) :
    gaugeFieldStrength ![] μ ν φ * gaugeFieldStrength ![] μ' ν' φ' ∈ massWeightSubmodule 8 := by
  simpa using massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul
    (F_mem_massWeightSubmodule ![] μ ν φ) (F_mem_massWeightSubmodule ![] μ' ν' φ'))

/-- The gluon trace contraction has mass weight eight. -/
lemma gluonTrace_mem_massWeightSubmodule (p : EightIdx) :
    gluonTrace p ∈ massWeightSubmodule 8 := by
  rw [gluonTrace_eq]
  exact Submodule.sum_mem _ fun a _ => F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The `W`-boson trace contraction has mass weight eight. -/
lemma wTrace_mem_massWeightSubmodule (p : EightIdx) : wTrace p ∈ massWeightSubmodule 8 := by
  rw [wTrace_eq]
  exact Submodule.sum_mem _ fun i _ => F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The hypercharge trace contraction has mass weight eight. -/
lemma hyperchargeTrace_mem_massWeightSubmodule (p : EightIdx) :
    hyperchargeTrace p ∈ massWeightSubmodule 8 := by
  rw [hyperchargeTrace_eq]
  exact F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The twice-derived hypercharge field strength has mass weight `2 * (2 + 2)`, eight. -/
lemma hyperchargeDeriv_mem_massWeightSubmodule (d : EightIdx) :
    hyperchargeDeriv d ∈ massWeightSubmodule 8 := by
  simpa [hyperchargeDeriv, hyperchargeField] using
    F_mem_massWeightSubmodule ![d 0, d 1] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord _)

/-!

## D. The families of mass weight eight

Mass weight eight is the twice-derived field strengths together with the products of two
underived ones (`massWeightSubmodule_eight_eq`), and each field-strength symbol is a
combination of its values on the twelve coordinates of the standard basis of the gauge
algebra: eight gluon, three `W`-boson and one hypercharge direction. Sorting the symbols and
their products by gauge factor gives five kinds of family.

- Two gluon symbols form a component of a gluon pair family, and two `W`-boson symbols one of
  a `W`-boson pair family, the bi-adjoint families of section C.
- Two hypercharge symbols form a hypercharge trace contraction, and a twice-derived
  hypercharge symbol is a twice-derived hypercharge field strength; both are fixed by the
  whole gauge group.
- A gluon symbol, alone or against a symbol of another factor, carries an unpaired `su(3)`
  adjoint index. These are the colour families, whose maps out of `SuT[3, .adj]` are
  equivariant: the colour factor moves the gluon index and fixes the other factor.
- A `W`-boson symbol, alone or against a hypercharge symbol, carries an unpaired `su(2)`
  adjoint index. These are the isospin families, with maps out of `SuT[2, .adj]`.

-/

/-- The join, over all covector indices, of the spans of the gluon pair families. -/
noncomputable def gluonPairSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ p, Submodule.span ℂ (Set.range (gluonPair p))

/-- The join, over all covector indices, of the spans of the `W`-boson pair families. -/
noncomputable def wPairSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ p, Submodule.span ℂ (Set.range (wPair p))

/-- The span of the hypercharge trace contractions. -/
noncomputable def hyperchargeTraceSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ p, ℂ ∙ hyperchargeTrace p

/-- The span of the twice-derived hypercharge field strengths. -/
noncomputable def hyperchargeDerivSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ d, ℂ ∙ hyperchargeDeriv d

/-- The underived symbols of the factors other than colour, on the `W`-boson and hypercharge
  coordinates of the standard basis. -/
noncomputable def neutralVec (μ ν : Fin 1 ⊕ Fin 3) (j : Fin 3 ⊕ Fin 1) :
    fieldData.LocalCovFieldAlgebra :=
  gaugeFieldStrength ![] μ ν (GaugeAlgebra.stdBasis.coord (Sum.inr j))

/-- The symbols of the factors other than colour are fixed by the colour factor of the gauge
  group. -/
lemma repGauge_su3_neutralVec (U : specialUnitaryGroup (Fin 3) ℂ) (μ ν : Fin 1 ⊕ Fin 3) :
    ∀ j, repGaugeGroupI (U, 1, 1) (neutralVec μ ν j) = neutralVec μ ν j
  | Sum.inl i => repGauge_su3_wField U ![] μ ν i
  | Sum.inr k => by
    rw [Subsingleton.elim k 0]
    exact repGauge_hyperchargeField (U, 1, 1) ![] μ ν

/-- The index of a twice-derived symbol, the two derivative slots and the two covector
  indices. -/
abbrev DerivIdx : Type :=
  (Fin 2 → Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)

/-- The index of a mixed product with a gluon symbol, the two covector indices of the gluon
  factor, the two of the other factor, and the coordinate of the other factor. -/
abbrev MixIdx : Type :=
  (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 3 ⊕ Fin 1)

/-- The index of a family carrying one unpaired `su(3)` adjoint index at mass weight
  eight, a twice-derived gluon tower, or an underived gluon field strength against an
  underived symbol of another factor on either side. -/
abbrev ColourIdx : Type := DerivIdx ⊕ (MixIdx ⊕ MixIdx)

/-- The families carrying one unpaired `su(3)` adjoint index. -/
noncomputable def colourFamily : ColourIdx → Fin 8 → fieldData.LocalCovFieldAlgebra
  | Sum.inl p => gluonField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) =>
      fun a => gluonField ![] q.1 q.2.1 a * neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2
  | Sum.inr (Sum.inr q) =>
      fun a => neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2 * gluonField ![] q.1 q.2.1 a

/-- Each colour family is an `su(3)` adjoint family, the colour factor moves the gluon
  index and fixes the other factor. -/
lemma isEquivariant_colourAdj_colourFamily :
    ∀ i : ColourIdx, (suTensor 3).IsEquivariant ![.adj] (repGaugeGroupI.comp GaugeGroupI.ofSU3)
      (liftComponents ((colourFamily i) ∘ relabelAdjIdx su3Label))
  | Sum.inl p => isEquivariant_colourAdj_gluonField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => ColourAdj.of_law fun U => map_mul_fixed_eq_sum (repGaugeGroupI_mul _)
      (repGauge_gluonField (U, 1, 1) ![] q.1 q.2.1) (repGauge_su3_neutralVec U _ _ _)
  | Sum.inr (Sum.inr q) => ColourAdj.of_law fun U => map_fixed_mul_eq_sum (repGaugeGroupI_mul _)
      (repGauge_gluonField (U, 1, 1) ![] q.1 q.2.1) (repGauge_su3_neutralVec U _ _ _)

/-- The index of a family carrying one unpaired `su(2)` adjoint index at mass weight
  eight, a twice-derived `W`-boson tower, or an underived `W`-boson field strength against
  an underived hypercharge field strength on either side. -/
abbrev IsospinIdx : Type := DerivIdx ⊕ (EightIdx ⊕ EightIdx)

/-- The families carrying one unpaired `su(2)` adjoint index. -/
noncomputable def isospinFamily : IsospinIdx → Fin 3 → fieldData.LocalCovFieldAlgebra
  | Sum.inl p => wField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => fun i => wField ![] (q 0) (q 1) i * hyperchargeField ![] (q 2) (q 3)
  | Sum.inr (Sum.inr q) => fun i => hyperchargeField ![] (q 2) (q 3) * wField ![] (q 0) (q 1) i

/-- Each isospin family is an `su(2)` adjoint family, the isospin factor moves the
  `W`-boson index and fixes hypercharge. -/
lemma isEquivariant_isospinAdj_isospinFamily :
    ∀ i : IsospinIdx, (suTensor 2).IsEquivariant ![.adj] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((isospinFamily i) ∘ relabelAdjIdx su2Label))
  | Sum.inl p => isEquivariant_isospinAdj_wField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => IsospinAdj.of_law fun U => map_mul_fixed_eq_sum (repGaugeGroupI_mul _)
      (repGauge_wField (1, U, 1) ![] (q 0) (q 1)) (repGauge_hyperchargeField _ _ _ _)
  | Sum.inr (Sum.inr q) => IsospinAdj.of_law fun U => map_fixed_mul_eq_sum (repGaugeGroupI_mul _)
      (repGauge_wField (1, U, 1) ![] (q 0) (q 1)) (repGauge_hyperchargeField _ _ _ _)

/-- The isospin families are fixed by the colour factor, every one of their factors
  being. -/
lemma repGauge_su3_isospinFamily (U : specialUnitaryGroup (Fin 3) ℂ) :
    ∀ (i : IsospinIdx) (a : Fin 3),
      repGaugeGroupI (U, 1, 1) (isospinFamily i a) = isospinFamily i a
  | Sum.inl p, a => repGauge_su3_wField U p.1 p.2.1 p.2.2 a
  | Sum.inr (Sum.inl q), a => by
      simp only [isospinFamily, repGaugeGroupI_mul, repGauge_su3_wField, repGauge_hyperchargeField]
  | Sum.inr (Sum.inr q), a => by
      simp only [isospinFamily, repGaugeGroupI_mul, repGauge_su3_wField, repGauge_hyperchargeField]

/-- The join of the spans of the colour families. -/
noncomputable def unpairedColourSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ i : ColourIdx, Submodule.span ℂ (Set.range (colourFamily i))

/-- The join of the spans of the isospin families. -/
noncomputable def unpairedIsospinSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ i : IsospinIdx, Submodule.span ℂ (Set.range (isospinFamily i))

/-- A component of a colour family lies in the join of the colour spans. -/
lemma colourFamily_mem (i : ColourIdx) (a : Fin 8) : colourFamily i a ∈ unpairedColourSpan :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨a, rfl⟩)

/-- A component of an isospin family lies in the join of the isospin spans. -/
lemma isospinFamily_mem (i : IsospinIdx) (a : Fin 3) :
    isospinFamily i a ∈ unpairedIsospinSpan :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨a, rfl⟩)

/-- The join of the isospin families is fixed pointwise by the colour factor. -/
lemma repGauge_su3_of_mem_unpairedIsospinSpan (U : specialUnitaryGroup (Fin 3) ℂ) :
    ∀ y ∈ unpairedIsospinSpan, repGaugeGroupI (U, 1, 1) y = y :=
  isFixedBy_iSup (σ := fun U : specialUnitaryGroup (Fin 3) ℂ => repGaugeGroupI (U, 1, 1))
    (fun i => isFixedBy_span_range fun a U => repGauge_su3_isospinFamily U i a) U

/-!

## E. Mass weight eight inside the family spans

A derivative submodule lies in a submodule as soon as the symbols on the twelve standard
coordinates do, by `F_mem_iSup_span_coord`. Sorting the twice-derived symbols and the
products of two underived ones by gauge factor, as in section D, bounds mass weight eight by
the joins of the unpaired families together with the pair spans, the hypercharge trace
contractions and the twice-derived hypercharge field strengths.

-/

/-- A derivative submodule lies in a submodule as soon as the symbols on the standard
  coordinates do. -/
lemma derivSubmodule_le_of_coord_mem {n : ℕ} {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hV : ∀ (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1),
      gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord c) ∈ V) :
    derivSubmodule n ≤ V :=
  iSup_le fun l => iSup_le fun μ => iSup_le fun ν => Submodule.span_le.2 <| by
    rintro _ ⟨φ, rfl⟩
    exact iSup_span_singleton_le _ (hV l μ ν) (F_mem_iSup_span_coord l μ ν φ)

/-- The twice-derived symbols. A gluon or `W`-boson symbol is a component of an unpaired
  family, and the hypercharge symbol is a twice-derived hypercharge field strength. -/
lemma derivSubmodule_two_le :
    derivSubmodule 2 ≤ (unpairedColourSpan ⊔ unpairedIsospinSpan) ⊔ hyperchargeDerivSpan :=
  derivSubmodule_le_of_coord_mem fun l μ ν c => by
    rcases c with a | i | k
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (colourFamily_mem (Sum.inl (l, μ, ν)) a))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (isospinFamily_mem (Sum.inl (l, μ, ν)) i))
    · rw [Subsingleton.elim k 0, ← show ![l 0, l 1] = l from FinVec.etaExpand_eq l]
      exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ![l 0, l 1, μ, ν]
        (Submodule.mem_span_singleton_self _))

/-- The underived symbols lie in the join of the lines through their values on the
  standard coordinates. -/
lemma derivSubmodule_zero_le :
    derivSubmodule 0 ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1),
      ℂ ∙ gaugeFieldStrength ![] μ ν (GaugeAlgebra.stdBasis.coord c) :=
  derivSubmodule_le_of_coord_mem fun l μ ν c => by
    rw [Subsingleton.elim l ![]]
    exact mem_iSup_span₃ (fun μ ν c => gaugeFieldStrength ![] μ ν
      (GaugeAlgebra.stdBasis.coord c)) μ ν c

/-- A product of two underived symbols on standard coordinates. Two symbols of one
  non-abelian factor form a component of a pair family, two hypercharge symbols a
  hypercharge trace contraction, and every mixed product carries an unpaired non-abelian
  index. -/
lemma F_coord_mul_F_coord_mem (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1)
    (μ' ν' : Fin 1 ⊕ Fin 3) (c' : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    gaugeFieldStrength ![] μ ν (GaugeAlgebra.stdBasis.coord c)
        * gaugeFieldStrength ![] μ' ν' (GaugeAlgebra.stdBasis.coord c')
      ∈ (unpairedColourSpan ⊔ unpairedIsospinSpan)
        ⊔ (gluonPairSpan ⊔ (wPairSpan ⊔ hyperchargeTraceSpan)) := by
  rcases c with a | j <;> rcases c' with a' | j'
  · exact Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem
      ![μ, ν, μ', ν'] (Submodule.subset_span ⟨![a, a'], rfl⟩)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (colourFamily_mem (Sum.inr (Sum.inl (μ, ν, μ', ν', j'))) a))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (colourFamily_mem (Sum.inr (Sum.inr (μ', ν', μ, ν, j))) a'))
  rcases j with i | k <;> rcases j' with i' | k'
  · exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_sup_left
      (Submodule.mem_iSup_of_mem ![μ, ν, μ', ν'] (Submodule.subset_span ⟨![i, i'], rfl⟩))))
  · rw [Subsingleton.elim k' 0]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (isospinFamily_mem (Sum.inr (Sum.inl ![μ, ν, μ', ν'])) i))
  · rw [Subsingleton.elim k 0]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (isospinFamily_mem (Sum.inr (Sum.inr ![μ', ν', μ, ν])) i'))
  · rw [Subsingleton.elim k 0, Subsingleton.elim k' 0]
    exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem ![μ, ν, μ', ν'] (Submodule.mem_span_singleton.2
        ⟨1, by rw [one_smul, hyperchargeTrace_eq]; rfl⟩))))

/-- Mass weight eight is bounded by the joins of the unpaired families together with the
  pair spans, the hypercharge trace contractions and the twice-derived hypercharge field
  strengths. -/
lemma massWeightSubmodule_eight_le :
    massWeightSubmodule 8
      ≤ (unpairedColourSpan ⊔ unpairedIsospinSpan)
        ⊔ (gluonPairSpan
          ⊔ (wPairSpan ⊔ (hyperchargeTraceSpan ⊔ hyperchargeDerivSpan))) := by
  rw [massWeightSubmodule_eight_eq]
  refine sup_le (derivSubmodule_two_le.trans (sup_le le_sup_left (le_sup_of_le_right
    (le_sup_of_le_right (le_sup_of_le_right le_sup_right))))) ?_
  have hmul : derivSubmodule 0 * derivSubmodule 0 ≤ _ :=
    Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (derivSubmodule_zero_le hx)
      (derivSubmodule_zero_le hy)
  exact (hmul.trans (iSup_span_mul_iSup_span_le _ _ F_coord_mul_F_coord_mem)).trans
    (sup_le_sup_left (sup_le_sup_left (sup_le_sup_left le_sup_left _) _) _)

/-!

## F. The unpaired non-abelian adjoint indices

A family carrying one unpaired adjoint index of a non-abelian factor has no gauge invariant
in its span at all, the adjoint representations of `su(3)` and `su(2)` having no invariant
vector: `ColourAdj.reducesInvariantsTo_bot` and its `su(2)` twin reduce such a span to
`⊥` for that factor. The colour families are reduced first, with the isospin join carried
in the target, since the colour factor fixes every isospin family; the isospin families
are reduced after that.

-/

/-- The joins of the unpaired families reduce to `⊥` for the gauge group, the colour
  families for the colour factor, with the colour-fixed isospin join kept in the target, and
  then the isospin families for the isospin factor. -/
lemma reducesInvariantsTo_unpaired :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g)
      (unpairedColourSpan ⊔ unpairedIsospinSpan) ⊥ := by
  classical
  have hfix : IsFixedBy (fun U : specialUnitaryGroup (Fin 3) ℂ => repGaugeGroupI (U, 1, 1))
      unpairedIsospinSpan := repGauge_su3_of_mem_unpairedIsospinSpan
  have hcolour : ReducesInvariantsTo
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGaugeGroupI (U, 1, 1))
      (unpairedColourSpan ⊔ unpairedIsospinSpan) unpairedIsospinSpan :=
    ((ReducesInvariantsTo.iSup
        (fun i => ColourAdj.reducesInvariantsTo_bot (isEquivariant_colourAdj_colourFamily i))
      (fun i => ColourAdj.isStableUnder_span (isEquivariant_colourAdj_colourFamily i))
      isStableUnder_bot).mono_right bot_le).sup (reducesInvariantsTo_of_le le_rfl)
      hfix.isStableUnder hfix.isStableUnder
  have hisospin : ReducesInvariantsTo
      (fun U : specialUnitaryGroup (Fin 2) ℂ => repGaugeGroupI (1, U, 1)) unpairedIsospinSpan ⊥ :=
    ReducesInvariantsTo.iSup
        (fun i => IsospinAdj.reducesInvariantsTo_bot (isEquivariant_isospinAdj_isospinFamily i))
      (fun i => IsospinAdj.isStableUnder_span (isEquivariant_isospinAdj_isospinFamily i))
      isStableUnder_bot
  exact (hcolour.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) (fun U => (U, 1, 1))).trans
    (hisospin.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) (fun U => (1, U, 1)))

/-!

## G. The gauge invariants of mass weight eight

Section E bounds mass weight eight by the unpaired joins, the two non-abelian pair spans and
the two hypercharge spans. Section F reduces the unpaired joins to `⊥`. Each pair span
reduces to its trace contractions by `ColourAdjAdj.reducesInvariantsTo_span_traceContraction` and
its `su(2)` twin, and the
two hypercharge spans are fixed pointwise by the gauge group and reduce to themselves.
`ReducesInvariantsTo.sup` joins the parts, asking stability of every part but the first and
of the target; no independence of the parts is needed.

The section closes with the converse, that the gauge span is made of gauge invariants of mass
weight eight already.

-/

/-- The span of the gluon trace contractions. -/
noncomputable def gluonTraceSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ p, ℂ ∙ gluonTrace p

/-- The span of the `W`-boson trace contractions. -/
noncomputable def wTraceSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra := ⨆ p, ℂ ∙ wTrace p

/-- The span of the three underived trace contractions, over all covector indices, the
  gauge invariants of mass weight eight that the bi-adjoint classification produces. -/
noncomputable def traceContractionEightSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  gluonTraceSpan ⊔ (wTraceSpan ⊔ hyperchargeTraceSpan)

/-- The gluon pair spans are stable under the gauge group. -/
lemma isStableUnder_gluonPairSpan :
    IsStableUnder (fun g : GaugeGroupI => repGaugeGroupI g) gluonPairSpan :=
  isStableUnder_iSup fun p g =>
    span_stable_of_map_eq_sum (gluonPair p) _ (repGaugeGroupI_gluonPair_eq_sum p g)

/-- The `W`-boson pair spans are stable under the gauge group. -/
lemma isStableUnder_wPairSpan :
    IsStableUnder (fun g : GaugeGroupI => repGaugeGroupI g) wPairSpan :=
  isStableUnder_iSup fun p g =>
    span_stable_of_map_eq_sum (wPair p) _ (repGaugeGroupI_wPair_eq_sum p g)

/-- The hypercharge trace contractions are fixed pointwise by the gauge group. -/
lemma repGauge_of_mem_hyperchargeTraceSpan (g : GaugeGroupI) :
    ∀ y ∈ hyperchargeTraceSpan, repGaugeGroupI g y = y :=
  map_eq_self_of_mem_iSup_span _ _ (repGauge_hyperchargeTrace g)

/-- The twice-derived hypercharge field strengths are fixed pointwise by the gauge
  group. -/
lemma repGauge_of_mem_hyperchargeDerivSpan (g : GaugeGroupI) :
    ∀ y ∈ hyperchargeDerivSpan, repGaugeGroupI g y = y :=
  map_eq_self_of_mem_iSup_span _ _ (repGauge_hyperchargeDeriv g)

/-- The gauge span is a space of gauge invariants of mass weight eight. Each generator is
  fixed by the gauge group and has mass weight eight by section C. This is the converse of
  the classification. -/
lemma traceContractionEightSpan_sup_hyperchargeDerivSpan_le :
    traceContractionEightSpan ⊔ hyperchargeDerivSpan
      ≤ massWeightSubmodule 8 ⊓ repGaugeGroupI.invariants :=
  sup_le (sup_le (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
      ⟨gluonTrace_mem_massWeightSubmodule p,
        (Representation.mem_invariants _ _).2 (repGauge_gluonTrace · p)⟩)
    (sup_le (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
        ⟨wTrace_mem_massWeightSubmodule p,
          (Representation.mem_invariants _ _).2 (repGauge_wTrace · p)⟩)
      (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
        ⟨hyperchargeTrace_mem_massWeightSubmodule p,
          (Representation.mem_invariants _ _).2 (repGauge_hyperchargeTrace · p)⟩)))
    (iSup_span_singleton_le _ fun d => Submodule.mem_inf.2
      ⟨hyperchargeDeriv_mem_massWeightSubmodule d,
        (Representation.mem_invariants _ _).2 (repGauge_hyperchargeDeriv · d)⟩)

/-- The gauge span is fixed pointwise by the gauge group. -/
lemma isFixedBy_traceContractionEightSpan_sup :
    IsFixedBy (fun g : GaugeGroupI => repGaugeGroupI g)
      (traceContractionEightSpan ⊔ hyperchargeDerivSpan) := fun g _ hy =>
  (Representation.mem_invariants _ _).1
    (Submodule.mem_inf.1 (traceContractionEightSpan_sup_hyperchargeDerivSpan_le hy)).2 g

/-- The gluon pair spans reduce, for the gauge group, to the gluon trace contractions, since each
  gluon pair family is bi-adjoint for the colour factor. -/
lemma reducesInvariantsTo_gluonPairSpan :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) gluonPairSpan gluonTraceSpan := by
  classical
  exact ReducesInvariantsTo.iSup
    (fun p => ((ColourAdjAdj.reducesInvariantsTo_span_traceContraction
      (isEquivariant_colourAdjAdj_gluonPair p)).comp (σ := fun g : GaugeGroupI => repGaugeGroupI g)
        (fun U => (U, 1, 1))).mono_right (le_iSup (fun p => ℂ ∙ gluonTrace p) p))
    (fun p g => span_stable_of_map_eq_sum (gluonPair p) _ (repGaugeGroupI_gluonPair_eq_sum p g))
    (isFixedBy_iSup fun p => isFixedBy_span_singleton (repGauge_gluonTrace · p)).isStableUnder

/-- The `W`-boson pair spans reduce, for the gauge group, to the `W`-boson trace contractions, since
  each `W`-boson pair family is bi-adjoint for the isospin factor. -/
lemma reducesInvariantsTo_wPairSpan :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) wPairSpan wTraceSpan := by
  classical
  exact ReducesInvariantsTo.iSup
    (fun p => ((IsospinAdjAdj.reducesInvariantsTo_span_traceContraction
      (isEquivariant_isospinAdjAdj_wPair p)).comp (σ := fun g : GaugeGroupI => repGaugeGroupI g)
        (fun U => (1, U, 1))).mono_right (le_iSup (fun p => ℂ ∙ wTrace p) p))
    (fun p g => span_stable_of_map_eq_sum (wPair p) _ (repGaugeGroupI_wPair_eq_sum p g))
    (isFixedBy_iSup fun p => isFixedBy_span_singleton (repGauge_wTrace · p)).isStableUnder

/-- Mass weight eight reduces, for the gauge group, to the three underived trace
  contractions and the twice-derived hypercharge field strengths. Of the parts bounding it,
  the unpaired joins reduce to `⊥`, the pair spans to their trace contractions, and the
  hypercharge spans are already fixed. -/
lemma reducesInvariantsTo_traceContractionEightSpan_sup :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (massWeightSubmodule 8)
      (traceContractionEightSpan ⊔ hyperchargeDerivSpan) := by
  have hW := isFixedBy_traceContractionEightSpan_sup.isStableUnder
  have hH : IsFixedBy (fun g : GaugeGroupI => repGaugeGroupI g)
      (hyperchargeTraceSpan ⊔ hyperchargeDerivSpan) :=
    IsFixedBy.sup (fun g => repGauge_of_mem_hyperchargeTraceSpan g)
      (fun g => repGauge_of_mem_hyperchargeDerivSpan g)
  -- the pair spans and the hypercharge spans, joined
  have hrest := (reducesInvariantsTo_gluonPairSpan.mono_right
      (le_sup_of_le_left le_sup_left)).sup ((reducesInvariantsTo_wPairSpan.mono_right
        (le_sup_of_le_left (le_sup_of_le_right le_sup_left))).sup
      (reducesInvariantsTo_of_le (sup_le (le_sup_of_le_left (le_sup_of_le_right le_sup_right))
        le_sup_right)) hH.isStableUnder hW)
    (isStableUnder_wPairSpan.sup hH.isStableUnder) hW
  exact ((reducesInvariantsTo_unpaired.mono_right bot_le).sup hrest
    (isStableUnder_gluonPairSpan.sup (isStableUnder_wPairSpan.sup hH.isStableUnder))
    hW).mono_left massWeightSubmodule_eight_le

/-!

## H. The Lorentz classification of the mass-weight eight invariants

A product of two underived field-strength symbols carries four covector indices and
nothing else, so as a family indexed by those four it is a quadruple Lorentz tensor in the
sense that its map out of `ℂT(fun _ : Fin 4 => .up)` is equivariant: `repLorentz_F` at no covariant
derivatives moves each covector index by the Lorentz matrix of the `SL(2,ℂ)` element, and
`repLorentzGroup_mul` carries that
through the product. The three trace contractions are sums of such products over a gauge
index, and a finite sum of quadruple Lorentz tensors is one again. So is the twice-derived
hypercharge field strength, whose two derivative slots and two covector indices are four
four-vector indices as well. The four spans of section G are exactly the spans of these
four families, and `ComplexVector.reducesInvariantsTo_span_contractionTensor` reduces each, for the
Lorentz group, to the span of its four contractions.

What is left is spanned by the four Lorentz contractions of each family,
`liftComponents T (RankFour.contractionTensor i)`: the metric contractions of the slot pairs
`(0,1)(2,3)`, `(0,2)(1,3)` and `(0,3)(1,2)` and the Levi-Civita contraction. These are
sixteen spanning vectors, `lorentzContractionEightSpan`, which is the output of the
classification.

Half of them are redundant. In each of the four families the last two slots are the two
covector indices of one field strength: of the second factor for the three trace families,
and of the only factor, after the two derivative slots, for the twice-derived hypercharge
field strength. So `F_antisymm` makes each family antisymmetric under exchanging slots `2` and
`3` (`gluonTrace_comp_swap_two_three` and its three companions), and
`RankFour.span_range_contractionTensor_of_antisymm` then removes two contractions of each.
The `(0,1)(2,3)` contraction vanishes, and the `(0,3)(1,2)` one is minus the `(0,2)(1,3)`
one (`quadContractionSpan_eq_of_antisymm`). Eight spanning vectors remain
(`lorentzContractionEightSpan_eq`).

* six underived ones, quadratic in the field strengths. For each of the gluon, `W`-boson and
  hypercharge trace families these are the `(0,2)(1,3)` metric contraction, of the kinetic
  shape `η^{μρ} η^{νσ} F_{μν} F_{ρσ}`, and the Levi-Civita contraction, of the theta shape
  `ε^{μνρσ} F_{μν} F_{ρσ}`, the gauge index summed in both;
* two linear in the twice-derived hypercharge field strength, `η^{μρ} η^{νσ} ∇_μ ∇_ν B_{ρσ}`
  and `ε^{μνρσ} ∇_μ ∇_ν B_{ρσ}`.

Each is the plain component sum of `RankFour.liftComponents_contractionTensor`, repeated
indices summed, against the integer metric `diag(1,-1,-1,-1)` or the symbol taking the value
`1` at `(t, x, y, z)`, with no further normalisation; the shapes are not claimed to carry the
conventional factors of an action. The last two are kept because nothing in the laws of the gauge
sector relates the two derivative slots, no symmetry of the derivatives, no Bianchi identity, no
equation of motion and no quotient by total derivatives. In the covariant field algebra of the
Standard Model the hypercharge derivatives do commute and the last two vanish
(`LocalCovFieldAlgebra.gaugeSector_lorentzContractionEightSpan_eq_traceFamilies`). The eight
form a spanning family, not a basis. None is shown to be nonzero, and no independence among them
is claimed.

-/

/-- The Lorentz transformation of an underived field-strength symbol. It is the general law
  `repLorentz_F` at no covariant derivatives, where the sum over the derivative slots is
  a single term, written with the two covector rotations gathered into one coefficient. -/
lemma repLorentz_F_underived (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentzGroup Λ (gaugeFieldStrength ![] μ ν φ)
      = ∑ a : Fin 1 ⊕ Fin 3, ∑ b : Fin 1 ⊕ Fin 3,
        ((((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ)) • gaugeFieldStrength ![] a b φ := by
  rw [repLorentz_F Λ 0 ![] μ ν φ,
    Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
      (fun hb => absurd (Finset.mem_univ _) hb), Fin.prod_univ_zero, one_smul]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_smul]

/-- A product of two double combinations is a combination indexed by quadruples. -/
lemma sum_mul_sum_eq_sum_pi_four (c c' : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℂ)
    (X Y : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra) :
    (∑ a, ∑ b, c a b • X a b) * (∑ x, ∑ y, c' x y • Y x y)
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
        (c (d 0) (d 1) * c' (d 2) (d 3)) • (X (d 0) (d 1) * Y (d 2) (d 3)) := by
  rw [RankFour.sum_pi_four, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fintype.sum_mul_sum, smul_mul_smul_comm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  exact Finset.sum_comm

/-- A product of two underived field-strength symbols, viewed as a family indexed by the
  four covector indices it carries, is a quadruple Lorentz tensor. -/
lemma isEquivariant_up_F_mul (φ ψ : Module.Dual ℝ GaugeAlgebra) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents
      fun d : Fin 4 → Fin 1 ⊕ Fin 3 => gaugeFieldStrength ![] (d 0) (d 1) φ * gaugeFieldStrength ![]
        (d 2) (d 3) ψ) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentzGroup_mul, repLorentz_F_underived g (l 0) (l 1) φ,
    repLorentz_F_underived g (l 2) (l 3) ψ, sum_mul_sum_eq_sum_pi_four]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.prod_univ_four, mul_assoc]

/-- A finite sum of quadruple Lorentz tensors is a quadruple Lorentz tensor, the
  transformation law is linear in the family. -/
lemma isEquivariant_up_sum {ι : Type} [Fintype ι] {T : ι → (Fin 4 → Fin 1 ⊕ Fin 3) →
    fieldData.LocalCovFieldAlgebra}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents (T i))) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents fun d => ∑ i, T i d) := by
  rw [liftComponents_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

/-- A family of four four-vector indices whose members are sums of products of two
  underived field-strength symbols is a quadruple Lorentz tensor. -/
lemma isEquivariant_up_of_eq_sum {ι : Type} [Fintype ι]
    {T : EightIdx → fieldData.LocalCovFieldAlgebra}
    (φ : ι → Module.Dual ℝ GaugeAlgebra)
    (hT : ∀ d, T d = ∑ i, gaugeFieldStrength ![] (d 0) (d 1) (φ i) * gaugeFieldStrength ![] (d 2) (d
      3) (φ i)) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents T) := by
  rw [show T = fun d => ∑ i, gaugeFieldStrength ![] (d 0) (d 1) (φ i) * gaugeFieldStrength ![] (d 2)
    (d 3) (φ i) from funext hT]
  exact isEquivariant_up_sum fun _ => isEquivariant_up_F_mul _ _

/-- The gluon trace contractions, read as a family of four four-vector indices, form a quadruple
  Lorentz tensor, being a sum over the colour index of products of two underived field-strength
  symbols. -/
lemma isEquivariant_up_gluonTrace :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents gluonTrace) :=
  isEquivariant_up_of_eq_sum (fun a : Fin 8 => GaugeAlgebra.stdBasis.coord (Sum.inl a))
    gluonTrace_eq

/-- The `W`-boson trace contractions form a quadruple Lorentz tensor. -/
lemma isEquivariant_up_wTrace :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents wTrace) :=
  isEquivariant_up_of_eq_sum
    (fun i : Fin 3 => GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inl i))) wTrace_eq

/-- The hypercharge trace contractions form a quadruple Lorentz tensor. -/
lemma isEquivariant_up_hyperchargeTrace :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents hyperchargeTrace) := by
  rw [show hyperchargeTrace = fun d =>
      gaugeFieldStrength ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0)))
        * gaugeFieldStrength ![] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0)))
          from
    funext hyperchargeTrace_eq]
  exact isEquivariant_up_F_mul _ _

/-- The twice-derived hypercharge field strengths, read as a family of four four-vector
  indices, form a quadruple Lorentz tensor, since the two derivative slots and the two covector
  indices all rotate. This is the second shape of mass weight eight. -/
lemma isEquivariant_up_hyperchargeDeriv :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents hyperchargeDeriv) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  simp only [hyperchargeDeriv, hyperchargeField]
  rw [repLorentz_F g 2 ![l 0, l 1] (l 2) (l 3), sum_pi_fin_two, RankFour.sum_pi_four]
  simp only [Finset.smul_sum, smul_smul, Fin.prod_univ_two, Fin.prod_univ_four, mul_assoc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]

/-- The gluon trace contractions are antisymmetric in the last two covector indices, by
  `F_antisymm` in the second factor. -/
lemma gluonTrace_comp_swap_two_three (d : EightIdx) :
    gluonTrace (d ∘ Equiv.swap 2 3) = -gluonTrace d := by
  simp [gluonTrace_eq, gluonField, Equiv.swap_apply_def, F_antisymm ![] (d 2) (d 3)]

/-- The `W`-boson trace contractions are antisymmetric in the last two covector indices. -/
lemma wTrace_comp_swap_two_three (d : EightIdx) :
    wTrace (d ∘ Equiv.swap 2 3) = -wTrace d := by
  simp [wTrace_eq, wField, Equiv.swap_apply_def, F_antisymm ![] (d 2) (d 3)]

/-- The hypercharge trace contractions are antisymmetric in the last two covector indices. -/
lemma hyperchargeTrace_comp_swap_two_three (d : EightIdx) :
    hyperchargeTrace (d ∘ Equiv.swap 2 3) = -hyperchargeTrace d := by
  simp [hyperchargeTrace_eq, hyperchargeField, Equiv.swap_apply_def,
    F_antisymm ![] (d 2) (d 3)]

/-- The twice-derived hypercharge field strengths are antisymmetric in their two covector
  indices, the last two slots, by `F_antisymm` at two covariant derivatives. Nothing is
  assumed about the two derivative slots. -/
lemma hyperchargeDeriv_comp_swap_two_three (d : EightIdx) :
    hyperchargeDeriv (d ∘ Equiv.swap 2 3) = -hyperchargeDeriv d := by
  simp [hyperchargeDeriv, hyperchargeField, Equiv.swap_apply_def,
    F_antisymm ![d 0, d 1] (d 2) (d 3)]

/-- The span of the four Lorentz contractions of a quadruple Lorentz tensor, the images of
  the three metric pairings and of the Levi-Civita symbol. -/
noncomputable def quadContractionSpan
    (T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra) :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  Submodule.span ℂ (Set.range fun i => liftComponents T (RankFour.contractionTensor i))

/-- The span of the four Lorentz contractions of a quadruple Lorentz family lies in the
  span of its components, since each contraction is a combination of components with constant
  coefficients. -/
lemma quadContractionSpan_le_span {T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra} :
    quadContractionSpan T ≤ Submodule.span ℂ (Set.range T) :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => by
    rw [SetLike.mem_coe, ← range_liftComponents (S := complexLorentzTensor)
        (c := fun _ : Fin 4 => .up)]
    exact LinearMap.mem_range_self _ _

/-- The span of the four Lorentz contractions of a quadruple Lorentz family is a space of
  Lorentz invariants, the four contractions being invariant by `RankFour`. -/
lemma quadContractionSpan_le_lorentzInvariants
    {T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hT : complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents T)) :
    quadContractionSpan T ≤ repLorentzGroup.invariants :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i =>
    (Representation.mem_invariants _ _).2
      (hT.rep_map_of_invariant (RankFour.contractionTensor_invariant i))

/-- For a quadruple family antisymmetric in its last two slots the four Lorentz contractions
  reduce to two, the `(0,2)(1,3)` metric contraction and the Levi-Civita one. The
  `(0,1)(2,3)` metric contraction vanishes and the `(0,3)(1,2)` one is minus the
  `(0,2)(1,3)` one. -/
lemma quadContractionSpan_eq_of_antisymm
    {T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ d, T (d ∘ Equiv.swap 2 3) = -T d) :
    quadContractionSpan T = Submodule.span ℂ {liftComponents T (RankFour.contractionTensor 1),
      liftComponents T (RankFour.contractionTensor 3)} :=
  RankFour.span_range_contractionTensor_of_antisymm (liftComponents_comp_permT_eq_neg _ _ hT)

/-- The span of the four Lorentz contractions of each of the three underived
  trace-contraction families and of the twice-derived hypercharge family, the gauge and
  Lorentz invariants of mass weight eight that the two classifications together produce. -/
noncomputable def lorentzContractionEightSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  quadContractionSpan gluonTrace
    ⊔ (quadContractionSpan wTrace
      ⊔ (quadContractionSpan hyperchargeTrace ⊔ quadContractionSpan hyperchargeDeriv))

/-- The Lorentz contraction span sits inside the gauge span. Each of its four blocks is
  spanned by the four contractions of a quadruple Lorentz family whose components generate
  the matching block of the gauge span. -/
lemma lorentzContractionEightSpan_le_traceContractionEightSpan_sup :
    lorentzContractionEightSpan ≤ traceContractionEightSpan ⊔ hyperchargeDerivSpan :=
  sup_le ((quadContractionSpan_le_span (T := gluonTrace)).trans
      (Submodule.span_range_eq_iSup.trans_le (le_sup_of_le_left le_sup_left)))
    (sup_le ((quadContractionSpan_le_span (T := wTrace)).trans
        (Submodule.span_range_eq_iSup.trans_le
          (le_sup_of_le_left (le_sup_of_le_right le_sup_left))))
      (sup_le ((quadContractionSpan_le_span (T := hyperchargeTrace)).trans
          (Submodule.span_range_eq_iSup.trans_le
            (le_sup_of_le_left (le_sup_of_le_right le_sup_right))))
        ((quadContractionSpan_le_span (T := hyperchargeDeriv)).trans
          (Submodule.span_range_eq_iSup.trans_le le_sup_right))))

/-- The Lorentz contraction span is a space of gauge invariants, since it lies in the gauge
  span, whose generators the gauge group fixes. -/
lemma lorentzContractionEightSpan_le_invariants :
    lorentzContractionEightSpan ≤ repGaugeGroupI.invariants :=
  lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_right)

open RankFour in
/-- The Lorentz contraction span is spanned by eight of its sixteen generators, for each
  family the `(0,2)(1,3)` metric contraction and the Levi-Civita contraction. All four families
  are antisymmetric in their last two slots by `F_antisymm`, which removes the other two
  contractions of each. -/
lemma lorentzContractionEightSpan_eq :
    lorentzContractionEightSpan
      = Submodule.span ℂ {liftComponents gluonTrace (contractionTensor 1),
          liftComponents gluonTrace (contractionTensor 3)}
        ⊔ (Submodule.span ℂ {liftComponents wTrace (contractionTensor 1),
            liftComponents wTrace (contractionTensor 3)}
          ⊔ (Submodule.span ℂ {liftComponents hyperchargeTrace (contractionTensor 1),
              liftComponents hyperchargeTrace (contractionTensor 3)}
            ⊔ Submodule.span ℂ {liftComponents hyperchargeDeriv (contractionTensor 1),
              liftComponents hyperchargeDeriv (contractionTensor 3)})) := by
  rw [lorentzContractionEightSpan,
    quadContractionSpan_eq_of_antisymm gluonTrace_comp_swap_two_three,
    quadContractionSpan_eq_of_antisymm wTrace_comp_swap_two_three,
    quadContractionSpan_eq_of_antisymm hyperchargeTrace_comp_swap_two_three,
    quadContractionSpan_eq_of_antisymm hyperchargeDeriv_comp_swap_two_three]

/-!

## I. The Lorentz contraction span as invariants of mass weight eight

The converse of the Lorentz classification is that the Lorentz contraction span is made of gauge
and Lorentz invariants of mass weight eight. Its gauge invariance and its mass weight pass
to it from the gauge span, which contains it; Lorentz invariance comes from `RankFour`
directly, each block being spanned by the four contractions of a quadruple Lorentz family.

-/

/-- The Lorentz contraction span lies in the mass-weight eight submodule. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    lorentzContractionEightSpan ≤ massWeightSubmodule 8 :=
  lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_left)

/-- The Lorentz contraction span is a space of Lorentz invariants. -/
lemma lorentzContractionEightSpan_le_lorentzInvariants :
    lorentzContractionEightSpan ≤ repLorentzGroup.invariants :=
  sup_le (quadContractionSpan_le_lorentzInvariants isEquivariant_up_gluonTrace)
    (sup_le (quadContractionSpan_le_lorentzInvariants isEquivariant_up_wTrace)
      (sup_le (quadContractionSpan_le_lorentzInvariants isEquivariant_up_hyperchargeTrace)
        (quadContractionSpan_le_lorentzInvariants isEquivariant_up_hyperchargeDeriv)))

/-- The Lorentz contraction span is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionEightSpan :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) lorentzContractionEightSpan :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => (Representation.mem_invariants _ _).1
      (lorentzContractionEightSpan_le_invariants hy) g,
      fun Λ _ hy => (Representation.mem_invariants _ _).1
        (lorentzContractionEightSpan_le_lorentzInvariants hy) Λ⟩

/-!

## J. The classifications as equivalences

The gauge reduction of section G and the Lorentz reduction of section H compose, and the
composite needs no stability or fixedness of the gauge span under the Lorentz group. The
converse, sections G and I, turns each reduction into an equivalence through
`ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff`.

-/

/-- The gauge sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the four Lorentz contractions of each of the four families. The gauge group
  leaves the trace contractions and the twice-derived hypercharge field strengths; each of
  the four spans is spanned by a quadruple Lorentz tensor and reduces, for the Lorentz
  group, to the span of its four contractions. Two of the four suffice for each family, by
  `lorentzContractionEightSpan_eq`. -/
lemma reducesInvariantsTo_lorentzContractionEightSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmodule 8)
      lorentzContractionEightSpan := by
  have hW : IsStableUnder (fun g : SL(2,ℂ) => repLorentzGroup g) lorentzContractionEightSpan :=
    fun g _ hy => by
      rw [(Representation.mem_invariants _ _).1
        (lorentzContractionEightSpan_le_lorentzInvariants hy) g]
      exact hy
  have hst : ∀ {T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra},
      complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents T) →
      IsStableUnder (fun g : SL(2,ℂ) => repLorentzGroup g) (Submodule.span ℂ (Set.range T)) :=
    fun hT => by
      rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 4 => .up)]
      exact hT.isStableUnder_range
  have hred : ∀ {T : (Fin 4 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra},
      complexLorentzTensor.IsEquivariant (fun _ : Fin 4 => .up) repLorentzGroup
      (liftComponents T) →
      quadContractionSpan T ≤ lorentzContractionEightSpan →
      ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentzGroup g) (Submodule.span ℂ (Set.range T))
        lorentzContractionEightSpan :=
    fun hT hle => by
      rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 4 => .up)]
      exact (ComplexVector.reducesInvariantsTo_span_contractionTensor hT).mono_right hle
  -- the Lorentz stage, on the four spans the gauge stage leaves
  have hlorentz : ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentzGroup g)
      (traceContractionEightSpan ⊔ hyperchargeDerivSpan) lorentzContractionEightSpan := by
    have hsrc : traceContractionEightSpan ⊔ hyperchargeDerivSpan
        = Submodule.span ℂ (Set.range gluonTrace) ⊔ (Submodule.span ℂ (Set.range wTrace)
          ⊔ (Submodule.span ℂ (Set.range hyperchargeTrace)
            ⊔ Submodule.span ℂ (Set.range hyperchargeDeriv))) := by
      simp only [traceContractionEightSpan, gluonTraceSpan, wTraceSpan, hyperchargeTraceSpan,
        hyperchargeDerivSpan, ← Submodule.span_range_eq_iSup, sup_assoc]
    rw [hsrc]
    exact (hred isEquivariant_up_gluonTrace le_sup_left).sup
      ((hred isEquivariant_up_wTrace (le_sup_of_le_right le_sup_left)).sup
        ((hred isEquivariant_up_hyperchargeTrace
            (le_sup_of_le_right (le_sup_of_le_right le_sup_left))).sup
          (hred isEquivariant_up_hyperchargeDeriv
            (le_sup_of_le_right (le_sup_of_le_right le_sup_right)))
          (hst isEquivariant_up_hyperchargeDeriv) hW)
        ((hst isEquivariant_up_hyperchargeTrace).sup
          (hst isEquivariant_up_hyperchargeDeriv)) hW)
      ((hst isEquivariant_up_wTrace).sup ((hst isEquivariant_up_hyperchargeTrace).sup
        (hst isEquivariant_up_hyperchargeDeriv))) hW
  exact (ReducesInvariantsTo.ofGauge reducesInvariantsTo_traceContractionEightSpan_sup).trans
    (ReducesInvariantsTo.ofLorentz hlorentz)

/-- The gauge classification of mass weight eight as an equivalence. An element of
  `massWeightSubmodule 8 ⊔ S` is gauge invariant exactly when it is a combination of the
  three underived trace contractions and the twice-derived hypercharge field strengths up
  to a gauge-invariant remainder in `S`. -/
lemma mem_massWeightSubmodule_eight_sup_and_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ ∀ g : GaugeGroupI, repGaugeGroupI g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ x - y ∈ traceContractionEightSpan ⊔ hyperchargeDerivSpan :=
  reducesInvariantsTo_traceContractionEightSpan_sup.mem_sup_and_forall_eq_self_iff
    (traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_left)
    isFixedBy_traceContractionEightSpan_sup hS x

/-- The gauge and Lorentz classification of mass weight eight as an equivalence. An
  element of `massWeightSubmodule 8 ⊔ S` is fixed by both groups exactly when it is a
  combination of the four Lorentz contractions of the four families of section H up to a
  remainder in `S` fixed by both groups. The version with two contractions of each family is
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_reduced`. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ lorentzContractionEightSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    reducesInvariantsTo_lorentzContractionEightSpan
    lorentzContractionEightSpan_le_massWeightSubmodule isFixedBy_lorentzContractionEightSpan
    hS hSL x

open RankFour in
/-- The same equivalence with the eight generators of `lorentzContractionEightSpan_eq`, for
  each of the three underived trace families its `(0,2)(1,3)` metric contraction, of the shape
  `η^{μρ} η^{νσ} F_{μν} F_{ρσ}`, and its Levi-Civita contraction, of the shape
  `ε^{μνρσ} F_{μν} F_{ρσ}`, and for the twice-derived hypercharge field strengths
  `η^{μρ} η^{νσ} ∇_μ ∇_ν B_{ρσ}` and `ε^{μνρσ} ∇_μ ∇_ν B_{ρσ}`. The eight span; they are not
  shown to be independent or nonzero. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_reduced
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ Submodule.span ℂ {liftComponents gluonTrace (contractionTensor 1),
              liftComponents gluonTrace (contractionTensor 3)}
            ⊔ (Submodule.span ℂ {liftComponents wTrace (contractionTensor 1),
                liftComponents wTrace (contractionTensor 3)}
              ⊔ (Submodule.span ℂ {liftComponents hyperchargeTrace (contractionTensor 1),
                  liftComponents hyperchargeTrace (contractionTensor 3)}
                ⊔ Submodule.span ℂ {liftComponents hyperchargeDeriv (contractionTensor 1),
                  liftComponents hyperchargeDeriv (contractionTensor 3)})) := by
  rw [← lorentzContractionEightSpan_eq]
  exact mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff S hS hSL x

end GaugeSector

end StandardModel
