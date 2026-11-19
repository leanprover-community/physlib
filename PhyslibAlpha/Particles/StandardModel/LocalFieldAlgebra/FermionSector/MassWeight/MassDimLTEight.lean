/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Components
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.GaugeWeight
public import PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction
public import PhyslibAlpha.Relativity.Bispinors.Pauli.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.InvariantReduction
/-!
# The invariants below mass weight eight

## i. Overview

The fermion sector carries nothing invariant below mass weight eight. Weights one, two
and four are trivial submodules and weights three, five and seven are single fermion
towers, which carry a nonzero hypercharge and so no gauge singlet. That leaves mass
weight six, the products of two underived towers, and it is the interesting one: it is
where a Dirac mass term `ψ̄ ψ` would sit, and the statement proved here is that no such
term exists.

The two symmetries cooperate. Gauge invariance cuts the hundred pairings of two fermion
symbols down to the ten conjugate ones, `d bard`, `bard d`, `u baru`, ..., `bare e`,
every other pairing having hypercharges that cannot cancel. This is
`massWeightSubmoduleGaugeWeightSix_piece_zero` of the gauge weight decomposition. Each
surviving pairing is then a product of two symbols of opposite chirality, one dotted and
one undotted, since a species and its conjugate always sit in opposite Weyl
representations. A pair of opposite-chirality spinor indices with nothing else to
contract against admits no invariant at all — `complexLorentzTensor.invariants_upL_upR_eq_bot`
— so each pairing contributes nothing and mass weight six is left empty.

That is the absence of a Dirac mass term in the Standard Model, and it is why the fermion
masses have to come from the Yukawa sector instead. The Higgs doublet supplies the missing
index, and its own mass weight makes the Yukawa terms weight eight.

The products of opposite-chirality one-index families, `Lorentz.isEquivariant_downLDownR_mul`
and its swap, live in `PhyslibAlpha.Relativity.Fermions.Weyl.Metric`; they take
the chirality law of each factor, contragredient to the left-handed Weyl representation or to
its conjugate. The chirality bookkeeping
of the species is done once here and reused at mass weight eight, in `MassDimEight`, which
imports this file. The five undotted species are indexed by
`LeftIdx` and the five dotted ones by `RightIdx`, and `leftComp` and `rightComp` list
their components with the spinor index singled out.

The final statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`
needs `0 < w` as well as `w < 8`. At `w = 0` the mass-weight submodule contains the
scalars, so `1` is an invariant of weight zero lying in no `S`.

## ii. Key results

- `leftComp`, `rightComp` : the components of the five undotted and the five dotted species,
  presented as two-element families in the spinor index.
- `mem_of_invariant_of_mem_massWeightSubmoduleSix_sup` : mass weight six carries no invariant,
  there being no Dirac mass term.
- `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff` : the classification below
  mass weight eight as an equivalence. An element of `massWeightSubmodule w ⊔ S` for `0 < w < 8`
  is fixed by both groups exactly when it is itself an element of `S` fixed by both groups.

## iii. Table of contents

- A. The five undotted and the five dotted species
- B. The ranges of the symbol maps inside the chirality spans
- C. Mass weight six with no Dirac mass term
- D. The classification below mass weight eight

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace FermionSector

/-!

## A. The five undotted and the five dotted species

Each of the ten fermion species sits in one of the two Weyl representations, and a
species and its conjugate always sit in opposite ones. The five undotted species are
`bard`, `baru`, `Q`, `L` and `bare`, the five dotted ones `d`, `u`, `barQ`, `barL` and
`e`. Indexing each list by the generation and the remaining internal indices, `leftComp`
and `rightComp` present every fermion component as a two-element family in its spinor
index, which is the shape the chirality laws `repLorentz_leftComp` and `repLorentz_rightComp`
are stated in.

-/

/-- An index for the components of the five undotted fermion species, the generation
  together with the colour and isospin the species carries. -/
inductive LeftIdx
  | bard (f : Fin 3) (c : Fin 3)
  | baru (f : Fin 3) (c : Fin 3)
  | Q (f : Fin 3) (c : Fin 3) (s : Fin 2)
  | L (f : Fin 3) (s : Fin 2)
  | bare (f : Fin 3)
  deriving DecidableEq, Fintype

/-- An index for the components of the five dotted fermion species, the generation
  together with the colour and isospin the species carries. -/
inductive RightIdx
  | d (f : Fin 3) (c : Fin 3)
  | u (f : Fin 3) (c : Fin 3)
  | barQ (f : Fin 3) (c : Fin 3) (s : Fin 2)
  | barL (f : Fin 3) (s : Fin 2)
  | e (f : Fin 3)
  deriving DecidableEq, Fintype

/-- The components of the five undotted species at the derivative slots `l`, presented as
  a two-element family in the spinor index. -/
noncomputable def leftComp
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : LeftIdx → Fin 2 → fieldData.LocalCovFieldAlgebra
  | .bard f c => fun a => bardComponent f l (a, c)
  | .baru f c => fun a => baruComponent f l (a, c)
  | .Q f c s => fun a => QComponent f l (a, c, s)
  | .L f s => fun a => LComponent f l (a, s)
  | .bare f => fun a => bareComponent f l a

/-- The components of the five dotted species at the derivative slots `l`, presented as a
  two-element family in the spinor index. -/
noncomputable def rightComp
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : RightIdx → Fin 2 → fieldData.LocalCovFieldAlgebra
  | .d f c => fun a => dComponent f l (a, c)
  | .u f c => fun a => uComponent f l (a, c)
  | .barQ f c s => fun a => barQComponent f l (a, c, s)
  | .barL f s => fun a => barLComponent f l (a, s)
  | .e f => fun a => eComponent f l a

/-- Every undotted component family carries a dual undotted spinor index, at zero
  covariant derivatives. -/
lemma repLorentz_leftComp (i : LeftIdx) (Λ : SL(2,ℂ)) (a : Fin 2) :
    repLorentz Λ (leftComp ![] i a) = ∑ β, (Λ⁻¹).1 a β • leftComp ![] i β := by
  cases i with
  | bard f c => exact repLorentz_bardComponent Λ f ![] (a, c)
  | baru f c => exact repLorentz_baruComponent Λ f ![] (a, c)
  | Q f c s => exact repLorentz_QComponent Λ f ![] (a, c, s)
  | L f s => exact repLorentz_LComponent Λ f ![] (a, s)
  | bare f => exact repLorentz_bareComponent Λ f ![] a

/-- Every dotted component family carries a dual dotted spinor index, at zero covariant
  derivatives. -/
lemma repLorentz_rightComp (i : RightIdx) (Λ : SL(2,ℂ)) (a : Fin 2) :
    repLorentz Λ (rightComp ![] i a) = ∑ β, star ((Λ⁻¹).1 a β) • rightComp ![] i β := by
  cases i with
  | d f c => exact repLorentz_dComponent Λ f ![] (a, c)
  | u f c => exact repLorentz_uComponent Λ f ![] (a, c)
  | barQ f c s => exact repLorentz_barQComponent Λ f ![] (a, c, s)
  | barL f s => exact repLorentz_barLComponent Λ f ![] (a, s)
  | e f => exact repLorentz_eComponent Λ f ![] a


/-!

## B. The ranges of the symbol maps inside the chirality spans

A symbol map is determined by its values on a basis of the dual of its value space, so
its range is the join of the lines through its components
(`LinearMap.range_eq_iSup_span_coord`).
Collecting the ten ranges into the two chirality spans is then a matter of naming the
right index.

-/

/-- The join of the lines through the components of the five undotted species. -/
noncomputable def leftSpan
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (i : LeftIdx) (a : Fin 2), ℂ ∙ leftComp l i a

/-- The join of the lines through the components of the five dotted species. -/
noncomputable def rightSpan
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (i : RightIdx) (a : Fin 2), ℂ ∙ rightComp l i a

/-- The range of the `bard` symbols lies in the undotted span. -/
lemma range_bard_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ leftSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord ((Basis.conj DownSinglet.basis)) (bard f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.bard f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `baru` symbols lies in the undotted span. -/
lemma range_baru_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ leftSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord ((Basis.conj UpSinglet.basis)) (baru f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.baru f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `Q` symbols lies in the undotted span. -/
lemma range_Q_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ leftSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord (QuarkDoublet.basis) (Q f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.Q f j.2.1 j.2.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `L` symbols lies in the undotted span. -/
lemma range_L_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ leftSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord (LeptonDoubletV.basis) (L f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.L f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `bare` symbols lies in the undotted span. -/
lemma range_bare_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ leftSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord ((Basis.conj LeptonSinglet.basis)) (bare f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.bare f)
    (Submodule.mem_iSup_of_mem j (Submodule.mem_span_singleton_self _))

/-- The range of the `d` symbols lies in the dotted span. -/
lemma range_d_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ rightSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord (DownSinglet.basis) (d f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.d f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `u` symbols lies in the dotted span. -/
lemma range_u_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ rightSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord (UpSinglet.basis) (u f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.u f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `barQ` symbols lies in the dotted span. -/
lemma range_barQ_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ rightSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord ((Basis.conj QuarkDoublet.basis)) (barQ f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.barQ f j.2.1 j.2.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `barL` symbols lies in the dotted span. -/
lemma range_barL_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ rightSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord ((Basis.conj LeptonDoubletV.basis)) (barL f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.barL f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `e` symbols lies in the dotted span. -/
lemma range_e_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ rightSpan l := by
  rw [LinearMap.range_eq_iSup_span_coord (LeptonSinglet.basis) (e f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← Module.Basis.coe_dualBasis]
  exact Submodule.mem_iSup_of_mem (.e f)
    (Submodule.mem_iSup_of_mem j (Submodule.mem_span_singleton_self _))


/-!

## C. Mass weight six with no Dirac mass term

Gauge invariance is what selects the conjugate pairings. A gauge-invariant element lies
in the weight-zero piece of the gauge weight decomposition, and modulo a gauge-stable
submodule the same holds with the submodule joined on. The torus generators scale every
other weight, and `GaugeWeightDecomposition.reducesInvariantsTo_piece_zero` deletes them
one piece at a time. Unlike the single-tower case, the generator has to be chosen weight by
weight, since a product like `Q barQ` at two different colours has vanishing hypercharge and
nonzero colour, so no one generator sees every weight.

Mass weight six is the product of two underived fermion towers. Gauge invariance puts
such an invariant in the weight-zero piece, which `massWeightSubmoduleGaugeWeightSix_piece_zero`
writes as the ten conjugate pairings, and every one of those is an undotted
component times a dotted one. `Lorentz.isEquivariant_downLDownR_mul` turns each into a dual
left-right Weyl family and `Lorentz.mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span`
peels the lot off, leaving nothing.

The physics is that the Standard Model has no Dirac mass term. A mass term pairs a
left-handed field with a right-handed one, and while such a pair is exactly what survives
the gauge cut, its two spinor indices have nothing to contract against. A dotted index
and an undotted one carry no invariant pairing, and only the symplectic form pairs two indices
of the same chirality. The fermion masses have to come from somewhere else, and they do,
from the Yukawa sector, where the Higgs doublet supplies the missing index.

-/

/-- If `V` lies in the join of the lines through an undotted family and `W` in the join
  for a dotted one, the product lies in the join of the spans of the pair families. -/
lemma mul_le_iSup_span_pair {ι κ : Type}
    {X : ι → Fin 2 → fieldData.LocalCovFieldAlgebra}
    {Y : κ → Fin 2 → fieldData.LocalCovFieldAlgebra}
    {V W : Submodule ℂ fieldData.LocalCovFieldAlgebra} (hV : V ≤ ⨆ (i : ι) (a : Fin 2), ℂ ∙ X i a)
    (hW : W ≤ ⨆ (j : κ) (a : Fin 2), ℂ ∙ Y j a) :
    V * W ≤ ⨆ (p : ι × κ) (l : Fin 2 × Fin 2), ℂ ∙ (X p.1 l.1 * Y p.2 l.2) := by
  refine le_trans (mul_le_mul' hV hW) ?_
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun j => iSup_le fun b => iSup_le fun i => iSup_le fun a => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact le_iSup₂_of_le (i, j) (a, b) le_rfl

/-- The mirror of `mul_le_iSup_span_pair` with the two spinor slots exchanged, for a
  product whose left factor is the dotted one. -/
lemma mul_le_iSup_span_pair_swap {ι κ : Type}
    {X : ι → Fin 2 → fieldData.LocalCovFieldAlgebra}
    {Y : κ → Fin 2 → fieldData.LocalCovFieldAlgebra}
    {V W : Submodule ℂ fieldData.LocalCovFieldAlgebra} (hV : V ≤ ⨆ (i : ι) (a : Fin 2), ℂ ∙ X i a)
    (hW : W ≤ ⨆ (j : κ) (a : Fin 2), ℂ ∙ Y j a) :
    V * W ≤ ⨆ (p : ι × κ) (l : Fin 2 × Fin 2), ℂ ∙ (X p.1 l.2 * Y p.2 l.1) := by
  refine le_trans (mul_le_mul' hV hW) ?_
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun j => iSup_le fun b => iSup_le fun i => iSup_le fun a => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact le_iSup₂_of_le (i, j) (b, a) le_rfl

/-- The mass-weight six families, a product of two underived components of opposite
  chirality, in either order. -/
noncomputable def sixFamily :
    (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx) → Fin 2 × Fin 2 → fieldData.LocalCovFieldAlgebra
  | .inl p => fun l => leftComp ![] p.1 l.1 * rightComp ![] p.2 l.2
  | .inr p => fun l => rightComp ![] p.1 l.2 * leftComp ![] p.2 l.1

/-- The join of the spans of the mass-weight six families. -/
noncomputable def sixSpan :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (i : (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx)) (l : Fin 2 × Fin 2),
    ℂ ∙ sixFamily i l

/-- Each mass-weight six family carries one dual undotted and one dual dotted spinor
  index. -/
lemma isEquivariant_downLDownR_sixFamily
    (i : (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx)) :
    complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz
      (liftComponents (sixFamily i ∘ pairIdx)) := by
  cases i with
  | inl p =>
    exact isEquivariant_downLDownR_mul repLorentz_mul (repLorentz_leftComp p.1)
      (repLorentz_rightComp p.2)
  | inr p =>
    exact isEquivariant_downLDownR_mul_swap repLorentz_mul (repLorentz_rightComp p.1)
      (repLorentz_leftComp p.2)

/-- An undotted range times a dotted one lies in the mass-weight six span. -/
lemma mul_le_sixSpan_left {V W : Submodule ℂ fieldData.LocalCovFieldAlgebra} (hV : V ≤ leftSpan ![])
    (hW : W ≤ rightSpan ![]) : V * W ≤ sixSpan :=
  (mul_le_iSup_span_pair hV hW).trans
    (iSup_le fun p => le_iSup (fun i => ⨆ l, ℂ ∙ sixFamily i l) (.inl p))

/-- A dotted range times an undotted one lies in the mass-weight six span. -/
lemma mul_le_sixSpan_right {V W : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hV : V ≤ rightSpan ![])
    (hW : W ≤ leftSpan ![]) : V * W ≤ sixSpan :=
  (mul_le_iSup_span_pair_swap hV hW).trans
    (iSup_le fun p => le_iSup (fun i => ⨆ l, ℂ ∙ sixFamily i l) (.inr p))

/-- The weight-zero piece at mass weight six lies in the span of the mass-weight six families, since
  each of the ten conjugate pairings is a product of an undotted range with a dotted one, in one
  order or the other. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero_le :
    (massWeightSubmoduleGaugeWeightSix).piece 0 ≤ sixSpan := by
  rw [massWeightSubmoduleGaugeWeightSix_piece_zero]
  refine iSup_le fun f => iSup_le fun f' => sup_le (sup_le (sup_le (sup_le (sup_le
    (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_right
      (range_d_le_rightSpan f ![]) (range_bard_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_left
      (range_bard_le_leftSpan f ![]) (range_d_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_right
      (range_u_le_rightSpan f ![]) (range_baru_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_left
      (range_baru_le_leftSpan f ![]) (range_u_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_left
      (range_Q_le_leftSpan f ![]) (range_barQ_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_right
      (range_barQ_le_rightSpan f ![]) (range_Q_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_left
      (range_L_le_leftSpan f ![]) (range_barL_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_right
      (range_barL_le_rightSpan f ![]) (range_L_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_right
      (range_e_le_rightSpan f ![]) (range_bare_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (mul_le_sixSpan_left
      (range_bare_le_leftSpan f ![]) (range_e_le_rightSpan f' ![]))

/-- Mass weight six carries no invariant modulo a stable submodule, there being no Dirac
  mass term. A gauge- and Lorentz-invariant element of `massWeightSubmodule 6 ⊔ S` lies
  in `S`, gauge invariance cutting the hundred pairings of two fermion symbols down to
  the ten conjugate ones and Lorentz invariance killing each of those, its two spinor
  indices being of opposite chirality. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleSix_sup
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (g : GaugeGroupI) (y : fieldData.LocalCovFieldAlgebra), y ∈ S → repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 6 ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hzero : x ∈ (massWeightSubmoduleGaugeWeightSix).piece 0 ⊔ S :=
    GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant _ (fun i y hy => hS _ y hy) hx
      fun _ => hG _
  refine mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span
    isEquivariant_downLDownR_sixFamily S hSL ?_ hL
  exact sup_le_sup_right massWeightSubmoduleGaugeWeightSix_piece_zero_le S hzero


/-!

## D. The classification below mass weight eight

The seven weights between zero and eight are now settled. Weights one, two and four are
trivial submodules, weights three, five and seven are single fermion towers and carry a
nonzero hypercharge, and weight six is section F. So between weight zero and weight eight
the fermion sector has no invariant beyond what `S` already supplies, and the equivalence
records it.

The lower bound `0 < w` cannot be dropped. Weight zero contains the scalars by
`one_le_massWeightSubmodule_zero`, and `1` is fixed by both groups, the two
representations being multiplicative, without lying in any given `S`.

-/

/-- Between mass weight zero and mass weight eight the fermion sector carries no
  invariant. An element of `massWeightSubmodule w ⊔ S` for `0 < w < 8` fixed by both
  groups lies in `S`. Weights one, two and four are trivial, weights three, five and
  seven carry no gauge singlet, and weight six is the missing Dirac mass term. -/
lemma mem_of_invariant_massWeightSubmodule_lt_eight_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  interval_cases w
  · exact mem_of_mem_massWeightSubmoduleOne_sup hx
  · exact mem_of_mem_massWeightSubmoduleTwo_sup hx
  · exact mem_of_invariant_of_mem_massWeightSubmoduleThree_sup hS hx hG
  · exact mem_of_mem_massWeightSubmoduleFour_sup hx
  · exact mem_of_invariant_of_mem_massWeightSubmoduleFive_sup hS hx hG
  · exact mem_of_invariant_of_mem_massWeightSubmoduleSix_sup hS hSL hx hG hL
  · exact mem_of_invariant_of_mem_massWeightSubmoduleSeven_sup hS hx hG

/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`. An element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is
  itself an element of `S` fixed by both groups. The span of invariants that the weight
  eight statement leaves over is here the trivial one, so `x - y` lies in it exactly when
  `x = y`. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hS hSL hx hG
      hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential. Below mass weight eight an element
  of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of `S` fixed by both
  groups, and conversely. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hS hSL hx.1
    hx.2.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end FermionSector

end StandardModel
