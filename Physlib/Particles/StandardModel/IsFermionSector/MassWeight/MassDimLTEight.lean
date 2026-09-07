/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Components
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Relativity.LorentzGroup.Invariants.IsVectorLeftRightWeyl
public import Physlib.Particles.StandardModel.Peeling
/-!
# The invariants below mass weight eight

The fermion sector carries nothing invariant below mass weight eight. Weights one, two
and four are trivial submodules and weights three, five and seven are single fermion
towers, which carry a nonzero hypercharge and so no gauge singlet. That leaves mass
weight six, the products of two underived towers, and it is the interesting one: it is
where a Dirac mass term `ψ̄ ψ` would sit, and the statement proved here is that no such
term exists.

The two symmetries cooperate. Gauge invariance cuts the hundred pairings of two fermion
symbols down to the ten conjugate ones, `d bard`, `bard d`, `u baru`, ..., `bare e`,
every other pairing having hypercharges that cannot cancel; this is
`massWeightSubmoduleGaugeWeightSix_piece_zero` of the gauge weight decomposition. Each
surviving pairing is then a product of two symbols of opposite chirality, one dotted and
one undotted, since a species and its conjugate always sit in opposite Weyl
representations. A pair of opposite-chirality spinor indices with nothing else to
contract against admits no invariant at all — `Lorentz.IsDualLeftRightWeyl.eq_zero_of_invariant`
— so each pairing contributes nothing and mass weight six is left empty.

That is the absence of a Dirac mass term in the Standard Model, and it is why the fermion
masses have to come from the Yukawa sector instead: the Higgs doublet supplies the missing
index, and its own mass weight makes the Yukawa terms weight eight.

The chirality bookkeeping is done once and reused at mass weight eight, in
`MassDimEight`, which imports this file: the five undotted species are indexed by
`LeftIdx` and the five dotted ones by `RightIdx`, and `leftComp` and `rightComp` list
their components with the spinor index singled out.

- A. Chiral component families
- B. The products of an opposite-chirality pair
- C. Peeling the pair spans off a Lorentz-stable submodule
- D. The five undotted and the five dotted species
- E. The ranges of the symbol maps inside the chirality spans
- F. Gauge invariants and the weight-zero piece
- G. Mass weight six: no Dirac mass term
- H. The classification below mass weight eight

The final statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`
needs `0 < w` as well as `w < 8`: at `w = 0` the mass-weight submodule contains the
scalars, so `1` is an invariant of weight zero lying in no `S`.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace IsFermionSector

/-!

## A. Chiral component families

A fermion symbol carries exactly one spinor index, and which of the two Weyl
representations it sits in is fixed by the species. Freezing every other index leaves a
two-element family of elements of `B`, and the two possible transformation laws are
recorded here. Both are contragredient, the symbols eating a covector of their value
space; the dotted law carries the extra complex conjugation.

-/

section ChiralFamilies

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A two-element family `X` of elements of `B` carries a dual undotted spinor index: it
  transforms by the contragredient of the left-handed Weyl representation. -/
def IsDualLeftWeyl (repLorentz : Representation ℂ SL(2,ℂ) B) (X : Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, (Λ⁻¹).1 a β • X β

/-- A two-element family `Y` of elements of `B` carries a dual dotted spinor index: it
  transforms by the contragredient of the right-handed Weyl representation, which is the
  conjugate of the undotted law. -/
def IsDualRightWeyl (repLorentz : Representation ℂ SL(2,ℂ) B) (Y : Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (Y a) = ∑ β, star ((Λ⁻¹).1 a β) • Y β

/-- A family `X` carrying one four-vector index and one dual undotted spinor index: the
  once-derived form of `IsDualLeftWeyl`, the derivative slot moving by the columns of the
  Lorentz matrix. Only the value index of a fermion symbol is dualised, so the derivative
  slot keeps the plain Lorentz law. -/
def IsVectorDualLeftWeyl (repLorentz : Representation ℂ SL(2,ℂ) B)
    (X : (Fin 1 ⊕ Fin 3) → Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (X μ a)
    = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * (Λ⁻¹).1 a β) • X ν β

/-- A family `Y` carrying one four-vector index and one dual dotted spinor index: the
  once-derived form of `IsDualRightWeyl`. -/
def IsVectorDualRightWeyl (repLorentz : Representation ℂ SL(2,ℂ) B)
    (Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2), repLorentz Λ (Y μ a)
    = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * star ((Λ⁻¹).1 a β)) • Y ν β

/-!

## B. The products of an opposite-chirality pair

Multiplying an undotted family by a dotted one gives a family of two opposite-chirality
spinor indices, which is what `Lorentz.IsDualLeftRightWeyl` classifies, and the four
lemmas here supply that classification in each of the four arrangements that the fermion
sector produces: the two orders of the product, each with and without a derivative on the
second factor. The representation being multiplicative is all that is needed, the two
factors transforming independently.

-/

variable (hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
  repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)

include hrepLorentz_mul

/-- An undotted family times a dotted one is a dual left-right Weyl family. -/
lemma isDualLeftRightWeyl_mul {X Y : Fin 2 → B} (hX : IsDualLeftWeyl repLorentz X)
    (hY : IsDualRightWeyl repLorentz Y) :
    IsDualLeftRightWeyl B repLorentz (fun l => X l.1 * Y l.2) where
  repLorentz_T g l := by
    rw [hrepLorentz_mul, hX g l.1, hY g l.2, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]

/-- A dotted family times an undotted one is a dual left-right Weyl family, the two
  spinor slots exchanged. -/
lemma isDualLeftRightWeyl_mul_swap {X Y : Fin 2 → B} (hX : IsDualRightWeyl repLorentz X)
    (hY : IsDualLeftWeyl repLorentz Y) :
    IsDualLeftRightWeyl B repLorentz (fun l => X l.2 * Y l.1) where
  repLorentz_T g l := by
    rw [hrepLorentz_mul, hX g l.2, hY g l.1, Finset.sum_mul_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

/-- An undotted family times a once-derived dotted one is a vector dual left-right Weyl
  family: the derivative supplies the four-vector index. -/
lemma isVectorDualLeftRightWeyl_mul {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : IsDualLeftWeyl repLorentz X) (hY : IsVectorDualRightWeyl repLorentz Y) :
    IsVectorDualLeftRightWeyl B repLorentz (fun p => X p.2.1 * Y p.1 p.2.2) where
  repLorentz_T g μ l := by
    rw [hrepLorentz_mul, hX g l.1, hY g μ l.2, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

/-- A dotted family times a once-derived undotted one is a vector dual left-right Weyl
  family, the two spinor slots exchanged. -/
lemma isVectorDualLeftRightWeyl_mul_swap {X : Fin 2 → B} {Y : (Fin 1 ⊕ Fin 3) → Fin 2 → B}
    (hX : IsDualRightWeyl repLorentz X) (hY : IsVectorDualLeftWeyl repLorentz Y) :
    IsVectorDualLeftRightWeyl B repLorentz (fun p => X p.2.2 * Y p.1 p.2.1) where
  repLorentz_T g μ l := by
    rw [hrepLorentz_mul, hX g l.2, hY g μ l.1, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

end ChiralFamilies


/-!

## C. Peeling the pair spans off a Lorentz-stable submodule

A dual left-right Weyl family carries no invariant, so its span can be discarded from a
Lorentz-stable submodule; iterating over a finite family of them discards a whole join.
The induction is the same one the gauge sector runs in `IsGaugeSector`, the span of the
components of each family being stable under the Lorentz group.

-/

section Peeling

variable {B : Type} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The span of the components of a dual left-right Weyl family is stable under the
  Lorentz group: each component transforms into a combination of components. -/
lemma isDualLeftRightWeyl_span_stable {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) (g : SL(2,ℂ)) {y : B}
    (hy : y ∈ ⨆ l, ℂ ∙ T l) : repLorentz g y ∈ ⨆ l, ℂ ∙ T l := by
  have key : (⨆ l, ℂ ∙ T l) ≤ Submodule.comap (repLorentz g) (⨆ l, ℂ ∙ T l) := by
    refine iSup_le fun l => ?_
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, hT.repLorentz_T]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))
  exact key hy

/-- Peeling a finite join of the spans of dual left-right Weyl families off a
  Lorentz-stable submodule: such a family has no invariant, so a Lorentz invariant of the
  join together with `S` lies in `S`. -/
lemma mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span {ι : Type} [DecidableEq ι]
    {T : ι → Fin 2 × Fin 2 → B} (hT : ∀ i, IsDualLeftRightWeyl B repLorentz (T i))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (s : Finset ι)
    {x : B} (hx : x ∈ (⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), ⨆ l, ℂ ∙ T i l) = ⊥ from by simp, bot_sup_eq] at hx
    exact hx
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ g : SL(2,ℂ), ∀ y ∈ (⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S,
        repLorentz g y ∈ (⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S)
          ≤ Submodule.comap (repLorentz g) ((⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi (isDualLeftRightWeyl_span_stable (hT i) g hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    exact ih ((hT a).mem_of_invariant_of_mem_sup _ hstab hx hinv) hinv

/-- The version of `mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span` joining over a
  whole finite index type. -/
lemma mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span {ι : Type} [Fintype ι]
    [DecidableEq ι] {T : ι → Fin 2 × Fin 2 → B}
    (hT : ∀ i, IsDualLeftRightWeyl B repLorentz (T i)) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span hT S hS Finset.univ ?_ hinv
  refine sup_le_sup_right (iSup_le fun i => ?_) S hx
  exact le_iSup₂_of_le i (Finset.mem_univ i) le_rfl

end Peeling


/-!

## D. The five undotted and the five dotted species

Each of the ten fermion species sits in one of the two Weyl representations, and a
species and its conjugate always sit in opposite ones. The five undotted species are
`bard`, `baru`, `Q`, `L` and `bare`, the five dotted ones `d`, `u`, `barQ`, `barL` and
`e`. Indexing each list by the generation and the remaining internal indices, `leftComp`
and `rightComp` present every fermion component as a two-element family in its spinor
index, which is the shape section A asks for.

-/

/-- An index for the components of the five undotted fermion species: the generation
  together with the colour and isospin the species carries. -/
inductive LeftIdx
  | bard (f : Fin 3) (c : Fin 3)
  | baru (f : Fin 3) (c : Fin 3)
  | Q (f : Fin 3) (c : Fin 3) (s : Fin 2)
  | L (f : Fin 3) (s : Fin 2)
  | bare (f : Fin 3)
  deriving DecidableEq, Fintype

/-- An index for the components of the five dotted fermion species: the generation
  together with the colour and isospin the species carries. -/
inductive RightIdx
  | d (f : Fin 3) (c : Fin 3)
  | u (f : Fin 3) (c : Fin 3)
  | barQ (f : Fin 3) (c : Fin 3) (s : Fin 2)
  | barL (f : Fin 3) (s : Fin 2)
  | e (f : Fin 3)
  deriving DecidableEq, Fintype

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

set_option linter.unusedVariables false in
/-- The components of the five undotted species at the derivative slots `l`, presented as
  a two-element family in the spinor index. -/
noncomputable def leftComp (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : LeftIdx → Fin 2 → B
  | .bard f c => fun a => h.bardComponent f l (a, c)
  | .baru f c => fun a => h.baruComponent f l (a, c)
  | .Q f c s => fun a => h.QComponent f l (a, c, s)
  | .L f s => fun a => h.LComponent f l (a, s)
  | .bare f => fun a => h.bareComponent f l a

set_option linter.unusedVariables false in
/-- The components of the five dotted species at the derivative slots `l`, presented as a
  two-element family in the spinor index. -/
noncomputable def rightComp (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : RightIdx → Fin 2 → B
  | .d f c => fun a => h.dComponent f l (a, c)
  | .u f c => fun a => h.uComponent f l (a, c)
  | .barQ f c s => fun a => h.barQComponent f l (a, c, s)
  | .barL f s => fun a => h.barLComponent f l (a, s)
  | .e f => fun a => h.eComponent f l a

/-- Every undotted component family carries a dual undotted spinor index, at zero
  covariant derivatives. -/
lemma isDualLeftWeyl_leftComp (i : LeftIdx) :
    IsDualLeftWeyl repLorentz (h.leftComp ![] i) := by
  cases i with
  | bard f c => exact fun Λ a => h.repLorentz_bardComponent Λ f ![] (a, c)
  | baru f c => exact fun Λ a => h.repLorentz_baruComponent Λ f ![] (a, c)
  | Q f c s => exact fun Λ a => h.repLorentz_QComponent Λ f ![] (a, c, s)
  | L f s => exact fun Λ a => h.repLorentz_LComponent Λ f ![] (a, s)
  | bare f => exact fun Λ a => h.repLorentz_bareComponent Λ f ![] a

/-- Every dotted component family carries a dual dotted spinor index, at zero covariant
  derivatives. -/
lemma isDualRightWeyl_rightComp (i : RightIdx) :
    IsDualRightWeyl repLorentz (h.rightComp ![] i) := by
  cases i with
  | d f c => exact fun Λ a => h.repLorentz_dComponent Λ f ![] (a, c)
  | u f c => exact fun Λ a => h.repLorentz_uComponent Λ f ![] (a, c)
  | barQ f c s => exact fun Λ a => h.repLorentz_barQComponent Λ f ![] (a, c, s)
  | barL f s => exact fun Λ a => h.repLorentz_barLComponent Λ f ![] (a, s)
  | e f => exact fun Λ a => h.repLorentz_eComponent Λ f ![] a


/-!

## E. The ranges of the symbol maps inside the chirality spans

A symbol map is determined by its values on a basis of the dual of its value space, so
its range is the join of the lines through its components; `range_eq_iSup_span` says so.
Collecting the ten ranges into the two chirality spans is then a matter of naming the
right index.

-/

/-- The join of the lines through the components of the five undotted species. -/
noncomputable def leftSpan (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : Submodule ℂ B :=
  ⨆ (i : LeftIdx) (a : Fin 2), ℂ ∙ h.leftComp l i a

/-- The join of the lines through the components of the five dotted species. -/
noncomputable def rightSpan (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) : Submodule ℂ B :=
  ⨆ (i : RightIdx) (a : Fin 2), ℂ ∙ h.rightComp l i a

/-- A basis vector of the dual basis is the matching coordinate functional. -/
lemma dualBasis_apply {ι M : Type} [AddCommGroup M] [Module ℂ M] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ M) (j : ι) : b.dualBasis j = b.coord j :=
  congrFun (Module.Basis.coe_dualBasis b) j

/-- The range of the `bard` symbols lies in the undotted span. -/
lemma range_bard_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ h.leftSpan l := by
  rw [range_eq_iSup_span (DownSinglet.basis.conj) (bard f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.bard f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `baru` symbols lies in the undotted span. -/
lemma range_baru_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ h.leftSpan l := by
  rw [range_eq_iSup_span (UpSinglet.basis.conj) (baru f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.baru f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `Q` symbols lies in the undotted span. -/
lemma range_Q_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ h.leftSpan l := by
  rw [range_eq_iSup_span (QuarkDoublet.basis) (Q f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.Q f j.2.1 j.2.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `L` symbols lies in the undotted span. -/
lemma range_L_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ h.leftSpan l := by
  rw [range_eq_iSup_span (LeptonDoublet.basis) (L f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.L f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `bare` symbols lies in the undotted span. -/
lemma range_bare_le_leftSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ h.leftSpan l := by
  rw [range_eq_iSup_span (LeptonSinglet.basis.conj) (bare f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.bare f)
    (Submodule.mem_iSup_of_mem j (Submodule.mem_span_singleton_self _))

/-- The range of the `d` symbols lies in the dotted span. -/
lemma range_d_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ h.rightSpan l := by
  rw [range_eq_iSup_span (DownSinglet.basis) (d f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.d f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `u` symbols lies in the dotted span. -/
lemma range_u_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ h.rightSpan l := by
  rw [range_eq_iSup_span (UpSinglet.basis) (u f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.u f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `barQ` symbols lies in the dotted span. -/
lemma range_barQ_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ h.rightSpan l := by
  rw [range_eq_iSup_span (QuarkDoublet.basis.conj) (barQ f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.barQ f j.2.1 j.2.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `barL` symbols lies in the dotted span. -/
lemma range_barL_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ h.rightSpan l := by
  rw [range_eq_iSup_span (LeptonDoublet.basis.conj) (barL f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.barL f j.2)
    (Submodule.mem_iSup_of_mem j.1 (Submodule.mem_span_singleton_self _))

/-- The range of the `e` symbols lies in the dotted span. -/
lemma range_e_le_rightSpan (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ h.rightSpan l := by
  rw [range_eq_iSup_span (LeptonSinglet.basis) (e f l)]
  refine iSup_le fun j => ?_
  rw [Submodule.span_singleton_le_iff_mem, ← dualBasis_apply]
  exact Submodule.mem_iSup_of_mem (.e f)
    (Submodule.mem_iSup_of_mem j (Submodule.mem_span_singleton_self _))


/-!

## F. Gauge invariants and the weight-zero piece

Gauge invariance is what selects the conjugate pairings. A gauge-invariant element lies
in the weight-zero piece of the gauge weight decomposition, and modulo a gauge-stable
submodule the same holds with the submodule joined on: the torus generators scale every
other weight, and the induction of `mem_of_invariant_of_mem_biSup_piece_sup` deletes them
one at a time. Unlike the single-tower case, the generator has to be chosen weight by
weight: a product like `Q barQ` at two different colours has vanishing hypercharge and
nonzero colour, so no one generator sees every weight.

-/

/-- The one-weight-at-a-time refinement, with the separating generator chosen per weight.
  Let `S` be closed under the four torus generators and let `s` be a finite set of gauge
  weights, each seen by some generator. Then a gauge-invariant element of the join of the
  weight-`w` pieces for `w ∈ s` with `S` already lies in `S`. -/
lemma mem_of_invariant_of_mem_biSup_piece_sup_of_ne_zero {V S : Submodule ℂ B}
    (dV : GaugeWeightDecomposition repGauge V)
    (hS : ∀ (i : Fin 4) (y : B), y ∈ S → repGauge (gaugeTorusGen i) y ∈ S) :
    ∀ (s : Finset GaugeWeight), (∀ w ∈ s, ∃ i, w.coord i ≠ 0) →
      ∀ x ∈ (⨆ w ∈ s, dV.piece w) ⊔ S, (∀ g : GaugeGroupI, repGauge g x = x) → x ∈ S := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ x hx _
    simpa using hx
  | @insert w₀ s' hw₀ ih =>
    intro hs x hx hinv
    obtain ⟨i, hi⟩ := hs w₀ (Finset.mem_insert_self w₀ s')
    rw [Finset.iSup_insert, sup_assoc] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have hc1 : ((expI : ℂ) ^ w₀.coord i) ≠ 1 := by
      intro hcc
      exact hi (expI_zpow_injective
        (show (expI : ℂ) ^ w₀.coord i = (expI : ℂ) ^ (0 : ℤ) by rw [zpow_zero]; exact hcc))
    have hpiece : ∀ w, ∀ z ∈ dV.piece w, repGauge (gaugeTorusGen i) z ∈ dV.piece w := by
      intro w z hz
      rw [dV.piece_le w z hz i]
      exact (dV.piece w).smul_mem _ hz
    have hmap : Submodule.map (repGauge (gaugeTorusGen i)) ((⨆ w ∈ s', dV.piece w) ⊔ S)
        ≤ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      rw [Submodule.map_sup]
      refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
      · simp only [Submodule.map_iSup]
        exact iSup₂_le fun w hw => le_iSup₂_of_le w hw
          (Submodule.map_le_iff_le_comap.mpr fun z hz => hpiece w z hz)
      · exact Submodule.map_le_iff_le_comap.mpr fun z hz => hS i z hz
    have hsum : ((expI : ℂ) ^ w₀.coord i) • a + repGauge (gaugeTorusGen i) y = a + y := by
      have hg := hinv (gaugeTorusGen i)
      rwa [map_add, dV.piece_le w₀ a ha i] at hg
    have hkey : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y)
        = ((expI : ℂ) ^ w₀.coord i) • y - repGauge (gaugeTorusGen i) y := by
      rw [sub_smul, one_smul, smul_add, ← hsum]
      abel
    have hmem : (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      have h1 : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
        rw [hkey]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (hmap ⟨y, hy, rfl⟩)
      have h2 := Submodule.smul_mem _ (((expI : ℂ) ^ w₀.coord i - 1)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc1), one_smul] at h2
    exact ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) (a + y) hmem hinv

/-- A gauge-invariant element of `V ⊔ S`, for `S` closed under the four torus generators,
  already lies in the weight-zero piece joined with `S`: every other weight is seen by
  some generator and is scaled away by it. -/
lemma mem_piece_zero_sup_of_invariant {V S : Submodule ℂ B}
    (dV : GaugeWeightDecomposition repGauge V)
    (hS : ∀ (i : Fin 4) (y : B), y ∈ S → repGauge (gaugeTorusGen i) y ∈ S)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x ∈ dV.piece 0 ⊔ S := by
  refine mem_of_invariant_of_mem_biSup_piece_sup_of_ne_zero dV ?_ (dV.supp.erase 0) ?_ x ?_
    hinv
  · intro i y hy
    rw [Submodule.mem_sup] at hy ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨repGauge (gaugeTorusGen i) a, ?_, repGauge (gaugeTorusGen i) b, hS i b hb, ?_⟩
    · rw [dV.piece_le 0 a ha i]
      exact (dV.piece 0).smul_mem _ ha
    · rw [map_add]
  · intro w hw
    have hw0 : w ≠ 0 := (Finset.mem_erase.mp hw).1
    by_contra hcon
    refine hw0 (GaugeWeight.coord_injective (funext fun i => ?_))
    have hi := not_not.mp (not_exists.mp hcon i)
    rw [hi, GaugeWeight.zero_coord i]
  · have hVle : V ≤ (⨆ w ∈ dV.supp.erase 0, dV.piece w) ⊔ dV.piece 0 := by
      refine le_trans (le_of_eq dV.iSup_piece.symm) (iSup_le fun w => ?_)
      by_cases hw0 : w = 0
      · subst hw0
        exact le_sup_right
      · by_cases hw : w ∈ dV.supp
        · exact le_sup_of_le_left (le_iSup₂_of_le w (Finset.mem_erase.mpr ⟨hw0, hw⟩) le_rfl)
        · rw [dV.piece_eq_bot w hw]
          exact bot_le
    exact ((sup_le_sup_right hVle S).trans (le_of_eq (sup_assoc _ _ _))) hx


/-!

## G. Mass weight six: no Dirac mass term

Mass weight six is the product of two underived fermion towers. Gauge invariance puts
such an invariant in the weight-zero piece, which section F of the gauge weight
decomposition writes as the ten conjugate pairings, and every one of those is an undotted
component times a dotted one. Section B turns each into a dual left-right Weyl family and
section C peels the lot off, leaving nothing.

The physics is that the Standard Model has no Dirac mass term. A mass term pairs a
left-handed field with a right-handed one, and while such a pair is exactly what survives
the gauge cut, its two spinor indices have nothing to contract against: a dotted index
and an undotted one carry no invariant pairing, only the symplectic form pairs two indices
of the same chirality. The fermion masses have to come from somewhere else, and they do —
from the Yukawa sector, where the Higgs doublet supplies the missing index.

-/

/-- If `V` lies in the join of the lines through an undotted family and `W` in the join
  for a dotted one, the product lies in the join of the spans of the pair families. -/
lemma mul_le_iSup_span_pair {ι κ : Type} {X : ι → Fin 2 → B} {Y : κ → Fin 2 → B}
    {V W : Submodule ℂ B} (hV : V ≤ ⨆ (i : ι) (a : Fin 2), ℂ ∙ X i a)
    (hW : W ≤ ⨆ (j : κ) (a : Fin 2), ℂ ∙ Y j a) :
    V * W ≤ ⨆ (p : ι × κ) (l : Fin 2 × Fin 2), ℂ ∙ (X p.1 l.1 * Y p.2 l.2) := by
  refine le_trans (mul_le_mul' hV hW) ?_
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun j => iSup_le fun b => iSup_le fun i => iSup_le fun a => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact le_iSup₂_of_le (i, j) (a, b) le_rfl

/-- The mirror of `mul_le_iSup_span_pair` with the two spinor slots exchanged, for a
  product whose left factor is the dotted one. -/
lemma mul_le_iSup_span_pair_swap {ι κ : Type} {X : ι → Fin 2 → B} {Y : κ → Fin 2 → B}
    {V W : Submodule ℂ B} (hV : V ≤ ⨆ (i : ι) (a : Fin 2), ℂ ∙ X i a)
    (hW : W ≤ ⨆ (j : κ) (a : Fin 2), ℂ ∙ Y j a) :
    V * W ≤ ⨆ (p : ι × κ) (l : Fin 2 × Fin 2), ℂ ∙ (X p.1 l.2 * Y p.2 l.1) := by
  refine le_trans (mul_le_mul' hV hW) ?_
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun j => iSup_le fun b => iSup_le fun i => iSup_le fun a => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact le_iSup₂_of_le (i, j) (b, a) le_rfl

set_option linter.unusedVariables false in
/-- The mass-weight six families: a product of two underived components of opposite
  chirality, in either order. -/
noncomputable def sixFamily (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) :
    (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx) → Fin 2 × Fin 2 → B
  | .inl p => fun l => h.leftComp ![] p.1 l.1 * h.rightComp ![] p.2 l.2
  | .inr p => fun l => h.rightComp ![] p.1 l.2 * h.leftComp ![] p.2 l.1

/-- The join of the spans of the mass-weight six families. -/
noncomputable def sixSpan (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) :
    Submodule ℂ B :=
  ⨆ (i : (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx)) (l : Fin 2 × Fin 2),
    ℂ ∙ h.sixFamily i l

include h in
/-- Each mass-weight six family carries one dual undotted and one dual dotted spinor
  index. -/
lemma isDualLeftRightWeyl_sixFamily
    (i : (LeftIdx × RightIdx) ⊕ (RightIdx × LeftIdx)) :
    IsDualLeftRightWeyl B repLorentz (h.sixFamily i) := by
  cases i with
  | inl p =>
    exact isDualLeftRightWeyl_mul hrepLorentz_mul (h.isDualLeftWeyl_leftComp p.1)
      (h.isDualRightWeyl_rightComp p.2)
  | inr p =>
    exact isDualLeftRightWeyl_mul_swap hrepLorentz_mul (h.isDualRightWeyl_rightComp p.1)
      (h.isDualLeftWeyl_leftComp p.2)

include h in
/-- An undotted range times a dotted one lies in the mass-weight six span. -/
lemma mul_le_sixSpan_left {V W : Submodule ℂ B} (hV : V ≤ h.leftSpan ![])
    (hW : W ≤ h.rightSpan ![]) : V * W ≤ h.sixSpan :=
  (mul_le_iSup_span_pair hV hW).trans
    (iSup_le fun p => le_iSup (fun i => ⨆ l, ℂ ∙ h.sixFamily i l) (.inl p))

include h in
/-- A dotted range times an undotted one lies in the mass-weight six span. -/
lemma mul_le_sixSpan_right {V W : Submodule ℂ B} (hV : V ≤ h.rightSpan ![])
    (hW : W ≤ h.leftSpan ![]) : V * W ≤ h.sixSpan :=
  (mul_le_iSup_span_pair_swap hV hW).trans
    (iSup_le fun p => le_iSup (fun i => ⨆ l, ℂ ∙ h.sixFamily i l) (.inr p))

include h in
/-- The weight-zero piece at mass weight six lies in the span of the mass-weight six
  families: each of the ten conjugate pairings is a product of an undotted range with a
  dotted one, in one order or the other. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero_le :
    (h.massWeightSubmoduleGaugeWeightSix).piece 0 ≤ h.sixSpan := by
  rw [h.massWeightSubmoduleGaugeWeightSix_piece_zero]
  refine iSup_le fun f => iSup_le fun f' => sup_le (sup_le (sup_le (sup_le (sup_le
    (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_right
      (h.range_d_le_rightSpan f ![]) (h.range_bard_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_left
      (h.range_bard_le_leftSpan f ![]) (h.range_d_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_right
      (h.range_u_le_rightSpan f ![]) (h.range_baru_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_left
      (h.range_baru_le_leftSpan f ![]) (h.range_u_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_left
      (h.range_Q_le_leftSpan f ![]) (h.range_barQ_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_right
      (h.range_barQ_le_rightSpan f ![]) (h.range_Q_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_left
      (h.range_L_le_leftSpan f ![]) (h.range_barL_le_rightSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_right
      (h.range_barL_le_rightSpan f ![]) (h.range_L_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_right
      (h.range_e_le_rightSpan f ![]) (h.range_bare_le_leftSpan f' ![]))
  · exact (GaugeWeightDecomposition.piece_le_self _ 0).trans (h.mul_le_sixSpan_left
      (h.range_bare_le_leftSpan f ![]) (h.range_e_le_rightSpan f' ![]))

include h in
/-- Mass weight six carries no invariant modulo a stable submodule: there is no Dirac
  mass term. A gauge- and Lorentz-invariant element of `massWeightSubmodule 6 ⊔ S` lies
  in `S`, gauge invariance cutting the hundred pairings of two fermion symbols down to
  the ten conjugate ones and Lorentz invariance killing each of those, its two spinor
  indices being of opposite chirality. -/
theorem mem_of_invariant_of_mem_massWeightSubmoduleSix_sup {S : Submodule ℂ B}
    (hS : ∀ (g : GaugeGroupI) (y : B), y ∈ S → repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 6 ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hzero : x ∈ (h.massWeightSubmoduleGaugeWeightSix).piece 0 ⊔ S :=
    mem_piece_zero_sup_of_invariant _ (fun i y hy => hS _ y hy) hx hG
  refine mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span
    h.isDualLeftRightWeyl_sixFamily S hSL ?_ hL
  exact sup_le_sup_right h.massWeightSubmoduleGaugeWeightSix_piece_zero_le S hzero


/-!

## H. The classification below mass weight eight

The seven weights between zero and eight are now settled: weights one, two and four are
trivial submodules, weights three, five and seven are single fermion towers and carry a
nonzero hypercharge, and weight six is section G. So between weight zero and weight eight
the fermion sector has no invariant beyond what `S` already supplies, and the equivalence
records it.

The lower bound `0 < w` cannot be dropped. Weight zero contains the scalars by
`one_le_massWeightSubmodule_zero`, and `1` is fixed by both groups, the two
representations being multiplicative, without lying in any given `S`.

-/

include h in
/-- Between mass weight zero and mass weight eight the fermion sector carries no
  invariant: an element of `massWeightSubmodule w ⊔ S` for `0 < w < 8` fixed by both
  groups lies in `S`. Weights one, two and four are trivial, weights three, five and
  seven carry no gauge singlet, and weight six is the missing Dirac mass term. -/
theorem mem_of_invariant_massWeightSubmodule_lt_eight_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  interval_cases w
  · exact h.mem_of_mem_massWeightSubmoduleOne_sup hx
  · exact h.mem_of_mem_massWeightSubmoduleTwo_sup hx
  · exact h.mem_of_invariant_of_mem_massWeightSubmoduleThree_sup hS hx hG
  · exact h.mem_of_mem_massWeightSubmoduleFour_sup hx
  · exact h.mem_of_invariant_of_mem_massWeightSubmoduleFive_sup hS hx hG
  · exact h.mem_of_invariant_of_mem_massWeightSubmoduleSix_sup hS hSL hx hG hL
  · exact h.mem_of_invariant_of_mem_massWeightSubmoduleSeven_sup hS hx hG

include h in
/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`: an element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is
  itself an element of `S` fixed by both groups. The span of invariants that the weight
  eight statement leaves over is here the trivial one, so `x - y` lies in it exactly when
  `x = y`. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hS hSL hx hG
      hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

include h in
/-- The same classification without the existential: below mass weight eight an element
  of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of `S` fixed by both
  groups, and conversely. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hS hSL hx.1
    hx.2.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsFermionSector

end StandardModel
