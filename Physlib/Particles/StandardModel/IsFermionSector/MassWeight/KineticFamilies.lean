/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.MassDimLTEight
public import Physlib.Particles.StandardModel.Peeling
/-!
# The kinetic terms of the fermion sector

The invariants of the fermion sector at mass weight eight are the kinetic terms, and this
file builds them. A kinetic term pairs a species with its own conjugate, one of the two
carrying a covariant derivative, and joins their indices in the only ways available: the
colour indices by the Kronecker delta, the isospin indices by the Kronecker delta, and the
four-vector index against the two opposite-chirality spinor indices by the conjugate Pauli
matrices. That last contraction is `ψ̄ σ̄^μ ∂_μ ψ`.

Ten blocks arise, the five conjugate pairs each with the derivative on one factor or the
other, and they differ only in which indices their symbols carry. So the work is done once,
generically, in the shape `StandardModel.Peeling` consumes: a `KineticBlock` packages a
block together with its three classification steps — colour, isospin, Lorentz — and from
that package alone come the contraction, its invariance under both groups, and the peeling
of the block down to the line through it. The ten blocks are then ten instantiations.

The three stages are the same three the Yukawa sector runs, in the same order, and for the
same reason: each contraction is a spectator of the ones after it. Where a block's symbols
carry no colour index — the two lepton-doublet blocks and the two lepton-singlet ones — the
colour stage is `Step.ofFixedFamily` rather than a classification, and likewise for isospin
where the symbols carry none. That keeps all ten blocks in one shape.

The ten blocks themselves are built in `KineticTerms`, which instantiates the package.

- A. The once-derived chiral component families
- B. The gauge laws of the components at each factor
- C. Products of two components
- D. The kinetic block package

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz ComplexConjugate

namespace IsFermionSector

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

/-!

## A. The once-derived chiral component families

A tower with one covariant derivative mixes into every assignment of one derivative
direction, so its Lorentz law is a sum over such assignments, with one column of the
Lorentz matrix per slot. The value index is untouched by that sum: it still moves by the
contragredient action, exactly as at zero derivatives. Composing the two gives the laws
`IsVectorDualLeftWeyl` and `IsVectorDualRightWeyl` of `MassDimLTEight`, the derivative
slot fundamental and the spinor slot dual.

-/

/-- A sum over the assignments of one derivative direction is a single sum. -/
lemma sum_deriv_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 1 ⊕ Fin 3) → M) :
    ∑ p : Fin 1 → Fin 1 ⊕ Fin 3, f p = ∑ x : Fin 1 ⊕ Fin 3, f ![x] :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 1 ⊕ Fin 3)) _ _ fun p => by
    congr 1
    funext i
    fin_cases i
    simp

/-- The Lorentz transformation of a symbol with one covariant derivative: the derivative
  slot moves by the columns of the Lorentz matrix and the value index by the
  contragredient action. -/
lemma repLorentz_symbol_deriv_one {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {X : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hX : IsLorentzCovDerivTransforms repLorentz rep X) (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ V) :
    repLorentz Λ (X ![μ] φ)
      = ∑ ν, (((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) • X ![ν] (rep.dual Λ φ) := by
  rw [hX Λ 1 ![μ] φ, sum_deriv_one]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  simp

/-- The Lorentz transformation of a component of a once-derived symbol, when the
  coordinate functionals `c` are permuted by the contragredient action with coefficients
  `m`. This is the once-derived form of the laws of `Components`. -/
lemma repLorentz_component_deriv_one {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {X : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hX : IsLorentzCovDerivTransforms repLorentz rep X)
    {c : Fin 2 → Module.Dual ℂ V} {m : SL(2,ℂ) → Fin 2 → Fin 2 → ℂ}
    (hc : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), rep.dual Λ (c a) = ∑ β, m Λ a β • c β)
    (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : Fin 2) :
    repLorentz Λ (X ![μ] (c a))
      = ∑ ν, ∑ β, ((((SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * m Λ a β) • X ![ν] (c β) := by
  rw [repLorentz_symbol_deriv_one hX Λ μ (c a), hc]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul, smul_smul]

/-- Every undotted component family carries a four-vector index and a dual undotted
  spinor index, at one covariant derivative. -/
lemma isVectorDualLeftWeyl_leftComp (i : LeftIdx) :
    IsVectorDualLeftWeyl repLorentz (fun μ => h.leftComp ![μ] i) := by
  cases i with
  | bard f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_bard f)
      (fun Λ a => DownSinglet.repLorentzGroup_conj_dual_dualBasis Λ (a, c)) Λ μ a
  | baru f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_baru f)
      (fun Λ a => UpSinglet.repLorentzGroup_conj_dual_dualBasis Λ (a, c)) Λ μ a
  | Q f c s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_Q f)
      (fun Λ a => QuarkDoublet.repLorentzGroup_dual_dualBasis Λ (a, c, s)) Λ μ a
  | L f s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_L f)
      (fun Λ a => LeptonDoublet.repLorentzGroup_dual_dualBasis Λ (a, s)) Λ μ a
  | bare f =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_bare f)
      (fun Λ a => LeptonSinglet.repLorentzGroup_conj_dual_dualBasis Λ a) Λ μ a

/-- Every dotted component family carries a four-vector index and a dual dotted spinor
  index, at one covariant derivative. -/
lemma isVectorDualRightWeyl_rightComp (i : RightIdx) :
    IsVectorDualRightWeyl repLorentz (fun μ => h.rightComp ![μ] i) := by
  cases i with
  | d f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_d f)
      (fun Λ a => DownSinglet.repLorentzGroup_dual_dualBasis Λ (a, c)) Λ μ a
  | u f c =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_u f)
      (fun Λ a => UpSinglet.repLorentzGroup_dual_dualBasis Λ (a, c)) Λ μ a
  | barQ f c s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_barQ f)
      (fun Λ a => QuarkDoublet.repLorentzGroup_conj_dual_dualBasis Λ (a, c, s)) Λ μ a
  | barL f s =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_barL f)
      (fun Λ a => LeptonDoublet.repLorentzGroup_conj_dual_dualBasis Λ (a, s)) Λ μ a
  | e f =>
    exact fun Λ μ a => repLorentz_component_deriv_one (h.repLorentz_e f)
      (fun Λ a => LeptonSinglet.repLorentzGroup_dual_dualBasis Λ a) Λ μ a

/-!

## B. The gauge laws of the components at each factor

A gauge transformation is a triple, and each of the three index laws that classify a block
constrains one factor of it. So each of the ten symbols is read at each factor in turn:
colour moves only a colour index, isospin only an isospin index, and hypercharge is an
overall scalar whose power is the `6Y` of the species. A symbol eats a covector, so it
carries the contragredient of its value space: the unbarred species come out
anti-fundamental in colour and isospin and the barred ones fundamental, which is what makes
every conjugate pair a fundamental against an anti-fundamental.

- B.1. The down singlet
- B.2. The conjugate down singlet
- B.3. The up singlet
- B.4. The conjugate up singlet
- B.5. The quark doublet
- B.6. The conjugate quark doublet
- B.7. The lepton doublet
- B.8. The conjugate lepton doublet
- B.9. The lepton singlet
- B.10. The conjugate lepton singlet

-/

/-!

### B.1. The down singlet

-/

/-- A colour transformation moves the colour index of a down-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_d (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.dComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • h.dComponent f l (s, a) := by
  rw [h.rep_dComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a down-singlet symbol, which carries no isospin. -/
lemma repGauge_su2_d (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.dComponent f l j)
      = h.dComponent f l j := by
  rw [h.rep_dComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a down-singlet symbol by the square of the scalar,
  the down singlet carrying `6Y = 2`. -/
lemma repGauge_u1_d (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.dComponent f l j)
      = (t : ℂ) ^ 2 • h.dComponent f l j := by
  rw [h.rep_dComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.2. The conjugate down singlet

-/

/-- A colour transformation moves the colour index of a conjugate down-singlet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_bard (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.bardComponent f l (s, c))
      = ∑ a, U.1 a c • h.bardComponent f l (s, a) := by
  rw [h.rep_bardComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate down-singlet symbol. -/
lemma repGauge_su2_bard (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.bardComponent f l j)
      = h.bardComponent f l j := by
  rw [h.rep_bardComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate down-singlet symbol by the square of
  the conjugate scalar, the conjugate down singlet carrying `6Y = -2`. -/
lemma repGauge_u1_bard (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.bardComponent f l j)
      = (star (t : ℂ)) ^ 2 • h.bardComponent f l j := by
  rw [h.rep_bardComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.3. The up singlet

-/

/-- A colour transformation moves the colour index of an up-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_u (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.uComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • h.uComponent f l (s, a) := by
  rw [h.rep_uComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes an up-singlet symbol. -/
lemma repGauge_su2_u (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.uComponent f l j)
      = h.uComponent f l j := by
  rw [h.rep_uComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales an up-singlet symbol by the fourth power of the
  conjugate scalar, the up singlet carrying `6Y = -4`. -/
lemma repGauge_u1_u (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.uComponent f l j)
      = (star (t : ℂ)) ^ 4 • h.uComponent f l j := by
  rw [h.rep_uComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.4. The conjugate up singlet

-/

/-- A colour transformation moves the colour index of a conjugate up-singlet symbol by the
  matrix itself, the index being fundamental. -/
lemma repGauge_su3_baru (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.baruComponent f l (s, c))
      = ∑ a, U.1 a c • h.baruComponent f l (s, a) := by
  rw [h.rep_baruComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate up-singlet symbol. -/
lemma repGauge_su2_baru (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.baruComponent f l j)
      = h.baruComponent f l j := by
  rw [h.rep_baruComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate up-singlet symbol by the fourth power
  of the scalar, the conjugate up singlet carrying `6Y = 4`. -/
lemma repGauge_u1_baru (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.baruComponent f l j)
      = (t : ℂ) ^ 4 • h.baruComponent f l j := by
  rw [h.rep_baruComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.5. The quark doublet

-/

/-- A colour transformation moves the colour index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_Q (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.QComponent f l (s, c, w))
      = ∑ a, conj (U.1 a c) • h.QComponent f l (s, a, w) := by
  rw [h.rep_QComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_Q (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.QComponent f l (s, c, w))
      = ∑ a, conj (V.1 a w) • h.QComponent f l (s, c, a) := by
  rw [h.rep_QComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a quark-doublet symbol by the conjugate scalar,
  the quark doublet carrying `6Y = -1`. -/
lemma repGauge_u1_Q (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.QComponent f l (s, c, w))
      = star (t : ℂ) • h.QComponent f l (s, c, w) := by
  rw [h.rep_QComponent]
  fin_cases w <;> simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.6. The conjugate quark doublet

-/

/-- A colour transformation moves the colour index of a conjugate quark-doublet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_barQ (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barQComponent f l (s, c, w))
      = ∑ a, U.1 a c • h.barQComponent f l (s, a, w) := by
  rw [h.rep_barQComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two]
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a conjugate quark-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barQ (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barQComponent f l (s, c, w))
      = ∑ a, V.1 a w • h.barQComponent f l (s, c, a) := by
  rw [h.rep_barQComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a conjugate quark-doublet symbol by the scalar,
  the conjugate quark doublet carrying `6Y = 1`. -/
lemma repGauge_u1_barQ (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barQComponent f l (s, c, w))
      = (t : ℂ) • h.barQComponent f l (s, c, w) := by
  rw [h.rep_barQComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.7. The lepton doublet

-/

/-- A colour transformation fixes a lepton-doublet symbol, which carries no colour. -/
lemma repGauge_su3_L (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.LComponent f l j)
      = h.LComponent f l j := by
  rw [h.rep_LComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a lepton-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_L (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.LComponent f l (s, w))
      = ∑ a, conj (V.1 a w) • h.LComponent f l (s, a) := by
  rw [h.rep_LComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a lepton-doublet symbol by the cube of the scalar,
  the lepton doublet carrying `6Y = 3`. -/
lemma repGauge_u1_L (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.LComponent f l j)
      = (t : ℂ) ^ 3 • h.LComponent f l j := by
  rw [h.rep_LComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.8. The conjugate lepton doublet

-/

/-- A colour transformation fixes a conjugate lepton-doublet symbol, which carries no
  colour. -/
lemma repGauge_su3_barL (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barLComponent f l j)
      = h.barLComponent f l j := by
  rw [h.rep_barLComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a conjugate lepton-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barL (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barLComponent f l (s, w))
      = ∑ a, V.1 a w • h.barLComponent f l (s, a) := by
  rw [h.rep_barLComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a conjugate lepton-doublet symbol by the cube of
  the conjugate scalar, the conjugate lepton doublet carrying `6Y = -3`. -/
lemma repGauge_u1_barL (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barLComponent f l (s, w))
      = (star (t : ℂ)) ^ 3 • h.barLComponent f l (s, w) := by
  rw [h.rep_barLComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.9. The lepton singlet

-/

/-- A colour transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su3_e (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.eComponent f l s)
      = h.eComponent f l s := by
  rw [h.rep_eComponent]
  simp

/-- An isospin transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su2_e (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.eComponent f l s)
      = h.eComponent f l s := by
  rw [h.rep_eComponent]
  simp

/-- A hypercharge transformation scales a lepton-singlet symbol by the sixth power of the
  scalar, the lepton singlet carrying `6Y = 6`. -/
lemma repGauge_u1_e (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.eComponent f l s)
      = (t : ℂ) ^ 6 • h.eComponent f l s := by
  rw [h.rep_eComponent]
  simp [unitary_inv_coe]

/-!

### B.10. The conjugate lepton singlet

-/

/-- A colour transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su3_bare (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.bareComponent f l s)
      = h.bareComponent f l s := by
  rw [h.rep_bareComponent]
  simp

/-- An isospin transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su2_bare (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.bareComponent f l s)
      = h.bareComponent f l s := by
  rw [h.rep_bareComponent]
  simp

/-- A hypercharge transformation scales a conjugate lepton-singlet symbol by the sixth
  power of the conjugate scalar, the conjugate lepton singlet carrying `6Y = -6`. -/
lemma repGauge_u1_bare (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.bareComponent f l s)
      = (star (t : ℂ)) ^ 6 • h.bareComponent f l s := by
  rw [h.rep_bareComponent]
  simp [unitary_inv_coe]

/-!

## C. Products of two components

A block is a product of two components, and each of its index laws comes from the laws of
the two factors: the representation respects multiplication, so the two transform
independently and their coefficients multiply. Which slot of the classifier a factor
occupies is decided by its variance, the fundamental one going first, so each law comes in
two arrangements according to which factor is the barred one.

-/

/-- A product of a component with a fundamental colour index and one with an
  anti-fundamental colour index carries one colour index of each kind. -/
lemma isSU3FunAntiFun_mul
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {A C : Fin 3 → B}
    (hA : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (A c) = ∑ a, U.1 a c • A a)
    (hC : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (C c) = ∑ a, conj (U.1 a c) • C a) :
    IsSU3FunAntiFun B repGauge (fun l : Fin 2 → Fin 3 => A (l 0) * C (l 1)) where
  repGauge_T U l := by
    rw [hmul, hA, hC, Finset.sum_mul_sum, IsSU3FunAntiFun.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      smul_mul_smul_comm _ _ _ _

/-- The same with the two factors exchanged, the anti-fundamental one first. -/
lemma isSU3FunAntiFun_mul_swap
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {A C : Fin 3 → B}
    (hA : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (A c) = ∑ a, conj (U.1 a c) • A a)
    (hC : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 3),
      repGauge ((U, 1, 1) : GaugeGroupI) (C c) = ∑ a, U.1 a c • C a) :
    IsSU3FunAntiFun B repGauge (fun l : Fin 2 → Fin 3 => A (l 1) * C (l 0)) where
  repGauge_T U l := by
    rw [hmul, hA, hC, Finset.sum_mul_sum, IsSU3FunAntiFun.sum_pi_two, Finset.sum_comm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm, mul_comm]

/-- A product of a component with a fundamental isospin index and one with an
  anti-fundamental isospin index carries one isospin index of each kind. -/
lemma isSU2FunAntiFun_mul
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {A C : Fin 2 → B}
    (hA : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (A w) = ∑ a, V.1 a w • A a)
    (hC : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (C w) = ∑ a, conj (V.1 a w) • C a) :
    IsSU2FunAntiFun B repGauge (fun l : Fin 2 → Fin 2 => A (l 0) * C (l 1)) where
  repGauge_T V l := by
    rw [hmul, hA, hC, Finset.sum_mul_sum, IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      smul_mul_smul_comm _ _ _ _

/-- The same with the two factors exchanged, the anti-fundamental one first. -/
lemma isSU2FunAntiFun_mul_swap
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {A C : Fin 2 → B}
    (hA : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (A w) = ∑ a, conj (V.1 a w) • A a)
    (hC : ∀ (V : specialUnitaryGroup (Fin 2) ℂ) (w : Fin 2),
      repGauge ((1, V, 1) : GaugeGroupI) (C w) = ∑ a, V.1 a w • C a) :
    IsSU2FunAntiFun B repGauge (fun l : Fin 2 → Fin 2 => A (l 1) * C (l 0)) where
  repGauge_T V l := by
    rw [hmul, hA, hC, Finset.sum_mul_sum, IsSU2BiFundamental.sum_pi_two, Finset.sum_comm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm, mul_comm]

/-- A product of two components that a gauge transformation fixes is fixed by it: the
  form in which a block whose symbols carry no colour, or no isospin, supplies the
  corresponding stage. -/
lemma repGauge_mul_fixed
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {g : GaugeGroupI} {a c : B} (ha : repGauge g a = a) (hc : repGauge g c = c) :
    repGauge g (a * c) = a * c := by
  rw [hmul, ha, hc]

/-- A product of two components that a gauge transformation scales by reciprocal scalars
  is fixed by it: the form in which the hypercharges of a species and its conjugate
  cancel. -/
lemma repGauge_mul_smul_fixed
    (hmul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    {g : GaugeGroupI} {z z' : ℂ} {a c : B} (hz : z * z' = 1)
    (ha : repGauge g a = z • a) (hc : repGauge g c = z' • c) :
    repGauge g (a * c) = a * c := by
  rw [hmul, ha, hc, smul_mul_smul_comm, hz, one_smul]



/-- A finite sum of families carrying one four-vector index and a pair of dual
  opposite-chirality Weyl indices is such a family again: the colour and isospin
  contractions are Lorentz spectators. -/
lemma isVectorDualLeftRightWeyl_sum {ι : Type} [Fintype ι]
    {T : ι → (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
    (hT : ∀ i, IsVectorDualLeftRightWeyl B repLorentz (T i)) :
    IsVectorDualLeftRightWeyl B repLorentz (fun p => ∑ i, T i p) where
  repLorentz_T Λ μ l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      (hT i).repLorentz_T Λ μ l, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- The conjugate Pauli contraction lies in the span of the components it contracts. -/
lemma pauliBarContraction_mem_iSup_span (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) :
    IsVectorDualLeftRightWeyl.pauliBarContraction (T := T) ∈ ⨆ q, ℂ ∙ T q := by
  rw [IsVectorDualLeftRightWeyl.pauliBarContraction]
  exact Submodule.sum_mem _ fun μ _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (μ, a) (Submodule.mem_span_singleton_self _))

/-- A unitary scalar times its conjugate is one, in the order the hypercharge cancellation
  of a species against its conjugate needs. -/
lemma unitary_mul_star_coe (t : unitary ℂ) : (t : ℂ) * star (t : ℂ) = 1 := t.2.2

/-- The conjugate of a unitary scalar times itself is one. -/
lemma unitary_star_mul_coe (t : unitary ℂ) : star (t : ℂ) * (t : ℂ) = 1 := t.2.1

/-!

## D. The kinetic block package

A kinetic block is classified in three stages, and every block runs the same three: colour,
then isospin, then Lorentz, each contraction a spectator of the ones after it. `KineticBlock`
packages a block together with the three steps, and from the package alone come the kinetic
term, its invariance under both groups, and the peeling of the block down to the line
through it.

The colour and isospin indices of the block are listed in the order the classifiers read
them, fundamental first; a block whose symbols carry no colour, or no isospin, simply
ignores the corresponding pair and supplies `Step.ofFixedFamily` for that stage. Each step
comes with the fact that its contraction lies in the submodule it classifies, which is what
carries the invariance of one stage through the stages after it.

-/

section Blocks

variable {B : Type} [Ring B] [Algebra ℂ B]
  (repGauge : Representation ℂ GaugeGroupI B) (repLorentz : Representation ℂ SL(2,ℂ) B)

/-- One kinetic block of the fermion sector, together with the three classifications its
  indices admit. The block is indexed by the derivative direction, the pair of spinor
  indices in the order `(undotted, dotted)`, the pair of colour indices and the pair of
  isospin indices, each pair in the order `(fundamental, anti-fundamental)`. -/
structure KineticBlock where
  /-- The components of the block. -/
  blk : (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B
  /-- The colour stage: at fixed derivative, spinor and isospin indices the colour pair is
    classified, by the delta contraction if the block carries colour and trivially if it
    does not. -/
  colourStep : ∀ (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (w w' : Fin 2),
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ blk q l (n 0) (n 1) w w')
  /-- The colour contraction lies in the span of the components it contracts. -/
  colourStep_mem : ∀ q l w w', (colourStep q l w w').contraction
    ∈ ⨆ n : Fin 2 → Fin 3, ℂ ∙ blk q l (n 0) (n 1) w w'
  /-- The isospin stage, applied to the colour contraction. -/
  isospinStep : ∀ (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (colourStep q l (n 0) (n 1)).contraction)
  /-- The isospin contraction lies in the span of the colour contractions. -/
  isospinStep_mem : ∀ q l, (isospinStep q l).contraction
    ∈ ⨆ n : Fin 2 → Fin 2, ℂ ∙ (colourStep q l (n 0) (n 1)).contraction
  /-- The Lorentz stage, applied to the doubly contracted block: one four-vector index
    against a dual dotted and a dual undotted spinor index. -/
  lorentzStep : Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
    (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ℂ ∙ (isospinStep p.1 p.2).contraction)
  /-- The Lorentz contraction lies in the span of the isospin contractions. -/
  lorentzStep_mem : lorentzStep.contraction
    ∈ ⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ℂ ∙ (isospinStep p.1 p.2).contraction
  /-- A hypercharge transformation fixes every component of the block, the hypercharges of
    a species and its conjugate cancelling. -/
  hyper : ∀ (t : unitary ℂ) q l c c' w w',
    repGauge ((1, 1, t) : GaugeGroupI) (blk q l c c' w w') = blk q l c c' w w'

namespace KineticBlock

variable {repGauge repLorentz} (K : KineticBlock repGauge repLorentz)

/-- The kinetic term of a block: the conjugate Pauli contraction of its doubly contracted
  form, which is `ψ̄ σ̄^μ ∂_μ ψ` with the colour and isospin indices already joined. -/
noncomputable def kineticTerm : B := K.lorentzStep.contraction

/-- The join, over the derivative, spinor and isospin indices, of the colour spans of the
  block: what the block submodule is peeled from. -/
noncomputable def blockSpan : Submodule ℂ B :=
  ⨆ k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
    ⨆ n : Fin 2 → Fin 3, ℂ ∙ K.blk k.1 k.2.1 (n 0) (n 1) k.2.2.1 k.2.2.2

/-- The three stages in sequence: the block span peels to the line through the kinetic
  term. -/
lemma peels :
    Peels (gaugeLorentzMaps repGauge repLorentz) K.blockSpan (ℂ ∙ K.kineticTerm) := by
  rw [blockSpan, kineticTerm]
  have hc := Peels.iSup_step (σ := fun U : specialUnitaryGroup (Fin 3) ℂ =>
    repGauge ((U, 1, 1) : GaugeGroupI))
    (V := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
      ⨆ n : Fin 2 → Fin 3, ℂ ∙ K.blk k.1 k.2.1 (n 0) (n 1) k.2.2.1 k.2.2.2)
    fun k => K.colourStep k.1 k.2.1 k.2.2.1 k.2.2.2
  have hi := Peels.iSup_step (σ := fun V : specialUnitaryGroup (Fin 2) ℂ =>
    repGauge ((1, V, 1) : GaugeGroupI))
    (V := fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
      ⨆ n : Fin 2 → Fin 2, ℂ ∙ (K.colourStep p.1 p.2 (n 0) (n 1)).contraction)
    fun p => K.isospinStep p.1 p.2
  have h1 := Peels.ofSU3 (repLorentz := repLorentz) hc
  have h2 := Peels.ofSU2 (repLorentz := repLorentz) hi
  have h3 := Peels.ofLorentz (repGauge := repGauge) K.lorentzStep.peels
  refine (h1.mono_right ?_).trans (h2.trans h3)
  refine iSup_le fun k => le_iSup_of_le (k.1, k.2.1) (le_iSup_of_le ![k.2.2.1, k.2.2.2] ?_)
  simp

/-- The kinetic term lies in any submodule containing every component of the block: each
  contraction lies in the span of the objects of the stage before it. -/
lemma kineticTerm_mem {V : Submodule ℂ B}
    (hV : ∀ q l c c' w w', K.blk q l c c' w w' ∈ V) : K.kineticTerm ∈ V := by
  have hcol : ∀ q l w w', (K.colourStep q l w w').contraction ∈ V := fun q l w w' =>
    (iSup_le fun n => (Submodule.span_singleton_le_iff_mem _ _).2 (hV _ _ _ _ _ _))
      (K.colourStep_mem q l w w')
  have hiso : ∀ q l, (K.isospinStep q l).contraction ∈ V := fun q l =>
    (iSup_le fun n => (Submodule.span_singleton_le_iff_mem _ _).2 (hcol _ _ _ _))
      (K.isospinStep_mem q l)
  exact (iSup_le fun p => (Submodule.span_singleton_le_iff_mem _ _).2 (hiso _ _))
    K.lorentzStep_mem

/-- The kinetic term is fixed by the colour factor: the colour contractions are, and every
  later stage stays inside their span. -/
lemma repGauge_su3_kineticTerm (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge ((U, 1, 1) : GaugeGroupI) K.kineticTerm = K.kineticTerm := by
  have hiso : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ∀ U',
      repGauge ((U', 1, 1) : GaugeGroupI) (K.isospinStep p.1 p.2).contraction
        = (K.isospinStep p.1 p.2).contraction := fun p U' =>
    isFixedBy_iSup_span_singleton
      (fun n U'' => (K.colourStep p.1 p.2 (n 0) (n 1)).contraction_fixed U'') U' _
      (K.isospinStep_mem p.1 p.2)
  exact isFixedBy_iSup_span_singleton (fun p U' => hiso p U') U _ K.lorentzStep_mem

/-- The kinetic term is fixed by the isospin factor. -/
lemma repGauge_su2_kineticTerm (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge ((1, V, 1) : GaugeGroupI) K.kineticTerm = K.kineticTerm :=
  isFixedBy_iSup_span_singleton
    (fun p V' => (K.isospinStep p.1 p.2).contraction_fixed V') V _ K.lorentzStep_mem

/-- The kinetic term is fixed by the hypercharge factor, the hypercharges of a species and
  its conjugate cancelling on every component of the block. -/
lemma repGauge_u1_kineticTerm (t : unitary ℂ) :
    repGauge ((1, 1, t) : GaugeGroupI) K.kineticTerm = K.kineticTerm := by
  have hcol : ∀ q l w w', ∀ t' : unitary ℂ,
      repGauge ((1, 1, t') : GaugeGroupI) (K.colourStep q l w w').contraction
        = (K.colourStep q l w w').contraction := fun q l w w' t' =>
    isFixedBy_iSup_span_singleton (fun n t'' => K.hyper t'' q l (n 0) (n 1) w w') t' _
      (K.colourStep_mem q l w w')
  have hiso : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2, ∀ t' : unitary ℂ,
      repGauge ((1, 1, t') : GaugeGroupI) (K.isospinStep p.1 p.2).contraction
        = (K.isospinStep p.1 p.2).contraction := fun p t' =>
    isFixedBy_iSup_span_singleton (fun n t'' => hcol p.1 p.2 (n 0) (n 1) t'') t' _
      (K.isospinStep_mem p.1 p.2)
  exact isFixedBy_iSup_span_singleton (fun p t' => hiso p t') t _ K.lorentzStep_mem

/-- The kinetic term is gauge invariant: a gauge transformation is the product of its
  colour, isospin and hypercharge parts, and each fixes it. -/
lemma repGauge_kineticTerm (g : GaugeGroupI) : repGauge g K.kineticTerm = K.kineticTerm :=
  forall_repGauge_eq_self K.repGauge_su3_kineticTerm K.repGauge_su2_kineticTerm
    K.repGauge_u1_kineticTerm g

/-- The kinetic term is Lorentz invariant, being the conjugate Pauli contraction of a
  vector dual left-right Weyl family. -/
lemma repLorentz_kineticTerm (Λ : SL(2,ℂ)) :
    repLorentz Λ K.kineticTerm = K.kineticTerm := K.lorentzStep.contraction_fixed Λ

end KineticBlock

end Blocks

end IsFermionSector

end StandardModel
