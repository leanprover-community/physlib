/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
/-!
# The `SU(2)` permutation decomposition of the neutral gauge sector

The gauge weight decomposition of a gauge mass-weight submodule already isolates its
weight-zero piece: the field strength evaluated on the four directions of the adjoint
that the gauge torus fixes, namely the two `su(3)` Cartan generators, the `su(2)` Cartan
generator and hypercharge.  The gauge weight cannot see any further into that piece,
because the torus fixes all four directions alike.

The Weyl element `gaugeSU2Perm` does see further.  It is trivial on colour and on
hypercharge, so it fixes the two `su(3)` Cartan directions and the `u(1)` direction; on
isospin it is the reflection sending the Cartan generator to its negative, so it negates
the neutral `W`.  The weight-zero piece therefore carries an `SU2PermDecomposition`
concentrated in the grades `0` and `2`: grade `0` is the colour-neutral and hypercharge
content, grade `2` is the neutral `W` alone.  This is exactly the separation that the
gauge weight is blind to, and it is what lets a `Z`-like combination be told apart from
a photon-like one by a grading.

The grades `1` and `3`, at the eigenvalues `± i`, are empty on that piece.  They are the
odd-isospin-degree grades, and the field strength is linear in a real adjoint direction,
so nothing in the gauge sector reaches them.

Mass weight eight is the one weight whose weight-zero piece is more than a piece of a
derivative submodule: it also holds the products pairing a raising vector against the
matching lowering vector, and the products of two weight-zero vectors.  The colour
products are fixed outright, and the products of two weight-zero vectors are graded by
adding the grades of their factors.  The isospin products need care, because the Weyl
element exchanges the two isospin root vectors rather than scaling them; it is their
symmetric and antisymmetric combinations that are graded, in grades zero and two.

## Table of contents

- A. The Weyl element on the coordinate functionals of the adjoint
- B. The Weyl element on the field-strength symbols
- C. The decomposition of the weight-zero piece of the derivative submodules
- D. The graded pieces
- E. The gauge-factor parts at mass weight eight
- F. Transport along the mass weights

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups GaugeAlgebra

/-!

## A. The Weyl element on the coordinate functionals of the adjoint

The Weyl element acts on the gauge algebra by conjugation, trivially on the colour and
hypercharge factors and by the reflection `!![0, -1; 1, 0]` on isospin.  In the standard
basis this is diagonal with entries `± 1`: everything is fixed except the `σ¹` and `σ³`
directions, which are negated.

-/

/-- The colour block of the inverse Weyl element is the identity matrix: `gaugeSU2Perm`
  is trivial on `SU(3)`. -/
lemma toSU3_inv_gaugeSU2Perm :
    ((GaugeGroupI.toSU3 gaugeSU2Perm⁻¹ : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  rw [map_inv, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [gaugeSU2Perm, GaugeGroupI.toSU3]

/-- The isospin block of the inverse Weyl element is `!![0, 1; -1, 0]`. -/
lemma toSU2_inv_gaugeSU2Perm :
    ((GaugeGroupI.toSU2 gaugeSU2Perm⁻¹ : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  rw [map_inv]
  exact su2Perm_inv_coe

/-- The Weyl element leaves the colour block of a gauge algebra element alone. -/
lemma adjointMap_inv_gaugeSU2Perm_toSU3Matrix (x : GaugeAlgebra) :
    (adjointMap gaugeSU2Perm⁻¹ x).toSU3Matrix = x.toSU3Matrix := by
  rw [adjointMap_toSU3Matrix, toSU3_inv_gaugeSU2Perm, one_mul, star_one, mul_one]

/-- The Weyl element leaves the hypercharge value of a gauge algebra element alone. -/
lemma adjointMap_inv_gaugeSU2Perm_toU1Value (x : GaugeAlgebra) :
    (adjointMap gaugeSU2Perm⁻¹ x).toU1Value = x.toU1Value := rfl

/-- The Weyl element conjugates the isospin block by `!![0, 1; -1, 0]`, which exchanges
  the two diagonal entries and negates the two off-diagonal ones. -/
lemma adjointMap_inv_gaugeSU2Perm_toSU2Matrix (x : GaugeAlgebra) :
    (adjointMap gaugeSU2Perm⁻¹ x).toSU2Matrix
      = !![x.toSU2Matrix 1 1, -x.toSU2Matrix 1 0;
          -x.toSU2Matrix 0 1, x.toSU2Matrix 0 0] := by
  rw [adjointMap_toSU2Matrix, toSU2_inv_gaugeSU2Perm]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- The Weyl element fixes the colour Cartan directions and hypercharge: the three
  weight-zero directions of the adjoint on which it acts trivially. -/
lemma dualMap_coord_cartanIdx_ne_two {c : Fin 4} (hc : c ≠ 2) :
    (adjointMap gaugeSU2Perm⁻¹).dualMap (stdBasis.coord (cartanIdx c))
      = stdBasis.coord (cartanIdx c) := by
  refine LinearMap.ext fun x => ?_
  have h3 := adjointMap_inv_gaugeSU2Perm_toSU3Matrix x
  have h1 := adjointMap_inv_gaugeSU2Perm_toU1Value x
  fin_cases c
  · simp only [LinearMap.dualMap_apply, cartanIdx, stdBasis_coord_apply, stdCoeff,
      gellMannCoeff, h3]
  · simp only [LinearMap.dualMap_apply, cartanIdx, stdBasis_coord_apply, stdCoeff,
      gellMannCoeff, h3]
  · exact absurd rfl hc
  · simp only [LinearMap.dualMap_apply, cartanIdx, stdBasis_coord_apply, stdCoeff, h1]

/-- The Weyl element negates the isospin Cartan direction: a Weyl reflection sends the
  Cartan generator of `su(2)` to its negative. -/
lemma dualMap_coord_cartanIdx_two :
    (adjointMap gaugeSU2Perm⁻¹).dualMap (stdBasis.coord (cartanIdx 2))
      = -stdBasis.coord (cartanIdx 2) := by
  refine LinearMap.ext fun x => ?_
  have htr : Matrix.trace x.toSU2Matrix = 0 := x.2.1.2.2
  rw [Matrix.trace_fin_two] at htr
  have h11 : x.toSU2Matrix 1 1 = -x.toSU2Matrix 0 0 := by linear_combination htr
  simp only [LinearMap.dualMap_apply, cartanIdx, stdBasis_coord_apply, stdCoeff,
    pauliCoeff, adjointMap_inv_gaugeSU2Perm_toSU2Matrix, LinearMap.neg_apply]
  simp [h11]

/-- The Weyl element fixes every colour coordinate functional, Cartan or not: it is
  trivial on `SU(3)`. -/
lemma dualMap_coord_inl (a : Fin 8) :
    (adjointMap gaugeSU2Perm⁻¹).dualMap (stdBasis.coord (Sum.inl a))
      = stdBasis.coord (Sum.inl a) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.dualMap_apply, stdBasis_coord_apply, stdCoeff,
    adjointMap_inv_gaugeSU2Perm_toSU3Matrix]

/-- The Weyl element negates the first isospin coordinate functional: the reflection
  turns the `σ¹` direction around. -/
lemma dualMap_coord_inr_inl_zero :
    (adjointMap gaugeSU2Perm⁻¹).dualMap (stdBasis.coord (Sum.inr (Sum.inl 0)))
      = -stdBasis.coord (Sum.inr (Sum.inl 0)) := by
  refine LinearMap.ext fun x => ?_
  have h10 : x.toSU2Matrix 1 0 = (starRingEnd ℂ) (x.toSU2Matrix 0 1) :=
    entry_symm_of_star_eq x.2.1.2.1 0 1
  simp only [LinearMap.dualMap_apply, stdBasis_coord_apply, stdCoeff, pauliCoeff,
    adjointMap_inv_gaugeSU2Perm_toSU2Matrix, LinearMap.neg_apply]
  simp [h10]

/-- The Weyl element fixes the second isospin coordinate functional: the `σ²` direction
  is the axis of the reflection. -/
lemma dualMap_coord_inr_inl_one :
    (adjointMap gaugeSU2Perm⁻¹).dualMap (stdBasis.coord (Sum.inr (Sum.inl 1)))
      = stdBasis.coord (Sum.inr (Sum.inl 1)) := by
  refine LinearMap.ext fun x => ?_
  have h10 : x.toSU2Matrix 1 0 = (starRingEnd ℂ) (x.toSU2Matrix 0 1) :=
    entry_symm_of_star_eq x.2.1.2.1 0 1
  simp only [LinearMap.dualMap_apply, stdBasis_coord_apply, stdCoeff, pauliCoeff,
    adjointMap_inv_gaugeSU2Perm_toSU2Matrix]
  simp [h10]

/-- The grade carried by each weight-zero direction of the adjoint under the Weyl
  element: the two colour Cartan directions and hypercharge are fixed and so have grade
  zero, while the isospin Cartan direction is negated and so has grade two. -/
def cartanSU2PermGrade : Fin 4 → ZMod 4
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

/-!

## B. The Weyl element on the field-strength symbols

-/

include h in
/-- The Weyl element fixes the field strength evaluated on a colour Cartan direction or
  on hypercharge. -/
lemma repGauge_gaugeSU2Perm_F_cartanIdx_ne_two {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) {c : Fin 4} (hc : c ≠ 2) :
    repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (cartanIdx c)))
      = F l μ ν (stdBasis.coord (cartanIdx c)) :=
  h.repGauge_fixed gaugeSU2Perm l μ ν _ (dualMap_coord_cartanIdx_ne_two hc)

include h in
/-- The Weyl element negates the field strength evaluated on the isospin Cartan
  direction: the neutral `W` is odd. -/
lemma repGauge_gaugeSU2Perm_F_cartanIdx_two {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (cartanIdx 2)))
      = -F l μ ν (stdBasis.coord (cartanIdx 2)) := by
  rw [h.repGauge_F, dualMap_coord_cartanIdx_two, map_neg]

include h in
/-- The field strength on each weight-zero direction of the adjoint is an eigenvector of
  the Weyl element, at the sign recorded by `cartanSU2PermGrade`. -/
lemma repGauge_gaugeSU2Perm_F_cartanIdx {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 4) :
    repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (cartanIdx c)))
      = su2PermSign (cartanSU2PermGrade c) • F l μ ν (stdBasis.coord (cartanIdx c)) := by
  rcases eq_or_ne c 2 with rfl | hc
  · rw [h.repGauge_gaugeSU2Perm_F_cartanIdx_two l μ ν,
      show cartanSU2PermGrade 2 = 2 from by decide, su2PermSign_two, neg_one_smul]
  · have hg : cartanSU2PermGrade c = 0 := by revert hc; fin_cases c <;> decide
    rw [h.repGauge_gaugeSU2Perm_F_cartanIdx_ne_two l μ ν hc, hg, su2PermSign_zero,
      one_smul]

include h in
/-- The Weyl element fixes the field strength on any colour direction of the adjoint. -/
lemma repGauge_gaugeSU2Perm_F_inl {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (a : Fin 8) :
    repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (Sum.inl a)))
      = F l μ ν (stdBasis.coord (Sum.inl a)) :=
  h.repGauge_fixed gaugeSU2Perm l μ ν _ (dualMap_coord_inl a)

/-- The Weyl element fixes the colour raising vectors of the adjoint: an isospin
  reflection leaves colour alone. -/
lemma repGauge_gaugeSU2Perm_adjVec_inl {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) {r : Fin 4} (hr : r ≠ 3) :
    repGauge gaugeSU2Perm (h.adjVec l μ ν (Sum.inl r))
      = h.adjVec l μ ν (Sum.inl r) := by
  have key : ∀ a b : Fin 8, repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (Sum.inl a))
        + Complex.I • F l μ ν (stdBasis.coord (Sum.inl b)))
      = F l μ ν (stdBasis.coord (Sum.inl a))
        + Complex.I • F l μ ν (stdBasis.coord (Sum.inl b)) := fun a b => by
    rw [map_add, map_smul, h.repGauge_gaugeSU2Perm_F_inl, h.repGauge_gaugeSU2Perm_F_inl]
  fin_cases r
  · exact key 0 1
  · exact key 3 4
  · exact key 5 6
  · exact absurd rfl hr

/-- The Weyl element fixes the colour lowering vectors of the adjoint. -/
lemma repGauge_gaugeSU2Perm_adjVec_inr_inl {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) {r : Fin 4} (hr : r ≠ 3) :
    repGauge gaugeSU2Perm (h.adjVec l μ ν (Sum.inr (Sum.inl r)))
      = h.adjVec l μ ν (Sum.inr (Sum.inl r)) := by
  have key : ∀ a b : Fin 8, repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (Sum.inl a))
        - Complex.I • F l μ ν (stdBasis.coord (Sum.inl b)))
      = F l μ ν (stdBasis.coord (Sum.inl a))
        - Complex.I • F l μ ν (stdBasis.coord (Sum.inl b)) := fun a b => by
    rw [map_sub, map_smul, h.repGauge_gaugeSU2Perm_F_inl, h.repGauge_gaugeSU2Perm_F_inl]
  fin_cases r
  · exact key 0 1
  · exact key 3 4
  · exact key 5 6
  · exact absurd rfl hr

/-- The Weyl element sends the isospin raising vector to minus the lowering vector: it
  is the reflection exchanging the two isospin roots. -/
lemma repGauge_gaugeSU2Perm_adjVec_isospin_raising {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGauge gaugeSU2Perm (h.adjVec l μ ν (Sum.inl 3))
      = -h.adjVec l μ ν (Sum.inr (Sum.inl 3)) := by
  show repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 0)))
      + Complex.I • F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 1))))
    = -(F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 0)))
      - Complex.I • F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 1))))
  rw [map_add, map_smul, h.repGauge_F, h.repGauge_F, dualMap_coord_inr_inl_zero,
    dualMap_coord_inr_inl_one, map_neg]
  module

/-- The Weyl element sends the isospin lowering vector to minus the raising vector. -/
lemma repGauge_gaugeSU2Perm_adjVec_isospin_lowering {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGauge gaugeSU2Perm (h.adjVec l μ ν (Sum.inr (Sum.inl 3)))
      = -h.adjVec l μ ν (Sum.inl 3) := by
  show repGauge gaugeSU2Perm (F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 0)))
      - Complex.I • F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 1))))
    = -(F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 0)))
      + Complex.I • F l μ ν (stdBasis.coord (Sum.inr (Sum.inl 1))))
  rw [map_sub, map_smul, h.repGauge_F, h.repGauge_F, dualMap_coord_inr_inl_zero,
    dualMap_coord_inr_inl_one, map_neg]
  module

/-- Every weight vector of the adjoint lies in the derivative submodule it is built
  from. -/
lemma adjVec_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : Fin 4 ⊕ Fin 4 ⊕ Fin 4) :
    h.adjVec l μ ν k ∈ h.derivSubmodule n := by
  have hF : ∀ φ, F l μ ν φ ∈ h.derivSubmodule n := fun φ => by
    rw [derivSubmodule]
    exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
      (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))
  match k with
  | Sum.inl r => exact Submodule.add_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
  | Sum.inr (Sum.inl r) => exact Submodule.sub_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
  | Sum.inr (Sum.inr c) => exact hF _

/-- Any two weight vectors of the adjoint commute: the gauge sector is bosonic. -/
lemma adjVec_commute {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (k : Fin 4 ⊕ Fin 4 ⊕ Fin 4) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k' : Fin 4 ⊕ Fin 4 ⊕ Fin 4) :
    Commute (h.adjVec l μ ν k) (h.adjVec l' μ' ν' k') :=
  h.commute_of_mem_derivSubmodule (h.adjVec_mem_derivSubmodule l μ ν k)
    (h.adjVec_mem_derivSubmodule l' μ' ν' k')

/-!

## C. The decomposition of the weight-zero piece of the derivative submodules

-/

/-- The `SU(2)` permutation decomposition of the weight-zero piece of a gauge derivative
  submodule: the reusable core of this file.  The weight-zero piece is spanned by the
  field strength on the four fixed directions of the adjoint, and each of those four
  spans is graded by `cartanSU2PermGrade`. -/
noncomputable def derivSubmoduleGaugeWeightPieceZeroSU2Perm (n : ℕ) :
    SU2PermDecomposition repGauge ((h.derivSubmoduleGaugeWeight n).piece 0) where
  piece k := ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
    (c : Fin 4) (_ : cartanSU2PermGrade c = k),
    ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c))
  piece_le := by
    intro k x hx
    have key : (⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
        (c : Fin 4) (_ : cartanSU2PermGrade c = k),
        ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)))
        ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) (su2PermSign k) := by
      refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c =>
        iSup_le fun hc => ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Module.End.mem_eigenspace_iff.mpr ?_
      rw [h.repGauge_gaugeSU2Perm_F_cartanIdx l μ ν c, hc]
    exact Module.End.mem_eigenspace_iff.mp (key hx)
  iSup_piece := by
    rw [h.derivSubmoduleGaugeWeight_piece_zero n]
    refine le_antisymm (iSup_le fun k => iSup_le fun l => iSup_le fun μ =>
      iSup_le fun ν => iSup_le fun c => iSup_le fun _ => ?_) ?_
    · exact le_iSup_of_le l (le_iSup_of_le μ (le_iSup_of_le ν (le_iSup_of_le c le_rfl)))
    · refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c => ?_
      exact le_iSup_of_le (cartanSU2PermGrade c) (le_iSup_of_le l (le_iSup_of_le μ
        (le_iSup_of_le ν (le_iSup_of_le c (le_iSup_of_le rfl le_rfl)))))

/-!

## D. The graded pieces

-/

/-- The grade-zero piece of the core decomposition: the two colour Cartan directions of
  the field strength together with hypercharge. -/
lemma derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm n).piece 0
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        (ℂ ∙ h.gluonField l μ ν 2 ⊔ ℂ ∙ h.gluonField l μ ν 7
          ⊔ ℂ ∙ h.hyperchargeField l μ ν) := by
  have hzero : ∀ c : Fin 4, cartanSU2PermGrade c = 0 → c = 0 ∨ c = 1 ∨ c = 3 := by decide
  refine iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν => ?_
  refine le_antisymm (iSup_le fun c => iSup_le fun hc => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · rcases hzero c hc with rfl | rfl | rfl
    · exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
    · exact le_sup_of_le_left (le_sup_of_le_right le_rfl)
    · exact le_sup_right
  · exact le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl)
  · exact le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
  · exact le_iSup_of_le 3 (le_iSup_of_le (by decide) le_rfl)

/-- The grade-two piece of the core decomposition: the neutral `W` alone.  This is the
  content of the weight-zero piece that the gauge weight cannot see. -/
lemma derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_two (n : ℕ) :
    (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm n).piece 2
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        ℂ ∙ h.wField l μ ν 2 := by
  have htwo : ∀ c : Fin 4, cartanSU2PermGrade c = 2 → c = 2 := by decide
  refine iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν => ?_
  refine le_antisymm (iSup_le fun c => iSup_le fun hc => ?_)
    (le_iSup_of_le 2 (le_iSup_of_le (by decide) le_rfl))
  rcases htwo c hc with rfl
  exact le_rfl

/-- The grade-one piece of the core decomposition is trivial: the field strength is
  linear in a real adjoint direction, so it never reaches the odd grades. -/
lemma derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_one (n : ℕ) :
    (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm n).piece 1 = ⊥ := by
  have hne : ∀ c : Fin 4, cartanSU2PermGrade c ≠ 1 := by decide
  exact le_antisymm (iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c =>
    iSup_le fun hc => absurd hc (hne c)) bot_le

/-- The grade-three piece of the core decomposition is trivial, for the same reason as
  the grade-one piece. -/
lemma derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_three (n : ℕ) :
    (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm n).piece 3 = ⊥ := by
  have hne : ∀ c : Fin 4, cartanSU2PermGrade c ≠ 3 := by decide
  exact le_antisymm (iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c =>
    iSup_le fun hc => absurd hc (hne c)) bot_le

/-!

## E. The gauge-factor parts at mass weight eight

At mass weight eight the weight-zero content acquires, beyond the twice-derived field
strength, the products pairing a raising vector against the matching lowering vector and
the products of two weight-zero vectors.  The colour products are fixed outright, the
products of two weight-zero vectors are graded by adding the grades of their factors, and
the isospin products need care: the Weyl element exchanges the two isospin root vectors
rather than scaling them, so it is the symmetric and antisymmetric combinations of the
isospin products that are graded, in grades zero and two respectively.

-/

/-- A submodule fixed pointwise by the Weyl element is concentrated in grade zero. -/
noncomputable def su2PermOfFixed (V : Submodule ℂ B)
    (hV : V ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1) :
    SU2PermDecomposition repGauge V where
  piece k := if k = 0 then V else ⊥
  piece_le := by
    intro k x hx
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl] at hx
      rw [su2PermSign_zero]
      exact Module.End.mem_eigenspace_iff.mp (hV hx)
    · rw [if_neg hk, Submodule.mem_bot] at hx
      subst hx
      simp
  iSup_piece := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (le_of_eq (if_pos rfl).symm))
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact bot_le

/-- The pieces of a fixed submodule: the submodule itself in grade zero, nothing
  elsewhere. -/
@[simp]
lemma su2PermOfFixed_piece (V : Submodule ℂ B)
    (hV : V ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1) (k : ZMod 4) :
    (su2PermOfFixed V hV).piece k = if k = 0 then V else ⊥ := rfl

/-- The colour raising vectors are fixed by the Weyl element. -/
lemma rootRaisingSpan_le_eigenspace {r : Fin 4} (hr : r ≠ 3) :
    h.rootRaisingSpan r ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1 := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Module.End.mem_eigenspace_iff.mpr
    (by rw [h.repGauge_gaugeSU2Perm_adjVec_inl l μ ν hr, one_smul])

/-- The colour lowering vectors are fixed by the Weyl element. -/
lemma rootLoweringSpan_le_eigenspace {r : Fin 4} (hr : r ≠ 3) :
    h.rootLoweringSpan r ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1 := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Module.End.mem_eigenspace_iff.mpr
    (by rw [h.repGauge_gaugeSU2Perm_adjVec_inr_inl l μ ν hr, one_smul])

/-- The colour contribution to the weight-zero piece at mass weight eight is fixed by the
  Weyl element: both factors of each product are colour vectors. -/
lemma gluonRootPart_le_eigenspace :
    h.gluonRootPart ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1 := by
  have key : ∀ r : Fin 4, r ≠ 3 → h.rootRaisingSpan r * h.rootLoweringSpan r
      ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1 := by
    intro r hr
    refine Submodule.mul_le.mpr fun x hx y hy => Module.End.mem_eigenspace_iff.mpr ?_
    rw [hrepGauge_mul,
      Module.End.mem_eigenspace_iff.mp (h.rootRaisingSpan_le_eigenspace hr hx),
      Module.End.mem_eigenspace_iff.mp (h.rootLoweringSpan_le_eigenspace hr hy),
      one_smul, one_smul, one_smul]
  exact sup_le (key 0 (by decide)) (sup_le (key 1 (by decide)) (key 2 (by decide)))

/-- The colour contribution to the weight-zero piece at mass weight eight, concentrated
  in grade zero. -/
noncomputable def gluonRootPartSU2Perm :
    SU2PermDecomposition repGauge h.gluonRootPart :=
  su2PermOfFixed h.gluonRootPart h.gluonRootPart_le_eigenspace

/-- The colour contribution sits in grade zero. -/
@[simp]
lemma gluonRootPartSU2Perm_piece_zero :
    h.gluonRootPartSU2Perm.piece 0 = h.gluonRootPart := rfl

/-- The colour contribution has no grade-two part. -/
@[simp]
lemma gluonRootPartSU2Perm_piece_two : h.gluonRootPartSU2Perm.piece 2 = ⊥ := rfl

/-- The symmetric isospin products: the grade-zero part of the isospin contribution to
  the weight-zero piece at mass weight eight. -/
noncomputable def isospinSymmPart : Submodule ℂ B :=
  ⨆ (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
    (l' : Fin 0 → Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3) (ν' : Fin 1 ⊕ Fin 3),
    ℂ ∙ (h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
      + h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3)))

/-- The antisymmetric isospin products: the grade-two part of the isospin contribution to
  the weight-zero piece at mass weight eight. -/
noncomputable def isospinAntisymmPart : Submodule ℂ B :=
  ⨆ (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
    (l' : Fin 0 → Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3) (ν' : Fin 1 ⊕ Fin 3),
    ℂ ∙ (h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
      - h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3)))

/-- A generator of the symmetric isospin part. -/
lemma mem_isospinSymmPart (l l' : Fin 0 → Fin 1 ⊕ Fin 3) (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
      + h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3))
      ∈ h.isospinSymmPart :=
  Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
    (Submodule.mem_iSup_of_mem l' (Submodule.mem_iSup_of_mem μ'
      (Submodule.mem_iSup_of_mem ν' (Submodule.mem_span_singleton_self _))))))

/-- A generator of the antisymmetric isospin part. -/
lemma mem_isospinAntisymmPart (l l' : Fin 0 → Fin 1 ⊕ Fin 3)
    (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
      - h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3))
      ∈ h.isospinAntisymmPart :=
  Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
    (Submodule.mem_iSup_of_mem l' (Submodule.mem_iSup_of_mem μ'
      (Submodule.mem_iSup_of_mem ν' (Submodule.mem_span_singleton_self _))))))

/-- A raising vector lies in the isospin raising span. -/
lemma adjVec_mem_rootRaisingSpan_three (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) : h.adjVec l μ ν (Sum.inl 3) ∈ h.rootRaisingSpan 3 :=
  Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.mem_span_singleton_self _)))

/-- A lowering vector lies in the isospin lowering span. -/
lemma adjVec_mem_rootLoweringSpan_three (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inr (Sum.inl 3)) ∈ h.rootLoweringSpan 3 :=
  Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.mem_span_singleton_self _)))

/-- The isospin contribution written out on generators: the products of one raising
  vector with one lowering vector. -/
lemma isospinRootPart_eq :
    h.isospinRootPart
      = ⨆ (l' : Fin 0 → Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3) (ν' : Fin 1 ⊕ Fin 3)
          (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        ℂ ∙ (h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))) := by
  rw [isospinRootPart, rootRaisingSpan, rootLoweringSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, Submodule.span_mul_span,
    Set.singleton_mul_singleton]

/-- The symmetric isospin part sits inside the isospin contribution. -/
lemma isospinSymmPart_le : h.isospinSymmPart ≤ h.isospinRootPart := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.add_mem _
    (Submodule.mul_mem_mul (h.adjVec_mem_rootRaisingSpan_three l μ ν)
      (h.adjVec_mem_rootLoweringSpan_three l' μ' ν'))
    (Submodule.mul_mem_mul (h.adjVec_mem_rootRaisingSpan_three l' μ' ν')
      (h.adjVec_mem_rootLoweringSpan_three l μ ν))

/-- The antisymmetric isospin part sits inside the isospin contribution. -/
lemma isospinAntisymmPart_le : h.isospinAntisymmPart ≤ h.isospinRootPart := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.sub_mem _
    (Submodule.mul_mem_mul (h.adjVec_mem_rootRaisingSpan_three l μ ν)
      (h.adjVec_mem_rootLoweringSpan_three l' μ' ν'))
    (Submodule.mul_mem_mul (h.adjVec_mem_rootRaisingSpan_three l' μ' ν')
      (h.adjVec_mem_rootLoweringSpan_three l μ ν))

/-- The symmetric isospin products are fixed by the Weyl element: it exchanges the two
  products being added, and the two factors of each commute. -/
lemma isospinSymmPart_le_eigenspace :
    h.isospinSymmPart ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) 1 := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  refine Module.End.mem_eigenspace_iff.mpr ?_
  rw [one_smul, map_add, hrepGauge_mul, hrepGauge_mul,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_raising,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_lowering,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_raising,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_lowering, neg_mul_neg, neg_mul_neg,
    (h.adjVec_commute l μ ν (Sum.inr (Sum.inl 3)) l' μ' ν' (Sum.inl 3)).eq,
    (h.adjVec_commute l' μ' ν' (Sum.inr (Sum.inl 3)) l μ ν (Sum.inl 3)).eq]
  exact add_comm _ _

/-- The antisymmetric isospin products are negated by the Weyl element: it exchanges the
  two products being subtracted. -/
lemma isospinAntisymmPart_le_eigenspace :
    h.isospinAntisymmPart ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) (-1) := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  refine Module.End.mem_eigenspace_iff.mpr ?_
  rw [neg_one_smul, map_sub, hrepGauge_mul, hrepGauge_mul,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_raising,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_lowering,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_raising,
    h.repGauge_gaugeSU2Perm_adjVec_isospin_lowering, neg_mul_neg, neg_mul_neg,
    (h.adjVec_commute l μ ν (Sum.inr (Sum.inl 3)) l' μ' ν' (Sum.inl 3)).eq,
    (h.adjVec_commute l' μ' ν' (Sum.inr (Sum.inl 3)) l μ ν (Sum.inl 3)).eq, neg_sub]

/-- The isospin contribution to the weight-zero piece at mass weight eight, split into
  its symmetric part in grade zero and its antisymmetric part in grade two.  The Weyl
  element exchanges the two isospin root vectors, so neither of the two products it
  exchanges is an eigenvector on its own, only their sum and difference are. -/
noncomputable def isospinRootPartSU2Perm :
    SU2PermDecomposition repGauge h.isospinRootPart where
  piece k :=
    if k = 0 then h.isospinSymmPart else if k = 2 then h.isospinAntisymmPart else ⊥
  piece_le := by
    intro k x hx
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [if_pos rfl] at hx
      rw [su2PermSign_zero]
      exact Module.End.mem_eigenspace_iff.mp (h.isospinSymmPart_le_eigenspace hx)
    · rcases eq_or_ne k 2 with rfl | hk2
      · rw [if_neg hk0, if_pos rfl] at hx
        rw [su2PermSign_two]
        exact Module.End.mem_eigenspace_iff.mp (h.isospinAntisymmPart_le_eigenspace hx)
      · rw [if_neg hk0, if_neg hk2, Submodule.mem_bot] at hx
        subst hx
        simp
  iSup_piece := by
    have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · rcases hcases k with rfl | rfl | rfl | rfl
      · rw [if_pos rfl]
        exact h.isospinSymmPart_le
      · rw [if_neg (by decide), if_neg (by decide)]
        exact bot_le
      · rw [if_neg (by decide), if_pos rfl]
        exact h.isospinAntisymmPart_le
      · rw [if_neg (by decide), if_neg (by decide)]
        exact bot_le
    · refine le_trans ?_ (sup_le (le_iSup _ (0 : ZMod 4)) (le_iSup _ (2 : ZMod 4)))
      rw [if_pos rfl, if_neg (by decide : ¬(2 : ZMod 4) = 0), if_pos rfl,
        h.isospinRootPart_eq]
      refine iSup_le fun l' => iSup_le fun μ' => iSup_le fun ν' => iSup_le fun l =>
        iSup_le fun μ => iSup_le fun ν => ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hs := Submodule.mem_sup_left (S := h.isospinSymmPart)
        (T := h.isospinAntisymmPart) (h.mem_isospinSymmPart l l' μ ν μ' ν')
      have ha := Submodule.mem_sup_right (S := h.isospinSymmPart)
        (T := h.isospinAntisymmPart) (h.mem_isospinAntisymmPart l l' μ ν μ' ν')
      have hsum := Submodule.smul_mem _ (2⁻¹ : ℂ) (Submodule.add_mem _ hs ha)
      rwa [show (2⁻¹ : ℂ) •
        ((h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
            + h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3)))
          + (h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
            - h.adjVec l' μ' ν' (Sum.inl 3) * h.adjVec l μ ν (Sum.inr (Sum.inl 3))))
        = h.adjVec l μ ν (Sum.inl 3) * h.adjVec l' μ' ν' (Sum.inr (Sum.inl 3))
        from by module] at hsum

/-- The graded pieces of the isospin contribution. -/
lemma isospinRootPartSU2Perm_piece (k : ZMod 4) :
    (h.isospinRootPartSU2Perm).piece k
      = if k = 0 then h.isospinSymmPart
        else if k = 2 then h.isospinAntisymmPart else ⊥ := rfl

/-- The grade-zero part of the isospin contribution is the symmetric part. -/
@[simp]
lemma isospinRootPartSU2Perm_piece_zero :
    h.isospinRootPartSU2Perm.piece 0 = h.isospinSymmPart := rfl

/-- The grade-two part of the isospin contribution is the antisymmetric part. -/
@[simp]
lemma isospinRootPartSU2Perm_piece_two :
    h.isospinRootPartSU2Perm.piece 2 = h.isospinAntisymmPart := rfl

/-- The neutral contribution to the weight-zero piece at mass weight eight: the products
  of two weight-zero vectors, whose grades add. -/
noncomputable def neutralCartanPartSU2Perm :
    SU2PermDecomposition repGauge h.neutralCartanPart :=
  SU2PermDecomposition.copy
    (SU2PermDecomposition.mul hrepGauge_mul
      ((h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 0).copy h.cartanSpan
        (h.derivSubmoduleGaugeWeight_piece_zero' 0).symm)
      ((h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 0).copy h.cartanSpan
        (h.derivSubmoduleGaugeWeight_piece_zero' 0).symm))
    _ rfl

/-!

## F. Transport along the mass weights

-/

/-- Mass weight one: the weight-zero piece is trivial, so is every grade. -/
noncomputable def massWeightSubmoduleGaugeWeightOneSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightOne).piece 0) :=
  SU2PermDecomposition.copy (SU2PermDecomposition.bot (rep := repGauge)) _ rfl

/-- Mass weight two: the weight-zero piece is trivial, so is every grade. -/
noncomputable def massWeightSubmoduleGaugeWeightTwoSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightTwo).piece 0) :=
  SU2PermDecomposition.copy (SU2PermDecomposition.bot (rep := repGauge)) _ rfl

/-- Mass weight three: the weight-zero piece is trivial, so is every grade. -/
noncomputable def massWeightSubmoduleGaugeWeightThreeSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightThree).piece 0) :=
  SU2PermDecomposition.copy (SU2PermDecomposition.bot (rep := repGauge)) _ rfl

/-- Mass weight four: the weight-zero piece is the underived field strength on the four
  fixed directions of the adjoint, graded by `cartanSU2PermGrade`. -/
noncomputable def massWeightSubmoduleGaugeWeightFourSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightFour).piece 0) :=
  SU2PermDecomposition.copy (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 0) _ rfl

/-- Mass weight five: the weight-zero piece is trivial, so is every grade. -/
noncomputable def massWeightSubmoduleGaugeWeightFiveSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightFive).piece 0) :=
  SU2PermDecomposition.copy (SU2PermDecomposition.bot (rep := repGauge)) _ rfl

/-- Mass weight six: the weight-zero piece is the once-derived field strength on the
  four fixed directions of the adjoint, graded by `cartanSU2PermGrade`. -/
noncomputable def massWeightSubmoduleGaugeWeightSixSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightSix).piece 0) :=
  SU2PermDecomposition.copy (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 1) _ rfl

/-- Mass weight seven: the weight-zero piece is trivial, so is every grade. -/
noncomputable def massWeightSubmoduleGaugeWeightSevenSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightSeven).piece 0) :=
  SU2PermDecomposition.copy (SU2PermDecomposition.bot (rep := repGauge)) _ rfl

/-- Mass weight eight: the twice-derived field strength on the four fixed directions of
  the adjoint, joined with the colour, isospin and neutral products.  The colour products
  are fixed outright, while the isospin and neutral products contribute to grade two as
  well as to grade zero. -/
noncomputable def massWeightSubmoduleGaugeWeightEightSU2Perm :
    SU2PermDecomposition repGauge ((h.massWeightSubmoduleGaugeWeightEight).piece 0) :=
  SU2PermDecomposition.copy
    (SU2PermDecomposition.sup
      ((h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 2).copy _
        (h.derivSubmoduleGaugeWeight_piece_zero 2).symm)
      (SU2PermDecomposition.sup h.gluonRootPartSU2Perm
        (SU2PermDecomposition.sup h.isospinRootPartSU2Perm h.neutralCartanPartSU2Perm)))
    _ h.massWeightSubmoduleGaugeWeightEight_piece_zero

/-- Every grade at mass weight one is trivial. -/
lemma massWeightSubmoduleGaugeWeightOneSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightOneSU2Perm).piece k = ⊥ := rfl

/-- Every grade at mass weight two is trivial. -/
lemma massWeightSubmoduleGaugeWeightTwoSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightTwoSU2Perm).piece k = ⊥ := rfl

/-- Every grade at mass weight three is trivial. -/
lemma massWeightSubmoduleGaugeWeightThreeSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightThreeSU2Perm).piece k = ⊥ := rfl

/-- Every grade at mass weight five is trivial. -/
lemma massWeightSubmoduleGaugeWeightFiveSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightFiveSU2Perm).piece k = ⊥ := rfl

/-- Every grade at mass weight seven is trivial. -/
lemma massWeightSubmoduleGaugeWeightSevenSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightSevenSU2Perm).piece k = ⊥ := rfl

/-- The grade-zero piece at mass weight four: the two colour Cartan directions of the
  underived field strength together with hypercharge. -/
lemma massWeightSubmoduleGaugeWeightFourSU2Perm_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFourSU2Perm).piece 0
      = ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        (ℂ ∙ h.gluonField ![] μ ν 2 ⊔ ℂ ∙ h.gluonField ![] μ ν 7
          ⊔ ℂ ∙ h.hyperchargeField ![] μ ν) := by
  show (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 0).piece 0 = _
  rw [h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_zero 0]
  exact le_antisymm (iSup_le fun l => by rw [Subsingleton.elim l ![]])
    (le_iSup (fun l : Fin 0 → Fin 1 ⊕ Fin 3 =>
      ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        (ℂ ∙ h.gluonField l μ ν 2 ⊔ ℂ ∙ h.gluonField l μ ν 7
          ⊔ ℂ ∙ h.hyperchargeField l μ ν)) ![])

/-- The grade-two piece at mass weight four: the neutral `W` of the underived field
  strength alone. -/
lemma massWeightSubmoduleGaugeWeightFourSU2Perm_piece_two :
    (h.massWeightSubmoduleGaugeWeightFourSU2Perm).piece 2
      = ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3), ℂ ∙ h.wField ![] μ ν 2 := by
  show (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 0).piece 2 = _
  rw [h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_two 0]
  exact le_antisymm (iSup_le fun l => by rw [Subsingleton.elim l ![]])
    (le_iSup (fun l : Fin 0 → Fin 1 ⊕ Fin 3 =>
      ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3), ℂ ∙ h.wField l μ ν 2) ![])

/-- The grade-zero piece at mass weight six: the two colour Cartan directions of the
  once-derived field strength together with hypercharge. -/
lemma massWeightSubmoduleGaugeWeightSixSU2Perm_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSixSU2Perm).piece 0
      = ⨆ (l : Fin 1 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        (ℂ ∙ h.gluonField l μ ν 2 ⊔ ℂ ∙ h.gluonField l μ ν 7
          ⊔ ℂ ∙ h.hyperchargeField l μ ν) :=
  h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_zero 1

/-- The grade-two piece at mass weight six: the neutral `W` of the once-derived field
  strength alone. -/
lemma massWeightSubmoduleGaugeWeightSixSU2Perm_piece_two :
    (h.massWeightSubmoduleGaugeWeightSixSU2Perm).piece 2
      = ⨆ (l : Fin 1 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        ℂ ∙ h.wField l μ ν 2 :=
  h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_two 1

/-- The graded pieces at mass weight eight, split into the four contributions: the
  twice-derived field strength, the colour products, the isospin products and the
  neutral products. -/
lemma massWeightSubmoduleGaugeWeightEightSU2Perm_piece (k : ZMod 4) :
    (h.massWeightSubmoduleGaugeWeightEightSU2Perm).piece k
      = (h.derivSubmoduleGaugeWeightPieceZeroSU2Perm 2).piece k
        ⊔ (h.gluonRootPartSU2Perm.piece k
          ⊔ (h.isospinRootPartSU2Perm.piece k
            ⊔ h.neutralCartanPartSU2Perm.piece k)) := rfl

/-- The grade-zero piece at mass weight eight: the colour Cartan directions and
  hypercharge of the twice-derived field strength, the colour products, the symmetric
  isospin products, and the even part of the neutral products. -/
lemma massWeightSubmoduleGaugeWeightEightSU2Perm_piece_zero :
    (h.massWeightSubmoduleGaugeWeightEightSU2Perm).piece 0
      = (⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
          (ℂ ∙ h.gluonField l μ ν 2 ⊔ ℂ ∙ h.gluonField l μ ν 7
            ⊔ ℂ ∙ h.hyperchargeField l μ ν))
        ⊔ (h.gluonRootPart
          ⊔ (h.isospinSymmPart ⊔ h.neutralCartanPartSU2Perm.piece 0)) := by
  rw [h.massWeightSubmoduleGaugeWeightEightSU2Perm_piece 0,
    h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_zero 2,
    h.gluonRootPartSU2Perm_piece_zero, h.isospinRootPartSU2Perm_piece_zero]

/-- The grade-two piece at mass weight eight: the neutral `W` of the twice-derived field
  strength, the antisymmetric isospin products, and the odd part of the neutral
  products.  The colour products contribute nothing. -/
lemma massWeightSubmoduleGaugeWeightEightSU2Perm_piece_two :
    (h.massWeightSubmoduleGaugeWeightEightSU2Perm).piece 2
      = (⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
          ℂ ∙ h.wField l μ ν 2)
        ⊔ (h.isospinAntisymmPart ⊔ h.neutralCartanPartSU2Perm.piece 2) := by
  rw [h.massWeightSubmoduleGaugeWeightEightSU2Perm_piece 2,
    h.derivSubmoduleGaugeWeightPieceZeroSU2Perm_piece_two 2,
    h.gluonRootPartSU2Perm_piece_two, h.isospinRootPartSU2Perm_piece_two, bot_sup_eq]

end IsGaugeSector

end StandardModel
