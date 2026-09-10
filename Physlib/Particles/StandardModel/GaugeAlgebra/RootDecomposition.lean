/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The root decomposition of the gauge algebra

The gauge torus acts on the gauge algebra by conjugation with a diagonal matrix, so it
scales the matrix entry `(j, k)` of the `su(3)` and `su(2)` blocks by `d j * star (d k)`.
Off the diagonal this makes the real and imaginary parts of an entry a rotating pair —
the root directions, recorded by `rootIdx`, `rootEntry` and `rootWeight` — while the
diagonal directions and the `u(1)` generator are fixed, and are recorded by `cartanIdx`,
which is assembled from the Cartan indices `su3CartanId` and `su2CartanId` of the
individual factors.

This is the adjoint analogue of the weights carried by the matter representations, and
is what the gauge sector's gauge weight decomposition is built from.

Section E makes that last sentence a theorem. A gauge weight is a character of the torus,
so the real Lie algebra carries no gauge weight decomposition of its own; but for any
complex algebra receiving the dual adjoint action, `adjointDecomposition` decomposes the
span of the resulting symbols, and its pieces are a single root line at each of the eight
nonzero weights and the span of the four Cartan symbols at weight zero. That is the sense
in which the root decomposition and the gauge weight decomposition of the adjoint are the
same thing.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-- Conjugation inverts a power of `expI`. -/
lemma star_expI_zpow (z : ℤ) : star ((expI : ℂ) ^ z) = (expI : ℂ) ^ (-z) := by
  rw [Complex.star_def, starRingEnd_expI_zpow]

/-!

## A. The coordinates of the standard basis

-/

namespace GaugeAlgebra

/-- coords -/
noncomputable def stdCoeff (x : GaugeAlgebra) : Fin 8 ⊕ Fin 3 ⊕ Fin 1 → ℝ
  | Sum.inl k => gellMannCoeff x.toSU3Matrix k
  | Sum.inr (Sum.inl i) => pauliCoeff x.toSU2Matrix i
  | Sum.inr (Sum.inr _) => (x.toU1Value).re

lemma eq_sum_stdCoeff (x : GaugeAlgebra) : x = ∑ y, stdCoeff x y • stdBasis y := by
  refine ext_of_matrix ?_ ?_ ?_
  · rw [toSU3Matrix_sum]
    simp only [Fintype.sum_sum_type, smul_toSU3Matrix, stdBasis_inl_toSU3Matrix,
      stdBasis_inr_inl_toSU3Matrix, stdBasis_inr_inr_toSU3Matrix, smul_zero,
      Finset.sum_const_zero, add_zero]
    exact eq_sum_gellMannCoeff_smul x.1.2.1 x.1.2.2
  · rw [toSU2Matrix_sum]
    simp only [Fintype.sum_sum_type, smul_toSU2Matrix, stdBasis_inl_toSU2Matrix,
      stdBasis_inr_inl_toSU2Matrix, stdBasis_inr_inr_toSU2Matrix, smul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
    exact eq_sum_pauliCoeff_smul x.2.1.2.1 x.2.1.2.2
  · have h1 : ((x.toU1Value.re : ℝ) : ℂ) = x.toU1Value :=
      Complex.conj_eq_iff_re.mp x.2.2.2
    rw [toU1Value_sum]
    simp only [Fintype.sum_sum_type, smul_toU1Value, stdBasis_inl_toU1Value,
      stdBasis_inr_inl_toU1Value, stdBasis_inr_inr_toU1Value, stdCoeff,
      Complex.real_smul, mul_zero, Finset.sum_const_zero, zero_add, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, h1]

/-- The coordinate functionals of `stdBasis` read off a gauge-algebra element's matrix
  entries. -/
lemma stdBasis_coord_apply (y : GaugeAlgebra) (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    stdBasis.coord a y = stdCoeff y a := by
  conv_lhs => rw [eq_sum_stdCoeff y]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a fun b => stdCoeff y b]
  simp

end GaugeAlgebra

/-!

## B. The torus acts by conjugation with a diagonal matrix

-/

/-- su3 diagonals of inverse torus gens -/
noncomputable def torusSU3Diag : Fin 4 → Fin 3 → ℂ :=
  ![![star (expI : ℂ), (expI : ℂ), 1], ![1, star (expI : ℂ), (expI : ℂ)], 1, 1]

/-- su2 -/
noncomputable def torusSU2Diag : Fin 4 → Fin 2 → ℂ :=
  ![1, 1, ![star (expI : ℂ), (expI : ℂ)], 1]

lemma toSU3_inv_gaugeTorusGen (i : Fin 4) :
    ((GaugeGroupI.toSU3 (gaugeTorusGen i)⁻¹ : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal (torusSU3Diag i) := by
  rw [map_inv, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  fin_cases i <;>
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeTorusGen, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, torusSU3Diag,
        Matrix.diagonal]

lemma toSU2_inv_gaugeTorusGen (i : Fin 4) :
    ((GaugeGroupI.toSU2 (gaugeTorusGen i)⁻¹ : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (torusSU2Diag i) := by
  rw [map_inv, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  fin_cases i <;>
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [gaugeTorusGen, GaugeGroupI.toSU2, su2ExpI, torusSU2Diag,
        Matrix.diagonal]

namespace GaugeAlgebra

lemma adjointMap_toSU3Matrix_apply_diagonal {g : GaugeGroupI} {d : Fin 3 → ℂ}
    (hg : ((GaugeGroupI.toSU3 g : specialUnitaryGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal d)
    (x : GaugeAlgebra) (j k : Fin 3) :
    (adjointMap g x).toSU3Matrix j k = d j * star (d k) * x.toSU3Matrix j k := by
  rw [adjointMap_toSU3Matrix, hg, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  ring

lemma adjointMap_toSU2Matrix_apply_diagonal {g : GaugeGroupI} {d : Fin 2 → ℂ}
    (hg : ((GaugeGroupI.toSU2 g : specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal d)
    (x : GaugeAlgebra) (j k : Fin 2) :
    (adjointMap g x).toSU2Matrix j k = d j * star (d k) * x.toSU2Matrix j k := by
  rw [adjointMap_toSU2Matrix, hg, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  ring

end GaugeAlgebra

lemma torusSU3Diag_mul_star (i : Fin 4) (j : Fin 3) :
    torusSU3Diag i j * star (torusSU3Diag i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [torusSU3Diag, expI_mul_conj, conj_mul_expI]

lemma torusSU2Diag_mul_star (i : Fin 4) (j : Fin 2) :
    torusSU2Diag i j * star (torusSU2Diag i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [torusSU2Diag, expI_mul_conj, conj_mul_expI]

namespace GaugeAlgebra

/-!

## C. An entrywise scaling rotates the real pair of coordinate functionals

-/

lemma dualMap_pair_of_entry {g : GaugeGroupI} {e : GaugeAlgebra → ℂ}
    {φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra} {z : ℂ}
    (h1 : ∀ x, φ₁ x = (e x).re) (h2 : ∀ x, φ₂ x = -(e x).im)
    (he : ∀ x, e (adjointMap g x) = star z * e x) :
    (adjointMap g).dualMap φ₁ = z.re • φ₁ - z.im • φ₂ ∧
      (adjointMap g).dualMap φ₂ = z.im • φ₁ + z.re • φ₂ := by
  constructor <;> refine LinearMap.ext fun x => ?_ <;>
    simp only [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, h1, h2, he, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring

end GaugeAlgebra

/-!

## D. The root and Cartan directions of the adjoint

The `su(3)` and `su(2)` blocks each contribute root directions — pairs of standard
basis indices whose coordinate functionals are the real part and minus the imaginary
part of one matrix entry — together with Cartan directions on which the torus acts
trivially; the `u(1)` generator is also fixed.

The Cartan directions are named one factor at a time first, by `su3CartanId` in the
Gell-Mann indices and `su2CartanId` in the Pauli indices, and `cartanIdx` assembles those
with the `u(1)` generator into the four weight-zero directions of the whole algebra. The
factorwise names are the ones the bi-adjoint files use, each of which sees a single
factor; they are reducible, so they behave exactly like the index literals they name.

-/

namespace GaugeAlgebra

/-- The four root directions of the adjoint. -/
def rootIdx : Fin 4 → (Fin 8 ⊕ Fin 3 ⊕ Fin 1) × (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
  | 0 => (Sum.inl 0, Sum.inl 1)
  | 1 => (Sum.inl 3, Sum.inl 4)
  | 2 => (Sum.inl 5, Sum.inl 6)
  | 3 => (Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1))

/-- The gauge weight of each root direction. -/
def rootWeight : Fin 4 → GaugeWeight
  | 0 => (2, -1, 0, 0)
  | 1 => (1, 1, 0, 0)
  | 2 => (-1, 2, 0, 0)
  | 3 => (0, 0, 2, 0)

/-- The matrix entry scaled by the torus along each root direction. -/
def rootEntry : Fin 4 → GaugeAlgebra → ℂ
  | 0, x => x.toSU3Matrix 0 1
  | 1, x => x.toSU3Matrix 0 2
  | 2, x => x.toSU3Matrix 1 2
  | 3, x => x.toSU2Matrix 0 1

/-- The Gell-Mann indices of the two Cartan directions of `su(3)`. -/
abbrev su3CartanId : Fin 2 → Fin 8
  | 0 => 2
  | 1 => 7

/-- The Pauli index of the Cartan direction of `su(2)`. -/
abbrev su2CartanId : Fin 3 := 2

/-- The four weight-zero directions: the two `su(3)` Cartan generators, the `su(2)`
  Cartan generator and the `u(1)` generator. -/
def cartanIdx : Fin 4 → (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
  | 0 => Sum.inl (su3CartanId 0)
  | 1 => Sum.inl (su3CartanId 1)
  | 2 => Sum.inr (Sum.inl su2CartanId)
  | 3 => Sum.inr (Sum.inr 0)

lemma coord_rootIdx_fst (r : Fin 4) (x : GaugeAlgebra) :
    stdBasis.coord (rootIdx r).1 x = (rootEntry r x).re := by
  fin_cases r <;> (rw [stdBasis_coord_apply]; rfl)

lemma coord_rootIdx_snd (r : Fin 4) (x : GaugeAlgebra) :
    stdBasis.coord (rootIdx r).2 x = -(rootEntry r x).im := by
  fin_cases r <;> (rw [stdBasis_coord_apply]; rfl)

lemma rootEntry_adjointMap (r : Fin 4) (i : Fin 4) (x : GaugeAlgebra) :
    rootEntry r (adjointMap (gaugeTorusGen i)⁻¹ x)
      = star ((expI : ℂ) ^ GaugeWeight.coord (rootWeight r) i) * rootEntry r x := by
  fin_cases r
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 0 1 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 0 1]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord,
        expI_inv_eq_star, _root_.zpow_neg, pow_two]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 0 2 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 0 2]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix 1 2 = _
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x 1 2]
    congr 1
    fin_cases i <;>
      simp [torusSU3Diag, rootWeight, GaugeWeight.coord,
        expI_inv_eq_star, _root_.zpow_neg, pow_two]
  · show (adjointMap (gaugeTorusGen i)⁻¹ x).toSU2Matrix 0 1 = _
    rw [adjointMap_toSU2Matrix_apply_diagonal (toSU2_inv_gaugeTorusGen i) x 0 1]
    congr 1
    fin_cases i <;>
      simp [torusSU2Diag, rootWeight, GaugeWeight.coord, pow_two]

lemma dualMap_coord_cartanIdx (c : Fin 4) (i : Fin 4) :
    (adjointMap (gaugeTorusGen i)⁻¹).dualMap (stdBasis.coord (cartanIdx c))
      = stdBasis.coord (cartanIdx c) := by
  refine LinearMap.ext fun x => ?_
  have h3 : ∀ j : Fin 3, (adjointMap (gaugeTorusGen i)⁻¹ x).toSU3Matrix j j
      = x.toSU3Matrix j j := fun j => by
    rw [adjointMap_toSU3Matrix_apply_diagonal (toSU3_inv_gaugeTorusGen i) x j j,
      torusSU3Diag_mul_star, one_mul]
  have h2 : ∀ j : Fin 2, (adjointMap (gaugeTorusGen i)⁻¹ x).toSU2Matrix j j
      = x.toSU2Matrix j j := fun j => by
    rw [adjointMap_toSU2Matrix_apply_diagonal (toSU2_inv_gaugeTorusGen i) x j j,
      torusSU2Diag_mul_star, one_mul]
  have h1 : (adjointMap (gaugeTorusGen i)⁻¹ x).toU1Value = x.toU1Value :=
    adjointMap_toU1Value _ _
  fin_cases c <;>
    simp only [LinearMap.dualMap_apply, cartanIdx, su3CartanId, su2CartanId,
      stdBasis_coord_apply, stdCoeff, gellMannCoeff, pauliCoeff, h3, h2, h1]

end GaugeAlgebra

/-!

## E. The root decomposition as a gauge weight decomposition

A gauge weight is a character of the torus, so the vectors carrying one are complex,
whereas the gauge algebra is a real Lie algebra and `GaugeWeightDecomposition` asks for a
complex algebra. The relation is therefore not a statement about `GaugeAlgebra`, which
carries no gauge weight decomposition at all, but about any complex algebra receiving the
dual adjoint action: a real-linear map `F` out of `Module.Dual ℝ GaugeAlgebra`
intertwining the gauge action with the coadjoint one, which is how the field strength of
the gauge sector meets the adjoint.

For such an `F` the root data of section D is exactly a gauge weight decomposition of the
span of the symbols. Each root contributes the two combinations `F φ₁ ± i F φ₂` of its
paired coordinate symbols, of weights `± rootWeight r`, and each Cartan direction
contributes its symbol, of weight zero; `exists_rootIdx_or_cartanIdx` says these twelve
vectors are enough, and `adjointDecomposition` joins their lines one weight at a time.

The pieces are the identification itself. `adjointDecomposition_piece_rootWeight` and
`adjointDecomposition_piece_neg_rootWeight` give a single root line at each of the eight
nonzero weights, and `adjointDecomposition_piece_zero` gives the span of the four Cartan
symbols at weight zero: the root directions are the nonzero-weight pieces and the Cartan
directions are the zero-weight piece.

-/

namespace GaugeAlgebra

variable {B : Type*} [Ring B] [Algebra ℂ B] {rep : Representation ℂ GaugeGroupI B}
  {F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}

/-- A real scalar acts on a complex algebra through its complex image. -/
lemma real_smul_eq_complex_smul (r : ℝ) (b : B) : r • b = ((r : ℂ)) • b := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

/-- A coadjoint symbol map: a real-linear map from the dual of the gauge algebra into a
  complex algebra which intertwines the gauge action with the dual adjoint action. The
  field strength of the gauge sector is one such map. -/
def IsCoadjointSymbol (rep : Representation ℂ GaugeGroupI B)
    (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) : Prop :=
  ∀ (g : GaugeGroupI) (φ : Module.Dual ℝ GaugeAlgebra),
    rep g (F φ) = F ((adjointMap g⁻¹).dualMap φ)

/-- The index type of the adjoint weight vectors: four positive roots, four negative
  roots and four Cartan directions. -/
abbrev AdjIdx : Type := Fin 4 ⊕ Fin 4 ⊕ Fin 4

/-- The gauge weight carried by each adjoint weight vector. -/
def adjWeight : AdjIdx → GaugeWeight
  | Sum.inl r => rootWeight r
  | Sum.inr (Sum.inl r) => -(rootWeight r)
  | Sum.inr (Sum.inr _) => 0

/-- The weight vectors of the adjoint in the image of a coadjoint symbol map: for each
  root the two combinations of its paired coordinate symbols, and for each Cartan
  direction the symbol itself. -/
noncomputable def adjVec (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) : AdjIdx → B
  | Sum.inl r => F (stdBasis.coord (rootIdx r).1)
      + Complex.I • F (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inl r) => F (stdBasis.coord (rootIdx r).1)
      - Complex.I • F (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inr c) => F (stdBasis.coord (cartanIdx c))

/-- A weight vector carries zero gauge weight exactly when it is a Cartan direction; the
  eight root directions all carry a nonzero weight. -/
lemma adjWeight_eq_zero_iff (k : AdjIdx) :
    adjWeight k = 0 ↔ ∃ c : Fin 4, k = Sum.inr (Sum.inr c) := by
  revert k
  decide

/-- The root and Cartan directions exhaust the standard basis: every standard index is
  one of the two members of a root pair, or a Cartan index. -/
lemma exists_rootIdx_or_cartanIdx (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    (∃ r : Fin 4, a = (rootIdx r).1) ∨ (∃ r : Fin 4, a = (rootIdx r).2)
      ∨ ∃ c : Fin 4, a = cartanIdx c := by
  revert a
  decide

/-- The positive combination of a rotating pair of symbols is scaled by the rotation. -/
lemma rep_pair_add (hF : IsCoadjointSymbol rep F) (g : GaugeGroupI)
    (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    rep g (F φ₁ + Complex.I • F φ₂) = z • (F φ₁ + Complex.I • F φ₂) := by
  rw [map_add, map_smul, hF, hF, h1, h2, map_sub, map_add, map_smul, map_smul,
    map_smul, map_smul, real_smul_eq_complex_smul z.re, real_smul_eq_complex_smul z.im,
    real_smul_eq_complex_smul z.im, real_smul_eq_complex_smul z.re]
  conv_rhs => rw [← Complex.re_add_im z]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

/-- The negative combination of a rotating pair of symbols is scaled by the conjugate
  rotation. -/
lemma rep_pair_sub (hF : IsCoadjointSymbol rep F) (g : GaugeGroupI)
    (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    rep g (F φ₁ - Complex.I • F φ₂)
      = (starRingEnd ℂ z) • (F φ₁ - Complex.I • F φ₂) := by
  rw [map_sub, map_smul, hF, hF, h1, h2, map_sub, map_add, map_smul, map_smul,
    map_smul, map_smul, real_smul_eq_complex_smul z.re, real_smul_eq_complex_smul z.im,
    real_smul_eq_complex_smul z.im, real_smul_eq_complex_smul z.re]
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

/-- A symbol at a fixed coordinate functional is itself fixed. -/
lemma rep_fixed (hF : IsCoadjointSymbol rep F) (g : GaugeGroupI)
    (φ : Module.Dual ℝ GaugeAlgebra) (h1 : (adjointMap g⁻¹).dualMap φ = φ) :
    rep g (F φ) = F φ := by
  rw [hF, h1]

/-- Each adjoint weight vector is a simultaneous eigenvector of the four torus
  generators, at the character of its weight. -/
lemma rep_adjVec (hF : IsCoadjointSymbol rep F) (k : AdjIdx) (i : Fin 4) :
    rep (gaugeTorusGen i) (adjVec F k)
      = ((expI : ℂ) ^ GaugeWeight.coord (adjWeight k) i) • adjVec F k := by
  match k with
  | Sum.inl r =>
    show rep (gaugeTorusGen i) (F (stdBasis.coord (rootIdx r).1)
        + Complex.I • F (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    exact rep_pair_add hF _ _ _ _ p1 p2
  | Sum.inr (Sum.inl r) =>
    show rep (gaugeTorusGen i) (F (stdBasis.coord (rootIdx r).1)
        - Complex.I • F (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    rw [rep_pair_sub hF _ _ _ _ p1 p2]
    congr 1
    rw [show GaugeWeight.coord (adjWeight (Sum.inr (Sum.inl r) : AdjIdx)) i
        = -(GaugeWeight.coord (rootWeight r) i) from by
      simp [adjWeight, GaugeWeight.coord_neg]]
    rw [← Complex.star_def, star_expI_zpow]
  | Sum.inr (Sum.inr c) =>
    show rep (gaugeTorusGen i) (F (stdBasis.coord (cartanIdx c))) = _
    rw [rep_fixed hF _ _ (dualMap_coord_cartanIdx c i)]
    show _ = ((expI : ℂ) ^ GaugeWeight.coord (0 : GaugeWeight) i) • _
    simp [adjVec]

/-- The first symbol of a root pair, recovered from the two weight vectors. -/
lemma symbol_rootIdx_fst (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (r : Fin 4) :
    F (stdBasis.coord (rootIdx r).1)
      = (2 : ℂ)⁻¹ • (adjVec F (Sum.inl r) + adjVec F (Sum.inr (Sum.inl r))) := by
  show _ = (2 : ℂ)⁻¹ • ((F (stdBasis.coord (rootIdx r).1)
      + Complex.I • F (stdBasis.coord (rootIdx r).2))
    + (F (stdBasis.coord (rootIdx r).1)
      - Complex.I • F (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · field_simp; try ring

/-- The second symbol of a root pair, recovered from the two weight vectors. -/
lemma symbol_rootIdx_snd (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (r : Fin 4) :
    F (stdBasis.coord (rootIdx r).2)
      = (-(Complex.I / 2)) • (adjVec F (Sum.inl r) - adjVec F (Sum.inr (Sum.inl r))) := by
  show _ = (-(Complex.I / 2)) • ((F (stdBasis.coord (rootIdx r).1)
      + Complex.I • F (stdBasis.coord (rootIdx r).2))
    - (F (stdBasis.coord (rootIdx r).1)
      - Complex.I • F (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

/-- Every standard coordinate symbol lies in the join of the twelve weight lines. -/
lemma symbol_mem_iSup (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    F (stdBasis.coord a) ∈ ⨆ k : AdjIdx, Submodule.span ℂ {adjVec F k} := by
  have hmem : ∀ k : AdjIdx, adjVec F k ∈ ⨆ k : AdjIdx, Submodule.span ℂ {adjVec F k} :=
    fun k => Submodule.mem_iSup_of_mem k (Submodule.mem_span_singleton_self _)
  rcases exists_rootIdx_or_cartanIdx a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c, rfl⟩
  · rw [symbol_rootIdx_fst]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hmem _) (hmem _))
  · rw [symbol_rootIdx_snd]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _) (hmem _))
  · exact hmem (Sum.inr (Sum.inr c))

/-- The span of the symbols is the join of the twelve weight lines. -/
lemma span_range_eq_iSup (F : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    Submodule.span ℂ (Set.range F) = ⨆ k : AdjIdx, Submodule.span ℂ {adjVec F k} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (iSup_le fun k => ?_)
  · rintro x ⟨φ, rfl⟩
    rw [← stdBasis.sum_dual_apply_smul_coord φ, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_smul, real_smul_eq_complex_smul]
    exact Submodule.smul_mem _ _ (symbol_mem_iSup F a)
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have hFm : ∀ φ, F φ ∈ Submodule.span ℂ (Set.range F) :=
      fun φ => Submodule.subset_span ⟨φ, rfl⟩
    match k with
    | Sum.inl r => exact Submodule.add_mem _ (hFm _) (Submodule.smul_mem _ _ (hFm _))
    | Sum.inr (Sum.inl r) =>
      exact Submodule.sub_mem _ (hFm _) (Submodule.smul_mem _ _ (hFm _))
    | Sum.inr (Sum.inr c) => exact hFm _

/-- The root decomposition read as a gauge weight decomposition: the span of the symbols
  of a coadjoint map, joined out of the twelve root and Cartan lines. -/
@[implicit_reducible]
noncomputable def adjointDecomposition (hmul : IsMulRep rep)
    (hF : IsCoadjointSymbol rep F) :
    GaugeWeightDecomposition rep (Submodule.span ℂ (Set.range F)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hmul fun k =>
      GaugeWeightDecomposition.spanSingleton hmul (adjVec F k) (adjWeight k)
        (fun i => rep_adjVec hF k i))
    _ (span_range_eq_iSup F)

/-- The gauge weights of the adjoint: the six `su(3)` roots, the two `su(2)` roots and
  the zero weight of the Cartan and `u(1)` directions. Every one of them has vanishing
  hypercharge. -/
lemma adjointDecomposition_supp (hmul : IsMulRep rep) (hF : IsCoadjointSymbol rep F) :
    (adjointDecomposition hmul hF).supp
      = {((2, -1, 0, 0) : GaugeWeight), (1, 1, 0, 0), (-1, 2, 0, 0), (0, 0, 2, 0),
        (-2, 1, 0, 0), (-1, -1, 0, 0), (1, -2, 0, 0), (0, 0, -2, 0), (0, 0, 0, 0)} := by
  show Finset.univ.biUnion (fun k : AdjIdx => ({adjWeight k} : Finset GaugeWeight)) = _
  decide

/-- The pieces of the decomposition: the weight-`w` piece is the join of the weight lines
  whose weight is `w`. -/
lemma adjointDecomposition_piece (hmul : IsMulRep rep) (hF : IsCoadjointSymbol rep F)
    (w : GaugeWeight) :
    (adjointDecomposition hmul hF).piece w
      = ⨆ k : AdjIdx, if w = adjWeight k then Submodule.span ℂ {adjVec F k} else ⊥ := rfl

/-- The piece at a root weight is the line of that root alone. -/
lemma adjointDecomposition_piece_rootWeight (hmul : IsMulRep rep)
    (hF : IsCoadjointSymbol rep F) (r : Fin 4) :
    (adjointDecomposition hmul hF).piece (rootWeight r)
      = Submodule.span ℂ {adjVec F (Sum.inl r)} := by
  rw [adjointDecomposition_piece, iSup_sum, iSup_sum]
  have h1 : ∀ a b : Fin 4, (rootWeight a = adjWeight (Sum.inl b)) ↔ b = a := by decide
  have h2 : ∀ a b : Fin 4, ¬ (rootWeight a = adjWeight (Sum.inr (Sum.inl b))) := by decide
  have h3 : ∀ a c : Fin 4, ¬ (rootWeight a = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, h3, if_false, iSup_bot, sup_bot_eq]
  refine le_antisymm (iSup_le fun b => ?_) (le_iSup_of_le r (by simp))
  split_ifs with hb
  · subst hb
    exact le_rfl
  · exact bot_le

/-- The piece at the opposite of a root weight is the line of the opposite root. -/
lemma adjointDecomposition_piece_neg_rootWeight (hmul : IsMulRep rep)
    (hF : IsCoadjointSymbol rep F) (r : Fin 4) :
    (adjointDecomposition hmul hF).piece (-(rootWeight r))
      = Submodule.span ℂ {adjVec F (Sum.inr (Sum.inl r))} := by
  rw [adjointDecomposition_piece, iSup_sum, iSup_sum]
  have h1 : ∀ a b : Fin 4, ¬ (-(rootWeight a) = adjWeight (Sum.inl b)) := by decide
  have h2 : ∀ a b : Fin 4,
      (-(rootWeight a) = adjWeight (Sum.inr (Sum.inl b))) ↔ b = a := by decide
  have h3 : ∀ a c : Fin 4,
      ¬ (-(rootWeight a) = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, h3, if_false, iSup_bot, bot_sup_eq, sup_bot_eq]
  refine le_antisymm (iSup_le fun b => ?_) (le_iSup_of_le r (by simp))
  split_ifs with hb
  · subst hb
    exact le_rfl
  · exact bot_le

/-- The weight-zero piece is the span of the four Cartan symbols: the two `su(3)` Cartan
  generators, the `su(2)` Cartan generator and the `u(1)` generator. -/
lemma adjointDecomposition_piece_zero (hmul : IsMulRep rep)
    (hF : IsCoadjointSymbol rep F) :
    (adjointDecomposition hmul hF).piece 0
      = ⨆ c : Fin 4, Submodule.span ℂ {F (stdBasis.coord (cartanIdx c))} := by
  rw [adjointDecomposition_piece, iSup_sum, iSup_sum]
  have h1 : ∀ b : Fin 4, ¬ ((0 : GaugeWeight) = adjWeight (Sum.inl b)) := by decide
  have h2 : ∀ b : Fin 4,
      ¬ ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inl b))) := by decide
  have h3 : ∀ c : Fin 4, ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, if_false, iSup_bot, bot_sup_eq]
  exact iSup_congr fun c => if_pos (h3 c)

/-- Every weight outside the nine is absent from the adjoint. -/
lemma adjointDecomposition_piece_eq_bot (hmul : IsMulRep rep)
    (hF : IsCoadjointSymbol rep F) {w : GaugeWeight}
    (hw : w ∉ (adjointDecomposition hmul hF).supp) :
    (adjointDecomposition hmul hF).piece w = ⊥ :=
  (adjointDecomposition hmul hF).piece_eq_bot w hw

end GaugeAlgebra

end StandardModel
