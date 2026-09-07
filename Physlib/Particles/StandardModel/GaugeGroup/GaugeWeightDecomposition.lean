/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Mathematics.ConjModule
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
/-!
# Gauge weight decompositions

## i. Overview

The operators that may appear in a Standard Model Lagrangian are those the gauge group leaves
fixed, and finding them means searching a large space of composite operators.

The maximal torus of the gauge group is four-dimensional, and a **gauge weight** is the
quadruple of charges

  `(colour₁, colour₂, isospin, hypercharge) : ℤ × ℤ × ℤ × ℤ`,

recording how a vector scales under four chosen elements of it. Two count colour, one counts
weak isospin normalized as `2T₃`, and one counts hypercharge normalized as `6Y`. A **gauge
weight decomposition** of a submodule `V` presents it as a finitely supported family of
subspaces on each of which those four elements act by one such character.

Carrying all four charges at once costs nothing, since the four elements commute. They lie in
different factors of the product group, and the two colour elements are both diagonal, so the
four gradings are simultaneously realizable. An invariant operator is fixed by the whole gauge
group, so in particular by these four elements, so it carries zero weight and the search can
be confined to the zero-weight piece.

In the adjoint representation this grading is the root decomposition of the gauge algebra.
That identification cannot be made here, since the file recording the root data imports
this one; it is `GaugeAlgebra.adjointDecomposition` in
`Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition`.

## ii. Key results

- `gaugeTorusGen` : the four commuting torus generators.
- `GaugeWeight` : the quadruple of charges measured against them.
- `GaugeWeightDecomposition` : a finitely supported family of pure-weight subspaces with
  supremum `V`.
- `GaugeWeightDecomposition.sup` : decompositions combine one weight at a time along
  `V ⊔ V'`.
- `GaugeWeightDecomposition.mul` : weights add under multiplication, decomposing `V * V'`.
- `GaugeWeightDecomposition.piece_eq_inf` : the pieces are cut out of `V` by the torus alone.
- `GaugeWeightDecomposition.mem_zero_of_invariant` : a gauge-invariant element lies in the
  zero-weight piece.
- `GaugeWeightDecomposition.pieceBoostWeightDecomposition` : a gauge weight piece inherits a
  boost weight decomposition, when the gauge and Lorentz actions commute.

## iii. Table of contents

- A. The scalar `exp i` and the torus generators
- B. The four torus generators and gauge weights
- C. Gauge weight decompositions
- D. Joins
- E. Products
- F. Invariants
- G. Compatibility with the boost weight decomposition

-/

@[expose] public section

namespace StandardModel

open Matrix Pointwise

/-!
## A. The scalar `exp i` and the torus generators

Every charge here is measured by one scalar. The unit complex number `exp i` has infinite
order, since `π` is irrational, so its integer powers are pairwise distinct and a single
element of the torus already separates all the weights in a given direction.

The torus generators are built by placing `exp i` and its inverse on a diagonal. The maximal
torus of `SU(3)` is two-dimensional, so colour is a two-component charge and needs the two
elements `diag (exp i, exp (-i), 1)` and `diag (1, exp i, exp (-i))`. Weak isospin needs one,
`diag (exp i, exp (-i))`. Each lies in its special unitary group because the diagonal entries
have modulus one and multiply to one. Hypercharge needs no matrix, since its factor of the
gauge group is already the unit circle.

The generators are elements of the group, and the purity of a weight space is recorded by a
character equation `rep g x = c • x`.
-/

/-- The unitary scalar `exp i`, a point of the unit circle of infinite order. -/
noncomputable def expI : unitary ℂ :=
  ⟨Complex.exp Complex.I, by
    have hstar : star (Complex.exp Complex.I) = Complex.exp (-Complex.I) := by
      rw [show star (Complex.exp Complex.I)
          = (starRingEnd ℂ) (Complex.exp Complex.I) from rfl, ← Complex.exp_conj,
        Complex.conj_I]
    constructor
    · rw [hstar, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    · rw [hstar, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]⟩

/-- The powers of `exp i` are pairwise distinct, by the irrationality of `π`. -/
lemma expI_zpow_injective : Function.Injective fun n : ℤ => ((expI : ℂ) ^ n) := by
  intro a b hab
  simp only [show ((expI : ℂ)) = Complex.exp Complex.I from rfl,
    ← Complex.exp_int_mul] at hab
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have hℂ : ((a : ℂ)) = b + k * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [hk]
    ring
  have hℝ : ((a : ℝ)) = b + k * (2 * Real.pi) := by
    have h := congrArg Complex.re hℂ
    simpa using h
  rcases eq_or_ne k 0 with rfl | hk0
  · exact_mod_cast (by simpa using hℝ : ((a : ℝ)) = b)
  · exfalso
    refine irrational_pi ⟨(a - b) / (2 * k), ?_⟩
    have h2k : ((2 * k : ℝ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hk0)
    push_cast
    rw [div_eq_iff h2k]
    linarith [hℝ]

/-- `exp i` is nonzero. -/
lemma expI_ne_zero : ((expI : ℂ)) ≠ 0 := fun h0 => by
  have h := Unitary.mul_star_self_of_mem expI.2
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- The inverse of `exp i` is its star. -/
lemma expI_inv_eq_star : ((expI : ℂ))⁻¹ = star (expI : ℂ) :=
  inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem expI.2)

/-- `exp i` times its conjugate is one. -/
lemma expI_mul_conj : (expI : ℂ) * (starRingEnd ℂ) (expI : ℂ) = 1 :=
  Unitary.mul_star_self_of_mem expI.2

/-- The conjugate of `exp i` times `exp i` is one. -/
lemma conj_mul_expI : (starRingEnd ℂ) (expI : ℂ) * (expI : ℂ) = 1 :=
  Unitary.star_mul_self_of_mem expI.2

/-- A diagonal matrix whose entries are unit scalars with product one lies in the special
  unitary group. -/
lemma _root_.Matrix.mem_specialUnitaryGroup_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (hd : ∀ i, d i * star (d i) = 1) (hdet : ∏ i, d i = 1) :
    Matrix.diagonal d ∈ Matrix.specialUnitaryGroup n ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply]
    rw [funext hd, Matrix.diagonal_one]
  · rw [Matrix.det_diagonal, hdet]

/-- The first colour torus generator, `diag (exp i, exp (-i), 1)`. -/
noncomputable def su3ExpIOne : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal ![(expI : ℂ), star (expI : ℂ), 1],
    Matrix.mem_specialUnitaryGroup_diagonal _
      (fun i => by fin_cases i <;> simp [expI_mul_conj, conj_mul_expI])
      (by simp [Fin.prod_univ_three, expI_mul_conj])⟩

/-- The second colour torus generator, `diag (1, exp i, exp (-i))`. -/
noncomputable def su3ExpITwo : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal ![1, (expI : ℂ), star (expI : ℂ)],
    Matrix.mem_specialUnitaryGroup_diagonal _
      (fun i => by fin_cases i <;> simp [expI_mul_conj, conj_mul_expI])
      (by simp [Fin.prod_univ_three, expI_mul_conj])⟩

/-- The `SU(2)` torus element, `diag (exp i, exp (-i))`. -/
noncomputable def su2ExpI : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal ![(expI : ℂ), star (expI : ℂ)],
    Matrix.mem_specialUnitaryGroup_diagonal _
      (fun i => by fin_cases i <;> simp [expI_mul_conj, conj_mul_expI])
      (by simp [Fin.prod_univ_two, expI_mul_conj])⟩

/-- The underlying matrix of the `SU(2)` torus element. -/
lemma su2ExpI_coe :
    (su2ExpI : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(expI : ℂ), 0; 0, star (expI : ℂ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [su2ExpI, Matrix.diagonal]

/-- The inverse torus element is `diag (exp (-i), exp i)`, so on a doublet the two components
  are scaled by the reciprocal characters. -/
lemma su2ExpI_inv_coe :
    (su2ExpI⁻¹ : specialUnitaryGroup (Fin 2) ℂ).1
      = !![star (expI : ℂ), 0; 0, (expI : ℂ)] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, su2ExpI_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-!
## B. The four torus generators and gauge weights

Weights are measured against four chosen elements of the maximal torus, one element per
direction, collected in `gaugeTorusGen`. Four suffice because of the separation in section A.

Both abelian charges are normalized to integers. Weak isospin is measured as `2T₃`, so the two
components of a doublet carry weights `+1` and `-1`, and hypercharge as `6Y`, the smallest
rescaling under which every Standard Model hypercharge is an integer, the quark doublet at `Y = 1/6`
becoming `6Y = 1`. Integrality is what allows every eigenvalue here to be an integer power
`(exp i) ^ k` of one scalar.

`GaugeWeight.coord` reads a weight at a given generator. It is additive, which is why charges
add when operators are multiplied, and injective, so a weight can be recovered from the four
characters by which the torus acts.
-/

/-- The four commuting generators of the maximal torus of the gauge group. -/
noncomputable def gaugeTorusGen : Fin 4 → GaugeGroupI :=
  ![⟨su3ExpIOne, 1, 1⟩, ⟨su3ExpITwo, 1, 1⟩, ⟨1, su2ExpI, 1⟩, ⟨1, 1, expI⟩]

/-- A **gauge weight**, the four exponents `(colour₁, colour₂, isospin, hypercharge)`
  recording how a vector scales under `gaugeTorusGen`. -/
abbrev GaugeWeight : Type := ℤ × ℤ × ℤ × ℤ

/-- The exponent of a gauge weight against the `i`-th torus generator. -/
def GaugeWeight.coord (w : GaugeWeight) : Fin 4 → ℤ := ![w.1, w.2.1, w.2.2.1, w.2.2.2]

/-- The exponent at the first colour generator. -/
@[simp] lemma GaugeWeight.coord_zero (w : GaugeWeight) : w.coord 0 = w.1 := rfl

/-- The exponent at the second colour generator. -/
@[simp] lemma GaugeWeight.coord_one (w : GaugeWeight) : w.coord 1 = w.2.1 := rfl

/-- The exponent at the isospin generator, normalized as `2T₃`. -/
@[simp] lemma GaugeWeight.coord_two (w : GaugeWeight) : w.coord 2 = w.2.2.1 := rfl

/-- The exponent at the hypercharge generator, normalized as `6Y`. -/
@[simp] lemma GaugeWeight.coord_three (w : GaugeWeight) : w.coord 3 = w.2.2.2 := rfl

/-- The zero gauge weight has vanishing exponent against every torus generator. -/
@[simp] lemma GaugeWeight.coord_neg (w : GaugeWeight) (i : Fin 4) :
    (-w).coord i = -(w.coord i) := by
  fin_cases i <;> rfl

@[simp] lemma GaugeWeight.zero_coord (i : Fin 4) : (0 : GaugeWeight).coord i = 0 := by
  fin_cases i <;> rfl

/-- Weights add coordinatewise. With `zero_coord` this says `coord` is additive, which is
  what makes gauge weights add under multiplication. -/
lemma GaugeWeight.coord_add (w w' : GaugeWeight) (i : Fin 4) :
    (w + w').coord i = w.coord i + w'.coord i := by
  fin_cases i <;> rfl

/-- **A gauge weight is determined by its four exponents.** This is what lets a weight be
  recovered from the characters by which the torus acts; see `piece_eq_inf`. -/
lemma GaugeWeight.coord_injective : Function.Injective GaugeWeight.coord := by
  rintro ⟨a, b, c, e⟩ ⟨a', b', c', e'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [GaugeWeight.coord_zero, GaugeWeight.coord_one, GaugeWeight.coord_two,
    GaugeWeight.coord_three] at h0 h1 h2 h3
  subst h0
  subst h1
  subst h2
  subst h3
  rfl

/-!
## C. Gauge weight decompositions

A gauge weight decomposition is the weight-space decomposition of a representation, with two
differences. It is recorded rather than derived, since the submodules of interest are spans of
explicitly given operators whose charges are read off directly, and it is required only to
cover `V`. Independence of the pieces is not part of the data, because it is automatic, as
section F shows.

Multiplicativity of the representation is named by `IsMulRep` and stored in the `rep_mul`
field, so that a decomposition of a product can be assembled from decompositions of the factors
with no further input. `copy` moves a decomposition across an equality of submodules, needed
because a submodule arising in practice is usually only propositionally the one for which a
decomposition was recorded.
-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- **A representation acts by algebra maps**, respecting multiplication. This is the
  hypothesis under which charges are additive. -/
abbrev IsMulRep (rep : Representation ℂ GaugeGroupI B) : Prop :=
  ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y

/-- A representation that respects multiplication respects the unit, since `g` is invertible
  and so `rep g 1` is cancellable. -/
lemma IsMulRep.map_one {rep : Representation ℂ GaugeGroupI B} (hmul : IsMulRep rep)
    (g : GaugeGroupI) : rep g 1 = 1 := by
  have h1 := hmul g 1 (rep g⁻¹ 1)
  rw [one_mul, rep.self_inv_apply, mul_one] at h1
  exact h1.symm

/-!

## C.1. Powers of `expI` under conjugation

-/

lemma starRingEnd_expI_pow (n : ℕ) :
    ((starRingEnd ℂ) (expI : ℂ)) ^ n = ((expI : ℂ) ^ n)⁻¹ := by
  rw [← inv_pow, expI_inv_eq_star]
  rfl

lemma starRingEnd_expI_zpow (z : ℤ) :
    (starRingEnd ℂ) ((expI : ℂ) ^ z) = (expI : ℂ) ^ (-z) := by
  rw [map_zpow₀, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [expI_inv_eq_star]
  rfl

lemma expI_zpow_ne_zero (z : ℤ) : ((expI : ℂ) ^ z) ≠ 0 :=
  zpow_ne_zero _ (by simp [expI, Complex.exp_ne_zero])

/-!

## C.2. The torus weights of the fundamental representations

The colour and isospin weights of the fundamental representations of `SU(3)` and
`SU(2)` against the torus generators.  They are the building blocks of the gauge
weights of the matter representations.

-/

/-- The colour weights of the fundamental of `SU(3)` against the two colour torus
  generators. -/
def colourWeight (c : Fin 3) : ℤ × ℤ := ![(1, 0), (-1, 1), (0, -1)] c

/-- The isospin weight of the fundamental of `SU(2)` against the isospin torus
  generator. -/
def isoWeight (s : Fin 2) : ℤ := ![1, -1] s

/-!

## C.3. The torus action on dual and conjugate bases

If the torus acts diagonally on a basis then it acts diagonally on the dual basis with
the negated weights, and on the conjugate basis with the negated weights as well — so
the conjugate-dual action carries the original weights back.

-/

section TorusBases

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma dual_gaugeTorusGen_coord (ρ : Representation ℂ GaugeGroupI V)
    (b : Module.Basis ι ℂ V) (g : GaugeGroupI) (w : ι → ℤ)
    (hb : ∀ j, ρ g (b j) = ((expI : ℂ) ^ w j) • b j) (j : ι) :
    ρ.dual g (b.coord j) = ((expI : ℂ) ^ (-(w j))) • b.coord j := by
  have hinv : ∀ j', ρ g⁻¹ (b j') = ((expI : ℂ) ^ (-(w j'))) • b j' := by
    intro j'
    have h1 : ρ g⁻¹ (ρ g (b j')) = b j' := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    rw [hb j', map_smul] at h1
    rw [_root_.zpow_neg]
    exact ((inv_smul_eq_iff₀ (expI_zpow_ne_zero (w j'))).mpr h1.symm).symm
  refine b.ext fun j' => ?_
  rw [Representation.dual_apply]
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, hinv j', map_smul,
    LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
  by_cases hne : j' = j
  · subst hne
    simp
  · simp [hne]

omit [Fintype ι] [DecidableEq ι] in
lemma conj_gaugeTorusGen_basis (ρ : Representation ℂ GaugeGroupI V)
    (b : Module.Basis ι ℂ V) (g : GaugeGroupI) (w : ι → ℤ)
    (hb : ∀ j, ρ g (b j) = ((expI : ℂ) ^ w j) • b j) (j : ι) :
    ρ.conj g (Module.Basis.conj b j)
      = ((expI : ℂ) ^ (-(w j))) • Module.Basis.conj b j := by
  simp only [Module.Basis.conj_apply, Representation.conj_apply,
    LinearEquiv.symm_apply_apply, hb j, map_smulₛₗ, starRingEnd_expI_zpow]

end TorusBases

/-- A **gauge weight decomposition** of a submodule `V`, a finitely supported family of
  subspaces of pure gauge weight whose supremum is `V`. Purity is recorded against the four
  commuting torus generators simultaneously. -/
class GaugeWeightDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The piece of gauge weight `w`. -/
  piece : GaugeWeight → Submodule ℂ B
  /-- The finite set of gauge weights that occur. -/
  supp : Finset GaugeWeight
  /-- Gauge transformations act by algebra maps. -/
  rep_mul : IsMulRep rep
  /-- Each piece is of pure gauge weight, as seen by all four torus generators. -/
  piece_le : ∀ w, ∀ x, x ∈ piece w → ∀ i,
    rep (gaugeTorusGen i) x = ((expI : ℂ) ^ w.coord i) • x
  /-- Only the gauge weights in `supp` occur. -/
  piece_eq_bot : ∀ w ∉ supp, piece w = ⊥
  /-- The pieces exhaust `V`. -/
  iSup_piece : (⨆ w, piece w) = V

namespace GaugeWeightDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The weight-`w` piece lies in the eigenspace of the `i`-th torus generator at the
  eigenvalue `(exp i) ^ (w.coord i)`. This is `piece_le` phrased as an inequality of
  submodules. -/
lemma piece_le_eigenspace (d : GaugeWeightDecomposition rep V) (w : GaugeWeight) (i : Fin 4) :
    d.piece w ≤ Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) :=
  fun _ hy => Module.End.mem_eigenspace_iff.mpr (d.piece_le w _ hy i)

/-- A weight outside the support has vanishing piece. This is the `piece_eq_bot` field, in
  the form a `simp` set can use to discard the absent weights of a computed product. -/
lemma piece_eq_zero_of_not_mem_supp (d : GaugeWeightDecomposition rep V) (w : GaugeWeight)
    (hw : w ∉ d.supp) : d.piece w = ⊥ := d.piece_eq_bot w hw

/-- Transport a decomposition along an equality of submodules. -/
@[implicit_reducible]
def copy (d : GaugeWeightDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    GaugeWeightDecomposition rep W where
  piece := d.piece
  supp := d.supp
  rep_mul := d.rep_mul
  piece_le := d.piece_le
  piece_eq_bot := d.piece_eq_bot
  iSup_piece := by rw [d.iSup_piece, hW]

@[simp]
lemma copy_piece (d : GaugeWeightDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    (copy d W hW).piece = d.piece := rfl

/-!
## D. Joins

If `V` and `V'` are decomposed then so is their join `V ⊔ V'`, one weight at a time. Its
weight-`w` piece is the join of the two weight-`w` pieces, and its support is the union of the
supports. A vector of the join need not have definite charge, but it is a sum of vectors that
do, which is all a decomposition claims.

The binary case `sup`, the empty case `bot`, a finite indexed family `iSup` and a join over a
proposition `iSupProp` are all the same construction. Multiplicativity of `rep` is recovered
from a summand where there is one and supplied as an argument where there is not, since `bot`
decomposes the zero submodule and the indexed forms may range over an empty family.
-/

/-- The join of two gauge weight decompositions, decomposing `V ⊔ V'`. Pieces and supports
  combine one weight at a time. -/
@[implicit_reducible]
noncomputable instance sup [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep V'] : GaugeWeightDecomposition rep (V ⊔ V') where
  piece w := d.piece w ⊔ d'.piece w
  supp := d.supp ∪ d'.supp
  rep_mul := d.rep_mul
  piece_le w x hx i :=
    Module.End.mem_eigenspace_iff.mp
      (sup_le (d.piece_le_eigenspace w i) (d'.piece_le_eigenspace w i) hx)
  piece_eq_bot w hw := by
    rw [Finset.mem_union, not_or] at hw
    rw [d.piece_eq_bot w hw.1, d'.piece_eq_bot w hw.2, bot_sup_eq]
  iSup_piece := by
    rw [iSup_sup_eq, d.iSup_piece, d'.iSup_piece]

@[simp]
lemma sup_piece [GaugeWeightDecomposition rep V] [GaugeWeightDecomposition rep V']
    (w : GaugeWeight) : piece rep (V ⊔ V') w = piece rep V w ⊔ piece rep V' w := rfl

/-- The zero submodule carries the empty decomposition. -/
@[implicit_reducible]
def bot (hmul : IsMulRep rep) :
    GaugeWeightDecomposition rep (⊥ : Submodule ℂ B) where
  piece _ := ⊥
  supp := ∅
  rep_mul := hmul
  piece_le w x hx i := by
    rw [Submodule.mem_bot] at hx
    subst hx
    simp
  piece_eq_bot _ _ := rfl
  iSup_piece := by simp

@[simp]
lemma bot_piece (hmul : IsMulRep rep)
    (w : GaugeWeight) : (bot hmul).piece w = ⊥ := rfl

@[simp]
lemma bot_supp (hmul : IsMulRep rep) :
    (bot hmul).supp = ∅ := rfl

/-- **The span of a single simultaneous eigenvector** of the gauge torus, as a
  decomposition concentrated in its one weight. This is the base case from which the
  decompositions of spans of weight vectors are assembled by `iSup` and `sup`. -/
@[implicit_reducible]
noncomputable def spanSingleton (hmul : IsMulRep rep) (x : B) (w : GaugeWeight)
    (hx : ∀ i, rep (gaugeTorusGen i) x = ((expI : ℂ) ^ w.coord i) • x) :
    GaugeWeightDecomposition rep (Submodule.span ℂ {x}) where
  piece w' := if w' = w then Submodule.span ℂ {x} else ⊥
  supp := {w}
  rep_mul := hmul
  piece_le := by
    intro w' y hy i
    split_ifs at hy with hw'
    · subst hw'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, hx i, smul_comm]
    · rw [Submodule.mem_bot] at hy
      subst hy
      simp
  piece_eq_bot := by
    intro w' hw'
    rw [if_neg (by simpa using hw')]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w' => ?_) (le_iSup_of_le w (by rw [if_pos rfl]))
    split_ifs
    · exact le_rfl
    · exact bot_le

@[simp]
lemma spanSingleton_piece (hmul : IsMulRep rep) (x : B) (w : GaugeWeight)
    (hx : ∀ i, rep (gaugeTorusGen i) x = ((expI : ℂ) ^ w.coord i) • x)
    (w' : GaugeWeight) :
    (spanSingleton hmul x w hx).piece w'
      = if w' = w then Submodule.span ℂ {x} else ⊥ := rfl

/-- **An indexed join of decompositions.** A family of decompositions indexed by a finite type
  decomposes the join, its pieces joined and its supports united one weight at a time. This is
  the arbitrary-arity form of `sup`. -/
@[implicit_reducible]
noncomputable def iSup {ι : Type*} [Fintype ι] {V : ι → Submodule ℂ B}
    (hmul : IsMulRep rep)
    (d : (a : ι) → GaugeWeightDecomposition rep (V a)) :
    GaugeWeightDecomposition rep (⨆ a, V a) where
  piece w := ⨆ a, (d a).piece w
  supp := Finset.univ.biUnion fun a => (d a).supp
  rep_mul := hmul
  piece_le w x hx i :=
    Module.End.mem_eigenspace_iff.mp
      (iSup_le (fun a => (d a).piece_le_eigenspace w i) hx)
  piece_eq_bot w hw := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hw
    exact le_antisymm (iSup_le fun a => le_of_eq ((d a).piece_eq_bot w (hw a))) bot_le
  iSup_piece := by
    rw [iSup_comm]
    exact iSup_congr fun a => (d a).iSup_piece

@[simp]
lemma piece_iSup {ι : Type*} [Fintype ι] {V : ι → Submodule ℂ B}
    (hmul : IsMulRep rep)
    (d : (a : ι) → GaugeWeightDecomposition rep (V a)) (w : GaugeWeight) :
    (iSup hmul d).piece w = ⨆ a, (d a).piece w := rfl

/-- The support of an indexed join is the union of the supports. -/
lemma iSup_supp {ι : Type*} [Fintype ι] {V : ι → Submodule ℂ B}
    (hmul : IsMulRep rep)
    (d : (a : ι) → GaugeWeightDecomposition rep (V a)) :
    (iSup hmul d).supp = Finset.univ.biUnion fun a => (d a).supp := rfl

/-- **A join over a proposition.** `⨆ _ : p, V` is `V` when `p` holds and `⊥` otherwise, so
  it is decomposed by the given decomposition or by `bot`. The argument is a function of the
  proof, so the decomposition of `V` may itself depend on `p`. -/
@[implicit_reducible]
noncomputable def iSupProp {p : Prop} [Decidable p]
    (hmul : IsMulRep rep)
    (d : p → GaugeWeightDecomposition rep V) :
    GaugeWeightDecomposition rep (⨆ _ : p, V) :=
  if hp : p then copy (d hp) _ (iSup_pos hp) else copy (bot hmul) _ (iSup_neg hp)

/-!
## E. Products

Charges add when operators are multiplied, and this section is where we prove this fact.
If the torus acts on `x` by the character of `w₁` and on `y` by the character of `w₂` then,
because `rep` respects multiplication, it acts on `x * y` by the product of the two characters,
which additivity of `GaugeWeight.coord` identifies with the character of `w₁ + w₂`. So the
weight-`w` piece of `V * V'` is spanned by products of pieces whose weights sum to `w`, and the
support of a product is the sumset of the supports.

The unit and the powers belong here for the same reason. The identity of the algebra is a gauge
singlet and so has weight zero, and `V ^ k` is decomposed by iterating the product from it.

The defining formula `mul_piece` joins over all pairs of weights in `ℤ⁴ × ℤ⁴`. Only finitely
many weights occur, so one of the two can always be eliminated against a support, and
`mul_piece_eq_sub`, `mul_piece_eq_sub'` and `mul_piece_of_supp` do this against the left
factor, the right factor and a supplied finite set. The resulting finite joins are what make
the weight pieces of an iterated product computable.
-/

/-- The product of two gauge weight decompositions, decomposing `V * V'`. -/
@[implicit_reducible]
noncomputable instance mul [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep V'] :
    GaugeWeightDecomposition rep (V * V') where
  piece w := ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, d.piece w₁ * d'.piece w₂
  supp := d.supp + d'.supp
  rep_mul := d.rep_mul
  piece_le w x hx i := by
    have key : (⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, d.piece w₁ * d'.piece w₂)
        ≤ Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) := by
      refine iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_
      refine Submodule.mul_le.mpr fun m hm n hn => ?_
      refine Module.End.mem_eigenspace_iff.mpr ?_
      rw [d.rep_mul, d.piece_le w₁ m hm i, d'.piece_le w₂ n hn i, smul_mul_smul_comm,
        ← zpow_add₀ expI_ne_zero, ← GaugeWeight.coord_add, hw]
    exact Module.End.mem_eigenspace_iff.mp (key hx)
  piece_eq_bot w hw := by
    refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hsum => ?_) bot_le
    by_cases h1 : w₁ ∈ d.supp
    · by_cases h2 : w₂ ∈ d'.supp
      · exact absurd (hsum ▸ Finset.add_mem_add h1 h2) hw
      · rw [d'.piece_eq_bot w₂ h2, Submodule.mul_bot]
    · rw [d.piece_eq_bot w₁ h1, Submodule.bot_mul]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w => iSup_le fun w₁ => iSup_le fun w₂ =>
      iSup_le fun _ => ?_) ?_
    · exact mul_le_mul' ((le_iSup d.piece w₁).trans d.iSup_piece.le)
        ((le_iSup d'.piece w₂).trans d'.iSup_piece.le)
    · have hV : (⨆ w₁, d.piece w₁) * (⨆ w₂, d'.piece w₂) = V * V' := by
        rw [d.iSup_piece, d'.iSup_piece]
      rw [← hV, Submodule.iSup_mul]
      refine iSup_le fun w₁ => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun w₂ => ?_
      exact le_iSup_of_le (w₁ + w₂)
        (le_iSup_of_le w₁ (le_iSup_of_le w₂ (le_iSup_of_le rfl le_rfl)))

/-- The support of a product is the pointwise sum of the supports. -/
lemma mul_supp [GaugeWeightDecomposition rep V] [GaugeWeightDecomposition rep V'] :
    supp rep (V * V') = supp rep V + supp rep V' := rfl

/-- **Weights add under multiplication.** The weight-`w` piece of a product is spanned by the
  products of pieces whose weights sum to `w`. -/
lemma mul_piece [GaugeWeightDecomposition rep V] [GaugeWeightDecomposition rep V']
    (w : GaugeWeight) :
    piece rep (V * V') w
      = ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, piece rep V w₁ * piece rep V' w₂ := rfl

/-- The product formula with the second weight eliminated against the support of the left
  factor, the right factor being read at the complement `w - w₁`. -/
lemma mul_piece_eq_sub [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep V'] (w : GaugeWeight) :
    piece rep (V * V') w = ⨆ w₁ ∈ supp rep V, piece rep V w₁ * piece rep V' (w - w₁) := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases h1 : w₁ ∈ d.supp
    · refine le_iSup₂_of_le w₁ h1 ?_
      rw [eq_sub_of_add_eq' hw]
    · rw [d.piece_eq_bot w₁ h1, Submodule.bot_mul]
      exact bot_le
  · exact iSup₂_le fun w₁ _ =>
      le_iSup_of_le w₁ (le_iSup_of_le (w - w₁) (le_iSup_of_le (add_sub_cancel w₁ w) le_rfl))

/-- The mirror of `mul_piece_eq_sub`, joining over the weights of the right factor. -/
lemma mul_piece_eq_sub' [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep V'] (w : GaugeWeight) :
    piece rep (V * V') w = ⨆ w₂ ∈ supp rep V', piece rep V (w - w₂) * piece rep V' w₂ := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases h2 : w₂ ∈ d'.supp
    · refine le_iSup₂_of_le w₂ h2 ?_
      rw [eq_sub_of_add_eq hw]
    · rw [d'.piece_eq_bot w₂ h2, Submodule.mul_bot]
      exact bot_le
  · exact iSup₂_le fun w₂ _ =>
      le_iSup_of_le (w - w₂) (le_iSup_of_le w₂ (le_iSup_of_le (sub_add_cancel w w₂) le_rfl))

/-- The decomposition of the unit submodule, concentrated at weight zero. -/
@[implicit_reducible]
noncomputable def one (hmul : IsMulRep rep) :
    GaugeWeightDecomposition rep (1 : Submodule ℂ B) where
  piece w := if w = 0 then 1 else ⊥
  supp := {0}
  rep_mul := hmul
  piece_le := by
    intro w x hx i
    rcases eq_or_ne w 0 with rfl | hw
    · rw [if_pos rfl, Submodule.one_eq_span, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, hmul.map_one, GaugeWeight.zero_coord, zpow_zero, one_smul]
    · rw [if_neg hw, Submodule.mem_bot] at hx
      subst hx
      simp
  piece_eq_bot w hw := by rw [if_neg (by simpa using hw)]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w => ?_) (le_iSup_of_le 0 (le_of_eq (if_pos rfl).symm))
    by_cases hw : w = 0
    · rw [if_pos hw]
    · rw [if_neg hw]
      exact bot_le

@[simp]
lemma one_piece (hmul : IsMulRep rep)
    (w : GaugeWeight) :
    (one (B := B) (rep := rep) hmul).piece w = if w = 0 then 1 else ⊥ := rfl

/-- When the right factor vanishes off a finite set `S` of weights, the weight-`w` piece of a
  product collapses to a join over `S`, pairing `w - v` against `v`. -/
lemma mul_piece_of_supp [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep V'] (S : Finset GaugeWeight)
    (hS : ∀ v ∉ S, piece rep V' v = ⊥) (w : GaugeWeight) :
    piece rep (V * V') w = ⨆ v ∈ S, piece rep V (w - v) * piece rep V' v := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun w₁ => iSup_le fun w₂ => iSup_le fun hw => ?_) ?_
  · by_cases hv : w₂ ∈ S
    · refine le_iSup₂_of_le w₂ hv ?_
      rw [eq_sub_of_add_eq hw]
    · rw [hS w₂ hv, Submodule.mul_bot]
      exact bot_le
  · exact iSup₂_le fun v _ =>
      le_iSup_of_le (w - v) (le_iSup_of_le v (le_iSup_of_le (sub_add_cancel w v) le_rfl))

/-- Powers of a decomposed submodule. Gauge weights add, so `V ^ k` inherits a decomposition
  by iterating `mul` from `one`. -/
@[implicit_reducible]
noncomputable instance pow [d : GaugeWeightDecomposition rep V] :
    (k : ℕ) → GaugeWeightDecomposition rep (V ^ k)
  | 0 => copy (one d.rep_mul) _ (pow_zero V)
  | (k + 1) => copy (mul (d := pow (d := d) k) (d' := d)) _ (pow_succ V k)

@[simp]
lemma pow_zero_piece [d : GaugeWeightDecomposition rep V] (w : GaugeWeight) :
    (pow (d := d) 0).piece w = if w = 0 then 1 else ⊥ := rfl

/-- One step of the power decomposition. Since `V ^ (k + 1)` is `V ^ k` times `V`, its pieces
  are given by the product formula against the pieces of `V`. -/
@[simp]
lemma pow_succ_piece [d : GaugeWeightDecomposition rep V] (k : ℕ) (w : GaugeWeight) :
    (pow (d := d) (k + 1)).piece w
      = ⨆ w₁, ⨆ w₂, ⨆ _ : w₁ + w₂ = w, (pow (d := d) k).piece w₁ * piece rep V w₂ := rfl

/-- The `mul_piece_of_supp` collapse applied to a power, so that only the weights in `S`
  contribute at each step. -/
lemma pow_succ_piece_of_supp [d : GaugeWeightDecomposition rep V] (S : Finset GaugeWeight)
    (hS : ∀ v ∉ S, piece rep V v = ⊥) (k : ℕ) (w : GaugeWeight) :
    (pow (d := d) (k + 1)).piece w
      = ⨆ v ∈ S, (pow (d := d) k).piece (w - v) * piece rep V v :=
  mul_piece_of_supp (d := pow (d := d) k) (d' := d) S hS w

/-!
## F. Invariants

A gauge-invariant element is fixed by the torus in particular, so it ought to have zero weight.
Making that an argument requires knowing the pieces are independent. Along one generator this
is immediate, since the pieces sit in eigenspaces of a single operator at the eigenvalues
`(exp i) ^ k`, pairwise distinct because `exp i` is not a root of unity, and eigenspaces at
distinct eigenvalues meet trivially. At rank four no single generator separates the weights, so
the argument is made one generator at a time.

What this yields is stronger than the statement about invariants. `piece_eq_inf` identifies the
weight-`w` piece with the intersection of `V` and the joint eigenspace of the four generators,
so the pieces depend only on `V` and the representation.

Zero weight is necessary but not sufficient for invariance. The torus is abelian and sees only
characters, so it cannot distinguish a true singlet from the neutral component of a higher
multiplet. Both `H†H` and `H†σ³H` carry zero weight, and only the first is gauge invariant. So
what passes `mem_zero_of_invariant` must still be checked. `SU2PermDecomposition` narrows the
`SU(2)` factor further, but no grading closes the gap, since a grading sees only the abelian
subgroup generated by the elements it uses.
-/

/-- **The one-generator refinement step.** A vector in the span of a family graded along a
  single operator, and an eigenvector of that operator at exponent `n`, lies in the span of
  just those pieces at exponent `n`. -/
lemma mem_iSup_of_eigenvector {ι : Type*} {T : Module.End ℂ B} {p : ι → Submodule ℂ B}
    {f : ι → ℤ} (hp : ∀ j, p j ≤ Module.End.eigenspace T ((expI : ℂ) ^ f j))
    {x : B} (hx : x ∈ ⨆ j, p j) {n : ℤ} (hT : T x = ((expI : ℂ) ^ n) • x) :
    x ∈ ⨆ j, ⨆ _ : f j = n, p j := by
  have hQle : ∀ k : ℤ, (⨆ j, ⨆ _ : f j = k, p j)
      ≤ Module.End.eigenspace T ((expI : ℂ) ^ k) :=
    fun k => iSup₂_le fun j hj => hj ▸ hp j
  have hQsup : (⨆ k : ℤ, ⨆ j, ⨆ _ : f j = k, p j) = ⨆ j, p j := by
    rw [iSup_comm]
    exact iSup_congr fun j =>
      le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le (f j) rfl le_rfl)
  have hdisj : Disjoint (Module.End.eigenspace T ((expI : ℂ) ^ n))
      (⨆ k : ℤ, ⨆ _ : k ≠ n, ⨆ j, ⨆ _ : f j = k, p j) :=
    (((Module.End.eigenspaces_iSupIndep T).comp expI_zpow_injective) n).mono_right
      (iSup₂_mono fun k _ => hQle k)
  have key : (⨆ k : ℤ, ⨆ j, ⨆ _ : f j = k, p j)
      ⊓ Module.End.eigenspace T ((expI : ℂ) ^ n) ≤ ⨆ j, ⨆ _ : f j = n, p j := by
    rw [iSup_split_single (fun k : ℤ => ⨆ j, ⨆ _ : f j = k, p j) n,
      sup_inf_assoc_of_le _ (hQle n)]
    exact sup_le le_rfl (hdisj.symm.le_bot.trans bot_le)
  exact key ⟨hQsup ▸ hx, Module.End.mem_eigenspace_iff.mpr hT⟩

/-- **The many-generator refinement.** The same for a finite family of operators. A vector in
  the span of the family and an eigenvector of every operator lies in the span of just those
  pieces whose exponents match throughout. -/
lemma mem_iSup_of_forall_eigenvector {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    {T : κ → Module.End ℂ B} {p : ι → Submodule ℂ B} {f : ι → κ → ℤ}
    (hp : ∀ j k, p j ≤ Module.End.eigenspace (T k) ((expI : ℂ) ^ f j k))
    {x : B} (hx : x ∈ ⨆ j, p j) {n : κ → ℤ}
    (hT : ∀ k, T k x = ((expI : ℂ) ^ n k) • x) :
    x ∈ ⨆ j, ⨆ _ : f j = n, p j := by
  have key : ∀ S : Finset κ, x ∈ ⨆ j, ⨆ _ : ∀ k ∈ S, f j k = n k, p j := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hx
    | @insert k S hk ih =>
      have hstep := mem_iSup_of_eigenvector (T := T k) (f := fun j => f j k)
        (p := fun j => ⨆ _ : ∀ k' ∈ S, f j k' = n k', p j)
        (fun j => iSup_le fun _ => hp j k) ih (hT k)
      have hle : (⨆ j, ⨆ _ : f j k = n k, ⨆ _ : ∀ k' ∈ S, f j k' = n k', p j)
          ≤ ⨆ j, ⨆ _ : ∀ k' ∈ insert k S, f j k' = n k', p j := by
        refine iSup_le fun j => iSup_le fun h1 => iSup_le fun h2 =>
          le_iSup_of_le j (le_iSup_of_le ?_ le_rfl)
        intro k' hk'
        rcases Finset.mem_insert.mp hk' with rfl | hk'S
        · exact h1
        · exact h2 k' hk'S
      exact hle hstep
  have hle : (⨆ j, ⨆ _ : ∀ k ∈ (Finset.univ : Finset κ), f j k = n k, p j)
      ≤ ⨆ j, ⨆ _ : f j = n, p j :=
    iSup_le fun j => iSup_le fun hj =>
      le_iSup_of_le j (le_iSup_of_le (funext fun k => hj k (Finset.mem_univ k)) le_rfl)
  exact hle (key Finset.univ)

/-- **The pieces are canonical.** The weight-`w` piece is exactly the part of `V` on which the
  four torus generators act by the weight-`w` characters. See `piece_congr`. -/
lemma piece_eq_inf (d : GaugeWeightDecomposition rep V) (w : GaugeWeight) :
    d.piece w
      = V ⊓ ⨅ i, Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) := by
  refine le_antisymm (le_inf ((le_iSup d.piece w).trans (le_of_eq d.iSup_piece))
    (le_iInf fun i => d.piece_le_eigenspace w i)) fun x hx => ?_
  obtain ⟨hxV, hxE⟩ := hx
  have hx0 : x ∈ ⨆ w' : GaugeWeight, d.piece w' := by rw [d.iSup_piece]; exact hxV
  have hspan : x ∈ ⨆ w' : GaugeWeight, ⨆ _ : w'.coord = w.coord, d.piece w' :=
    mem_iSup_of_forall_eigenvector (T := fun i => rep (gaugeTorusGen i)) (p := d.piece)
      (f := fun w' : GaugeWeight => w'.coord) (n := w.coord)
      (fun w' i => d.piece_le_eigenspace w' i) hx0
      (fun i => Module.End.mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hxE i))
  have hle : (⨆ w' : GaugeWeight, ⨆ _ : w'.coord = w.coord, d.piece w') ≤ d.piece w :=
    iSup_le fun w' => iSup_le fun hw' =>
      le_of_eq (congrArg d.piece (GaugeWeight.coord_injective hw'))
  exact hle hspan

/-- **The pieces depend only on the submodule.** Two decompositions of equal submodules have
  the same pieces, so a computation of `piece` may be carried along any equality of
  submodules. -/
lemma piece_congr {W : Submodule ℂ B} [d : GaugeWeightDecomposition rep V]
    [d' : GaugeWeightDecomposition rep W] (hVW : V = W) (w : GaugeWeight) :
    d.piece w = d'.piece w := by
  rw [d.piece_eq_inf, d'.piece_eq_inf, hVW]

/-- **A gauge-invariant element sits in the zero-weight piece.** Only invariance under the
  four torus generators is used. The converse is false; see the warning in section F. -/
lemma mem_zero_of_invariant (d : GaugeWeightDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ d.piece 0 := by
  rw [d.piece_eq_inf]
  refine ⟨hx, Submodule.mem_iInf _ |>.mpr fun i => ?_⟩
  rw [Module.End.mem_eigenspace_iff, GaugeWeight.zero_coord, zpow_zero, one_smul]
  exact hV _

/-!
## G. Compatibility with the boost weight decomposition

The gauge group acts on the value indices of an operator and the Lorentz group on its
spacetime indices, so in every representation met here the two actions commute. Given that, a
submodule carrying both a gauge weight decomposition and a boost weight decomposition passes
the second one down to each piece of the first.

The content is that a boost-homogeneous component of a vector of pure gauge weight again has
that gauge weight. A torus generator commutes with the boosts, so it preserves every boost
weight space; the boost weight spaces are independent, so the weight-`k` component of a
scaled vector is the scaled weight-`k` component; and the eigenvector equations defining the
gauge weight therefore descend to every component. The lattice identity `piece_eq_inf` then
places each component back in the gauge weight piece.

Meets do not distribute over suprema in a submodule lattice, so the independence is what makes
the argument work; it is isolated in `biSup_inf_eigenspace_le` and its two corollaries, which
know nothing about either group.
-/

section BoostWeight

open MatrixGroups
open Lorentz.BoostWeight (WeightDecomposition boostWeightSubmodule mem_boostWeightSubmodule
  boostWeightSubmodule_iSupIndep)

variable {repLorentz : Representation ℂ SL(2,ℂ) B} {i : Fin 3}

/-- **Refining a finite independent decomposition by a commuting operator.** If the pieces `p`
  sit inside an independent family `P` of `T`-invariant submodules, then an eigenvector of `T`
  in the join of the pieces is the sum of eigenvectors, one in each piece. -/
lemma biSup_inf_eigenspace_le {ι : Type*} {P p : ι → Submodule ℂ B} (hpP : ∀ j, p j ≤ P j)
    (hP : iSupIndep P) {T : Module.End ℂ B} (hT : ∀ j, (P j).map T ≤ P j) (c : ℂ)
    (s : Finset ι) :
    (⨆ j ∈ s, p j) ⊓ Module.End.eigenspace T c
      ≤ ⨆ j ∈ s, (p j ⊓ Module.End.eigenspace T c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.iSup_insert]
    rintro x ⟨hx, hxE⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    have hvP : v ∈ ⨆ j ∈ s, P j := (iSup₂_mono fun j _ => hpP j) hv
    have hTv : T v ∈ ⨆ j ∈ s, P j := by
      have hmap : (⨆ j ∈ s, P j).map T ≤ ⨆ j ∈ s, P j := by
        simp only [Submodule.map_iSup]
        exact iSup₂_mono fun j _ => hT j
      exact hmap ⟨v, hvP, rfl⟩
    have hzero : (T u - c • u) + (T v - c • v) = 0 := by
      have hsum : T (u + v) = c • (u + v) := Module.End.mem_eigenspace_iff.mp hxE
      rw [map_add, smul_add] at hsum
      rw [show (T u - c • u) + (T v - c • v) = (T u + T v) - (c • u + c • v) from by abel,
        hsum, sub_self]
    have hdisj : Disjoint (P a) (⨆ j ∈ s, P j) :=
      (hP a).mono_right (iSup₂_le fun j hj =>
        le_iSup₂_of_le j (show j ≠ a from fun hja => ha (hja ▸ hj)) le_rfl)
    have hu0 : T u - c • u = 0 := by
      refine Submodule.disjoint_def.mp hdisj _ (sub_mem (hT a ⟨u, hpP a hu, rfl⟩)
        (Submodule.smul_mem _ _ (hpP a hu))) ?_
      rw [show T u - c • u = -(T v - c • v) from by rw [eq_neg_iff_add_eq_zero]; exact hzero]
      exact neg_mem (sub_mem hTv (Submodule.smul_mem _ _ hvP))
    have hv0 : T v - c • v = 0 := by rwa [hu0, zero_add] at hzero
    refine Submodule.mem_sup.mpr ⟨u, ⟨hu, Module.End.mem_eigenspace_iff.mpr (by
      rwa [sub_eq_zero] at hu0)⟩, v, ih ⟨hv, Module.End.mem_eigenspace_iff.mpr (by
      rwa [sub_eq_zero] at hv0)⟩, rfl⟩

/-- **Refining an independent decomposition by a commuting operator.** The form of
  `biSup_inf_eigenspace_le` for a family vanishing off a finite set of indices. -/
lemma iSup_inf_eigenspace_le {ι : Type*} {P p : ι → Submodule ℂ B} {s : Finset ι}
    (hpP : ∀ j, p j ≤ P j) (hbot : ∀ j ∉ s, p j = ⊥) (hP : iSupIndep P)
    {T : Module.End ℂ B} (hT : ∀ j, (P j).map T ≤ P j) (c : ℂ) :
    (⨆ j, p j) ⊓ Module.End.eigenspace T c
      ≤ ⨆ j, (p j ⊓ Module.End.eigenspace T c) := by
  classical
  have hs : (⨆ j, p j) = ⨆ j ∈ s, p j := by
    refine le_antisymm (iSup_le fun j => ?_) (iSup₂_le fun j _ => le_iSup p j)
    by_cases hj : j ∈ s
    · exact le_iSup₂_of_le j hj le_rfl
    · rw [hbot j hj]
      exact bot_le
  rw [hs]
  exact (biSup_inf_eigenspace_le hpP hP hT c s).trans
    (iSup₂_le fun j _ => le_iSup (fun j => p j ⊓ Module.End.eigenspace T c) j)

/-- **Refining an independent decomposition by a family of commuting operators.** A joint
  eigenvector of finitely many operators preserving each member of an independent family is a
  sum of joint eigenvectors, one in each piece. -/
lemma iSup_inf_iInf_eigenspace_le {ι κ : Type*} [Fintype κ] {P p : ι → Submodule ℂ B}
    {s : Finset ι} (hpP : ∀ j, p j ≤ P j) (hbot : ∀ j ∉ s, p j = ⊥) (hP : iSupIndep P)
    {T : κ → Module.End ℂ B} (hT : ∀ a j, (P j).map (T a) ≤ P j) (c : κ → ℂ) :
    (⨆ j, p j) ⊓ ⨅ a, Module.End.eigenspace (T a) (c a)
      ≤ ⨆ j, (p j ⊓ ⨅ a, Module.End.eigenspace (T a) (c a)) := by
  classical
  have key : ∀ (S : Finset κ) (q : ι → Submodule ℂ B), (∀ j, q j ≤ P j) →
      (∀ j ∉ s, q j = ⊥) →
      (⨆ j, q j) ⊓ (⨅ a ∈ S, Module.End.eigenspace (T a) (c a))
        ≤ ⨆ j, (q j ⊓ ⨅ a ∈ S, Module.End.eigenspace (T a) (c a)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro q _ _
      simp
    | @insert a S ha ih =>
      intro q hq hqbot
      simp only [Finset.iInf_insert, ← inf_assoc]
      refine le_trans (inf_le_inf_right _ (iSup_inf_eigenspace_le hq hqbot hP
        (fun j => hT a j) (c a))) ?_
      exact ih (fun j => q j ⊓ Module.End.eigenspace (T a) (c a))
        (fun j => inf_le_left.trans (hq j))
        (fun j hj => by rw [hqbot j hj, bot_inf_eq])
  have huniv : (⨅ a ∈ (Finset.univ : Finset κ), Module.End.eigenspace (T a) (c a))
      = ⨅ a, Module.End.eigenspace (T a) (c a) := by simp
  rw [← huniv]
  exact key Finset.univ p hpP hbot

/-- **A gauge transformation preserves every boost weight space**, when the gauge action and
  the Lorentz action commute. The boosts are what cut out the weight space, and the two
  actions may be exchanged past them. -/
lemma boostWeightSubmodule_map_le
    (hcomm : ∀ (g : GaugeGroupI) (Λ : SL(2,ℂ)) (x : B),
      rep g (repLorentz Λ x) = repLorentz Λ (rep g x)) (g : GaugeGroupI) (k : ℤ) :
    (boostWeightSubmodule repLorentz i k).map (rep g)
      ≤ boostWeightSubmodule repLorentz i k := by
  rintro _ ⟨y, hy, rfl⟩
  refine mem_boostWeightSubmodule.mpr fun t ht => ?_
  rw [← hcomm, mem_boostWeightSubmodule.mp hy t ht, map_smul]

/-- **A gauge weight piece inherits the boost weight decomposition.** If `V` carries both a
  gauge weight decomposition and a boost weight decomposition, and the two actions commute,
  then the weight-`w` gauge piece is decomposed by its intersections with the boost pieces. -/
noncomputable def pieceBoostWeightDecomposition (d : GaugeWeightDecomposition rep V)
    (b : WeightDecomposition repLorentz i V)
    (hcomm : ∀ (g : GaugeGroupI) (Λ : SL(2,ℂ)) (x : B),
      rep g (repLorentz Λ x) = repLorentz Λ (rep g x)) (w : GaugeWeight) :
    WeightDecomposition repLorentz i (d.piece w) where
  piece k := b.piece k ⊓ d.piece w
  supp := b.supp
  piece_le k := inf_le_left.trans (b.piece_le k)
  piece_eq_bot k hk := by rw [b.piece_eq_bot k hk, bot_inf_eq]
  iSup_piece := by
    refine le_antisymm (iSup_le fun k => inf_le_right) ?_
    have hpiece : ∀ k, b.piece k ≤ V := fun k =>
      le_of_le_of_eq (le_iSup b.piece k) b.iSup_piece
    have hkey := iSup_inf_iInf_eigenspace_le (P := boostWeightSubmodule repLorentz i)
      (p := b.piece) (s := b.supp) b.piece_le b.piece_eq_bot
      (boostWeightSubmodule_iSupIndep (i := i) repLorentz)
      (T := fun j => rep (gaugeTorusGen j))
      (hT := fun j k => boostWeightSubmodule_map_le hcomm (gaugeTorusGen j) k)
      (c := fun j => (expI : ℂ) ^ w.coord j)
    rw [b.iSup_piece] at hkey
    refine le_trans (le_of_eq (d.piece_eq_inf w)) (hkey.trans (iSup_mono fun k => ?_))
    refine le_inf inf_le_left ?_
    rw [d.piece_eq_inf]
    exact inf_le_inf (hpiece k) le_rfl

/-- The pieces of the inherited boost weight decomposition. -/
@[simp]
lemma pieceBoostWeightDecomposition_piece (d : GaugeWeightDecomposition rep V)
    (b : WeightDecomposition repLorentz i V)
    (hcomm : ∀ (g : GaugeGroupI) (Λ : SL(2,ℂ)) (x : B),
      rep g (repLorentz Λ x) = repLorentz Λ (rep g x)) (w : GaugeWeight) (k : ℤ) :
    (pieceBoostWeightDecomposition d b hcomm w).piece k = b.piece k ⊓ d.piece w := rfl

/-- The support of the inherited boost weight decomposition. -/
lemma pieceBoostWeightDecomposition_supp (d : GaugeWeightDecomposition rep V)
    (b : WeightDecomposition repLorentz i V)
    (hcomm : ∀ (g : GaugeGroupI) (Λ : SL(2,ℂ)) (x : B),
      rep g (repLorentz Λ x) = repLorentz Λ (rep g x)) (w : GaugeWeight) :
    (pieceBoostWeightDecomposition d b hcomm w).supp = b.supp := rfl

end BoostWeight

end GaugeWeightDecomposition
end StandardModel
