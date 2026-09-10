/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
public import Physlib.Relativity.Fermions.Weyl.BoostWeight
/-!
# Lorentz invariants of a left-handed and a right-handed Weyl index

A bispinor `T^{α α'}`, carrying one left-handed and one right-handed Weyl index, has no
Lorentz invariant built from its four components but `0`. The pair of indices carries the
`(1/2, 1/2)` representation, which is the four-vector representation, and a single
four-vector index has nothing to contract with; this file proves that from scratch on the
spinor side. That is `eq_zero_of_invariant`, and `mem_of_invariant_of_mem_sup` is the same
statement modulo a Lorentz-stable subspace `S`, the form the Standard Model files use.

The components are vectors `T a` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by a pair of Weyl indices, and `IsLeftRightWeyl` says
the group moves the left index by the matrix of `g` and the right index by its complex
conjugate (C). `hT.span` is the set of their combinations.

An invariant of the span is `∑_a c_a • T a` for a coefficient function `c` that the group
itself fixes (C, from `Invariants.Basic`), and the proof then follows the four-vector one with
the light-cone basis replaced by Weyl weight bases. Along a spatial axis the `SL(2,ℂ)` boost is
the diagonal `z`-boost conjugated by `rotationZToAxis i`, so the columns of that rotation are
boost eigenvectors of weight `±1` (A). The coefficients transform contragrediently, so their
weight basis conjugates the left slot and not the right, the opposite of the components; the
four products of a left and a right eigenvector carry weights `2`, `0`, `0`, `-2` (B). An
invariant has weight `0` along every axis, so it is fixed by the weight-zero projection along
each (D); averaging the three gives a matrix `M` with `M ^ 2 = 2 M` (E), and an invariant would
need `M c = 3 c`, which forces `c = 0` (F). Section G divides out `S`.

A family carrying dual Weyl indices transforms by the contragredient `(Λ⁻¹)ᵀ` on the
undotted slot and by `(Λ⁻¹)ᴴ` on the dotted one. That law is `IsDualLeftRightWeyl` here;
its classification, still that there is no invariant, hence no Dirac mass term, is in
`IsVectorLeftRightWeyl`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants
open IsQuadLorentz (quotRep quotRep_mkQ)

/-!

## A. The Weyl weight bases along a spatial axis

Along the `z`-axis the `SL(2,ℂ)` boost is `diag (t, t⁻¹)`, which the standard Weyl basis
already diagonalises, with weights `weylWeight`. Along a general axis the boost is that
one conjugated by `rotationZToAxis`, so the columns of the rotation are the eigenvectors,
recorded here without their `√2` normalisation. A right-handed index sees the conjugate
boost, so its weight basis is the entrywise conjugate.

-/

/-- The axis-`i` Weyl weight basis of a left-handed index, written as coefficient
  vectors on the standard Weyl basis. -/
def weylCoeff (i : Fin 3) (κ α : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 1 else if α = 0 then -1 else 1)
  else if i = 1 then (if κ = α then 1 else Complex.I)
  else (if κ = α then 1 else 0)

/-- The axis-`i` Weyl weight basis of a right-handed index: the entrywise conjugate of
  the left-handed one. -/
def weylCoeffC (i : Fin 3) (κ α : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 1 else if α = 0 then -1 else 1)
  else if i = 1 then (if κ = α then 1 else -Complex.I)
  else (if κ = α then 1 else 0)

/-- The standard Weyl basis of a left-handed index written back in the axis-`i` weight
  basis. -/
noncomputable def weylCoeffInv (i : Fin 3) (α κ : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 2⁻¹ else if α = 0 then -2⁻¹ else 2⁻¹)
  else if i = 1 then (if κ = α then 2⁻¹ else -(2⁻¹ * Complex.I))
  else (if κ = α then 1 else 0)

/-- The standard Weyl basis of a right-handed index written back in the axis-`i` weight
  basis. -/
noncomputable def weylCoeffInvC (i : Fin 3) (α κ : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 2⁻¹ else if α = 0 then -2⁻¹ else 2⁻¹)
  else if i = 1 then (if κ = α then 2⁻¹ else 2⁻¹ * Complex.I)
  else (if κ = α then 1 else 0)

/-- The left-handed weight basis is a basis: the two coefficient matrices are
  inverse. -/
lemma sum_weylCoeffInv_mul (i : Fin 3) (α β : Fin 2) :
    ∑ κ, weylCoeffInv i α κ * weylCoeff i κ β = if α = β then 1 else 0 := by
  fin_cases i <;> fin_cases α <;> fin_cases β <;>
    simp [weylCoeff, weylCoeffInv, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

/-- The right-handed weight basis is a basis: the two coefficient matrices are
  inverse. -/
lemma sum_weylCoeffInvC_mul (i : Fin 3) (α β : Fin 2) :
    ∑ κ, weylCoeffInvC i α κ * weylCoeffC i κ β = if α = β then 1 else 0 := by
  fin_cases i <;> fin_cases α <;> fin_cases β <;>
    simp [weylCoeffC, weylCoeffInvC, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

/-- The matrix of an axis boost is Hermitian, so conjugating an entry transposes it. -/
lemma star_boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (β α : Fin 2) :
    star ((SL2C.boostAxis i t ht).1 β α) = (SL2C.boostAxis i t ht).1 α β := by
  have h := SL2C.boostAxis_conjTranspose i t ht
  have h2 := congrFun (congrFun h α) β
  rwa [Matrix.conjTranspose_apply] at h2

/-- The left-handed weight basis diagonalises the axis-`i` boost, with the weights
  `weylWeight`. -/
lemma sum_boostAxis_weylCoeff (i : Fin 3) (κ β : Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ α, (SL2C.boostAxis i t ht).1 β α * weylCoeff i κ α
      = ((t : ℝ) : ℂ) ^ (weylWeight κ) * weylCoeff i κ β := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  fin_cases i <;> fin_cases κ <;> fin_cases β
  all_goals simp [SL2C.boostAxis, weylCoeff, weylWeight, Fin.sum_univ_two]
  all_goals try field_simp
  all_goals try simp only [Complex.I_sq]
  all_goals try ring

/-- The right-handed weight basis diagonalises the conjugate of the axis-`i` boost,
  with the weights `weylWeight`. -/
lemma sum_boostAxis_weylCoeffC (i : Fin 3) (κ β : Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ α, star ((SL2C.boostAxis i t ht).1 β α) * weylCoeffC i κ α
      = ((t : ℝ) : ℂ) ^ (weylWeight κ) * weylCoeffC i κ β := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [star_boostAxis_apply]
  fin_cases i <;> fin_cases κ <;> fin_cases β
  all_goals simp [SL2C.boostAxis, weylCoeffC, weylWeight, Fin.sum_univ_two]
  all_goals try field_simp
  all_goals try simp only [Complex.I_sq]
  all_goals try ring

/-!

## B. The weight basis of the coefficients of a left-right pair

The two indices are graded independently, so the weight basis of the pair is the tensor
product of the two, and its weight is the sum of the two Weyl weights. What is graded here is
the coefficient function, which transforms contragrediently, so its left slot takes the
conjugated basis and its right slot the plain one, the opposite of the components.

-/

/-- The boost weight of a pair of Weyl weight indices: the sum of the two. -/
def pairWeight (κ : Fin 2 × Fin 2) : ℤ := weylWeight κ.1 + weylWeight κ.2

/-- The weight-zero pairs are the two mixed pairs. -/
lemma sum_weightZeroFilter {M : Type*} [AddCommMonoid M] (f : Fin 2 × Fin 2 → M) :
    ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0), f κ
      = f (0, 1) + f (1, 0) := by
  rw [show (Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0))
      = {(0, 1), (1, 0)} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- The axis-`i` weight basis of the coefficients of a left-right pair of indices. -/
def pairCoeff (i : Fin 3) (κ α : Fin 2 × Fin 2) : ℂ :=
  weylCoeffC i κ.1 α.1 * weylCoeff i κ.2 α.2

/-- The standard basis of the coefficients written back in the axis-`i` weight basis. -/
noncomputable def pairCoeffInv (i : Fin 3) (α κ : Fin 2 × Fin 2) : ℂ :=
  weylCoeffInvC i α.1 κ.1 * weylCoeffInv i α.2 κ.2

/-- The pair weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_pairCoeffInv_mul (i : Fin 3) (α β : Fin 2 × Fin 2) :
    ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * pairCoeff i κ β
      = if α = β then 1 else 0 := by
  have hfac : (∑ κ₁, weylCoeffInvC i α.1 κ₁ * weylCoeffC i κ₁ β.1)
      * (∑ κ₂, weylCoeffInv i α.2 κ₂ * weylCoeff i κ₂ β.2)
      = ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * pairCoeff i κ β := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun κ₁ _ => Finset.sum_congr rfl fun κ₂ _ => by
      simp only [pairCoeff, pairCoeffInv]
      ring
  rw [← hfac, sum_weylCoeffInvC_mul, sum_weylCoeffInv_mul]
  obtain ⟨α₁, α₂⟩ := α
  obtain ⟨β₁, β₂⟩ := β
  by_cases h1 : α₁ = β₁ <;> by_cases h2 : α₂ = β₂ <;> simp [h1, h2, Prod.mk.injEq]

/-- The pair weight basis diagonalises the axis-`i` boost on coefficients, with the weight
  `pairWeight`. -/
lemma sum_boostAxis_pairCoeff (i : Fin 3) (κ l : Fin 2 × Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ a : Fin 2 × Fin 2, pairCoeff i κ a
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * star ((SL2C.boostAxis i t ht).1 a.2 l.2))
      = ((t : ℝ) : ℂ) ^ (pairWeight κ) * pairCoeff i κ l := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hfac : (∑ a₁, star ((SL2C.boostAxis i t ht).1 l.1 a₁) * weylCoeffC i κ.1 a₁)
      * (∑ a₂, (SL2C.boostAxis i t ht).1 l.2 a₂ * weylCoeff i κ.2 a₂)
      = ∑ a : Fin 2 × Fin 2, pairCoeff i κ a
        * ((SL2C.boostAxis i t ht).1 a.1 l.1
          * star ((SL2C.boostAxis i t ht).1 a.2 l.2)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
    simp only [pairCoeff, star_boostAxis_apply]
    ring
  rw [← hfac, sum_boostAxis_weylCoeffC i κ.1 l.1 ht, sum_boostAxis_weylCoeff i κ.2 l.2 ht,
    pairWeight, pairCoeff, zpow_add₀ htc]
  ring

/-!

## C. Left-right bispinors, their span, and coefficient functions

`IsLeftRightWeyl B repLorentz T` says the group moves the left index of `T^{α α'}` by the
matrix of `g` and the right index by its complex conjugate, and `hT.span` is the set of
combinations `∑ a, c a • T a` of the four components.

-/

/-- A family `T` indexed by one left-handed and one right-handed Weyl index, moved by
  `repLorentz` as a bispinor `T^{α α'}`. -/
structure IsLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      (g.1 a.1 l.1 * star (g.1 a.2 l.2)) • T a

namespace IsLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : Fin 2 × Fin 2 → B}
  (hT : IsLeftRightWeyl B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsLeftRightWeyl B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 2 × Fin 2 → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-- The action of `g : SL(2,ℂ)` on coefficient functions: the left slot moves by `g` and the
  right by its conjugate, with the free index first in each factor and the summed one second. -/
def act (g : SL(2,ℂ)) (c : Fin 2 × Fin 2 → ℂ) (a : Fin 2 × Fin 2) : ℂ :=
  ∑ d : Fin 2 × Fin 2, c d * (g.1 a.1 d.1 * star (g.1 a.2 d.2))

/-- A coefficient function fixed by every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : Fin 2 × Fin 2 → ℂ) : Prop := ∀ g : SL(2,ℂ), act g c = c

include hT in
/-- An invariant of the span is the contraction of an invariant coefficient function: the
  adjoint of the action of `g` is the action of `g†`. -/
theorem exists_isInvariantCoeff_of_mem_span {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : Fin 2 × Fin 2 → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d := by
  obtain ⟨c, hc, hx'⟩ := Invariants.exists_invariantCoeff_matrix T (fun g => repLorentz g)
    (fun g a d => g.1 a.1 d.1 * star (g.1 a.2 d.2)) hT.repLorentz_T
    (fun g => ⟨Invariants.dagger g, fun a d => by
      simp [Invariants.dagger, Matrix.conjTranspose_apply, mul_comm]⟩)
    (by rwa [← span]) hinv
  exact ⟨c, hc, hx'⟩

/-!

## D. The weight grading of the coefficients

The four products `pairCoeff i κ` of a left and a right weight covector read off the weight
components of a coefficient function, and the axis-`i` boost multiplies the component at `κ`
by `t ^ pairWeight κ`. An invariant function therefore has no component of weight `±2`, and is
recovered from its two weight-zero components alone.

-/

/-- The axis-`i` weight component of a coefficient function at the pair `κ`. -/
def weightComponent (i : Fin 3) (c : Fin 2 × Fin 2 → ℂ) (κ : Fin 2 × Fin 2) : ℂ :=
  ∑ a : Fin 2 × Fin 2, pairCoeff i κ a * c a

/-- The axis-`i` boost multiplies the weight component at `κ` by `t ^ pairWeight κ`. -/
lemma weightComponent_act_boostAxis (i : Fin 3) (c : Fin 2 × Fin 2 → ℂ)
    (κ : Fin 2 × Fin 2) {t : ℝ} (ht : t ≠ 0) :
    weightComponent i (act (SL2C.boostAxis i t ht) c) κ
      = ((t : ℝ) : ℂ) ^ (pairWeight κ) * weightComponent i c κ := by
  simp only [weightComponent, act, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  calc ∑ a : Fin 2 × Fin 2, pairCoeff i κ a * (c d * ((SL2C.boostAxis i t ht).1 a.1 d.1
        * star ((SL2C.boostAxis i t ht).1 a.2 d.2)))
      = c d * ∑ a : Fin 2 × Fin 2, pairCoeff i κ a * ((SL2C.boostAxis i t ht).1 a.1 d.1
          * star ((SL2C.boostAxis i t ht).1 a.2 d.2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by rw [sum_boostAxis_pairCoeff i κ d ht]; ring

/-- An invariant coefficient function has no weight component of nonzero weight. -/
lemma weightComponent_eq_zero {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c) (i : Fin 3)
    {κ : Fin 2 × Fin 2} (hκ : pairWeight κ ≠ 0) : weightComponent i c κ = 0 := by
  have h := weightComponent_act_boostAxis i c κ (two_ne_zero (α := ℝ))
  rw [hc] at h
  have h2 : ((2 : ℝ) : ℂ) ^ (pairWeight κ) ≠ 1 := by
    rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
      zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
    exact hκ
  exact (mul_left_eq_self₀.1 h.symm).resolve_left h2

/-- A coefficient function is recovered from its weight components. -/
lemma eq_sum_weightComponent (i : Fin 3) (c : Fin 2 × Fin 2 → ℂ) (α : Fin 2 × Fin 2) :
    c α = ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * weightComponent i c κ := by
  simp only [weightComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_pairCoeffInv_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-!

## E. The weight-zero round and its average over the axes

Keeping only the weight-zero components writes an invariant coefficient function as one matrix
per axis applied to itself, and the three average to a matrix with a short closed form.

-/

/-- The matrix of the axis-`i` weight-zero projection on coefficient functions. -/
noncomputable def weightZeroTransition (i : Fin 3) (α β : Fin 2 × Fin 2) : ℂ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0),
    pairCoeffInv i α κ * pairCoeff i κ β

/-- An invariant coefficient function is fixed by the axis-`i` weight-zero projection. -/
lemma eq_sum_weightZeroTransition {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c) (i : Fin 3)
    (α : Fin 2 × Fin 2) : c α = ∑ β, weightZeroTransition i α β * c β := by
  have hfil : ∀ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => ¬ pairWeight κ = 0),
      pairCoeffInv i α κ * weightComponent i c κ = 0 :=
    fun κ hκ => by rw [weightComponent_eq_zero hc i (Finset.mem_filter.1 hκ).2, mul_zero]
  rw [eq_sum_weightComponent i c α, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0), Finset.sum_eq_zero hfil, add_zero]
  simp only [weightComponent, weightZeroTransition, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

/-!

## F. The quadratic certificate and the classification

The summed transition `M` satisfies `M ^ 2 = 2 M`, while an invariant coefficient function
would have to satisfy `M c = 3 c`. Only `c = 0` does both.

-/

/-- The closed form of the summed weight-zero transition: twice the identity minus the
  outer product of the two diagonal indicators. -/
def transitionEntry (β α : Fin 2 × Fin 2) : ℂ :=
  2 * (if β.1 = α.1 then 1 else 0) * (if β.2 = α.2 then 1 else 0)
    - (if β.1 = β.2 then 1 else 0) * (if α.1 = α.2 then 1 else 0)

/-- The sum over the three axes of the weight-zero transitions has the closed form
  `transitionEntry`. -/
lemma sum_weightZeroTransition_eq (β α : Fin 2 × Fin 2) :
    ∑ i : Fin 3, weightZeroTransition i β α = transitionEntry β α := by
  simp only [weightZeroTransition, sum_weightZeroFilter, Fin.sum_univ_three]
  obtain ⟨β₁, β₂⟩ := β
  obtain ⟨α₁, α₂⟩ := α
  fin_cases β₁ <;> fin_cases β₂ <;> fin_cases α₁ <;> fin_cases α₂ <;>
    simp [transitionEntry, pairCoeff, pairCoeffInv, weylCoeff, weylCoeffC,
      weylCoeffInv, weylCoeffInvC] <;>
    norm_num [Complex.ext_iff]

/-- The action of the summed transition matrix on a coefficient vector. -/
noncomputable def applyTransition (c : Fin 2 × Fin 2 → ℂ) (β : Fin 2 × Fin 2) : ℂ :=
  ∑ α, transitionEntry β α * c α

/-- The action of the summed transition matrix is homogeneous. -/
lemma applyTransition_const_mul (k : ℂ) (c : Fin 2 × Fin 2 → ℂ) (β : Fin 2 × Fin 2) :
    applyTransition (fun γ => k * c γ) β = k * applyTransition c β := by
  simp only [applyTransition, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- The summed transition matrix squares to twice itself. -/
lemma sum_transitionEntry_mul (β α : Fin 2 × Fin 2) :
    ∑ γ : Fin 2 × Fin 2, transitionEntry β γ * transitionEntry γ α
      = 2 * transitionEntry β α := by
  obtain ⟨β₁, β₂⟩ := β
  obtain ⟨α₁, α₂⟩ := α
  fin_cases β₁ <;> fin_cases β₂ <;> fin_cases α₁ <;> fin_cases α₂ <;>
    simp [transitionEntry, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

/-- Two rounds of the summed transition are twice one round. -/
lemma applyTransition_applyTransition (c : Fin 2 × Fin 2 → ℂ) (β : Fin 2 × Fin 2) :
    applyTransition (applyTransition c) β = 2 * applyTransition c β := by
  calc applyTransition (applyTransition c) β
      = ∑ α, (∑ γ, transitionEntry β γ * transitionEntry γ α) * c α := by
        simp only [applyTransition, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun γ _ => (mul_assoc _ _ _).symm
    _ = ∑ α, (2 * transitionEntry β α) * c α :=
        Finset.sum_congr rfl fun α _ => by rw [sum_transitionEntry_mul]
    _ = 2 * applyTransition c β := by
        simp only [applyTransition, Finset.mul_sum]
        exact Finset.sum_congr rfl fun α _ => by ring

/-- An invariant coefficient function is `3` times its averaged round, so it is an eigenvector
  of the summed transition for the eigenvalue `3`. -/
lemma applyTransition_eq_three_smul {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c)
    (β : Fin 2 × Fin 2) : applyTransition c β = 3 * c β := by
  have h3 : ∑ i : Fin 3, ∑ α, weightZeroTransition i β α * c α = 3 * c β := by
    rw [Fin.sum_univ_three, ← eq_sum_weightZeroTransition hc 0 β,
      ← eq_sum_weightZeroTransition hc 1 β, ← eq_sum_weightZeroTransition hc 2 β]
    ring
  rw [← h3, applyTransition, Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ => by rw [← Finset.sum_mul, sum_weightZeroTransition_eq]

/-- An invariant coefficient function is zero: `3` is not an eigenvalue of a matrix squaring
  to twice itself unless the eigenvector is. -/
lemma eq_zero_of_isInvariantCoeff {c : Fin 2 × Fin 2 → ℂ} (hc : IsInvariantCoeff c) : c = 0 := by
  funext β
  show c β = 0
  have h9 : applyTransition (applyTransition c) β = 9 * c β := by
    rw [show applyTransition c = fun γ => 3 * c γ from
      funext fun γ => applyTransition_eq_three_smul hc γ, applyTransition_const_mul,
      applyTransition_eq_three_smul hc]
    ring
  have h6 : applyTransition (applyTransition c) β = 6 * c β := by
    rw [applyTransition_applyTransition, applyTransition_eq_three_smul hc]
    ring
  rw [h9] at h6
  linear_combination h6 / 3

include hT in
/-- Every Lorentz invariant in the span of the components is zero: the pair of indices carries
  the four-vector representation, which has no invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_span hx hinv
  simp [eq_zero_of_isInvariantCoeff hc]

/-!

## G. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a bispinor, so the
classification applies there and lifts back with an error term in `S`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a left-right bispinor. -/
lemma isLeftRightWeyl_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsLeftRightWeyl (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

include hT in
/-- A Lorentz invariant of `hT.span ⊔ S`, for a Lorentz-stable subspace `S`, already lies
  in `S`. -/
lemma mem_of_invariant_of_mem_sup {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT' := hT.isLeftRightWeyl_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  have hzero := hT'.eq_zero_of_invariant hmk hinv'
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end IsLeftRightWeyl

end Lorentz
