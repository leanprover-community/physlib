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

The proof follows the four-vector one with the light-cone basis replaced by Weyl weight
bases. Along a spatial axis the `SL(2,ℂ)` boost is the diagonal `z`-boost conjugated by
`rotationZToAxis i`, so the columns of that rotation are boost eigenvectors of weight
`±1` (A), and the four products of a left and a right eigenvector carry weights `2`, `0`,
`0`, `-2` (B). An invariant has weight `0` along every axis, so it is fixed by the
weight-zero projection along each (D); averaging the three gives a matrix `M` with
`M ^ 2 = 2 M` and no eigenvalue `3` (E), so `3 λ ^ 2 - 2 λ` at `λ = M / 3` annihilates
every invariant (F). Section G divides out `S`.

A family carrying dual Weyl indices transforms by the contragredient `(Λ⁻¹)ᵀ` on the
undotted slot and by `(Λ⁻¹)ᴴ` on the dotted one. That law is `IsDualLeftRightWeyl` here;
its classification, still that there is no invariant, hence no Dirac mass term, is in
`IsVectorLeftRightWeyl`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

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

## B. The weight basis of a left-right pair

The two indices are graded independently, so the weight basis of the pair is the tensor
product of the two, and its weight is the sum of the two Weyl weights.

-/

/-- The boost weight of a pair of Weyl weight indices: the sum of the two. -/
def pairWeight (κ : Fin 2 × Fin 2) : ℤ := weylWeight κ.1 + weylWeight κ.2

/-- The pair weight takes the values `-2`, `0` and `2`. -/
lemma pairWeight_mem (κ : Fin 2 × Fin 2) : pairWeight κ ∈ ({-2, 0, 2} : Finset ℤ) := by
  revert κ
  decide

/-- The weight-zero pairs are the two mixed pairs. -/
lemma sum_weightZeroFilter {M : Type*} [AddCommMonoid M] (f : Fin 2 × Fin 2 → M) :
    ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0), f κ
      = f (0, 1) + f (1, 0) := by
  rw [show (Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0))
      = {(0, 1), (1, 0)} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- The axis-`i` weight basis of a left-right pair of indices. -/
def pairCoeff (i : Fin 3) (κ α : Fin 2 × Fin 2) : ℂ :=
  weylCoeff i κ.1 α.1 * weylCoeffC i κ.2 α.2

/-- The standard basis of a left-right pair written back in the axis-`i` weight
  basis. -/
noncomputable def pairCoeffInv (i : Fin 3) (α κ : Fin 2 × Fin 2) : ℂ :=
  weylCoeffInv i α.1 κ.1 * weylCoeffInvC i α.2 κ.2

/-- The pair weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_pairCoeffInv_mul (i : Fin 3) (α β : Fin 2 × Fin 2) :
    ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * pairCoeff i κ β
      = if α = β then 1 else 0 := by
  have hfac : (∑ κ₁, weylCoeffInv i α.1 κ₁ * weylCoeff i κ₁ β.1)
      * (∑ κ₂, weylCoeffInvC i α.2 κ₂ * weylCoeffC i κ₂ β.2)
      = ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * pairCoeff i κ β := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun κ₁ _ => Finset.sum_congr rfl fun κ₂ _ => by
      simp only [pairCoeff, pairCoeffInv]
      ring
  rw [← hfac, sum_weylCoeffInv_mul, sum_weylCoeffInvC_mul]
  obtain ⟨α₁, α₂⟩ := α
  obtain ⟨β₁, β₂⟩ := β
  by_cases h1 : α₁ = β₁ <;> by_cases h2 : α₂ = β₂ <;> simp [h1, h2, Prod.mk.injEq]

/-- The pair weight basis diagonalises the axis-`i` boost, with the weight
  `pairWeight`. -/
lemma sum_boostAxis_pairCoeff (i : Fin 3) (κ a : Fin 2 × Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ l : Fin 2 × Fin 2, pairCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * star ((SL2C.boostAxis i t ht).1 a.2 l.2))
      = ((t : ℝ) : ℂ) ^ (pairWeight κ) * pairCoeff i κ a := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hfac : (∑ l₁, (SL2C.boostAxis i t ht).1 a.1 l₁ * weylCoeff i κ.1 l₁)
      * (∑ l₂, star ((SL2C.boostAxis i t ht).1 a.2 l₂) * weylCoeffC i κ.2 l₂)
      = ∑ l : Fin 2 × Fin 2, pairCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1
          * star ((SL2C.boostAxis i t ht).1 a.2 l.2)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => by
      simp only [pairCoeff]
      ring
  rw [← hfac, sum_boostAxis_weylCoeff i κ.1 a.1 ht, sum_boostAxis_weylCoeffC i κ.2 a.2 ht,
    pairWeight, pairCoeff, zpow_add₀ htc]
  ring

/-!

## C. Left-right bispinors and the span of their components

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

/-!

## D. The weight grading of the span

The four products `weightVec i κ` of a left and a right weight vector span the same space
as the components and are boost eigenvectors along the axis `i`, of weights `2`, `0`, `0`
and `-2`.

-/

set_option linter.unusedVariables false in
/-- The weight component of `T` along axis `i` at the pair `κ` of Weyl weight indices;
  `hT` is present only so it reads `hT.weightVec`. -/
noncomputable def weightVec (hT : IsLeftRightWeyl B repLorentz T) (i : Fin 3)
    (κ : Fin 2 × Fin 2) : B :=
  ∑ a : Fin 2 × Fin 2, pairCoeff i κ a • T a

/-- Each weight component lies in the span of the components. -/
lemma weightVec_mem_span (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ hT.span :=
  sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the weight components along any axis. -/
lemma eq_sum_weightVec (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ • hT.weightVec i κ := by
  calc T α = ∑ β : Fin 2 × Fin 2,
        (∑ κ : Fin 2 × Fin 2, pairCoeffInv i α κ * pairCoeff i κ β) • T β := by
        simp only [sum_pairCoeffInv_mul, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [weightVec, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The weight components along any axis span the same space as the components. -/
lemma span_eq_weightVec (hT : IsLeftRightWeyl B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ κ, ℂ ∙ hT.weightVec i κ := by
  rw [span]
  refine le_antisymm (iSup_le fun α => ?_) (iSup_le fun κ => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_weightVec i α]
    exact sum_mem fun κ _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem κ (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.weightVec_mem_span i κ

/-- The weight components are boost eigenvectors: along axis `i` the component at `κ`
  has boost weight `pairWeight κ`. -/
lemma weightVec_mem_boostWeightSubmodule (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ boostWeightSubmodule repLorentz i (pairWeight κ) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ l : Fin 2 × Fin 2,
      pairCoeff i κ l • repLorentz (SL2C.boostAxis i t ht) (T l)
        = ∑ a : Fin 2 × Fin 2, (pairCoeff i κ l
            * ((SL2C.boostAxis i t ht).1 a.1 l.1
              * star ((SL2C.boostAxis i t ht).1 a.2 l.2))) • T a := by
    intro l
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.weightVec i κ)
      = ∑ l : Fin 2 × Fin 2, pairCoeff i κ l
          • repLorentz (SL2C.boostAxis i t ht) (T l) := by
        simp only [weightVec, map_sum, map_smul]
    _ = ∑ a : Fin 2 × Fin 2, (∑ l : Fin 2 × Fin 2, pairCoeff i κ l
          * ((SL2C.boostAxis i t ht).1 a.1 l.1
            * star ((SL2C.boostAxis i t ht).1 a.2 l.2))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 2 × Fin 2,
          (((t : ℝ) : ℂ) ^ (pairWeight κ) * pairCoeff i κ a) • T a :=
        Finset.sum_congr rfl fun a _ => by rw [sum_boostAxis_pairCoeff i κ a ht]
    _ = (algebraMap ℝ ℂ) t ^ (pairWeight κ) • hT.weightVec i κ := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, weightVec, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-- The axis-`i` weight-`m` component of the generator `T α`: the weight-`m` partial sum
  of `eq_sum_weightVec`. -/
noncomputable def monoComponent (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) : B :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = m),
    pairCoeffInv i α κ • hT.weightVec i κ

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) :
    hT.monoComponent i α m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun κ hκ => Submodule.smul_mem _ _ ?_
  exact (show pairWeight κ = m from (Finset.mem_filter.1 hκ).2) ▸
    hT.weightVec_mem_boostWeightSubmodule i κ

/-- A component is the sum of its weight components over the three possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m := by
  rw [hT.eq_sum_weightVec i α]
  exact (Finset.sum_fiberwise_of_maps_to (fun κ _ => pairWeight_mem κ) _).symm

/-!

## E. The weight-zero round and its average over the axes

An invariant has boost weight zero along every axis, so along each axis it equals its own
weight-zero part, which written back on the components is the matrix
`weightZeroTransition i`.

-/

/-- The matrix of the axis-`i` weight-zero projection in the `T`-basis: the coefficient
  of `T β` in the re-expansion of `monoComponent i α 0` through the weight basis. -/
noncomputable def weightZeroTransition (i : Fin 3) (β α : Fin 2 × Fin 2) : ℂ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0),
    pairCoeffInv i α κ * pairCoeff i κ β

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i α 0` is the
  `α`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (α : Fin 2 × Fin 2) :
    hT.monoComponent i α 0
      = ∑ β : Fin 2 × Fin 2, weightZeroTransition i β α • T β := by
  rw [monoComponent]
  simp only [weightVec, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_smul, weightZeroTransition]

include hT in
/-- A vector of boost weight zero along axis `i` is written with the weight-zero transition
  applied to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : Fin 2 × Fin 2 → ℂ) (hx : x = ∑ α, c α • T α)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
  have hsum : x = ∑ m ∈ ({-2, 0, 2} : Finset ℤ),
      ∑ α, c α • hT.monoComponent i α m := by
    rw [hx]
    calc ∑ α, c α • T α
        = ∑ α, c α • ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m :=
          Finset.sum_congr rfl fun α _ => by rw [← hT.eq_sum_monoComponent_univ i α]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ α, c α • hT.monoComponent i α 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ α, c α • hT.monoComponent i α m) hw
      (fun m _ => sum_mem fun α _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i α m))
      (by decide) hsum
  calc x = ∑ α, c α • hT.monoComponent i α 0 := hx0
    _ = ∑ α, c α • ∑ β, weightZeroTransition i β α • T β :=
        Finset.sum_congr rfl fun α _ => by rw [hT.monoComponent_zero_eq i α]
    _ = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul]
        exact congrArg (· • T β) (Finset.sum_congr rfl fun α _ => mul_comm _ _)

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

include hT in
/-- A vector of boost weight zero along all three axes is written with a third of the summed
  transition applied to its coefficients. -/
lemma eq_sum_transitionEntry_smul {x : B} (c : Fin 2 × Fin 2 → ℂ)
    (hx : x = ∑ α, c α • T α)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
  have hround : ∀ i : Fin 3,
      x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3 : ℂ)⁻¹ • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, x := by rw [h3]
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, ∑ β,
          (∑ α, weightZeroTransition i β α * c α) • T β :=
        congrArg (fun y => (3 : ℂ)⁻¹ • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [show (∑ i : Fin 3, ∑ α, weightZeroTransition i β α * c α)
            = ∑ α, transitionEntry β α * c α from by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun α _ => by
            rw [← Finset.sum_mul, sum_weightZeroTransition_eq]]

/-!

## F. The quadratic certificate and the classification

The summed transition `M` satisfies `M ^ 2 = 2 M`, so `M / 3` has eigenvalues `2/3` and
`0`, never the `1` an invariant would need: `3 λ ^ 2 - 2 λ` annihilates every invariant.

-/

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

include hT in
/-- Every Lorentz invariant in the span of the components is zero: the pair of indices carries
  the four-vector representation, which has no invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h1 := hT.eq_sum_transitionEntry_smul c hc hw
  have h2 := hT.eq_sum_transitionEntry_smul
    (fun β => (3 : ℂ)⁻¹ * applyTransition c β) h1 hw
  have h2' : x = ∑ β, ((9 : ℂ)⁻¹ * (2 * applyTransition c β)) • T β := by
    rw [h2]
    refine Finset.sum_congr rfl fun β _ => ?_
    congr 1
    rw [show (∑ α, transitionEntry β α * ((3 : ℂ)⁻¹ * applyTransition c α))
      = applyTransition (fun γ => (3 : ℂ)⁻¹ * applyTransition c γ) β from rfl,
      applyTransition_const_mul, applyTransition_applyTransition]
    ring
  have h1' : x = ∑ β, ((3 : ℂ)⁻¹ * applyTransition c β) • T β := h1
  calc x = (3 : ℂ) • x - (2 : ℂ) • x := by module
    _ = ∑ β, ((3 : ℂ) * ((9 : ℂ)⁻¹ * (2 * applyTransition c β))
        - (2 : ℂ) * ((3 : ℂ)⁻¹ * applyTransition c β)) • T β := by
        nth_rewrite 1 [h2']
        nth_rewrite 1 [h1']
        simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun β _ => ?_
        rw [show (3 : ℂ) * ((9 : ℂ)⁻¹ * (2 * applyTransition c β))
          - (2 : ℂ) * ((3 : ℂ)⁻¹ * applyTransition c β) = 0 from by ring, zero_smul]

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
