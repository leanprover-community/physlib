/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants among two four-vector indices

A rank-two tensor `T^{μν}` has `16` components, and exactly one combination of them is
fixed by every rotation and boost, the metric trace

`metricContraction = η_{μν} T^{μν}`.

Every other invariant is a multiple of it: nothing else ties two indices, the Levi-Civita
symbol needing four. That is `exists_smul_metricContraction_of_invariant`, and
`exists_smul_metricContraction_of_invariant_subset` is the same statement modulo a
Lorentz-stable subspace `S`, the form the Standard Model files use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by two directions, and `IsBiLorentz` says the group
moves them with one factor of the Lorentz matrix per slot (A). `hT.span` is the set of
their combinations.

An invariant of the span is `∑_d c_d • T d` for a coefficient tensor `c` that the Lorentz
matrices themselves fix (A, from `Invariants.Basic`), and the rest is the two-index case of the
argument in `IsQuadLorentz`, reusing its light-cone coefficients and sector matrices. Along a
spatial axis the four light-cone directions carry boost weights `2`, `-2`, `0`, `0`, and an
invariant `c` has no light-cone component of nonzero weight, so it is fixed by the weight-zero
projection along each axis (B); averaging the three gives one linear map on the `16`
coefficients, `12` times an integer matrix with a short closed form (C, D). Its eigenvalues are
`12`, `10`, `4`, `0`, with `12` simple, so the cubic `λ (λ - 4) (λ - 10)` sends everything onto
that one eigenvector, which is the metric (E). Section F draws the conclusion and G divides
out `S`.

No rotation averaging is needed here, unlike the four-index case: for two indices the
three weight-zero conditions already cut the `16` components down to a single line.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants
open IsQuadLorentz (lightConeCoeffZ coe_lightConeCoeffZ lightConeCoeffInvQ
  coe_lightConeCoeffInvQ lightConeCoeffInvZ coe_lightConeCoeffInvZ sectorIndex sectorWeight
  lightConeWeight_eq_sectorWeight slotTransition slotTransitionZ slotTransitionZ_eq_sum quotRep
  quotRep_mkQ)

/-!

## A. Bi-Lorentz tensors and the span of their components

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes, and an index
vector puts one in each of the two slots, so `T d` is `T^{μν}` at `(μ, ν) = d`.
`IsBiLorentz B repLorentz T` says the group moves the components with one factor of the
Lorentz matrix per slot, and `hT.span` is the set of combinations `∑ d, c d • T d`.

-/

/-- A family `T` of elements of `B`, indexed by two four-vector indices, transforms as
  a tensor `T^{μ₁ μ₂}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsBiLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 2 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 2), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsBiLorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 2 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsBiLorentz B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsBiLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]


include hT in
/-- An invariant of the span is the contraction of an invariant coefficient tensor. -/
theorem exists_isInvariantCoeff_of_mem_span {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d :=
  Invariants.exists_isInvariantCoeff_of_mem_span hT.repLorentz_T hx hinv

/-!

## B. The weight-zero transition along one axis

An invariant coefficient tensor keeps only its light-cone components of total weight zero, so
writing it back on the coefficients it is fixed by one matrix per axis: a sum over the sector
patterns of total weight zero of the per-slot sector matrices of `IsQuadLorentz`.

-/

/-- The weight-zero projection along axis `i`, as a matrix on the components: the sum over the
  three sector patterns of weight zero of the products of the two per-slot sector matrices. -/
def weightZeroTransition (i : Fin 3) (d e : Fin 2 → Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ w ∈ Finset.univ.filter (fun w : Fin 2 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
    ∏ s, slotTransition i (w s) (e s) (d s)

/-- A weight-zero light-cone sum over two slots regroups as a sum over sector patterns of
  weight zero of the products of the slotwise sector sums. -/
lemma sum_weightZero_eq_sum_sector {R : Type*} [CommSemiring R] (f : Fin 2 → Fin 4 → R) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, f s (c s)
      = ∑ w ∈ Finset.univ.filter (fun w : Fin 2 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
          ∏ s, ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = w s),
            f s κ' := by
  have hmaps : ∀ c ∈ Finset.univ.filter
      (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
      (fun s => sectorIndex (c s)) ∈ Finset.univ.filter
        (fun w : Fin 2 → Fin 3 => (∑ s, sectorWeight (w s)) = 0) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc]
    exact (Finset.sum_congr rfl fun s _ => lightConeWeight_eq_sectorWeight (c s)).symm
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw0 : (∑ s, sectorWeight (w s)) = 0 := (Finset.mem_filter.1 hw).2
  have hfiber : (Finset.univ.filter
        (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0)).filter
      (fun c => (fun s => sectorIndex (c s)) = w)
      = Fintype.piFinset
          (fun s => Finset.univ.filter (fun κ : Fin 4 => sectorIndex κ = w s)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      funext_iff]
    constructor
    · rintro ⟨-, hcw⟩ s
      exact hcw s
    · intro hcw
      refine ⟨?_, hcw⟩
      rw [show (∑ s, lightConeWeight (c s)) = ∑ s, sectorWeight (w s) from
        Finset.sum_congr rfl fun s _ => by rw [lightConeWeight_eq_sectorWeight, hcw s]]
      exact hw0
  rw [hfiber]
  exact (Finset.prod_univ_sum
    (fun s => Finset.univ.filter fun κ' : Fin 4 => sectorIndex κ' = w s)
    (fun s κ' => f s κ')).symm

/-- The weight-zero transition as a light-cone sum: the sector convolution expands to
  the sum over weight-zero light-cone monomials of the composite slot coefficients. -/
lemma weightZeroTransition_eq_sum_lightCone (i : Fin 3) (d e : Fin 2 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition i d e
      = ∑ c ∈ Finset.univ.filter
          (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ) := by
  rw [weightZeroTransition]
  exact (sum_weightZero_eq_sum_sector
    (fun s κ => lightConeCoeffInvQ i (e s) κ * (lightConeCoeffZ i κ (d s) : ℚ))).symm

/-- An invariant coefficient tensor is fixed by the axis-`i` weight-zero transition. -/
lemma eq_sum_weightZeroTransition {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    c d = ∑ e, ((weightZeroTransition i e d : ℚ) : ℂ) * c e := by
  have hfil : ∀ κ ∈ Finset.univ.filter
      (fun κ : Fin 2 → Fin 4 => ¬ (∑ s, lightConeWeight (κ s)) = 0),
      (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ = 0 :=
    fun κ hκ => by
      rw [hc.lightConeComponent_eq_zero i (Finset.mem_filter.1 hκ).2, mul_zero]
  rw [eq_sum_lightConeComponent i c d, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun κ : Fin 2 → Fin 4 => (∑ s, lightConeWeight (κ s)) = 0), Finset.sum_eq_zero hfil,
    add_zero]
  calc ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 → Fin 4 => (∑ s, lightConeWeight (κ s)) = 0),
        (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ
      = ∑ e, (∑ κ ∈ Finset.univ.filter
          (fun κ : Fin 2 → Fin 4 => (∑ s, lightConeWeight (κ s)) = 0),
          ∏ s, lightConeCoeffInv i (d s) (κ s) * lightConeCoeff i (κ s) (e s)) * c e := by
        simp only [lightConeComponent, Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun κ _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun e _ => ?_
        congr 1
        rw [weightZeroTransition_eq_sum_lightCone]
        push_cast
        simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ]

/-!

## C. The average over the axes

An invariant coefficient tensor is fixed by each of the three weight-zero transitions, hence
by their average.

-/

/-- The average `M` of the three weight-zero transitions, as a matrix on the components. Its
  powers drive the endgame. -/
def boostAverageTransition :
    Matrix (Fin 2 → Fin 1 ⊕ Fin 3) (Fin 2 → Fin 1 ⊕ Fin 3) ℚ :=
  Matrix.of fun d e => (3⁻¹ : ℚ) * ∑ i : Fin 3, weightZeroTransition i d e

/-- An invariant coefficient tensor is fixed by the average of the three transitions. -/
lemma eq_sum_boostAverageTransition {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    c d = ∑ e, ((boostAverageTransition e d : ℚ) : ℂ) * c e := by
  have h3 : (3 : ℂ) * c d = ∑ i : Fin 3, ∑ e, ((weightZeroTransition i e d : ℚ) : ℂ) * c e := by
    rw [Fin.sum_univ_three, ← eq_sum_weightZeroTransition hc 0 d,
      ← eq_sum_weightZeroTransition hc 1 d, ← eq_sum_weightZeroTransition hc 2 d]
    ring
  rw [show (∑ e, ((boostAverageTransition e d : ℚ) : ℂ) * c e)
      = (3 : ℂ)⁻¹ * ∑ i : Fin 3, ∑ e, ((weightZeroTransition i e d : ℚ) : ℂ) * c e from by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [boostAverageTransition, Matrix.of_apply]
    push_cast
    rw [mul_assoc, Finset.sum_mul], ← h3]
  ring

/-!

## D. The average as an integer matrix

Twelve times the average is an integer matrix on the `16` components, with a short closed
form that the kernel can evaluate cheaply.

-/

/-- Integer mirror of the weight-zero transition: four times its value, as the
  balanced-sector convolution of the integer slot matrices of `IsQuadLorentz`. -/
def weightZeroTransitionZ (i : Fin 3) (d e : Fin 2 → Fin 1 ⊕ Fin 3) : ℤ :=
  ∑ w ∈ Finset.univ.filter (fun w : Fin 2 → Fin 3 => (∑ s, sectorWeight (w s)) = 0),
    ∏ s, slotTransitionZ i (w s) (e s) (d s)

/-- The integer weight-zero transition as a light-cone sum. -/
lemma weightZeroTransitionZ_eq_sum_lightCone (i : Fin 3) (d e : Fin 2 → Fin 1 ⊕ Fin 3) :
    weightZeroTransitionZ i d e
      = ∑ c ∈ Finset.univ.filter
          (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
        ∏ s, lightConeCoeffInvZ i (e s) (c s) * lightConeCoeffZ i (c s) (d s) := by
  rw [weightZeroTransitionZ]
  simp only [slotTransitionZ_eq_sum]
  exact (sum_weightZero_eq_sum_sector
    (fun s κ => lightConeCoeffInvZ i (e s) κ * lightConeCoeffZ i κ (d s))).symm

/-- The integer mirror casts to four times the weight-zero transition. -/
lemma coe_weightZeroTransitionZ (i : Fin 3) (d e : Fin 2 → Fin 1 ⊕ Fin 3) :
    ((weightZeroTransitionZ i d e : ℤ) : ℚ) = 4 * weightZeroTransition i d e := by
  rw [weightZeroTransitionZ_eq_sum_lightCone, weightZeroTransition_eq_sum_lightCone]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc ∏ s, ((lightConeCoeffInvZ i (e s) (c s) : ℤ) : ℚ)
        * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)
      = ∏ s, 2 * (lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [coe_lightConeCoeffInvZ]
        ring
    _ = 4 * ∏ s, lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        norm_num [Finset.card_univ]

/-- Twelve times the boost average, as an integer matrix on the sixteen components. -/
def boostAverageZ : Matrix (Fin 2 → Fin 1 ⊕ Fin 3) (Fin 2 → Fin 1 ⊕ Fin 3) ℤ :=
  Matrix.of fun d e => ∑ i : Fin 3, weightZeroTransitionZ i d e

/-- The integer mirror casts to twelve times the boost average. -/
lemma coe_boostAverageZ (d e : Fin 2 → Fin 1 ⊕ Fin 3) :
    ((boostAverageZ d e : ℤ) : ℚ) = 12 * boostAverageTransition d e := by
  rw [boostAverageZ, boostAverageTransition, Matrix.of_apply, Matrix.of_apply]
  push_cast
  simp only [coe_weightZeroTransitionZ]
  rw [← Finset.mul_sum]
  ring

/-- The closed form of the integer average. A pair of equal indices talks only to such pairs,
  with time-time `6`, mixed time-space `-2` and space-space diagonal `10`; a pair with one
  time index carries `2` on itself and `-2` on its transpose; a pair of distinct space
  indices carries `4` on itself. -/
def boostAverageEntry (d e : Fin 2 → Fin 1 ⊕ Fin 3) : ℤ :=
  if d 0 = d 1 then
    (if e 0 = e 1 then
      (if d 0 = Sum.inl 0 then (if e 0 = Sum.inl 0 then 6 else -2)
        else if e 0 = Sum.inl 0 then -2 else if d 0 = e 0 then 10 else 0)
      else 0)
  else if d 0 = Sum.inl 0 ∨ d 1 = Sum.inl 0 then
    (if e 0 = d 0 ∧ e 1 = d 1 then 2 else if e 0 = d 1 ∧ e 1 = d 0 then -2 else 0)
  else (if e 0 = d 0 ∧ e 1 = d 1 then 4 else 0)

/-- Entrywise decidability for integer matrices; instance search does not see through the
  `Matrix` synonym when both indices are bound. -/
private instance decidableForallEntriesZ {ι : Type*} [Fintype ι] (f g : Matrix ι ι ℤ) :
    Decidable (∀ k l, f k l = g k l) :=
  @Fintype.decidableForallFintype ι _
    (fun _ => @Fintype.decidableForallFintype ι _ (fun _ => Int.instDecidableEq _ _) _) _

/-- The integer averaged round agrees with its closed form. -/
lemma boostAverageZ_eq : boostAverageZ = Matrix.of boostAverageEntry := by
  ext d e
  revert d e
  decide +kernel

/-!

## E. The certificate polynomial and the trace projector

The average has eigenvalues `12`, `10`, `4` and `0` on the `16` components, with the
invariant eigenvalue `12` simple, so the cubic `λ (λ - 4) (λ - 10)` sends the matrix to a
rank-one one, the outer square of the metric. That identity is the certificate, checked
entry by entry.

-/

/-- The certificate polynomial applied to the integer averaged round. -/
def Q : Matrix (Fin 2 → Fin 1 ⊕ Fin 3) (Fin 2 → Fin 1 ⊕ Fin 3) ℤ :=
  boostAverageZ * (boostAverageZ - 4) * (boostAverageZ - 10)

/-- The closed form of `M (M - 4)`: supported on the pairs of equal indices, where it is a
  multiple of the metric outer square minus a multiple of the identity on the space block. -/
def boostAverageSqEntry (d e : Fin 2 → Fin 1 ⊕ Fin 3) : ℤ :=
  if d 0 = d 1 ∧ e 0 = e 1 then
    (if d 0 = Sum.inl 0 then (if e 0 = Sum.inl 0 then 24 else -24)
      else if e 0 = Sum.inl 0 then -24 else if d 0 = e 0 then 64 else 4)
  else 0

set_option maxRecDepth 20000 in
/-- The certificate: the cubic at the integer average is `48` times the outer square of the
  metric. Checked through a materialised intermediate product, so each kernel step is one
  multiplication of matrices with cheap entries. -/
lemma Q_explicit :
    Q = Matrix.of fun d e : Fin 2 → Fin 1 ⊕ Fin 3 =>
      48 * (minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (e 0) (e 1)) := by
  have h1 : boostAverageZ * (boostAverageZ - 4) = Matrix.of boostAverageSqEntry := by
    rw [boostAverageZ_eq]
    ext a b
    revert a b
    decide +kernel
  rw [Q, h1, boostAverageZ_eq]
  ext a b
  revert a b
  decide +kernel

/-- The certificate polynomial expanded into powers. -/
lemma Q_eq_poly : Q = boostAverageZ ^ 3 - (14 : ℤ) • boostAverageZ ^ 2
    + (40 : ℤ) • boostAverageZ := by
  rw [Q]
  noncomm_ring

/-- The integer averaged round is a symmetric matrix, a finite check. -/
lemma boostAverageZ_transpose : boostAverageZᵀ = boostAverageZ := by
  rw [boostAverageZ_eq]
  ext d e
  revert d e
  decide +kernel

/-- The same read on a pair of entries. -/
lemma boostAverageZ_symm (d e : Fin 2 → Fin 1 ⊕ Fin 3) :
    boostAverageZ d e = boostAverageZ e d := by
  have h := congrFun (congrFun boostAverageZ_transpose e) d
  rwa [Matrix.transpose_apply] at h

/-!

## F. The classification of the Lorentz invariants

## F.1. The metric contraction

-/

/-- The metric contraction `g^{μν} T_{μν}`, the only invariant contraction of two
  four-vector indices. -/
noncomputable def metricContraction : B :=
  ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d

/-!

## F.2. Iterating the averaged round on the coefficients

-/

/-- An invariant coefficient tensor is fixed by the integer averaged round, up to `12`. -/
lemma twelve_mul_eq_sum_boostAverageZ {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    (12 : ℂ) * c d = ∑ e, ((boostAverageZ d e : ℤ) : ℂ) * c e := by
  rw [show (12 : ℂ) * c d = ∑ e, (12 : ℂ) * (((boostAverageTransition e d : ℚ) : ℂ) * c e) from by
    rw [← Finset.mul_sum, ← eq_sum_boostAverageTransition hc]]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hb := congrArg (fun q : ℚ => (q : ℂ)) (coe_boostAverageZ e d)
  push_cast at hb
  rw [boostAverageZ_symm d e, hb]
  ring

/-- The same for `n` rounds: the `n`-th power of the integer matrix, up to `12 ^ n`. -/
lemma pow_mul_eq_sum_pow_boostAverageZ {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (n : ℕ) (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    ((12 : ℂ) ^ n) * c d = ∑ e, (((boostAverageZ ^ n) d e : ℤ) : ℂ) * c e := by
  induction n generalizing d with
  | zero => simp [Matrix.one_apply, apply_ite (fun q : ℤ => (q : ℂ)), ite_mul, Finset.sum_ite_eq]
  | succ n ih =>
    calc ((12 : ℂ) ^ (n + 1)) * c d
        = (12 : ℂ) ^ n * ((12 : ℂ) * c d) := by ring
      _ = ∑ f, ((boostAverageZ d f : ℤ) : ℂ) * ((12 : ℂ) ^ n * c f) := by
          rw [twelve_mul_eq_sum_boostAverageZ hc, Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => by ring
      _ = ∑ e, (((boostAverageZ ^ (n + 1)) d e : ℤ) : ℂ) * c e := by
          simp only [ih, Finset.mul_sum, pow_succ' boostAverageZ n, Matrix.mul_apply]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          push_cast
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun f _ => by ring

/-!

## F.3. The certificate round

-/

/-- The certificate applied to an invariant coefficient tensor: `192 c = 48 η (η ⬝ c)`, so
  every invariant coefficient tensor is a multiple of the metric. -/
lemma eq_smul_minkowskiMatrixZ {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    c d = ((4 : ℂ)⁻¹ * ∑ e, ((minkowskiMatrixZ (e 0) (e 1) : ℤ) : ℂ) * c e)
      * ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) := by
  have hQ : ∑ e, ((Q d e : ℤ) : ℂ) * c e = (192 : ℂ) * c d := by
    have h1 := pow_mul_eq_sum_pow_boostAverageZ hc 1 d
    have h2 := pow_mul_eq_sum_pow_boostAverageZ hc 2 d
    have h3 := pow_mul_eq_sum_pow_boostAverageZ hc 3 d
    simp only [pow_one] at h1
    rw [show (∑ e, ((Q d e : ℤ) : ℂ) * c e)
        = (∑ e, (((boostAverageZ ^ 3) d e : ℤ) : ℂ) * c e)
          - 14 * (∑ e, (((boostAverageZ ^ 2) d e : ℤ) : ℂ) * c e)
          + 40 * (∑ e, ((boostAverageZ d e : ℤ) : ℂ) * c e) from by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Q_eq_poly]
      push_cast [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring, ← h1, ← h2, ← h3]
    ring
  rw [show (∑ e, ((Q d e : ℤ) : ℂ) * c e)
      = 48 * ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ)
        * ∑ e, ((minkowskiMatrixZ (e 0) (e 1) : ℤ) : ℂ) * c e from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Q_explicit, Matrix.of_apply]
    push_cast
    ring] at hQ
  linear_combination -hQ / 192

/-!

## F.4. The classification

-/

include hT in
/-- Every Lorentz invariant in the span of the components is a multiple of the metric
  contraction. -/
theorem exists_smul_metricContraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • metricContraction (T := T) := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_span hx hinv
  refine ⟨(4 : ℂ)⁻¹ * ∑ e, ((minkowskiMatrixZ (e 0) (e 1) : ℤ) : ℂ) * c e, ?_⟩
  rw [metricContraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul, ← eq_smul_minkowskiMatrixZ hc d]

/-!

## G. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a bi-Lorentz tensor, so
section F applies there and lifts back with an error term in `S`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a bi-Lorentz tensor. -/
lemma isBiLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsBiLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the metric contraction to the metric contraction of the
  images. -/
lemma mkQ_metricContraction (S : Submodule ℂ B) :
    S.mkQ (metricContraction (T := T))
      = metricContraction (T := fun l => S.mkQ (T l)) := by
  rw [metricContraction, metricContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

include hT in
/-- The same modulo a Lorentz-stable subspace `S`: a multiple of the metric contraction plus an
  error in `S`. -/
lemma exists_smul_metricContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • metricContraction (T := T) + y := by
  have hT' := hT.isBiLorentz_quotRep S hS
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
  obtain ⟨a, hcomb⟩ := hT'.exists_smul_metricContraction_of_invariant hmk hinv'
  rw [← mkQ_metricContraction] at hcomb
  refine ⟨a, x - a • metricContraction (T := T), ?_, by abel⟩
  have hker : x - a • metricContraction (T := T) ∈ LinearMap.ker S.mkQ := by
    rw [LinearMap.mem_ker, map_sub, hcomb, map_smul]
    abel
  rwa [Submodule.ker_mkQ] at hker

end IsBiLorentz

end Lorentz
