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

The proof is the two-index case of the argument in `IsQuadLorentz`, and reuses its
light-cone coefficients and sector matrices. Along a spatial axis the four light-cone
directions carry boost weights `2`, `-2`, `0`, `0` (B), and an invariant, having weight
`0` along every axis, is fixed by the weight-zero projection along each; averaging the
three gives one linear map on the `16` components, `12` times an integer matrix with a
short closed form (C, D). Its eigenvalues are `12`, `10`, `4`, `0`, with `12` simple, so
the cubic `λ (λ - 4) (λ - 10)` sends everything onto that one eigenvector, which is the
metric (E). Section F draws the conclusion and G divides out `S`.

No rotation averaging is needed here, unlike the four-index case: for two indices the
three weight-zero conditions already cut the `16` components down to a single line.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (lightConeCoeffZ coe_lightConeCoeffZ lightConeCoeffInvQ
  coe_lightConeCoeffInvQ lightConeCoeffInvZ coe_lightConeCoeffInvZ sectorIndex
  sectorWeight lightConeWeight_eq_sectorWeight slotTransition slotTransitionZ
  slotTransitionZ_eq_sum eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant etaZ quotRep quotRep_mkQ)

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

/-!

## B. The light-cone basis along one axis

The boost along the axis `i` scales the light-cone directions `D₀ - Dᵢ`, `D₀ + Dᵢ` and the
two transverse ones by `t²`, `t⁻²`, `1`, `1`, so their weights are `2`, `-2`, `0`, `0`.
Recombining the components along those directions gives `hT.lightCone i c`, which spans
the same space and is a boost eigenvector of weight the total weight of `c`.

-/

set_option linter.unusedVariables false in
/-- The light-cone component of `T` along axis `i` at the light-cone index `c`; `hT` is
  present only so it reads `hT.lightCone`. -/
noncomputable def lightCone (hT : IsBiLorentz B repLorentz T) (i : Fin 3)
    (c : Fin 2 → Fin 4) : B :=
  ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the coordinate components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 2 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the light-cone components along any axis. -/
lemma eq_sum_lightCone (i : Fin 3) (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 2 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 2 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 2 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The light-cone components along any axis span the same space as the components. -/
lemma span_eq_lightCone (hT : IsBiLorentz B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ c, ℂ ∙ hT.lightCone i c := by
  rw [span]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun c => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_lightCone i d]
    exact sum_mem fun c _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.lightCone_mem_span i c

/-- The light-cone components are boost eigenvectors: along axis `i` the component at
  `c` has boost weight the total light-cone weight of `c`. -/
lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 2 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 2 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [lightCone, map_sum, map_smul, hT.repLorentz_T, Finset.smul_sum,
          smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul.symm
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        simp only [sum_prod_lightConeCoeff i c _ ht, lightCone, Finset.smul_sum, smul_smul]
        rfl

/-!

## C. The weight-zero projection and its average over the axes

## C.1. The boost-weight parts of a component

Each component `T e` is the sum of its boost-weight parts `hT.monoComponent i e m`; with
two indices the weights are the five even numbers from `-4` to `4`.

-/

/-- The axis-`i` weight-`m` component of the generator `T e`: the weight-`m` partial
  sum of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 2 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 2 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 2 → Fin 1 ⊕ Fin 3)
    (m : ℤ) : hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The total light-cone weight of two slots is even and lies between `-4` and `4`. -/
lemma sum_lightConeWeight_mem (c : Fin 2 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-4, -2, 0, 2, 4} : Finset ℤ) := by
  have hweight (κ : Fin 4) :
      ∃ q : ℤ, -1 ≤ q ∧ q ≤ 1 ∧ lightConeWeight κ = 2 * q := by
    fin_cases κ
    · exact ⟨1, by norm_num [lightConeWeight]⟩
    · exact ⟨-1, by norm_num [lightConeWeight]⟩
    · exact ⟨0, by norm_num [lightConeWeight]⟩
    · exact ⟨0, by norm_num [lightConeWeight]⟩
  obtain ⟨q0, hq0_lower, hq0_upper, hq0⟩ := hweight (c 0)
  obtain ⟨q1, hq1_lower, hq1_upper, hq1⟩ := hweight (c 1)
  rw [Fin.sum_univ_two, hq0, hq1]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A component is the sum of its weight components over the five possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 2 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-4, -2, 0, 2, 4} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

/-!

## C.2. The weight-zero transition matrix

Written back on the components, the weight-zero part of `T e` is a matrix applied to the
components: a sum over the sector patterns of total weight zero of the per-slot sector
matrices of `IsQuadLorentz`.

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

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i e 0`
  is the `e`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (e : Fin 2 → Fin 1 ⊕ Fin 3) :
    hT.monoComponent i e 0
      = ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((weightZeroTransition i d e : ℚ) : ℂ) • T d := by
  rw [monoComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [weightZeroTransition_eq_sum_lightCone]
  push_cast
  simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ, Finset.prod_mul_distrib]

/-!

## C.3. The average over the axes, and its powers

An invariant has weight zero along all three axes, so it is fixed by each of the three
weight-zero transitions, hence by their average and by every power of that average.

-/

/-- The average `M` of the three weight-zero transitions, as a matrix on the components. Its
  powers drive the endgame. -/
def boostAverageTransition :
    Matrix (Fin 2 → Fin 1 ⊕ Fin 3) (Fin 2 → Fin 1 ⊕ Fin 3) ℚ :=
  Matrix.of fun d e => (3⁻¹ : ℚ) * ∑ i : Fin 3, weightZeroTransition i d e

include hT in
/-- A vector of boost weight zero along axis `i` is written with the weight-zero transition
  applied to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
  have hsum : x = ∑ m ∈ ({-4, -2, 0, 2, 4} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-4, -2, 0, 2, 4} : Finset ℤ), hT.monoComponent i e m :=
          Finset.sum_congr rfl fun e _ => by rw [← hT.eq_sum_monoComponent_univ i e]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ e, c e • hT.monoComponent i e 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ e, c e • hT.monoComponent i e m) hw
      (fun m _ => sum_mem fun e _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i e m))
      (by decide) hsum
  calc x = ∑ e, c e • hT.monoComponent i e 0 := hx0
    _ = ∑ e, c e • ∑ d, ((weightZeroTransition i d e : ℚ) : ℂ) • T d :=
        Finset.sum_congr rfl fun e _ => by rw [hT.monoComponent_zero_eq i e]
    _ = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        exact Finset.sum_congr rfl fun e _ => mul_comm _ _

include hT in
/-- One averaged round of the recursion: an element of weight zero along all three
  axes re-expands with the boost-average matrix `M` applied to its coefficients. -/
lemma eq_sum_boostAverageTransition_smul {x : B}
    (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
  have hround : ∀ i : Fin 3,
      x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3⁻¹ : ℂ) • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, x := by rw [h3]
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, ∑ d,
          (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
        congrArg (fun y => (3⁻¹ : ℂ) • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [boostAverageTransition, Matrix.of_apply]
        push_cast
        rw [mul_assoc, Finset.sum_mul]

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
      48 * (etaZ (d 0) (d 1) * etaZ (e 0) (e 1)) := by
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

/-!

## F. The classification of the Lorentz invariants

## F.1. The metric contraction

-/

/-- The metric contraction `g^{μν} T_{μν}`, the only invariant contraction of two
  four-vector indices. -/
noncomputable def metricContraction : B :=
  ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 1) : ℤ) : ℂ) • T d

/-!

## F.2. Iterating the averaged round

-/

include hT in
/-- One averaged round in integer form: the averaged round acts by the integer matrix
  `boostAverageZ` with the overall `12⁻¹` normalisation. -/
lemma eq_sum_boostAverageZ_smul {x : B} (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, ((12 : ℂ)⁻¹ * ∑ e, ((boostAverageZ d e : ℤ) : ℂ) * c e) • T d := by
  rw [hT.eq_sum_boostAverageTransition_smul c hx hw]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hb := congrArg (fun q : ℚ => (q : ℂ)) (coe_boostAverageZ d e)
  push_cast at hb ⊢
  rw [hb]
  ring

include hT in
/-- Iterated averaged rounds in integer form: `n` rounds act by the `n`-th power of the
  integer matrix with the `12⁻ⁿ` normalisation. -/
lemma eq_sum_pow_boostAverageZ_smul {x : B} (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) (n : ℕ) :
    x = ∑ d, (((12 : ℂ) ^ n)⁻¹ * ∑ e, (((boostAverageZ ^ n) d e : ℤ) : ℂ) * c e)
      • T d := by
  induction n with
  | zero =>
    rw [hx]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    rw [pow_zero, pow_zero]
    simp [Matrix.one_apply, apply_ite (fun q : ℤ => (q : ℂ)), ite_mul, Finset.sum_ite_eq]
  | succ n ih =>
    rw [hT.eq_sum_boostAverageZ_smul
      (fun d => ((12 : ℂ) ^ n)⁻¹ * ∑ e, (((boostAverageZ ^ n) d e : ℤ) : ℂ) * c e)
      ih hw]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    calc (12 : ℂ)⁻¹ * ∑ f, ((boostAverageZ d f : ℤ) : ℂ)
          * (((12 : ℂ) ^ n)⁻¹ * ∑ e, (((boostAverageZ ^ n) f e : ℤ) : ℂ) * c e)
        = ((12 : ℂ) ^ (n + 1))⁻¹ * ∑ f, ((boostAverageZ d f : ℤ) : ℂ)
            * ∑ e, (((boostAverageZ ^ n) f e : ℤ) : ℂ) * c e := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [pow_succ]
          field_simp
      _ = ((12 : ℂ) ^ (n + 1))⁻¹
            * ∑ e, (((boostAverageZ * boostAverageZ ^ n) d e : ℤ) : ℂ) * c e := by
          congr 1
          calc ∑ f, ((boostAverageZ d f : ℤ) : ℂ)
                * ∑ e, (((boostAverageZ ^ n) f e : ℤ) : ℂ) * c e
              = ∑ f, ∑ e, ((boostAverageZ d f : ℤ) : ℂ)
                  * ((((boostAverageZ ^ n) f e : ℤ) : ℂ) * c e) :=
                Finset.sum_congr rfl fun f _ => by rw [Finset.mul_sum]
            _ = ∑ e, (∑ f, ((boostAverageZ d f : ℤ) : ℂ)
                  * (((boostAverageZ ^ n) f e : ℤ) : ℂ)) * c e := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun e _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun f _ => (mul_assoc _ _ _).symm
            _ = ∑ e, (((boostAverageZ * boostAverageZ ^ n) d e : ℤ) : ℂ) * c e := by
                refine Finset.sum_congr rfl fun e _ => ?_
                congr 1
                rw [Matrix.mul_apply]
                push_cast
                rfl
      _ = ((12 : ℂ) ^ (n + 1))⁻¹
            * ∑ e, (((boostAverageZ ^ (n + 1)) d e : ℤ) : ℂ) * c e := by
          rw [← pow_succ' boostAverageZ n]

/-!

## F.3. The certificate round

-/

include hT in
/-- Applying the certificate polynomial to the coefficients reproduces `x`, as the combination
  of three iterated averages weighted by the certificate coefficients. -/
lemma eq_sum_Q_smul {x : B} (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, ((192 : ℂ)⁻¹ * ∑ e, ((Q d e : ℤ) : ℂ) * c e) • T d := by
  have h1 := hT.eq_sum_pow_boostAverageZ_smul c hx hw 1
  have h2 := hT.eq_sum_pow_boostAverageZ_smul c hx hw 2
  have h3 := hT.eq_sum_pow_boostAverageZ_smul c hx hw 3
  simp only [pow_one] at h1
  have key : (9 : ℂ) • x - (21 / 2 : ℂ) • x + (5 / 2 : ℂ) • x
      = ∑ d, ((192 : ℂ)⁻¹ * ∑ e, ((Q d e : ℤ) : ℂ) * c e) • T d := by
    nth_rewrite 1 [h3]
    nth_rewrite 1 [h2]
    nth_rewrite 1 [h1]
    simp only [Finset.smul_sum, smul_smul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [← sub_smul, ← add_smul]
    congr 1
    have hQc : ∀ e, ((Q d e : ℤ) : ℂ)
        = (((boostAverageZ ^ 3) d e : ℤ) : ℂ)
          - 14 * (((boostAverageZ ^ 2) d e : ℤ) : ℂ)
          + 40 * ((boostAverageZ d e : ℤ) : ℂ) := fun e => by
      rw [Q_eq_poly]
      push_cast [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hsplit : ∑ e, ((Q d e : ℤ) : ℂ) * c e
        = (∑ e, (((boostAverageZ ^ 3) d e : ℤ) : ℂ) * c e)
          - 14 * (∑ e, (((boostAverageZ ^ 2) d e : ℤ) : ℂ) * c e)
          + 40 * (∑ e, ((boostAverageZ d e : ℤ) : ℂ) * c e) := by
      simp only [hQc, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [hsplit]
    field_simp
    ring_nf
  calc x = (9 : ℂ) • x - (21 / 2 : ℂ) • x + (5 / 2 : ℂ) • x := by module
    _ = _ := key

include hT in
/-- A vector of the span of boost weight zero along all three axes is the corresponding
  multiple of the metric contraction. -/
lemma eq_smul_metricContraction {x : B} (c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ((4 : ℂ)⁻¹ * ∑ e, ((etaZ (e 0) (e 1) : ℤ) : ℂ) * c e)
      • metricContraction (T := T) := by
  rw [hT.eq_sum_Q_smul c hx hw, metricContraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]
  congr 1
  have hP : ∀ e, ((Q d e : ℤ) : ℂ)
      = 48 * ((etaZ (d 0) (d 1) : ℤ) : ℂ) * ((etaZ (e 0) (e 1) : ℤ) : ℂ) := fun e => by
    rw [Q_explicit, Matrix.of_apply]
    push_cast
    ring
  rw [show (∑ e, ((Q d e : ℤ) : ℂ) * c e)
      = 48 * ((etaZ (d 0) (d 1) : ℤ) : ℂ)
        * ∑ e, ((etaZ (e 0) (e 1) : ℤ) : ℂ) * c e from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [hP e]; ring]
  field_simp
  ring

/-!

## F.4. The classification

-/

include hT in
/-- Every Lorentz invariant in the span of the components is a multiple of the metric
  contraction. -/
theorem exists_smul_metricContraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • metricContraction (T := T) := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  exact ⟨_, hT.eq_smul_metricContraction c hc
    (mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv)⟩

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
