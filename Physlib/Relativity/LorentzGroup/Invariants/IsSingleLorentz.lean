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
# Lorentz invariants of a single four-vector index

A four-vector `T^{μ}` has no Lorentz invariant built from its four components but `0`.
There is nothing to contract it with: the metric takes two indices and the Levi-Civita
symbol four. That is `eq_zero_of_invariant`, and `mem_of_invariant_of_mem_sup` is the
same statement modulo a Lorentz-stable subspace `S`, the form the Standard Model files
use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by one direction `d`, and `IsSingleLorentz` says the
group moves them by the Lorentz matrix (A). `hT.span` is the set of their combinations.

The proof takes one boost at a time and needs no certificate. Along a spatial axis the
four light-cone directions carry boost weights `2`, `-2`, `0`, `0` (B), so an invariant,
having weight `0`, keeps only the coefficients of the two weight-zero directions, which
are the two directions transverse to time and to that axis (C). No direction is
transverse to all three axes, so running the three axes in turn leaves nothing (D).
Section E divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (lightConeCoeffZ coe_lightConeCoeffZ lightConeCoeffInvQ
  coe_lightConeCoeffInvQ lightConeCoeffInvZ coe_lightConeCoeffInvZ
  eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. Single Lorentz tensors and the span of their components

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes, and `T d` is
the component `T^{μ}` at `μ = d`. `IsSingleLorentz B repLorentz T` says the group moves
them by the Lorentz matrix `Λ` of `g : SL(2,ℂ)`, and `hT.span` is the set of combinations
`∑ d, c d • T d` (`mem_span_iff`).

-/

/-- A family `T` of elements of `B`, indexed by a single four-vector index, transforms
  as a vector `T^{μ}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsSingleLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 1 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 1), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsSingleLorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsSingleLorentz B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsSingleLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-!

## B. The light-cone basis along one axis

The boost along the axis `i` scales the light-cone directions `D₀ - Dᵢ`, `D₀ + Dᵢ` and the
two transverse ones by `t²`, `t⁻²`, `1`, `1`, so their weights, the exponents of `t`, are
`2`, `-2`, `0`, `0`. Recombining the components along those directions gives the light-cone
components `hT.lightCone i c`, which span the same space and are boost eigenvectors of
weight the total weight of `c`.

-/

set_option linter.unusedVariables false in
/-- The light-cone component of `T` along axis `i` at the light-cone index `c`; `hT` is
  present only so it reads `hT.lightCone`. -/
noncomputable def lightCone (hT : IsSingleLorentz B repLorentz T) (i : Fin 3)
    (c : Fin 1 → Fin 4) : B :=
  ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 1 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Each component is recovered from the light-cone components along any axis. -/
lemma eq_sum_lightCone (i : Fin 3) (d : Fin 1 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 1 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 1 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 1 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The light-cone components along any axis span the same space as the components. -/
lemma span_eq_lightCone (hT : IsSingleLorentz B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ c, ℂ ∙ hT.lightCone i c := by
  rw [span]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun c => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_lightCone i d]
    exact sum_mem fun c _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.lightCone_mem_span i c

/-- A light-cone component is a boost eigenvector, of weight the total weight of `c`. -/
lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 1 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ a : Fin 1 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 1 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
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

## C. The weight-zero part along one axis

## C.1. The boost-weight parts of a component

Each component `T e` is the sum of its boost-weight parts `hT.monoComponent i e m`; with
one index the only weights are `-2`, `0` and `2`.

-/

/-- The weight-`m` part of `T e` along axis `i`: the weight-`m` terms of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

/-- The weight-`m` part has boost weight `m`. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3)
    (m : ℤ) : hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- With one index the only light-cone weights are `-2`, `0` and `2`. -/
lemma sum_lightConeWeight_mem (c : Fin 1 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-2, 0, 2} : Finset ℤ) := by
  have hweight : ∀ κ : Fin 4, lightConeWeight κ ∈ ({-2, 0, 2} : Finset ℤ) := by decide
  rw [Fin.sum_univ_one]
  exact hweight (c 0)

/-- A component is the sum of its three boost-weight parts. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

/-!

## C.2. The weight-zero transition matrix

Written back on the components, the weight-zero part of `T e` is a matrix applied to the
components. Its closed form, checked by computation on the four directions, is the
projector onto the two directions transverse to time and to the axis. The integer copy
`weightZeroTransitionZ` carries a factor of `2`, from `lightConeCoeffInvZ`, so that the
check runs over integers.

-/

/-- A direction transverse to the boost along axis `i`: neither time nor the axis. -/
def Transverse (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Prop :=
  μ = Sum.inr (i + 1) ∨ μ = Sum.inr (i + 2)

instance (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Decidable (Transverse i μ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The weight-zero projection along axis `i`, as a matrix on the components: the
  coefficient of `T d` in the weight-zero part of `T e`. -/
def weightZeroTransition (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ)

/-- The weight-zero part of `T e`, written back on the components. -/
lemma monoComponent_zero_eq (i : Fin 3) (e : Fin 1 → Fin 1 ⊕ Fin 3) :
    hT.monoComponent i e 0
      = ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, ((weightZeroTransition i d e : ℚ) : ℂ) • T d := by
  rw [monoComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [weightZeroTransition]
  push_cast
  simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ, Finset.prod_mul_distrib]

/-- Twice the weight-zero transition, over `ℤ`, so that the closed form can be computed. -/
def weightZeroTransitionZ (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) : ℤ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 1 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvZ i (e s) (c s) * lightConeCoeffZ i (c s) (d s)

/-- The integer copy is twice the weight-zero transition. -/
lemma coe_weightZeroTransitionZ (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    ((weightZeroTransitionZ i d e : ℤ) : ℚ) = 2 * weightZeroTransition i d e := by
  rw [weightZeroTransitionZ, weightZeroTransition]
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
    _ = 2 * ∏ s, lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        norm_num [Finset.card_univ]

/-- Twice the projector onto the two directions transverse to time and to the axis `i`,
  a finite check over the four directions. -/
lemma weightZeroTransitionZ_eq (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    weightZeroTransitionZ i d e = if e 0 = d 0 ∧ Transverse i (d 0) then 2 else 0 := by
  revert i
  revert d e
  decide

/-- So the weight-zero transition is the projector onto the two directions transverse to
  time and to the axis `i`. -/
lemma weightZeroTransition_eq (i : Fin 3) (d e : Fin 1 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition i d e = if e 0 = d 0 ∧ Transverse i (d 0) then 1 else 0 := by
  have h := coe_weightZeroTransitionZ i d e
  rw [weightZeroTransitionZ_eq] at h
  split_ifs at h ⊢ <;> push_cast at h <;> linarith

/-!

## C.3. What one axis leaves

An invariant has boost weight zero along every axis, so along the axis `i` it is its own
weight-zero part: every coefficient outside the transverse pair of that axis is `0`.

-/

include hT in
/-- A vector of boost weight zero along axis `i` is written with the weight-zero
  transition applied to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
  have hsum : x = ∑ m ∈ ({-2, 0, 2} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i e m :=
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

/-- That transition keeps the coefficients of the two directions transverse to the axis
  `i` and discards the rest. -/
lemma sum_weightZeroTransition_mul (i : Fin 3) (d : Fin 1 → Fin 1 ⊕ Fin 3)
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) :
    ∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e
      = if Transverse i (d 0) then c d else 0 := by
  by_cases htr : Transverse i (d 0)
  · rw [if_pos htr]
    have hterm : ∀ e : Fin 1 → Fin 1 ⊕ Fin 3,
        ((weightZeroTransition i d e : ℚ) : ℂ) * c e = if e = d then c e else 0 := by
      intro e
      rw [weightZeroTransition_eq]
      by_cases he : e = d
      · subst he
        simp [htr]
      · have h0 : e 0 ≠ d 0 := fun h =>
          he (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
        simp [h0, he]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg htr]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [weightZeroTransition_eq, if_neg (fun h => htr h.2)]
    simp

include hT in
/-- So a vector of boost weight zero along axis `i` is written with every coefficient
  outside the transverse pair of that axis set to zero. -/
lemma eq_sum_transverse_smul (i : Fin 3) {x : B}
    (c : (Fin 1 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (if Transverse i (d 0) then c d else 0) • T d := by
  rw [hT.eq_sum_weightZeroTransition_smul i c hx hw]
  exact Finset.sum_congr rfl fun d _ => by rw [sum_weightZeroTransition_mul]

/-!

## D. The classification of the Lorentz invariants

No direction is transverse to all three axes at once, so applying C.3 to the three axes
in turn leaves nothing.

-/

/-- No direction is transverse to all three axes at once, a finite check. -/
lemma not_transverse_all (μ : Fin 1 ⊕ Fin 3) :
    ¬(Transverse 0 μ ∧ Transverse 1 μ ∧ Transverse 2 μ) := by
  revert μ
  decide

include hT in
/-- Every Lorentz invariant in the span of the components is zero: one index carries no
  invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h0 := hT.eq_sum_transverse_smul 0 c hc (hw 0)
  have h1 := hT.eq_sum_transverse_smul 1
    (fun d => if Transverse 0 (d 0) then c d else 0) h0 (hw 1)
  have h2 := hT.eq_sum_transverse_smul 2
    (fun d => if Transverse 1 (d 0) then (if Transverse 0 (d 0) then c d else 0) else 0)
    h1 (hw 2)
  rw [h2]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h2t : Transverse 2 (d 0)
  · by_cases h1t : Transverse 1 (d 0)
    · by_cases h0t : Transverse 0 (d 0)
      · exact absurd ⟨h0t, h1t, h2t⟩ (not_transverse_all (d 0))
      · rw [if_pos h2t, if_pos h1t, if_neg h0t, zero_smul]
    · rw [if_pos h2t, if_neg h1t, zero_smul]
  · rw [if_neg h2t, zero_smul]

/-!

## E. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a single Lorentz tensor, so
section D applies there and an invariant of `hT.span ⊔ S` lies in `S`.

-/

include hT in
/-- The classes of the components in the quotient again form a single Lorentz tensor. -/
lemma isSingleLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsSingleLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
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
  have hT' := hT.isSingleLorentz_quotRep S hS
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

end IsSingleLorentz

end Lorentz
