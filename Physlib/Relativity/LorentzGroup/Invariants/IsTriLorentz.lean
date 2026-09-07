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
# Lorentz invariants of three four-vector indices

A rank-three tensor `T^{μνρ}` has no Lorentz invariant built from its components but `0`.
Nothing ties three indices: the metric takes two and the Levi-Civita symbol four, and an
odd number is left over either way. That is `eq_zero_of_invariant`, and
`mem_of_invariant_of_mem_sup` is the same statement modulo a Lorentz-stable subspace `S`,
the form the Standard Model files use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by three directions, and `IsTriLorentz` says the group
moves them with one factor of the Lorentz matrix per slot (B). `hT.span` is the set of
their combinations.

One axis does all the work, with a parity argument in place of a certificate. Along a
spatial axis the four light-cone directions carry boost weights `2`, `-2`, `0`, `0`, the
two of weight `0` being the two directions transverse to time and to that axis (C). An
invariant has weight `0`, so it is a combination of light-cone multi-indices of total
weight `0` (D); in such a multi-index the `+2` and `-2` slots pair off, leaving an odd
number of the three slots transverse. The half turn about the axis, the rotation by `π`,
fixes time and the axis and negates the two transverse directions (A), so it multiplies
each of those multi-indices by `-1` to an odd power, that is by `-1`. An invariant is
therefore both negated and fixed by it, hence zero (E). Section F divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. The half turn about a spatial axis

The half turn about the axis `i` is the rotation by `π` about it, `SL2C.halfTurn i`. Its
Lorentz matrix is diagonal, fixing time and the axis and negating the two transverse
directions, so on the light-cone directions of that axis it is `1` on the two of weight
`±2` and `-1` on the two transverse ones (`lightConeSign`).

-/

namespace SL2C

/-- The half turn about the axis `i`: the rotation by `π` about the `i`-th spatial
  axis, written in `SL(2,ℂ)`. -/
noncomputable def halfTurn : Fin 3 → SL(2,ℂ)
  | 0 => ⟨!![0, -Complex.I; -Complex.I, 0], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩
  | 1 => ⟨!![0, -1; 1, 0], by
      rw [Matrix.det_fin_two_of]
      simp⟩
  | 2 => ⟨!![-Complex.I, 0; 0, Complex.I], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩

/-- The matrix entries of the half turn about the `x`-axis. -/
@[simp] lemma halfTurn_zero_apply (j k : Fin 2) :
    (halfTurn 0).1 j k = (!![0, -Complex.I; -Complex.I, 0]) j k := rfl

/-- The matrix entries of the half turn about the `y`-axis. -/
@[simp] lemma halfTurn_one_apply (j k : Fin 2) :
    (halfTurn 1).1 j k = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the half turn about the `z`-axis. -/
@[simp] lemma halfTurn_two_apply (j k : Fin 2) :
    (halfTurn 2).1 j k = (!![-Complex.I, 0; 0, Complex.I]) j k := rfl

/-- The Lorentz matrix of the half turn about the axis `i` is diagonal: it fixes the
  time direction and the axis, and negates the two transverse directions. -/
lemma toLorentzGroup_halfTurn_apply (i : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup (halfTurn i)).1 a b =
      if a = b then (if b = Sum.inl 0 ∨ b = Sum.inr i then 1 else -1) else 0 := by
  refine Complex.ofReal_injective ?_
  rw [toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  fin_cases i <;>
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ext_iff]

end SL2C

/-- The sign the half turn about an axis gives each light-cone direction of that axis: `1` on
  the two of weight `±2`, `-1` on the two transverse ones. -/
def lightConeSign (κ : Fin 4) : ℤ := if κ = 0 ∨ κ = 1 then 1 else -1

/-- The half turn about the axis `i` acts on each light-cone direction along that axis
  by its sign. -/
lemma sum_halfTurn_lightConeCoeff (i : Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3) :
    ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ *
        (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 ν μ : ℝ) : ℂ)
      = ((lightConeSign κ : ℤ) : ℂ) * lightConeCoeff i κ ν := by
  simp only [SL2C.toLorentzGroup_halfTurn_apply]
  rcases ν with a | j
  · rw [Subsingleton.elim a 0]
    fin_cases i <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]

/-- The scalar behind the action of the half turn on a light-cone multi-index: the half
  turn acts slot by slot, so the product of the per-slot signs factors out. -/
lemma sum_prod_halfTurn_lightConeCoeff (i : Fin 3) {n : ℕ} (c : Fin n → Fin 4)
    (a : Fin n → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
  calc ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ∑ d : Fin n → Fin 1 ⊕ Fin 3, ∏ j, (lightConeCoeff i (c j) (d j) *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ j, ∑ μ : Fin 1 ⊕ Fin 3, (lightConeCoeff i (c j) μ *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) μ : ℝ) : ℂ)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, (((lightConeSign (c j) : ℤ) : ℂ) * lightConeCoeff i (c j) (a j)) :=
        Finset.prod_congr rfl fun j _ => sum_halfTurn_lightConeCoeff i (c j) (a j)
    _ = (∏ j, ((lightConeSign (c j) : ℤ) : ℂ)) * ∏ j, lightConeCoeff i (c j) (a j) :=
        Finset.prod_mul_distrib
    _ = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
        push_cast
        rfl

/-- A light-cone multi-index of three slots and total boost weight zero has an odd
  number of transverse slots, so the half turn acts on it by `-1`. -/
lemma prod_lightConeSign_of_sum_lightConeWeight_eq_zero (c : Fin 3 → Fin 4)
    (hc : (∑ j, lightConeWeight (c j)) = 0) : ∏ j, lightConeSign (c j) = -1 := by
  revert c
  decide

/-!

## B. Triple Lorentz tensors and the span of their components

The hypothesis on the family and the space its components span, which is where the
invariants to be classified live.

-/

/-- A family `T` of elements of `B`, indexed by three four-vector indices, transforms as
  a tensor `T^{μ₁ μ₂ μ₃}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsTriLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 3 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 3 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 3), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsTriLorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 3 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsTriLorentz B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsTriLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 3 → Fin 1 ⊕ Fin 3) → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-!

## C. The light-cone basis along one axis

Recombining the components along the light-cone directions of the axis `i` gives the
light-cone components `hT.lightCone i c`: they span the same space, are boost
eigenvectors of weight the total weight of `c`, and the half turn multiplies each by the
product of the signs of its slots, so it negates exactly those with an odd number of
transverse slots.

-/

set_option linter.unusedVariables false in
/-- The light-cone component of `T` along axis `i` at the light-cone index `c`; `hT` is
  present only so it reads `hT.lightCone`. -/
noncomputable def lightCone (hT : IsTriLorentz B repLorentz T) (i : Fin 3)
    (c : Fin 3 → Fin 4) : B :=
  ∑ d : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 3 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Each component is recovered from the light-cone components along any axis. -/
lemma eq_sum_lightCone (i : Fin 3) (d : Fin 3 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 3 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 3 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 3 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The light-cone components along any axis span the same space as the components. -/
lemma span_eq_lightCone (hT : IsTriLorentz B repLorentz T) (i : Fin 3) :
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
lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 3 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [lightCone, map_sum, map_smul, hT.repLorentz_T, Finset.smul_sum,
          smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul.symm
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        simp only [sum_prod_lightConeCoeff i c _ ht, lightCone, Finset.smul_sum, smul_smul]
        rfl

/-- The half turn about the axis `i` acts on the light-cone component at `c` by the
  product of the signs of its slots. -/
lemma repLorentz_halfTurn_lightCone (i : Fin 3) (c : Fin 3 → Fin 4) :
    repLorentz (SL2C.halfTurn i) (hT.lightCone i c)
      = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) • hT.lightCone i c := by
  have hstep : ∀ x : Fin 3 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) • repLorentz (SL2C.halfTurn i) (T x)
        = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.halfTurn i) (hT.lightCone i c)
      = ∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.halfTurn i) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3, (((∏ j, lightConeSign (c j) : ℤ) : ℂ) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a :=
        Finset.sum_congr rfl fun a _ => by
          rw [sum_prod_halfTurn_lightConeCoeff i c a]
    _ = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) • hT.lightCone i c := by
        rw [lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-!

## D. The weight-zero part of a component

Each component `T e` is the sum of its boost-weight parts `hT.monoComponent i e m`, so a
vector of weight zero along the axis `i` is the combination of the weight-zero parts
alone. Those are built from light-cone multi-indices of total weight zero, which the half
turn negates.

-/

/-- The weight-`m` part of `T e` along axis `i`: the weight-`m` terms of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 3 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

/-- The weight-`m` part has boost weight `m`. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3)
    (m : ℤ) : hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The total weight of three slots is even and between `-6` and `6`, a finite check. -/
lemma sum_lightConeWeight_mem (c : Fin 3 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ) := by
  revert c
  decide

/-- A component is the sum of its boost-weight parts. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

include hT in
/-- A vector of boost weight zero along axis `i` is the combination of the weight-zero
  parts alone. -/
lemma eq_sum_monoComponent_zero (i : Fin 3) {x : B}
    (c : (Fin 3 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ e, c e • hT.monoComponent i e 0 := by
  have hsum : x = ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ),
            hT.monoComponent i e m :=
          Finset.sum_congr rfl fun e _ => by rw [← hT.eq_sum_monoComponent_univ i e]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  exact eq_component_zero_of_mem_boostWeightSubmodule
    (w := fun m => ∑ e, c e • hT.monoComponent i e m) hw
    (fun m _ => sum_mem fun e _ => Submodule.smul_mem _ _
      (hT.monoComponent_mem_boostWeightSubmodule i e m))
    (by decide) hsum

/-- The half turn about the axis `i` negates the weight-zero part of a component: every
  light-cone multi-index in it has an odd number of transverse slots. -/
lemma repLorentz_halfTurn_monoComponent_zero (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) :
    repLorentz (SL2C.halfTurn i) (hT.monoComponent i e 0) = -hT.monoComponent i e 0 := by
  rw [monoComponent, map_sum, ← neg_one_smul (R := ℂ), Finset.smul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [map_smul, hT.repLorentz_halfTurn_lightCone i c,
    prod_lightConeSign_of_sum_lightConeWeight_eq_zero c (Finset.mem_filter.1 hc).2,
    smul_smul, smul_smul]
  norm_num [mul_comm]

/-!

## E. The classification of the Lorentz invariants

One axis suffices. An invariant has boost weight zero along it, so section D writes it
through the weight-zero parts alone, which the half turn about that axis negates. The
invariant is therefore both fixed and negated by one Lorentz transformation, so it is
zero.

-/

include hT in
/-- Every Lorentz invariant in the span of the components is zero: three indices carry no
  invariant contraction. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h0 : x = ∑ e, c e • hT.monoComponent 2 e 0 :=
    hT.eq_sum_monoComponent_zero 2 c hc (hw 2)
  have hneg : repLorentz (SL2C.halfTurn 2) x = -x := by
    calc repLorentz (SL2C.halfTurn 2) x
        = ∑ e, c e • repLorentz (SL2C.halfTurn 2) (hT.monoComponent 2 e 0) := by
          conv_lhs => rw [h0]
          rw [map_sum]
          exact Finset.sum_congr rfl fun e _ => map_smul _ _ _
      _ = ∑ e, c e • -hT.monoComponent 2 e 0 :=
          Finset.sum_congr rfl fun e _ => by
            rw [hT.repLorentz_halfTurn_monoComponent_zero 2 e]
      _ = -x := by
          rw [h0]
          simp
  have hself : x = -x := by
    conv_lhs => rw [← hinv (SL2C.halfTurn 2)]
    exact hneg
  have htwo : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 hself
  simpa using htwo

/-!

## F. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a triple Lorentz tensor, so
section E applies there and an invariant of `hT.span ⊔ S` lies in `S`.

-/

include hT in
/-- The classes of the components in the quotient again form a triple Lorentz tensor. -/
lemma isTriLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsTriLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
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
  have hT' := hT.isTriLorentz_quotRep S hS
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

end IsTriLorentz

end Lorentz
