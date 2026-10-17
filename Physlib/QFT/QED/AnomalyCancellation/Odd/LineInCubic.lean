/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.LineInPlaneCond
public import Physlib.QFT.QED.AnomalyCancellation.Odd.BasisLinear
/-!

# Line In Cubic Odd case

We say that a linear solution satisfies the `lineInCubic` property
if the line through that point and through the two different planes formed by the basis of
`LinSols` lies in the cubic.

We show that for a solution all its permutations satisfy this property,
then the charge must be zero.

## References

* The main reference for this file is https://arxiv.org/pdf/1912.04804.pdf. [ref: arxiv_1912_04804]
-/

@[expose] public section
namespace PureU1
namespace Odd

open BigOperators

variable {n : ℕ}
open VectorLikeOddPlane

/-- A property on `LinSols`, satisfied if every point on the line between the two planes
in the basis through that point is in the cubic. -/
def LineInCubic (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (g f : Fin n → ℚ) (_ : S.val = Pa g f) (a b : ℚ),
  accCube (2 * n + 1) (a • Unshifted.planeCharges g + b • Shifted.planeCharges f) = 0

set_option backward.isDefEq.respectTransparency false in
/-- The condition that a linear solution sits on a line between the two planes
  within the cubic expands into a on `accCubeTriLinSymm` applied to the points
  within the planes. -/
lemma lineInCubic_expand {S : (PureU1 (2 * n + 1)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ)
      (_ : S.val = Unshifted.planeCharges g + Shifted.planeCharges f)
      (a b : ℚ),
    3 * a * b *
      (a * accCubeTriLinSymm (Unshifted.planeCharges g) (Unshifted.planeCharges g)
          (Shifted.planeCharges f) +
        b * accCubeTriLinSymm (Shifted.planeCharges f) (Shifted.planeCharges f)
          (Unshifted.planeCharges g)) = 0 := by
  intro g f hS a b
  have h1 := h g f hS a b
  change accCubeTriLinSymm.toCubic
    (a • Unshifted.planeCharges g + b • Shifted.planeCharges f) = 0 at h1
  simp only [TriLinearSymm.toCubic_add, HomogeneousCubic.map_smul,
    accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂, accCubeTriLinSymm.map_smul₃] at h1
  erw [Unshifted.planeCharges_accCube, Shifted.planeCharges_accCube] at h1
  linear_combination h1

lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n + 1)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ)
      (_ : S.val = Unshifted.planeCharges g + Shifted.planeCharges f),
    accCubeTriLinSymm (Unshifted.planeCharges g) (Unshifted.planeCharges g)
      (Shifted.planeCharges f) = 0 := by
  intro g f hS
  linear_combination 2 / 3 * (lineInCubic_expand h g f hS 1 1) -
      (lineInCubic_expand h g f hS 1 2) / 6

/-- A `LinSol` satisfies `lineInCubicPerm` if all its permutations satisfy `lineInCubic`. -/
def LineInCubicPerm (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n + 1)).group),
    LineInCubic ((FamilyPermutations (2 * n + 1)).linSolRep M S)

/-- If `lineInCubicPerm S`, then `lineInCubic S`. -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n + 1)).LinSols} (hS : LineInCubicPerm S) :
    LineInCubic S := hS 1

/-- If `lineInCubicPerm S`, then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n + 1)).LinSols}
    (hS : LineInCubicPerm S) (M' : (FamilyPermutations (2 * n + 1)).group) :
    LineInCubicPerm ((FamilyPermutations (2 * n + 1)).linSolRep M' S) :=
  fun M => hS (M * M')

set_option backward.isDefEq.respectTransparency false in
lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) :
    ∀ (j : Fin n.succ) (g f : Fin n.succ → ℚ) (_ : S.val = Pa g f),
      (S.val (oddShiftSnd j) - S.val (oddShiftFst j))
      * accCubeTriLinSymm
        (Unshifted.planeCharges g) (Unshifted.planeCharges g)
        (Shifted.basisAsCharges j) = 0 := by
  intro j g f h
  obtain ⟨g', f', hall⟩ := span_basis_swap! j rfl g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P! (lineInCubicPerm_self (lineInCubicPerm_permute LIC
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2, accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (f g : Fin n.succ.succ → ℚ) (hS : S.val = Pa f g) :
    accCubeTriLinSymm (Unshifted.planeCharges f) (Unshifted.planeCharges f)
      (Shifted.basisAsCharges 0) =
    (S.val (oddShiftFst 0) + S.val (oddShiftSnd 0)) *
    (2 * S.val oddShiftZero + S.val (oddShiftFst 0) + S.val (oddShiftSnd 0)) := by
  rw [P_P_P!_accCube f 0, ← Pa_oddShiftShiftZero f g, ← hS]
  nth_rewrite 1 [show oddShiftFst (0 : Fin n.succ.succ) = oddFst 1 from rfl]
  rw [Unshifted.planeCharges_oddFst]
  have h1 := Pa_oddShiftShiftZero f g
  have h4 := Pa_oddShiftShiftSnd f g 0
  have h2 := Pa_oddShiftShiftFst f g 0
  rw [← hS] at h1 h2 h4
  simp only [Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Fin.castSucc_zero] at h2
  have h5 : f 1 = S.val (oddShiftShiftFst 0) + S.val oddShiftShiftZero +
      S.val (oddShiftShiftSnd 0) := by
    linear_combination -h1 - h4 - h2
  rw [h5, oddShiftShiftSnd_eq_oddShiftSnd,
    show (oddShiftShiftFst (0 : Fin n.succ)) = oddShiftFst 0 from rfl,
    oddShiftShiftZero_eq_oddShiftZero]
  ring

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ+1)).LinSols}
    (LIC : LineInCubicPerm S) :
    LineInPlaneProp ((S.val (oddShiftSnd 0)), ((S.val (oddShiftFst 0)), (S.val oddShiftZero))) := by
  obtain ⟨g, f, hfg⟩ := span_basis S
  have h1 := lineInCubicPerm_swap LIC 0 g f hfg
  rw [P_P_P!_accCube' g f hfg] at h1
  simp only [Nat.succ_eq_add_one, mul_eq_zero] at h1
  rcases h1 with h1 | h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (Or.inl (by linear_combination h1))
  · exact Or.inr (Or.inr (by linear_combination h1))

lemma lineInCubicPerm_last_perm {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : LineInPlaneCond S :=
  @Prop_three (2 * n.succ.succ + 1) LineInPlaneProp S (oddShiftSnd 0) (oddShiftFst 0)
    oddShiftZero (ne_of_beq_false rfl) (ne_of_beq_false rfl) (ne_of_beq_false rfl)
    (fun M => lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M))

lemma lineInCubicPerm_constAbs {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : ConstAbs S.val :=
  linesInPlane_constAbs (lineInCubicPerm_last_perm LIC)

lemma lineInCubicPerm_zero {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : S = 0 :=
  ConstAbs.boundary_value_odd S (lineInCubicPerm_constAbs LIC)

end Odd
end PureU1
