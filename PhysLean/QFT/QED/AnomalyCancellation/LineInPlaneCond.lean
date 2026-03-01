/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.ConstAbs
/-!
# Line in plane condition

We say a `LinSol` satisfies the `line in plane` condition if for all distinct `i1`, `i2`, `i3` in
`Fin n`, we have
`S i1 = S i2` or `S i1 = - S i2` or `2 S i3 + S i1 + S i2 = 0`.

We look at various consequences of this.
The main reference for this material is

- https://arxiv.org/pdf/1912.04804.pdf

We will show that `n ≥ 4` the `line in plane` condition on solutions implies the
`constAbs` condition.

-/

namespace PureU1

open BigOperators

variable {n : ℕ}

/-- The proposition on three rationals to satisfy the `linInPlane` condition. -/
def LineInPlaneProp : ℚ × ℚ × ℚ → Prop := fun s =>
  s.1 = s.2.1 ∨ s.1 = - s.2.1 ∨ 2 * s.2.2 + s.1 + s.2.1 = 0

/-- The proposition on a `LinSol` to satisfy the `linInPlane` condition. -/
def LineInPlaneCond (S : (PureU1 n).LinSols) : Prop :=
  ∀ (i1 i2 i3 : Fin n) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
  LineInPlaneProp (S.val i1, (S.val i2, S.val i3))

lemma lineInPlaneCond_perm {S : (PureU1 n).LinSols} (hS : LineInPlaneCond S)
    (M : (FamilyPermutations n).group) :
    LineInPlaneCond ((FamilyPermutations n).linSolRep M S) := by
  intro i1 i2 i3 h1 h2 h3
  rw [FamilyPermutations_anomalyFreeLinear_apply, FamilyPermutations_anomalyFreeLinear_apply,
    FamilyPermutations_anomalyFreeLinear_apply]
  refine hS (M.invFun i1) (M.invFun i2) (M.invFun i3) ?_ ?_ ?_
  all_goals simp_all only [ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq,
    not_false_eq_true]

lemma lineInPlaneCond_eq_last' {S : (PureU1 (n.succ.succ)).LinSols} (hS : LineInPlaneCond S)
    (h : ¬ (S.val ((Fin.last n).castSucc))^2 = (S.val ((Fin.last n).succ))^2) :
    (2 - n) * S.val (Fin.last (n + 1)) =
    - (2 - n)* S.val (Fin.castSucc (Fin.last n)) := by
  erw [sq_eq_sq_iff_eq_or_eq_neg] at h
  rw [LineInPlaneCond] at hS
  simp only [LineInPlaneProp] at hS
  simp only [Nat.succ_eq_add_one, Fin.succ_last, not_or] at h
  have h1 (i : Fin n) : S.val i.castSucc.castSucc =
      - (S.val ((Fin.last n).castSucc) + (S.val ((Fin.last n).succ))) / 2 := by
    have h1S := hS (Fin.last n).castSucc ((Fin.last n).succ) i.castSucc.castSucc
      (by simp only [Fin.ext_iff, Nat.succ_eq_add_one, Fin.succ_last, ne_eq]
          exact Nat.ne_add_one ↑(Fin.last n).castSucc)
      (by simp only [Nat.succ_eq_add_one, Fin.succ_last, ne_eq, Fin.ext_iff, Fin.val_last,
        Fin.val_castSucc]
          omega)
      (by simp only [Nat.succ_eq_add_one, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
          omega)
    simp_all only [Nat.succ_eq_add_one, ne_eq, Fin.succ_last, false_or, neg_add_rev]
    field_simp
    linear_combination h1S
  have h2 := pureU1_last S
  rw [Fin.sum_univ_castSucc] at h2
  simp only [Nat.succ_eq_add_one, h1, Fin.succ_last, neg_add_rev, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  field_simp at h2
  linear_combination h2

lemma lineInPlaneCond_eq_last {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : LineInPlaneCond S) : ConstAbsProp ((S.val ((Fin.last n.succ.succ.succ).castSucc)),
    (S.val ((Fin.last n.succ.succ.succ).succ))) := by
  rw [ConstAbsProp]
  by_contra hn
  have h := lineInPlaneCond_eq_last' hS hn
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hn
  simp only [Nat.succ_eq_add_one, Fin.succ_last, not_or] at hn
  have hx : ((2 : ℚ) - ↑(n + 3)) ≠ 0 := by
    rw [Nat.cast_add]
    simp only [Nat.cast_ofNat, ne_eq]
    apply Not.intro
    intro a
    linarith
  have ht : S.val ((Fin.last n.succ.succ.succ).succ) =
    - S.val ((Fin.last n.succ.succ.succ).castSucc) := by
    rw [← mul_right_inj' hx]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.succ_eq_add_one, Fin.succ_last, mul_neg]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.succ_eq_add_one, neg_sub] at h
    rw [h]
    ring
  simp_all

lemma linesInPlane_eq_sq {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : LineInPlaneCond S) : ∀ (i j : Fin n.succ.succ.succ.succ.succ) (_ : i ≠ j),
    ConstAbsProp (S.val i, S.val j) := by
  have hneq : ((Fin.last n.succ.succ.succ).castSucc) ≠ ((Fin.last n.succ.succ.succ).succ) := by
    simp [Fin.ext_iff]
  refine Prop_two ConstAbsProp hneq ?_
  intro M
  exact lineInPlaneCond_eq_last (lineInPlaneCond_perm hS M)

theorem linesInPlane_constAbs {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : LineInPlaneCond S) : ConstAbs S.val := by
  intro i j
  by_cases hij : i ≠ j
  · exact linesInPlane_eq_sq hS i j hij
  · simp only [Nat.succ_eq_add_one, PureU1_numberCharges, ne_eq, Decidable.not_not] at hij
    rw [hij]

lemma linesInPlane_four (S : (PureU1 4).Sols) (hS : LineInPlaneCond S.1.1) :
    ConstAbsProp (S.val (0 : Fin 4), S.val (1 : Fin 4)) := by
  simp only [ConstAbsProp, Fin.isValue]
  by_contra hn
  have hLin := pureU1_linear S.1.1
  have hcube := pureU1_cube S
  simp only [PureU1_numberCharges] at hLin hcube
  rw [Fin.sum_univ_four] at hLin hcube
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hn
  simp only [Fin.isValue, not_or] at hn
  have l012 := hS 0 1 2 (ne_of_beq_false rfl) (ne_of_beq_false rfl) (ne_of_beq_false rfl)
  have l013 := hS 0 1 3 (ne_of_beq_false rfl) (ne_of_beq_false rfl) (ne_of_beq_false rfl)
  have l023 := hS 0 2 3 (ne_of_beq_false rfl) (ne_of_beq_false rfl) (ne_of_beq_false rfl)
  simp_all [LineInPlaneProp]
  have h1 : S.val (2 : Fin 4) = S.val (3 : Fin 4) := by
    linear_combination l012 / 2 + -1 * l013 / 2
  by_cases h2 : S.val (0 : Fin 4) = S.val (2 : Fin 4)
  · simp_all
    have h3 : S.val (1 : Fin 4) = - 3 * S.val (2 : Fin 4) := by
      linear_combination l012 + 3 * h1
    rw [← h1, h3] at hcube
    have h4 : S.val (2 : Fin 4) ^ 3 = 0 := by
      linear_combination -1 * hcube / 24
    simp only [Fin.isValue, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h4
    simp_all only [neg_mul, neg_neg, add_eq_right, add_eq_left, not_true_eq_false, false_and]
  · by_cases h3 : S.val (0 : Fin 4) = - S.val (2 : Fin 4)
    · simp_all
      have h4 : S.val (1 : Fin 4) = - S.val (2 : Fin 4) := by
        linear_combination l012 + h1
      simp_all
    · simp_all
      have h4 : S.val (0 : Fin 4) = - 3 * S.val (3 : Fin 4) := by
        linear_combination l023
      have h5 : S.val (1 : Fin 4) = S.val (3 : Fin 4) := by
        linear_combination l013 - 1 * h4
      rw [h4, h5] at hcube
      have h6 : S.val (3 : Fin 4) ^ 3 = 0 := by
        linear_combination -1 * hcube / 24
      simp only [Fin.isValue, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h6
      simp_all

lemma linesInPlane_eq_sq_four {S : (PureU1 4).Sols}
    (hS : LineInPlaneCond S.1.1) : ∀ (i j : Fin 4) (_ : i ≠ j),
    ConstAbsProp (S.val i, S.val j) := by
  refine Prop_two ConstAbsProp Fin.zero_ne_one ?_
  intro M
  let S' := (FamilyPermutations 4).solAction.toFun _ _ S M
  have hS' : LineInPlaneCond S'.1.1 :=
    (lineInPlaneCond_perm hS M)
  exact linesInPlane_four S' hS'

lemma linesInPlane_constAbs_four (S : (PureU1 4).Sols)
    (hS : LineInPlaneCond S.1.1) : ConstAbs S.val := by
  intro i j
  by_cases hij : i ≠ j
  · exact linesInPlane_eq_sq_four hS i j hij
  · simp only [PureU1_numberCharges, ne_eq, Decidable.not_not] at hij
    rw [hij]

theorem linesInPlane_constAbs_AF (S : (PureU1 (n.succ.succ.succ.succ)).Sols)
    (hS : LineInPlaneCond S.1.1) : ConstAbs S.val := by
  induction n
  · exact linesInPlane_constAbs_four S hS
  · exact linesInPlane_constAbs hS

end PureU1
