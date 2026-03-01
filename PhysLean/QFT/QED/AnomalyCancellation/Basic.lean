/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.AnomalyCancellation.Basic
import Mathlib.Tactic.LinearCombination
/-!

# Anomaly cancellation of a theory with a pure U(1)-gauge group

In a pure U(1) gauge theory with `n` Weyl fermions carrying charges `xᵢ` the anomaly cancellation
conditions (ACCs) which must be satisfied for a consistent gauge theory correspond to:

- The linear ACC: `∑ xᵢ = 0`
- The cubic ACC: `∑ xᵢ³ = 0`

The charges `xᵢ` have rational fractions with one another, here they are specified as
rational numbers.

-/

open Nat

open Finset

namespace PureU1
open BigOperators

TODO "K3HYF" "The implementation of pure U(1) anomaly cancellation conditions is done
  currently through the type `ACCSystemCharges`. This whole directory could be
  simplified by refactoring to remove `ACCSystemCharges` defining `PureU1Charges` as
  `Fin n → ℚ` directly, or this space quotiented by permutations and overall factors."

/-- The vector space of charges. -/
@[simps!]
def PureU1Charges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

open BigOperators in
/-- The gravitational anomaly. -/
def accGrav (n : ℕ) : ((PureU1Charges n).Charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
    simp only [HSMul.hSMul, SMul.smul, eq_ratCast, Rat.cast_eq_id, id_eq]
    rw [← Finset.mul_sum]

/-- The symmetric trilinear form used to define the cubic anomaly. -/
@[simps!]
def accCubeTriLinSymm {n : ℕ} : TriLinearSymm (PureU1Charges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, S.1 i * S.2.1 i * S.2.2 i)
  (by
    intro a S L T
    simp only [PureU1Charges_numberCharges, HSMul.hSMul, ACCSystemCharges.chargesModule_smul]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S L T R
    simp only [PureU1Charges_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add]
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S L T
    simp only [PureU1Charges_numberCharges]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S L T
    simp only [PureU1Charges_numberCharges]
    apply Fintype.sum_congr
    intro i
    ring)

/-- The cubic anomaly equation. -/
@[simp]
def accCube (n : ℕ) : HomogeneousCubic ((PureU1Charges n).Charges) :=
  (accCubeTriLinSymm).toCubic

/-- The cubic ACC for the pure-`U(1)` anomaly equations is equal to the sum of the cubed
  charges. -/
lemma accCube_explicit (n : ℕ) (S : (PureU1Charges n).Charges) :
    accCube n S = ∑ i : Fin n, S i ^ 3:= by
  rw [accCube, TriLinearSymm.toCubic]
  change accCubeTriLinSymm S S S = _
  rw [accCubeTriLinSymm]
  simp only [PureU1Charges_numberCharges, TriLinearSymm.mk₃_toFun_apply_apply]
  exact Finset.sum_congr rfl fun x _ => Eq.symm (pow_three' (S x))

end PureU1

/-- The ACC system for a pure $U(1)$ gauge theory with $n$ fermions. -/
@[simps!]
def PureU1 (n : ℕ) : ACCSystem where
  numberCharges := n
  numberLinear := 1
  linearACCs := fun i =>
    match i with
    | 0 => PureU1.accGrav n
  numberQuadratic := 0
  quadraticACCs := Fin.elim0
  cubicACC := PureU1.accCube n

/-- An equivalence of vector spaces of charges when the number of fermions is equal. -/
def pureU1EqCharges {n m : ℕ} (h : n = m) :
    (PureU1 n).Charges ≃ₗ[ℚ] (PureU1 m).Charges where
  toFun f := f ∘ Fin.cast h.symm
  invFun f := f ∘ Fin.cast h
  map_add' _ _ := rfl
  map_smul' _ _:= rfl
  left_inv _ := rfl
  right_inv _ := rfl

open BigOperators

/-- A solution to the pure U(1) accs satisfies the linear ACCs. -/
lemma pureU1_linear {n : ℕ} (S : (PureU1 n).LinSols) :
    ∑ (i : Fin n), S.val i = 0 := by
  have hS := S.linearSol
  simp only [PureU1_numberLinear, PureU1_linearACCs] at hS
  exact hS 0

/-- A solution to the pure U(1) accs satisfies the cubic ACCs. -/
lemma pureU1_cube {n : ℕ} (S : (PureU1 n).Sols) :
    ∑ i, (S.val i) ^ 3 = 0 := by
  rw [← PureU1.accCube_explicit]
  exact S.cubicSol

/-- The last charge of a solution to the linear ACCs is equal to the negation of the sum
  of the other charges. -/
lemma pureU1_last {n : ℕ} (S : (PureU1 n.succ).LinSols) :
    S.val (Fin.last n) = - ∑ i : Fin n, S.val i.castSucc := by
  have hS := pureU1_linear S
  simp only [succ_eq_add_one] at hS
  rw [Fin.sum_univ_castSucc] at hS
  linear_combination hS

/-- Two solutions to the Linear ACCs for `n.succ` are equal if their first `n` charges are
  equal. -/
lemma pureU1_anomalyFree_ext {n : ℕ} {S T : (PureU1 n.succ).LinSols}
    (h : ∀ (i : Fin n), S.val i.castSucc = T.val i.castSucc) : S = T := by
  apply ACCSystemLinear.LinSols.ext
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with hi | hi
  · obtain ⟨j, hj⟩ := hi
    subst hj
    exact h j
  · rw [hi, pureU1_last, pureU1_last]
    exact neg_inj.mpr (Finset.sum_congr rfl fun j _ => h j)

namespace PureU1

/-- The `j`th charge of a sum of pure-`U(1)` charges is equal to the sum of
  their `j`th charges. -/
lemma sum_of_charges {n : ℕ} (f : Fin k → (PureU1 n).Charges) (j : Fin n) :
    (∑ i : Fin k, (f i)) j = ∑ i : Fin k, (f i) j := by
  induction k
  · rfl
  · rename_i k hl
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    erw [← hl (f ∘ Fin.castSucc)]
    rfl

/-- The `j`th charge of a sum of solutions to the linear ACC is equal to the sum of
  their `j`th charges. -/
lemma sum_of_anomaly_free_linear {n : ℕ} (f : Fin k → (PureU1 n).LinSols) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) := by
  induction k
  · rfl
  · rename_i k hl
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    erw [← hl (f ∘ Fin.castSucc)]
    rfl

end PureU1
