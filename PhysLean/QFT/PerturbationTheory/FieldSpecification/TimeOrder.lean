/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldSpecification.CrAnSection
import PhysLean.QFT.PerturbationTheory.FieldSpecification.NormalOrder
/-!

# Time ordering of states

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-!

## Time ordering for states

-/

/-- The time ordering relation on states. We have that `timeOrderRel φ0 φ1` is true
  if and only if `φ1` has a time less-then or equal to `φ0`, or `φ1` is a negative
  asymptotic state, or `φ0` is a positive asymptotic state. -/
def timeOrderRel : 𝓕.FieldOp → 𝓕.FieldOp → Prop
  | FieldOp.outAsymp _, _ => True
  | FieldOp.position φ0, FieldOp.position φ1 => φ1.2 (Sum.inl 0) ≤ φ0.2 (Sum.inl 0)
  | FieldOp.position _, FieldOp.inAsymp _ => True
  | FieldOp.position _, FieldOp.outAsymp _ => False
  | FieldOp.inAsymp _, FieldOp.outAsymp _ => False
  | FieldOp.inAsymp _, FieldOp.position _ => False
  | FieldOp.inAsymp _, FieldOp.inAsymp _ => True

/-- The relation `timeOrderRel` is decidable, but not computable so due to
  `Real.decidableLE`. -/
noncomputable instance : (φ φ' : 𝓕.FieldOp) → Decidable (timeOrderRel φ φ')
  | FieldOp.outAsymp _, _ => isTrue True.intro
  | FieldOp.position φ0, FieldOp.position φ1 => inferInstanceAs
    (Decidable (φ1.2 (Sum.inl 0) ≤ φ0.2 (Sum.inl 0)))
  | FieldOp.position _, FieldOp.inAsymp _ => isTrue True.intro
  | FieldOp.position _, FieldOp.outAsymp _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.outAsymp _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.position _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.inAsymp _ => isTrue True.intro

/-- Time ordering is total. -/
instance : Std.Total 𝓕.timeOrderRel where
  total a b := by
    cases a <;> cases b <;>
      simp only [or_self, or_false, or_true, timeOrderRel, Fin.isValue]
    exact LinearOrder.le_total _ _

/-- Time ordering is transitive. -/
instance : IsTrans 𝓕.FieldOp 𝓕.timeOrderRel where
  trans a b c := by
    cases a <;> cases b <;> cases c <;>
      simp only [timeOrderRel, Fin.isValue, implies_true, imp_self, IsEmpty.forall_iff]
    exact fun h1 h2 => Preorder.le_trans _ _ _ h2 h1

noncomputable section

open FieldStatistic
open PhysLean.List

/-- Given a list `φ :: φs` of states, the (zero-based) position of the state which is
  of maximum time. For example
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `1`.
  This is defined for a list `φ :: φs` instead of `φs` to ensure that such a position exists.
-/
def maxTimeFieldPos (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : ℕ :=
  insertionSortMinPos timeOrderRel φ φs

lemma maxTimeFieldPos_lt_length (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    maxTimeFieldPos φ φs < (φ :: φs).length := by
  simp only [maxTimeFieldPos, List.length_cons, Order.lt_add_one_iff]
  exact Fin.is_le (insertionSortMinPos timeOrderRel φ φs)

/-- Given a list `φ :: φs` of states, the left-most state of maximum time, if there are more.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `φ2(t = 5)`.
  It is the state at the position `maxTimeFieldPos φ φs`.
-/
def maxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : 𝓕.FieldOp :=
  insertionSortMin timeOrderRel φ φs

/-- Given a list `φ :: φs` of states, the list with the left-most state of maximum
  time removed.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return
    `[φ1(t = 4), φ3(t = 3), φ4(t = 5)]`.
-/
def eraseMaxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : List 𝓕.FieldOp :=
  insertionSortDropMinPos timeOrderRel φ φs

@[simp]
lemma eraseMaxTimeField_length (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    (eraseMaxTimeField φ φs).length = φs.length := by
  simp [eraseMaxTimeField, insertionSortDropMinPos, eraseIdx_length']

lemma maxTimeFieldPos_lt_eraseMaxTimeField_length_succ (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    maxTimeFieldPos φ φs < (eraseMaxTimeField φ φs).length.succ := by
  simp only [eraseMaxTimeField_length, Nat.succ_eq_add_one]
  exact maxTimeFieldPos_lt_length φ φs

/-- Given a list `φ :: φs` of states, the position of the left-most state of maximum
  time as an element of `Fin (eraseMaxTimeField φ φs).length.succ`.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `⟨1,...⟩`.
-/
def maxTimeFieldPosFin (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    Fin (eraseMaxTimeField φ φs).length.succ :=
  insertionSortMinPosFin timeOrderRel φ φs

lemma lt_maxTimeFieldPosFin_not_timeOrder (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin (eraseMaxTimeField φ φs).length)
    (hi : (maxTimeFieldPosFin φ φs).succAbove i < maxTimeFieldPosFin φ φs) :
    ¬ timeOrderRel ((eraseMaxTimeField φ φs)[i.val]) (maxTimeField φ φs) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt timeOrderRel φ φs i hi

lemma timeOrder_maxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin (eraseMaxTimeField φ φs).length) :
    timeOrderRel (maxTimeField φ φs) ((eraseMaxTimeField φ φs)[i.val]) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos timeOrderRel φ φs _

/-- The sign associated with putting a list of states into time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def timeOrderSign (φs : List 𝓕.FieldOp) : ℂ :=
  Wick.koszulSign 𝓕.fieldOpStatistic 𝓕.timeOrderRel φs

@[simp]
lemma timeOrderSign_nil : timeOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp only [timeOrderSign]
  rfl

lemma timeOrderSign_pair_ordered {φ ψ : 𝓕.FieldOp} (h : timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 1 := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, ite_eq_left_iff,
    ite_eq_right_iff, and_imp]
  exact fun h' => False.elim (h' h)

lemma timeOrderSign_pair_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, instCommGroup.eq_1]
  rw [if_neg h]
  simp [FieldStatistic.exchangeSign_eq_if]

lemma timerOrderSign_of_eraseMaxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    timeOrderSign (eraseMaxTimeField φ φs) = timeOrderSign (φ :: φs) *
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) := by
  rw [eraseMaxTimeField, insertionSortDropMinPos, timeOrderSign,
    Wick.koszulSign_eraseIdx_insertionSortMinPos]
  rw [← timeOrderSign, ← maxTimeField]
  rfl

/-- The time ordering of a list of states. A schematic example is:
  - `normalOrderList [φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` is equal to
    `[φ2(t = 5), φ4(t = 5), φ1(t = 4), φ3(t = 3)]` -/
def timeOrderList (φs : List 𝓕.FieldOp) : List 𝓕.FieldOp :=
  List.insertionSort 𝓕.timeOrderRel φs

lemma timeOrderList_pair_ordered {φ ψ : 𝓕.FieldOp} (h : timeOrderRel φ ψ) :
    timeOrderList [φ, ψ] = [φ, ψ] := by
  simp only [timeOrderList, List.insertionSort_cons, List.insertionSort_nil, List.orderedInsert,
    ite_eq_left_iff, List.cons.injEq, and_true]
  exact fun h' => False.elim (h' h)

lemma timeOrderList_pair_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    timeOrderList [φ, ψ] = [ψ, φ] := by
  simp only [timeOrderList, List.insertionSort_cons, List.insertionSort_nil, List.orderedInsert,
    ite_eq_right_iff, List.cons.injEq, and_true]
  exact fun h' => False.elim (h h')

@[simp]
lemma timeOrderList_nil : timeOrderList (𝓕 := 𝓕) [] = [] := by
  simp [timeOrderList]

lemma timeOrderList_eq_maxTimeField_timeOrderList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    timeOrderList (φ :: φs) = maxTimeField φ φs :: timeOrderList (eraseMaxTimeField φ φs) := by
  exact insertionSort_eq_insertionSortMin_cons timeOrderRel φ φs

/-!

## Time ordering for CrAnFieldOp

-/

/-!

## timeOrderRel

-/

/-- For a field specification `𝓕`, `𝓕.crAnTimeOrderRel` is a relation on
  `𝓕.CrAnFieldOp` representing time ordering.
  It is defined such that `𝓕.crAnTimeOrderRel φ₀ φ₁` is true if and only if one of the following
  holds
- `φ₀` is an *outgoing* asymptotic operator
- `φ₁` is an *incoming* asymptotic field operator
- `φ₀` and `φ₁` are both position field operators where
  the `SpaceTime` point of `φ₀` has a time *greater* than or equal to that of `φ₁`.

Thus, colloquially `𝓕.crAnTimeOrderRel φ₀ φ₁` if `φ₀` has time *greater* than or equal to `φ₁`.
The use of *greater* than rather then *less* than is because on ordering lists of operators
it is needed that the operator with the greatest time is to the left.
-/
def crAnTimeOrderRel (a b : 𝓕.CrAnFieldOp) : Prop := 𝓕.timeOrderRel a.1 b.1

/-- The relation `crAnTimeOrderRel` is decidable, but not computable so due to
  `Real.decidableLE`. -/
noncomputable instance (φ φ' : 𝓕.CrAnFieldOp) : Decidable (crAnTimeOrderRel φ φ') :=
  inferInstanceAs (Decidable (𝓕.timeOrderRel φ.1 φ'.1))

/-- Time ordering of `CrAnFieldOp` is total. -/
instance : Std.Total 𝓕.crAnTimeOrderRel where
  total a b := Std.Total.total (r := 𝓕.timeOrderRel) a.1 b.1

/-- Time ordering of `CrAnFieldOp` is transitive. -/
instance : IsTrans 𝓕.CrAnFieldOp 𝓕.crAnTimeOrderRel where
  trans a b c := IsTrans.trans (r := 𝓕.timeOrderRel) a.1 b.1 c.1

@[simp]
lemma crAnTimeOrderRel_refl (φ : 𝓕.CrAnFieldOp) : crAnTimeOrderRel φ φ := by
  exact (Std.Total.to_refl (r := 𝓕.crAnTimeOrderRel)).refl φ

/-- For a field specification `𝓕`, and a list `φs` of `𝓕.CrAnFieldOp`,
  `𝓕.crAnTimeOrderSign φs` is the sign corresponding to the number of `ferimionic`-`fermionic`
  exchanges undertaken to time-order (i.e. order with respect to `𝓕.crAnTimeOrderRel`) `φs` using
  the insertion sort algorithm. -/
def crAnTimeOrderSign (φs : List 𝓕.CrAnFieldOp) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.crAnTimeOrderRel φs

@[simp]
lemma crAnTimeOrderSign_nil : crAnTimeOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp only [crAnTimeOrderSign]
  rfl

lemma crAnTimeOrderSign_pair_ordered {φ ψ : 𝓕.CrAnFieldOp} (h : crAnTimeOrderRel φ ψ) :
    crAnTimeOrderSign [φ, ψ] = 1 := by
  simp only [crAnTimeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, ite_eq_left_iff,
    ite_eq_right_iff, and_imp]
  exact fun h' => False.elim (h' h)

lemma crAnTimeOrderSign_pair_not_ordered {φ ψ : 𝓕.CrAnFieldOp} (h : ¬ crAnTimeOrderRel φ ψ) :
    crAnTimeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) := by
  simp only [crAnTimeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, instCommGroup.eq_1]
  rw [if_neg h]
  simp [FieldStatistic.exchangeSign_eq_if]

lemma crAnTimeOrderSign_swap_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (h1 : crAnTimeOrderRel φ ψ) (h2 : crAnTimeOrderRel ψ φ) (φs φs' : List 𝓕.CrAnFieldOp) :
    crAnTimeOrderSign (φs ++ φ :: ψ :: φs') = crAnTimeOrderSign (φs ++ ψ :: φ :: φs') := by
  exact Wick.koszulSign_swap_eq_rel _ _ h1 h2 _ _

/-- For a field specification `𝓕`, and a list `φs` of `𝓕.CrAnFieldOp`,
  `𝓕.crAnTimeOrderList φs` is the list `φs` time-ordered using the insertion sort algorithm. -/
def crAnTimeOrderList (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.insertionSort 𝓕.crAnTimeOrderRel φs

@[simp]
lemma crAnTimeOrderList_nil : crAnTimeOrderList (𝓕 := 𝓕) [] = [] := by
  simp [crAnTimeOrderList]

lemma crAnTimeOrderList_pair_ordered {φ ψ : 𝓕.CrAnFieldOp} (h : crAnTimeOrderRel φ ψ) :
    crAnTimeOrderList [φ, ψ] = [φ, ψ] := by
  simp only [crAnTimeOrderList, List.insertionSort_cons, List.insertionSort_nil, List.orderedInsert,
    ite_eq_left_iff, List.cons.injEq, and_true]
  exact fun h' => False.elim (h' h)

lemma crAnTimeOrderList_pair_not_ordered {φ ψ : 𝓕.CrAnFieldOp} (h : ¬ crAnTimeOrderRel φ ψ) :
    crAnTimeOrderList [φ, ψ] = [ψ, φ] := by
  simp only [crAnTimeOrderList, List.insertionSort_cons, List.insertionSort_nil, List.orderedInsert,
    ite_eq_right_iff, List.cons.injEq, and_true]
  exact fun h' => False.elim (h h')

lemma orderedInsert_swap_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (h1 : crAnTimeOrderRel φ ψ) (h2 : crAnTimeOrderRel ψ φ) (φs : List 𝓕.CrAnFieldOp) :
    List.orderedInsert crAnTimeOrderRel φ (List.orderedInsert crAnTimeOrderRel ψ φs) =
    List.takeWhile (fun b => ¬ crAnTimeOrderRel ψ b) φs ++ φ :: ψ ::
    List.dropWhile (fun b => ¬ crAnTimeOrderRel ψ b) φs := by
  rw [List.orderedInsert_eq_take_drop crAnTimeOrderRel ψ φs]
  simp only [decide_not]
  rw [List.orderedInsert_eq_take_drop]
  simp only [decide_not]
  have h1 (b : 𝓕.CrAnFieldOp) : (crAnTimeOrderRel φ b) ↔ (crAnTimeOrderRel ψ b) :=
    Iff.intro (fun h => IsTrans.trans _ _ _ h2 h) (fun h => IsTrans.trans _ _ _ h1 h)
  simp only [h1]
  rw [List.takeWhile_append]
  rw [List.takeWhile_takeWhile]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, and_self, decide_not,
    ↓reduceIte, crAnTimeOrderRel_refl, decide_true, Bool.false_eq_true, not_false_eq_true,
    List.takeWhile_cons_of_neg, List.append_nil, List.append_cancel_left_eq, List.cons.injEq,
    true_and]
  rw [List.dropWhile_append]
  simp only [List.isEmpty_iff, List.dropWhile_eq_nil_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, crAnTimeOrderRel_refl, decide_true, Bool.false_eq_true,
    not_false_eq_true, List.dropWhile_cons_of_neg, ite_eq_left_iff, not_forall, Decidable.not_not,
    List.append_left_eq_self, forall_exists_index]
  intro x hx hxψ y hy
  simpa using List.mem_takeWhile_imp hy

lemma orderedInsert_in_swap_eq_time {φ ψ φ': 𝓕.CrAnFieldOp} (h1 : crAnTimeOrderRel φ ψ)
    (h2 : crAnTimeOrderRel ψ φ) : (φs φs' : List 𝓕.CrAnFieldOp) → ∃ l1 l2,
    List.orderedInsert crAnTimeOrderRel φ' (φs ++ φ :: ψ :: φs') = l1 ++ φ :: ψ :: l2 ∧
    List.orderedInsert crAnTimeOrderRel φ' (φs ++ ψ :: φ :: φs') = l1 ++ ψ :: φ :: l2
  | [], φs' => by
    have h1 (b : 𝓕.CrAnFieldOp) : (crAnTimeOrderRel b φ) ↔ (crAnTimeOrderRel b ψ) :=
      Iff.intro (fun h => IsTrans.trans _ _ _ h h1) (fun h => IsTrans.trans _ _ _ h h2)
    by_cases h : crAnTimeOrderRel φ' φ
    · simp only [List.nil_append, List.orderedInsert, h, ↓reduceIte, ← h1 φ']
      use [φ'], φs'
      simp
    · simp only [List.nil_append, List.orderedInsert, h, ↓reduceIte, ← h1 φ']
      use [], List.orderedInsert crAnTimeOrderRel φ' φs'
      simp
  | φ'' :: φs, φs' => by
    obtain ⟨l1, l2, hl⟩ := orderedInsert_in_swap_eq_time (φ' := φ') h1 h2 φs φs'
    simp only [List.cons_append, List.orderedInsert]
    rw [hl.1, hl.2]
    by_cases h : crAnTimeOrderRel φ' φ''
    · simp only [h, ↓reduceIte]
      use (φ' :: φ'' :: φs), φs'
      simp
    · simp only [h, ↓reduceIte]
      use (φ'' :: l1), l2
      simp

lemma crAnTimeOrderList_swap_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (h1 : crAnTimeOrderRel φ ψ) (h2 : crAnTimeOrderRel ψ φ) :
    (φs φs' : List 𝓕.CrAnFieldOp) →
    ∃ (l1 l2 : List 𝓕.CrAnFieldOp),
      crAnTimeOrderList (φs ++ φ :: ψ :: φs') = l1 ++ φ :: ψ :: l2 ∧
      crAnTimeOrderList (φs ++ ψ :: φ :: φs') = l1 ++ ψ :: φ :: l2
  | [], φs' => by
    simp only [crAnTimeOrderList]
    simp only [List.nil_append, List.insertionSort]
    use List.takeWhile (fun b => ¬ crAnTimeOrderRel ψ b) (List.insertionSort crAnTimeOrderRel φs'),
      List.dropWhile (fun b => ¬ crAnTimeOrderRel ψ b) (List.insertionSort crAnTimeOrderRel φs')
    apply And.intro
    · exact orderedInsert_swap_eq_time h1 h2 _
    · have h1' (b : 𝓕.CrAnFieldOp) : (crAnTimeOrderRel φ b) ↔ (crAnTimeOrderRel ψ b) :=
        Iff.intro (fun h => IsTrans.trans _ _ _ h2 h) (fun h => IsTrans.trans _ _ _ h1 h)
      simp only [← h1', decide_not]
      simpa using orderedInsert_swap_eq_time h2 h1 _
  | φ'' :: φs, φs' => by
    rw [crAnTimeOrderList, crAnTimeOrderList]
    simp only [List.cons_append, List.insertionSort_cons]
    obtain ⟨l1, l2, hl⟩ := crAnTimeOrderList_swap_eq_time h1 h2 φs φs'
    simp only [crAnTimeOrderList] at hl
    rw [hl.1, hl.2]
    obtain ⟨l1', l2', hl'⟩ := orderedInsert_in_swap_eq_time (φ' := φ'') h1 h2 l1 l2
    rw [hl'.1, hl'.2]
    use l1', l2'

/-!

## Relationship to sections
-/

lemma koszulSignInsert_crAnTimeOrderRel_crAnSection {φ : 𝓕.FieldOp} {ψ : 𝓕.CrAnFieldOp}
    (h : ψ.1 = φ) : {φs : List 𝓕.FieldOp} → (ψs : CrAnSection φs) →
    Wick.koszulSignInsert 𝓕.crAnStatistics 𝓕.crAnTimeOrderRel ψ ψs.1 =
    Wick.koszulSignInsert 𝓕.fieldOpStatistic 𝓕.timeOrderRel φ φs
  | [], ⟨[], h⟩ => by
    simp [Wick.koszulSignInsert]
  | φ' :: φs, ⟨ψ' :: ψs, h1⟩ => by
    simp only [Wick.koszulSignInsert, crAnTimeOrderRel, h]
    simp only [List.map_cons, List.cons.injEq] at h1
    have hi := koszulSignInsert_crAnTimeOrderRel_crAnSection h (φs := φs) ⟨ψs, h1.2⟩
    rw [hi]
    congr
    · exact h1.1
    · simp only [crAnStatistics, crAnFieldOpToFieldOp, Function.comp_apply]
      congr
    · simp only [crAnStatistics, crAnFieldOpToFieldOp, Function.comp_apply]
      congr
      exact h1.1

@[simp]
lemma crAnTimeOrderSign_crAnSection : {φs : List 𝓕.FieldOp} → (ψs : CrAnSection φs) →
    crAnTimeOrderSign ψs.1 = timeOrderSign φs
  | [], ⟨[], h⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩ => by
    simp only [crAnTimeOrderSign, Wick.koszulSign, timeOrderSign]
    simp only [List.map_cons, List.cons.injEq] at h
    congr 1
    · rw [koszulSignInsert_crAnTimeOrderRel_crAnSection h.1 ⟨ψs, h.2⟩]
    · exact crAnTimeOrderSign_crAnSection ⟨ψs, h.2⟩

lemma orderedInsert_crAnTimeOrderRel_crAnSection {φ : 𝓕.FieldOp} {ψ : 𝓕.CrAnFieldOp}
    (h : ψ.1 = φ) : {φs : List 𝓕.FieldOp} → (ψs : CrAnSection φs) →
    (List.orderedInsert 𝓕.crAnTimeOrderRel ψ ψs.1).map 𝓕.crAnFieldOpToFieldOp =
    List.orderedInsert 𝓕.timeOrderRel φ φs
  | [], ⟨[], _⟩ => by
    simp only [List.orderedInsert, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact h
  | φ' :: φs, ⟨ψ' :: ψs, h1⟩ => by
    simp only [List.orderedInsert, crAnTimeOrderRel, h]
    simp only [List.map_cons, List.cons.injEq] at h1
    by_cases hr : timeOrderRel φ φ'
    · simp only [hr, ↓reduceIte]
      rw [← h1.1] at hr
      simp only [crAnFieldOpToFieldOp] at hr
      simp only [hr, ↓reduceIte, List.map_cons, List.cons.injEq]
      exact And.intro h (And.intro h1.1 h1.2)
    · simp only [hr, ↓reduceIte]
      rw [← h1.1] at hr
      simp only [crAnFieldOpToFieldOp] at hr
      simp only [hr, ↓reduceIte, List.map_cons, List.cons.injEq]
      apply And.intro h1.1
      exact orderedInsert_crAnTimeOrderRel_crAnSection h ⟨ψs, h1.2⟩

lemma crAnTimeOrderList_crAnSection_is_crAnSection : {φs : List 𝓕.FieldOp} → (ψs : CrAnSection φs) →
    (crAnTimeOrderList ψs.1).map 𝓕.crAnFieldOpToFieldOp = timeOrderList φs
  | [], ⟨[], h⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩ => by
    simp only [crAnTimeOrderList, List.insertionSort, timeOrderList]
    simp only [List.map_cons, List.cons.injEq] at h
    exact orderedInsert_crAnTimeOrderRel_crAnSection h.1 ⟨(List.insertionSort crAnTimeOrderRel ψs),
      crAnTimeOrderList_crAnSection_is_crAnSection ⟨ψs, h.2⟩⟩

/-- Time ordering of sections of a list of states. -/
def crAnSectionTimeOrder (φs : List 𝓕.FieldOp) (ψs : CrAnSection φs) :
    CrAnSection (timeOrderList φs) :=
  ⟨crAnTimeOrderList ψs.1, crAnTimeOrderList_crAnSection_is_crAnSection ψs⟩

lemma orderedInsert_crAnTimeOrderRel_injective {ψ ψ' : 𝓕.CrAnFieldOp} (h : ψ.1 = ψ'.1) :
    {φs : List 𝓕.FieldOp} → (ψs ψs' : 𝓕.CrAnSection φs) →
    (ho : List.orderedInsert crAnTimeOrderRel ψ ψs.1 =
    List.orderedInsert crAnTimeOrderRel ψ' ψs'.1) → ψ = ψ' ∧ ψs = ψs'
  | [], ⟨[], _⟩, ⟨[], _⟩, h => by
    simp only [List.orderedInsert, List.cons.injEq, and_true] at h
    simpa using h
  | φ :: φs, ⟨ψ1 :: ψs, h1⟩, ⟨ψ1' :: ψs', h1'⟩, ho => by
    simp only [List.map_cons, List.cons.injEq] at h1 h1'
    have ih := orderedInsert_crAnTimeOrderRel_injective h ⟨ψs, h1.2⟩ ⟨ψs', h1'.2⟩
    simp only [List.orderedInsert] at ho
    by_cases hr : crAnTimeOrderRel ψ ψ1
    · simp_all only [ite_true]
      by_cases hr2 : crAnTimeOrderRel ψ' ψ1'
      · simp_all
      · simp only [crAnTimeOrderRel] at hr hr2
        simp_all only
        rw [crAnFieldOpToFieldOp] at h1 h1'
        rw [h1.1] at hr
        rw [h1'.1] at hr2
        exact False.elim (hr2 hr)
    · simp_all only [ite_false]
      by_cases hr2 : crAnTimeOrderRel ψ' ψ1'
      · simp only [crAnTimeOrderRel] at hr hr2
        simp_all only
        rw [crAnFieldOpToFieldOp] at h1 h1'
        rw [h1.1] at hr
        rw [h1'.1] at hr2
        exact False.elim (hr hr2)
      · simp only [hr2, ↓reduceIte, List.cons.injEq] at ho
        have ih' := ih ho.2
        simp_all only [and_self, implies_true, not_false_eq_true, true_and]
        apply Subtype.ext
        simp only [List.cons.injEq, true_and]
        rw [Subtype.ext_iff] at ih'
        exact ih'.2

lemma crAnSectionTimeOrder_injective : {φs : List 𝓕.FieldOp} →
    Function.Injective (𝓕.crAnSectionTimeOrder φs)
  | [], ⟨[], _⟩, ⟨[], _⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩, ⟨ψ' :: ψs', h'⟩ => by
    intro h1
    apply Subtype.ext
    simp only [List.cons.injEq]
    simp only [crAnSectionTimeOrder] at h1
    rw [Subtype.ext_iff] at h1
    simp only [crAnTimeOrderList, List.insertionSort] at h1
    simp only [List.map_cons, List.cons.injEq] at h h'
    rw [crAnFieldOpToFieldOp] at h h'
    have hin := orderedInsert_crAnTimeOrderRel_injective (by rw [h.1, h'.1])
      (𝓕.crAnSectionTimeOrder φs ⟨ψs, h.2⟩)
      (𝓕.crAnSectionTimeOrder φs ⟨ψs', h'.2⟩) h1
    apply And.intro hin.1
    have hl := crAnSectionTimeOrder_injective hin.2
    rw [Subtype.ext_iff] at hl
    simpa using hl

lemma crAnSectionTimeOrder_bijective (φs : List 𝓕.FieldOp) :
    Function.Bijective (𝓕.crAnSectionTimeOrder φs) := by
  rw [Fintype.bijective_iff_injective_and_card]
  apply And.intro crAnSectionTimeOrder_injective
  apply CrAnSection.card_perm_eq
  simp only [timeOrderList]
  exact List.Perm.symm (List.perm_insertionSort timeOrderRel φs)

lemma sum_crAnSections_timeOrder {φs : List 𝓕.FieldOp} [AddCommMonoid M]
    (f : CrAnSection (timeOrderList φs) → M) : ∑ s, f s = ∑ s, f (𝓕.crAnSectionTimeOrder φs s) := by
  erw [(Equiv.ofBijective _ (𝓕.crAnSectionTimeOrder_bijective φs)).sum_comp]

/-!

## normTimeOrderRel

-/

/-- The time ordering relation on `CrAnFieldOp` such that if two CrAnFieldOp have the same
  time, we normal order them. -/
def normTimeOrderRel (a b : 𝓕.CrAnFieldOp) : Prop :=
  crAnTimeOrderRel a b ∧ (crAnTimeOrderRel b a → normalOrderRel a b)

/-- The relation `normTimeOrderRel` is decidable, but not computable so due to
  `Real.decidableLE`. -/
noncomputable instance (φ φ' : 𝓕.CrAnFieldOp) : Decidable (normTimeOrderRel φ φ') :=
  instDecidableAnd

/-- Norm-Time ordering of `CrAnFieldOp` is total. -/
instance : Std.Total 𝓕.normTimeOrderRel where
  total a b := by
    simp only [normTimeOrderRel]
    match Std.Total.total (r := 𝓕.crAnTimeOrderRel) a b,
      Std.Total.total (r := 𝓕.normalOrderRel) a b with
    | Or.inl h1, Or.inl h2 => simp [h1, h2]
    | Or.inr h1, Or.inl h2 =>
      simp only [h1, h2, imp_self, and_true, true_and]
      by_cases hn : crAnTimeOrderRel a b
      · simp [hn]
      · simp [hn]
    | Or.inl h1, Or.inr h2 =>
      simp only [h1, true_and, h2, imp_self, and_true]
      by_cases hn : crAnTimeOrderRel b a
      · simp [hn]
      · simp [hn]
    | Or.inr h1, Or.inr h2 => simp [h1, h2]

/-- Norm-Time ordering of `CrAnFieldOp` is transitive. -/
instance : IsTrans 𝓕.CrAnFieldOp 𝓕.normTimeOrderRel where
  trans a b c := by
    intro h1 h2
    simp_all only [normTimeOrderRel]
    apply And.intro
    · exact IsTrans.trans _ _ _ h1.1 h2.1
    · intro hc
      refine IsTrans.trans _ _ _ (h1.2 ?_) (h2.2 ?_)
      · exact IsTrans.trans _ _ _ h2.1 hc
      · exact IsTrans.trans _ _ _ hc h1.1

/-- The sign associated with putting a list of `CrAnFieldOp` into normal-time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def normTimeOrderSign (φs : List 𝓕.CrAnFieldOp) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.normTimeOrderRel φs

/-- Sort a list of `CrAnFieldOp` based on `normTimeOrderRel`. -/
def normTimeOrderList (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.insertionSort 𝓕.normTimeOrderRel φs

end
end FieldSpecification
