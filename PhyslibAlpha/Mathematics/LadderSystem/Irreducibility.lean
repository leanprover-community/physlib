/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.Mathematics.LadderSystem.OccupationBasis
/-!

# Irreducibility of the excitation-number sector

## i. Overview

`LadderSystem.vacuumSpan L Ω n` is `gl(d)`-irreducible: the only submodules of `vacuumSpan L Ω n`
invariant under every `E i j` are `⊥` and `vacuumSpan L Ω n` itself. Completeness in an ambient
Hilbert space is a separate analytic question. The proof uses linear algebra over a field of
characteristic zero.

## ii. Key results

- `LadderSystem.vacuumSpan_eq_of_ne_bot` : a nonzero `E i j`-invariant submodule of
    `vacuumSpan L Ω n` is all of `vacuumSpan L Ω n`.

## iii. Table of contents

- A. Moving a quantum between modes
- B. Extracting a single basis vector from an invariant submodule
- C. Connectivity: one basis vector reaches every other
- D. Irreducibility

## iv. References

* None.
-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LadderSystem

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {d : ℕ}
    (L : LadderSystem K V d)

/-!

## A. Moving a quantum between modes

-/

/-- `α` with one quantum moved from color `j` to color `i`. Only meaningful for `i ≠ j`; the
degenerate `i = j` case is handled separately by `N_word`. -/
def moveOneTo (α : Fin d → ℕ) (i j : Fin d) : Fin d → ℕ :=
  fun c => if c = i then α i + 1 else if c = j then α j - 1 else α c

lemma countWord_moveOneTo_perm {i j : Fin d} (hij : i ≠ j) {α : Fin d → ℕ} :
    List.Perm (i :: (countWord d α).erase j) (countWord d (moveOneTo α i j)) := by
  rw [List.perm_iff_count]
  intro c
  rw [count_countWord]
  by_cases hci : c = i
  · subst hci
    rw [List.count_cons_self, List.count_erase_of_ne hij, count_countWord]
    simp [moveOneTo]
  · rw [List.count_cons_of_ne (Ne.symm hci)]
    by_cases hcj : c = j
    · subst hcj
      rw [List.count_erase_self, count_countWord]
      simp [moveOneTo, hci]
    · rw [List.count_erase_of_ne hcj, count_countWord]
      simp [moveOneTo, hci, hcj]

variable {L}

omit [CharZero K] in
/-- The transfer formula: `E i j` moves one quantum from color `j` to color `i`, scaled by
`j`'s occupation number. -/
lemma E_word_countWord {Ω : V} (P : L.HasVacuum Ω) {i j : Fin d} (hij : i ≠ j)
    {α : Fin d → ℕ} :
    L.E i j (L.word (countWord d α) Ω) =
      (α j : K) • L.word (countWord d (moveOneTo α i j)) Ω := by
  rw [Nat.cast_smul_eq_nsmul K, E_word L P.ann i j (countWord d α), count_countWord,
    word_perm L (countWord_moveOneTo_perm hij)]

/-!

## B. Extracting a single basis vector from an invariant submodule

-/

omit [CharZero K] in
/-- A submodule invariant under an endomorphism `M` is invariant under any polynomial in `M`. -/
lemma mapsTo_aeval {W : Submodule K V} {M : Module.End K V} (hW : ∀ w ∈ W, M w ∈ W)
    (p : Polynomial K) : ∀ w ∈ W, (Polynomial.aeval M p) w ∈ W := by
  refine p.induction_on ?_ ?_ ?_
  · intro a w hw
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact W.smul_mem a hw
  · intro p q hp hq w hw
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp w hw) (hq w hw)
  · intro k a hka w hw
    have heq : Polynomial.C a * Polynomial.X ^ (k + 1) =
        (Polynomial.C a * Polynomial.X ^ k) * Polynomial.X := by ring
    rw [heq, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact hka (M w) (hW w hw)

/-- A nonzero `E i j`-invariant submodule of `vacuumSpan L Ω n` contains an occupation-number
basis vector. A Lagrange-interpolation polynomial in the diagonal separator
`∑ᵢ(n+1)^i • Nᵢ` projects a nonzero element onto one of its basis components. -/
lemma exists_word_countWord_mem_of_ne_bot {Ω : V} (P : L.HasVacuum Ω) (n : ℕ)
    {W : Submodule K V} (hWle : W ≤ vacuumSpan L Ω n)
    (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) (hWbot : W ≠ ⊥) :
    ∃ α : CountFun d n, L.word (countWord d α.1) Ω ∈ W := by
  classical
  set M : Module.End K V := ∑ i : Fin d, ((n + 1 : K)) ^ (i : ℕ) • L.N i with hM
  have hWM : ∀ w ∈ W, M w ∈ W := by
    intro w hw
    rw [hM, LinearMap.sum_apply]
    refine Submodule.sum_mem W fun i _ => ?_
    rw [LinearMap.smul_apply]
    exact W.smul_mem _ (hWE i i w hw)
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hWbot
  have hwspan : w ∈ vacuumSpan L Ω n := hWle hwW
  set c := (vacuumBasis L P n).repr ⟨w, hwspan⟩ with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hw0
    have h' : (⟨w, hwspan⟩ : L.vacuumSpan Ω n) = 0 := by
      rw [hc] at h
      exact (vacuumBasis L P n).repr.map_eq_zero_iff.mp h
    simpa using congrArg Subtype.val h'
  obtain ⟨α₀, hα₀⟩ := Finsupp.support_nonempty_iff.mpr hc0
  set p : Polynomial K :=
    ∏ β ∈ (Finset.univ.erase α₀ : Finset (CountFun d n)),
      (Polynomial.X - Polynomial.C (countEncode n β.1 : K)) with hp
  have heval_ne : ∀ β : CountFun d n, β ≠ α₀ → p.eval (countEncode n β.1 : K) = 0 := by
    intro β hβ
    rw [hp, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hβ, Finset.mem_univ β⟩) ?_
    simp
  have heval_eq : p.eval (countEncode n α₀.1 : K) ≠ 0 := by
    rw [hp, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun β hβ => ?_
    have hβne : β ≠ α₀ := (Finset.mem_erase.mp hβ).1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro heq
    have heqn : countEncode n α₀.1 = countEncode n β.1 := by exact_mod_cast heq
    exact hβne (Subtype.ext (countEncode_injOn α₀.2 β.2 heqn)).symm
  have haeval : ∀ β : CountFun d n,
      (Polynomial.aeval M p) (L.word (countWord d β.1) Ω) =
        p.eval (countEncode n β.1 : K) • L.word (countWord d β.1) Ω :=
    fun β => Module.End.aeval_apply_of_hasEigenvector (hasEigenvector_word_countWord L P n β)
  have hwe : w = ∑ β : CountFun d n, c β • L.word (countWord d β.1) Ω := by
    have hsum := (vacuumBasis L P n).sum_repr (⟨w, hwspan⟩ : L.vacuumSpan Ω n)
    rw [← hc] at hsum
    have hval : (∑ β : CountFun d n, c β • (vacuumBasis L P n β : V)) = w := by
      simpa using congrArg Subtype.val hsum
    rw [← hval]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [vacuumBasis_apply]
  have hmem : (Polynomial.aeval M p) w ∈ W := mapsTo_aeval hWM p w hwW
  have hcompute : (Polynomial.aeval M p) w =
      (c α₀ * p.eval (countEncode n α₀.1 : K)) • L.word (countWord d α₀.1) Ω := by
    rw [hwe, map_sum]
    rw [Finset.sum_eq_single α₀]
    · rw [map_smul, haeval, smul_smul]
    · intro β _ hβne
      rw [map_smul, haeval, heval_ne β hβne, zero_smul, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ α₀) h
  rw [hcompute] at hmem
  refine ⟨α₀, ?_⟩
  have hne : c α₀ * p.eval (countEncode n α₀.1 : K) ≠ 0 :=
    mul_ne_zero (Finsupp.mem_support_iff.mp hα₀) heval_eq
  have := W.smul_mem (c α₀ * p.eval (countEncode n α₀.1 : K))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-!

## C. Connectivity: one basis vector reaches every other

-/

omit [CharZero K] in
/-- The total occupation number matches the length of the canonical word representing it. -/
lemma sum_eq_length_countWord (α : Fin d → ℕ) : (∑ c, α c) = (countWord d α).length := by
  rw [← sum_count_eq_length (countWord d α)]
  exact Finset.sum_congr rfl fun c _ => (count_countWord α c).symm

omit [CharZero K] in
/-- Moving one quantum between two modes preserves the total occupation number. -/
lemma sum_moveOneTo {i j : Fin d} (hij : i ≠ j) {α : Fin d → ℕ} (hj : α j ≠ 0) :
    (∑ c, moveOneTo α i j c) = ∑ c, α c := by
  have hcj : (countWord d α).count j ≠ 0 := by rw [count_countWord]; exact hj
  have hmem : j ∈ countWord d α := List.count_pos_iff.mp (Nat.pos_of_ne_zero hcj)
  rw [sum_eq_length_countWord, sum_eq_length_countWord,
    ← (countWord_moveOneTo_perm hij).length_eq, List.length_cons, List.length_erase_of_mem hmem]
  have := List.length_pos_of_mem hmem
  omega

omit [CharZero K] in
/-- `moveOneTo` at the color it moves quanta *into* just increments that color's count. -/
lemma moveOneTo_self (α : Fin d → ℕ) (i j : Fin d) : moveOneTo α i j i = α i + 1 := by
  show (if i = i then α i + 1 else if i = j then α j - 1 else α i) = α i + 1
  rw [ite_eq_left rfl]

omit [CharZero K] in
/-- Moving a quantum from `j` to `i` and then immediately back from `i` to `j` is the identity. -/
lemma moveOneTo_moveOneTo {i j : Fin d} (hij : i ≠ j) {α : Fin d → ℕ} (hj : α j ≠ 0) :
    moveOneTo (moveOneTo α i j) j i = α := by
  have hβj : moveOneTo α i j j = α j - 1 := by
    show (if j = i then α i + 1 else if j = j then α j - 1 else α j) = α j - 1
    rw [ite_eq_right (Ne.symm hij), ite_eq_left rfl]
  have hβi : moveOneTo α i j i = α i + 1 := moveOneTo_self α i j
  funext c
  show (if c = j then moveOneTo α i j j + 1 else if c = i then moveOneTo α i j i - 1
      else moveOneTo α i j c) = α c
  rcases eq_or_ne c j with rfl | hcj
  · rw [ite_eq_left rfl, hβj]
    omega
  · rw [ite_eq_right hcj]
    rcases eq_or_ne c i with rfl | hci
    · rw [ite_eq_left rfl, hβi]
      omega
    · rw [ite_eq_right hci]
      show (if c = i then α i + 1 else if c = j then α j - 1 else α c) = α c
      rw [ite_eq_right hci, ite_eq_right hcj]

/-- The atomic move: if `W` is `E i j`-invariant and contains the word for `β`, and mode `k`
is occupied, `W` also contains the word obtained by moving one quantum from `k` to any other
mode `l`. -/
lemma word_countWord_moveOneTo_mem {Ω : V} (P : L.HasVacuum Ω) {W : Submodule K V}
    (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) {β : Fin d → ℕ}
    (hmem : L.word (countWord d β) Ω ∈ W) {l k : Fin d} (hkl : l ≠ k) (hk : β k ≠ 0) :
    L.word (countWord d (moveOneTo β l k)) Ω ∈ W := by
  have hE : L.E l k (L.word (countWord d β) Ω) ∈ W := hWE l k _ hmem
  rw [E_word_countWord P hkl] at hE
  have hne : (β k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hsm := W.smul_mem (β k : K)⁻¹ hE
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hsm

/-- Every occupation-number word reaches the mode-`0` hub word, given `W`
is `E i j`-invariant and contains it. Proved by strong induction on the mass sitting outside
mode `0`. -/
lemma word_countWord_hub_mem_of_mem {hd : 0 < d} {Ω : V} (P : L.HasVacuum Ω)
    {W : Submodule K V} (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) :
    ∀ m : ℕ, ∀ α : Fin d → ℕ, (∑ c, α c) - α (⟨0, hd⟩ : Fin d) = m →
      L.word (countWord d α) Ω ∈ W →
      L.word (countWord d (fun c => if c = (⟨0, hd⟩ : Fin d) then (∑ c, α c) else 0)) Ω ∈ W := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α hdeficit hmem
    set hub0 := (⟨0, hd⟩ : Fin d)
    have hle0 : α hub0 ≤ ∑ c, α c := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ hub0)
    rcases eq_or_ne m 0 with rfl | hm0
    · have hα0 : α hub0 = ∑ c, α c := by omega
      have hα : α = (fun c => if c = hub0 then (∑ c, α c) else 0) := by
        have hsplit : α hub0 + ∑ c ∈ Finset.univ.erase hub0, α c = ∑ c, α c :=
          Finset.add_sum_erase _ α (Finset.mem_univ hub0)
        funext c
        by_cases hc : c = hub0
        · subst hc; rw [ite_eq_left rfl]; exact hα0
        · rw [ite_eq_right hc]
          have hle : α c ≤ ∑ c' ∈ Finset.univ.erase hub0, α c' :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
          omega
      rwa [← hα]
    · obtain ⟨j, hjne, hjpos⟩ : ∃ j : Fin d, j ≠ hub0 ∧ α j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hsplit : (∑ c, α c) = α hub0 :=
          Finset.sum_eq_single hub0 (fun c _ hc => hcon c hc)
            (fun h => absurd (Finset.mem_univ hub0) h)
        rw [hsplit, Nat.sub_self] at hdeficit
        exact hm0 hdeficit.symm
      have hstep := word_countWord_moveOneTo_mem P hWE hmem (Ne.symm hjne) hjpos
      have hsum' := sum_moveOneTo (Ne.symm hjne) hjpos (α := α)
      have hval : moveOneTo α hub0 j hub0 = α hub0 + 1 := moveOneTo_self α hub0 j
      have hdeficit' : (∑ c, moveOneTo α hub0 j c) - (moveOneTo α hub0 j) hub0 = m - 1 := by
        rw [hsum', hval]
        omega
      have := ih (m - 1) (by omega) (moveOneTo α hub0 j) hdeficit' hstep
      rwa [hsum'] at this

/-- The hub word reaches every occupation-number word, given `W` is `E i j`-invariant and
contains it. Proved by strong induction on the mass sitting outside mode `0` in the target. -/
lemma word_countWord_mem_of_hub_mem {hd : 0 < d} {Ω : V} (P : L.HasVacuum Ω)
    {W : Submodule K V} (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) :
    ∀ m : ℕ, ∀ α : Fin d → ℕ, (∑ c, α c) - α (⟨0, hd⟩ : Fin d) = m →
      L.word (countWord d (fun c => if c = (⟨0, hd⟩ : Fin d) then (∑ c, α c) else 0)) Ω ∈ W →
      L.word (countWord d α) Ω ∈ W := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α hdeficit hmem
    set hub0 := (⟨0, hd⟩ : Fin d)
    have hle0 : α hub0 ≤ ∑ c, α c := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ hub0)
    rcases eq_or_ne m 0 with rfl | hm0
    · have hα0 : α hub0 = ∑ c, α c := by omega
      have hα : α = (fun c => if c = hub0 then (∑ c, α c) else 0) := by
        have hsplit : α hub0 + ∑ c ∈ Finset.univ.erase hub0, α c = ∑ c, α c :=
          Finset.add_sum_erase _ α (Finset.mem_univ hub0)
        funext c
        by_cases hc : c = hub0
        · subst hc; rw [ite_eq_left rfl]; exact hα0
        · rw [ite_eq_right hc]
          have hle : α c ≤ ∑ c' ∈ Finset.univ.erase hub0, α c' :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
          omega
      rwa [hα]
    · obtain ⟨j, hjne, hjpos⟩ : ∃ j : Fin d, j ≠ hub0 ∧ α j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hsplit : (∑ c, α c) = α hub0 :=
          Finset.sum_eq_single hub0 (fun c _ hc => hcon c hc)
            (fun h => absurd (Finset.mem_univ hub0) h)
        rw [hsplit, Nat.sub_self] at hdeficit
        exact hm0 hdeficit.symm
      set α' : Fin d → ℕ := moveOneTo α hub0 j with hα'
      have hsum' : (∑ c, α' c) = ∑ c, α c := sum_moveOneTo (Ne.symm hjne) hjpos
      have hval' : α' hub0 = α hub0 + 1 := by rw [hα']; exact moveOneTo_self α hub0 j
      have hα'0 : α' hub0 ≠ 0 := by omega
      have hdeficit' : (∑ c, α' c) - α' hub0 = m - 1 := by rw [hsum', hval']; omega
      have hhubeq : (fun c => if c = hub0 then (∑ c, α' c) else 0) =
          (fun c => if c = hub0 then (∑ c, α c) else 0) := by rw [hsum']
      have hmem' : L.word (countWord d α') Ω ∈ W := by
        refine ih (m - 1) (by omega) α' hdeficit' ?_
        rwa [hhubeq]
      have hstep := word_countWord_moveOneTo_mem P hWE hmem' hjne hα'0
      have hrev : moveOneTo α' j hub0 = α := by
        rw [hα']
        exact moveOneTo_moveOneTo (Ne.symm hjne) hjpos
      rwa [hrev] at hstep

/-- Connectivity: any two occupation-number words of the same total excitation number reach
each other, given `W` is `E i j`-invariant and contains one of them. -/
lemma word_countWord_mem_of_mem {hd : 0 < d} {Ω : V} (P : L.HasVacuum Ω)
    {W : Submodule K V} (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) {α α' : Fin d → ℕ}
    (hsum : (∑ c, α c) = ∑ c, α' c) (hmem : L.word (countWord d α) Ω ∈ W) :
    L.word (countWord d α') Ω ∈ W := by
  have h1 := word_countWord_hub_mem_of_mem (hd := hd) P hWE _ α rfl hmem
  have h2 := word_countWord_mem_of_hub_mem (hd := hd) P hWE _ α' rfl
  rw [hsum] at h1
  exact h2 h1

/-!

## D. Irreducibility

-/

/-- `vacuumSpan L Ω n` is `gl(d)`-irreducible. The only submodules of `vacuumSpan L Ω n`
invariant under every `E i j` are `⊥` and `vacuumSpan L Ω n` itself. -/
theorem vacuumSpan_eq_of_ne_bot {hd : 0 < d} {Ω : V} (P : L.HasVacuum Ω) (n : ℕ)
    {W : Submodule K V} (hWle : W ≤ vacuumSpan L Ω n)
    (hWE : ∀ i j, ∀ w ∈ W, L.E i j w ∈ W) (hWbot : W ≠ ⊥) :
    W = vacuumSpan L Ω n := by
  obtain ⟨α₀, hα₀⟩ := exists_word_countWord_mem_of_ne_bot P n hWle hWE hWbot
  refine le_antisymm hWle ?_
  rw [← span_word_countFun_eq_vacuumSpan L Ω n, Submodule.span_le]
  rintro _ ⟨α, rfl⟩
  refine word_countWord_mem_of_mem (hd := hd) P hWE ?_ hα₀
  have h1 : (∑ c, α₀.1 c) = n := α₀.2
  have h2 : (∑ c, α.1 c) = n := α.2
  rw [h1, h2]

end LadderSystem
