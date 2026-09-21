/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.Mathematics.LadderSystem.Vacuum
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
/-!

# The occupation-number basis

## i. Overview

The occupation-number states `word (countWord d α) Ω`, indexed by degree-`n` count functions
`α : CountFun d n`, form a basis of `vacuumSpan L Ω n`. For linear independence, each state is
viewed as a nonzero eigenvector of the diagonal operator
`M := ∑ᵢ (n+1)^i • Nᵢ`, at the pairwise-distinct eigenvalue `countEncode n α` (a positional
encoding of `α`), so Mathlib's general "eigenvectors at distinct eigenvalues are independent" fact
applies. It follows that `vacuumSpan` is finite-dimensional and has dimension
`(d+n-1).choose n`, the degeneracy of the `n`-th level of a `d`-dimensional bosonic oscillator.

## ii. Key results

Definitions:
- `CountFun d n` : a degree-`n` count function on `d` colors.
- `LadderSystem.vacuumBasis` : the occupation-number basis of `vacuumSpan L Ω n`.

Theorems:
- `LadderSystem.linearIndependent_word_countFun` : the occupation-number states are linearly
    independent.
- `LadderSystem.finrank_vacuumSpan_eq_choose` : `vacuumSpan L Ω n` has dimension
    `(d+n-1).choose n`.

## iii. Table of contents

- A. Count functions
- B. Exact annihilation
- C. The occupation-number basis
  - C.1. A positional encoding of count functions
  - C.2. Linear independence
  - C.3. The basis and its dimension

## iv. References

* None.
-/

@[expose] public section

open Module (Basis)

/-!

## A. Count functions

-/

/-- A degree-`n` count function on `d` colors. -/
abbrev CountFun (d n : ℕ) := {α : Fin d → ℕ // ∑ c, α c = n}

/-- Degree-`n` count functions on `d` colors biject with `Sym (Fin d) n`. -/
noncomputable def countFunEquivSym (d n : ℕ) : CountFun d n ≃ Sym (Fin d) n :=
  (Sym.equivNatSumOfFintype (Fin d) n).symm

noncomputable instance instFintypeCountFun {d n : ℕ} : Fintype (CountFun d n) :=
  Fintype.ofEquiv (Sym (Fin d) n) (Sym.equivNatSumOfFintype (Fin d) n)

/-- There are exactly `(d + n - 1).choose n` degree-`n` count functions on `d` colors. -/
lemma card_countFun (d n : ℕ) : Fintype.card (CountFun d n) = (d + n - 1).choose n := by
  rw [Fintype.card_congr (countFunEquivSym d n), Sym.card_sym_eq_choose, Fintype.card_fin]

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LadderSystem

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {d : ℕ}
    (L : LadderSystem K V d)

/-!

## B. Exact annihilation

-/

omit [CharZero K] in
/-- Annihilation and creation operators of different colors commute at any power. -/
lemma pow_a_comm_ac {i c : Fin d} (hic : i ≠ c) (k : ℕ) (y : V) :
    ((L.a i) ^ k) (L.ac c y) = L.ac c (((L.a i) ^ k) y) := by
  have h := L.comm_a_ac i c
  rw [ite_eq_right hic, LieRing.of_associative_ring_bracket, sub_eq_zero] at h
  have hpow : (L.a i) ^ k * L.ac c = L.ac c * (L.a i) ^ k := Commute.pow_left h k
  have happly := congrArg (fun f : Module.End K V => f y) hpow
  simpa [Module.End.mul_apply] using happly

omit [CharZero K] in
/-- Exact annihilation: applying `a i` exactly `count i` times removes every `i`, scaled by the
factorial. -/
lemma word_peel_eq_count (L : LadderSystem K V d) (i : Fin d) {x : V} (hx : L.a i x = 0) :
    ∀ v : List (Fin d),
      ((L.a i) ^ (v.count i)) (L.word v x) = (v.count i).factorial • L.word (v.filter (· != i)) x
  | [] => by simp [word]
  | c :: v' => by
    by_cases hic : i = c
    · subst hic
      have hpeel := word_peel L i hx (i :: v')
      rw [List.count_cons_self, List.erase_cons_head] at hpeel
      rw [List.count_cons_self, List.filter_cons_of_neg (by simp), pow_succ,
        Module.End.mul_apply, hpeel, map_nsmul, word_peel_eq_count L i hx v',
        Nat.factorial_succ, mul_smul]
    · rw [List.count_cons_of_ne (Ne.symm hic), word_cons,
        pow_a_comm_ac L hic, word_peel_eq_count L i hx v', map_nsmul, ← word_cons,
        List.filter_cons_of_pos (by simpa using Ne.symm hic)]

/-- The joint annihilation monomial for a list of colors `cs` and exponents `α`:
`∏_{c ∈ cs} (a c)^{α c}`. -/
def annMono (cs : List (Fin d)) (α : Fin d → ℕ) : Module.End K V :=
  (cs.map (fun c => (L.a c) ^ (α c))).prod

omit [CharZero K] in
@[simp] theorem annMono_nil (α : Fin d → ℕ) : L.annMono [] α = 1 := rfl

omit [CharZero K] in
lemma annMono_cons (c : Fin d) (cs : List (Fin d)) (α : Fin d → ℕ) :
    L.annMono (c :: cs) α = (L.a c) ^ (α c) * L.annMono cs α := rfl

omit [CharZero K] in
/-- Exact annihilation of every color in the list produces the product of factorials. -/
lemma annMono_eq_count (L : LadderSystem K V d) {x : V} (hx : ∀ i, L.a i x = 0) :
    ∀ (cs : List (Fin d)), cs.Nodup → ∀ (α : Fin d → ℕ) (v : List (Fin d)),
      (∀ c ∈ cs, v.count c = α c) →
      (L.annMono cs α) (L.word v x)
        = ((cs.map (fun c => (α c).factorial)).prod) •
            L.word (v.filter (fun y => !cs.contains y)) x
  | [], _, _, _, _ => by simp
  | c :: cs', hnodup, α, v, hmatch => by
    obtain ⟨hcnotmem, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hmatch' : ∀ e ∈ cs', v.count e = α e := fun e he => hmatch e (List.mem_cons_of_mem c he)
    have hcm : v.count c = α c := hmatch c List.mem_cons_self
    rw [annMono_cons, Module.End.mul_apply,
      annMono_eq_count L hx cs' hnodup' α v hmatch', map_nsmul]
    have hcount : (v.filter (fun y => !cs'.contains y)).count c = v.count c :=
      List.count_filter (by simpa using hcnotmem)
    have hpeel : ((L.a c) ^ (α c)) (L.word (v.filter (fun y => !cs'.contains y)) x)
        = (α c).factorial •
            L.word ((v.filter (fun y => !cs'.contains y)).filter (· != c)) x := by
      have h := word_peel_eq_count L c (hx c) (v.filter (fun y => !cs'.contains y))
      rwa [hcount, hcm] at h
    have hY : L.word ((v.filter (fun y => !cs'.contains y)).filter (· != c)) x
        = L.word (v.filter (fun y => !(c :: cs').contains y)) x := by
      congr 1
      rw [List.filter_filter]
      congr 1
      funext y
      by_cases hy : y = c
      · subst hy; simp
      · simp [hy]
    rw [hpeel, List.map_cons, List.prod_cons, hY, ← mul_smul, mul_comm]

end LadderSystem

/-- `countWord α` contains only colors from `List.finRange d`, i.e. everything. -/
lemma countWord_filter_finRange {d : ℕ} (α : Fin d → ℕ) :
    (LadderSystem.countWord d α).filter (fun y => !(List.finRange d).contains y) = [] :=
  List.filter_eq_nil_iff.mpr fun y _ => by simp [List.mem_finRange]

/-!

## C. The occupation-number basis

-/

/-!

### C.1. A positional encoding of count functions

-/

/-- A base-`b` positional encoding is injective on tuples with digits `< b`. -/
lemma encode_injOn_aux : ∀ (d b : ℕ), 0 < b → ∀ γ γ' : Fin d → ℕ,
    (∀ c, γ c < b) → (∀ c, γ' c < b) →
    (∑ i : Fin d, γ i * b ^ (i : ℕ)) = (∑ i : Fin d, γ' i * b ^ (i : ℕ)) → γ = γ' := by
  intro d
  induction d with
  | zero => intro b _ γ γ' _ _ _; exact funext fun i => i.elim0
  | succ d ih =>
    intro b hb γ γ' hγ hγ' heq
    have hfactor : ∀ f : Fin d → ℕ,
        (∑ i : Fin d, f i * b ^ (i.succ : ℕ)) = b * ∑ i : Fin d, f i * b ^ (i : ℕ) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ']
      ring
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at heq
    simp only [Fin.val_zero, pow_zero, mul_one] at heq
    rw [hfactor (fun i => γ i.succ), hfactor (fun i => γ' i.succ)] at heq
    have h0 : γ 0 = γ' 0 := by
      have hmod := congrArg (· % b) heq
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hγ 0), Nat.mod_eq_of_lt (hγ' 0)]
        at hmod
      exact hmod
    have hrest : (∑ i : Fin d, γ i.succ * b ^ (i : ℕ)) = ∑ i : Fin d, γ' i.succ * b ^ (i : ℕ) := by
      have heq' := heq
      rw [h0] at heq'
      exact Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel heq')
    have htail := ih b hb (fun i => γ i.succ) (fun i => γ' i.succ)
      (fun i => hγ i.succ) (fun i => hγ' i.succ) hrest
    funext i
    exact Fin.cases h0 (fun j => congrFun htail j) i

/-- The base-`(n+1)` positional encoding of a degree-`n` count function; injective on such
functions. -/
def countEncode (n : ℕ) {d : ℕ} (γ : Fin d → ℕ) : ℕ := ∑ i : Fin d, γ i * (n + 1) ^ (i : ℕ)

lemma countEncode_injOn {d n : ℕ} {γ γ' : Fin d → ℕ}
    (hγ : ∑ c, γ c = n) (hγ' : ∑ c, γ' c = n) (heq : countEncode n γ = countEncode n γ') :
    γ = γ' := by
  refine encode_injOn_aux d (n + 1) (Nat.succ_pos n) γ γ' (fun c => ?_) (fun c => ?_) heq
  · exact Nat.lt_succ_of_le (hγ ▸ Finset.single_le_sum (fun c _ => Nat.zero_le _)
      (Finset.mem_univ c))
  · exact Nat.lt_succ_of_le (hγ' ▸ Finset.single_le_sum (fun c _ => Nat.zero_le _)
      (Finset.mem_univ c))

namespace LadderSystem

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {d : ℕ}
    (L : LadderSystem K V d)

/-!

### C.2. Linear independence

-/

/-- Every occupation-number state is nonzero: peeling every color's annihilation operator down to
the vacuum leaves a nonzero factorial multiple of `Ω`. -/
lemma word_countWord_ne_zero {Ω : V} (hΩ : L.HasVacuum Ω) (α : Fin d → ℕ) :
    L.word (countWord d α) Ω ≠ 0 := by
  intro hz
  have h := L.annMono_eq_count hΩ.ann (List.finRange d) (List.nodup_finRange d) α
    (countWord d α) (fun c _ => count_countWord α c)
  rw [countWord_filter_finRange, hz, map_zero] at h
  have hfact_pos : (0 : ℕ) < ((List.finRange d).map (fun c => (α c).factorial)).prod :=
    List.prod_pos (by
      intro a ha
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
      exact Nat.factorial_pos _)
  have hfact_ne : (((List.finRange d).map (fun c => (α c).factorial)).prod : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hfact_pos.ne'
  have hΩ' : L.word ([] : List (Fin d)) Ω = Ω := by simp [word]
  rw [hΩ', ← Nat.cast_smul_eq_nsmul K] at h
  rcases smul_eq_zero.mp h.symm with h1 | h2
  · exact hfact_ne h1
  · exact hΩ.ne_zero h2

/-- The occupation-number states are the eigenvectors, at pairwise-distinct eigenvalues, of the
single diagonal operator `M := ∑ᵢ (n+1)^i • Nᵢ`. -/
lemma hasEigenvector_word_countWord {Ω : V} (hΩ : L.HasVacuum Ω) (n : ℕ) (α : CountFun d n) :
    Module.End.HasEigenvector (∑ i : Fin d, ((n + 1 : K)) ^ (i : ℕ) • L.N i)
      (countEncode n α.1 : K) (L.word (countWord d α.1) Ω) := by
  refine ⟨?_, L.word_countWord_ne_zero hΩ α.1⟩
  rw [Module.End.mem_eigenspace_iff]
  have hterm : ∀ i : Fin d, (((n + 1 : K)) ^ (i : ℕ) • L.N i) (L.word (countWord d α.1) Ω)
      = ((n + 1 : K) ^ (i : ℕ) * (α.1 i : K)) • L.word (countWord d α.1) Ω := by
    intro i
    rw [LinearMap.smul_apply, L.N_word hΩ.ann i, count_countWord,
      ← Nat.cast_smul_eq_nsmul K, smul_smul]
  rw [LinearMap.sum_apply]
  simp only [hterm]
  rw [← Finset.sum_smul]
  congr 1
  unfold countEncode
  push_cast
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The occupation-number family is linearly independent because its elements are eigenvectors at
pairwise-distinct eigenvalues (`Module.End.eigenvectors_linearIndependent'`). -/
theorem linearIndependent_word_countFun {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    LinearIndependent K (fun α : CountFun d n => L.word (countWord d α.1) Ω) := by
  have hinj : Function.Injective (fun α : CountFun d n => (countEncode n α.1 : K)) := by
    intro α β hαβ
    have hαβ' : countEncode n α.1 = countEncode n β.1 := by
      have := hαβ
      simp only at this
      exact_mod_cast this
    exact Subtype.ext (countEncode_injOn α.2 β.2 hαβ')
  exact Module.End.eigenvectors_linearIndependent' _
    (fun α : CountFun d n => (countEncode n α.1 : K)) hinj _
    (fun α => L.hasEigenvector_word_countWord P n α)

/-!

### C.3. The basis and its dimension

-/

omit [CharZero K] in
/-- The occupation-number family spans `vacuumSpan L Ω n`. -/
lemma span_word_countFun_eq_vacuumSpan (Ω : V) (n : ℕ) :
    Submodule.span K (Set.range fun α : CountFun d n => L.word (countWord d α.1) Ω)
      = L.vacuumSpan Ω n := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact word_mem_vacuumSpan_of_length_eq L Ω (by
      rw [← sum_count_eq_length]
      exact (Finset.sum_congr rfl (fun c _ => count_countWord α.1 c)).trans α.2)
  · rw [vacuumSpan, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show L.word (List.ofFn w) Ω ∈ _
    have hsum : (∑ c, (List.ofFn w).count c) = n := by
      rw [sum_count_eq_length, List.length_ofFn]
    have hperm : L.word (List.ofFn w) Ω
        = L.word (countWord d (fun c => (List.ofFn w).count c)) Ω :=
      L.word_perm (List.perm_iff_count.mpr (fun c => by rw [count_countWord])) Ω
    rw [hperm]
    exact Submodule.subset_span ⟨⟨fun c => (List.ofFn w).count c, hsum⟩, rfl⟩

/-- A basis of `vacuumSpan L Ω n` indexed by degree-`n` occupation-count functions. -/
noncomputable def vacuumBasis {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    Basis (CountFun d n) K (L.vacuumSpan Ω n) :=
  (Basis.span (L.linearIndependent_word_countFun P n)).map
    (LinearEquiv.ofEq _ _ (L.span_word_countFun_eq_vacuumSpan Ω n))

lemma vacuumBasis_apply {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) (α : CountFun d n) :
    (vacuumBasis L P n α : V) = L.word (countWord d α.1) Ω := by
  unfold vacuumBasis
  rw [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]

/-- The dimension of `vacuumSpan L Ω n` is `(d+n-1).choose n`, the degeneracy of the `n`-th level
of a `d`-mode bosonic system. -/
theorem finrank_vacuumSpan_eq_choose {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    Module.finrank K (L.vacuumSpan Ω n) = (d + n - 1).choose n := by
  rw [Module.finrank_eq_card_basis (vacuumBasis L P n), card_countFun]

lemma finiteDimensional_vacuumSpan {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    FiniteDimensional K (L.vacuumSpan Ω n) :=
  Module.Basis.finiteDimensional_of_finite (vacuumBasis L P n)

lemma vacuumSpan_ne_bot {Ω : V} (P : L.HasVacuum Ω) (hd : 0 < d) (n : ℕ) :
    L.vacuumSpan Ω n ≠ ⊥ := by
  obtain ⟨α⟩ : Nonempty (CountFun d n) := ⟨⟨fun c => if c = ⟨0, hd⟩ then n else 0, by simp⟩⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨(vacuumBasis L P n α : V), (vacuumBasis L P n α).2, ?_⟩
  have hne := (vacuumBasis L P n).ne_zero α
  exact fun h => hne (Subtype.ext h)

end LadderSystem
