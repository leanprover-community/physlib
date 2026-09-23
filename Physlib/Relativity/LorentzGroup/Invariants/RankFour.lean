/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LightCone
public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import Physlib.Mathematics.LeviCivita.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Lorentz invariants of a rank-four tensor

A rank-four tensor `T^{μνρσ}` has `4 ^ 4 = 256` components. Four combinations of them are fixed
by every rotation and boost, the Lorentz transformations coming from `SL(2,ℂ)`:

* `outerContraction = η_{μν} η_{ρσ} T^{μνρσ}`,
* `innerContraction = η_{μρ} η_{νσ} T^{μνρσ}`,
* `splitContraction = η_{μσ} η_{νρ} T^{μνρσ}`,
* `epsilonContraction = ε_{μνρσ} T^{μνρσ}`.

There are no others. The fourth is a pseudoscalar, so it would drop out if reflections were
allowed; independence is not proved, and for a given `T` the four may be dependent or zero. The
components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, and `IsLorentzCovariant 4 B repLorentz T` says the group moves
them with one factor of the Lorentz matrix per slot (A). A vector of `B` is invariant when every
`repLorentz g` fixes it, and `componentSpan T` is the set of contractions `∑_d c_d • T d`. The
theorem `mem_span_sup_invariant_iff` (H) allows a Lorentz-stable subspace `S` beside the span,
where the files using it park their other tensors: a vector of `componentSpan T ⊔ S`, the sums
`u + y`, is invariant exactly when it is a combination of the four contractions plus an
invariant `y` of `S`. For `S = ⊥` that is `exists_smul_contraction_of_invariant`.

The four coefficient tensors are invariant, by `Λ η Λᵀ = η` and `det Λ = 1` (B); an invariant
of the span is the contraction of an invariant one, by projecting off the tensors that contract
to `0` (C); and such a tensor is a combination of the four, two rotations cutting `256`
coefficients to `22` (D), a boost keeping only what it does not rescale (E), and the `22 × 22`
integer equation left being solved by one checked matrix identity (F, G).
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants

/-!

## A. Rank-four families, their span, and coefficient tensors

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes; an index vector
`d : Fin 4 → Fin 1 ⊕ Fin 3` puts one in each slot, so `T d` is `T^{μνρσ}` at `(μ, ν, ρ, σ) = d`.
The predicate and the span are `IsLorentzCovariant 4` and `componentSpan`, both from
`Invariants.LorentzCovariance`. The law is

`repLorentz g (T l) = ∑_a Λ_{a₀ l₀} Λ_{a₁ l₁} Λ_{a₂ l₂} Λ_{a₃ l₃} • T a`,

with `l` free and `a` summed, and transforming a contraction moves its coefficient tensor by
`(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯ Λ_{a₃ d₃}`, now with `a` free and `d` summed
(`repLorentz_sum_smul`): the same `Λ`, never its inverse, but transposed index slots, which is
what makes `act Λᵀ` the adjoint of `act Λ` in C. Two invariance conditions are therefore in
play, kept apart by name: `x : B` is Lorentz invariant when `repLorentz g x = x`, and `c` is
`IsInvariantCoeff` when `act Λ c = c`. Everything in this paragraph, and section C below, is
stated for any number of slots in `Invariants.Basic` and used here at four.
-/

namespace RankFour

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B}

/-!

## B. The four contractions

## B.1. The metric, the Levi-Civita symbol and the contractions

Neither the metric nor the Levi-Civita symbol is defined here. The metric is
`minkowskiMatrixZ`, the integer form of `minkowskiMatrix`, and the symbol is
`leviCivitaSymbol`, read on an index vector through `finSumFinEquiv`. Both are integer
valued because sections F and G evaluate them in the kernel, which cannot compute with real
numbers. The metric pairings use the slots `(0,1)(2,3)`,
`(0,2)(1,3)` and `(0,3)(1,2)` for `outerContraction`, `innerContraction` and
`splitContraction`; `contractionCoeff` holds the four coefficient tensors and `contraction T`
the four contractions in that order.
-/

/-- The four coefficient tensors: the three metric pairings, then the Levi-Civita symbol. -/
def contractionCoeff : Fin 4 → (Fin 4 → Fin 1 ⊕ Fin 3) → ℤ :=
  ![fun d => minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3),
    fun d => minkowskiMatrixZ (d 0) (d 2) * minkowskiMatrixZ (d 1) (d 3),
    fun d => minkowskiMatrixZ (d 0) (d 3) * minkowskiMatrixZ (d 1) (d 2),
    fun d => leviCivitaSymbol fun μ => d (finSumFinEquiv μ)]

/-- The contraction `η_{μν} η_{ρσ} T^{μνρσ}`, pairing slots `(0,1)` and `(2,3)`. -/
noncomputable def outerContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
    ((minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3) : ℤ) : ℂ) • T d

/-- The contraction `η_{μρ} η_{νσ} T^{μνρσ}`, pairing slots `(0,2)` and `(1,3)`. -/
noncomputable def innerContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
    ((minkowskiMatrixZ (d 0) (d 2) * minkowskiMatrixZ (d 1) (d 3) : ℤ) : ℂ) • T d

/-- The contraction `η_{μσ} η_{νρ} T^{μνρσ}`, pairing slots `(0,3)` and `(1,2)`. -/
noncomputable def splitContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
    ((minkowskiMatrixZ (d 0) (d 3) * minkowskiMatrixZ (d 1) (d 2) : ℤ) : ℂ) • T d

/-- The contraction `ε_{μνρσ} T^{μνρσ}` with the Levi-Civita symbol. -/
noncomputable def epsilonContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
    ((leviCivitaSymbol fun μ => d (finSumFinEquiv μ) : ℤ) : ℂ) • T d

/-- The four contractions in order, from the outer one to the Levi-Civita one. -/
noncomputable def contraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : Fin 4 → B :=
  ![outerContraction T, innerContraction T, splitContraction T, epsilonContraction T]

/-- Each contraction is the contraction with its coefficient tensor. -/
lemma contraction_eq (i : Fin 4) :
    contraction T i = ∑ d, ((contractionCoeff i d : ℤ) : ℂ) • T d := by
  fin_cases i <;> rfl

/-- A combination of the four contractions, written out. -/
lemma sum_smul_contraction (a : Fin 4 → ℂ) :
    ∑ i, a i • contraction T i
      = a 0 • outerContraction T + a 1 • innerContraction T + a 2 • splitContraction T
        + a 3 • epsilonContraction T := by
  rw [Fin.sum_univ_four]
  rfl

/-- The outer contraction lies in the span of the components. -/
lemma outerContraction_mem_span : outerContraction T ∈ componentSpan T :=
  sum_smul_mem_componentSpan T _

/-- The inner contraction lies in the span of the components. -/
lemma innerContraction_mem_span : innerContraction T ∈ componentSpan T :=
  sum_smul_mem_componentSpan T _

/-- The split contraction lies in the span of the components. -/
lemma splitContraction_mem_span : splitContraction T ∈ componentSpan T :=
  sum_smul_mem_componentSpan T _

/-- The Levi-Civita contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span : epsilonContraction T ∈ componentSpan T :=
  sum_smul_mem_componentSpan T _

/-- A combination of the four contractions lies in the span of the components. -/
lemma smul_contraction_mem_span (a₁ a₂ a₃ a₄ : ℂ) :
    a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
      + a₄ • epsilonContraction T ∈ componentSpan T :=
  add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (outerContraction_mem_span (T := T)))
    (Submodule.smul_mem _ _ (innerContraction_mem_span (T := T))))
    (Submodule.smul_mem _ _ (splitContraction_mem_span (T := T))))
    (Submodule.smul_mem _ _ (epsilonContraction_mem_span (T := T)))

/-!

## B.2. The four coefficient tensors are invariant

`Λ η Λᵀ = η` defines the Lorentz group; entry by entry it is
`LorentzGroup.sum_minkowskiMatrixZ_mul`, and a pair of metrics is two copies of it, one per
pair of slots (`act_outerPair`). The inner and split pairings are the outer one with the slots
permuted (`act_outerPair_comp`). The symbol against
four rows of `M` gives `det M` times the symbol of those rows (`sum_leviCivitaSymbol_mul_prod`),
and `det Λ = 1` here: the only use of the determinant, and the reason there are four invariants
and not three, a reflection having `det = -1`. `sum_pi_four` is bookkeeping.
-/

/-- Bookkeeping: a sum over index vectors is a fourfold sum over directions. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3, F ![x, y, z, w] := by
  rw [show (∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
      Fintype.sum_equiv
        { toFun := fun d => (d 0, d 1, d 2, d 3)
          invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
          left_inv := fun d => by funext i; fin_cases i <;> simp
          right_inv := fun p => by simp } _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-- The pairing of slots `(0,1)` and `(2,3)` is fixed: two copies of
  `LorentzGroup.sum_minkowskiMatrixZ_mul`. -/
lemma act_outerPair (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3) : ℤ) : ℂ)) a
      = ((minkowskiMatrixZ (a 0) (a 1) * minkowskiMatrixZ (a 2) (a 3) : ℤ) : ℂ) := by
  have h : ∀ x y z w : Fin 1 ⊕ Fin 3,
      ((minkowskiMatrixZ (![x, y, z, w] 0) (![x, y, z, w] 1)
          * minkowskiMatrixZ (![x, y, z, w] 2) (![x, y, z, w] 3) : ℤ) : ℂ)
        * ∏ s, ((Λ.1 (a s) (![x, y, z, w] s) : ℝ) : ℂ)
      = (((minkowskiMatrixZ x y : ℤ) : ℂ)
          * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 1) y : ℝ) : ℂ)))
        * (((minkowskiMatrixZ z w : ℤ) : ℂ)
          * (((Λ.1 (a 2) z : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
    intro x y z w
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    push_cast
    ring
  rw [act, sum_pi_four]
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, LorentzGroup.sum_minkowskiMatrixZ_mul]
  push_cast
  ring

/-- The same for the slots permuted by `σ`, by renaming the summation variable. -/
lemma act_outerPair_comp (σ : Equiv.Perm (Fin 4)) (Λ : LorentzGroup 3)
    (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((minkowskiMatrixZ (d (σ 0)) (d (σ 1))
        * minkowskiMatrixZ (d (σ 2)) (d (σ 3)) : ℤ) : ℂ)) a
      = ((minkowskiMatrixZ (a (σ 0)) (a (σ 1))
        * minkowskiMatrixZ (a (σ 2)) (a (σ 3)) : ℤ) : ℂ) := by
  have h := act_outerPair Λ (a ∘ σ)
  rw [act, ← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 1 ⊕ Fin 3)))] at h
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_def,
    id] at h
  rw [← h, act]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.prod_comp σ fun i => ((Λ.1 (a i) (d i) : ℝ) : ℂ)]

/-- The symbol is fixed by a Lorentz matrix of determinant `1`; in general it picks up `det Λ`,
  by `sum_leviCivitaSymbol_mul_prod`. -/
lemma act_leviCivitaSymbol (Λ : LorentzGroup 3) (hΛ : Λ.1.det = 1) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((leviCivitaSymbol fun μ => d (finSumFinEquiv μ) : ℤ) : ℂ)) a
      = ((leviCivitaSymbol fun μ => a (finSumFinEquiv μ) : ℤ) : ℂ) := by
  have hdet : (Complex.ofRealHom.mapMatrix Λ.1).det = 1 := by
    rw [← RingHom.map_det, hΛ]
    simp
  have h := sum_leviCivitaSymbol_mul_prod (Complex.ofRealHom.mapMatrix Λ.1)
    (fun μ => a (finSumFinEquiv μ))
  rw [hdet, one_mul] at h
  rw [act, ← h, ← Equiv.sum_comp
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 1 ⊕ Fin 3)))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_def, id]
  congr 1

/-- The four coefficient tensors are invariant. -/
lemma isInvariantCoeff_contractionCoeff (i : Fin 4) :
    IsInvariantCoeff fun d => ((contractionCoeff i d : ℤ) : ℂ) := by
  intro g
  funext a
  fin_cases i
  · exact act_outerPair _ a
  · simpa [contractionCoeff, Equiv.swap_apply_def] using
      act_outerPair_comp (Equiv.swap 1 2) (SL2C.toLorentzGroup g) a
  · simpa [contractionCoeff, Equiv.swap_apply_def, Equiv.trans_apply] using
      act_outerPair_comp ((Equiv.swap 1 3).trans (Equiv.swap 1 2)) (SL2C.toLorentzGroup g) a
  · exact act_leviCivitaSymbol _ (SL2C.toLorentzGroup_det_one g) a

/-!

## B.3. The four contractions are Lorentz invariant

Contracting with an invariant coefficient tensor gives an invariant vector, so each contraction
is invariant, as is any combination: with `smul_contraction_mem_span`, the easy direction.
-/

/-- Each of the four contractions is Lorentz invariant, its coefficient tensor being invariant. -/
lemma repLorentz_contraction (hT : IsLorentzCovariant 4 B repLorentz T) (i : Fin 4)
    (g : SL(2,ℂ)) : repLorentz g (contraction T i) = contraction T i := by
  rw [contraction_eq, hT.isInvariant_sum_smul (isInvariantCoeff_contractionCoeff i)]

/-- The outer contraction is Lorentz invariant. -/
lemma repLorentz_outerContraction (hT : IsLorentzCovariant 4 B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (outerContraction T) = outerContraction T :=
  repLorentz_contraction hT 0 g

/-- The inner contraction is Lorentz invariant. -/
lemma repLorentz_innerContraction (hT : IsLorentzCovariant 4 B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (innerContraction T) = innerContraction T :=
  repLorentz_contraction hT 1 g

/-- The split contraction is Lorentz invariant. -/
lemma repLorentz_splitContraction (hT : IsLorentzCovariant 4 B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (splitContraction T) = splitContraction T :=
  repLorentz_contraction hT 2 g

/-- The Levi-Civita contraction is Lorentz invariant. -/
lemma repLorentz_epsilonContraction (hT : IsLorentzCovariant 4 B repLorentz T)
    (g : SL(2,ℂ)) : repLorentz g (epsilonContraction T) = epsilonContraction T :=
  repLorentz_contraction hT 3 g

/-- A combination of the four contractions is Lorentz invariant. -/
lemma repLorentz_smul_contraction (hT : IsLorentzCovariant 4 B repLorentz T)
    (a₁ a₂ a₃ a₄ : ℂ) (g : SL(2,ℂ)) :
    repLorentz g (a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T)
      = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T := by
  simp only [map_add, map_smul, repLorentz_outerContraction hT, repLorentz_innerContraction hT,
    repLorentz_splitContraction hT, repLorentz_epsilonContraction hT]

/-!

## C. An invariant of the span is the contraction of an invariant tensor

The components may satisfy linear relations, so the `c` with `x = ∑ c_d • T d` is not
determined by `x` and need not be invariant. Replacing `c` by its part orthogonal to the
coefficient tensors that contract to `0` repairs that without changing the vector; the argument
is the same for any number of slots and is carried out in `Invariants.Basic`, reached here
through `IsLorentzCovariant.exists_isInvariantCoeff_of_mem_componentSpan`.

The inner product it uses is the standard one on the `ℂ^{256}` of coefficient tensors, positive
definite and unrelated to `η`; `B` carries none, and the coefficient action is not unitary. All
that is needed is that the adjoint of `act Λ` is `act Λᵀ`, which is again the action of a
Lorentz matrix coming from `SL(2,ℂ)`, that of `g†`.
-/

/-!

## D. The rotations by `π` about the axes and the rotation `x → y → z → x`

The rotation by `π` about the `k`-th axis is `i σ_k` (`flipAxis k`), with diagonal Lorentz
matrix fixing time and that axis and negating the other two, so it multiplies `c d` by `-1`
once per slot of `d` holding a negated direction (`act_flipAxis`), and where that sign is `-1`
invariance forces `c d = 0`. Call `d` flip-fixed when all three signs are `1` (`IsFlipFixed`):
with `n_t, n_x, n_y, n_z` the counts of each direction that says all four have the same parity,
so `xxyy` and `txyz` survive, `tttx` does not, and `64` of `256` remain.

The rotation `x → y → z → x` fixes time (`rotationCycle`) and permutes rather than rescales, so
the new coefficient at `a` is the old one at `cycIdx (cycIdx a)` (`act_rotationCycle`) and
invariance reads `c (cycIdx d) = c d`: `c` is constant on the orbit
`{d, cycIdx d, cycIdx (cycIdx d)}`, of three members unless `d` is `tttt`.
-/

/-- Rotation by `π` about the `k`-th axis: the matrices below are `i σ_x`, `i σ_y`, `i σ_z`. -/
def flipAxis : Fin 3 → SL(2,ℂ)
  | 0 => ⟨!![0, Complex.I; Complex.I, 0], by simp [Matrix.det_fin_two_of]⟩ -- `i σ_x`
  | 1 => ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩ -- `i σ_y`
  | 2 => ⟨!![Complex.I, 0; 0, -Complex.I], by simp [Matrix.det_fin_two_of]⟩ -- `i σ_z`

/-- The sign the `k`-th flip gives a direction: `+1` on time and the axis, `-1` transverse. -/
def flipSign (k : Fin 3) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if μ = Sum.inl 0 ∨ μ = Sum.inr k then 1 else -1

/-- The Lorentz matrix of the `k`-th flip is diagonal, carrying `flipSign k`. -/
lemma toLorentzGroup_flipAxis_apply (k : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (flipAxis k)).1 a b = if a = b then (flipSign k a : ℝ) else 0 := by
  refine Complex.ofReal_injective ?_
  rw [SL2C.toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  fin_cases k <;> rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [flipAxis, flipSign, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- Being diagonal, the flip rescales each coefficient by the product of its four signs. -/
lemma act_flipAxis (k : Fin 3) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup (flipAxis k)).1 c a = ((∏ s, flipSign k (a s) : ℤ) : ℂ) * c a := by
  rw [act, Finset.sum_eq_single a]
  · rw [mul_comm]
    push_cast
    congr 1
    exact Finset.prod_congr rfl fun s _ => by
      rw [toLorentzGroup_flipAxis_apply, ite_eq_left rfl, Complex.ofReal_intCast]
  · intro d _ hda
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hda.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [toLorentzGroup_flipAxis_apply, ite_eq_right hs, Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ a) h

/-- The sign a flip attaches to a coefficient is `1` or `-1`, being a product of such signs. -/
lemma prod_flipSign_eq_one_or (k : Fin 3) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∏ s, flipSign k (d s) = 1 ∨ ∏ s, flipSign k (d s) = -1 := by
  refine Finset.prod_induction _ (fun n : ℤ => n = 1 ∨ n = -1) ?_ (Or.inl rfl) fun s _ => ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · unfold flipSign
    split_ifs <;> simp

/-- All three flips fix the coefficient at `d`, that is the sign product is `1` for each axis.
  Equivalently, and not used below, all four directions occur an even number of times among the
  slots, or all four an odd number. -/
def IsFlipFixed (d : Fin 4 → Fin 1 ⊕ Fin 3) : Prop :=
  ∀ k : Fin 3, ∏ s, flipSign k (d s) = 1

instance : DecidablePred IsFlipFixed := fun d =>
  inferInstanceAs (Decidable (∀ k : Fin 3, ∏ s, flipSign k (d s) = 1))

/-- An invariant coefficient tensor vanishes off the flip-fixed index vectors. -/
lemma eq_zero_of_not_isFlipFixed {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) {d : Fin 4 → Fin 1 ⊕ Fin 3} (hd : ¬IsFlipFixed d) : c d = 0 := by
  obtain ⟨k, hk⟩ := not_forall.1 hd
  have h := congrFun (hc (flipAxis k)) d
  rw [act_flipAxis, (prod_flipSign_eq_one_or k d).resolve_left hk] at h
  push_cast at h
  linear_combination (-2⁻¹ : ℂ) * h

/-- The relabelling `cycDir`, which fixes time and sends `x → y → z → x`, applied in every slot. -/
def cycIdx (d : Fin 4 → Fin 1 ⊕ Fin 3) : Fin 4 → Fin 1 ⊕ Fin 3 := fun s => cycDir (d s)

/-- Cycling the axes three times is the identity. -/
lemma cycIdx_cycIdx_cycIdx (d : Fin 4 → Fin 1 ⊕ Fin 3) : cycIdx (cycIdx (cycIdx d)) = d :=
  funext fun s => cycDir_cycDir_cycDir (d s)

/-- The cyclic rotation permutes entries: the new entry at `a` is the old one at `a` cycled back. -/
lemma act_rotationCycle (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup rotationCycle).1 c a = c (cycIdx (cycIdx a)) := by
  rw [act, Finset.sum_eq_single (cycIdx (cycIdx a))]
  · rw [Finset.prod_eq_one fun s _ => ?_, mul_one]
    rw [toLorentzGroup_rotationCycle_apply, ite_eq_left, Complex.ofReal_one]
    exact (congrFun (cycIdx_cycIdx_cycIdx a) s).symm
  · intro d _ hda
    have hne : cycIdx d ≠ a := fun h => hda (by rw [← h, cycIdx_cycIdx_cycIdx])
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hne
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [toLorentzGroup_rotationCycle_apply, ite_eq_right fun h : a s = cycDir (d s) => hs h.symm,
      Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- An invariant coefficient tensor is constant on the orbits of the cyclic rotation. -/
lemma apply_cycIdx {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) : c (cycIdx d) = c d := by
  have h := congrFun (hc rotationCycle) (cycIdx d)
  rw [act_rotationCycle, cycIdx_cycIdx_cycIdx] at h
  exact h.symm

/-!

## E. The boost along an axis

## E.1. An invariant tensor has boost weight zero

The boosts along the axis `i` are `SL2C.boostAxis i t ht`, of rapidity `2 log t` for `t > 0`.
In each slot replace the coordinate directions by the light-cone directions `D₀ - Dᵢ`,
`D₀ + Dᵢ` and the two transverse ones: they are eigenvectors of the boost with eigenvalues
`t²`, `t⁻²`, `1`, `1` (`sum_boostAxis_lightConeCoeff`, imported), so their weights, the
exponents of `t`, are `2`, `-2`, `0`, `0` (`lightConeWeight`). A multi-index `κ` picks one per
slot and `lightConeComponent i c κ` contracts `c` against that choice; the boost scales it by
`t` to the total weight of `κ`, so `t = 2` kills every component of nonzero weight. Only the
`z`-axis is used below, and nothing claims these elements generate the group: F and G show that
what they force is enough.
-/

/-!

## E.2. The weight-zero projection

Writing each coordinate direction in the light-cone basis recovers `c` from its light-cone
components (`eq_sum_lightConeComponent`), and for an invariant `c` only weight zero survives.
The projection that keeps total weight `m` is `Invariants.transitionZ`, built a slot at a time
and stated at any number of slots in `Invariants.LightCone`; each slot carries the factor `2`
of `lightConeCoeffInvZ`, so at four slots the projection is `2 ^ 4 = 16` times the true one.
That is the only place the `16` comes from.
-/

/-- An invariant coefficient tensor is its own weight-zero projection. -/
lemma sixteen_mul_eq_sum_transitionZ {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    16 * c d = ∑ e, ((transitionZ i d e 0 : ℤ) : ℂ) * c e := by
  rw [eq_sum_lightConeComponent i c d, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun κ : Fin 4 → Fin 4 => ∑ s, lightConeWeight (κ s) = 0),
    Finset.sum_eq_zero (s := Finset.univ.filter fun κ : Fin 4 → Fin 4 =>
      ¬∑ s, lightConeWeight (κ s) = 0) fun κ hκ => by
        rw [hc.lightConeComponent_eq_zero i (Finset.mem_filter.1 hκ).2, mul_zero],
    add_zero]
  simp only [lightConeComponent, Finset.mul_sum, transitionZ_eq_sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ hκ => Finset.sum_congr rfl fun e _ => ?_
  simp only [slotZ, Int.cast_prod, Int.cast_mul, coe_lightConeCoeffInvZ_eq_two_mul,
    coe_lightConeCoeffZ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-!

## F. The `22` orbit coordinates and the orbit matrix

## F.1. The orbits

Write an index vector as a word, `tttt` or `txxt`. Cycling the axes carries one to another and
three cyclings return it, so they fall into orbits of at most three: `txxt`, `tyyt`, `tzzt`
form one, and `tttt` is alone. By D an invariant tensor vanishes off the `64` flip-fixed
vectors and is constant on each orbit, and those `64` make `22` orbits, `21` of size three plus
`tttt`; `orbitRep` lists one from each, and the two lemmas below check at all `256` index
vectors that these cover the flip-fixed ones without overlapping. So an invariant tensor is its
`22` values at the representatives, its orbit coordinates, which `ofOrbitCoord` inverts.
-/

/-- One index vector from each of the `22` orbits, checked by the two lemmas below. -/
def orbitRep : Fin 22 → Fin 4 → Fin 1 ⊕ Fin 3 :=
  ![![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0],                            -- tttt
    ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0],                            -- ttxx
    ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0],                            -- txtx
    ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0],                            -- txxt
    ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2],                            -- txyz
    ![Sum.inl 0, Sum.inr 0, Sum.inr 2, Sum.inr 1],                            -- txzy
    ![Sum.inr 0, Sum.inl 0, Sum.inl 0, Sum.inr 0],                            -- xttx
    ![Sum.inr 0, Sum.inl 0, Sum.inr 0, Sum.inl 0],                            -- xtxt
    ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2],                            -- xtyz
    ![Sum.inr 0, Sum.inl 0, Sum.inr 2, Sum.inr 1],                            -- xtzy
    ![Sum.inr 0, Sum.inr 0, Sum.inl 0, Sum.inl 0],                            -- xxtt
    ![Sum.inr 0, Sum.inr 0, Sum.inr 0, Sum.inr 0],                            -- xxxx
    ![Sum.inr 0, Sum.inr 0, Sum.inr 1, Sum.inr 1],                            -- xxyy
    ![Sum.inr 0, Sum.inr 0, Sum.inr 2, Sum.inr 2],                            -- xxzz
    ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2],                            -- xytz
    ![Sum.inr 0, Sum.inr 1, Sum.inr 0, Sum.inr 1],                            -- xyxy
    ![Sum.inr 0, Sum.inr 1, Sum.inr 1, Sum.inr 0],                            -- xyyx
    ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0],                            -- xyzt
    ![Sum.inr 0, Sum.inr 2, Sum.inl 0, Sum.inr 1],                            -- xzty
    ![Sum.inr 0, Sum.inr 2, Sum.inr 0, Sum.inr 2],                            -- xzxz
    ![Sum.inr 0, Sum.inr 2, Sum.inr 1, Sum.inl 0],                            -- xzyt
    ![Sum.inr 0, Sum.inr 2, Sum.inr 2, Sum.inr 0]]                            -- xzzx

/-- The `k`-th representative and its two cyclings; for `tttt` the three coincide. -/
def orbit (k : Fin 22) : Finset (Fin 4 → Fin 1 ⊕ Fin 3) :=
  {orbitRep k, cycIdx (orbitRep k), cycIdx (cycIdx (orbitRep k))}

/-- The vectors in one of the `22` orbits are exactly the flip-fixed ones, a finite check. -/
lemma isFlipFixed_iff_exists_mem_orbit :
    ∀ d, IsFlipFixed d ↔ ∃ k, d ∈ orbit k := by
  decide +kernel

/-- Different orbits share no index vector, a finite check. -/
lemma disjoint_orbit : ∀ k l : Fin 22, k ≠ l → Disjoint (orbit k) (orbit l) := by
  decide +kernel

/-- An index vector lies in at most one orbit. -/
lemma eq_of_mem_orbit {k l : Fin 22} {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hk : d ∈ orbit k) (hl : d ∈ orbit l) : k = l :=
  by_contra fun h => Finset.disjoint_left.1 (disjoint_orbit k l h) hk hl

/-- A tensor unchanged by cycling takes, on an orbit, its value at the representative. -/
lemma eq_orbitRep_of_mem_orbit {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : ∀ d, c (cycIdx d) = c d) {k : Fin 22} {d : Fin 4 → Fin 1 ⊕ Fin 3}
    (h : d ∈ orbit k) : c d = c (orbitRep k) := by
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · rfl
  · exact hc _
  · rw [hc, hc]

/-- The coefficient tensor with orbit coordinates `b`, and `0` off the orbits. -/
noncomputable def ofOrbitCoord (b : Fin 22 → ℂ) (d : Fin 4 → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ k, if d ∈ orbit k then b k else 0

/-- An invariant coefficient tensor is rebuilt from its `22` orbit coordinates. -/
lemma eq_ofOrbitCoord {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    c = ofOrbitCoord fun k => c (orbitRep k) := by
  funext d
  by_cases hd : IsFlipFixed d
  · obtain ⟨k, hk⟩ := (isFlipFixed_iff_exists_mem_orbit d).1 hd
    rw [ofOrbitCoord, Finset.sum_eq_single k, ite_eq_left hk,
      eq_orbitRep_of_mem_orbit (apply_cycIdx hc) hk]
    · exact fun l _ hl => ite_eq_right fun hdl => hl (eq_of_mem_orbit hdl hk)
    · exact fun h => absurd (Finset.mem_univ k) h
  · rw [eq_zero_of_not_isFlipFixed hc hd]
    exact (Finset.sum_eq_zero fun k _ =>
      ite_eq_right fun hk => hd ((isFlipFixed_iff_exists_mem_orbit d).2 ⟨k, hk⟩)).symm

/-- Contracting against such a tensor collects the `256` index vectors into the `22` orbits. -/
lemma sum_mul_ofOrbitCoord (f : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (b : Fin 22 → ℂ) :
    ∑ e, f e * ofOrbitCoord b e = ∑ l, (∑ e ∈ orbit l, f e) * b l := by
  simp only [ofOrbitCoord, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_mul]

/-!

## F.2. The orbit matrix

Take `16 c_d = ∑_e transitionZ 2 d e 0 * c_e` at a representative and its two cyclings and add.
The left gives `48` times one orbit coordinate, the right collects the `256` index vectors into
the `22` orbits, and what is left is `M b = 48 b` with `M = orbitMatrix` below and
`48 = 3 * 16`. Entry `M k l` sums the transitions from the three cyclings of the representative
of orbit `k` into orbit `l` (`orbitMatrix_apply`, checked over `484` entries), so the printed
integers are not meant to be read; `M` is not symmetric, a row carrying three cyclings and a
column an orbit.
-/

/-- Forty-eight times the weight-zero projection along `z` on the orbit coordinates, the three
  cyclings summed and not averaged, so `48 = 3 * 16`. Meaningful only through
  `orbitMatrix_apply`. -/
def orbitMatrix : Matrix (Fin 22) (Fin 22) ℤ :=
  !![18, -6, -6, -6, 0, 0, -6, -6, 0, 0, -6, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -2, 22, -2, -2, 0, 0, -2, -2, 0, 0, 6, -2, -8, -8, 0, 0, 0, 0, 0, 0, 0, 0;
    -2, -2, 22, -2, 0, 0, -2, 6, 0, 0, -2, -2, 0, 0, 0, -8, 0, 0, 0, -8, 0, 0;
    -2, -2, -2, 22, 0, 0, 6, -2, 0, 0, -2, -2, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8;
    0, 0, 0, 0, 24, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0;
    0, 0, 0, 0, 0, 24, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, -8, 0;
    -2, -2, -2, 6, 0, 0, 22, -2, 0, 0, -2, -2, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8;
    -2, -2, 6, -2, 0, 0, -2, 22, 0, 0, -2, -2, 0, 0, 0, -8, 0, 0, 0, -8, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 24, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, -8, 0;
    0, 0, 0, 0, 0, -8, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, -8, -8, 0, 0, 0;
    -2, 6, -2, -2, 0, 0, -2, -2, 0, 0, 22, -2, -8, -8, 0, 0, 0, 0, 0, 0, 0, 0;
    6, -2, -2, -2, 0, 0, -2, -2, 0, 0, -2, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -8, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 24, 0, 0, -8, 0, 0, 0, 0;
    0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 24, 0, 0, 0, 0;
    0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, -8, 0;
    0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0;
    0, 0, 0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 24, 0;
    0, 0, 0, -8, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32]

/-- Decidability for a matrix against a function; search misses the `Matrix` synonym. -/
private instance decidableForallEntries {n : ℕ} (f : Matrix (Fin n) (Fin n) ℤ)
    (g : Fin n → Fin n → ℤ) : Decidable (∀ k l, f k l = g k l) :=
  @Nat.decidableForallFin n _ fun _ => @Nat.decidableForallFin n _ fun _ =>
    Int.instDecidableEq _ _

/-- The same for two matrices, which is the shape of `certificate`. -/
private instance decidableForallEntries' {n : ℕ} (f g : Matrix (Fin n) (Fin n) ℤ) :
    Decidable (∀ k l, f k l = g k l) :=
  @Nat.decidableForallFin n _ fun _ => @Nat.decidableForallFin n _ fun _ =>
    Int.instDecidableEq _ _

/-- Each entry sums the `z`-axis transitions from orbit `k` into orbit `l`, a finite check. -/
lemma orbitMatrix_apply : ∀ k l : Fin 22,
    orbitMatrix k l = ∑ e ∈ orbit l, (transitionZ 2 (orbitRep k) e 0
      + transitionZ 2 (cycIdx (orbitRep k)) e 0
      + transitionZ 2 (cycIdx (cycIdx (orbitRep k))) e 0) := by
  decide +kernel

/-- The orbit coordinates of an invariant coefficient tensor satisfy `M b = 48 b`. -/
lemma orbitMatrix_mulVec {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) :
    orbitMatrix.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => c (orbitRep k))
      = (48 : ℂ) • fun k => c (orbitRep k) := by
  have h : ∀ d, 16 * c d
      = ∑ l, (∑ e ∈ orbit l, ((transitionZ 2 d e 0 : ℤ) : ℂ)) * c (orbitRep l) := by
    intro d
    rw [sixteen_mul_eq_sum_transitionZ hc 2 d]
    conv_lhs => rw [eq_ofOrbitCoord hc]
    exact sum_mul_ofOrbitCoord _ _
  funext k
  have h₀ := h (orbitRep k)
  have h₁ := h (cycIdx (orbitRep k))
  have h₂ := h (cycIdx (cycIdx (orbitRep k)))
  rw [apply_cycIdx hc] at h₁
  rw [apply_cycIdx hc, apply_cycIdx hc] at h₂
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, orbitMatrix_apply, Pi.smul_apply,
    smul_eq_mul, Int.cast_sum, Int.cast_add, Finset.sum_add_distrib, add_mul]
  linear_combination -(h₀ + h₁ + h₂)

/-!

## G. The certificate

F leaves `M b = 48 b` for the orbit coordinates `b k = c (orbitRep k)`. Four solutions are
known, the orbit coordinates `v i = contractionOrbit i` of the tensors of B; there are no
others, by one identity between `22 × 22` integer matrices:

`M (M - 32) (M - 16) (M² - 44 M + 192) = 393216 • projector`,

where `projector = ∑ i, (v i) (w i)ᵀ` is four rank-one matrices built from the columns `v i`
and rows `w i = contractionWeight i`, so it sends any vector to a combination of the `v i`.
Lean checks it by computing all `484` entries of each side. On a solution `b` every factor
turns `M` into `48`, giving `48² - 44 * 48 + 192 = 384`, then `32`, `16`, `48`, so the left
sends `b` to `48 * 16 * 32 * 384 = 9437184` times `b` and the right to `393216 • (projector b)`.
As `9437184 = 393216 * 24` this leaves `projector b = 24 b` (`projector_mulVec`), writing `b`,
and with it `c`, as a combination of the four; the `24` is
`contractionWeight_mul_contractionOrbit`. The identity is
`λ (3λ - 2) (3λ - 1) (12λ² - 11λ + 1) / 4` at `λ = M / 48` with denominators cleared, but that
is only where it came from: the file proves nothing about the spectrum.
-/

/-- The orbit coordinates of the `i`-th coefficient tensor. -/
def contractionOrbit (i : Fin 4) (k : Fin 22) : ℤ := contractionCoeff i (orbitRep k)

/-- Four rows of `22` integers paired with `contractionOrbit` to build `projector`. Found by
  computation and characterised by `contractionWeight_mul_contractionOrbit`; unrelated to boost
  weight. -/
def contractionWeight : Fin 4 → Fin 22 → ℤ :=
  ![![1, -5, 1, 1, 0, 0, 1, 1, 0, 0, -5, 3, 5, 5, 0, -1, -1, 0, 0, -1, 0, -1],
    ![1, 1, -5, 1, 0, 0, 1, -5, 0, 0, 1, 3, -1, -1, 0, 5, -1, 0, 0, 5, 0, -1],
    ![1, 1, 1, -5, 0, 0, -5, 1, 0, 0, 1, 3, -1, -1, 0, -1, 5, 0, 0, -1, 0, 5],
    ![0, 0, 0, 0, 3, -3, 0, 0, -3, 3, 0, 0, 0, 0, 3, 0, 0, -3, -3, 0, 3, 0]]

/-- The weight rows and orbit coordinates pair to `24 δᵢⱼ`, a finite check. -/
lemma contractionWeight_mul_contractionOrbit : ∀ i j : Fin 4,
    ∑ k, contractionWeight i k * contractionOrbit j k = if i = j then 24 else 0 := by
  decide +kernel

/-- Four rank-one matrices, so it sends any vector to a combination of the `v i`. -/
def projector : Matrix (Fin 22) (Fin 22) ℤ :=
  Matrix.of fun k l => ∑ i, contractionOrbit i k * contractionWeight i l

/-- An identity between `22 × 22` integer matrices, a finite check over `484` entries. -/
lemma certificate :
    orbitMatrix * (orbitMatrix - 32 • 1) * (orbitMatrix - 16 • 1)
      * (orbitMatrix * orbitMatrix - 44 • orbitMatrix + 192 • 1) = 393216 • projector := by
  ext k l
  revert k l
  decide +kernel

/-- The integer projector matrix acts on invariant orbit coordinates by multiplication by `24`.
  The `24` is the normalization of `projector`: each factor of the certificate acts on such a
  vector as a scalar, `M` by `48`, `M - z` by `48 - z` and the quadratic factor by
  `48 ^ 2 - 44 * 48 + 192 = 384`, so the left-hand side scales it by
  `48 * 32 * 16 * 384 = 9437184`, and dividing by the `393216` on the right leaves `24`. -/
lemma projector_mulVec {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    projector.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => c (orbitRep k))
      = (24 : ℂ) • fun k => c (orbitRep k) := by
  set b : Fin 22 → ℂ := fun k => c (orbitRep k) with hb
  set M : Matrix (Fin 22) (Fin 22) ℂ := orbitMatrix.map (Int.cast : ℤ → ℂ) with hM
  have hMb : M *ᵥ b = (48 : ℂ) • b := orbitMatrix_mulVec hc
  have hlin : ∀ z : ℂ, (M - z • 1) *ᵥ b = (48 - z) • b := fun z => by
    rw [Matrix.sub_mulVec, hMb, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hquad : (M * M - (44 : ℂ) • M + (192 : ℂ) • 1) *ᵥ b = (384 : ℂ) • b := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hMb, Matrix.mulVec_smul,
      hMb, Matrix.smul_mulVec, hMb, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, smul_smul,
      ← sub_smul, ← add_smul]
    norm_num
  have h₂ : (M - (16 : ℂ) • 1) *ᵥ ((384 : ℂ) • b) = (12288 : ℂ) • b := by
    rw [Matrix.mulVec_smul, hlin, smul_smul]
    norm_num
  have h₃ : (M - (32 : ℂ) • 1) *ᵥ ((12288 : ℂ) • b) = (196608 : ℂ) • b := by
    rw [Matrix.mulVec_smul, hlin, smul_smul]
    norm_num
  have h₄ : M *ᵥ ((196608 : ℂ) • b) = (9437184 : ℂ) • b := by
    rw [Matrix.mulVec_smul, hMb, smul_smul]
    norm_num
  have hcert : M * (M - (32 : ℂ) • 1) * (M - (16 : ℂ) • 1)
      * (M * M - (44 : ℂ) • M + (192 : ℂ) • 1)
        = (393216 : ℂ) • projector.map (Int.cast : ℤ → ℂ) := by
    have h := congrArg (Int.castRingHom ℂ).mapMatrix certificate
    simpa only [map_mul, map_sub, map_add, map_nsmul, map_one, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat, ← hM] using h
  have hpb : (M * (M - (32 : ℂ) • 1) * (M - (16 : ℂ) • 1)
      * (M * M - (44 : ℂ) • M + (192 : ℂ) • 1)) *ᵥ b
        = ((393216 : ℂ) • projector.map (Int.cast : ℤ → ℂ)) *ᵥ b := by
    rw [hcert]
  rw [← Matrix.mulVec_mulVec, hquad, ← Matrix.mulVec_mulVec, h₂, ← Matrix.mulVec_mulVec, h₃, h₄,
    Matrix.smul_mulVec] at hpb
  refine smul_right_injective (Fin 22 → ℂ) (show (393216 : ℂ) ≠ 0 by norm_num) ?_
  simp only [← hpb, smul_smul]
  norm_num

/-- `24` times an orbit coordinate of an invariant tensor, read entry by entry off the previous
  lemma: `projector` is built from the columns `contractionOrbit i` and the rows
  `contractionWeight i`. -/
lemma orbitCoord_eq {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (k : Fin 22) :
    24 * c (orbitRep k)
      = ∑ i, (contractionOrbit i k : ℂ) * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l) := by
  have hk := congrFun (projector_mulVec hc) k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, projector,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul] at hk
  rw [Finset.sum_comm] at hk
  rw [← hk]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

/-- An invariant coefficient tensor is a combination of the four. -/
theorem exists_eq_sum {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    ∃ a : Fin 4 → ℂ, c = fun d => ∑ i, a i * ((contractionCoeff i d : ℤ) : ℂ) := by
  refine ⟨fun i => 24⁻¹ * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l), funext fun d => ?_⟩
  have hfour : ∀ i d, ((contractionCoeff i d : ℤ) : ℂ)
      = ∑ k, if d ∈ orbit k then (contractionOrbit i k : ℂ) else 0 :=
    fun i d => congrFun (eq_ofOrbitCoord (isInvariantCoeff_contractionCoeff i)) d
  have hb : ∀ k, c (orbitRep k) = 24⁻¹ * ∑ i, (contractionOrbit i k : ℂ)
      * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l) :=
    fun k => by rw [← orbitCoord_eq hc]; ring
  conv_lhs => rw [eq_ofOrbitCoord hc, ofOrbitCoord]
  rw [Finset.sum_congr rfl fun k _ => by rw [hb k]]
  simp only [hfour, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : d ∈ orbit k
  · simp only [hk, ite_true, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  · simp [hk]

/-!

## H. The classification, and the classification modulo a stable submodule

C to G give `exists_smul_contraction_of_invariant`, the case `S = ⊥` of the theorem. For
general `S`, right to left is immediate and does not use `hS`; left to right passes to the
quotient `B ⧸ S`, that is `B` with `S` declared zero and `S.mkQ` the map to classes. Stability
lets `repLorentz` act there and the classes of the components again form a rank-four family,
both by `IsLorentzCovariant.quotient`, so back in `B` the difference between `x` and the
matching combination of contractions has zero class, hence lies in `S`, and is invariant as a
difference of invariants.
-/

/-- Every Lorentz invariant of the span is a combination of the four contractions. -/
theorem exists_smul_contraction_of_invariant (hT : IsLorentzCovariant 4 B repLorentz T)
    {x : B} (hx : x ∈ componentSpan T) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ,
      x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_componentSpan hx hinv
  obtain ⟨a, rfl⟩ := exists_eq_sum hc
  refine ⟨a 0, a 1, a 2, a 3, ?_⟩
  rw [← sum_smul_contraction]
  simp only [contraction_eq, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- Left to right in `mem_span_sup_invariant_iff`, proved in the quotient by `S`. -/
lemma exists_smul_contraction_of_invariant_subset
    (hT : IsLorentzCovariant 4 B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
      x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T + y
      ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  obtain ⟨a₁, a₂, a₃, a₄, hcomb⟩ := exists_smul_contraction_of_invariant (hT.quotient S hS)
    (mkQ_mem_componentSpan T S hx) fun g => by rw [quotient_apply_mkQ, hinv g]
  refine ⟨a₁, a₂, a₃, a₄,
    x - (a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
      + a₄ • epsilonContraction T), ?_, by abel, fun g => ?_⟩
  · rw [← Submodule.ker_mkQ S, LinearMap.mem_ker, map_sub, hcomb]
    simp only [outerContraction, innerContraction, splitContraction, epsilonContraction,
      map_add, map_smul, map_sum]
    abel
  · rw [map_sub, hinv g, repLorentz_smul_contraction hT a₁ a₂ a₃ a₄ g]

/-- A vector of `componentSpan T ⊔ S`, the sums `u + y` with `u` in the span and `y` in the
  Lorentz-stable subspace `S`, is invariant exactly when it is a combination of the four
  contractions plus an invariant `y` of `S`. `hS` is used only left to right. -/
theorem mem_span_sup_invariant_iff (hT : IsLorentzCovariant 4 B repLorentz T) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    (x ∈ componentSpan T ⊔ S ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
        x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
          + a₄ • epsilonContraction T + y
        ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  refine ⟨fun h => exists_smul_contraction_of_invariant_subset hT S hS h.1 h.2, ?_⟩
  rintro ⟨a₁, a₂, a₃, a₄, y, hyS, rfl, hyinv⟩
  refine ⟨add_mem (Submodule.mem_sup_left (smul_contraction_mem_span (T := T) a₁ a₂ a₃ a₄))
    (Submodule.mem_sup_right hyS), fun g => ?_⟩
  rw [map_add, repLorentz_smul_contraction hT a₁ a₂ a₃ a₄ g, hyinv g]

end RankFour

end Lorentz
