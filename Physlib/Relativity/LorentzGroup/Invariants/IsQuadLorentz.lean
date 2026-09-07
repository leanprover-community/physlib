/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LightConeDeriv
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- Not used here; `Peeling` reaches it through this file.
public import Physlib.Relativity.IsLorentzDeriv
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
`repLorentz` of `SL(2,ℂ)`, and `IsQuadLorentz B repLorentz T` says the group moves them with
one factor of the Lorentz matrix per slot (A). A vector of `B` is invariant when every
`repLorentz g` fixes it, and `hT.span` is the set of contractions `∑_d c_d • T d`. The theorem
`mem_span_sup_invariant_iff` (H) allows a Lorentz-stable subspace `S` beside the span, where
the files using it park their other tensors: a vector of `hT.span ⊔ S`, the sums `u + y`, is
invariant exactly when it is a combination of the four contractions plus an invariant `y` of
`S`. For `S = ⊥` that is `exists_smul_contraction_of_invariant`.

The four coefficient tensors are invariant, by `Λ η Λᵀ = η` and `det Λ = 1` (B); an invariant
of the span is the contraction of an invariant one, by projecting off the tensors that contract
to `0` (C); and such a tensor is a combination of the four, two rotations cutting `256`
coefficients to `22` (D), a boost keeping only what it does not rescale (E), and the `22 × 22`
integer equation left being solved by one checked matrix identity (F, G).
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C BoostWeight

/-!

## A. Quadruple Lorentz tensors, their span, and coefficient tensors

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes; an index vector
`d : Fin 4 → Fin 1 ⊕ Fin 3` puts one in each slot, so `T d` is `T^{μνρσ}` at `(μ, ν, ρ, σ) = d`.
The law is

`repLorentz g (T l) = ∑_a Λ_{a₀ l₀} Λ_{a₁ l₁} Λ_{a₂ l₂} Λ_{a₃ l₃} • T a`,

with `l` free and `a` summed, and transforming a contraction moves its coefficient tensor by
`(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯ Λ_{a₃ d₃}`, now with `a` free and `d` summed
(`repLorentz_sum_smul`): the same `Λ`, never its inverse, but transposed index slots, which is
what makes `act Λᵀ` the adjoint of `act Λ` in C. Two invariance conditions are therefore in
play, kept apart by name: `x : B` is Lorentz invariant when `repLorentz g x = x`, and `c` is
`IsInvariantCoeff` when `act Λ c = c`.
-/

/-- A family `T` of vectors of `B`, one per index vector, which `repLorentz` moves the way the
  components of a rank-four tensor transform: one factor of the Lorentz matrix per slot, the
  moved index second in each factor and the summed one first. -/
structure IsQuadLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 4 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 4), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsQuadLorentz

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsQuadLorentz B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the `256` components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsQuadLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a contraction `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-- Every contraction of the components lies in their span. -/
lemma sum_smul_mem_span (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) : ∑ d, c d • T d ∈ hT.span :=
  (hT.mem_span_iff _).2 ⟨c, rfl⟩

/-- The action of a real `4 × 4` matrix on coefficient tensors, one factor per slot:
  `(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯ Λ_{a₃ d₃}`, with `a` free and `d` summed. Same `Λ` as on
  the components, never its inverse, but with the free index in the first slot, not the second. -/
def act (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (a : Fin 4 → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ d, c d * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)

include hT in
/-- Transforming a contraction is the same as contracting the transformed coefficient tensor. -/
lemma repLorentz_sum_smul (g : SL(2,ℂ)) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) :
    repLorentz g (∑ d, c d • T d) = ∑ a, act (SL2C.toLorentzGroup g).1 c a • T a := by
  simp only [map_sum, map_smul, hT.repLorentz_T, Finset.smul_sum, smul_smul, act,
    Finset.sum_smul]
  exact Finset.sum_comm

/-- A coefficient tensor fixed by `act` of the Lorentz matrix of every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) : Prop :=
  ∀ g : SL(2,ℂ), act (SL2C.toLorentzGroup g).1 c = c

include hT in
/-- Contracting with an invariant coefficient tensor gives a Lorentz invariant vector. -/
lemma repLorentz_sum_smul_of_isInvariantCoeff {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (g : SL(2,ℂ)) :
    repLorentz g (∑ d, c d • T d) = ∑ d, c d • T d := by
  rw [hT.repLorentz_sum_smul, hc g]

/-!

## B. The four contractions

## B.1. The metric, the Levi-Civita symbol and the contractions

`etaZ` is `η = diag(1, -1, -1, -1)`, checked against `minkowskiMatrix` by `etaZ_cast`, and
`epsilonSignZ d` is the determinant of the matrix whose rows are the unit vectors of
`d 0, d 1, d 2, d 3`: `1` on `(t, x, y, z)`, minus itself under a swap of two slots, `0` on a
repeated direction. Both are integer valued, as is everything F and G compute with. The metric
pairings use the slots `(0,1)(2,3)`, `(0,2)(1,3)` and `(0,3)(1,2)` for `outerContraction`,
`innerContraction` and `splitContraction`; `contractionCoeff` holds the four coefficient
tensors and `contraction T` the four contractions in that order.
-/

/-- The Minkowski sign of a direction: `+1` on time, `-1` on each spatial axis. -/
def minkowskiSignZ : Fin 1 ⊕ Fin 3 → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- The Minkowski metric `η = diag(1, -1, -1, -1)`, integer valued so the later checks compute. -/
def etaZ (μ ν : Fin 1 ⊕ Fin 3) : ℤ := if μ = ν then minkowskiSignZ μ else 0

/-- The Levi-Civita symbol; the row index is a slot, carried across by `finSumFinEquiv`. -/
def epsilonSignZ (d : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 => if d (finSumFinEquiv μ) = ν then (1 : ℤ) else 0).det

/-- The four coefficient tensors: the three metric pairings, then the Levi-Civita symbol. -/
def contractionCoeff : Fin 4 → (Fin 4 → Fin 1 ⊕ Fin 3) → ℤ :=
  ![fun d => etaZ (d 0) (d 1) * etaZ (d 2) (d 3),
    fun d => etaZ (d 0) (d 2) * etaZ (d 1) (d 3),
    fun d => etaZ (d 0) (d 3) * etaZ (d 1) (d 2),
    epsilonSignZ]

/-- The contraction `η_{μν} η_{ρσ} T^{μνρσ}`, pairing slots `(0,1)` and `(2,3)`. -/
noncomputable def outerContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 1) * etaZ (d 2) (d 3) : ℤ) : ℂ) • T d

/-- The contraction `η_{μρ} η_{νσ} T^{μνρσ}`, pairing slots `(0,2)` and `(1,3)`. -/
noncomputable def innerContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 2) * etaZ (d 1) (d 3) : ℤ) : ℂ) • T d

/-- The contraction `η_{μσ} η_{νρ} T^{μνρσ}`, pairing slots `(0,3)` and `(1,2)`. -/
noncomputable def splitContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((etaZ (d 0) (d 3) * etaZ (d 1) (d 2) : ℤ) : ℂ) • T d

/-- The contraction `ε_{μνρσ} T^{μνρσ}` with the Levi-Civita symbol. -/
noncomputable def epsilonContraction (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : ℂ) • T d

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
lemma outerContraction_mem_span : outerContraction T ∈ hT.span := hT.sum_smul_mem_span _

/-- The inner contraction lies in the span of the components. -/
lemma innerContraction_mem_span : innerContraction T ∈ hT.span := hT.sum_smul_mem_span _

/-- The split contraction lies in the span of the components. -/
lemma splitContraction_mem_span : splitContraction T ∈ hT.span := hT.sum_smul_mem_span _

/-- The Levi-Civita contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span : epsilonContraction T ∈ hT.span := hT.sum_smul_mem_span _

/-- A combination of the four contractions lies in the span of the components. -/
lemma smul_contraction_mem_span (a₁ a₂ a₃ a₄ : ℂ) :
    a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
      + a₄ • epsilonContraction T ∈ hT.span :=
  add_mem (add_mem (add_mem (Submodule.smul_mem _ _ hT.outerContraction_mem_span)
    (Submodule.smul_mem _ _ hT.innerContraction_mem_span))
    (Submodule.smul_mem _ _ hT.splitContraction_mem_span))
    (Submodule.smul_mem _ _ hT.epsilonContraction_mem_span)

/-!

## B.2. The four coefficient tensors are invariant

`Λ η Λᵀ = η` defines the Lorentz group; entry by entry it is `sum_etaZ_mul`, and a pair of
metrics is two copies of it, one per pair of slots (`act_outerPair`). The inner and split
pairings are the outer one with the slots permuted (`act_outerPair_comp`). The symbol against
four rows of `M` gives `det M` times the symbol of those rows (`sum_epsilonSignZ_mul_prod`),
and `det Λ = 1` here: the only use of the determinant, and the reason there are four invariants
and not three, a reflection having `det = -1`. `sum_pi_four`, `coe_epsilonSignZ` and
`det_eq_sum_perm_prod` are bookkeeping.
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

/-- The integer metric agrees with `minkowskiMatrix`, which is therefore `diag(1, -1, -1, -1)`. -/
lemma etaZ_cast (μ ν : Fin 1 ⊕ Fin 3) : ((etaZ μ ν : ℤ) : ℝ) = minkowskiMatrix μ ν := by
  rcases eq_or_ne μ ν with rfl | h
  · match μ with
    | Sum.inl i => fin_cases i; simp [etaZ, minkowskiSignZ]
    | Sum.inr i => simp [etaZ, minkowskiSignZ]
  · simp [etaZ, h]

/-- The defining relation `Λ η Λᵀ = η`, read on the entry `(a, b)`. -/
lemma sum_etaZ_mul (Λ : LorentzGroup 3) (a b : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ((etaZ x y : ℤ) : ℂ)
        * (((Λ.1 a x : ℝ) : ℂ) * ((Λ.1 b y : ℝ) : ℂ))
      = ((etaZ a b : ℤ) : ℂ) := by
  have hR : ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3,
      ((etaZ x y : ℤ) : ℝ) * (Λ.1 a x * Λ.1 b y) = ((etaZ a b : ℤ) : ℝ) := by
    have h := congrFun (congrFun
      (LorentzGroup.mul_minkowskiMatrix_mul_transpose (Λ := Λ)) a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [etaZ_cast, ← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [etaZ_cast]; ring
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  push_cast at hC ⊢
  exact hC

/-- The pairing of slots `(0,1)` and `(2,3)` is fixed: two copies of `sum_etaZ_mul`. -/
lemma act_outerPair (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((etaZ (d 0) (d 1) * etaZ (d 2) (d 3) : ℤ) : ℂ)) a
      = ((etaZ (a 0) (a 1) * etaZ (a 2) (a 3) : ℤ) : ℂ) := by
  have h : ∀ x y z w : Fin 1 ⊕ Fin 3,
      ((etaZ (![x, y, z, w] 0) (![x, y, z, w] 1)
          * etaZ (![x, y, z, w] 2) (![x, y, z, w] 3) : ℤ) : ℂ)
        * ∏ s, ((Λ.1 (a s) (![x, y, z, w] s) : ℝ) : ℂ)
      = (((etaZ x y : ℤ) : ℂ) * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 1) y : ℝ) : ℂ)))
        * (((etaZ z w : ℤ) : ℂ) * (((Λ.1 (a 2) z : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
    intro x y z w
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    push_cast
    ring
  rw [act, sum_pi_four]
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, sum_etaZ_mul]
  push_cast
  ring

/-- The same for the slots permuted by `σ`, by renaming the summation variable. -/
lemma act_outerPair_comp (σ : Equiv.Perm (Fin 4)) (Λ : LorentzGroup 3)
    (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((etaZ (d (σ 0)) (d (σ 1)) * etaZ (d (σ 2)) (d (σ 3)) : ℤ) : ℂ)) a
      = ((etaZ (a (σ 0)) (a (σ 1)) * etaZ (a (σ 2)) (a (σ 3)) : ℤ) : ℂ) := by
  have h := act_outerPair Λ (a ∘ σ)
  rw [act, ← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 1 ⊕ Fin 3)))] at h
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_def,
    id] at h
  rw [← h, act]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.prod_comp σ fun i => ((Λ.1 (a i) (d i) : ℝ) : ℂ)]

/-- Bookkeeping: the symbol reads the same in every commutative ring. -/
lemma coe_epsilonSignZ {R : Type*} [CommRing R] (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    ((epsilonSignZ d : ℤ) : R)
      = (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 =>
          if d (finSumFinEquiv μ) = ν then (1 : R) else 0).det := by
  have h := RingHom.map_det (Int.castRingHom R)
    (Matrix.of fun μ ν : Fin 1 ⊕ Fin 3 => if d (finSumFinEquiv μ) = ν then (1 : ℤ) else 0)
  simp only [Int.coe_castRingHom, RingHom.mapMatrix_apply] at h
  rw [epsilonSignZ, h]
  congr 1
  ext μ ν
  by_cases hdν : d (finSumFinEquiv μ) = ν <;> simp [Matrix.map_apply, hdν]

/-- Bookkeeping: the Leibniz formula, with the permutation moving the column index. -/
lemma det_eq_sum_perm_prod {R : Type*} [CommRing R]
    (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) R) :
    X.det = ∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 3),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ μ, X μ (σ μ) := by
  rw [← Matrix.det_transpose X, Matrix.det_apply']
  rfl

/-- Against four rows of `M` the symbol gives `det M` times the symbol of those rows. -/
lemma sum_epsilonSignZ_mul_prod {R : Type*} [CommRing R]
    (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) R) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsilonSignZ d : ℤ) : R) * ∏ i, M (a i) (d i)
      = M.det * ((epsilonSignZ a : ℤ) : R) := by
  classical
  have hrows : (Matrix.of fun μ ν => M (a (finSumFinEquiv μ)) ν).det
      = ((epsilonSignZ a : ℤ) : R) * M.det := by
    rw [coe_epsilonSignZ, ← Matrix.det_mul]
    congr 1
    ext μ ν
    simp [Matrix.mul_apply]
  have hfun : ∀ (σ : Equiv.Perm (Fin 1 ⊕ Fin 3)) (d : Fin 4 → Fin 1 ⊕ Fin 3),
      (∀ μ, d (finSumFinEquiv μ) = σ μ) ↔ d = fun s => σ (finSumFinEquiv.symm s) := by
    refine fun σ d => ⟨fun h => funext fun s => ?_, fun h μ => by subst h; simp⟩
    rw [← h, Equiv.apply_symm_apply]
  rw [mul_comm, ← hrows, det_eq_sum_perm_prod]
  simp only [coe_epsilonSignZ, det_eq_sum_perm_prod, Matrix.of_apply, Finset.sum_mul,
    Fintype.prod_boole, hfun, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
  congr 1

/-- The symbol is fixed by a Lorentz matrix of determinant `1`; in general it picks up `det Λ`. -/
lemma act_epsilonSignZ (Λ : LorentzGroup 3) (hΛ : Λ.1.det = 1) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((epsilonSignZ d : ℤ) : ℂ)) a = ((epsilonSignZ a : ℤ) : ℂ) := by
  have hdet : (Complex.ofRealHom.mapMatrix Λ.1).det = 1 := by
    rw [← RingHom.map_det, hΛ]
    simp
  have h := sum_epsilonSignZ_mul_prod (Complex.ofRealHom.mapMatrix Λ.1) a
  rw [hdet, one_mul] at h
  rw [← h]
  rfl

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
  · exact act_epsilonSignZ _ (SL2C.toLorentzGroup_det_one g) a

/-!

## B.3. The four contractions are Lorentz invariant

Contracting with an invariant coefficient tensor gives an invariant vector, so each contraction
is invariant, as is any combination: with `smul_contraction_mem_span`, the easy direction.
-/

include hT in
/-- Each of the four contractions is Lorentz invariant, its coefficient tensor being invariant. -/
lemma repLorentz_contraction (i : Fin 4) (g : SL(2,ℂ)) :
    repLorentz g (contraction T i) = contraction T i := by
  rw [contraction_eq,
    hT.repLorentz_sum_smul_of_isInvariantCoeff (isInvariantCoeff_contractionCoeff i)]

include hT in
/-- The outer contraction is Lorentz invariant. -/
lemma repLorentz_outerContraction (g : SL(2,ℂ)) :
    repLorentz g (outerContraction T) = outerContraction T :=
  hT.repLorentz_contraction 0 g

include hT in
/-- The inner contraction is Lorentz invariant. -/
lemma repLorentz_innerContraction (g : SL(2,ℂ)) :
    repLorentz g (innerContraction T) = innerContraction T :=
  hT.repLorentz_contraction 1 g

include hT in
/-- The split contraction is Lorentz invariant. -/
lemma repLorentz_splitContraction (g : SL(2,ℂ)) :
    repLorentz g (splitContraction T) = splitContraction T :=
  hT.repLorentz_contraction 2 g

include hT in
/-- The Levi-Civita contraction is Lorentz invariant. -/
lemma repLorentz_epsilonContraction (g : SL(2,ℂ)) :
    repLorentz g (epsilonContraction T) = epsilonContraction T :=
  hT.repLorentz_contraction 3 g

include hT in
/-- A combination of the four contractions is Lorentz invariant. -/
lemma repLorentz_smul_contraction (a₁ a₂ a₃ a₄ : ℂ) (g : SL(2,ℂ)) :
    repLorentz g (a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T)
      = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T := by
  simp only [map_add, map_smul, hT.repLorentz_outerContraction, hT.repLorentz_innerContraction,
    hT.repLorentz_splitContraction, hT.repLorentz_epsilonContraction]

/-!

## C. An invariant of the span is the contraction of an invariant tensor

The components may satisfy linear relations, so the `c` with `x = ∑ c_d • T d` is not
determined by `x` and need not be invariant. Let `K` be the coefficient tensors contracting to
`0`, a subspace of `ℂ^{256}` that the group preserves and that is the whole ambiguity in `c`.
Give `ℂ^{256}` the standard inner product `∑_d conj(u_d) v_d`, positive definite and unrelated
to `η`, written `EuclideanSpace ℂ (Fin 4 → Fin 1 ⊕ Fin 3)`, where `WithLp.toLp 2` and `.ofLp`
only move to and from the plain function type. The complement `Kᗮ` is preserved too, since
`act Λ` across the inner product becomes `act Λᵀ` (`inner_act_eq_inner_act_transpose`) and `Λᵀ`
is again such a matrix, that of `g†`; the action is not unitary, and is not used to be. So keep
the `Kᗮ` part of `c`: it still contracts to `x`, and acting on it changes it by an element of
`K` and of `Kᗮ`, hence by `0` (`exists_isInvariantCoeff_of_mem_span`).
-/

/-- The conjugate transpose `g†`, again in `SL(2,ℂ)`. -/
def dagger (g : SL(2,ℂ)) : SL(2,ℂ) := ⟨g.1ᴴ, by rw [Matrix.det_conjTranspose, g.2, star_one]⟩

/-- The Lorentz matrix of `g†` is the transpose of that of `g`. -/
lemma toLorentzGroup_dagger (g : SL(2,ℂ)) :
    (SL2C.toLorentzGroup (dagger g)).1 = (SL2C.toLorentzGroup g).1ᵀ :=
  SL2C.toLorentzGroup_conjTranspose rfl

/-- Contraction with the components, as a linear map on the inner product space. -/
noncomputable def contractₗ (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) :
    EuclideanSpace ℂ (Fin 4 → Fin 1 ⊕ Fin 3) →ₗ[ℂ] B where
  toFun c := ∑ d, c.ofLp d • T d
  map_add' c c' := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      smul_smul]

open scoped InnerProductSpace in
/-- Across the standard inner product the action of a real matrix `Λ` becomes that of `Λᵀ`. -/
lemma inner_act_eq_inner_act_transpose (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (u v : EuclideanSpace ℂ (Fin 4 → Fin 1 ⊕ Fin 3)) :
    ⟪u, WithLp.toLp 2 (act Λ v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (act Λᵀ u.ofLp), v⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, act, Matrix.transpose_apply, map_sum,
    map_mul, map_prod, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring

include hT in
/-- An invariant of the span is the contraction of an invariant coefficient tensor. -/
theorem exists_isInvariantCoeff_of_mem_span {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff x).1 hx
  have hcontr : ∀ (g : SL(2,ℂ)) (u : EuclideanSpace ℂ (Fin 4 → Fin 1 ⊕ Fin 3)),
      contractₗ T (WithLp.toLp 2 (act (SL2C.toLorentzGroup g).1 u.ofLp))
        = repLorentz g (contractₗ T u) :=
    fun g u => (hT.repLorentz_sum_smul g u.ofLp).symm
  set K := LinearMap.ker (contractₗ T) with hK
  obtain ⟨k, hk, k', hk', hkk'⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 c)
  have hx' : ∑ d, c d • T d = contractₗ T k' := by
    have h := congrArg (contractₗ T) hkk'
    rwa [map_add, LinearMap.mem_ker.1 hk, zero_add] at h
  refine ⟨k'.ofLp, fun g => ?_, hx'⟩
  have h1 : WithLp.toLp 2 (act (SL2C.toLorentzGroup g).1 k'.ofLp) - k' ∈ K := by
    rw [hK, LinearMap.mem_ker, map_sub, hcontr, ← hx', hinv, hx', sub_self]
  have h2 : WithLp.toLp 2 (act (SL2C.toLorentzGroup g).1 k'.ofLp) ∈ Kᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [inner_act_eq_inner_act_transpose, ← toLorentzGroup_dagger]
    refine Submodule.inner_right_of_mem_orthogonal (K := K) ?_ hk'
    rw [hK, LinearMap.mem_ker, hcontr, LinearMap.mem_ker.1 hu, map_zero]
  have h3 : WithLp.toLp 2 (act (SL2C.toLorentzGroup g).1 k'.ofLp) - k' ∈ K ⊓ Kᗮ :=
    ⟨h1, Submodule.sub_mem _ h2 hk'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
  exact congrArg WithLp.ofLp h3

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
      rw [toLorentzGroup_flipAxis_apply, if_pos rfl, Complex.ofReal_intCast]
  · intro d _ hda
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hda.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [toLorentzGroup_flipAxis_apply, if_neg hs, Complex.ofReal_zero]
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
lemma IsInvariantCoeff.eq_zero_of_not_isFlipFixed {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
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
    rw [toLorentzGroup_rotationCycle_apply, if_pos, Complex.ofReal_one]
    exact (congrFun (cycIdx_cycIdx_cycIdx a) s).symm
  · intro d _ hda
    have hne : cycIdx d ≠ a := fun h => hda (by rw [← h, cycIdx_cycIdx_cycIdx])
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hne
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [toLorentzGroup_rotationCycle_apply, if_neg fun h : a s = cycDir (d s) => hs h.symm,
      Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- An invariant coefficient tensor is constant on the orbits of the cyclic rotation. -/
lemma IsInvariantCoeff.apply_cycIdx {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
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

/-- A light-cone component: `c` contracted against one light-cone direction per slot. -/
def lightConeComponent (i : Fin 3) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin 4 → Fin 4) : ℂ :=
  ∑ a, (∏ s, lightConeCoeff i (κ s) (a s)) * c a

/-- The Lorentz matrix of a boost is symmetric. -/
lemma toLorentzGroup_boostAxis_symm (i : Fin 3) {t : ℝ} (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 a b
      = (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 b a :=
  congrFun (congrFun
    (SL2C.toLorentzGroup_conjTranspose (SL2C.boostAxis_conjTranspose i t ht).symm) a) b

/-- The boost with parameter `t` multiplies a light-cone component by `t` to the weight of `κ`. -/
lemma lightConeComponent_act_boostAxis (i : Fin 3) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (κ : Fin 4 → Fin 4) {t : ℝ} (ht : t ≠ 0) :
    lightConeComponent i (act (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 c) κ
      = ((t : ℝ) : ℂ) ^ (∑ s, lightConeWeight (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, act, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := sum_prod_lightConeCoeff i κ d ht
  simp only [toLorentzGroup_boostAxis_symm i ht (d _)] at h
  rw [← mul_assoc, mul_comm _ (c d), ← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- An invariant coefficient tensor has no light-cone component of nonzero weight. -/
lemma IsInvariantCoeff.lightConeComponent_eq_zero {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin 4 → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) ≠ 0) :
    lightConeComponent i c κ = 0 := by
  have h := lightConeComponent_act_boostAxis i c κ (two_ne_zero (α := ℝ))
  rw [hc] at h
  have h2 : ((2 : ℝ) : ℂ) ^ (∑ s, lightConeWeight (κ s)) ≠ 1 := by
    rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
      zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
    exact hκ
  exact (mul_left_eq_self₀.1 h.symm).resolve_left h2

/-!

## E.2. The weight-zero projection

Writing each coordinate direction in the light-cone basis recovers `c` from its light-cone
components (`eq_sum_lightConeComponent`), and for an invariant `c` only weight zero survives:
`16 * c d = ∑_e transitionZ i d e 0 * c e`. Time and the axis span the boost plane
(`InBoostPlane`); a direction in it is a half-sum of `D₀ ∓ Dᵢ`, so `lightConeCoeffInvZ` carries
twice the true coefficients and four slots give the `2 ^ 4 = 16`, bought for integer entries.
`transitionZ i d e m` is `16` times the entry, at `d` and `e`, of the map keeping total weight
`m`, built a slot at a time: a slot of `d` in the boost plane takes weight `2` or `-2`, leaving
`m - 2` or `m + 2`, a transverse slot takes either weight `0` direction, which is why those two
are added, and leaves `m` (`transitionZ_eq_sum` as one sum).
-/

/-- The four light-cone directions of axis `i`, as integers. -/
def lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 0 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then -1 else 0)
  else if κ = 1 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then 1 else 0)
  else if κ = 2 then (if μ = Sum.inr (i + 1) then 1 else 0)
  else (if μ = Sum.inr (i + 2) then 1 else 0)

/-- The integer copy casts to `lightConeCoeff`. -/
lemma coe_lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) :
    ((lightConeCoeffZ i κ μ : ℤ) : ℂ) = lightConeCoeff i κ μ := by
  rw [lightConeCoeffZ, lightConeCoeff]
  split_ifs <;> norm_num

/-- Twice the coordinate directions in the light-cone basis, the `2` clearing the halves. -/
def lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℤ :=
  if μ = Sum.inl 0 then (if κ = 0 then 1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr i then (if κ = 0 then -1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 2 else 0)
  else (if κ = 3 then 2 else 0)

/-- The integer copy is exactly twice `lightConeCoeffInv`. -/
lemma coe_lightConeCoeffInvZ_eq_two_mul (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℂ) = 2 * lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- The boost plane of axis `i`: time and the axis, the two directions the boost moves. -/
def InBoostPlane (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Prop := μ = Sum.inl 0 ∨ μ = Sum.inr i

instance (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Decidable (InBoostPlane i μ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A direction in the boost plane has no transverse light-cone components. -/
lemma lightConeCoeffInvZ_eq_zero_of_inBoostPlane {i : Fin 3} {μ : Fin 1 ⊕ Fin 3}
    (hμ : InBoostPlane i μ) {κ : Fin 4} (hκ : κ = 2 ∨ κ = 3) :
    lightConeCoeffInvZ i μ κ = 0 := by
  rcases hμ with rfl | rfl <;> rcases hκ with rfl | rfl <;> simp [lightConeCoeffInvZ]

/-- A transverse direction has no light-cone components in the boost plane. -/
lemma lightConeCoeffInvZ_eq_zero_of_not_inBoostPlane {i : Fin 3} {μ : Fin 1 ⊕ Fin 3}
    (hμ : ¬InBoostPlane i μ) {κ : Fin 4} (hκ : κ = 0 ∨ κ = 1) :
    lightConeCoeffInvZ i μ κ = 0 := by
  simp only [InBoostPlane, not_or] at hμ
  rcases hκ with rfl | rfl <;> simp [lightConeCoeffInvZ, hμ.1, hμ.2]

/-- One slot's factor: twice the coefficient of `κ` in `μ`, times that of `ν` in `κ`. -/
def slotZ (i : Fin 3) (κ : Fin 4) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  lightConeCoeffInvZ i μ κ * lightConeCoeffZ i κ ν

/-- Sixteen times the entry, at `d` and `e`, of the map keeping the light-cone components of total
  weight `m` along axis `i`. A slot of `d` in the boost plane takes weight `2` or `-2`, leaving
  `m - 2` or `m + 2`; a transverse slot takes weight `0` and leaves `m`. -/
def transitionZ (i : Fin 3) : {n : ℕ} → (d e : Fin n → Fin 1 ⊕ Fin 3) → ℤ → ℤ
  | 0, _, _, m => if m = 0 then 1 else 0
  | _ + 1, d, e, m =>
    if InBoostPlane i (d 0) then
      slotZ i 0 (d 0) (e 0) * transitionZ i (Fin.tail d) (Fin.tail e) (m - 2)
        + slotZ i 1 (d 0) (e 0) * transitionZ i (Fin.tail d) (Fin.tail e) (m + 2)
    else (slotZ i 2 (d 0) (e 0) + slotZ i 3 (d 0) (e 0))
      * transitionZ i (Fin.tail d) (Fin.tail e) m

/-- The recursion unfolded, as a sum over the multi-indices of total weight `m`. -/
lemma transitionZ_eq_sum (i : Fin 3) :
    ∀ {n : ℕ} (d e : Fin n → Fin 1 ⊕ Fin 3) (m : ℤ),
    transitionZ i d e m
      = ∑ κ ∈ Finset.univ.filter
          (fun κ : Fin n → Fin 4 => (∑ s, lightConeWeight (κ s)) = m),
        ∏ s, slotZ i (κ s) (d s) (e s)
  | 0, d, e, m => by
    rw [Finset.sum_filter, Fintype.sum_unique]
    simp [transitionZ, eq_comm]
  | n + 1, d, e, m => by
    have hpeel : ∀ κ : Fin 4,
        (∑ κ' : Fin n → Fin 4, if lightConeWeight κ + ∑ s, lightConeWeight (κ' s) = m then
          slotZ i κ (d 0) (e 0) * ∏ s, slotZ i (κ' s) (d s.succ) (e s.succ) else 0)
        = slotZ i κ (d 0) (e 0)
          * transitionZ i (Fin.tail d) (Fin.tail e) (m - lightConeWeight κ) := by
      intro κ
      rw [transitionZ_eq_sum i (Fin.tail d) (Fin.tail e), Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun κ' _ => by
        rw [mul_ite, mul_zero]
        exact if_congr (by omega) rfl rfl
    calc transitionZ i d e m
        = ∑ κ : Fin 4, slotZ i κ (d 0) (e 0)
            * transitionZ i (Fin.tail d) (Fin.tail e) (m - lightConeWeight κ) := by
          rw [Fin.sum_univ_four, transitionZ]
          simp only [show lightConeWeight 0 = 2 from rfl, show lightConeWeight 1 = -2 from rfl,
            show lightConeWeight 2 = 0 from rfl, show lightConeWeight 3 = 0 from rfl,
            sub_neg_eq_add, sub_zero]
          by_cases h : InBoostPlane i (d 0)
          · rw [if_pos h]
            simp [slotZ, lightConeCoeffInvZ_eq_zero_of_inBoostPlane h]
          · rw [if_neg h]
            simp [slotZ, lightConeCoeffInvZ_eq_zero_of_not_inBoostPlane h]
            ring
      _ = _ := by
          rw [Finset.sum_filter,
            ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => Fin 4), Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun κ _ => ?_
          rw [← hpeel κ]
          refine Finset.sum_congr rfl fun κ' _ => ?_
          simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ]

/-- A coefficient tensor is recovered from its light-cone components. -/
lemma eq_sum_lightConeComponent (i : Fin 3) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    c d = ∑ κ, (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_prod_lightConeCoeffInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- An invariant coefficient tensor is its own weight-zero projection. -/
lemma IsInvariantCoeff.sixteen_mul_eq_sum_transitionZ {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
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
lemma IsInvariantCoeff.eq_ofOrbitCoord {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    c = ofOrbitCoord fun k => c (orbitRep k) := by
  funext d
  by_cases hd : IsFlipFixed d
  · obtain ⟨k, hk⟩ := (isFlipFixed_iff_exists_mem_orbit d).1 hd
    rw [ofOrbitCoord, Finset.sum_eq_single k, if_pos hk,
      eq_orbitRep_of_mem_orbit hc.apply_cycIdx hk]
    · exact fun l _ hl => if_neg fun hdl => hl (eq_of_mem_orbit hdl hk)
    · exact fun h => absurd (Finset.mem_univ k) h
  · rw [hc.eq_zero_of_not_isFlipFixed hd]
    exact (Finset.sum_eq_zero fun k _ =>
      if_neg fun hk => hd ((isFlipFixed_iff_exists_mem_orbit d).2 ⟨k, hk⟩)).symm

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
lemma IsInvariantCoeff.orbitMatrix_mulVec {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) :
    orbitMatrix.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => c (orbitRep k))
      = (48 : ℂ) • fun k => c (orbitRep k) := by
  have h : ∀ d, 16 * c d
      = ∑ l, (∑ e ∈ orbit l, ((transitionZ 2 d e 0 : ℤ) : ℂ)) * c (orbitRep l) := by
    intro d
    rw [hc.sixteen_mul_eq_sum_transitionZ 2 d]
    conv_lhs => rw [hc.eq_ofOrbitCoord]
    exact sum_mul_ofOrbitCoord _ _
  funext k
  have h₀ := h (orbitRep k)
  have h₁ := h (cycIdx (orbitRep k))
  have h₂ := h (cycIdx (cycIdx (orbitRep k)))
  rw [hc.apply_cycIdx] at h₁
  rw [hc.apply_cycIdx, hc.apply_cycIdx] at h₂
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
As `9437184 = 393216 * 24` this leaves `projector b = 24 b`, writing `b`, and with it `c`, as a
combination of the four; the `24` is `contractionWeight_mul_contractionOrbit`. The identity is
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

/-- `24` times the orbit coordinates of an invariant tensor is `projector` applied to them. -/
lemma IsInvariantCoeff.orbitCoord_eq {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (k : Fin 22) :
    24 * c (orbitRep k)
      = ∑ i, (contractionOrbit i k : ℂ) * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l) := by
  set b : Fin 22 → ℂ := fun k => c (orbitRep k) with hb
  set M : Matrix (Fin 22) (Fin 22) ℂ := orbitMatrix.map (Int.cast : ℤ → ℂ) with hM
  have hMb : M *ᵥ b = (48 : ℂ) • b := hc.orbitMatrix_mulVec
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
  have hk := congrFun hpb k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, projector,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul, hb] at hk
  rw [Finset.sum_comm] at hk
  have hk' : (393216 : ℂ) * (24 * c (orbitRep k))
      = (393216 : ℂ) * ∑ i, (contractionOrbit i k : ℂ)
        * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l) := by
    rw [← mul_assoc, show (393216 : ℂ) * 24 = 9437184 by norm_num, hk]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  exact mul_left_cancel₀ (by norm_num) hk'

/-- An invariant coefficient tensor is a combination of the four. -/
theorem IsInvariantCoeff.exists_eq_sum {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    ∃ a : Fin 4 → ℂ, c = fun d => ∑ i, a i * ((contractionCoeff i d : ℤ) : ℂ) := by
  refine ⟨fun i => 24⁻¹ * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l), funext fun d => ?_⟩
  have hfour : ∀ i d, ((contractionCoeff i d : ℤ) : ℂ)
      = ∑ k, if d ∈ orbit k then (contractionOrbit i k : ℂ) else 0 :=
    fun i d => congrFun (isInvariantCoeff_contractionCoeff i).eq_ofOrbitCoord d
  have hb : ∀ k, c (orbitRep k) = 24⁻¹ * ∑ i, (contractionOrbit i k : ℂ)
      * ∑ l, (contractionWeight i l : ℂ) * c (orbitRep l) :=
    fun k => by rw [← hc.orbitCoord_eq]; ring
  conv_lhs => rw [hc.eq_ofOrbitCoord, ofOrbitCoord]
  rw [Finset.sum_congr rfl fun k _ => by rw [hb k]]
  simp only [hfour, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : d ∈ orbit k
  · simp only [hk, if_true, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  · simp [hk]

/-!

## H. The classification, and the classification modulo a stable submodule

C to G give `exists_smul_contraction_of_invariant`, the case `S = ⊥` of the theorem. For
general `S`, right to left is immediate and does not use `hS`; left to right passes to the
quotient `B ⧸ S`, that is `B` with `S` declared zero and `S.mkQ` the map to classes. Stability
lets `repLorentz` act there (`quotRep`) and the classes of the components again form a
quadruple Lorentz tensor (`isQuadLorentz_quotRep`), so back in `B` the difference between `x`
and the matching combination of contractions has zero class, hence lies in `S`, and is
invariant as a difference of invariants.
-/

include hT in
/-- Every Lorentz invariant of the span is a combination of the four contractions. -/
theorem exists_smul_contraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ,
      x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_span hx hinv
  obtain ⟨a, rfl⟩ := hc.exists_eq_sum
  refine ⟨a 0, a 1, a 2, a 3, ?_⟩
  rw [← sum_smul_contraction]
  simp only [contraction_eq, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- The representation induced on `B ⧸ S`, well defined because `S` is stable. -/
noncomputable def quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    Representation ℂ SL(2,ℂ) (B ⧸ S) where
  toFun g := S.mapQ S (repLorentz g) fun y hy => hS g y hy
  map_one' := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

/-- `S.mkQ y` is the class of `y`, and the induced representation moves a class by any lift. -/
lemma quotRep_mkQ (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (g : SL(2,ℂ)) (y : B) :
    quotRep (repLorentz := repLorentz) S hS g (S.mkQ y) = S.mkQ (repLorentz g y) := rfl

/-- Taking classes turns a contraction of the components into one of their classes. -/
lemma mkQ_sum_smul (S : Submodule ℂ B) (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) :
    S.mkQ (∑ d, c d • T d) = ∑ d, c d • S.mkQ (T d) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

include hT in
/-- The classes of the components again form a quadruple Lorentz tensor. -/
lemma isQuadLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsQuadLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, mkQ_sum_smul]

include hT in
/-- Left to right in `mem_span_sup_invariant_iff`, proved in the quotient by `S`. -/
lemma exists_smul_contraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
      x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
        + a₄ • epsilonContraction T + y
      ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  have hT' := hT.isQuadLorentz_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, mkQ_sum_smul]
    exact hT'.sum_smul_mem_span c
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x :=
    fun g => by rw [quotRep_mkQ, hinv g]
  obtain ⟨a₁, a₂, a₃, a₄, hcomb⟩ := hT'.exists_smul_contraction_of_invariant hmk hinv'
  simp only [outerContraction, innerContraction, splitContraction, epsilonContraction,
    ← mkQ_sum_smul] at hcomb
  refine ⟨a₁, a₂, a₃, a₄,
    x - (a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
      + a₄ • epsilonContraction T), ?_, by abel, fun g => ?_⟩
  · rw [← Submodule.ker_mkQ S, LinearMap.mem_ker, map_sub, hcomb, outerContraction,
      innerContraction, splitContraction, epsilonContraction]
    simp only [map_add, map_smul]
    abel
  · rw [map_sub, hinv g, hT.repLorentz_smul_contraction a₁ a₂ a₃ a₄ g]

include hT in
/-- A vector of `hT.span ⊔ S`, the sums `u + y` with `u` in the span and `y` in the Lorentz-stable
  subspace `S`, is invariant exactly when it is a combination of the four contractions plus an
  invariant `y` of `S`. `hS` is used only left to right. -/
theorem mem_span_sup_invariant_iff (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ a₁ a₂ a₃ a₄ : ℂ, ∃ y ∈ S,
        x = a₁ • outerContraction T + a₂ • innerContraction T + a₃ • splitContraction T
          + a₄ • epsilonContraction T + y
        ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  refine ⟨fun h => hT.exists_smul_contraction_of_invariant_subset S hS h.1 h.2, ?_⟩
  rintro ⟨a₁, a₂, a₃, a₄, y, hyS, rfl, hyinv⟩
  refine ⟨add_mem (Submodule.mem_sup_left (hT.smul_contraction_mem_span a₁ a₂ a₃ a₄))
    (Submodule.mem_sup_right hyS), fun g => ?_⟩
  rw [map_add, hT.repLorentz_smul_contraction a₁ a₂ a₃ a₄ g, hyinv g]

/-!

## Aside: what other files import from here

None of this is used above. A vector has weight `m` along the axis `i` when the boost with
parameter `t` scales it by `t ^ m`, `boostWeightSubmodule` is the space of such vectors, an
invariant has weight `0` along every axis, and weights are independent. The rest repeats E over
`ℚ`, sorting the light-cone directions into sectors: raising `2`, lowering `-2`, transverse `0`.
-/

/-- A Lorentz invariant has boost weight zero along every axis, being fixed by every boost. -/
lemma mem_boostWeightSubmodule_zero_of_invariant {x : B}
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) (i : Fin 3) :
    x ∈ boostWeightSubmodule repLorentz i 0 := by
  rw [mem_boostWeightSubmodule]
  intro t ht
  rw [hinv, zpow_zero, one_smul]

/-- Vectors of distinct boost weights adding to zero are each zero. -/
lemma eq_zero_of_sum_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A}
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (hsum : ∑ m ∈ s, w m = 0) :
    ∀ m ∈ s, w m = 0 := by
  intro m₀ hm₀
  refine Submodule.disjoint_def.1
    (iSupIndep_def.1 (boostWeightSubmodule_iSupIndep rep) m₀) (w m₀) (hw m₀ hm₀) ?_
  have h : w m₀ = -∑ m ∈ s.erase m₀, w m :=
    eq_neg_of_add_eq_zero_left (by rw [Finset.add_sum_erase s w hm₀]; exact hsum)
  rw [h]
  exact neg_mem (sum_mem fun m hm => Submodule.mem_iSup_of_mem m
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hm)
      (hw m (Finset.mem_of_mem_erase hm))))

/-- A weight-zero vector written as a sum of definite weights equals the weight-zero term. -/
lemma eq_component_zero_of_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A} {x : A}
    (hx : x ∈ boostWeightSubmodule rep i 0)
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (h0 : (0 : ℤ) ∈ s) (hsum : x = ∑ m ∈ s, w m) :
    x = w 0 := by
  have hv : ∀ m ∈ s, Function.update w 0 (w 0 - x) m ∈ boostWeightSubmodule rep i m := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [Function.update_self]
      exact sub_mem (hw 0 h0) hx
    · rw [Function.update_of_ne h]
      exact hw m hm
  have hsum0 : ∑ m ∈ s, Function.update w 0 (w 0 - x) m = 0 := by
    rw [Finset.sum_update_of_mem h0, hsum, ← Finset.add_sum_erase s w h0, Finset.erase_eq]
    abel
  have h := eq_zero_of_sum_mem_boostWeightSubmodule hv hsum0 0 h0
  rw [Function.update_self] at h
  exact (sub_eq_zero.1 h).symm

/-- If each `S m` lies in the weight-`m` space, a weight-zero vector of their join lies in `S 0`. -/
lemma mem_of_mem_iSup_of_boostWeight_zero {i : Fin 3} {S : ℤ → Submodule ℂ B}
    (hS : ∀ m : ℤ, S m ≤ boostWeightSubmodule repLorentz i m) {x : B}
    (hx : x ∈ ⨆ m, S m) (h0 : x ∈ boostWeightSubmodule repLorentz i 0) : x ∈ S 0 := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  have hkey := eq_component_zero_of_mem_boostWeightSubmodule (i := i)
    (s := insert 0 f.support) (w := fun m => f m) h0
    (fun m _ => hS m (hf m)) (Finset.mem_insert_self 0 _) ?_
  · rw [hkey]
    exact hf 0
  · rw [Finsupp.sum]
    by_cases h : (0 : ℤ) ∈ f.support
    · rw [Finset.insert_eq_self.2 h]
    · rw [Finset.sum_insert h, Finsupp.notMem_support_iff.1 h, zero_add]

/-- The inverse light-cone coefficients of section E over `ℚ`, with the halves kept as halves. -/
def lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℚ :=
  if μ = Sum.inl 0 then (if κ = 0 then 2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr i then (if κ = 0 then -2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 1 else 0)
  else (if κ = 3 then 1 else 0)

/-- The rational mirror casts to the inverse light-cone coefficients. -/
lemma coe_lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvQ i μ κ : ℚ) : ℂ) = lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvQ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- The integer mirror is twice the rational one. -/
lemma coe_lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℚ) = 2 * lightConeCoeffInvQ i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInvQ]
  split_ifs <;> norm_num

/-- The sector of each light-cone direction: `0` raising, `1` lowering, `2` and `3` transverse. -/
def sectorIndex : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The boost weight of each sector: `2` raising, `-2` lowering, `0` transverse. -/
def sectorWeight : Fin 3 → ℤ := ![2, -2, 0]

/-- The light-cone weight of a direction is the weight of its sector. -/
lemma lightConeWeight_eq_sectorWeight (κ : Fin 4) :
    lightConeWeight κ = sectorWeight (sectorIndex κ) := by
  fin_cases κ <;> rfl

/-- The slot factor summed over the directions of one sector, over `ℚ`. -/
def slotTransition (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
    lightConeCoeffInvQ i μ κ' * (lightConeCoeffZ i κ' ν : ℚ)

/-- The slot factor summed over one sector, in closed form over `ℤ`: on the boost plane the
  raising sector carries `[[1, -1], [-1, 1]]` and the lowering sector the all-ones matrix, and
  the transverse sector is twice the identity on the transverse directions. -/
def slotTransitionZ (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 2 then (if μ = ν ∧ μ ≠ Sum.inl 0 ∧ μ ≠ Sum.inr i then 2 else 0)
  else if (μ = Sum.inl 0 ∨ μ = Sum.inr i) ∧ (ν = Sum.inl 0 ∨ ν = Sum.inr i) then
    (if κ = 0 then (if μ = Sum.inr i then -1 else 1) * (if ν = Sum.inr i then -1 else 1)
    else 1)
  else 0

/-- The closed form is the sector sum of the slot factors. -/
lemma slotTransitionZ_eq_sum (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    slotTransitionZ i κ μ ν
      = ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
        lightConeCoeffInvZ i μ κ' * lightConeCoeffZ i κ' ν := by
  rw [Finset.sum_filter, Fin.sum_univ_four]
  rcases μ with a | j <;> rcases ν with b | l
  · simp only [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
    fin_cases κ <;> simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · simp only [Fin.fin_one_eq_zero a]
    fin_cases κ <;> fin_cases i <;> fin_cases l <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · simp only [Fin.fin_one_eq_zero b]
    fin_cases κ <;> fin_cases i <;> fin_cases j <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · fin_cases κ <;> fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]

/-- The integer sector matrix is twice the rational one, which is what the two names promise. -/
lemma coe_slotTransitionZ (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    ((slotTransitionZ i κ μ ν : ℤ) : ℚ) = 2 * slotTransition i κ μ ν := by
  rw [slotTransitionZ_eq_sum, slotTransition, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun κ' _ => by rw [coe_lightConeCoeffInvZ]; ring

end IsQuadLorentz

end Lorentz
