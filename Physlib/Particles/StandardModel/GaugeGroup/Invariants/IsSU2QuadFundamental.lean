/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Gauge tensors carrying four `su(2)` fundamental indices

The quartic Higgs coupling `(H†H)²` is a product of four isospin doublets, so it carries four
fundamental `su(2)` indices. A doublet index can only be contracted against another through
the antisymmetric symbol, so an invariant of four indices is a way of pairing them off, and
there are three pairings: `(12)(34)`, `(13)(24)` and `(14)(23)`. They are not independent.
Antisymmetrizing three indices of a two-dimensional space gives zero, and written out that is
the Schouten identity, one linear relation between the three. So `2 ⊗ 2 ⊗ 2 ⊗ 2` contains
exactly two singlets, and this file proves it in the form the Standard Model files consume:
modulo an isospin-stable submodule, every isospin invariant in the span of the components is
a combination of the first two epsilon contractions.

`IsSU2QuadFundamental B repGauge T` records the hypothesis. `T` is a family indexed by four
fundamental indices and valued in a module `B` carrying a representation of the gauge group,
and an isospin rotation `U ∈ SU(2)` moves its components by one factor of `U` per index.
Nothing is asked of the colour and hypercharge factors.

The proof follows `IsSU2BiFundamental`. The action on coefficient functions `c l`, with
`l : Fin 4 → Fin 2`, is the fourth Kronecker power of `U`, unitary, so an isospin invariant of
the span is the contraction of an invariant coefficient, by `Family.exists_invariant_coeff`,
and three rotations pin such a coefficient down. The diagonal matrix `diag(ζ, ζ²)`, with `ζ` a
primitive cube root of unity, lies in `SU(2)` and scales `c l` by `ζ ^ (4 + k)` where `k` is
the number of indices equal to `1`, so only the six balanced entries, with two indices of
each kind, survive. The Weyl element `su2Perm` exchanges `0` and `1` in all four slots and
equates each balanced entry with its complement, leaving three unknowns. The third of a turn
`su2Cyc` has a first row with two equal entries, so it carries `c ![0, 0, 0, 0]` to a multiple
of the sum of all sixteen entries: that sum vanishes, and with it the sum of the three
unknowns. Two remain, and they are the coefficients of the two pairings.

Section A gives the transformation law and the span, section B the two pairings and their
contractions, section C the action on coefficients, section D the classification of invariant
coefficients, section E the invariants of the span, and section F the form modulo a stable
submodule. An aside at the end holds the gauge form of the theorem, which the Higgs sector
uses.
-/

@[expose] public section

namespace StandardModel

open Matrix
open IsSU2BiFundamental (epsilon sum_epsilon_mul inv_apply)
open IsSU2BiAdjoint (su2Cyc su2Cyc_coe)

/-!

## A. The transformation law and the span of the components

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with four
  fundamental indices: one factor of `U` per index, with the summed index in the row
  slot. -/
def IsSU2QuadFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 4 → Fin 2) → B) : Prop :=
  ∀ l : Fin 4 → Fin 2,
    f (T l) = ∑ a : Fin 4 → Fin 2, (∏ i : Fin 4, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by four `su(2)` fundamental indices, transforms
  as a tensor `T^{a b c d}` under the isospin factor of the gauge group. Nothing is asked of
  the colour and hypercharge factors. -/
structure IsSU2QuadFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 4 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2QuadFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2QuadFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 4 → Fin 2) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff {T : (Fin 4 → Fin 2) → B} (x : B) :
    x ∈ span T ↔ ∃ (c : (Fin 4 → Fin 2) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 4 → Fin 2) → B} (d : Fin 4 → Fin 2) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over families of four fundamental indices is a fourfold sum. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 2) → M) :
    ∑ d : Fin 4 → Fin 2, F d
      = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ w : Fin 2, F ![x, y, z, w] := by
  rw [show (∑ d : Fin 4 → Fin 2, F d)
      = ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
        Fintype.sum_equiv
          { toFun := fun d => (d 0, d 1, d 2, d 3)
            invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
            left_inv := fun d => by funext i; fin_cases i <;> simp
            right_inv := fun p => by simp } _ _ fun d => by
          congr 1
          funext i
          fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-!

## B. The two epsilon pairings

The pairing `(12)(34)` has coefficient function `ε (l 0) (l 1) * ε (l 2) (l 3)`, and the
pairing `(13)(24)` has `ε (l 0) (l 2) * ε (l 1) (l 3)`. The third pairing is the difference
of these two by the Schouten identity, so two contractions suffice: `epsilonContraction₁₂`
and `epsilonContraction₁₃`, the contractions of `T` against the two coefficient functions.

-/

/-- The coefficient function of the pairing `(12)(34)`. -/
def epsilonPair₁₂ (l : Fin 4 → Fin 2) : ℂ := epsilon (l 0) (l 1) * epsilon (l 2) (l 3)

/-- The coefficient function of the pairing `(13)(24)`. -/
def epsilonPair₁₃ (l : Fin 4 → Fin 2) : ℂ := epsilon (l 0) (l 2) * epsilon (l 1) (l 3)

/-- The contraction pairing the first index with the second and the third with the
  fourth. -/
def epsilonContraction₁₂ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 1, 0, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 0, 1, 0]

/-- The contraction pairing the first index with the third and the second with the
  fourth. -/
def epsilonContraction₁₃ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 0, 1, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 1, 0, 0]

/-- The first contraction is the contraction against the first pairing. -/
lemma sum_epsilonPair₁₂_smul (T : (Fin 4 → Fin 2) → B) :
    ∑ l, epsilonPair₁₂ l • T l = epsilonContraction₁₂ T := by
  rw [sum_pi_four]
  simp [epsilonPair₁₂, epsilonContraction₁₂, Fin.sum_univ_two]
  abel

/-- The second contraction is the contraction against the second pairing. -/
lemma sum_epsilonPair₁₃_smul (T : (Fin 4 → Fin 2) → B) :
    ∑ l, epsilonPair₁₃ l • T l = epsilonContraction₁₃ T := by
  rw [sum_pi_four]
  simp [epsilonPair₁₃, epsilonContraction₁₃, Fin.sum_univ_two]
  abel

/-!

## C. The action on coefficients

A vector of the span is a contraction `∑ l, c l • T l` against a coefficient function `c`,
and the law says that an isospin rotation moves it by moving `c` with the fourth Kronecker
power `act U` of `U`. Unitarity of `U` makes `act U⁻¹` the adjoint of `act U`, and the two
pairings are invariant coefficients, each being a product of two invariant antisymmetric
symbols.

-/

/-- The action of `U ∈ SU(2)` on coefficient functions: the fourth Kronecker power of
  `U`. -/
noncomputable def act (U : specialUnitaryGroup (Fin 2) ℂ) :
    ((Fin 4 → Fin 2) → ℂ) →ₗ[ℂ] (Fin 4 → Fin 2) → ℂ :=
  Matrix.toLin' (Matrix.of fun a l => ∏ i : Fin 4, U.1 (a i) (l i))

/-- The action on coefficients, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 4 → Fin 2) → ℂ)
    (a : Fin 4 → Fin 2) :
    act U c a = ∑ l, (∏ i : Fin 4, U.1 (a i) (l i)) * c l := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form. -/
lemma map_sum_smul {T : (Fin 4 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T) (c : (Fin 4 → Fin 2) → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The action of `U⁻¹` is the adjoint of the action of `U`. -/
lemma sum_star_mul_act (U : specialUnitaryGroup (Fin 2) ℂ) (c d : (Fin 4 → Fin 2) → ℂ) :
    ∑ a, star (c a) * act U d a = ∑ l, star (act U⁻¹ c l) * d l := by
  simp only [act_apply, inv_apply, Fin.prod_univ_four, Finset.mul_sum, Finset.sum_mul,
    star_sum, star_mul', Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The first pairing is invariant: the sum over the four indices factors into two
  invariant antisymmetric symbols. -/
lemma act_epsilonPair₁₂ (U : specialUnitaryGroup (Fin 2) ℂ) :
    act U epsilonPair₁₂ = epsilonPair₁₂ := by
  funext a
  have key : act U epsilonPair₁₂ a
      = (∑ x : Fin 2, ∑ y : Fin 2, epsilon x y * (U.1 (a 0) x * U.1 (a 1) y))
        * (∑ z : Fin 2, ∑ w : Fin 2, epsilon z w * (U.1 (a 2) z * U.1 (a 3) w)) := by
    rw [act_apply, sum_pi_four]
    simp only [epsilonPair₁₂, Fin.prod_univ_four, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  rw [key, sum_epsilon_mul, sum_epsilon_mul, epsilonPair₁₂]

/-- The second pairing is invariant, by the same factorization with the indices
  interleaved. -/
lemma act_epsilonPair₁₃ (U : specialUnitaryGroup (Fin 2) ℂ) :
    act U epsilonPair₁₃ = epsilonPair₁₃ := by
  funext a
  have key : act U epsilonPair₁₃ a
      = (∑ x : Fin 2, ∑ z : Fin 2, epsilon x z * (U.1 (a 0) x * U.1 (a 2) z))
        * (∑ y : Fin 2, ∑ w : Fin 2, epsilon y w * (U.1 (a 1) y * U.1 (a 3) w)) := by
    rw [act_apply, sum_pi_four]
    simp only [epsilonPair₁₃, Fin.prod_univ_four, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  rw [key, sum_epsilon_mul, sum_epsilon_mul, epsilonPair₁₃]

/-- Any map moving the components by an element of `SU(2)` fixes the first
  contraction. -/
lemma map_epsilonContraction₁₂ {T : (Fin 4 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T) :
    f (epsilonContraction₁₂ T) = epsilonContraction₁₂ T := by
  rw [← sum_epsilonPair₁₂_smul, map_sum_smul hf, act_epsilonPair₁₂]

/-- Any map moving the components by an element of `SU(2)` fixes the second
  contraction. -/
lemma map_epsilonContraction₁₃ {T : (Fin 4 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T) :
    f (epsilonContraction₁₃ T) = epsilonContraction₁₃ T := by
  rw [← sum_epsilonPair₁₃_smul, map_sum_smul hf, act_epsilonPair₁₃]

/-- The first contraction is isospin invariant. -/
lemma repGauge_epsilonContraction₁₂ {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction₁₂ T) = epsilonContraction₁₂ T :=
  map_epsilonContraction₁₂ (hT.repGauge_T V)

/-- The second contraction is isospin invariant. -/
lemma repGauge_epsilonContraction₁₃ {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction₁₃ T) = epsilonContraction₁₃ T :=
  map_epsilonContraction₁₃ (hT.repGauge_T V)

/-!

## D. An invariant coefficient is a combination of the two pairings

## D.1. A diagonal element of order three keeps only the balanced entries

The matrix `diag(ζ, ζ²)`, with `ζ` a primitive cube root of unity, is unitary of determinant
`ζ³ = 1`. It scales the entry `c l` by `ζ` for each index equal to `0` and by `ζ²` for each
index equal to `1`, so by `ζ ^ (4 + k)` with `k` the number of indices equal to `1`, and that
is `1` only when `3 ∣ 4 + k`, which for `k ≤ 4` means `k = 2`.

-/

/-- A primitive cube root of unity. -/
noncomputable def cubeRoot : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- The cube root of unity is primitive. -/
lemma cubeRoot_isPrimitiveRoot : IsPrimitiveRoot cubeRoot 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [cubeRoot] using h

/-- The cube root of unity has unit modulus. -/
lemma cubeRoot_mul_star : cubeRoot * star cubeRoot = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    cubeRoot_isPrimitiveRoot.norm'_eq_one (by norm_num)]
  simp

/-- The diagonal matrix `diag(ζ, ζ²)` as an element of `SU(2)`. -/
noncomputable def su2Cube : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal ![cubeRoot, cubeRoot ^ 2], by
    have hd : ∀ i : Fin 2, ![cubeRoot, cubeRoot ^ 2] i * star (![cubeRoot, cubeRoot ^ 2] i)
        = 1 := by
      intro i
      fin_cases i
      · simpa using cubeRoot_mul_star
      · show cubeRoot ^ 2 * star (cubeRoot ^ 2) = 1
        rw [star_pow, ← mul_pow, cubeRoot_mul_star, one_pow]
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      simp only [Pi.star_apply, hd, Matrix.diagonal_one]
    · rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination cubeRoot_isPrimitiveRoot.pow_eq_one⟩

/-- The entries of the diagonal element. -/
lemma su2Cube_apply (a b : Fin 2) :
    su2Cube.1 a b = if a = b then cubeRoot ^ (1 + (a : ℕ)) else 0 := by
  show Matrix.diagonal ![cubeRoot, cubeRoot ^ 2] a b = _
  rw [Matrix.diagonal_apply]
  fin_cases a <;> fin_cases b <;> simp

/-- The diagonal element scales an entry by `ζ ^ (4 + k)`, where `k` is the number of its
  indices equal to `1`. -/
lemma act_su2Cube (c : (Fin 4 → Fin 2) → ℂ) (l : Fin 4 → Fin 2) :
    act su2Cube c l = cubeRoot ^ (4 + ∑ i, (l i : ℕ)) * c l := by
  rw [act_apply, Finset.sum_eq_single l]
  · congr 1
    rw [show (∏ i, su2Cube.1 (l i) (l i)) = ∏ i : Fin 4, cubeRoot ^ (1 + (l i : ℕ)) from
      Finset.prod_congr rfl fun i _ => by rw [su2Cube_apply, if_pos rfl],
      Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
    simp
  · intro m _ hm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [su2Cube_apply, if_neg (Ne.symm hi)]),
      zero_mul]
  · simp

/-- An entry of an invariant coefficient vanishes unless exactly two of its indices are
  `1`. -/
lemma eq_zero_of_act_su2Cube_eq {c : (Fin 4 → Fin 2) → ℂ} (hc : act su2Cube c = c)
    {l : Fin 4 → Fin 2} (hl : (∑ i, (l i : ℕ)) ≠ 2) : c l = 0 := by
  have h := congrFun hc l
  rw [act_su2Cube] at h
  have hdvd : ∀ l : Fin 4 → Fin 2, (∑ i, (l i : ℕ)) ≠ 2 → ¬ 3 ∣ 4 + ∑ i, (l i : ℕ) := by
    decide
  refine (mul_left_eq_self₀.1 h).resolve_left fun h1 => hdvd l hl ?_
  exact (cubeRoot_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 h1

/-!

## D.2. The Weyl element and the third of a turn

The Weyl element `su2Perm = !![0, -1; 1, 0]` exchanges the two values of every index, and
on a balanced entry the four signs multiply to `1`. The third of a turn `su2Cyc` has both
entries of its first row equal to `(1 + i)/2`, so the entry `c ![0, 0, 0, 0]` of `act su2Cyc c`
is `((1 + i)/2)⁴` times the sum of all sixteen entries of `c`.

-/

/-- The Weyl element carries `c ![0, 0, 1, 1]` to `c ![1, 1, 0, 0]`. -/
lemma act_su2Perm_zero_zero_one_one (c : (Fin 4 → Fin 2) → ℂ) :
    act su2Perm c ![0, 0, 1, 1] = c ![1, 1, 0, 0] := by
  rw [act_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The Weyl element carries `c ![0, 1, 0, 1]` to `c ![1, 0, 1, 0]`. -/
lemma act_su2Perm_zero_one_zero_one (c : (Fin 4 → Fin 2) → ℂ) :
    act su2Perm c ![0, 1, 0, 1] = c ![1, 0, 1, 0] := by
  rw [act_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The Weyl element carries `c ![0, 1, 1, 0]` to `c ![1, 0, 0, 1]`. -/
lemma act_su2Perm_zero_one_one_zero (c : (Fin 4 → Fin 2) → ℂ) :
    act su2Perm c ![0, 1, 1, 0] = c ![1, 0, 0, 1] := by
  rw [act_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The third of a turn carries the entry with all indices `0` to a nonzero multiple of the
  sum of all the entries. -/
lemma act_su2Cyc_zero (c : (Fin 4 → Fin 2) → ℂ) :
    act su2Cyc c (fun _ => 0) = ((1 + Complex.I) / 2) ^ 4 * ∑ m, c m := by
  have hrow : ∀ j : Fin 2, su2Cyc.1 0 j = (1 + Complex.I) / 2 := by
    intro j
    fin_cases j <;> simp [su2Cyc_coe]
  rw [act_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!

## D.3. The classification

-/

/-- An invariant coefficient is a combination of the two pairings. -/
theorem exists_eq_smul_add_smul_of_act_eq {c : (Fin 4 → Fin 2) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, act U c = c) :
    ∃ c₁ c₂ : ℂ, c = c₁ • epsilonPair₁₂ + c₂ • epsilonPair₁₃ := by
  -- the diagonal element: only the balanced entries survive
  have hz : ∀ l : Fin 4 → Fin 2, (∑ i, (l i : ℕ)) ≠ 2 → c l = 0 :=
    fun l hl => eq_zero_of_act_su2Cube_eq (hc su2Cube) hl
  have hz0000 : c ![0, 0, 0, 0] = 0 := hz _ (by decide)
  have hz0001 : c ![0, 0, 0, 1] = 0 := hz _ (by decide)
  have hz0010 : c ![0, 0, 1, 0] = 0 := hz _ (by decide)
  have hz0100 : c ![0, 1, 0, 0] = 0 := hz _ (by decide)
  have hz1000 : c ![1, 0, 0, 0] = 0 := hz _ (by decide)
  have hz0111 : c ![0, 1, 1, 1] = 0 := hz _ (by decide)
  have hz1011 : c ![1, 0, 1, 1] = 0 := hz _ (by decide)
  have hz1101 : c ![1, 1, 0, 1] = 0 := hz _ (by decide)
  have hz1110 : c ![1, 1, 1, 0] = 0 := hz _ (by decide)
  have hz1111 : c ![1, 1, 1, 1] = 0 := hz _ (by decide)
  -- the Weyl element: each balanced entry equals its complement
  have hw1 : c ![1, 1, 0, 0] = c ![0, 0, 1, 1] := by
    have h := congrFun (hc su2Perm) ![0, 0, 1, 1]
    rwa [act_su2Perm_zero_zero_one_one] at h
  have hw2 : c ![1, 0, 1, 0] = c ![0, 1, 0, 1] := by
    have h := congrFun (hc su2Perm) ![0, 1, 0, 1]
    rwa [act_su2Perm_zero_one_zero_one] at h
  have hw3 : c ![1, 0, 0, 1] = c ![0, 1, 1, 0] := by
    have h := congrFun (hc su2Perm) ![0, 1, 1, 0]
    rwa [act_su2Perm_zero_one_one_zero] at h
  -- the third of a turn: the three remaining unknowns sum to zero
  have hcyc : c ![0, 0, 1, 1] + c ![0, 1, 0, 1] + c ![0, 1, 1, 0] = 0 := by
    have h := congrFun (hc su2Cyc) (fun _ => 0)
    rw [act_su2Cyc_zero, hz (fun _ => 0) (by decide)] at h
    have hu : ((1 + Complex.I) / 2) ^ 4 ≠ 0 := by
      refine pow_ne_zero _ fun h0 => ?_
      have := congrArg Complex.re h0
      norm_num at this
    have hsum := (mul_eq_zero.1 h).resolve_left hu
    rw [sum_pi_four] at hsum
    simp only [Fin.sum_univ_two, hz0000, hz0001, hz0010, hz0100, hz1000, hz0111, hz1011,
      hz1101, hz1110, hz1111, hw1, hw2, hw3] at hsum
    linear_combination hsum / 2
  refine ⟨c ![0, 1, 0, 1], c ![0, 0, 1, 1], funext fun l => ?_⟩
  obtain ⟨a, b, d, e, rfl⟩ : ∃ a b d e, l = ![a, b, d, e] :=
    ⟨l 0, l 1, l 2, l 3, by ext i; fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [epsilonPair₁₂, epsilonPair₁₃, hz0000, hz0001, hz0010, hz0100, hz1000, hz0111,
      hz1011, hz1101, hz1110, hz1111, hw1, hw2, hw3] <;>
    linear_combination hcyc

/-!

## E. The isospin invariants of the span

The action on coefficients is unitary, so `Family.exists_invariant_coeff` writes an isospin
invariant of the span as the contraction of an invariant coefficient, and section D makes
that coefficient a combination of the two pairings. The statement is made for any family of
linear maps `φ U` obeying the law, so that section F can apply it in a quotient.

-/

/-- Every invariant in the span of a family obeying the law for a family of linear maps
  `φ U` is a combination of the two epsilon contractions: the two singlets of
  `2 ⊗ 2 ⊗ 2 ⊗ 2`. -/
theorem exists_smul_add_smul_of_invariant' {T : (Fin 4 → Fin 2) → B}
    {φ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU2QuadFundamentalMat U (φ U) T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ U, φ U x = x) :
    ∃ c₁ c₂ : ℂ, x = c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c) sum_star_mul_act hx hinv
  obtain ⟨c₁, c₂, hc'⟩ := exists_eq_smul_add_smul_of_act_eq hc
  refine ⟨c₁, c₂, ?_⟩
  rw [hc', ← sum_epsilonPair₁₂_smul, ← sum_epsilonPair₁₃_smul, Finset.smul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul]

/-- Every isospin invariant in the span of the components is a combination of the two
  epsilon contractions. -/
theorem exists_smul_add_smul_of_su2_invariant {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c₁ c₂ : ℂ, x = c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T :=
  exists_smul_add_smul_of_invariant' hT.repGauge_T hx hinv

/-!

## F. The invariants modulo a stable submodule

The law descends to the quotient by an isospin-stable `S`, so section E applies there, and
`Family.exists_mem_add_of_mem_sup` lifts the result back, the invariants of the quotient
family being the classes of the plane spanned by the two contractions.

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU2QuadFundamentalMat_mapQ {T : (Fin 4 → Fin 2) → B}
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T)
    (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU2QuadFundamentalMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The first contraction of the quotient family is the class of the first contraction. -/
lemma mkQ_epsilonContraction₁₂ (T : (Fin 4 → Fin 2) → B) (S : Submodule ℂ B) :
    epsilonContraction₁₂ (fun l => S.mkQ (T l)) = S.mkQ (epsilonContraction₁₂ T) := by
  simp only [epsilonContraction₁₂, map_sub, map_add]

/-- The second contraction of the quotient family is the class of the second
  contraction. -/
lemma mkQ_epsilonContraction₁₃ (T : (Fin 4 → Fin 2) → B) (S : Submodule ℂ B) :
    epsilonContraction₁₃ (fun l => S.mkQ (T l)) = S.mkQ (epsilonContraction₁₃ T) := by
  simp only [epsilonContraction₁₃, map_sub, map_add]

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` is a combination of the two epsilon contractions up to an isospin-invariant
  remainder in `S`. -/
theorem mem_span_sup_su2_invariant_iff {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c₁ c₂ : ℂ, ∃ y ∈ S,
      x = c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T + y
        ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  obtain ⟨w, hw, y, hyS, hxy, hyinv⟩ := Family.exists_mem_add_of_mem_sup T
    (fun V => repGauge (1, V, 1)) S hS
    (Submodule.span ℂ {epsilonContraction₁₂ T, epsilonContraction₁₃ T})
    (fun w hw V => by
      obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.1 hw
      rw [map_add, map_smul, map_smul, repGauge_epsilonContraction₁₂ hT,
        repGauge_epsilonContraction₁₃ hT])
    (fun x hx hinv => by
      obtain ⟨c₁, c₂, hx'⟩ := exists_smul_add_smul_of_invariant'
        (fun V => isSU2QuadFundamentalMat_mapQ (hT.repGauge_T V) S (hS V)) hx hinv
      refine ⟨c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T,
        Submodule.mem_span_pair.2 ⟨c₁, c₂, rfl⟩, ?_⟩
      rw [map_add, map_smul, map_smul, ← mkQ_epsilonContraction₁₂, ← mkQ_epsilonContraction₁₃,
        hx']) hx hinv
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.1 hw
  exact ⟨c₁, c₂, y, hyS, hxy, hyinv⟩

/-!

## Aside: the gauge form of the theorem, for the Higgs sector

-/

/-- A gauge invariant of the span joined with a gauge-stable submodule is a combination of
  the two epsilon contractions up to a gauge-invariant remainder, once the two contractions
  are known to be gauge invariant. The hypotheses on the contractions cannot be dropped: the
  law says nothing about the hypercharge factor, which may scale them. -/
theorem mem_span_sup_invariant_iff {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hec₁₂ : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction₁₂ T) = epsilonContraction₁₂ T)
    (hec₁₃ : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction₁₃ T) = epsilonContraction₁₃ T)
    (hx : x ∈ span T ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c₁ c₂ : ℂ, ∃ y ∈ S,
      x = c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T + y
        ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c₁, c₂, y, hyS, hxy, -⟩ :=
    hT.mem_span_sup_su2_invariant_iff x S (fun V => hS (1, V, 1)) hx fun V => hinv (1, V, 1)
  refine ⟨c₁, c₂, y, hyS, hxy, fun g => ?_⟩
  rw [show y = x - (c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T) from by
    rw [hxy]; abel, map_sub, map_add, map_smul, map_smul, hinv g, hec₁₂ g, hec₁₃ g]

end IsSU2QuadFundamental

end StandardModel
