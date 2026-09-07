/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
/-!
# Gauge tensors carrying a fundamental and an anti-fundamental `su(3)` index

A quark carries a fundamental colour index and an antiquark an anti-fundamental one, so a
quark-antiquark bilinear, the colour structure of every Yukawa coupling and of every
fermion kinetic term, carries one of each. Here there is a colour singlet, exactly one:
`3 ⊗ 3̄ = 8 ⊕ 1`, and the singlet is the Kronecker delta `δ^a_b`, the colour trace
`∑ a, T ![a, a]` of the bilinear. This file proves that in the form the Standard Model files
consume, modulo a colour-stable submodule.

`IsSU3FunAntiFun B repGauge T` records the hypothesis: `T` is a family indexed by one
fundamental and one anti-fundamental colour index, valued in a module `B` carrying a
representation of the gauge group, and a colour rotation `U ∈ SU(3)` moves its components
by `U` on the first index and by the complex conjugate of `U` on the second, which is what an
anti-fundamental index means. Nothing is asked of the isospin and hypercharge factors, which
may well move the components: a quark-antiquark bilinear carries hypercharge.

The proof follows `IsSU3BiAdjoint`. The action on coefficient functions `c ![a, b]` is
`c ↦ U c U†`, unitary, so a colour invariant of the span is the contraction of an invariant
coefficient, by `Family.exists_invariant_coeff`. An invariant coefficient is a `3 × 3`
matrix commuting with every `U ∈ SU(3)`, and two rotations pin it down: the colour parity
fixing a colour `a` and reversing the other two changes the sign of every entry `c ![a, b]`
with `b ≠ a`, so the matrix is diagonal, and the cyclic permutation of the colours equates
the diagonal entries. So the matrix is a multiple of the identity and the vector a multiple
of the trace. The delta uses only unitarity, `U * star U = 1`, so it is an invariant of
`U(3)` and not merely of `SU(3)`; the epsilon of `IsSU2BiFundamental` uses the determinant.

Section A gives the transformation law and the span, section B the action on coefficients
and the delta contraction, section C the classification of invariant coefficients, section
D the invariants of the span, and section E the form modulo a stable submodule.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law and the span of the components

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  fundamental and one anti-fundamental index: a factor of `U` for the first index and a
  factor of `conj U` for the second. -/
def IsSU3FunAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` fundamental and one
  anti-fundamental index, transforms as a tensor `T^{a}{}_{b}` under the colour factor of
  the gauge group. Nothing is asked of the isospin and hypercharge factors. -/
structure IsSU3FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3FunAntiFunMat g (repGauge (g, 1, 1)) T

namespace IsSU3FunAntiFun

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 2 → Fin 3) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff {T : (Fin 2 → Fin 3) → B} (x : B) :
    x ∈ span T ↔ ∃ c : (Fin 2 → Fin 3) → ℂ, x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 2 → Fin 3) → B} (d : Fin 2 → Fin 3) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over pairs of colour indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] :=
  Family.sum_pi_two F

/-!

## B. The action on coefficients and the delta contraction

A coefficient function on pairs of colour indices is a `3 × 3` matrix `c ![a, b]`, and the
law says a colour rotation moves the contraction `∑ l, c l • T l` by `c ↦ U c U†`, the
action `act U`. Since `U⁻¹ = U†`, the action of `U⁻¹` is the adjoint of the action of `U`,
which is the hypothesis of `Family.exists_invariant_coeff`. The Kronecker delta is an
invariant coefficient because the rows of a unitary matrix are orthonormal, and the delta
contraction, the trace `∑ a, T ![a, a]`, is colour invariant for that reason.

-/

/-- The action of `U ∈ SU(3)` on coefficient functions, `c ↦ U c U†`. -/
noncomputable def act (U : specialUnitaryGroup (Fin 3) ℂ) :
    ((Fin 2 → Fin 3) → ℂ) →ₗ[ℂ] (Fin 2 → Fin 3) → ℂ :=
  Matrix.toLin' (Matrix.of fun a l => U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1)))

/-- The action on coefficients, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 3) ℂ) (c : (Fin 2 → Fin 3) → ℂ)
    (a : Fin 2 → Fin 3) :
    act U c a = ∑ l, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) * c l := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form. -/
lemma map_sum_smul {T : (Fin 2 → Fin 3) → B} {U : specialUnitaryGroup (Fin 3) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU3FunAntiFunMat U f T) (c : (Fin 2 → Fin 3) → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The inverse of a special unitary matrix is its conjugate transpose. -/
lemma inv_apply (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 3) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, Matrix.star_apply]
  rfl

/-- The action of `U⁻¹` is the adjoint of the action of `U`. -/
lemma sum_star_mul_act (U : specialUnitaryGroup (Fin 3) ℂ) (c d : (Fin 2 → Fin 3) → ℂ) :
    ∑ a, star (c a) * act U d a = ∑ l, star (act U⁻¹ c l) * d l := by
  simp only [act_apply, inv_apply, Finset.mul_sum, Finset.sum_mul, star_sum, star_mul',
    Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The rows of a unitary matrix are orthonormal. -/
lemma sum_mul_conj (U : specialUnitaryGroup (Fin 3) ℂ) (b c : Fin 3) :
    ∑ x : Fin 3, U.1 b x * conj (U.1 c x) = if b = c then 1 else 0 := by
  have hU : U.1 * (U.1)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
    rwa [Matrix.star_eq_conjTranspose] at h
  have h := congrFun (congrFun hU b) c
  rw [Matrix.mul_apply] at h
  simpa [Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def] using h

/-- The Kronecker delta on pairs of colour indices: the coefficients of the trace. -/
def deltaCoeff : (Fin 2 → Fin 3) → ℂ := fun l => if l 0 = l 1 then 1 else 0

/-- The Kronecker delta is an invariant coefficient. -/
lemma act_deltaCoeff (U : specialUnitaryGroup (Fin 3) ℂ) : act U deltaCoeff = deltaCoeff := by
  funext a
  rw [act_apply, sum_pi_two]
  have key : ∀ x y : Fin 3,
      (U.1 (a 0) (![x, y] 0) * conj (U.1 (a 1) (![x, y] 1))) * deltaCoeff ![x, y]
        = if y = x then U.1 (a 0) x * conj (U.1 (a 1) x) else 0 := by
    intro x y
    by_cases h : y = x
    · subst h
      simp [deltaCoeff]
    · simp [deltaCoeff, h, Ne.symm h]
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, sum_mul_conj]
  simp [deltaCoeff]

/-- The delta contraction: the colour trace of the family. -/
def deltaContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- The delta contraction is the contraction against the Kronecker delta. -/
lemma sum_deltaCoeff_smul (T : (Fin 2 → Fin 3) → B) :
    ∑ l, deltaCoeff l • T l = deltaContraction T := by
  rw [sum_pi_two]
  simp [deltaCoeff, deltaContraction, ite_smul]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T ∈ span T :=
  sum_mem fun _ _ => mem_span _

/-- Any map moving the components by an element of `SU(3)` fixes the delta contraction. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 3) → B} {U : specialUnitaryGroup (Fin 3) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU3FunAntiFunMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  rw [← sum_deltaCoeff_smul, map_sum_smul hf, act_deltaCoeff]

/-- The delta contraction is colour invariant. Nothing constrains the isospin and
  hypercharge factors, which may well move it. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge (U, 1, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T U)

/-!

## C. An invariant coefficient is a multiple of the Kronecker delta

The colour parity fixing the colour `k` and reversing the other two is the diagonal matrix
with entries `±1`, so it multiplies `c ![a, b]` by the product of the signs of `a` and `b`,
which is `-1` whenever exactly one of them is `k`: taking `k = a` kills every entry off the
diagonal. The cyclic permutation `su3Perm` of the colours carries `c ![a, a]` to
`c ![a + 1, a + 1]`, so the diagonal entries agree.

-/

/-- The entries of a colour parity. -/
lemma su3Parity_apply (k a b : Fin 3) :
    (IsSU3BiAdjoint.su3Parity k).1 a b = if a = b then (if a = k then 1 else -1) else 0 := by
  simp [IsSU3BiAdjoint.su3Parity, Matrix.diagonal_apply]

/-- A colour parity multiplies an entry by the product of the signs of its two indices. -/
lemma act_su3Parity (k : Fin 3) (c : (Fin 2 → Fin 3) → ℂ) (a b : Fin 3) :
    act (IsSU3BiAdjoint.su3Parity k) c ![a, b]
      = (if a = k then 1 else -1) * (if b = k then 1 else -1) * c ![a, b] := by
  rw [act_apply, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [su3Parity_apply, apply_ite conj]
  · intro y _ hy
    simp [su3Parity_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [su3Parity_apply, Ne.symm hx]
  · simp

/-- The cyclic permutation carries the first diagonal entry to the second. -/
lemma act_su3Perm_one_one (c : (Fin 2 → Fin 3) → ℂ) :
    act su3Perm c ![1, 1] = c ![0, 0] := by
  rw [act_apply, sum_pi_two]
  simp [su3Perm_coe, Fin.sum_univ_three]

/-- The cyclic permutation carries the second diagonal entry to the third. -/
lemma act_su3Perm_two_two (c : (Fin 2 → Fin 3) → ℂ) :
    act su3Perm c ![2, 2] = c ![1, 1] := by
  rw [act_apply, sum_pi_two]
  simp [su3Perm_coe, Fin.sum_univ_three]

/-- An invariant coefficient is a multiple of the Kronecker delta. -/
theorem exists_smul_deltaCoeff_of_act_eq {c : (Fin 2 → Fin 3) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, act U c = c) :
    ∃ z : ℂ, c = z • deltaCoeff := by
  have hoff : ∀ a b : Fin 3, a ≠ b → c ![a, b] = 0 := by
    intro a b hab
    have h := congrFun (hc (IsSU3BiAdjoint.su3Parity a)) ![a, b]
    rw [act_su3Parity, if_pos rfl, if_neg (Ne.symm hab)] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hdiag : ∀ a : Fin 3, c ![a, a] = c ![0, 0] := by
    have h1 := congrFun (hc su3Perm) ![1, 1]
    have h2 := congrFun (hc su3Perm) ![2, 2]
    rw [act_su3Perm_one_one] at h1
    rw [act_su3Perm_two_two] at h2
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
      revert a
      decide
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · rw [← h2, ← h1]
  refine ⟨c ![0, 0], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  by_cases h : a = b
  · subst h
    simp [deltaCoeff, hdiag]
  · simp [deltaCoeff, h, hoff a b h]

/-!

## D. The colour invariants of the span

-/

/-- Every invariant in the span of a family obeying the law for a family of linear maps
  `φ U` is a multiple of the delta contraction: the one singlet of `3 ⊗ 3̄`. -/
theorem exists_smul_deltaContraction_of_invariant' {T : (Fin 2 → Fin 3) → B}
    {φ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU3FunAntiFunMat U (φ U) T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ U, φ U x = x) :
    ∃ z : ℂ, x = z • deltaContraction T := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c) sum_star_mul_act hx hinv
  obtain ⟨z, hz⟩ := exists_smul_deltaCoeff_of_act_eq hc
  refine ⟨z, ?_⟩
  rw [hz, ← sum_deltaCoeff_smul, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Every colour invariant in the span of the components is a multiple of the delta
  contraction. -/
theorem exists_smul_deltaContraction_of_su3_invariant {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ z : ℂ, x = z • deltaContraction T :=
  exists_smul_deltaContraction_of_invariant' hT.repGauge_T hx hinv

/-!

## E. The invariants modulo a stable submodule

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU3FunAntiFunMat_mapQ {T : (Fin 2 → Fin 3) → B} {U : specialUnitaryGroup (Fin 3) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU3FunAntiFunMat U f T) (S : Submodule ℂ B)
    (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU3FunAntiFunMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- A colour invariant of the span of the components joined with a colour-stable submodule
  `S` is a multiple of the delta contraction up to a colour-invariant remainder in `S`. -/
theorem mem_span_sup_su3_invariant_iff {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) y = y := by
  refine Family.exists_smul_add_of_mem_sup T (fun U => repGauge (U, 1, 1)) S hS
    (deltaContraction T) (repGauge_deltaContraction hT) (fun x hx hinv => ?_) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_deltaContraction_of_invariant'
    (fun U => isSU3FunAntiFunMat_mapQ (hT.repGauge_T U) S (hS U)) hx hinv
  exact ⟨z, by rw [hz, deltaContraction, deltaContraction, map_sum]⟩

end IsSU3FunAntiFun

end StandardModel
