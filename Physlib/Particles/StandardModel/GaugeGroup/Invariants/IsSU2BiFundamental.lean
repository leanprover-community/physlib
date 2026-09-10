/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
/-!
# Gauge tensors carrying two `su(2)` fundamental indices

The Higgs field and the left-handed fermions are isospin doublets: each carries one
fundamental `su(2)` index, taking two values. A product of two doublets carries two, and
there is exactly one way to contract them into an isospin singlet: `2 ⊗ 2 = 1 ⊕ 3`, and the
singlet is the antisymmetric combination `ε_{ab} T^{ab} = T^{01} - T^{10}`. It is invariant
because the antisymmetric symbol of a two-dimensional space transforms by the determinant,
and the determinant of an element of `SU(2)` is one. This file proves that the antisymmetric
contraction is the only invariant, in the form the Standard Model files consume, modulo an
isospin-stable submodule in which other families are parked.

`IsSU2BiFundamental B repGauge T` records the hypothesis. `T` is a family indexed by two
fundamental indices and valued in a module `B` carrying a representation of the gauge group,
and an isospin rotation `U ∈ SU(2)` moves its components by one factor of `U` per index.
Nothing is asked of the colour and hypercharge factors, which may well move the components:
a product of two Higgs fields carries hypercharge.

The proof follows `IsSU2BiAdjoint`. The action on coefficient functions `c ![a, b]` is
`c ↦ U c Uᵀ`, unitary, so an isospin invariant of the span is the contraction of an
invariant coefficient, by `Family.exists_invariant_coeff`. An invariant coefficient is a
`2 × 2` matrix fixed by every `U ∈ SU(2)`, and two rotations pin it down. The diagonal
element `diag(i, -i)` scales each diagonal entry `c ![a, a]` by `i² = -1`, so the matrix has
zero diagonal, and the Weyl element `su2Perm = !![0, -1; 1, 0]` carries `c ![1, 0]` to
`-c ![0, 1]`, so the matrix is antisymmetric. It is a multiple of the antisymmetric symbol
and the vector a multiple of the epsilon contraction.

Section A gives the transformation law and the span, section B the antisymmetric symbol and
the epsilon contraction, section C the action on coefficients, section D the classification
of invariant coefficients, section E the invariants of the span, and section F the form
modulo a stable submodule. An aside at the end records how the entries of an `SU(2)` matrix
behave under complex conjugation, which is what `IsSU2AntiFundamental` needs to reduce
anti-fundamental indices to fundamental ones.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law and the span of the components

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  fundamental indices: one factor of `U` per index, with the summed index in the row
  slot. -/
def IsSU2BiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` fundamental indices, transforms
  as a tensor `T^{a b}` under the isospin factor of the gauge group. Nothing is asked of the
  colour and hypercharge factors. -/
structure IsSU2BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 2 → Fin 2) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff {T : (Fin 2 → Fin 2) → B} (x : B) :
    x ∈ span T ↔ ∃ (c : (Fin 2 → Fin 2) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 2 → Fin 2) → B} (d : Fin 2 → Fin 2) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over pairs of fundamental indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 2) → M) :
    ∑ d : Fin 2 → Fin 2, F d = ∑ x : Fin 2, ∑ y : Fin 2, F ![x, y] :=
  Family.sum_pi_two F

/-!

## B. The antisymmetric symbol and the epsilon contraction

The antisymmetric symbol `ε` on two indices is the Levi-Civita symbol of `Fin 2`, written
as Physlib writes every Levi-Civita symbol, as a generalized Kronecker delta. Its invariance
under `SU(2)`, `∑ x y, ε x y U b x U c y = ε b c`, is the statement that the determinant of
`U` is one, and it makes the epsilon contraction `T ![0, 1] - T ![1, 0]` invariant.

-/

/-- The antisymmetric symbol on a pair of `su(2)` fundamental indices, normalized so that
  its value on the increasing pair is one. -/
def epsilon (a b : Fin 2) : ℂ :=
  (KroneckerDelta.generalizedKroneckerDelta ![a, b] (id : Fin 2 → Fin 2) : ℤ)

/-- The two-by-two determinant, stated for a plain function of the indices. Unfolding
  `generalizedKroneckerDelta` leaves the matrix as a bare lambda, which `Matrix.det_fin_two`
  cannot match through the `Matrix` type synonym. -/
private lemma det_fin_two_fun (f : Fin 2 → Fin 2 → ℤ) :
    Matrix.det f = f 0 0 * f 1 1 - f 0 1 * f 1 0 :=
  Matrix.det_fin_two _

/-- The antisymmetric symbol vanishes on the repeated lower index. -/
@[simp] lemma epsilon_zero_zero : epsilon 0 0 = 0 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, det_fin_two_fun]

/-- The antisymmetric symbol on the increasing pair. -/
@[simp] lemma epsilon_zero_one : epsilon 0 1 = 1 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, det_fin_two_fun,
    KroneckerDelta.kroneckerDelta]

/-- The antisymmetric symbol on the decreasing pair. -/
@[simp] lemma epsilon_one_zero : epsilon 1 0 = -1 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, det_fin_two_fun,
    KroneckerDelta.kroneckerDelta]

/-- The antisymmetric symbol vanishes on the repeated upper index. -/
@[simp] lemma epsilon_one_one : epsilon 1 1 = 0 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, det_fin_two_fun]

/-- The antisymmetric symbol is invariant under an element of `SU(2)`, because its
  determinant is one. -/
lemma sum_epsilon_mul (U : specialUnitaryGroup (Fin 2) ℂ) (b c : Fin 2) :
    ∑ x : Fin 2, ∑ y : Fin 2, epsilon x y * (U.1 b x * U.1 c y) = epsilon b c := by
  have hdet : U.1 0 0 * U.1 1 1 - U.1 0 1 * U.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
  fin_cases b <;> fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.sum_univ_two,
      epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one]
  · ring
  · linear_combination hdet
  · linear_combination -hdet
  · ring

/-- The epsilon contraction: the antisymmetric contraction of the two fundamental
  indices. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

/-- The antisymmetric symbol as a coefficient function on pairs of indices. -/
def epsilonCoeff : (Fin 2 → Fin 2) → ℂ := fun l => epsilon (l 0) (l 1)

/-- The epsilon contraction is the contraction against the antisymmetric symbol. -/
lemma sum_epsilonCoeff_smul (T : (Fin 2 → Fin 2) → B) :
    ∑ l, epsilonCoeff l • T l = epsilonContraction T := by
  rw [sum_pi_two]
  simp [epsilonCoeff, epsilonContraction, Fin.sum_univ_two, sub_eq_add_neg]

/-- The epsilon contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T ∈ span T :=
  sub_mem (mem_span _) (mem_span _)

/-!

## C. The action on coefficients

A vector of the span is a contraction `∑ l, c l • T l` against a coefficient function `c`
on pairs of indices, and the law says that an isospin rotation moves it by moving `c` with
the Kronecker square `act U` of `U`. Unitarity of `U` makes `act U⁻¹` the adjoint of
`act U`, which is the hypothesis of `Family.exists_invariant_coeff`. The antisymmetric
symbol is an invariant coefficient, so the epsilon contraction is invariant.

-/

/-- The action of `U ∈ SU(2)` on coefficient functions: the Kronecker square of `U`. -/
noncomputable def act (U : specialUnitaryGroup (Fin 2) ℂ) :
    ((Fin 2 → Fin 2) → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2) → ℂ :=
  Matrix.toLin' (Matrix.of fun a l => ∏ i : Fin 2, U.1 (a i) (l i))

/-- The action on coefficients, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 2 → Fin 2) → ℂ)
    (a : Fin 2 → Fin 2) :
    act U c a = ∑ l, (∏ i : Fin 2, U.1 (a i) (l i)) * c l := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form. -/
lemma map_sum_smul {T : (Fin 2 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2BiFundamentalMat U f T) (c : (Fin 2 → Fin 2) → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The inverse of a special unitary matrix is its conjugate transpose. -/
lemma inv_apply (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, Matrix.star_apply]
  rfl

/-- The action of `U⁻¹` is the adjoint of the action of `U`. -/
lemma sum_star_mul_act (U : specialUnitaryGroup (Fin 2) ℂ) (c d : (Fin 2 → Fin 2) → ℂ) :
    ∑ a, star (c a) * act U d a = ∑ l, star (act U⁻¹ c l) * d l := by
  simp only [act_apply, inv_apply, Fin.prod_univ_two, Finset.mul_sum, Finset.sum_mul,
    star_sum, star_mul', Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The antisymmetric symbol is an invariant coefficient. -/
lemma act_epsilonCoeff (U : specialUnitaryGroup (Fin 2) ℂ) : act U epsilonCoeff = epsilonCoeff := by
  funext a
  rw [act_apply, sum_pi_two]
  simp only [epsilonCoeff, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_epsilon_mul U (a 0) (a 1)]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- Any map moving the components by an element of `SU(2)` fixes the epsilon
  contraction. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2BiFundamentalMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  rw [← sum_epsilonCoeff_smul, map_sum_smul hf, act_epsilonCoeff]

/-- The epsilon contraction is isospin invariant. Nothing constrains the colour and
  hypercharge factors, which may well move it. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T V)

/-!

## D. An invariant coefficient is a multiple of the antisymmetric symbol

The isospin flip `su2Flip 2` about the third axis is the diagonal matrix `diag(i, -i)`. It
scales `c ![a, b]` by the product of the two diagonal entries, which on the diagonal `a = b`
is `-1`, so an invariant coefficient has zero diagonal. The Weyl element `su2Perm`, the
matrix `!![0, -1; 1, 0]`, carries `c ![1, 0]` to `-c ![0, 1]`, so an invariant coefficient
is antisymmetric.

-/

/-- The isospin flip about the third axis is the diagonal matrix `diag(i, -i)`. -/
lemma su2Flip_two_apply (a b : Fin 2) :
    (IsSU2BiAdjoint.su2Flip 2).1 a b
      = if a = b then ![Complex.I, -Complex.I] a else 0 := by
  rw [IsSU2BiAdjoint.su2Flip_coe]
  fin_cases a <;> fin_cases b <;> simp [IsSU2BiAdjoint.su2FlipMatrix]

/-- The flip about the third axis scales a coefficient by the product of the diagonal
  entries at its two indices. -/
lemma act_su2Flip_two (c : (Fin 2 → Fin 2) → ℂ) (a b : Fin 2) :
    act (IsSU2BiAdjoint.su2Flip 2) c ![a, b]
      = ![Complex.I, -Complex.I] a * ![Complex.I, -Complex.I] b * c ![a, b] := by
  rw [act_apply, sum_pi_two, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [su2Flip_two_apply]
  · intro y _ hy
    simp [su2Flip_two_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    simp [su2Flip_two_apply, Ne.symm hx]
  · simp

/-- The Weyl element carries the lower mixed coefficient to minus the upper one. -/
lemma act_su2Perm_one_zero (c : (Fin 2 → Fin 2) → ℂ) :
    act su2Perm c ![1, 0] = -c ![0, 1] := by
  rw [act_apply, sum_pi_two]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_two]

/-- An invariant coefficient is a multiple of the antisymmetric symbol. -/
theorem exists_smul_epsilonCoeff_of_act_eq {c : (Fin 2 → Fin 2) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, act U c = c) :
    ∃ z : ℂ, c = z • epsilonCoeff := by
  have hdiag : ∀ a : Fin 2, c ![a, a] = 0 := by
    intro a
    have hsq : ![Complex.I, -Complex.I] a * ![Complex.I, -Complex.I] a = -1 := by
      fin_cases a <;> simp
    have h := congrFun (hc (IsSU2BiAdjoint.su2Flip 2)) ![a, a]
    rw [act_su2Flip_two, hsq] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hoff : c ![1, 0] = -c ![0, 1] := by
    have h := congrFun (hc su2Perm) ![1, 0]
    rw [act_su2Perm_one_zero] at h
    exact h.symm
  refine ⟨c ![0, 1], funext fun l => ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = ![a, b] := ⟨l 0, l 1, by ext i; fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> simp [epsilonCoeff, hdiag, hoff]

/-!

## E. The isospin invariants of the span

The action on coefficients is unitary, so `Family.exists_invariant_coeff` writes an isospin
invariant of the span as the contraction of an invariant coefficient, and section D makes
that coefficient a multiple of the antisymmetric symbol. The statement is made for any
family of linear maps `φ U` obeying the law, so that section F can apply it in a quotient.

-/

/-- Every invariant in the span of a family obeying the law for a family of linear maps
  `φ U` is a multiple of the epsilon contraction: the one singlet of `2 ⊗ 2`. -/
theorem exists_smul_epsilonContraction_of_invariant' {T : (Fin 2 → Fin 2) → B}
    {φ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU2BiFundamentalMat U (φ U) T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ U, φ U x = x) :
    ∃ z : ℂ, x = z • epsilonContraction T := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c) sum_star_mul_act hx hinv
  obtain ⟨z, hz⟩ := exists_smul_epsilonCoeff_of_act_eq hc
  refine ⟨z, ?_⟩
  rw [hz, ← sum_epsilonCoeff_smul, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Every isospin invariant in the span of the components is a multiple of the epsilon
  contraction. -/
theorem exists_smul_epsilonContraction_of_su2_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ z : ℂ, x = z • epsilonContraction T :=
  exists_smul_epsilonContraction_of_invariant' hT.repGauge_T hx hinv

/-!

## F. The invariants modulo a stable submodule

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU2BiFundamentalMat_mapQ {T : (Fin 2 → Fin 2) → B}
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU2BiFundamentalMat U f T)
    (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU2BiFundamentalMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` is a multiple of the epsilon contraction up to an isospin-invariant
  remainder in `S`. -/
theorem mem_span_sup_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • epsilonContraction T + y
      ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  refine Family.exists_smul_add_of_mem_sup T (fun V => repGauge (1, V, 1)) S hS
    (epsilonContraction T) (repGauge_epsilonContraction hT) (fun x hx hinv => ?_) hx hinv
  obtain ⟨z, hz⟩ := exists_smul_epsilonContraction_of_invariant'
    (fun V => isSU2BiFundamentalMat_mapQ (hT.repGauge_T V) S (hS V)) hx hinv
  exact ⟨z, by rw [hz, epsilonContraction, epsilonContraction, map_sub]⟩

/-!

## Aside: the entries of an `SU(2)` matrix under conjugation

Nothing from here on is used by the theorem above. `SU(2)` is pseudo-real: the conjugate of
an `SU(2)` matrix is its conjugate by the antisymmetric symbol, so an anti-fundamental index
is a fundamental index in another basis. `IsSU2AntiFundamental` reduces its two laws to the
one above by that change of basis, and what it needs is the four identities
`conj U₀₀ = U₁₁`, `conj U₁₁ = U₀₀`, `conj U₀₁ = -U₁₀`, `conj U₁₀ = -U₀₁`. They come from one
computation: the determinant being one, the adjugate of `U` is its inverse, and `U` being
unitary, so is its conjugate transpose. The Higgs sector uses the same four identities.

-/

/-- An index pair is the pair of its own two entries. -/
lemma eq_cons (d : Fin 2 → Fin 2) : d = ![d 0, d 1] :=
  funext fun j => by fin_cases j <;> simp

/-- The conjugate transpose of an `SU(2)` matrix is its adjugate. -/
lemma star_eq_adjugate (U : specialUnitaryGroup (Fin 2) ℂ) :
    star U.1 = Matrix.adjugate U.1 := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  have hu : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp hmem.1
  calc star U.1 = star U.1 * (U.1 * Matrix.adjugate U.1) := by
        rw [Matrix.mul_adjugate, hmem.2, one_smul, mul_one]
    _ = star U.1 * U.1 * Matrix.adjugate U.1 := by rw [mul_assoc]
    _ = Matrix.adjugate U.1 := by rw [hu, one_mul]

/-- The conjugate of an entry of an `SU(2)` matrix is the transposed entry of its
  adjugate. -/
lemma conj_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    conj (U.1 i j) = Matrix.adjugate U.1 j i := by
  have := congrFun (congrFun (star_eq_adjugate U) j) i
  simpa [Matrix.star_apply] using this

/-- Conjugating the upper left entry of an `SU(2)` matrix gives the lower right one. -/
@[simp] lemma conj_apply_zero_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 0) = U.1 1 1 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower right entry of an `SU(2)` matrix gives the upper left one. -/
@[simp] lemma conj_apply_one_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 1) = U.1 0 0 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the upper right entry of an `SU(2)` matrix gives minus the lower left
  one. -/
@[simp] lemma conj_apply_zero_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 1) = -U.1 1 0 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower left entry of an `SU(2)` matrix gives minus the upper right
  one. -/
@[simp] lemma conj_apply_one_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 0) = -U.1 0 1 := by
  rw [conj_apply, Matrix.adjugate_fin_two]
  simp

end IsSU2BiFundamental

end StandardModel
