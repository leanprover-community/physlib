/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LightConeDeriv
public import Physlib.Mathematics.LinearCombination
/-!
# Invariants of the span of a family of components

Every file in this folder asks the same question of a different index pattern. A family `T` of
vectors of a complex vector space `B`, indexed by a finite set `ι` and moved by a
representation of `SL(2,ℂ)`, spans a subspace of `B`; which of its vectors does the group
leave alone? The answer has three steps that do not depend on the pattern.

The first, general linear algebra, turns the question into a finite one. A vector of the span
is a contraction `∑ i, c i • T i` for a coefficient function `c : ι → ℂ`, and the group moves
such a vector by moving `c`. The components may satisfy linear relations, so `c` is not
determined by the vector and need not be invariant, but the coefficients contracting to `0` form
a subspace `K` which the group preserves, and so does its orthogonal complement whenever the
coefficient action is closed under taking adjoints. Replacing `c` by its part in `Kᗮ` keeps the
vector and makes `c` invariant: `Fintype.exists_invariant_coeff_of_adjoint_mem`, in
`Physlib.Mathematics.LinearCombination`. What is left is a question about `ι`-indexed tuples of
complex numbers. This file holds the other two steps.

The second reads that condition off the transformation law. Every family here is moved by a
matrix, `repLorentz g (T l) = ∑_a M_g(a, l) • T a`, so the coefficients move by `actMat M_g`,
whose adjoint is the action of the conjugate transpose of `M_g`. The hypothesis to check is
therefore that these matrices are closed under conjugate transposition, and in every case it
is `g†` that supplies the adjoint of `g`: `exists_invariantCoeff_matrix`.

The third is for the patterns whose indices are spacetime directions, `ι = Fin n → Fin 1 ⊕
Fin 3`. There `M_g` is a product of Lorentz-matrix entries, one per slot, whose conjugate
transpose is the same product for the transposed matrix, which is again a Lorentz matrix coming
from `SL(2,ℂ)`, so `exists_isInvariantCoeff_of_mem_span` applies. Writing each slot of a
coefficient tensor in the light-cone basis of an axis splits it into pieces that a boost
scales by powers of its parameter, and an invariant keeps only the piece of weight zero:
`IsInvariantCoeff.lightConeComponent_eq_zero`. The Weyl patterns run the same argument on the
second step with the Weyl weight bases of `Fermions.Weyl.BoostWeight`.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-!

## A. Coefficient functions moved by a matrix

Every family in this folder is moved by a matrix: `repLorentz g (T l) = ∑_a M_g(a, l) • T a`,
with `M_g` built from the Lorentz matrix of `g`, from `g` itself on Weyl indices, or from both.
The coefficients then move by `actMat M_g`, whose adjoint is the action of the conjugate
transpose of `M_g`. So the adjoint hypothesis of `Fintype.exists_invariant_coeff_of_adjoint_mem`
reads: for every `g` some `g'` has `M_{g'}` the conjugate transpose of `M_g`. In every case below
`g'` is `g†`.

The weight argument is also generic: a covector that the transposed matrix reproduces up to a
scalar reads off a component that `actMat M_g` scales by that scalar, so an invariant
coefficient function has no such component unless the scalar is `1`.

-/

section Mat

variable {ι : Type} [Fintype ι] {G : Type*}

/-- The action on coefficient functions of a matrix moving the components:
  `(actMat M c) a = ∑_d c_d M_{a d}`, with `a` free and `d` summed. -/
def actMat (M : ι → ι → ℂ) (c : ι → ℂ) (a : ι) : ℂ := ∑ d, c d * M a d

/-- That action, as a linear map. -/
noncomputable def actMatₗ (M : ι → ι → ℂ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun := actMat M
  map_add' c c' := by
    funext a
    simp only [actMat, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' z c := by
    funext a
    simp only [actMat, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

open scoped InnerProductSpace in
/-- Across the standard inner product the action of `M` becomes that of its conjugate
  transpose. The action is not unitary, and is not used to be. -/
lemma inner_actMat (M N : ι → ι → ℂ) (hN : ∀ a d, N a d = star (M d a))
    (u v : EuclideanSpace ℂ ι) :
    ⟪u, WithLp.toLp 2 (actMat M v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (actMat N u.ofLp), v⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, actMat, hN, map_sum, map_mul, Complex.conj_conj,
    Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring

/-- An invariant of the span is the contraction of a coefficient function that every `M g`
  fixes, provided the matrices are closed under conjugate transposition. -/
theorem exists_invariantCoeff_matrix (T : ι → B) (φ : G → B →ₗ[ℂ] B) (M : G → ι → ι → ℂ)
    (hT : ∀ (g : G) l, φ g (T l) = ∑ a, M g a l • T a)
    (hM : ∀ g : G, ∃ g' : G, ∀ a d, M g' a d = star (M g d a))
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, (∀ g, actMat (M g) c = c) ∧ x = ∑ i, c i • T i := by
  obtain ⟨c, hc, hinvc⟩ := Fintype.exists_invariant_coeff_of_adjoint_mem T φ
    (fun g => actMatₗ (M g))
    (fun g c => (φ g).map_sum_smul_of_forall_eq T T (M g) (hT g) c)
    (fun g => by
      obtain ⟨g', hg'⟩ := hM g
      exact ⟨g', fun u v => inner_actMat (M g) (M g') hg' u v⟩) hx hinv
  exact ⟨c, hinvc, hc⟩

/-- A covector `P` that the transposed matrix reproduces up to a scalar `k` reads off a
  component of the coefficients that `actMat M` scales by `k`. -/
lemma sum_mul_actMat (M : ι → ι → ℂ) (P c : ι → ℂ) (k : ℂ)
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) :
    ∑ a, P a * actMat M c a = k * ∑ a, P a * c a := by
  simp only [actMat, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← mul_assoc, mul_comm _ (c d), ← hP d, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- A coefficient function fixed by `actMat M` has no component along a covector that the
  transposed matrix scales by an eigenvalue other than `1`. -/
lemma sum_mul_eq_zero_of_actMat_eq (M : ι → ι → ℂ) {P c : ι → ℂ} (hc : actMat M c = c) {k : ℂ}
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) (hk : k ≠ 1) :
    ∑ a, P a * c a = 0 := by
  have h := sum_mul_actMat M P c k hP
  rw [hc] at h
  exact (mul_left_eq_self₀.1 h.symm).resolve_left hk

/-- The boost with parameter `2` distinguishes every nonzero weight: `2 ^ w ≠ 1` for `w ≠ 0`. -/
lemma two_zpow_ne_one {w : ℤ} (hw : w ≠ 0) : ((2 : ℝ) : ℂ) ^ w ≠ 1 := by
  rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
  exact hw

end Mat

/-!

## B. Coefficient tensors on spacetime indices

-/

section Spacetime

variable {n : ℕ}

/-- The conjugate transpose `g†` of an element of `SL(2,ℂ)`, again in `SL(2,ℂ)`. -/
def dagger (g : SL(2,ℂ)) : SL(2,ℂ) := ⟨g.1ᴴ, by rw [Matrix.det_conjTranspose, g.2, star_one]⟩

/-- The Lorentz matrix of `g†` is the transpose of that of `g`, so these matrices are closed
  under transposition. -/
lemma toLorentzGroup_dagger (g : SL(2,ℂ)) :
    (SL2C.toLorentzGroup (dagger g)).1 = (SL2C.toLorentzGroup g).1ᵀ :=
  SL2C.toLorentzGroup_conjTranspose rfl

/-- The action of a real `4 × 4` matrix on coefficient tensors, one factor per slot:
  `(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯`, with `a` free and `d` summed. -/
def act (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ d, c d * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)

/-- The action on coefficient tensors is that of the matrix of products, one factor per slot. -/
lemma act_eq_actMat (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    act Λ c = actMat (fun a d => ∏ i, ((Λ (a i) (d i) : ℝ) : ℂ)) c := rfl

/-- A coefficient tensor fixed by `act` of the Lorentz matrix of every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) : Prop :=
  ∀ g : SL(2,ℂ), act (SL2C.toLorentzGroup g).1 c = c

section Monoid

variable {B : Type*} [AddCommMonoid B] [Module ℂ B]

/-- Transforming a contraction is the same as contracting the transformed coefficient tensor. -/
lemma repLorentz_sum_smul {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hT : ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a)
    (g : SL(2,ℂ)) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    repLorentz g (∑ d, c d • T d) = ∑ a, act (SL2C.toLorentzGroup g).1 c a • T a :=
  (repLorentz g).map_sum_smul_of_forall_eq T T _ (hT g) c

/-- Contracting the components with an invariant coefficient tensor gives a vector fixed by
  the representation. -/
lemma repLorentz_sum_smul_of_isInvariantCoeff {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hT : ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a)
    {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) (g : SL(2,ℂ)) :
    repLorentz g (∑ d, c d • T d) = ∑ d, c d • T d := by
  rw [repLorentz_sum_smul hT, hc g]

end Monoid

/-- An invariant of the span is the contraction of an invariant coefficient tensor: the
  adjoint of `act Λ` is the action of `Λᵀ`, which is the Lorentz matrix of `g†`. -/
theorem exists_isInvariantCoeff_of_mem_span {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hT : ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a)
    {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d := by
  obtain ⟨c, hc, hx'⟩ := exists_invariantCoeff_matrix T (fun g => repLorentz g)
    (fun g a d => ∏ i, (((SL2C.toLorentzGroup g).1 (a i) (d i) : ℝ) : ℂ)) hT
    (fun g => ⟨dagger g, fun a d => by
      rw [toLorentzGroup_dagger]
      simp [Matrix.transpose_apply]⟩) hx hinv
  exact ⟨c, fun g => (act_eq_actMat _ c).trans (hc g), hx'⟩

/-- A light-cone component of a coefficient tensor along axis `i`: the multi-index `κ` picks
  one light-cone direction per slot and `c` is contracted against that choice. -/
def lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) : ℂ :=
  ∑ a, (∏ s, lightConeCoeff i (κ s) (a s)) * c a

/-- A light-cone multi-index that `Λ` reproduces up to a scalar `k` has its light-cone
  component scaled by `k`. The hypothesis is the eigenvector equation for the covector
  `∏ₛ lightConeCoeff i (κ s) (·)` under the transposed action, which is the form the light-cone
  directions of an axis satisfy for the transformations diagonal in that basis: the boost along
  the axis, with `k` a power of its parameter, and the half turn about it, with `k` the product
  of the signs of the slots. -/
lemma lightConeComponent_act (i : Fin 3) (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) (k : ℂ)
    (hΛ : ∀ d : Fin n → Fin 1 ⊕ Fin 3,
      ∑ a : Fin n → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (κ s) (a s))
          * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)
        = k * ∏ s, lightConeCoeff i (κ s) (d s)) :
    lightConeComponent i (act Λ c) κ = k * lightConeComponent i c κ :=
  sum_mul_actMat _ _ c k hΛ

/-- The Lorentz matrix of a boost is symmetric. -/
lemma toLorentzGroup_boostAxis_symm (i : Fin 3) {t : ℝ} (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 a b
      = (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 b a :=
  congrFun (congrFun
    (SL2C.toLorentzGroup_conjTranspose (SL2C.boostAxis_conjTranspose i t ht).symm) a) b

/-- The boost with parameter `t` multiplies a light-cone component by `t` raised to the weight
  of `κ`, the sum of the weights of the directions `κ` picks. -/
lemma lightConeComponent_act_boostAxis (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (κ : Fin n → Fin 4) {t : ℝ} (ht : t ≠ 0) :
    lightConeComponent i (act (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 c) κ
      = ((t : ℝ) : ℂ) ^ (∑ s, lightConeWeight (κ s)) * lightConeComponent i c κ :=
  lightConeComponent_act i _ c κ _ fun d => by
    simpa only [toLorentzGroup_boostAxis_symm i ht (d _)] using sum_prod_lightConeCoeff i κ d ht

/-- An invariant coefficient tensor has no light-cone component of nonzero weight: the boost at
  `t = 2` would rescale such a component by a factor other than `1`. -/
lemma IsInvariantCoeff.lightConeComponent_eq_zero {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin n → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) ≠ 0) :
    lightConeComponent i c κ = 0 :=
  sum_mul_eq_zero_of_actMat_eq _ (hc (SL2C.boostAxis i 2 two_ne_zero))
    (fun d => by
      simpa only [toLorentzGroup_boostAxis_symm i two_ne_zero (d _)] using
        sum_prod_lightConeCoeff i κ d two_ne_zero)
    (two_zpow_ne_one hκ)

/-- A coefficient tensor is recovered from its light-cone components. -/
lemma eq_sum_lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (d : Fin n → Fin 1 ⊕ Fin 3) :
    c d = ∑ κ, (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_prod_lightConeCoeffInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Spacetime

end Invariants

end Lorentz
