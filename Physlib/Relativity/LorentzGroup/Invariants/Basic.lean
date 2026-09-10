/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LightConeDeriv
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
/-!
# Invariants of the span of a family of components

Every file in this folder asks the same question of a different index pattern. A family `T` of
vectors of a complex vector space `B`, indexed by a finite set `ι` and moved by a
representation of `SL(2,ℂ)`, spans a subspace of `B`; which of its vectors does the group
leave alone? This file holds the three steps of the answer that do not depend on the pattern.

The first turns the question into a finite one. A vector of the span is a contraction
`∑ i, c i • T i` for a coefficient function `c : ι → ℂ`, and the group moves such a vector by
moving `c`. The components may satisfy linear relations, so `c` is not determined by the
vector and need not be invariant, but the coefficients contracting to `0` form a subspace `K`
which the group preserves, and so does its orthogonal complement whenever the coefficient
action is closed under taking adjoints. Replacing `c` by its part in `Kᗮ` keeps the vector and
makes `c` invariant: `exists_invariantCoeff`. What is left is a question about `ι`-indexed
tuples of complex numbers.

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
`IsInvariantCoeff.lightConeComponent_eq_zero`. The Weyl patterns have their own weight bases,
built in the files that need them on top of the second step.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-!

## A. An invariant of the span is the contraction of an invariant coefficient

-/

section Complement

variable {ι : Type} [Fintype ι] {G : Type*}

/-- Contraction with the components, as a linear map on the coefficients carrying the standard
  inner product; `WithLp.toLp 2` and `.ofLp` only translate to the plain function type. -/
noncomputable def contractₗ (T : ι → B) : EuclideanSpace ℂ ι →ₗ[ℂ] B where
  toFun c := ∑ i, c.ofLp i • T i
  map_add' c c' := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      smul_smul]

open scoped InnerProductSpace in
/-- An invariant of the span is the contraction of an invariant coefficient function, provided
  the coefficient action `A` has all its adjoints inside the family: for every `g` some `g'`
  acts as the adjoint of `g`. Nothing is claimed about uniqueness, the components being
  possibly dependent. -/
theorem exists_invariantCoeff (T : ι → B) (φ : G → B →ₗ[ℂ] B)
    (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hφ : ∀ (g : G) (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g : G, ∃ g' : G, ∀ u v : EuclideanSpace ℂ ι,
      ⟪u, WithLp.toLp 2 (A g v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (A g' u.ofLp), v⟫_ℂ)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c := by
  classical
  obtain ⟨c, rfl⟩ : ∃ c : ι → ℂ, x = ∑ i, c i • T i := by
    rw [← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
      LinearMap.mem_range] at hx
    simpa only [Fintype.linearCombination_apply, eq_comm] using hx
  have hcontr : ∀ (g : G) (u : EuclideanSpace ℂ ι),
      contractₗ T (WithLp.toLp 2 (A g u.ofLp)) = φ g (contractₗ T u) :=
    fun g u => (hφ g u.ofLp).symm
  set K := LinearMap.ker (contractₗ T) with hK
  have hKstab : ∀ (g : G) (u : EuclideanSpace ℂ ι), u ∈ K →
      WithLp.toLp 2 (A g u.ofLp) ∈ K := by
    intro g u hu
    rw [hK, LinearMap.mem_ker] at hu ⊢
    rw [hcontr, hu, map_zero]
  obtain ⟨k, hk, k', hk', hkk'⟩ := K.exists_add_mem_mem_orthogonal (WithLp.toLp 2 c)
  have hx' : ∑ i, c i • T i = contractₗ T k' := by
    have h := congrArg (contractₗ T) hkk'
    rwa [map_add, LinearMap.mem_ker.1 hk, zero_add] at h
  refine ⟨k'.ofLp, hx', fun g => ?_⟩
  have h1 : WithLp.toLp 2 (A g k'.ofLp) - k' ∈ K := by
    rw [hK, LinearMap.mem_ker, map_sub, hcontr, ← hx', hinv, hx', sub_self]
  have h2 : WithLp.toLp 2 (A g k'.ofLp) ∈ Kᗮ := by
    obtain ⟨g', hg'⟩ := hA g
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [hg' u k']
    exact Submodule.inner_right_of_mem_orthogonal (hKstab g' u hu) hk'
  have h3 : WithLp.toLp 2 (A g k'.ofLp) - k' ∈ K ⊓ Kᗮ :=
    ⟨h1, Submodule.sub_mem _ h2 hk'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
  exact congrArg WithLp.ofLp h3

end Complement

/-!

## B. Coefficient functions moved by a matrix

Every family in this folder is moved by a matrix: `repLorentz g (T l) = ∑_a M_g(a, l) • T a`,
with `M_g` built from the Lorentz matrix of `g`, from `g` itself on Weyl indices, or from both.
The coefficients then move by `actMat M_g`, whose adjoint is the action of the conjugate
transpose of `M_g`. So the hypothesis of A reads: for every `g` some `g'` has `M_{g'}` the
conjugate transpose of `M_g`. In every case below `g'` is `g†`.

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
  obtain ⟨c, hc, hinvc⟩ := exists_invariantCoeff T φ (fun g => actMatₗ (M g))
    (fun g c => by
      simp only [map_sum, map_smul, hT, Finset.smul_sum, smul_smul, actMatₗ, LinearMap.coe_mk,
        AddHom.coe_mk, actMat, Finset.sum_smul]
      exact Finset.sum_comm)
    (fun g => by
      obtain ⟨g', hg'⟩ := hM g
      exact ⟨g', fun u v => inner_actMat (M g) (M g') hg' u v⟩) hx hinv
  exact ⟨c, hinvc, hc⟩

end Mat

/-!

## C. Coefficient tensors on spacetime indices

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

/-- Transforming a contraction is the same as contracting the transformed coefficient tensor. -/
lemma repLorentz_sum_smul {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hT : ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a)
    (g : SL(2,ℂ)) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    repLorentz g (∑ d, c d • T d) = ∑ a, act (SL2C.toLorentzGroup g).1 c a • T a := by
  simp only [map_sum, map_smul, hT, Finset.smul_sum, smul_smul, act, Finset.sum_smul]
  exact Finset.sum_comm

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

/-- Contracting the components with an invariant coefficient tensor gives a vector fixed by
  the representation. -/
lemma repLorentz_sum_smul_of_isInvariantCoeff {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hT : ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a)
    {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) (g : SL(2,ℂ)) :
    repLorentz g (∑ d, c d • T d) = ∑ d, c d • T d := by
  rw [repLorentz_sum_smul hT, hc g]

/-- A light-cone component of a coefficient tensor along axis `i`: the multi-index `κ` picks
  one light-cone direction per slot and `c` is contracted against that choice. -/
def lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) : ℂ :=
  ∑ a, (∏ s, lightConeCoeff i (κ s) (a s)) * c a

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
      = ((t : ℝ) : ℂ) ^ (∑ s, lightConeWeight (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, act, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := sum_prod_lightConeCoeff i κ d ht
  simp only [toLorentzGroup_boostAxis_symm i ht (d _)] at h
  rw [← mul_assoc, mul_comm _ (c d), ← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- An invariant coefficient tensor has no light-cone component of nonzero weight: the boost at
  `t = 2` would rescale such a component by a factor other than `1`. -/
lemma IsInvariantCoeff.lightConeComponent_eq_zero {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin n → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) ≠ 0) :
    lightConeComponent i c κ = 0 := by
  have h := lightConeComponent_act_boostAxis i c κ (two_ne_zero (α := ℝ))
  rw [hc] at h
  have h2 : ((2 : ℝ) : ℂ) ^ (∑ s, lightConeWeight (κ s)) ≠ 1 := by
    rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
      zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
    exact hκ
  exact (mul_left_eq_self₀.1 h.symm).resolve_left h2

/-- A coefficient tensor is recovered from its light-cone components. -/
lemma eq_sum_lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (d : Fin n → Fin 1 ⊕ Fin 3) :
    c d = ∑ κ, (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_prod_lightConeCoeffInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Spacetime

end Invariants

end Lorentz
