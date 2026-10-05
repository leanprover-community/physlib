/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.AdjointClosed
/-!
# Lorentz invariants of two Weyl indices of the same kind

Let `k` be one of the four Weyl colours and `f : ℂT[k, k] →ₗ[ℂ] B` a Lorentz-equivariant linear
map. Every Lorentz invariant in the range of `f` is a multiple of `f (metricTensor k)`, the
image of the `ε` metric of that colour, the shape of a Majorana or Dirac mass term. That is
`exists_smul_map_metricTensor_add_of_invariant`, stated modulo a
Lorentz-stable submodule `S`, and packaged for the reductions of the Standard Model as
`invariantReductionToMetricTensor`. The families with two left-handed,
two right-handed, two dual left-handed and two dual right-handed indices are `IsBiLeftWeyl`,
`IsBiRightWeyl`, `IsBiDualLeftWeyl` and `IsBiDualRightWeyl` (A).

By `TensorSpecies.IsEquivariant.invariantReductionToSpan` it is enough to show that the invariant
tensors of `ℂT[k, k]` are the multiples of `metricTensor k` (B). Two elements of `SL(2,ℂ)` pin
the components `r` of an invariant tensor down. The first acts on the colour `k` by
`diag (2, 2⁻¹)`, which scales `r (0, 0)` by `4` and `r (1, 1)` by `4⁻¹`, so these vanish. The
second acts by an antidiagonal matrix with entries `μ`, `μ² = -1`, which sends `r (0, 1)` to
`μ² r (1, 0)`, so `r (0, 1) = -r (1, 0)`. For `k = upL` these are the boost along `z` and the
half turn about `x`; for the other colours they are their images under conjugation and inversion.
The metric is itself invariant, with a nonzero `(0, 1)` component, so `r` is a multiple of its
components.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Families with two Weyl indices of the same kind

-/

/-- A family with two left-handed Weyl indices `T^{α₁ α₂}`: an equivariant linear map out of
  `ℂT[.upL, .upL]`. -/
abbrev IsBiLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upL, .upL] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upL, .upL] repLorentz f

/-- A family with two right-handed Weyl indices `T^{α̇₁ α̇₂}`: an equivariant linear map out of
  `ℂT[.upR, .upR]`. -/
abbrev IsBiRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upR, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upR, .upR] repLorentz f

/-- A family with two dual left-handed Weyl indices `T_{α₁ α₂}`: an equivariant linear map out
  of `ℂT[.downL, .downL]`. -/
abbrev IsBiDualLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downL, .downL] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentz f

/-- A family with two dual right-handed Weyl indices `T_{α̇₁ α̇₂}`: an equivariant linear map
  out of `ℂT[.downR, .downR]`. -/
abbrev IsBiDualRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downR, .downR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downR, .downR] repLorentz f

/-!

## B. The invariant tensors with two Weyl indices of the same kind

-/

section InvariantTensors

variable {k k' : complexLorentzTensor.Color}

/-- The components of `g • t` for a tensor with two indices: the matrix of `g` in the colour of
  each index acts on that index. -/
lemma basis_repr_smul_pair (g : SL(2,ℂ)) (t : ℂT[k, k']) (a : Fin (repDim k))
    (b : Fin (repDim k')) :
    (Tensor.basis ![k, k']).repr (g • t)
        ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k'] j))).symm (a, b))
      = ∑ x, ∑ y, LinearMap.toMatrix (complexLorentzTensor.basis k)
          (complexLorentzTensor.basis k) (complexLorentzTensor.rep k g) a x *
        LinearMap.toMatrix (complexLorentzTensor.basis k') (complexLorentzTensor.basis k')
          (complexLorentzTensor.rep k' g) b y *
        (Tensor.basis ![k, k']).repr t
          ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k'] j))).symm (x, y)) := by
  rw [basis_repr_smul,
    ← (piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k'] j))).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.prod_univ_two]
  rfl

/-- The components of an invariant tensor with two Weyl indices of the same colour are
  antisymmetric. The inverse boost along `z` scales the two diagonal components by `4` and `4⁻¹`,
  and the inverse half turn about `x` sends the mixed component `(0, 1)` to minus `(1, 0)`; for
  the dual colours the inverse cancels against the inverse in the matrix of the colour. -/
lemma basis_repr_pair_eq_neg_swap_of_invariant
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR) {t : ℂT[k, k]}
    (ht : ∀ g : SL(2,ℂ), g • t = t) (a b : Fin (repDim k)) :
    (Tensor.basis ![k, k]).repr t
        ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k] j))).symm (a, b))
      = - (Tensor.basis ![k, k]).repr t
        ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k] j))).symm (b, a)) := by
  have hinv : ∀ g : SL(2,ℂ), (g⁻¹).1⁻¹ = g.1 := fun g => by rw [SL2C.inverse_coe, inv_inv]
  rcases hk with rfl | rfl | rfl | rfl
  all_goals
    have h := fun (g : SL(2,ℂ)) (x y : Fin 2) => congrArg (fun s : type_of% t =>
      (Tensor.basis (S := complexLorentzTensor) _).repr s
        ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![_, _] j))).symm (x, y))) (ht g)
    have h1 := h (SL2C.boostAxis 2 2 two_ne_zero)⁻¹ 0 0
    have h2 := h (SL2C.boostAxis 2 2 two_ne_zero)⁻¹ 1 1
    have h3 := h (SL2C.halfTurn 0)⁻¹ 0 1
    rw [basis_repr_smul_pair] at h1 h2 h3
    first
      | rw [toMatrix_rep_upL] at h1 h2 h3 | rw [toMatrix_rep_downL] at h1 h2 h3
      | rw [toMatrix_rep_upR] at h1 h2 h3 | rw [toMatrix_rep_downR] at h1 h2 h3
    try simp only [hinv] at h1 h2 h3
    simp [Fin.sum_univ_two, Matrix.adjugate_fin_two, map_ofNat] at h1 h2 h3
    replace h1 := (mul_left_eq_self₀.1 h1).resolve_left (by norm_num)
    replace h2 := (mul_left_eq_self₀.1 h2).resolve_left (by norm_num)
    revert a b
    change ∀ a b : Fin 2, _
    simp only [Fin.forall_fin_two]
    exact ⟨⟨h1.trans (neg_eq_zero.2 h1).symm, h3.symm⟩, neg_eq_iff_eq_neg.1 h3,
      h2.trans (neg_eq_zero.2 h2).symm⟩

/-- The invariant tensors with two Weyl indices of the same colour are the multiples of the
  metric of that colour: both have antisymmetric components, and the `(0, 1)` component of the
  metric does not vanish. -/
lemma exists_eq_smul_metricTensor_of_invariant
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR) (t : ℂT[k, k])
    (ht : ∀ g : SL(2,ℂ), g • t = t) : ∃ a : ℂ, t = a • metricTensor k := by
  have hz : ∀ x : ℂ, x = -x → x = 0 := fun x hx => by linear_combination hx / 2
  have ht' := basis_repr_pair_eq_neg_swap_of_invariant hk ht
  have hm' := basis_repr_pair_eq_neg_swap_of_invariant hk
    (metricTensor_invariant (S := complexLorentzTensor) (c := k))
  rcases hk with rfl | rfl | rfl | rfl
  all_goals
    set e := (piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![_, _] j))).symm
    have hm : (Tensor.basis (S := complexLorentzTensor) _).repr (metricTensor _)
        (e ((0 : Fin 2), (1 : Fin 2))) ≠ 0 := by
      first
        | rw [show metricTensor Color.upL = εL from rfl, leftMetric_eq_basis]
        | rw [show metricTensor Color.downL = εL' from rfl, dualLeftMetric_eq_basis]
        | rw [show metricTensor Color.upR = εR from rfl, rightMetric_eq_basis]
        | rw [show metricTensor Color.downR = εR' from rfl, dualRightMetric_eq_basis]
      simp only [e, map_add, map_sub, map_neg, Module.Basis.repr_self, Finsupp.coe_add,
        Finsupp.coe_sub, Finsupp.coe_neg, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Finsupp.single_apply]
      split_ifs with h1 h2
      · exact absurd (congrFun h2 0 : (1 : Fin 2) = 0) (by decide)
      · norm_num
      all_goals exact absurd (by funext j; fin_cases j <;> rfl) h1
    refine ⟨(Tensor.basis (S := complexLorentzTensor) _).repr t (e ((0 : Fin 2), (1 : Fin 2)))
      / (Tensor.basis (S := complexLorentzTensor) _).repr (metricTensor _)
        (e ((0 : Fin 2), (1 : Fin 2))), ?_⟩
    apply (Tensor.basis (S := complexLorentzTensor) _).repr.injective
    ext φ
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective φ
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    revert a b
    change ∀ a b : Fin 2, _
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, by field_simp⟩, ?_, ?_⟩
    · simp only [hz _ (ht' 0 0), hz _ (hm' 0 0), mul_zero]
    · rw [ht' 1 0, hm' 1 0]
      field_simp
    · simp only [hz _ (ht' 1 1), hz _ (hm' 1 1), mul_zero]

end InvariantTensors

/-!

## C. The classification of the invariants

-/

section Reduction

variable {k : complexLorentzTensor.Color} {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[k, k] →ₗ[ℂ] B}

/-- For a Weyl colour `k` and an equivariant map `f` out of `ℂT[k, k]`, the Lorentz invariants
  of the range of `f` reduce to the span of the image `f (metricTensor k)` of the metric. -/
noncomputable def invariantReductionToMetricTensor
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR)
    (hf : complexLorentzTensor.IsEquivariant ![k, k] repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (complexLorentzTensor.isAdjointClosed _)
    (metricTensor k) (fun g => metricTensor_invariant g)
    (exists_eq_smul_metricTensor_of_invariant hk)

/-- For a Weyl colour `k` and an equivariant map `f` out of `ℂT[k, k]`, every Lorentz invariant
  of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a multiple of the image
  `f (metricTensor k)` of the metric plus an element of `S`. -/
lemma exists_smul_map_metricTensor_add_of_invariant
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR)
    (hf : complexLorentzTensor.IsEquivariant ![k, k] repLorentz f) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f (metricTensor k) + y :=
  (invariantReductionToMetricTensor hk hf).reduce S hS x hx hinv

end Reduction

/-- The Lorentz invariants of the range of a family with two left-handed Weyl indices reduce to
  the span of the image of `εL`. -/
noncomputable def IsBiLeftWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.upL, .upL] →ₗ[ℂ] B}
    (hf : IsBiLeftWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inl rfl) hf

/-- The Lorentz invariants of the range of a family with two right-handed Weyl indices reduce to
  the span of the image of `εR`. -/
noncomputable def IsBiRightWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.upR, .upR] →ₗ[ℂ] B}
    (hf : IsBiRightWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inr (Or.inl rfl))) hf

/-- The Lorentz invariants of the range of a family with two dual left-handed Weyl indices
  reduce to the span of the image of `εL'`. -/
noncomputable def IsBiDualLeftWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.downL, .downL] →ₗ[ℂ] B}
    (hf : IsBiDualLeftWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inl rfl)) hf

/-- The Lorentz invariants of the range of a family with two dual right-handed Weyl indices
  reduce to the span of the image of `εR'`. -/
noncomputable def IsBiDualRightWeyl.invariantReductionToSpan {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT[.downR, .downR] →ₗ[ℂ] B}
    (hf : IsBiDualRightWeyl B repLorentz f) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) :=
  invariantReductionToMetricTensor (Or.inr (Or.inr (Or.inr rfl))) hf

/-!

## D. Maps from components

A family of vectors `T a b` indexed by two basis indices is the linear map
`ofPairComponents T` sending `e_a ⊗ e_b` to `T a b`, and it is equivariant when the vectors are
moved as the basis tensors are.

-/

section PairComponents

variable {k k' : complexLorentzTensor.Color} {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The linear map out of `ℂT[k, k']` sending the basis tensor `e_a ⊗ e_b` to `T a b`. -/
noncomputable def ofPairComponents (T : Fin (repDim k) → Fin (repDim k') → B) :
    ℂT[k, k'] →ₗ[ℂ] B :=
  (Tensor.basis ![k, k']).constr ℂ fun φ => T (φ 0) (φ 1)

/-- The range of `ofPairComponents T` is the span of the vectors `T a b`. -/
lemma range_ofPairComponents (T : Fin (repDim k) → Fin (repDim k') → B) :
    LinearMap.range (ofPairComponents T)
      = Submodule.span ℂ (Set.range fun m : Fin (repDim k) × Fin (repDim k') => T m.1 m.2) := by
  rw [ofPairComponents, Module.Basis.constr_range]
  exact congrArg _ ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k'] j))).surjective.range_comp
    fun m => T m.1 m.2)

/-- The image of `ofPairComponents T` lies in every submodule containing the vectors
  `T a b`. -/
lemma ofPairComponents_mem (T : Fin (repDim k) → Fin (repDim k') → B) {M : Submodule ℂ B}
    (hT : ∀ a b, T a b ∈ M) (t : ℂT[k, k']) : ofPairComponents T t ∈ M := by
  have h : LinearMap.range (ofPairComponents T) ≤ M := by
    rw [range_ofPairComponents, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hT m.1 m.2
  exact h (LinearMap.mem_range_self _ t)

/-- A linear map applied after `ofPairComponents T` is `ofPairComponents` of its values on the
  components. -/
lemma map_ofPairComponents {B' : Type*} [AddCommGroup B'] [Module ℂ B'] (σ : B →ₗ[ℂ] B')
    (T : Fin (repDim k) → Fin (repDim k') → B) (t : ℂT[k, k']) :
    σ (ofPairComponents T t) = ofPairComponents (fun a b => σ (T a b)) t :=
  LinearMap.congr_fun (show σ ∘ₗ ofPairComponents T = ofPairComponents (fun a b => σ (T a b)) from
    (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by
      simp [ofPairComponents]) t

/-- `ofPairComponents` of a sum of families is the sum of the maps. -/
lemma ofPairComponents_sum {ι : Type*} (s : Finset ι)
    (T : ι → Fin (repDim k) → Fin (repDim k') → B) :
    ofPairComponents (fun a b => ∑ i ∈ s, T i a b) = ∑ i ∈ s, ofPairComponents (T i) :=
  (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by
    simp [ofPairComponents, LinearMap.sum_apply]

/-- `ofPairComponents` of a difference of families is the difference of the maps. -/
lemma ofPairComponents_sub (T T' : Fin (repDim k) → Fin (repDim k') → B) :
    ofPairComponents (fun a b => T a b - T' a b) = ofPairComponents T - ofPairComponents T' :=
  (Tensor.basis (S := complexLorentzTensor) ![k, k']).ext fun φ => by simp [ofPairComponents]

/-- `ofPairComponents T` is equivariant when each index of `T a b` is moved by the matrix of `g`
  in its colour, the summed index first in each factor. -/
lemma isEquivariant_ofPairComponents {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : Fin (repDim k) → Fin (repDim k') → B)
    (hT : ∀ (g : SL(2,ℂ)) a b, repLorentz g (T a b)
      = ∑ x, ∑ y, (LinearMap.toMatrix (complexLorentzTensor.basis k)
          (complexLorentzTensor.basis k) (complexLorentzTensor.rep k g) x a *
        LinearMap.toMatrix (complexLorentzTensor.basis k') (complexLorentzTensor.basis k')
          (complexLorentzTensor.rep k' g) y b) • T x y) :
    complexLorentzTensor.IsEquivariant ![k, k'] repLorentz (ofPairComponents T) :=
  isEquivariant_constr _ fun g φ => (hT g (φ 0) (φ 1)).trans <| by
    rw [← (piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![k, k'] j))).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.prod_univ_two]
    rfl

end PairComponents

end Lorentz
