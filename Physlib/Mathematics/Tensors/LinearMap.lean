/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.CoordTensorHom
public import Mathlib.RepresentationTheory.Invariants
public import Physlib.Mathematics.Tensors.Contraction
/-!

# Tensors of two factors as linear maps

A tensor in `V a ⊗ U` is read as a linear map `V a.dual → U`. The delta is the identity map, and
contracting an index with a tensor of two factors applies its linear map.

## i. Overview

A tensor `z` in `V a ⊗ U`, for a color `a` of a species `S` and any module `U`, is read as the
linear map `S.toLin z : V a.dual → U` that contracts its input with the first factor of `z`. On a
pure tensor `z = x ⊗ y` it is `v ↦ (v^μ x_μ) y`. Every linear map `V a.dual → U` is `toLin z` for
exactly one `z`. `toLin` is `Module.Basis.coordTensorHomEquiv` for the bases of `a` and `a.dual`,
which is Mathlib's `dualTensorHomEquivOfBasis` once the contraction identifies `V a` with the dual
of `V a.dual`. The results that need only the bases, such as the matrix of `toLin z`, are stated
there.

This is how two-index tensors act as maps. A metric `g_μν` is the map `v^μ ↦ v^μ g_μν`, and the
inverse metric `g^μν` is the tensor of the inverse map. The map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`, so `z` is
invariant exactly when its linear map commutes with the group action. This is Mathlib's
`Representation.mem_linHom_invariants_iff_isIntertwining`, read through `toLin`.

The delta `S.delta c = ∑ μ, e^μ ⊗ e_μ` is the tensor of the identity map, `u^μ δ_μ^ν = u^ν`. The
identity commutes with every group element, so the delta is invariant. `S.deltaTensor c` is the
delta as a tensor on two slots, and its components form the identity matrix.

Contracting the inner indices of two tensors on two slots, `M^μ_ν N^ν_ρ`, applies the linear map
of `N` to the second factor of `M`, and the result is the delta exactly when the two linear maps
are inverse. More generally, contracting an index of any tensor with the first index of a tensor
`F` on two slots applies the linear map of `F` at that index, and for the delta this is the
identity.

## ii. Key results

- `Species.toLin` : `V a ⊗ U` as the linear maps `V a.dual → U`, with `Species.toLin_map_rep` :
  the linear map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`, and `Species.isIntertwiningMap_toLin_iff` : `z` is
  invariant exactly when its linear map commutes with the group action.
- `Species.delta` : the delta `δ_μ^ν`, with `Species.delta_invariant` : it is invariant.
- `Species.deltaTensor` : the delta as a tensor on two slots, with
  `Species.tensorBasis_repr_deltaTensor_eq_one` : its components form the identity matrix.
- `Species.Tensor.contr_matMul` : the contraction `M^μ_ν N^ν_ρ`, and
  `Species.Tensor.contr_matMul_eq_deltaTensor_iff` : it is the delta exactly when the linear maps
  of `M` and `N` are inverse.
- `Species.Tensor.contr_matMulAt` : contracting the index `i` with the first index of `F` applies
  `F` at `i`, and `Species.Tensor.contr_deltaTensor` : for the delta this is
  `T^…μ… δ_μ^ν = T^…ν…`.

## iii. Table of contents

- A. Tensors of two factors as linear maps
- B. The delta
- C. Products with a tensor on two slots

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K basisIdx)

/-!

## A. Tensors of two factors as linear maps

-/

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`. For a lower color `a` and `z = g` in `V a ⊗ V a` it is `v^μ ↦ v^μ g_μν`.
Every linear map arises so. -/
noncomputable abbrev toLin {a : Color K} {U : Type} [AddCommGroup U] [Module k U] :
    S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  (S.basis a).coordTensorHomEquiv (S.basis a.dual)

/-- The coordinate pairing of the bases of `c` and `c.dual` is the contraction. -/
@[simp]
lemma coordPairing_basis (c : Color K) {x : S.V c} {y : S.V c.dual} :
    (S.basis c).coordPairing (S.basis c.dual) (x ⊗ₜ y) = S.contr c (x ⊗ₜ y) :=
  rfl

/-- The coordinate pairing of the bases of `c.dual` and `c` is the contraction at `c.dual`. -/
@[simp]
lemma coordPairing_basis_dual (c : Color K) {x : S.V c.dual} {y : S.V c} :
    (S.basis c.dual).coordPairing (S.basis c) (x ⊗ₜ y) = S.contr c.dual (x ⊗ₜ y) :=
  rfl

/-- The linear map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`. -/
lemma toLin_map_rep {a b : Color K} (z : S.V a ⊗[k] S.V b) (g : G) :
    S.toLin (TensorProduct.map (S.rep a g) (S.rep b g) z) =
      S.rep b g ∘ₗ S.toLin z ∘ₗ S.rep a.dual g⁻¹ :=
  LinearMap.ext fun x => by
    induction z using TensorProduct.inductionOn with
    | tmul w y =>
      simpa using congrArg (· • S.rep b g y) (S.contr_invariant a.dual g (S.rep a.dual g⁻¹ x) w)
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', LinearMap.comp_apply]

/-- The linear map of `Λz` is bijective when that of `z` is. -/
lemma toLin_map_rep_bijective {a b : Color K} (z : S.V a ⊗[k] S.V b)
    (h : Function.Bijective (S.toLin z)) (g : G) :
    Function.Bijective (S.toLin (TensorProduct.map (S.rep a g) (S.rep b g) z)) := by
  rw [toLin_map_rep, LinearMap.coe_comp, LinearMap.coe_comp]
  exact ((S.rep b).apply_bijective g).comp (h.comp ((S.rep a.dual).apply_bijective g⁻¹))

/-- A tensor is invariant exactly when its linear map commutes with the group action. -/
lemma isIntertwiningMap_toLin_iff {a b : Color K} (z : S.V a ⊗[k] S.V b) :
    (S.rep a.dual).IsIntertwiningMap (S.rep b) (S.toLin z) ↔
      ∀ g, TensorProduct.map (S.rep a g) (S.rep b g) z = z := by
  rw [← Representation.mem_linHom_invariants_iff_isIntertwining]
  exact forall_congr' fun g => by rw [← toLin_map_rep, S.toLin.injective.eq_iff]

/-!

## B. The delta

-/

/-- The Kronecker delta `∑ μ, e^μ ⊗ e_μ ∈ V c.dual ⊗ V c`, with components `δ_μ^ν`. The factor of
the dual color is first. -/
noncomputable abbrev delta (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  (S.basis c.dual).coordDelta (S.basis c)

/-- The delta is invariant, `Λ δ = δ`, with `Λ` acting on both factors. -/
lemma delta_invariant (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c := by
  -- The linear map of the delta is the identity, which commutes with the action.
  refine (S.isIntertwiningMap_toLin_iff (S.delta c)).1 ?_ g
  rw [Module.Basis.coordTensorHomEquiv_coordDelta]
  exact ⟨fun _ _ => rfl⟩

variable {S}

variable (S) in
/-- The delta `S.delta c` as a tensor with colors `![c.dual, c]`. It is `δ_μ^ν` for an upper
color `c` and `δ^μ_ν` for a lower one. -/
noncomputable def deltaTensor (c : Color K) : S.Tensor ![c.dual, c] :=
  S.twoIndexEquiv c.dual c (S.delta c)

/-- The delta tensor is invariant, `Λ δ = δ`. -/
lemma deltaTensor_invariant (c : Color K) (Λ : G) : Λ • S.deltaTensor c = S.deltaTensor c :=
  (S.twoIndexEquiv _ c).toIntertwiningMap.map_invariant (S.delta_invariant c Λ)

/-- The components of the delta tensor are the coordinates of `S.delta c` in Mathlib's product
basis, at the pair of labels `(μ 0, μ 1)`. -/
lemma tensorBasis_repr_deltaTensor (c : Color K) (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      ((S.basis c.dual).tensorProduct (S.basis c)).repr (S.delta c) (μ 0, μ 1) :=
  tensorBasis_repr_twoIndexEquiv _ _ _ μ

/-- The components of the delta tensor form the identity matrix, `δ_μ^ν = 1` for `μ = ν` and `0`
otherwise. -/
lemma tensorBasis_repr_deltaTensor_eq_one (c : Color K)
    (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      (1 : Matrix (basisIdx c.kind) (basisIdx c.kind) k) (μ 0) (μ 1) :=
  (tensorBasis_repr_deltaTensor c μ).trans
    ((Module.Basis.tensorProduct_repr_coordDelta _ _ _ _).trans Matrix.one_apply.symm)

namespace Tensor

open TensorProduct PiTensorProduct

variable {ι₁ κ : Type} {c : ι₁ → Color K} {c' : κ → Color K}

/-!

## C. Products with a tensor on two slots

-/

/-- The relabeling of the product `M^μ_ν N^ν_ρ` of two tensors on two slots that contracts the
second index of `M`, of color `c`, with the first index of `N`. The free indices `μ` and `ρ` are
`0` and `1`. -/
def _root_.Tensor.ColorEquiv.matMul (a c b : Color K) :
    ColorEquiv (prodColors ![a, c] ![c.dual, b]) (contrColors ![a, b] fun _ : Unit => c) where
  toEquiv.toFun
    | .inl 0 => .inl 0 | .inl 1 => .inr (.inl ()) | .inr 0 => .inr (.inr ()) | .inr 1 => .inl 1
  toEquiv.invFun
    | .inl 0 => .inl 0 | .inl 1 => .inr 1 | .inr (.inl ()) => .inl 1 | .inr (.inr ()) => .inr 0
  toEquiv.left_inv := by decide
  toEquiv.right_inv := by decide

/-- The contraction `M^μ_ν N^ν_ρ` of two tensors on two slots is `M` with its second factor mapped
by `S.toLin N`, the linear map `v_ν ↦ v_ν N^ν_ρ`. -/
lemma contr_matMul (a c b : Color K) (M : S.V a ⊗[k] S.V c) (N : S.V c.dual ⊗[k] S.V b) :
    contr (ColorEquiv.matMul a c b)
        (S.tmulEquiv _ _ (S.twoIndexEquiv a c M ⊗ₜ S.twoIndexEquiv _ b N)) =
      S.twoIndexEquiv a b ((S.toLin N).lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, add_tmul, hM, hM']
  | tmul m₁ m₂ =>
  induction N using TensorProduct.inductionOn with
  | add N N' hN hN' =>
    simp only [map_add, tmul_add, LinearMap.lTensor_add, LinearMap.add_apply, hN, hN']
  | tmul n₁ n₂ =>
    simp only [twoIndexEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique,
      LinearMap.lTensor_tmul, Module.Basis.coordTensorHomEquiv_tmul, coordPairing_basis, tmul_smul,
      map_smul]
    congr 2
    funext j
    fin_cases j <;> rfl

/-- Two tensors on two slots contract to the delta, `X_μν Y^νρ = δ_μ^ρ`, exactly when their linear
maps compose to the identity, `Y ∘ X = id`. -/
lemma contr_matMul_eq_deltaTensor_iff {x y : Color K} (X : S.V x ⊗[k] S.V y)
    (Y : S.V y.dual ⊗[k] S.V x.dual) :
    contr (ColorEquiv.matMul x y x.dual)
        (S.tmulEquiv _ _ (S.twoIndexEquiv x y X ⊗ₜ S.twoIndexEquiv _ _ Y)) = S.deltaTensor x.dual ↔
      S.toLin Y ∘ₗ S.toLin X = LinearMap.id := by
  rw [deltaTensor, contr_matMul, (EquivLike.injective (S.twoIndexEquiv _ _)).eq_iff,
    ← (S.toLin (a := x)).injective.eq_iff, Module.Basis.coordTensorHomEquiv_lTensor,
    Module.Basis.coordTensorHomEquiv_coordDelta]

/-- The relabeling of `T^…μ… F_μ^ν`, which contracts the slot `i` of `T` with the first slot of a
tensor `F` on two slots and puts the second slot of `F` in the place of `i`. It is
`ColorEquiv.matMul` at any slot of a tensor on any slots. -/
def _root_.Tensor.ColorEquiv.matMulAt [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁)
    (a b : Color K) (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) :
    ColorEquiv (prodColors c ![a.dual, b]) (contrColors c' fun _ : Unit => a) where
  toEquiv :=
    { toFun := Sum.elim (fun x => if x = i then .inr (.inl ()) else .inl x)
        (fun j => if j = 0 then .inr (.inr ()) else .inl i)
      invFun := Sum.elim (fun x => if x = i then .inr 1 else .inl x)
        (Sum.elim (fun _ => .inl i) fun _ => .inr 0)
      left_inv := by
        rintro (x | j)
        · by_cases hx : x = i <;> simp [hx]
        · fin_cases j <;> simp
      right_inv := by
        rintro (x | (⟨⟩ | ⟨⟩))
        · by_cases hx : x = i <;> simp [hx]
        · simp
        · simp }
  color_eq := by
    rintro (x | (⟨⟩ | ⟨⟩))
    · by_cases hx : x = i
      · subst hx
        simp [hi]
      · simp [hx, h x hx]
    · simp [ha]
    · simp

/-- On a pure tensor, contracting the slot `i` with the first slot of `F` applies `F`, read as a
linear map by `Species.toLin`, to the vector at `i`. The vectors `q` at the other slots are
those of `p`, moved along `h`. -/
lemma contr_matMulAt_pure [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁) (a b : Color K)
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) (F : S.V a.dual ⊗[k] S.V b)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (S.pure p ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.pure (Function.update q i (S.cast hi.symm (S.toLin F (S.cast ha (p i))))) := by
  induction F using TensorProduct.inductionOn with
  | add F F' hF hF' =>
    simp only [map_add, LinearMap.add_apply, tmul_add, hF, hF']
    rw [pure, pure, pure, MultilinearMap.map_update_add, map_add]
  | tmul x y =>
    rw [Module.Basis.coordTensorHomEquiv_tmul, coordPairing_basis, map_smul]
    conv_rhs => rw [pure, MultilinearMap.map_update_smul, map_smul, ← pure]
    rw [twoIndexEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique]
    congr 2
    funext z
    by_cases hz : z = i
    · subst hz
      rw [Function.update_self, cast_apply_congr _ (show
        (ColorEquiv.matMulAt z a b ha hi h).toEquiv.symm (.inl z) = .inr 1 by
          simp [ColorEquiv.matMulAt])]
      rfl
    · rw [Function.update_of_ne hz, cast_apply_congr _ (show
        (ColorEquiv.matMulAt i a b ha hi h).toEquiv.symm (.inl z) = .inl z by
          simp [ColorEquiv.matMulAt, hz]), hq z hz]

/-- Contracting the index `i` of `t` with the first index of a tensor `F` on two slots applies `F`,
read as a linear map by `Species.toLin`, at `i`, as in `T^…μ… F_μ^ν`. -/
lemma contr_matMulAt [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁) (a b : Color K)
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) (F : S.V a.dual ⊗[k] S.V b)
    (t : S.Tensor c) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (t ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.mapAt i ((S.cast hi.symm).toLinearMap ∘ₗ S.toLin F ∘ₗ (S.cast ha).toLinearMap) h t := by
  refine LinearMap.congr_fun (f := (contr _).toLinearMap ∘ₗ (S.tmulEquiv c ![a.dual, b]).toLinearMap
    ∘ₗ (TensorProduct.mk k _ _).flip (S.twoIndexEquiv a.dual b F)) (ext_pure fun p => ?_) t
  -- The vectors of `p` moved along `h` away from `i`. The vector at `i` is replaced below.
  let q : Π x, S.V (c' x) := fun x => if hx : x = i then 0 else S.cast (h x hx) (p x)
  exact (contr_matMulAt_pure i a b ha hi h F p q (fun x hx => by simp [q, hx])).trans
    (mapAt_pure i _ h p (Function.update q i (S.cast hi.symm (S.toLin F (S.cast ha (p i)))))
      (Function.update_self _ _ _) (fun x hx => by simp [q, hx])).symm

/-- Contracting the index `i` with the first index of the delta is the identity,
`T^…μ… δ_μ^ν = T^…ν…`. -/
lemma contr_deltaTensor [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K) (ha : c i = a)
    (t : S.Tensor c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a] (t ⊗ₜ S.deltaTensor a)) = t := by
  subst ha
  rw [deltaTensor, contr_matMulAt, Module.Basis.coordTensorHomEquiv_coordDelta]
  exact LinearMap.congr_fun (mapAt_id i _) t

/-- Contracting the index `i` with the second index of the delta is the identity,
`δ^ν_μ T^…μ… = T^…ν…`. -/
lemma contr_deltaTensor_swap [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K)
    (ha : c i = a) (t : S.Tensor c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a]
        (t ⊗ₜ S.reindex (ColorEquiv.swapTwo a a.dual) (S.deltaTensor a.dual))) = t := by
  rw [deltaTensor, reindex_twoIndexEquiv, show TensorProduct.comm k _ _ (S.delta a.dual) = S.delta a
    from Module.Basis.comm_coordDelta _ _]
  exact contr_deltaTensor i a ha t

end Tensor

end Species

end Tensor
