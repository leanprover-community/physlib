/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Color.Discrete
import PhysLean.Relativity.Tensors.Color.Lift
/-!

# Tensor species

- A tensor species is a structure including all of the ingredients needed to define a type of
  tensor.
- Examples of tensor species will include real Lorentz tensors, complex Lorentz tensors, and
  Einstein tensors.
- Tensor species are built upon symmetric monoidal categories.

-/

open IndexNotation CategoryTheory Module MonoidalCategory

/-- The structure `TensorSpecies` contains the necessary structure needed to define
  a system of tensors with index notation. Examples of `TensorSpecies` include real Lorentz tensors,
  complex Lorentz tensors, and ordinary Euclidean tensors. -/
structure TensorSpecies (k : Type) [CommRing k] (C : Type) (G : Type) [Group G] where
  /-- A functor from `C` to `Rep k G` giving our building block representations.
    Equivalently a function `C → Re k G`. -/
  FD : Discrete C ⥤ Rep k G
  /-- A specification of the dimension of each color in C. This will be used for explicit
    evaluation of tensors. -/
  repDim : C → ℕ
  /-- repDim is not zero for any color. This allows casting of `ℕ` to `Fin (S.repDim c)`. -/
  repDim_neZero (c : C) : NeZero (repDim c)
  /-- A basis for each Module, determined by the evaluation map. -/
  basis : (c : C) → Basis (Fin (repDim c)) k (FD.obj (Discrete.mk c)).V
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  /-- The condition that `τ` is an involution. -/
  τ_involution : Function.Involutive τ
  /-- The natural transformation describing contraction. -/
  contr : OverColor.Discrete.pairτ FD τ ⟶ 𝟙_ (Discrete C ⥤ Rep k G)
  /-- Contraction is symmetric with respect to duals. -/
  contr_tmul_symm (c : C) (x : FD.obj (Discrete.mk c))
      (y : FD.obj (Discrete.mk (τ c))) :
    (contr.app (Discrete.mk c)).hom (x ⊗ₜ[k] y) = (contr.app (Discrete.mk (τ c))).hom
    (y ⊗ₜ (FD.map (Discrete.eqToHom (τ_involution c).symm)).hom x)
  /-- The natural transformation describing the unit. -/
  unit : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.τPair FD τ
  /-- The unit is symmetric.
    The de-categorification of this lemma is: `unitTensor_eq_permT_dual`. -/
  unit_symm (c : C) :
    ((unit.app (Discrete.mk c)).hom (1 : k)) =
    ((FD.obj (Discrete.mk (τ (c)))) ◁
      (FD.map (Discrete.eqToHom (τ_involution c)))).hom
    ((β_ (FD.obj (Discrete.mk (τ (τ c)))) (FD.obj (Discrete.mk (τ (c))))).hom.hom
    ((unit.app (Discrete.mk (τ c))).hom (1 : k)))
  /-- Contraction with unit leaves invariant.
    The de-categorification of this lemma is: `contrT_single_unitTensor`. -/
  contr_unit (c : C) (x : FD.obj (Discrete.mk (c))) :
    (λ_ (FD.obj (Discrete.mk (c)))).hom.hom
    (((contr.app (Discrete.mk c)) ▷ (FD.obj (Discrete.mk (c)))).hom
    ((α_ _ _ (FD.obj (Discrete.mk (c)))).inv.hom
    (x ⊗ₜ[k] (unit.app (Discrete.mk c)).hom (1 : k)))) = x
  /-- The natural transformation describing the metric. -/
  metric : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.pair FD
  /-- On contracting metrics we get back the unit.
    The de-categorification of this lemma is: `contrT_metricTensor_metricTensor`. -/
  contr_metric (c : C) :
    (β_ (FD.obj (Discrete.mk c)) (FD.obj (Discrete.mk (τ c)))).hom.hom
    (((FD.obj (Discrete.mk c)) ◁ (λ_ (FD.obj (Discrete.mk (τ c)))).hom).hom
    (((FD.obj (Discrete.mk c)) ◁ ((contr.app (Discrete.mk c)) ▷
    (FD.obj (Discrete.mk (τ c))))).hom
    (((FD.obj (Discrete.mk c)) ◁ (α_ (FD.obj (Discrete.mk (c)))
      (FD.obj (Discrete.mk (τ c))) (FD.obj (Discrete.mk (τ c)))).inv).hom
    ((α_ (FD.obj (Discrete.mk (c))) (FD.obj (Discrete.mk (c)))
      (FD.obj (Discrete.mk (τ c)) ⊗ FD.obj (Discrete.mk (τ c)))).hom.hom
    ((metric.app (Discrete.mk c)).hom (1 : k) ⊗ₜ[k]
      (metric.app (Discrete.mk (τ c))).hom (1 : k))))))
    = (unit.app (Discrete.mk c)).hom (1 : k)

noncomputable section

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C : Type} [Group G] (S : TensorSpecies k C G)

/-- The field `repDim` of a `TensorSpecies` is non-zero for all colors. -/
instance (c : C) : NeZero (S.repDim c) := S.repDim_neZero c

@[simp]
lemma τ_τ_apply (c : C) : S.τ (S.τ c) = c := S.τ_involution c

lemma basis_congr {c c1 : C} (h : c = c1) (i : Fin (S.repDim c)) :
    S.basis c i = S.FD.map (eqToHom (by simp [h])) (S.basis c1 (Fin.cast (by simp [h]) i)) := by
  subst h
  simp

lemma basis_congr_repr {c c1 : C} (h : c = c1) (i : Fin (S.repDim c))
    (t : S.FD.obj (Discrete.mk c)) :
    (S.basis c).repr t i = (S.basis c1).repr (S.FD.map (eqToHom (by simp [h])) t)
    (Fin.cast (by simp [h]) i) := by
  subst h
  simp

lemma FD_map_basis {c c1 : C} (h : c = c1) (i : Fin (S.repDim c)) :
    (S.FD.map (Discrete.eqToHom h)).hom.hom (S.basis c i)
    = S.basis c1 (Fin.cast (by simp [h]) i) := by
  subst h
  simp

/-- The lift of the functor `S.F` to functor. -/
def F : Functor (OverColor C) (Rep k G) := ((OverColor.lift).obj S.FD).toFunctor

/- The definition of `F` as a lemma. -/
lemma F_def : F S = ((OverColor.lift).obj S.FD).toFunctor := rfl

/-- The functor `F` is monoidal. -/
instance F_monoidal : Functor.Monoidal S.F :=
  lift.instMonoidalRepObjFunctorDiscreteLaxBraidedFunctor S.FD

/-- The functor `F` is lax-braided. -/
instance F_laxBraided : Functor.LaxBraided S.F :=
  lift.instLaxBraidedRepObjFunctorDiscreteLaxBraidedFunctor S.FD

/-- The functor `F` is braided. -/
instance F_braided : Functor.Braided S.F := Functor.Braided.mk
  (fun X Y => Functor.LaxBraided.braided X Y)

set_option linter.unusedVariables false in
/-- Casts an element of the monoidal unit of `Rep k G` to the field `k`. -/
@[nolint unusedArguments]
def castToField {S : TensorSpecies k C G}
    (v : (↑((𝟙_ (Discrete C ⥤ Rep k G)).obj { as := c }).V)) : k := v

lemma castToField_eq_self {S : TensorSpecies k C G} {c}
    (v : (↑((𝟙_ (Discrete C ⥤ Rep k G)).obj { as := c }).V)) :
    S.castToField v = v := rfl

/-- Casts an element of `(S.F.obj (OverColor.mk c)).V` for `c` a map from `Fin 0` to an
  element of the field. -/
def castFin0ToField {c : Fin 0 → C} : (S.F.obj (OverColor.mk c)).V →ₗ[k] k :=
  (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap

lemma castFin0ToField_tprod {c : Fin 0 → C}
    (x : (i : Fin 0) → S.FD.obj (Discrete.mk (c i))) :
    castFin0ToField S (PiTensorProduct.tprod k x) = 1 := by
  simp only [castFin0ToField, mk_hom, LinearEquiv.coe_coe]
  erw [PiTensorProduct.isEmptyEquiv_apply_tprod]

/-!

## Some properties of contractions

-/

lemma contr_congr (c c' : C) (h : c = c') (x : S.FD.obj (Discrete.mk c))
    (y : S.FD.obj (Discrete.mk (S.τ c))) :
    (S.contr.app { as := c }).hom (x ⊗ₜ[k] y) =
    (S.contr.app { as := c' }).hom
    ((S.FD.map (Discrete.eqToHom (by simp [h]))).hom x ⊗ₜ
    (S.FD.map (Discrete.eqToHom (by simp [h]))).hom y) := by
  subst h
  simp

/-- The number of indices `n` from a tensor. -/
@[nolint unusedArguments]
def numIndices {S : TensorSpecies k C G} {n : ℕ} {c : Fin n → C}
    (_ : S.F.obj (OverColor.mk c)) : ℕ := n

end TensorSpecies

end
