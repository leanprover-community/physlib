/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Color.Basic
import Mathlib.RepresentationTheory.Rep
import PhysLean.Mathematics.PiTensorProduct
import Mathlib.Algebra.Lie.OfAssociative
import PhysLean.Meta.Informal.Basic
/-!

## Lifting functors.

There is a functor from functors `Discrete C ⥤ Rep k G` to
braided monoidal functors `BraidedFunctor (OverColor C) (Rep k G)`.
We call this functor `lift`. It is a lift in the
sense that it is a section of the forgetful functor
`BraidedFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G)`.

Functors in `Discrete C ⥤ Rep k G` form the basic building blocks of tensor structures.
The fact that they extend to monoidal functors `OverColor C ⥤ Rep k G` allows us to
interact more generally with tensors.

-/

namespace IndexNotation
namespace OverColor

open CategoryTheory
open MonoidalCategory
variable {C k : Type} [CommRing k] {G : Type} [Group G]

namespace Discrete

/-- Takes a homomorphism in `Discrete C` to an isomorphism built on the same objects. -/
def homToIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) : c1 ≅ c2 :=
  Discrete.eqToIso (Discrete.eq_of_hom h)

end Discrete

namespace lift
noncomputable section
variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

section toRep
/-!

## To representation

Given an object in `OverColor C` and a functor `F : Discrete C ⥤ Rep k G`,
we get an object of `Rep k G` by taking the tensor product of the representations.

-/

variable (F : Discrete C ⥤ Rep k G)

/-- Given an object `f : OverColor C` and a function `F : Discrete C ⥤ Rep k G`, the object
  in `Rep k G` obtained by taking the tensor product of all colors in `f`. -/
def toRep (f : OverColor C) : Rep k G := Rep.of {
  toFun := fun M => PiTensorProduct.map (ι := f.left) (fun x =>
    (F.obj (Discrete.mk (f.hom x))).ρ M),
  map_one' := by
    simp only [map_one, PiTensorProduct.map_one]
  map_mul' := fun M N => by
    simp only [map_mul]
    ext x : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, Module.End.mul_apply]}

lemma toRep_ρ (f : OverColor C) (M : G) : (toRep F f).ρ M =
    PiTensorProduct.map (fun x => (F.obj (Discrete.mk (f.hom x))).ρ M) := rfl

lemma toRep_ρ_tprod (f : OverColor C) (M : G) (x : (i : f.left) → F.obj (Discrete.mk (f.hom i))) :
    (toRep F f).ρ M (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k fun i => (F.obj (Discrete.mk (f.hom i))).ρ M (x i) := by
  rw [toRep_ρ]
  change (PiTensorProduct.map fun x => _) ((PiTensorProduct.tprod k) x) =_
  rw [PiTensorProduct.map_tprod]
  rfl

lemma toRep_ρ_empty (g : G) : (toRep F (𝟙_ (OverColor C))).ρ g = LinearMap.id := by
  rw [toRep_ρ]
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
    simp_all
  simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
    PiTensorProduct.map_tprod, LinearMap.id_coe, id_eq]
  apply congrArg
  apply congrArg
  funext i
  exact Empty.elim i

lemma toRep_ρ_from_fin0 (c : Fin 0 → C) (g : G) :
    (toRep F (OverColor.mk c)).ρ g = LinearMap.id := by
  rw [toRep_ρ]
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
    simp_all
  simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
    _root_.map_smul, PiTensorProduct.map_tprod, LinearMap.id_coe, id_eq]
  apply congrArg
  apply congrArg
  funext i
  simp only [mk_left] at i
  exact Fin.elim0 i

open TensorProduct in

lemma toRep_V_carrier (f : OverColor C) :
    (toRep F f).V = ⨂[k] (i : f.left), F.obj (Discrete.mk (f.hom i)) := rfl

end toRep

section homToRepHom
/-!

## Hom to representation hom

Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
we get an morphism in `Rep k G` between `toRep F f` and `toRep F g` by taking the
tensor product.

-/

/-- For a function `F : Discrete C ⥤ Rep k G`, the linear equivalence
  `(F.obj c1).V ≃ₗ[k] (F.obj c2).V` induced by an equality of `c1` and `c2`. -/
def linearIsoOfEq {c1 c2 : Discrete C} (h : c1.as = c2.as) :
    (F.obj c1).V ≃ₗ[k] (F.obj c2).V := LinearEquiv.ofLinear
  (F.mapIso (Discrete.eqToIso h)).hom.hom.hom (F.mapIso (Discrete.eqToIso h)).inv.hom.hom
  (by rw [← ModuleCat.hom_id, ← ModuleCat.hom_comp, Action.inv_hom_hom])
  (by rw [← ModuleCat.hom_id, ← ModuleCat.hom_comp, Action.hom_inv_hom])

lemma linearIsoOfEq_comm_ρ {c1 c2 : Discrete C} (h : c1.as = c2.as) (M : G)
    (x : F.obj c1) : linearIsoOfEq F h ((F.obj c1).ρ M x) =
    (F.obj c2).ρ M (linearIsoOfEq F h x) := by
  have h1 := Discrete.ext_iff.mpr h
  subst h1
  simp only [linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
    Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  rfl

/-- Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
  the linear equivalence `(toRep F f).V ≃ₗ[k] (toRep F g).V` formed by reindexing. -/
def linearIsoOfHom {f g : OverColor C} (m : f ⟶ g) : (toRep F f).V ≃ₗ[k] (toRep F g).V :=
  (PiTensorProduct.reindex k (fun x => (F.obj (Discrete.mk (f.hom x))))
    (OverColor.Hom.toEquiv m)).trans
  (PiTensorProduct.congr (fun i =>
    linearIsoOfEq F (Hom.toEquiv_symm_apply m i)))

lemma linearIsoOfHom_tprod {f g : OverColor C} (m : f ⟶ g)
    (x : (i : f.left) → (F.obj (Discrete.mk (f.hom i)))) :
    linearIsoOfHom F m (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k (fun i => (linearIsoOfEq F (Hom.toEquiv_symm_apply m i))
    (x ((OverColor.Hom.toEquiv m).symm i))) := by
  rw [linearIsoOfHom]
  simp only [CategoryTheory.Functor.id_obj, LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => _) ((PiTensorProduct.reindex k
    (fun x => ↑(F.obj (Discrete.mk (f.hom x))).V) (OverColor.Hom.toEquiv m))
    ((PiTensorProduct.tprod k) x)) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]
  rfl

/-- Given a morphism in `OverColor C`, `m : f ⟶ g` and a functor `F : Discrete C ⥤ Rep k G`,
  the morphism `(toRep F f) ⟶ (toRep F g)` formed by reindexing. -/
def homToRepHom {f g : OverColor C} (m : f ⟶ g) : toRep F f ⟶ toRep F g where
  hom := ModuleCat.ofHom (linearIsoOfHom F m).toLinearMap
  comm M := by
    ext x : 2
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [map_add, hx, hy])
    intro r x
    simp only [ModuleCat.hom_comp, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
    apply congrArg
    change (linearIsoOfHom F m) (((toRep F f).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((toRep F g).ρ M) ((linearIsoOfHom F m) ((PiTensorProduct.tprod k) x))
    rw [linearIsoOfHom_tprod, toRep_ρ_tprod]
    simp only [Functor.id_obj]
    rw [linearIsoOfHom_tprod, toRep_ρ_tprod]
    apply congrArg
    funext i
    rw [linearIsoOfEq_comm_ρ]

lemma homToRepHom_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (f : X ⟶ Y) : (homToRepHom F f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => linearIsoOfEq F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  simp only [homToRepHom, linearIsoOfHom, Functor.id_obj]
  erw [LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => linearIsoOfEq F _)
    ((PiTensorProduct.reindex k (fun x => _) (OverColor.Hom.toEquiv f))
      ((PiTensorProduct.tprod k) p)) = _
  rw [PiTensorProduct.reindex_tprod]
  exact PiTensorProduct.congr_tprod
    (fun i => linearIsoOfEq F (Hom.toEquiv_symm_apply f i))
    fun i => p ((Hom.toEquiv f).symm i)

lemma homToRepHom_id (X : OverColor C) : homToRepHom F (𝟙 X) = 𝟙 _ := by
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
    simp only [map_add, hx, hy])
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, Action.id_hom, ModuleCat.id_apply]
  apply congrArg
  simp only [homToRepHom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  rw [linearIsoOfHom_tprod]
  simp only [toRep_V_carrier, linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl,
    Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  exact congrArg _ (funext (fun i => rfl))

lemma homToRepHom_comp {X Y Z : OverColor C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homToRepHom F (f ≫ g) = homToRepHom F f ≫ homToRepHom F g := by
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
    simp only [map_add, hx, hy])
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, Action.comp_hom,
    ModuleCat.hom_comp]
  apply congrArg
  rw [homToRepHom, homToRepHom, homToRepHom]
  change (linearIsoOfHom F (CategoryTheory.CategoryStruct.comp f g))
    ((PiTensorProduct.tprod k) x) =
    (linearIsoOfHom F g) ((linearIsoOfHom F f) ((PiTensorProduct.tprod k) x))
  rw [linearIsoOfHom_tprod, linearIsoOfHom_tprod]
  conv_rhs =>
    erw [linearIsoOfHom_tprod F g]
  refine congrArg _ (funext (fun i => ?_))
  simp only [linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
    eqToIso.inv, LinearEquiv.ofLinear_apply]
  have hX {c1 c2 c3 : Discrete C} (h1 : c1 = c2) (h2 : c2 = c3)
    (v : F.obj c1) : (F.map (eqToHom h2)).hom ((F.map (eqToHom h1)).hom v)
    = (F.map (eqToHom (h1.trans h2))).hom v := by
    subst h2 h1
    simp_all only [eqToHom_refl, Discrete.functor_map_id, Action.id_hom, ModuleCat.id_apply]
  rw [hX]
  rfl

end homToRepHom

/-!

## toRepFunc

The functions `toRep F` and `homToRepHom F` together form a functor.

-/

/-- The `Functor (OverColor C) (Rep k G)` from a functor `Discrete C ⥤ Rep k G`. -/
def toRepFunc : Functor (OverColor C) (Rep k G) where
  obj := toRep F
  map := homToRepHom F
  map_comp := homToRepHom_comp F
  map_id := homToRepHom_id F

/-!

## The braiding of toRepFunc

The functor `toRepFunc` is a braided monoidal functor.
This is made manifest in the result
- `toRepFunc_braidedFunctor`.

-/

/-- The unit isomorphism between `𝟙_ (Rep k G)` and `toRep F (𝟙_ (OverColor C))`
  generated using `PiTensorProduct.isEmptyEquiv`. -/
def toRepUnitIso : 𝟙_ (Rep k G) ≅ toRep F (𝟙_ (OverColor C)) :=
  Action.mkIso (PiTensorProduct.isEmptyEquiv Empty).symm.toModuleIso
  (by
    intro g
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun x => ?_)
    simp only [toRep_V_carrier]
    rw [ModuleCat.hom_comp]
    simp only [toRep_V_carrier, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    change _ = (toRep F (𝟙_ (OverColor C))).ρ g ((PiTensorProduct.isEmptyEquiv Empty).symm x)
    simp only [toRep_ρ_empty F g,
      PiTensorProduct.isEmptyEquiv_symm_apply, map_smul, LinearMap.id_coe, id_eq]
    rfl)

/-- An equivalence used in the lemma of `μ_tmul_tprod_mk`. Identical to `μModEquiv`
  except with arguments based on maps instead of elements of `OverColor C`. -/
def discreteSumEquiv {X Y : Type} {cX : X → C} {cY : Y → C} (i : X ⊕ Y) :
    Sum.elim (fun i => F.obj (Discrete.mk (cX i)))
    (fun i => F.obj (Discrete.mk (cY i))) i ≃ₗ[k] F.obj (Discrete.mk ((Sum.elim cX cY) i)) :=
  match i with
  | Sum.inl _ => LinearEquiv.refl _ _
  | Sum.inr _ => LinearEquiv.refl _ _

open TensorProduct in
/-- The equivalence of modules corresponding to the tensor. -/
def μModEquiv (X Y : OverColor C) :
    ((toRep F X).V ⊗[k] (toRep F Y).V) ≃ₗ[k] toRep F (X ⊗ Y) :=
  PhysLean.PiTensorProduct.tmulEquiv ≪≫ₗ PiTensorProduct.congr (discreteSumEquiv F)

lemma μModEquiv_tmul_tprod {X Y : OverColor C}
    (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk (Y.hom i))) :
    μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    PiTensorProduct.tprod k fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  rw [μModEquiv]
  simp only [toRep_V_carrier]
  rw [LinearEquiv.trans_apply]
  rw [PhysLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  change PiTensorProduct.congr (discreteSumEquiv F)
    (PiTensorProduct.tprod k (PhysLean.PiTensorProduct.elimPureTensor p q)) = _
  rw [PiTensorProduct.congr_tprod]

/-- The natural isomorphism corresponding to the tensor. -/
def μ (X Y : OverColor C) : toRep F X ⊗ toRep F Y ≅ toRep F (X ⊗ Y) :=
  Action.mkIso (μModEquiv F X Y).toModuleIso
  (fun M => by
    refine ModuleCat.hom_ext ?_
    refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
    change (μModEquiv F X Y)
      ((toRep F X).ρ M (PiTensorProduct.tprod k p) ⊗ₜ[k]
      (toRep F Y).ρ M (PiTensorProduct.tprod k q)) = (toRep F (X ⊗ Y)).ρ M
      (μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q))
    rw [μModEquiv_tmul_tprod]
    rw [toRep_ρ_tprod, toRep_ρ_tprod]
    simp only [Functor.id_obj]
    rw [μModEquiv_tmul_tprod]
    erw [toRep_ρ_tprod]
    apply congrArg
    funext i
    match i with
    | Sum.inl i =>
      rfl
    | Sum.inr i =>
      rfl)

lemma μ_tmul_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i))
    (q : (i : Y.left) → (F.obj <| Discrete.mk (Y.hom i))) :
    (μ F X Y).hom.hom (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) :=
  μModEquiv_tmul_tprod F p q

lemma μ_tmul_tprod_mk {X Y : Type} {cX : X → C} {cY : Y → C}
    (p : (i : X) → F.obj (Discrete.mk <| cX i))
    (q : (i : Y) → (F.obj <| Discrete.mk (cY i))) :
    (μ F (OverColor.mk cX) (OverColor.mk cY)).hom.hom
    (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q)
    = (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) :=
  μModEquiv_tmul_tprod F _ _

lemma μ_natural_left {X Y : OverColor C} (f : X ⟶ Y) (Z : OverColor C) :
    MonoidalCategory.whiskerRight (homToRepHom F f) (toRep F Z) ≫ (μ F Y Z).hom =
    (μ F X Z).hom ≫ homToRepHom F (MonoidalCategory.whiskerRight f Z) := by
  ext1
  refine ModuleCat.hom_ext ?_
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, tensorObj_of_left, tensorObj_of_hom, Action.tensorObj_V,
    CategoryStruct.comp, Action.Hom.comp_hom, Action.whiskerRight_hom]
  change _ = (homToRepHom F (MonoidalCategory.whiskerRight f Z)).hom
    ((μ F X Z).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  change _ = (homToRepHom F (f ▷ Z)).hom
    (PiTensorProduct.tprod k fun i => discreteSumEquiv F i
    (PhysLean.PiTensorProduct.elimPureTensor p q i))
  rw [homToRepHom_tprod]
  change ((μ F Y Z).hom.hom.hom' ∘ₗ ((homToRepHom F f).hom ▷ (toRep F Z).V).hom') _ = _
  simp only [toRep_V_carrier,
    LinearMap.coe_comp, Function.comp_apply, Functor.id_obj]
  conv_lhs =>
    right
    change ((homToRepHom F f).hom ((PiTensorProduct.tprod k) p) ⊗ₜ[k] ((PiTensorProduct.tprod k) q))
  rw [homToRepHom_tprod]
  change (μ F Y Z).hom.hom (((PiTensorProduct.tprod k) fun i => (linearIsoOfEq F _)
    (p ((OverColor.Hom.toEquiv f).symm i))) ⊗ₜ[k] (PiTensorProduct.tprod k) q) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i =>
    simp only [Sum.elim_inr, Hom.toEquiv, Equiv.coe_fn_symm_mk, linearIsoOfEq, Functor.mapIso_hom,
      eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, LinearEquiv.ofLinear_apply, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv]
    rfl

lemma μ_natural_right {X Y : OverColor C} (X' : OverColor C) (f : X ⟶ Y) :
    MonoidalCategory.whiskerLeft (toRep F X') (homToRepHom F f) ≫ (μ F X' Y).hom =
    (μ F X' X).hom ≫ homToRepHom F (MonoidalCategory.whiskerLeft X' f) := by
  ext1
  refine ModuleCat.hom_ext ?_
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp, Action.Hom.comp_hom]
  change _ = (homToRepHom F (X' ◁ f)).hom ((μ F X' X).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  change _ = (homToRepHom F (X' ◁ f)).hom ((PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor p q i))
  rw [homToRepHom_tprod]
  rw [ModuleCat.Hom.hom, ConcreteCategory.hom]
  simp only [ModuleCat.instConcreteCategoryLinearMapIdCarrier, LinearMap.coe_comp,
    Function.comp_apply]
  conv_lhs =>
    right
    change (PiTensorProduct.tprod k) p ⊗ₜ[k] (homToRepHom F f).hom ((PiTensorProduct.tprod k) q)
  rw [homToRepHom_tprod]
  change (μ F X' Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (linearIsoOfEq F _) (q ((OverColor.Hom.toEquiv f).symm i))) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simp only [Sum.elim_inl, linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
      eqToIso.inv, LinearEquiv.ofLinear_apply, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
      Action.id_hom, Iso.refl_inv, Functor.id_obj]
    rfl
  | Sum.inr i => rfl

lemma associativity (X Y Z : OverColor C) :
    whiskerRight (μ F X Y).hom (toRep F Z) ≫
    (μ F (X ⊗ Y) Z).hom ≫ homToRepHom F (associator X Y Z).hom =
    (associator (toRep F X) (toRep F Y) (toRep F Z)).hom ≫
    whiskerLeft (toRep F X) (μ F Y Z).hom ≫ (μ F X (Y ⊗ Z)).hom := by
  ext1
  refine ModuleCat.hom_ext ?_
  refine PhysLean.PiTensorProduct.induction_assoc' (fun p q m => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp, Action.Hom.comp_hom]
  change (homToRepHom F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    ((((μ F X Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k]
    (PiTensorProduct.tprod k) q)) ⊗ₜ[k] (PiTensorProduct.tprod k) m))) =
    (μ F X (Y ⊗ Z)).hom.hom ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((μ F Y Z).hom.hom
    ((PiTensorProduct.tprod k) q ⊗ₜ[k] (PiTensorProduct.tprod k) m)))))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  change (homToRepHom F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    (((PiTensorProduct.tprod k) fun i => (discreteSumEquiv F i)
    (PhysLean.PiTensorProduct.elimPureTensor p q i)) ⊗ₜ[k] (PiTensorProduct.tprod k) m)) =
    (μ F X (Y ⊗ Z)).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (PhysLean.PiTensorProduct.elimPureTensor q m i))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [homToRepHom_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simp only [Functor.id_obj,
      linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
      Iso.refl_inv, LinearEquiv.ofLinear_apply, Sum.elim_inl]
    rfl
  | Sum.inr (Sum.inl i) =>
    simp only [Functor.id_obj,
      linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
      Iso.refl_inv, LinearEquiv.ofLinear_apply, Sum.elim_inr]
    rfl
  | Sum.inr (Sum.inr i) =>
    simp only [Functor.id_obj,
      linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
      Iso.refl_inv, LinearEquiv.ofLinear_apply, Sum.elim_inr]
    rfl

open TensorProduct in
lemma left_unitality (X : OverColor C) : (leftUnitor (toRep F X)).hom =
    whiskerRight (toRepUnitIso F).hom (toRep F X) ≫
    (μ F (𝟙_ (OverColor C)) X).hom ≫ homToRepHom F (leftUnitor X).hom := by
  ext1
  refine ModuleCat.hom_ext ?_
  apply PhysLean.PiTensorProduct.induction_mod_tmul (fun x q => ?_)
  simp only [toRep_V_carrier, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.tensorUnit_V, Action.tensorObj_V,
    Action.leftUnitor_hom_hom, CategoryStruct.comp, Action.Hom.comp_hom, tensorObj_of_left,
    tensorUnit_of_left, tensorObj_of_hom, Action.whiskerRight_hom]
  change TensorProduct.lid k (toRep F X) (x ⊗ₜ[k] (PiTensorProduct.tprod k) q) =
    (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((((PiTensorProduct.isEmptyEquiv Empty).symm x) ⊗ₜ[k] (PiTensorProduct.tprod k) q)))
  simp only [toRep_V_carrier, lid_tmul,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, PiTensorProduct.isEmptyEquiv,
    LinearEquiv.coe_symm_mk]
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (homToRepHom F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((PiTensorProduct.tprod k) _ ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  erw [homToRepHom_tprod]
  simp only [toRep_V_carrier, linearIsoOfEq, eqToIso_refl, Functor.mapIso_refl,
    Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  rfl

open TensorProduct in
lemma right_unitality (X : OverColor C) : (rightUnitor (toRep F X)).hom =
    whiskerLeft (toRep F X) (toRepUnitIso F).hom ≫
    (μ F X (𝟙_ (OverColor C))).hom ≫ homToRepHom F (rightUnitor X).hom := by
  ext1
  refine ModuleCat.hom_ext ?_
  apply PhysLean.PiTensorProduct.induction_tmul_mod (fun p x => ?_)
  simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, CategoryStruct.comp, Action.Hom.comp_hom]
  change TensorProduct.rid k (toRep F X) ((PiTensorProduct.tprod k) p ⊗ₜ[k] x) =
    (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((PiTensorProduct.isEmptyEquiv Empty).symm x)))))
  simp only [rid_tmul, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, PiTensorProduct.isEmptyEquiv,
    LinearEquiv.coe_symm_mk, tmul_smul]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (homToRepHom F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) _))
  rw [μ_tmul_tprod]
  erw [homToRepHom_tprod]
  simp only [toRep_V_carrier, linearIsoOfEq, eqToIso_refl,
    Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  rfl

lemma braided' (X Y : OverColor C) : (μ F X Y).hom ≫ (homToRepHom F) (β_ X Y).hom =
    (β_ (toRep F X) (toRep F Y)).hom ≫ (μ F Y X).hom := by
  ext1
  refine ModuleCat.hom_ext ?_
  apply PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRep_V_carrier, CategoryStruct.comp, Action.Hom.comp_hom]
  change (homToRepHom F (β_ X Y).hom).hom ((μ F X Y).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q)) = (μ F Y X).hom.hom
    ((PiTensorProduct.tprod k) q ⊗ₜ[k] (PiTensorProduct.tprod k) p)
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [homToRepHom_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simp only [Functor.id_obj, Sum.elim_inl, linearIsoOfEq, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    rfl
  | Sum.inr i =>
    simp only [Functor.id_obj, Sum.elim_inr, linearIsoOfEq, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    rfl

lemma braided (X Y : OverColor C) :
    (homToRepHom F) (β_ X Y).hom = (μ F X Y).inv ≫
    ((β_ (toRep F X) (toRep F Y)).hom ≫ (μ F Y X).hom) :=
  (Iso.eq_inv_comp (μ F X Y)).mpr (braided' F X Y)

/-- The lift of a functor is lax braided. -/
instance toRepFunc_laxBraidedFunctor : Functor.LaxBraided (toRepFunc F) where
  ε := (toRepUnitIso F).hom
  μ := fun X Y => (μ F X Y).hom
  μ_natural_left := μ_natural_left F
  μ_natural_right := μ_natural_right F
  associativity := associativity F
  left_unitality := left_unitality F
  right_unitality := right_unitality F
  braided := fun X Y => by
    simp only [toRepFunc]
    rw [braided F X Y]
    simp

/-- The lift of a functor is monoidal. -/
instance toRepFunc_monoidalFunctor : Functor.Monoidal (toRepFunc F) :=
  haveI : IsIso (Functor.LaxMonoidal.ε (toRepFunc F)) :=
    Action.isIso_of_hom_isIso (toRepUnitIso F).hom
  haveI : (∀ (X Y : OverColor C), IsIso (Functor.LaxMonoidal.μ (toRepFunc F) X Y)) :=
    fun X Y => Action.isIso_of_hom_isIso ((μ F X Y).hom)
  Functor.Monoidal.ofLaxMonoidal _

/-- The lift of a functor is braided. -/
instance toRepFunc_braidedFunctor : Functor.Braided (toRepFunc F) := Functor.Braided.mk (fun X Y =>
  Functor.LaxBraided.braided X Y)

/-!

## The natural transformation `repNatTransOfColor`

Given two functors `F F' : Discrete C ⥤ Rep k G` and a natural transformation `η : F ⟶ F'`,
we construct a natural transformation `repNatTransOfColor : toRepFunc F ⟶ toRepFunc F'`
by taking the tensor product of the corresponding morphisms in `η`.

-/

variable {F F' : Discrete C ⥤ Rep k G} (η : F ⟶ F')

/-- Given two functors `F F' : Discrete C ⥤ Rep k G` and a natural transformation `η : F ⟶ F'`,
  and an `X : OverColor C`, the `(toRepFunc F).obj X ⟶ (toRepFunc F').obj X` in `Rep k G`
  constructed by the tensor product of the morphisms in `η` with corresponding color. -/
def repNatTransOfColorApp (X : OverColor C) : (toRepFunc F).obj X ⟶ (toRepFunc F').obj X where
  hom := ModuleCat.ofHom <| PiTensorProduct.map (fun x => (η.app (Discrete.mk (X.hom x))).hom.hom)
  comm M := by
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [map_add, ModuleCat.hom_comp]
      erw [hx, hy]
      rfl)
    intro r x
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, ModuleCat.hom_comp]
    apply congrArg
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom.hom)
      ((((toRepFunc F).obj X).ρ M) ((PiTensorProduct.tprod k) x)) =
      (((toRepFunc F').obj X).ρ M) ((PiTensorProduct.map fun x =>
      (η.app { as := X.hom x }).hom.hom) ((PiTensorProduct.tprod k) x))
    rw [PiTensorProduct.map_tprod]
    simp only [Functor.id_obj, toRepFunc]
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom.hom)
      (((toRep F X).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((toRep F' X).ρ M) ((PiTensorProduct.tprod k) fun i =>
      (η.app { as := X.hom i }).hom.hom (x i))
    rw [toRep_ρ_tprod, toRep_ρ_tprod]
    erw [PiTensorProduct.map_tprod]
    apply congrArg
    funext i
    have h := ModuleCat.hom_ext_iff.mp ((η.app (Discrete.mk (X.hom i))).comm M)
    simpa using LinearMap.congr_fun h (x i)

lemma repNatTransOfColorApp_tprod (X : OverColor C)
    (p : (i : X.left) → F.obj (Discrete.mk (X.hom i))) :
    (repNatTransOfColorApp η X).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun i => (η.app (Discrete.mk (X.hom i))).hom (p i) := by
  simp only [repNatTransOfColorApp]
  erw [PiTensorProduct.map_tprod]
  rfl

lemma repNatTransOfColorApp_naturality {X Y : OverColor C} (f : X ⟶ Y) :
    (toRepFunc F).map f ≫ repNatTransOfColorApp η Y =
    repNatTransOfColorApp η X ≫ (toRepFunc F').map f := by
  ext x
  refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [map_add]
      rw [hx, hy])
  intro r x
  simp only [Action.comp_hom, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
    ModuleCat.hom_comp]
  apply congrArg
  simp only [toRepFunc, toRep_V_carrier]
  change (repNatTransOfColorApp η Y).hom ((homToRepHom F f).hom ((PiTensorProduct.tprod k) x)) =
  (homToRepHom F' f).hom ((repNatTransOfColorApp η X).hom ((PiTensorProduct.tprod k) x))
  rw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
  erw [repNatTransOfColorApp_tprod, homToRepHom_tprod]
  apply congrArg
  funext i
  simp only [linearIsoOfEq, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
    eqToIso.inv, LinearEquiv.ofLinear_apply]
  generalize_proofs h1
  have hn := ModuleCat.hom_ext_iff.mp <| Action.hom_ext_iff.mp <|
    η.naturality (eqToHom h1)
  have h := LinearMap.congr_fun hn (x ((Hom.toEquiv f).symm i))
  simpa

/-- Given a natural transformation between `F F' : Discrete C ⥤ Rep k G` the
  monoidal natural transformation between `toRepFunc F` and `toRepFunc F'`. -/
def repNatTransOfColor : (toRepFunc F) ⟶ (toRepFunc F') where
  app := repNatTransOfColorApp η
  naturality _ _ f := repNatTransOfColorApp_naturality η f
/-!

## The Monoidal structure of `repNatTransOfColor`

The natural transformation `repNatTransOfColor` is monoidal,
which is made manifest in the results
- `repNatTransOfColor_isMonoidal`.

-/

lemma repNatTransOfColorApp_unit : Functor.LaxMonoidal.ε (toRepFunc F) ≫
    repNatTransOfColorApp η (𝟙_ (OverColor C)) = Functor.LaxMonoidal.ε (toRepFunc F') := by
  ext
  simp only [toRepFunc, toRep_V_carrier, tensorUnit_of_left, tensorUnit_of_hom, Action.tensorUnit_V,
    CategoryStruct.comp, Action.Hom.comp_hom]
  rw [ModuleCat.Hom.hom, ConcreteCategory.hom, ModuleCat.Hom.hom, ConcreteCategory.hom]
  simp only [ModuleCat.instConcreteCategoryLinearMapIdCarrier, LinearMap.coe_comp,
    Function.comp_apply]
  erw [PiTensorProduct.isEmptyEquiv_symm_apply, PiTensorProduct.isEmptyEquiv_symm_apply]
  simp only [map_smul]
  apply congrArg
  erw [repNatTransOfColorApp_tprod]
  apply congrArg
  funext i
  exact Empty.elim i

lemma repNatTransOfColorApp_tensor (X Y : OverColor C) :
    (Functor.LaxMonoidal.μ (toRepFunc F)) X Y ≫ repNatTransOfColorApp η (X ⊗ Y) =
    (repNatTransOfColorApp η X ⊗ₘ repNatTransOfColorApp η Y) ≫
    (Functor.LaxMonoidal.μ (toRepFunc F')) X Y := by
  ext1
  refine ModuleCat.hom_ext ?_
  refine PhysLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [toRepFunc, toRep_V_carrier, CategoryStruct.comp, Action.Hom.comp_hom]
  rw [ModuleCat.Hom.hom, ConcreteCategory.hom, ModuleCat.Hom.hom, ConcreteCategory.hom]
  simp only [ModuleCat.instConcreteCategoryLinearMapIdCarrier, LinearMap.coe_comp,
    Function.comp_apply]
  erw [μ_tmul_tprod]
  erw [repNatTransOfColorApp_tprod]
  change _ = (μ F' X Y).hom.hom
    ((repNatTransOfColorApp η X).hom (PiTensorProduct.tprod k p) ⊗ₜ[k]
    (repNatTransOfColorApp η Y).hom (PiTensorProduct.tprod k q))
  rw [repNatTransOfColorApp_tprod, repNatTransOfColorApp_tprod]
  erw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inr i => rfl
  | Sum.inl i => rfl

/-- The lift of a natural transformation is monoidal. -/
instance repNatTransOfColor_isMonoidal : NatTrans.IsMonoidal (repNatTransOfColor η) where
  unit := repNatTransOfColorApp_unit η
  tensor := repNatTransOfColorApp_tensor η

end
end lift
open lift

/-!

## The functor `lift`

-/

/-- The functor taking functors in `Discrete C ⥤ Rep k G` to monoidal functors in
  `BraidedFunctor (OverColor C) (Rep k G)`, built on the PiTensorProduct. -/
noncomputable def lift : (Discrete C ⥤ Rep k G) ⥤ LaxBraidedFunctor (OverColor C) (Rep k G) where
  obj F := LaxBraidedFunctor.of (lift.toRepFunc F)
  map η := LaxBraidedFunctor.homMk (repNatTransOfColor η)
  map_id F := by
    simp only [repNatTransOfColor]
    refine LaxBraidedFunctor.hom_ext ?_
    ext X : 2
    simp only [LaxBraidedFunctor.toLaxMonoidalFunctor_toFunctor, LaxBraidedFunctor.of_toFunctor,
      LaxBraidedFunctor.homMk_hom_hom, LaxBraidedFunctor.id_hom, NatTrans.id_app]
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
        intro x y hx hy
        simp only [map_add]
        rw [hx, hy])
    intro r y
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
    apply congrArg
    rw [repNatTransOfColorApp_tprod]
    rfl
  map_comp {F G H} η θ := by
    refine LaxBraidedFunctor.hom_ext ?_
    ext X : 2
    simp only [LaxBraidedFunctor.toLaxMonoidalFunctor_toFunctor, LaxBraidedFunctor.of_toFunctor,
      LaxBraidedFunctor.homMk_hom_hom, LaxBraidedFunctor.comp_hom, LaxMonoidalFunctor.comp_hom,
      NatTrans.comp_app]
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
        intro x y hx hy
        simp only [map_add]
        rw [hx, hy])
    intro r y
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, Action.comp_hom,
      ModuleCat.hom_comp]
    apply congrArg
    simp only [repNatTransOfColor]
    erw [repNatTransOfColorApp_tprod]
    change _ = (repNatTransOfColorApp θ X).hom
      ((repNatTransOfColorApp η X).hom ((PiTensorProduct.tprod k) y))
    rw [lift.repNatTransOfColorApp_tprod]
    erw [lift.repNatTransOfColorApp_tprod]
    rfl

namespace lift
variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

/-- The lift of a functor is monoidal. -/
noncomputable instance : (lift.obj F).Monoidal := toRepFunc_monoidalFunctor F

/-- The lift of a functor is lax-braided. -/
noncomputable instance : (lift.obj F).LaxBraided := toRepFunc_laxBraidedFunctor F

/-- The lift of a functor is braided. -/
noncomputable instance : (lift.obj F).Braided := Functor.Braided.mk (fun X Y =>
  Functor.LaxBraided.braided X Y)

lemma map_tprod (F : Discrete C ⥤ Rep k G) {X Y : OverColor C} (f : X ⟶ Y)
    (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i)) :
    ((lift.obj F).map f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => linearIsoOfEq F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  simp only [lift, toRepFunc]
  erw [homToRepHom_tprod]

lemma obj_μ_tprod_tmul (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : X.left) → (F.obj (Discrete.mk <| X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk <| Y.hom i)) :
    (Functor.LaxMonoidal.μ (lift.obj F).toFunctor X Y).hom
    (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (PhysLean.PiTensorProduct.elimPureTensor p q i) := by
  exact μ_tmul_tprod F p q

lemma μIso_inv_tprod (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : (X ⊗ Y).left) → F.obj (Discrete.mk <| (X ⊗ Y).hom i)) :
    (Functor.Monoidal.μIso (lift.obj F).toFunctor X Y).inv.hom (PiTensorProduct.tprod k p) =
    (PiTensorProduct.tprod k (fun i => p (Sum.inl i))) ⊗ₜ[k]
    (PiTensorProduct.tprod k (fun i => p (Sum.inr i))) := by
  change ((Action.forget _ _).mapIso (Functor.Monoidal.μIso (lift.obj F).toFunctor X Y)).inv
    (PiTensorProduct.tprod k p) = _
  trans ((Action.forget _ _).mapIso
    (Functor.Monoidal.μIso (lift.obj F).toFunctor X Y)).toLinearEquiv.symm
    (PiTensorProduct.tprod k p)
  · rfl
  erw [← LinearEquiv.eq_symm_apply]
  change _ = (Functor.LaxMonoidal.μ (lift.obj F).toFunctor X Y).hom _
  erw [obj_μ_tprod_tmul]
  congr
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i => rfl

lemma inv_μ (X Y : OverColor C) : inv (Functor.LaxMonoidal.μ (lift.obj F).toFunctor X Y) =
    (lift.μ F X Y).inv := by
  change inv (lift.μ F X Y).hom = _
  exact IsIso.Iso.inv_hom (μ F X Y)

end lift

/-!

## The forgetful functor from `BraidedFunctor (OverColor C) (Rep k G)` to `Discrete C ⥤ Rep k G`

-/

/-- The natural inclusion of `Discrete C` into `OverColor C`. -/
def incl : Discrete C ⥤ OverColor C := Discrete.functor fun c =>
  OverColor.mk (fun (_ : Fin 1) => c)

noncomputable section

/-- The forgetful map from `BraidedFunctor (OverColor C) (Rep k G)` to `Discrete C ⥤ Rep k G`
  built on the inclusion `incl` and forgetting the monoidal structure. -/
def forget : LaxBraidedFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G) where
  obj F := Discrete.functor fun c => F.obj (incl.obj (Discrete.mk c))
  map η := Discrete.natTrans fun c => η.hom.hom.app (incl.obj c)

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

open TensorProduct

/--
The `forgetLiftAppV` function takes an object `c` of type `C` and returns a linear equivalence
between the vector space obtained by applying the lift of `F` and that obtained by applying
`F`.
--/
def forgetLiftAppV (c : C) : ((lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))).V ≃ₗ[k]
    (F.obj (Discrete.mk c)).V :=
  (PiTensorProduct.subsingletonEquiv 0 :
    (⨂[k] (_ : Fin 1), (F.obj (Discrete.mk c))) ≃ₗ[k] F.obj (Discrete.mk c))

@[simp]
lemma forgetLiftAppV_symm_apply (c : C) (x : (F.obj (Discrete.mk c)).V) :
    (forgetLiftAppV F c).symm x = PiTensorProduct.tprod k (fun _ => x) := by
  simp [forgetLiftAppV]
  erw [PiTensorProduct.subsingletonEquiv_symm_apply]
  congr
  funext i
  fin_cases i
  rfl

/-- The `forgetLiftAppV` function takes an object `c` of type `C` and returns a isomorphism
between the objects obtained by applying the lift of `F` and that obtained by applying
`F`. -/
def forgetLiftApp (c : C) : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))
    ≅ F.obj (Discrete.mk c) :=
  Action.mkIso (forgetLiftAppV F c).toModuleIso
  (fun g => by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun x => ?_)
    rw [ModuleCat.Hom.hom, ConcreteCategory.hom, ModuleCat.Hom.hom, ConcreteCategory.hom]
    simp only [ModuleCat.instConcreteCategoryLinearMapIdCarrier]
    simp only [forgetLiftAppV, Fin.isValue]
    refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      simp_rw [map_add, hx, hy]
    simp only [CategoryStruct.comp, Fin.isValue,
      PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, LinearMap.coe_comp,
      Function.comp_apply]
    apply congrArg
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    simp only [lift, lift.toRepFunc, Fin.isValue]
    simp
    erw [lift.toRep_ρ_tprod]
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    rfl)

lemma forgetLiftApp_naturality_eqToHom (c c1 : C) (h : c = c1) :
    (forgetLiftApp F c).hom ≫ F.map (Discrete.eqToHom h) =
    (lift.obj F).map (OverColor.mkIso (by rw [h])).hom ≫ (forgetLiftApp F c1).hom := by
  subst h
  simp [mkIso_refl_hom]

lemma forgetLiftApp_naturality_eqToHom_apply (c c1 : C) (h : c = c1)
    (x : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))) :
    (F.map (Discrete.eqToHom h)).hom ((forgetLiftApp F c).hom.hom x) =
    (forgetLiftApp F c1).hom.hom (((lift.obj F).map (OverColor.mkIso (by rw [h])).hom).hom x) := by
  change ((forgetLiftApp F c).hom ≫ F.map (Discrete.eqToHom h)).hom x = _
  rw [forgetLiftApp_naturality_eqToHom]
  rfl

lemma forgetLiftApp_hom_hom_apply_eq (c : C)
    (x : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c)))
    (y : (F.obj (Discrete.mk c)).V) :
    (forgetLiftApp F c).hom.hom x = y ↔ x = PiTensorProduct.tprod k (fun _ => y) := by
  rw [← forgetLiftAppV_symm_apply]
  erw [LinearEquiv.eq_symm_apply]
  rfl

/-- The isomorphism between the representation `(lift.obj F).obj (OverColor.mk ![c])`
  and the representation `F.obj (Discrete.mk c)`. See `forgetLiftApp` for
  an alternative version. -/
def forgetLiftAppCon (c : C) : (lift.obj F).obj (OverColor.mk ![c])
    ≅ F.obj (Discrete.mk c) := ((lift.obj F).mapIso (OverColor.mkIso (by
  funext i
  fin_cases i
  rfl))).trans (forgetLiftApp F c)

lemma forgetLiftAppCon_inv_apply_expand (c : C) (x : F.obj (Discrete.mk c)) :
    (forgetLiftAppCon F c).inv.hom x =
    ((lift.obj F).map (OverColor.mkIso (by
    funext i
    fin_cases i
    rfl)).hom).hom ((forgetLiftApp F c).inv.hom x) := by
  rw [forgetLiftAppCon]
  simp_all only [Nat.succ_eq_add_one, Iso.trans_inv, Functor.mapIso_inv, Action.comp_hom,
    ModuleCat.hom_comp]
  rfl

lemma forgetLiftAppCon_naturality_eqToHom (c c1 : C) (h : c = c1) :
    (forgetLiftAppCon F c).hom ≫ F.map (Discrete.eqToHom h) =
    (lift.obj F).map (OverColor.mkIso (by rw [h])).hom ≫ (forgetLiftAppCon F c1).hom := by
  subst h
  simp [mkIso_refl_hom]

lemma forgetLiftAppCon_naturality_eqToHom_apply (c c1 : C) (h : c = c1)
    (x : (lift.obj F).obj (OverColor.mk ![c])) :
    (F.map (Discrete.eqToHom h)).hom ((forgetLiftAppCon F c).hom.hom x) =
    (forgetLiftAppCon F c1).hom.hom
    (((lift.obj F).map (OverColor.mkIso (by rw [h])).hom).hom x) := by
  change ((forgetLiftAppCon F c).hom ≫ F.map (Discrete.eqToHom h)).hom x = _
  rw [forgetLiftAppCon_naturality_eqToHom]
  rfl

/-- The natural isomorphism between `lift (C := C) ⋙ forget` and
`Functor.id (Discrete C ⥤ Rep k G)`.
-/
informal_definition forgetLift where
  deps := [``forget, ``lift]
  tag := "6VZWS"

end
end OverColor
end IndexNotation
