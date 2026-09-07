/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.ClassicalFieldTheory.JetAlgebra.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# The jet component space of a matter field

## i. Overview

For a matter field valued in a complex vector space `V`, the *jet component space* is the
span of the derivative symbols `∂_s ψ_α` and their conjugates `∂_s ψ̄_α`: the local
coordinate functions on the space of jets of the field. This file defines that space and
the structure on it that does not involve a gauge group: the Lorentz action, the jet
derivative, functoriality in `V` and the mass-weight scaling. The action of a gauge group
is in `Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.GaugeAction`.

## ii. Key results

- `JetComponentSpace` : the space of component functions.
- `JetComponentSpace.repLorentzGroup` : the Lorentz action on the component space.
- `JetComponentSpace.jetDeriv` : the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the label.
- `JetComponentSpace.jetDeriv_comm` : the shifts in different directions commute.
- `JetComponentSpace.repLorentzGroup_jetDeriv` : the shift is a Lorentz vector.
- `JetComponentSpace.comap` : functoriality, contravariant in the target space.
- `JetComponentSpace.massWeightScale` : the mass-weight scaling.
- `JetComponentSpace.prodEquiv` : the component space of a direct sum.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

variable {V : Type _} [AddCommGroup V] [Module ℂ V]


/-- The space of component functions of a `V`-valued matter field: the span of the
symbols `∂_s ψ_α` and their conjugates `∂_s ψ̄_α`. The first factor holds the
unconjugated symbols, the second the conjugate ones; in each, `DerivAlgebraComplex`
carries the derivative label `s` and the dual factor the target component `α`. -/
abbrev JetComponentSpace (V : Type _) [AddCommGroup V] [Module ℂ V]  :=
  (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V) ×
  (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V))

/-!

## The Lorentz action on the component space

-/

/-- **The Lorentz action on the jet component space.** Under a Lorentz transformation a
matter field transforms as `ψ(x) ↦ ρ(Λ) ψ(Λ⁻¹ x)`, so a derivative symbol `∂_s ψ_α` is
acted on in *both* of its labels: the derivative multiset `s` by the Lorentz action on
covectors, extended to `DerivAlgebraComplex`, and the target index `α` by the
contragredient of `ρ`.

Unlike the gauge action, this needs no fibrewise-linearity or finite-dimensionality
hypothesis: the two labels transform independently, so the action is simply a tensor
product of representations. The conjugate half is the same with `ρ` replaced by its
conjugate, the symbols `∂_s ψ̄_α` transforming by `star` of the spinor matrix. -/
noncomputable def JetComponentSpace.repLorentzGroup
    (repV : Representation ℂ SL(2,ℂ) V) :
    Representation ℂ SL(2,ℂ) (JetComponentSpace V) :=
  (DerivAlgebraComplex.repLorentzGroup.tprod repV.dual).prod
    (DerivAlgebraComplex.repLorentzGroup.tprod repV.conj.dual)

@[simp]
lemma JetComponentSpace.repLorentzGroup_fst (repV : Representation ℂ SL(2,ℂ) V)
    (Λ : SL(2,ℂ)) (x : JetComponentSpace V) :
    (JetComponentSpace.repLorentzGroup repV Λ x).1
      = (DerivAlgebraComplex.repLorentzGroup.tprod repV.dual) Λ x.1 := rfl

@[simp]
lemma JetComponentSpace.repLorentzGroup_snd (repV : Representation ℂ SL(2,ℂ) V)
    (Λ : SL(2,ℂ)) (x : JetComponentSpace V) :
    (JetComponentSpace.repLorentzGroup repV Λ x).2
      = (DerivAlgebraComplex.repLorentzGroup.tprod repV.conj.dual) Λ x.2 := rfl

/-- On a pure symbol the Lorentz action is diagonal in the two labels: the derivative
label transforms in `DerivAlgebraComplex`, the target index contragrediently. -/
@[simp]
lemma JetComponentSpace.repLorentzGroup_fst_tmul (repV : Representation ℂ SL(2,ℂ) V)
    (Λ : SL(2,ℂ)) (a : DerivAlgebraComplex) (φ : Module.Dual ℂ V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)) :
    (JetComponentSpace.repLorentzGroup repV Λ (a ⊗ₜ[ℂ] φ, y)).1
      = DerivAlgebraComplex.repLorentzGroup Λ a ⊗ₜ[ℂ] (φ ∘ₗ repV Λ⁻¹) := rfl

/-!

## The jet derivative

-/

/-- the derivative of components in the jet component space,
  in the direction `μ`: the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative label,
  and likewise on the conjugate components.

  This is right multiplication by the degree-one element `∂_μ` on the
  `DerivAlgebraComplex` factor, leaving the target index untouched. It uses a basis of
  the Lorentz covectors — that is what the index `μ` is — but no basis of `V`. -/
noncomputable def JetComponentSpace.jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace V →ₗ[ℂ] JetComponentSpace V :=
  LinearMap.prodMap
    (TensorProduct.map
      (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)
    (TensorProduct.map
      (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)

@[simp]
lemma JetComponentSpace.jetDeriv_fst_tmul (μ : Fin 1 ⊕ Fin 3)
    (a : DerivAlgebraComplex) (φ : Module.Dual ℂ V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)) :
    (JetComponentSpace.jetDeriv μ (a ⊗ₜ[ℂ] φ, y)).1
      = (a * DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

@[simp]
lemma JetComponentSpace.jetDeriv_snd_tmul (μ : Fin 1 ⊕ Fin 3)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)
    (a : DerivAlgebraComplex) (φ : Module.Dual ℂ (ConjModule V)) :
    (JetComponentSpace.jetDeriv μ (x, a ⊗ₜ[ℂ] φ)).2
      = (a * DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

/-- **Total derivatives commute.** Mixed partials agree because the derivative labels
  live in a *symmetric* algebra; no basis of `V` is involved. -/
lemma JetComponentSpace.jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.jetDeriv (V := V) μ).comp (JetComponentSpace.jetDeriv ν)
      = (JetComponentSpace.jetDeriv (V := V) ν).comp (JetComponentSpace.jetDeriv μ) := by
  have hmul : ∀ b c : DerivAlgebraComplex,
      (LinearMap.mulRight ℂ b).comp (LinearMap.mulRight ℂ c)
        = LinearMap.mulRight ℂ (c * b) :=
    fun b c => LinearMap.ext fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, mul_assoc]
  rw [JetComponentSpace.jetDeriv, JetComponentSpace.jetDeriv, LinearMap.prodMap_comp,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, hmul, hmul, mul_comm]

/-- The element being multiplied in is the degree-one derivative symbol `∂_μ`, the image
  of the dual basis covector under `SymmetricAlgebra.ι`. -/
lemma JetComponentSpace.jetDeriv_eq_ι (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.jetDeriv (V := V) μ
      = LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.mulRight ℂ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
            (Lorentz.complexCoBasis.dualBasis μ))) LinearMap.id)
        (TensorProduct.map
          (LinearMap.mulRight ℂ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
            (Lorentz.complexCoBasis.dualBasis μ))) LinearMap.id) := by
  rw [JetComponentSpace.jetDeriv, DerivAlgebraComplex.basis_singleton]

@[simp]
lemma JetComponentSpace.jetDeriv_fst (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace V) :
    (JetComponentSpace.jetDeriv μ v).1
      = TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.1 := rfl

@[simp]
lemma JetComponentSpace.jetDeriv_snd (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace V) :
    (JetComponentSpace.jetDeriv μ v).2
      = TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.2 := rfl

/-!

## Lorentz covariance of the jet derivative

-/

/-- The covariance of the derivative-symbol multiplication on one tensor factor of the
  component space, for an arbitrary representation on the other factor. -/
private lemma repLorentzGroup_tprod_mulRight_jetSymbol {W : Type*} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ SL(2,ℂ) W) (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (w : DerivAlgebraComplex ⊗[ℂ] W) :
    (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ
      (TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id w) =
    ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id ((DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ w) := by
  have hsym : DerivAlgebraComplex.repLorentzGroup Λ
      (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [DerivAlgebraComplex.basis_singleton, DerivAlgebraComplex.repLorentzGroup_apply_ι,
      Lorentz.CoℂModule.SL2CRep_dual_dualBasis, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, DerivAlgebraComplex.basis_singleton]
  have hrep : ∀ (q : DerivAlgebraComplex) (f : W),
      (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ (q ⊗ₜ[ℂ] f) =
        (DerivAlgebraComplex.repLorentzGroup Λ q) ⊗ₜ[ℂ] (ρ Λ f) := fun _ _ => rfl
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply, hrep, hrep,
      DerivAlgebraComplex.repLorentzGroup_apply_mul, hsym, Finset.mul_sum,
      TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
        mul_smul_comm, TensorProduct.smul_tmul']

/-- **The jet derivative is a Lorentz vector on the component space.** Appending `∂_μ` and
  then acting is acting and then appending the transformed `∂_μ`, which is a combination of
  the `∂_a`. Both halves of the component space are covered by the same argument: the
  derivative label lives in the first tensor factor, and what sits in the second factor —
  `repV.dual` or `repV.conj.dual` — plays no role. -/
lemma JetComponentSpace.repLorentzGroup_jetDeriv (repV : Representation ℂ SL(2,ℂ) V)
    (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace V) :
    JetComponentSpace.repLorentzGroup repV Λ (JetComponentSpace.jetDeriv μ v) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        JetComponentSpace.jetDeriv a (JetComponentSpace.repLorentzGroup repV Λ v) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, JetComponentSpace.repLorentzGroup_fst,
      JetComponentSpace.jetDeriv_fst]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.1
  · simp only [Prod.snd_sum, Prod.smul_snd, JetComponentSpace.repLorentzGroup_snd,
      JetComponentSpace.jetDeriv_snd]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.2

/-!

## Functoriality in the target space

-/

variable {W : Type _} [AddCommGroup W] [Module ℂ W]

/-- **The component space is contravariant in the target space.** A linear map `f : V →ₗ W`
  of target spaces pulls the component functions of a `W`-valued field back to component
  functions of a `V`-valued field: a component function is a *covector* on the target, so it
  transposes. The derivative label is untouched, and the conjugate half transposes the
  conjugate of `f`. -/
noncomputable def JetComponentSpace.comap (f : V →ₗ[ℂ] W) :
    JetComponentSpace W →ₗ[ℂ] JetComponentSpace V :=
  LinearMap.prodMap
    (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
    (TensorProduct.map LinearMap.id (Module.Dual.transpose (ConjModule.map f)))

@[simp]
lemma JetComponentSpace.comap_fst_tmul (f : V →ₗ[ℂ] W) (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ W) (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule W)) :
    (JetComponentSpace.comap f (a ⊗ₜ[ℂ] φ, y)).1 = a ⊗ₜ[ℂ] (φ ∘ₗ f) := rfl

@[simp]
lemma JetComponentSpace.comap_snd_tmul (f : V →ₗ[ℂ] W)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ W) (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ (ConjModule W)) :
    (JetComponentSpace.comap f (x, a ⊗ₜ[ℂ] φ)).2 = a ⊗ₜ[ℂ] (φ ∘ₗ ConjModule.map f) := rfl

@[simp]
lemma JetComponentSpace.comap_id :
    JetComponentSpace.comap (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  rw [JetComponentSpace.comap,
    show Module.Dual.transpose (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id from rfl,
    show ConjModule.map (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id from rfl,
    show Module.Dual.transpose (LinearMap.id : ConjModule V →ₗ[ℂ] ConjModule V)
      = LinearMap.id from rfl, TensorProduct.map_id, TensorProduct.map_id]
  rfl

/-- Functoriality: pulling back along `g ∘ f` is pulling back along `g` and then along `f`.
  The order reverses, as it must for a contravariant construction. -/
lemma JetComponentSpace.comap_comp {U : Type _} [AddCommGroup U] [Module ℂ U]
    (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] U) :
    JetComponentSpace.comap (g.comp f)
      = (JetComponentSpace.comap f).comp (JetComponentSpace.comap g) := by
  rw [JetComponentSpace.comap, JetComponentSpace.comap, JetComponentSpace.comap,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp]
  rfl

/-- **The pullback commutes with the jet derivative.** The two act on different tensor
  factors — the derivative label and the target index — so an inclusion of species is a map
  of differential algebras. -/
lemma JetComponentSpace.comap_jetDeriv (f : V →ₗ[ℂ] W) (μ : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.jetDeriv μ)
      = (JetComponentSpace.jetDeriv μ).comp (JetComponentSpace.comap f) := by
  rw [JetComponentSpace.comap, JetComponentSpace.jetDeriv, JetComponentSpace.jetDeriv,
    LinearMap.prodMap_comp, LinearMap.prodMap_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.comp_id, LinearMap.id_comp]

/-!

## The mass-weight scaling

The mass dimension is tracked multiplicatively, through a scaling action: for a field of
*mass weight* `w` — twice the mass dimension, kept integral so that fermions of dimension
`3/2` carry weight `3` — the generator `∂_s φ_α` scales by `c ^ (w + 2 |s|)`, one factor
of `c ^ 2` per derivative. The scaling on the component space below lifts functorially to
the bosonic and fermionic algebras, where it defines their mass-dimension grading.

-/

/-- The mass-weight scaling on the jet component space of a field of mass weight `w`
  (twice the mass dimension): the generator `∂_s φ_α` and its conjugate are scaled by
  `c ^ (w + 2 |s|)`, through the derivative-degree scaling `DerivAlgebraComplex.gradeScale`
  on the derivative label. -/
noncomputable def JetComponentSpace.massWeightScale (w : ℕ) (c : ℂ) :
    JetComponentSpace V →ₗ[ℂ] JetComponentSpace V :=
  c ^ w • LinearMap.prodMap
    (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id)
    (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id)

/-- On an unconjugated component function `∂_s φ_α` the mass-weight scaling is
  multiplication by `c ^ (w + 2 |s|)`. -/
lemma JetComponentSpace.massWeightScale_fst_basis_tmul (w : ℕ) (c : ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)) :
    (JetComponentSpace.massWeightScale w c
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, y) : JetComponentSpace V)).1
      = c ^ (w + 2 * Multiset.card s) • (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) := by
  simp only [massWeightScale, LinearMap.smul_apply, Prod.smul_fst, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, DerivAlgebraComplex.gradeScale_basis,
    LinearMap.id_apply, TensorProduct.smul_tmul', ← pow_mul, pow_add, mul_smul,
    mul_comm 2 (Multiset.card s)]

@[simp]
lemma JetComponentSpace.massWeightScale_fst (w : ℕ) (c : ℂ) (v : JetComponentSpace V) :
    (JetComponentSpace.massWeightScale w c v).1
      = c ^ w • TensorProduct.map
          (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.1 := rfl

@[simp]
lemma JetComponentSpace.massWeightScale_snd (w : ℕ) (c : ℂ) (v : JetComponentSpace V) :
    (JetComponentSpace.massWeightScale w c v).2
      = c ^ w • TensorProduct.map
          (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.2 := rfl

/-- The derivative-degree scaling intertwines multiplication by a single derivative
  symbol up to one factor of the scaling parameter, on either half of the component
  space. -/
private lemma gradeScale_map_mulRight_basis {W : Type*} [AddCommGroup W] [Module ℂ W]
    (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : DerivAlgebraComplex ⊗[ℂ] W) :
    TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id
      (TensorProduct.map (LinearMap.mulRight ℂ
        (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id x)
    = c ^ 2 • TensorProduct.map (LinearMap.mulRight ℂ
        (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | tmul a y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, map_mul, DerivAlgebraComplex.gradeScale_basis,
      Multiset.card_singleton, pow_one, mul_smul_comm, TensorProduct.smul_tmul']

/-- **The total derivative carries mass weight two** on the component space: the scaling
  intertwines the derivative shift up to a factor `c ^ 2`. -/
lemma JetComponentSpace.massWeightScale_jetDeriv (w : ℕ) (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.massWeightScale (V := V) w c).comp (JetComponentSpace.jetDeriv μ)
      = c ^ 2 • (JetComponentSpace.jetDeriv μ).comp
          (JetComponentSpace.massWeightScale w c) := by
  have key := fun {W : Type _} [AddCommGroup W] [Module ℂ W]
      (x : DerivAlgebraComplex ⊗[ℂ] W) => gradeScale_map_mulRight_basis c μ x
  refine LinearMap.ext fun v => Prod.ext ?_ ?_
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_fst,
      JetComponentSpace.massWeightScale_fst, JetComponentSpace.jetDeriv_fst, map_smul]
    exact (congrArg (fun z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V => c ^ w • z)
      (key v.1)).trans (smul_comm _ _ _)
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_snd,
      JetComponentSpace.massWeightScale_snd, JetComponentSpace.jetDeriv_snd, map_smul]
    exact (congrArg (fun z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V) =>
      c ^ w • z) (key v.2)).trans (smul_comm _ _ _)

/-!

## The component space of a direct sum

-/

/-- **The component space of a direct sum splits.** The component functions of a
  `(V × W)`-valued field are those of a `V`-valued field together with those of a
  `W`-valued field: the dual and the conjugate both distribute over the finite product, and
  the derivative label is untouched. -/
noncomputable def JetComponentSpace.prodEquiv (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    JetComponentSpace (V × W) ≃ₗ[ℂ] JetComponentSpace V × JetComponentSpace W :=
  (LinearEquiv.prodCongr
      (TensorProduct.congr (LinearEquiv.refl ℂ DerivAlgebraComplex)
        (Module.dualProdDualEquivDual ℂ V W).symm)
      (TensorProduct.congr (LinearEquiv.refl ℂ DerivAlgebraComplex)
        (((ConjModule.prodEquiv (k := ℂ) (M := V) (N := W)).symm.dualMap).trans
          (Module.dualProdDualEquivDual ℂ (ConjModule V) (ConjModule W)).symm))).trans <|
    (LinearEquiv.prodCongr (TensorProduct.prodRight ℂ ℂ _ _ _)
        (TensorProduct.prodRight ℂ ℂ _ _ _)).trans
      (LinearEquiv.prodProdProdComm ℂ _ _ _ _)
