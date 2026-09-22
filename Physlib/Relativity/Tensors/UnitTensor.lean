/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Constructors
/-!

# The unit tensors

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
attribute [-simp] LinearEquiv.cast_apply

open Tensor

/-- The unit tensor associated with a color `c`. -/
noncomputable def unitTensor (c : C) : S.Tensor ![S.τ c, c] :=
  fromConstPair (S.unit c)

/-- A component of the unit tensor is the corresponding component of the unit intertwiner in the
tensor-product basis. -/
lemma unitTensor_basis_repr (c : C) (φ : ComponentIdx (S := S) ![S.τ c, c]) :
    (Tensor.basis _).repr (unitTensor (S := S) c) φ =
      (Module.Basis.tensorProduct (b (S.τ c)) (b c)).repr ((S.unit c) (1 : k))
        (φ 0, φ 1) := by
  rw [unitTensor, fromConstPair, fromPairT_basis_repr]

lemma unitTensor_congr {c c1 : C} (h : c = c1) :
    unitTensor c = permT id (by simp [h]) (unitTensor (S := S) c1) := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The unit tensor is symmetric on dualing the color. -/
lemma unitTensor_eq_permT_dual (c : C) :
    S.unitTensor c = permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
    (unitTensor (S.τ c)) := by
  rw [unitTensor, fromConstPair, S.unit_symm]
  rw [unitTensor, fromConstPair]
  simp [fromPairT]
  generalize (S.unit (S.τ c)) 1 = u at *
  induction' u using TensorProduct.inductionOn with x y
  · simp [fromSingleT_map]
    generalize (fromSingleT (S := S) y) = y at *
    generalize (fromSingleT (S := S) x) = x at *
    induction' y using induction_on_pure with p
    · induction' x using induction_on_pure with x r t
      · simp [permT_pure]
        repeat rw [prodT_pure, permT_pure]
        congr 1
        ext i
        fin_cases i
        · rfl
        · rfl
      · simp_all
      · simp_all
    · simp_all
    · simp_all
  · simp_all

set_option backward.isDefEq.respectTransparency false in
lemma dual_unitTensor_eq_permT_unitTensor (c : C) :
    S.unitTensor (S.τ c) = permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
      (unitTensor c) := by
  rw [unitTensor_eq_permT_dual]
  rw [unitTensor_congr (by simp : c = S.τ (S.τ c))]
  simp

lemma unit_fromSingleTContrFromPairT_eq_fromSingleT {c : C} (x : V c) :
    fromSingleTContrFromPairT x ((S.unit c) (1 : k)) =
    fromSingleT x := by
  conv_rhs => rw [← S.contr_unit c x]
  rfl

/-- This lemma represents the de-categorification of `S.contr_unit`. -/
@[simp]
lemma contrT_single_unitTensor {c : C} (x : Tensor S ![c]) :
    contrT 1 0 1 (by simp; rfl) (prodT x (unitTensor c)) =
    permT id (by simp; rfl) x := by
  obtain ⟨x, rfl⟩ := fromSingleT.surjective x
  rw [unitTensor, fromConstPair, contrT_fromSingleT_fromPairT]
  congr 1
  rw [← unit_fromSingleTContrFromPairT_eq_fromSingleT x]

set_option backward.isDefEq.respectTransparency false in
lemma contrT_unitTensor_dual_single {c : C} (x : Tensor S ![S.τ c]) :
    contrT 1 1 2 (by simp; rfl) (prodT (unitTensor c) x) =
    permT id (by simp; rfl) x := by
  rw [unitTensor_eq_permT_dual]
  rw [prodT_permT_left]
  rw [contrT_permT]
  rw [prodT_swap]
  rw [contrT_permT]
  rw [permT_permT]
  conv_lhs =>
    enter [2]
    change contrT 1 1 0 _ _
    rw [contrT_symm]
  rw [contrT_single_unitTensor]
  rw [permT_permT]
  conv_lhs =>
    rw (transparency := .instances) [permT_permT]
  apply permT_congr
  · ext i
    fin_cases i
    rfl
  · rfl

@[simp]
lemma unitTensor_invariant {c : C} (g : G) :
    g • S.unitTensor c = S.unitTensor c := by
  rw [unitTensor, actionT_fromConstPair]

end TensorSpecies
