/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Constructors
public import Physlib.Relativity.Tensors.ComponentIdx.Single
public import Physlib.Relativity.Tensors.Contraction.Basis
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

/-- For a species with dual bases at dual colours, the unit tensor's components are a Kronecker δ,
  the first label carried across the variance dual by `contrDualIdxEquiv`. -/
lemma unitTensor_pair_basis_repr [HasContrDualBases S] (c : C) (J y : basisIdx c) :
    (basis ![S.τ c, c]).repr (unitTensor c)
        (ComponentIdx.pair.symm ((HasContrDualBases.contrDualIdxEquiv S c).symm J, y)) =
      if J = y then 1 else 0 := by
  -- Contract the unit tensor against the basis vector `J` (`contrT_single_unitTensor`) and read the
  -- result in components. The output slot has colour `c` only after `Fin.append` and
  -- `Fin.succSuccAbove` reduce; `hz` names that equality.
  have hz : ∀ m : Fin 1, c = (Fin.append ![c] ![S.τ c, c] ∘ Fin.succSuccAbove 0 1) m :=
    fun m => by fin_cases m; rfl
  have key := congrArg (fun t => (basis (S := S)
        (Fin.append ![c] ![S.τ c, c] ∘ Fin.succSuccAbove 0 1)).repr t
        (fun m => basisIdxCongr (hz m) y))
      (contrT_single_unitTensor (S := S) (c := c) (basis ![c] (ComponentIdx.single.symm J)))
  rw [contrT_basis_repr_apply_eq_sum_dual,
    permT_basis_repr_of_id (σ := id) (fun i => id_eq i)] at key
  simp only [prodT_basis_repr_apply, Module.Basis.repr_self, Finsupp.single_apply] at key
  refine Eq.trans ?_ (key.trans ?_)
  · refine Eq.trans ?_ (Finset.sum_eq_single J ?_ ?_).symm
    · rw [ite_eq_left (by funext i; fin_cases i; rfl), one_mul]
      exact congrArg _ (by funext i; fin_cases i <;> rfl)
    · intro x _ hx
      rw [ite_eq_right fun h => hx (congrFun h 0).symm, zero_mul]
    · exact fun h => absurd (Finset.mem_univ J) h
  · by_cases h : J = y
    · rw [ite_eq_left h, ite_eq_left (by subst h; funext i; fin_cases i; rfl)]
    · rw [ite_eq_right h, ite_eq_right fun hc => h (congrFun hc 0)]

set_option backward.isDefEq.respectTransparency false in
/-- `unitTensor_pair_basis_repr` at an arbitrary component index. -/
lemma unitTensor_basis_repr_eq_ite [HasContrDualBases S] (c : C)
    (φ : ComponentIdx (S := S) ![S.τ c, c]) :
    (basis ![S.τ c, c]).repr (unitTensor c) φ =
      if HasContrDualBases.contrDualIdxEquiv S c (φ 0) = φ 1 then 1 else 0 := by
  have hφ : ComponentIdx.pair.symm
      ((HasContrDualBases.contrDualIdxEquiv S c).symm
        (HasContrDualBases.contrDualIdxEquiv S c (φ 0)), φ 1) = φ := by
    rw [Equiv.symm_apply_apply]
    exact (ComponentIdx.pair (S := S)).symm_apply_apply φ
  conv_lhs => rw [← hφ]
  exact unitTensor_pair_basis_repr c _ (φ 1)

namespace Tensor

/-- The component matrix of a unit tensor recoloured without moving its slots is the identity, with
  the labels transported back to the unit tensor's colours. -/
lemma matrixOfCs_permT_unitTensor [HasContrDualBases S] (c : C) {cs : Fin 2 → C}
    {σ : Fin 2 → Fin 2} (hσ : ∀ i, σ i = i) (hperm : IsReindexing ![S.τ c, c] cs σ) :
    matrixOfCs (permT σ hperm (unitTensor (S := S) c)) =
      (1 : Matrix (basisIdx c) (basisIdx c) k).submatrix
        (fun x => HasContrDualBases.contrDualIdxEquiv S c
          (basisIdxCongr (by rw [← hperm.2 0, hσ]; rfl) x))
        (fun y => basisIdxCongr (by rw [← hperm.2 1, hσ]; rfl) y) := by
  ext x y
  rw [matrixOfCs_apply, permT_basis_repr_of_id hσ, unitTensor_basis_repr_eq_ite,
    Matrix.submatrix_apply, Matrix.one_apply]
  simp only [ComponentIdx.pair_symm_apply_zero, ComponentIdx.pair_symm_apply_one]
  congr 1

/-- The unit tensor's component matrix is the identity, carried along `contrDualIdxEquiv`. -/
lemma matrixOf_unitTensor [HasContrDualBases S] (c : C) :
    matrixOf (unitTensor (S := S) c) =
      (1 : Matrix (basisIdx c) (basisIdx c) k).submatrix
        ⇑(HasContrDualBases.contrDualIdxEquiv S c) id := by
  ext x y
  rw [matrixOf_apply, unitTensor_basis_repr_eq_ite, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
  simp only [ComponentIdx.pair_symm_apply_zero, ComponentIdx.pair_symm_apply_one]
  exact if_congr (Eq.congr (congrArg _ (basisIdxCongr_rfl _ x)) (basisIdxCongr_rfl _ y)) rfl rfl

end Tensor

end TensorSpecies
