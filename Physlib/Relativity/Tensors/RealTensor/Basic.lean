/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Metrics.Pre
public import Physlib.Relativity.Tensors.Elab
public import Physlib.Relativity.Tensors.Conjugation.Basic
/-!

## Real Lorentz tensors

Within this directory `Pre` is used to denote that the definitions are preliminary and
which are used to define `realLorentzTensor`.

-/

@[expose] public section

open Matrix
open MatrixGroups
open TensorProduct

namespace realLorentzTensor

set_option backward.isDefEq.respectTransparency false in
/-- The colors associated with real representations of O(1, 3) of interest to physics. -/
inductive Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color
deriving Fintype

/-- Color for real Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h

/-- The modules associated with each of the different types of real Lorentz vector space. -/
abbrev modules (d : ℕ) : Color → Type
  | Color.up => Lorentz.ContrMod d
  | Color.down => Lorentz.CoMod d

instance modulesAddCommGroup (d : ℕ) : ∀ c, AddCommGroup (modules d c)
  | Color.up => inferInstance
  | Color.down => inferInstance

instance modulesModule (d : ℕ) : ∀ c, Module ℝ (modules d c)
  | Color.up => inferInstance
  | Color.down => inferInstance

end realLorentzTensor

TODO "Replace Lorentz.ContrMod and Lorentz.CoMod in the definition of realLorentzTensor
  directly with Lorentz.Vector and Lorentz.Covector, and
  representations defined on them."

noncomputable section
open realLorentzTensor in
/-- The tensor structure for real Lorentz tensors. -/
def realLorentzTensor (d : ℕ := 3) : TensorSpecies
    ℝ realLorentzTensor.Color (LorentzGroup d)
    (fun | Color.up => Lorentz.ContrMod d | Color.down => Lorentz.CoMod d)
    (fun _ => Fin 1 ⊕ Fin d)
    (fun | Color.up => Lorentz.ContrMod.rep | Color.down => Lorentz.CoMod.rep)
    (fun | Color.up => Lorentz.contrBasis d | Color.down => Lorentz.coBasis d) where
  τ := fun c =>
    match c with
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.up => rfl
    | Color.down => rfl
  contr := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract
    | Color.down => Lorentz.coContrContract
  unit := fun c =>
    match c with
    | Color.up => Lorentz.preCoContrUnit d
    | Color.down => Lorentz.preContrCoUnit d
  contr_tmul_symm := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract_tmul_symm
    | Color.down => Lorentz.coContrContract_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.up => Lorentz.contr_preCoContrUnit
    | Color.down => Lorentz.contr_preContrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.up => Lorentz.preCoContrUnit_symm
    | Color.down => Lorentz.preContrCoUnit_symm


open realLorentzTensor in
/-- The real Lorentz tensors as a conjugation species: over `ℝ` conjugation is trivial, so every
  colour is its own conjugate. -/
def realLorentzConjTensor (d : ℕ := 3) : ConjTensorSpecies ℝ Color (LorentzGroup d)
    (modules d) (fun _ => Fin 1 ⊕ Fin d)
    (fun | Color.up => Lorentz.ContrMod.rep | Color.down => Lorentz.CoMod.rep)
    (fun | Color.up => Lorentz.contrBasis d | Color.down => Lorentz.coBasis d) where
  toTensorSpecies := realLorentzTensor d
  bar := id
  bar_involution _ := rfl
  bar_tau _ := rfl
  barIdx_eq _ := rfl
  conj_basis_equivariant _ _ _ _ := by simp
  conj_contrComm _ _ _ := by simp [TensorSpecies.basisIdxCongr]

namespace realLorentzTensor

/-- The Minkowski metric of the real Lorentz tensors, on both vector colors. -/
instance instWithMetric (d : ℕ) : (realLorentzTensor d).WithMetric where
  metric := fun c =>
    match c with
    | Color.up => Lorentz.preContrMetric d
    | Color.down => Lorentz.preCoMetric d
  contr_metric := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract_apply_metric
    | Color.down => Lorentz.coContrContract_apply_metric

/-- Notation for a real Lorentz tensor. -/
syntax (name := realLorentzTensorSyntax) "ℝT[" term,* "]" : term

macro_rules
  | `(ℝT[$termDim:term, $term:term, $terms:term,*]) =>
      `(((realLorentzTensor $termDim).Tensor (vecCons $term ![$terms,*])))
  | `(ℝT[$termDim:term, $term:term]) =>
    `(((realLorentzTensor $termDim).Tensor (vecCons $term ![])))
  | `(ℝT[$termDim:term]) =>`(((realLorentzTensor $termDim).Tensor (vecEmpty)))
  | `(ℝT[]) =>`(((realLorentzTensor 3).Tensor (vecEmpty)))

set_option quotPrecheck false in
/-- Notation for a real Lorentz tensor. -/
scoped[realLorentzTensor] notation "ℝT(" d "," c ")" =>
  (realLorentzTensor d).Tensor c

/-!

## Basis and discrete functor objects

These re-express fields of `realLorentzTensor d` in terms of `Lorentz` data.

-/

@[simp]
lemma basisIdxCongr_eq_refl {d : ℕ} {c1 c2 : realLorentzTensor.Color} (h : c1 = c2) :
    TensorSpecies.basisIdxCongr (basisIdx := fun _ => Fin 1 ⊕ Fin d) h = Equiv.refl _ := by
  rfl

lemma basisIdxCongr_apply {d : ℕ} {c1 c2 : realLorentzTensor.Color} (h : c1 = c2)
    (i : Fin 1 ⊕ Fin d) :
    TensorSpecies.basisIdxCongr (basisIdx := fun _ => Fin 1 ⊕ Fin d) h i = i := by
  simp

/-!

## Simplifying τ

-/

@[simp]
lemma τ_up_eq_down {d : ℕ} : (realLorentzTensor d).τ Color.up = Color.down := rfl

@[simp]
lemma τ_down_eq_up {d : ℕ} : (realLorentzTensor d).τ Color.down = Color.up := rfl

/-!

## Contractions and to Field

-/

attribute [-simp] Fintype.sum_sum_type
open TensorSpecies Tensor

/-- At every real Lorentz color, the bases at the color and its dual are dual bases, with
labels matched by the identity. -/
lemma isContrDualMatching_refl (c : realLorentzTensor.Color) :
    IsContrDualMatching (realLorentzTensor d) c (Equiv.refl _) := by
  intro x₁ x₂
  cases c
  · exact Lorentz.contrCoContract_basis x₁ x₂
  · exact Lorentz.coContrContract_basis x₁ x₂

/-- Real Lorentz tensors have dual bases under contraction, with the identity matching. -/
instance : HasContrDualBases (realLorentzTensor d) where
  exists_matching c := ⟨_, isContrDualMatching_refl c⟩

/-- The dual-label matching of real Lorentz tensors is the identity. -/
@[simp]
lemma contrDualIdxEquiv_eq_refl (c : realLorentzTensor.Color) :
    HasContrDualBases.contrDualIdxEquiv (realLorentzTensor d) c = Equiv.refl _ :=
  HasContrDualBases.contrDualIdxEquiv_eq_of_isContrDualMatching (isContrDualMatching_refl c)

lemma contrPCoeff_basis {d n : ℕ} {c : Fin n → realLorentzTensor.Color} (i j : Fin n)
    (hij : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j)
    (b : ComponentIdx (S := realLorentzTensor d) c) :
    Pure.contrPCoeff i j hij (Pure.basisVector c b) = if b i = b j then 1 else 0 := by
  rw [Pure.contrPCoeff_basisVector, contrDualIdxEquiv_eq_refl]
  rfl

lemma contrT_eq_sum_evalT {n} {d} (c : Fin (n + 1 + 1) → Color) (i j : Fin (n + 1 + 1))
    (h : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j) (t : ℝT(d, c)) :
    contrT n i j h t = ∑ (μ : Fin 1 ⊕ Fin d), permT id (by
      simp [Fin.succSuccAbove_eq_predAbove h.1])
      (evalT ((Fin.predAbove 0 i).predAbove j) μ (evalT i μ t)) := by
  induction' t using Tensor.induction_on_basis with b r t h t1 t2 h1 h2
  · rw [contrT_basis]
    simp only [contrPCoeff_basis, ite_smul, one_smul, zero_smul]
    conv_rhs =>
      enter [2, μ];
      simp only [evalT_basis, Fin.zero_succAbove, apply_ite, Fin.succ_zero_eq_one, map_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have h0 : i.succAbove ((Fin.predAbove 0 i).predAbove j) = j := by
      rcases i.eq_zero_or_eq_succ with rfl | ⟨k, rfl⟩
      · exact Fin.succAbove_predAbove (Ne.symm h.1)
      · rw [Fin.predAbove_zero_succ]
        exact Fin.succ_succAbove_predAbove (Ne.symm h.1)
    rw [h0]
    split_ifs with h₁ _ h₂
    · rw [permT_basis]
      congr
      ext x
      simp only [Function.comp_apply, ComponentIdx.dropPair, id_eq, basisIdxCongr_eq_refl,
        Equiv.refl_apply]
      rw [Fin.succSuccAbove_eq_predAbove h.1]
    · symm at h₁; contradiction
    · symm at h₂; contradiction
    · rfl
  · simp
  · simp [Finset.smul_sum, h]
  · simp [h1, h2, Finset.sum_add_distrib]

lemma contrT_toScalar {d} (c : Fin 2 → Color)
    (h : 0 ≠ 1 ∧ (realLorentzTensor d).τ (c 0) = c 1) (t : ℝT(d, c)) :
    (contrT 0 0 1 h t).toScalar = ∑ (μ : Fin 1 ⊕ Fin d), {t | [μ] [μ]}ᵀ.toScalar := by
  rw [contrT_eq_sum_evalT, map_sum]
  congr
  ext μ
  simp only [toScalar_permT]
  rfl

open ComponentIdx in
lemma contrT_basis_repr_apply_eq_fin {n d: ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)}
    {h : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j}
    (t : ℝT(d,c)) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j)) :
    (basis (c ∘ Fin.succSuccAbove i j)).repr (contrT n i j h t) b =
    ∑ (x : Fin 1 ⊕ Fin d), ((basis c).repr t
    (DropPairSection.ofFinEquiv h.1 b ⟨x, x⟩)) := by
  rw [contrT_basis_repr_apply_eq_sum_dual, contrDualIdxEquiv_eq_refl]
  rfl

end realLorentzTensor
end
