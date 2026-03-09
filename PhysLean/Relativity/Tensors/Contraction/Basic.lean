/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.Contraction.Pure
/-!

# Contractions on tensors

-/

@[expose] public section

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

/-!

## contrT

-/

open Pure

lemma contrT_decide {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (hx : S.τ (c i) = c j) (hij : i ≠ j := by decide) :
    i ≠ j ∧ S.τ (c i) = c j := by
  apply And.intro hij hx

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a tensor
  `t : Tensor S c`, `contrT i j _ t` is the tensor
  formed by contracting the `i`th index of `t`
  with the `j`th index. -/
noncomputable def contrT (n : ℕ) {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
      (hij : i ≠ j ∧ S.τ (c i) = c j) :
    Tensor S c →ₗ[k] Tensor S (c ∘ dropPairEmb i j) :=
  PiTensorProduct.lift (Pure.contrPMultilinear i j hij)

lemma contrT_congr {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j}
    (i' j' : Fin (n + 1 + 1)) (t : S.Tensor c)
    (hii' : i = i' := by decide)
    (hjj' : j = j' := by decide) :
    contrT n i j hij t = permT id (And.intro (Function.bijective_id) (by subst hii' hjj'; simp))
      (contrT n i' j' (by subst hii' hjj'; exact hij) t) := by
  subst hii' hjj'
  simp

@[simp]
lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    contrT n i j hij p.toTensor = p.contrP i j hij := by
  simp only [contrT, Pure.toTensor]
  change _ = Pure.contrPMultilinear i j hij p
  conv_rhs => rw [← PiTensorProduct.lift.tprod]
  rfl

@[simp]
lemma contrT_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (g : G)
    (t : Tensor S c) :
    contrT n i j hij (g • t) = g • contrT n i j hij t := by
  let P (t : Tensor S c) : Prop := contrT n i j hij (g • t) = g • contrT n i j hij t
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [actionT_pure, contrT_pure]
    simp only [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_smul]
    congr 1
    exact Eq.symm actionT_pure
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr, Tensor.actionT_add]

lemma contrT_permT {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j ∧ S.τ (c1 i) = (c1 j))
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1))
    (hσ : PermCond c c1 σ) (t : Tensor S c) :
    contrT n1 i j hij (permT σ hσ t) = permT (dropPairOfMap i j hij.1 σ hσ.1)
      (permCond_dropPairOfMap i j hij.1 σ hσ)
      (contrT n (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t) := by
  let P (t : Tensor S c) : Prop := contrT n1 i j hij (permT σ hσ t) =
      permT (dropPairOfMap i j hij.1 σ hσ.1)
        (permCond_dropPairOfMap i j hij.1 σ hσ)
        (contrT n (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t)
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [permT_pure, contrT_pure]
    simp only [contrP, contrPCoeff_permP, dropPair_permP, map_smul]
    congr
    rw [permT_pure]
  · intro r t ht
    simp_all [P]
  · intro t1 t2 ht1 ht2
    simp_all [P]

lemma contrT_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} (t : Tensor S c) :
    contrT n i j hij t = permT id (by simp)
      (contrT n j i ⟨hij.1.symm, by simp [← hij.2]⟩ t) := by
  let P (t : Tensor S c) : Prop := contrT n i j hij t = permT id (by simp)
      (contrT n j i ⟨hij.1.symm, by simp [← hij.2]⟩ t)
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [contrP_symm]
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]

lemma contrT_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (dropPairEmb i1 j1 i2)) = (c (dropPairEmb i1 j1 j2)))
    (t : Tensor S c) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    contrT n i2 j2 hij2 (contrT (n + 1 + 1) i1 j1 hij1 t) =
    permT id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1.left hij2.left)
      (contrT n i1' j1' (by simp [i1', j1', i2', j2', hij1])
      (contrT (n + 1 + 1) i2' j2' (by simp [i2', j2', hij2]) t)) := by
  let i2' := (dropPairEmb i1 j1 i2);
  let j2' := (dropPairEmb i1 j1 j2);
  let i1' := (dropPairEmbPre i2' j2' (by simp [i2', j2', hij2]) i1
    (by simp [i2', j2']));
  let j1' := (dropPairEmbPre i2' j2' (by simp [i2', j2', hij2]) j1
    (by simp [i2', j2']));
  let P (t : Tensor S c) : Prop := contrT n i2 j2 hij2 (contrT (n + 1 + 1) i1 j1 hij1 t) =
      permT id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1.left hij2.left)
        (contrT n i1' j1' (by simp [i1', j1', i2', j2', hij1])
        (contrT (n + 1 + 1) i2' j2' (by simp [i2', j2', hij2]) t))
  change P t
  apply induction_on_pure
  · intro p
    dsimp only [P]
    conv_lhs => enter [2]; rw [contrT_pure, contrP]
    conv_lhs => rw [map_smul, contrT_pure, contrP, smul_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul, permT_pure]
    conv_rhs => rw [smul_smul]
    congr 1
    · exact contrPCoeff_mul_dropPair i1 j1 i2 j2 hij1 hij2 p
    · congr 1
      rw [dropPair_comm]
  · intro p q hp
    dsimp only [P] at hp ⊢
    conv_lhs => rw [map_smul, map_smul, hp]
    conv_rhs => enter [2, 2]; rw [map_smul]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
  · intro p r hp hr
    dsimp only [P] at hp hr ⊢
    conv_lhs => rw [map_add, map_add, hp]
    conv_lhs => enter [2]; rw [hr]
    conv_rhs => enter [2, 2]; rw [map_add]
    conv_rhs => enter [2]; rw [map_add]
    conv_rhs => rw [map_add]

end Tensor

end TensorSpecies
