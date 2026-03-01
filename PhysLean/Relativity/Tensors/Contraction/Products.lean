/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Contraction.Basic
import PhysLean.Relativity.Tensors.Product
/-!

# The interaction of contractions and products

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

/-!

## Products and contractions

-/

lemma Pure.dropPairEmb_apply_lt_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) (hi : m.val < i.val) (hj : m.val < j.val) :
    dropPairEmb i j m = m.castSucc.castSucc := by
  rcases Fin.eq_self_or_eq_succAbove i j with hj' | hj'
  · subst hj'
    simp at hij
  obtain ⟨j, rfl⟩ := hj'
  rw [dropPairEmb_succAbove]
  simp only [Function.comp_apply]
  have hj'' : m.val < j.val := by
    simp_all only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, ne_eq]
    by_cases hj : j.val < i.val
    · simp_all
    · simp_all only [ite_false, Fin.val_succ, not_lt]
      omega
  rw [Fin.succAbove_of_succ_le, Fin.succAbove_of_succ_le]
  · simp only [Fin.le_def, Fin.val_succ]
    omega
  · simp_all only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, ne_eq, ite_true, Fin.le_def,
    Fin.val_succ]
    omega

lemma Pure.dropPairEmb_natAdd_apply_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n1) :
    (dropPairEmb (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    (Fin.castAdd n m)
    = Fin.castAdd (n + 1 + 1) (m) := by
  rw [dropPairEmb_apply_lt_lt]
  · simp [Fin.ext_iff]
  · simp_all [Fin.ne_iff_vne]
  · simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega

lemma Pure.dropPairEmb_natAdd_image_range_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    (dropPairEmb (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j)) ''
    (Set.range (Fin.castAdd (m := n) (n := n1))) = {i | i.1 < n1} := by
  ext a
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
  conv_lhs =>
    enter [1, b]
    rw [dropPairEmb_natAdd_apply_castAdd i j hij]
  apply Iff.intro
  · intro h
    obtain ⟨b, rfl⟩ := h
    simp
  · intro h
    use ⟨a, by omega⟩
    simp

lemma Pure.dropPairEmb_comm_natAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    (dropPairEmb (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    (Fin.natAdd n1 m)
    = Fin.natAdd (n1) (dropPairEmb i j m) := by
  let f : Fin n ↪o Fin (n1 + n + 1 + 1) :=
    ⟨⟨(dropPairEmb (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    ∘ Fin.natAdd n1, by
      intro i j
      simp only [Function.comp_apply, dropPairEmb_eq_iff_eq]
      simp [Fin.ext_iff]⟩, by
      intro a b
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply, dropPairEmb_leq_iff_leq]
      rw [Fin.le_def, Fin.le_def]
      simp⟩
  let g : Fin n ↪o Fin (n1 + n + 1 + 1) :=
      ⟨⟨(Fin.natAdd (n1) ∘ dropPairEmb i j), by
      intro a b
      simp only [Function.comp_apply, Fin.ext_iff, Fin.val_natAdd, add_right_inj]
      simp [← Fin.ext_iff]⟩, by
      intro a b
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
      rw [Fin.le_def, Fin.le_def]
      simp⟩
  have hcastRange : Set.range (Fin.castAdd (m := n) (n := n1)) = {i | i.1 < n1} := by
    rw [@Set.range_eq_iff]
    apply And.intro
    · intro a
      simp
    · intro b hb
      simp only [Set.mem_setOf_eq] at hb
      use ⟨b, by omega⟩
      simp
  have hnatRange : Set.range (Fin.natAdd (m := n) n1) =
    (Set.range (Fin.castAdd (m := n) (n := n1)))ᶜ := by
    rw [hcastRange]
    rw [@Set.range_eq_iff]
    apply And.intro
    · intro a
      simp
    · intro b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hb
      use ⟨b - n1, by omega⟩
      simp only [Fin.natAdd_mk, Fin.ext_iff]
      omega
  have hfg : f = g := by
    rw [← OrderEmbedding.range_inj]
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, f, g]
    rw [Set.range_comp, Set.range_comp]
    simp only [dropPairEmb_range hij]
    rw [hnatRange]
    rw [dropPairEmb_image_compl]
    simp only [Set.compl_union]
    rw [dropPairEmb_natAdd_image_range_castAdd i j hij]
    ext a
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or, Set.mem_setOf_eq, not_lt, Set.mem_image]
    apply Iff.intro
    · intro h
      use ⟨a - n1, by omega⟩
      simp only [Fin.ext_iff, Fin.val_natAdd, Fin.natAdd_mk] at h ⊢
      omega
    · intro h
      obtain ⟨x, h1, rfl⟩ := h
      simp_all [Fin.ext_iff]
    · simp_all [Fin.ext_iff]
  simpa using congrFun (congrArg (fun x => x.toFun) hfg) m

lemma Pure.dropPairEmb_permCond_prod {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) :
    PermCond
      (Fin.append c1 c ∘
        (dropPairEmb (finSumFinEquiv (m := n1) (Sum.inr i))
        (finSumFinEquiv (m := n1) (Sum.inr j))))
      (Fin.append c1 (c ∘ (dropPairEmb i j)))
      id := by
  apply And.intro (Function.bijective_id)
  simp [Fin.forall_fin_add]
  apply And.intro
  · intro m
    rw [dropPairEmb_natAdd_apply_castAdd i j hij.1]
    simp
  · intro m
    rw [dropPairEmb_comm_natAdd i j hij.1]
    simp

lemma Pure.contrPCoeff_natAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.natAdd n1 i) (Fin.natAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p1.prodP p)
    = contrPCoeff i j hij p := by
  simp only [contrPCoeff, Function.comp_apply, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, prodP_apply_natAdd]
  conv_lhs => erw [S.contr_congr _ ((c i)) (by simp)]
  apply congrArg
  congr 1
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) (p i)) = _
    simp [map_map_apply]
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) _) = _
    simp [map_map_apply]

lemma Pure.contrPCoeff_castAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.castAdd n1 i) (Fin.castAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p.prodP p1)
    = contrPCoeff i j hij p := by
  simp only [contrPCoeff, Function.comp_apply, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, prodP_apply_castAdd]
  conv_lhs => erw [S.contr_congr _ ((c i)) (by simp)]
  apply congrArg
  congr 1
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) (p i)) = _
    simp [map_map_apply]
  · change (ConcreteCategory.hom (S.FD.map (Discrete.eqToHom _)))
      ((ConcreteCategory.hom (S.FD.map (eqToHom _))) _) = _
    simp [map_map_apply]

lemma Pure.prodP_dropPair {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    p1.prodP (dropPair i j hij.1 p) = permP id (Pure.dropPairEmb_permCond_prod i j hij)
    (dropPair (Fin.natAdd n1 i) (Fin.natAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p1.prodP p)) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  rw [prodP_apply_finSumFinEquiv]
  simp only [Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, dropPair,
    permP, Nat.add_eq, id_eq]
  match x with
  | Sum.inl x =>
    simp only [finSumFinEquiv_apply_left]
    rw [← congr_right (p1.prodP p) _ (Fin.castAdd (n + 1 + 1) x)
      (by rw [dropPairEmb_natAdd_apply_castAdd i j hij.1])]
    simp [map_map_apply]
  | Sum.inr m =>
    simp only [finSumFinEquiv_apply_right]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 (dropPairEmb i j m))
      (by rw [dropPairEmb_comm_natAdd i j hij.1])]
    simp [map_map_apply]

lemma Pure.prodP_contrP_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    prodT p1.toTensor (contrP i j hij p) =
    ((permT id (Pure.dropPairEmb_permCond_prod i j hij)) <|
    contrP
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <|
    prodP p1 p) := by
  simp only [contrP, map_smul, Nat.add_eq, finSumFinEquiv_apply_right]
  rw [contrPCoeff_natAdd i j hij]
  congr 1
  rw [prodT_pure, permT_pure]
  congr
  rw [prodP_dropPair _ _ hij]

lemma prodT_contrT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    prodT t1 (contrT n i j hij t) =
    ((permT id (Pure.dropPairEmb_permCond_prod i j hij)) <|
    contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <|
    prodT t1 t) := by
  generalize_proofs ha hb hc hd
  let P (t : Tensor S c) (t1 : Tensor S c1) : Prop :=
    prodT t1 (contrT _ i j hij t) =
    ((permT id (Pure.dropPairEmb_permCond_prod i j hij)) <|
    contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j)) hc <|
    prodT t1 t)
  let P1 (t : Tensor S c) := P t t1
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by
      dsimp only [P1, P] at h1
      simp only [h1, map_smul, P1, P])
    (fun t1 t2 h1 h2 => by
      dsimp only [P1, P] at h1 h2
      simp only [h1, h2, map_add, P1, P]) t
  intro p
  let P2 (t1 : Tensor S c1) := P p.toTensor t1
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      dsimp only [P1, P, P2] at h1
      simp only [h1, map_smul, LinearMap.smul_apply, P, P2])
    (fun t1 t2 h1 h2 => by
      dsimp only [P1, P, P2] at h1 h2
      simp only [map_add, LinearMap.add_apply, h1, h2, P2, P]) t1
  intro p1
  simp only [Nat.add_eq, finSumFinEquiv_apply_right, contrT_pure, P2, P]
  rw [Pure.prodP_contrP_snd, prodT_pure, contrT_pure]
  rfl

lemma contrT_prodT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    (contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simpa using hij) <|
    prodT t1 t) =
    ((permT id (PermCond.on_id_symm (Pure.dropPairEmb_permCond_prod i j hij))) <|
      (prodT t1 (contrT n i j hij t))) := by
  rw [prodT_contrT_snd]
  simp

end Tensor

end TensorSpecies
