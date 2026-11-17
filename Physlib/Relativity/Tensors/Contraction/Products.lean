/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.Product
/-!

# The interaction of contractions and products

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
attribute [-simp] LinearEquiv.cast_apply

namespace Tensor

/-!

## Products and contractions

-/

lemma Pure.contrPCoeff_natAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.natAdd n1 i) (Fin.natAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p1.prodP p) = contrPCoeff i j hij p := by
  simp only [contrPCoeff, prodP_apply_natAdd]
  generalize_proofs ha hb hc hd he
  generalize p i = pi at *
  generalize p j = pj at *
  generalize c i = ci at *
  generalize c j = cj at *
  subst he
  subst hb
  simp [LinearEquiv.cast_apply]

lemma Pure.contrPCoeff_castAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    contrPCoeff (Fin.castAdd n1 i) (Fin.castAdd n1 j)
    (by simp_all [Fin.ext_iff]) (p.prodP p1) = contrPCoeff i j hij p := by
  simp only [contrPCoeff, prodP_apply_castAdd]
  generalize_proofs ha hb hc hd he
  generalize p i = pi at *
  generalize p j = pj at *
  generalize c i = ci at *
  generalize c j = cj at *
  subst he
  subst hb
  simp [LinearEquiv.cast_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_dropPair {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    p1.prodP (dropPair i j hij.1 p) = permP _ (IsReindexing.append_succSuccAbove_natAdd i j)
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
      (by rw [Fin.succSuccAbove_natAdd_apply_castAdd i j])]
    simp [LinearEquiv.cast_apply]
  | Sum.inr m =>
    simp only [finSumFinEquiv_apply_right]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 (i.succSuccAbove j m))
      (by rw [Fin.succSuccAbove_comm_natAdd i j])]
    simp [LinearEquiv.cast_apply]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_contrP_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (p1 : Pure S c1) :
    prodT p1.toTensor (contrP i j hij p) =
    ((permT id (IsReindexing.append_succSuccAbove_natAdd i j)) <|
    contrP (Fin.natAdd n1 i) (Fin.natAdd n1 j) (by simpa using hij) <|
    prodP p1 p) := by
  simp only [contrP, map_smul, Nat.add_eq]
  rw [contrPCoeff_natAdd i j hij]
  rw [prodT_pure]
  rw [prodP_dropPair _ _ hij]
  generalize_proofs ha hb hc hd
  rw [LinearMap.map_smul]
  congr
  rw [permT_pure]

set_option backward.isDefEq.respectTransparency false in
lemma prodT_contrT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    prodT t1 (contrT n i j hij t) =
    ((permT id (IsReindexing.append_succSuccAbove_natAdd i j)) <|
    contrT _ (Fin.natAdd n1 i) (Fin.natAdd n1 j)
      (by simpa using hij) <| prodT t1 t) := by
  generalize_proofs ha hb hc hd
  let P (t : Tensor S c) (t1 : Tensor S c1) : Prop :=
    prodT t1 (contrT _ i j hij t) =
    ((permT id (IsReindexing.append_succSuccAbove_natAdd i j)) <|
    contrT _
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j)) hc <|
    prodT t1 t)
  let P1 (t : Tensor S c) := P t t1
  change P1 t
  apply induction_on_pure
  · intro p
    let P2 (t1 : Tensor S c1) := P p.toTensor t1
    change P2 t1
    apply induction_on_pure
    · intro p1
      simp only [Nat.add_eq, finSumFinEquiv_apply_right, contrT_pure, P2, P]
      rw [Pure.prodP_contrP_snd, prodT_pure, contrT_pure]
      rfl
    · intro r t h1
      simp_all only [map_smul, LinearMap.smul_apply, P2, P]
    · intro t1 t2 h1 h2
      simp_all only [map_add, LinearMap.add_apply, P2, P]
  · intro r t h1
    simp_all only [map_smul, P1, P]
  · intro t1 t2 h1 h2
    simp_all only [map_add, P1, P]

lemma contrT_prodT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C} (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    (contrT _ (i.natAdd n1) (j.natAdd n1) (by simpa using hij) <| prodT t1 t) =
    ((permT id (IsReindexing.on_id_symm (IsReindexing.append_succSuccAbove_natAdd i j))) <|
      (prodT t1 (contrT n i j hij t))) := by
  rw [prodT_contrT_snd]
  simp

/-- A contraction internal to the left factor commutes past the outer product with a right
  spectator. The mirror of `prodT_contrT_snd`, obtained from it by `prodT_swap`, so the right-hand
  side contracts the swapped product `prodT t1 t` and carries a block swap. -/
lemma prodT_contrT_fst {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (t : Tensor S c) (t1 : Tensor S c1) :
    prodT (contrT n i j hij t) t1 =
    permT _ IsReindexing.append_swap
      (permT id (IsReindexing.append_succSuccAbove_natAdd i j) <|
      contrT _
        (Fin.natAdd n1 i)
        (Fin.natAdd n1 j)
        (by simpa using hij) <|
      prodT t1 t) := by
  rw [prodT_swap, prodT_contrT_snd]

end Tensor

end TensorSpecies
