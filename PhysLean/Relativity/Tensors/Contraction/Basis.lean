/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Contraction.Basic
/-!

# Contractions on basis tensors

-/

open IndexNotation CategoryTheory MonoidalCategory Module

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

/-!

-/
namespace ComponentIdx

/-- The `ComponentIdx` obtained by dropping two components. -/
def dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (b : ComponentIdx (S := S) c) :
    ComponentIdx (S := S) (c ∘ Pure.dropPairEmb i j) :=
  fun m => b (Pure.dropPairEmb i j m)

/-- Given a coordinate parameter
  `b : Π k, Fin (S.repDim ((c ∘ i.succAbove ∘ j.succAbove) k)))`, the
  coordinate parameter `Π k, Fin (S.repDim (c k))` which map down to `b`. -/
def DropPairSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i : Fin (n + 1 + 1)} {j : Fin (n + 1 + 1)}
    (b : ComponentIdx (S := S) (c ∘ Pure.dropPairEmb i j)) :
    Finset (ComponentIdx (S := S) c) :=
  {b' : ComponentIdx c | dropPair i j b' = b}

namespace DropPairSection

lemma mem_iff_apply_dropPairEmb_eq {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (b' : ComponentIdx c) :
    b' ∈ DropPairSection (S := S) b ↔
      ∀ m, b' (Pure.dropPairEmb i j m) = b m := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [funext_iff]
  simp [dropPair]

@[simp]
lemma mem_self_of_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c)) :
    b ∈ DropPairSection (S := S) (b.dropPair i j) := by
  simp [DropPairSection]

/-- Given a `b` in `ComponentIdx (c ∘ Pure.dropPairEmb i j))` and
  an `x` in `Fin (S.repDim (c i)) × Fin (S.repDim (c j))`, the corresponding
  coordinate parameter in `ComponentIdx c`. -/
def ofFin {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (S := S) (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    ComponentIdx (S := S) c := fun m =>
  if hi : m = i then Fin.cast (by subst hi; rfl) x.1
  else if hj : m = j then Fin.cast (by subst hj; rfl) x.2
  else
    Fin.cast (by simp; rw [Pure.dropPairEmb_dropPairEmbPre])
    (b (Pure.dropPairEmbPre i j hij m (by omega)))

@[simp]
lemma ofFin_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    ofFin hij b x i = x.1 := by
  simp [ofFin]

@[simp]
lemma ofFin_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    ofFin hij b x j = x.2 := by
  simp [ofFin]
  intro h
  omega

lemma ofFin_mem_dropPairEmbSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    ofFin hij b x ∈ DropPairSection b := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  ext m
  simp only [ofFin, dropPair, Pure.dropPairEmb_ne_fst, ↓reduceDIte, Pure.dropPairEmb_ne_snd,
    Function.comp_apply]
  simp only [Fin.val_cast]
  rw [Pure.dropPairEmbPre_dropPairEmb]

/-- The equivalence between `ContrSection b` and
  `Fin (S.repDim (c i)) × Fin (S.repDim (c (i.succAbove j)))`. -/
def ofFinEquiv {n : ℕ} {c : Fin n.succ.succ → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (b : ComponentIdx (c ∘ Pure.dropPairEmb i j)) :
    Fin (S.repDim (c i)) × Fin (S.repDim (c j)) ≃ DropPairSection (S := S) b where
  invFun b' := ⟨b'.1 i, b'.1 j⟩
  toFun x := ⟨ofFin hij b x, ofFin_mem_dropPairEmbSection hij b x⟩
  right_inv b' := by
    ext m
    simp
    rcases Pure.eq_or_exists_dropPairEmb i j hij m with rfl | rfl | ⟨m, rfl⟩
    · simp
    · simp
    · simp [ofFin]
      obtain ⟨b', hb'⟩ := b'
      simp only [mem_iff_apply_dropPairEmb_eq] at hb'
      rw [Pure.dropPairEmbPre_dropPairEmb]
      simp [hb']
  left_inv x := by
    simp

@[simp]
lemma ofFinEquiv_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    (ofFinEquiv hij b x).1 i = x.1 := by
  simp [ofFinEquiv]

@[simp]
lemma ofFinEquiv_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j))
    (x : Fin (S.repDim (c i)) × Fin (S.repDim (c j))) :
    (ofFinEquiv hij b x).1 j = x.2 := by
  simp [ofFinEquiv]

end DropPairSection

end ComponentIdx
open ComponentIdx

lemma Pure.dropPair_basisVector {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx c) :
    Pure.dropPair i j hij (basisVector c b) =
    basisVector (S := S) (c ∘ Pure.dropPairEmb i j) fun m => b (dropPairEmb i j m) := by
  funext l
  simp [dropPair, basisVector]

lemma contrT_basis_repr_apply {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : Tensor S c)
    (b : ComponentIdx (c ∘ Pure.dropPairEmb i j)) :
    (basis (c ∘ Pure.dropPairEmb i j)).repr (contrT n i j h t) b =
    ∑ (b' : DropPairSection b), (basis c).repr t b'.1 *
    S.castToField ((S.contr.app (Discrete.mk (c i))).hom
    (S.basis (c i) (b'.1 i) ⊗ₜ[k] S.basis (S.τ (c i)) (Fin.cast (by rw [h.2]) (b'.1 j)))) := by
  apply induction_on_basis _ _ _ _ t
  · intro b'
    conv_lhs =>
      rw [basis_apply, contrT_pure]
      simp [Pure.contrP, Pure.dropPair_basisVector]
      change if b'.dropPair i j = b then _ else 0
    split_ifs
    · rename_i h
      subst h
      rw [Finset.sum_eq_single ⟨b', by simp⟩]
      · simp [Pure.contrPCoeff, castToField]
        simp [Pure.basisVector]
        rw [S.basis_congr (h.2 : S.τ (c i) = c j)]
        simp
        rfl
      · intro b'' _ hb
        simp only [Basis.repr_self, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
          Action.functorCategoryEquivalence_functor,
          Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj,
          Discrete.functor_obj_eq_as, Function.comp_apply]
        apply mul_eq_zero_of_left
        rw [@MonoidAlgebra.single_apply]
        rw [if_neg]
        by_contra hn
        apply hb
        exact Subtype.coe_eq_of_eq_mk (id (Eq.symm hn))
      · simp
    · symm
      apply Finset.sum_eq_zero
      intro b'' hbf
      apply mul_eq_zero_of_left
      simp only [Basis.repr_self]
      rw [@MonoidAlgebra.single_apply]
      rw [if_neg]
      by_contra hn
      obtain ⟨b'', hb''⟩ := b''
      subst hn
      simp [DropPairSection] at hb''
      rename_i _ hb _
      exact hb hb''
  · simp
  · intro r t h1
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [h1, Finset.mul_sum]
    ring_nf
  · intro t1 t2 h1 h2
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [h1, h2, ← Finset.sum_add_distrib]
    congr 1
    funext x
    rw [← add_mul]

lemma contrT_basis_repr_apply_eq_sum_fin {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : Tensor S c)
    (b : ComponentIdx (c ∘ Pure.dropPairEmb i j)) :
    (basis (c ∘ Pure.dropPairEmb i j)).repr (contrT n i j h t) b =
    ∑ (x1 : Fin (S.repDim (c i))), ∑ (x2 : Fin (S.repDim (c j))),
    (basis c).repr t (DropPairSection.ofFinEquiv h.1 b (x1, x2)).1 *
    S.castToField ((S.contr.app (Discrete.mk (c i))).hom
    (S.basis (c i) x1 ⊗ₜ[k] S.basis (S.τ (c i)) (Fin.cast (by rw [h.2]) x2))) := by
  rw [contrT_basis_repr_apply h t b, ← (DropPairSection.ofFinEquiv h.1 b).sum_comp,
    Fintype.sum_prod_type]
  simp

end Tensor

end TensorSpecies
