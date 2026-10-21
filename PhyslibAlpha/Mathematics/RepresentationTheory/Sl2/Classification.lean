/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Basic

/-!
# Classification of irreducible sl₂ modules

Constructs the primitive-vector string basis and classifies finite-dimensional irreducible modules.

## i. Overview

Mathlib’s primitive-vector formulas give a lowering string of nonzero vectors with distinct
weights. For an irreducible module, its invariant span is the whole space, so the string is a
basis. Comparing its action with the explicit standard module yields a linear equivalence
intertwining the generated Lie subalgebra.

## ii. Key results

- `string_isBasis` constructs the lowering-string basis.
- `finrank_eq_succ` reads off the dimension from the highest weight.
- `classification` identifies an irreducible module with the standard module.

## iii. Table of contents

- A. Primitive strings and classification

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Primitive strings and classification
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    {h e f : L} {m : M} {n : ℕ}

/-- The vectors `m, fm, …, fⁿm` of the primitive-vector string, indexed by `Fin (n+1)`. -/
def stringVecs (f : L) (m : M) (n : ℕ) (k : Fin (n + 1)) : M :=
  (LieModule.toEnd K L M f ^ (k : ℕ)) m

/-- Each vector in a primitive lowering string is a nonzero eigenvector of `h`. -/
lemma string_hasEigenvector [CharZero K] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (k : Fin (n + 1)) :
    (LieModule.toEnd K L M h).HasEigenvector ((n : K) - 2 * (k : ℕ))
      (stringVecs (K := K) f m n k) := by
  refine ⟨?_, P.pow_toEnd_f_ne_zero_of_eq_nat rfl (Nat.lt_succ_iff.mp k.isLt)⟩
  rw [Module.End.mem_eigenspace_iff, LieModule.toEnd_apply_apply]
  exact P.lie_h_pow_toEnd_f k

omit [LieRingModule L M] [LieModule K L M] in
/-- The weights `n - 2k` of a lowering string are pairwise distinct in characteristic zero. -/
lemma string_weight_injective [CharZero K] {n : ℕ} :
    Function.Injective (fun k : Fin (n + 1) => (n : K) - 2 * (k : ℕ)) := by
  intro k₁ k₂ hk
  simp only [sub_right_inj, mul_eq_mul_left_iff] at hk
  rcases hk with hk | hk
  · exact Fin.ext (Nat.cast_injective hk)
  · norm_num at hk

/-- The lowering string is linearly independent because its weights are distinct. -/
lemma string_linearIndependent [CharZero K] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    LinearIndependent K (stringVecs (K := K) f m n) :=
  (LieModule.toEnd K L M h).eigenvectors_linearIndependent'
    (fun k : Fin (n + 1) => (n : K) - 2 * (k : ℕ)) string_weight_injective
    (stringVecs (K := K) f m n) (string_hasEigenvector P)

/-- The span of the primitive-vector string, as a plain `K`-submodule. -/
def stringSpan (f : L) (m : M) (n : ℕ) : Submodule K M :=
  Submodule.span K (Set.range (stringVecs (K := K) f m n))

/-- Every power of the lowering operator lies in the truncated string span. -/
lemma stringPow_mem_span [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (k : ℕ) :
    (LieModule.toEnd K L M f ^ k) m ∈ stringSpan (K := K) f m n := by
  by_cases hk : k ≤ n
  · exact Submodule.subset_span ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · have h0 := P.pow_toEnd_f_eq_zero_of_eq_nat rfl
    have heq : (LieModule.toEnd K L M f ^ k) m =
        (LieModule.toEnd K L M f ^ (k - (n + 1)))
          ((LieModule.toEnd K L M f ^ (n + 1)) m) := by
      rw [← Module.End.mul_apply, ← pow_add]
      congr 2
      omega
    rw [heq, h0, map_zero]
    exact (stringSpan (K := K) f m n).zero_mem

/-- The raising operator preserves the span of a primitive lowering string. -/
lemma lie_e_string_mem [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (k : Fin (n + 1)) :
    ⁅e, stringVecs (K := K) f m n k⁆ ∈ stringSpan (K := K) f m n := by
  rcases eq_or_ne (k : ℕ) 0 with hk | hk
  · have heq : stringVecs (K := K) f m n k = m := by
      simp [stringVecs, hk]
    rw [heq, P.lie_e]
    exact (stringSpan (K := K) f m n).zero_mem
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have heq : stringVecs (K := K) f m n k =
        (LieModule.toEnd K L M f ^ (j + 1)) m := by simp [stringVecs, hj]
    rw [heq, P.lie_e_pow_succ_toEnd_f j]
    exact (stringSpan (K := K) f m n).smul_mem _ (stringPow_mem_span P j)

/-- The raising operator preserves the string span on `f`-powers. -/
lemma lie_f_string_mem [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (k : Fin (n + 1)) :
    ⁅f, stringVecs (K := K) f m n k⁆ ∈ stringSpan (K := K) f m n := by
  change ⁅f, (LieModule.toEnd K L M f ^ (k : ℕ)) m⁆ ∈ _
  rw [P.lie_f_pow_toEnd_f k]
  exact stringPow_mem_span P _

/-- The Cartan operator preserves the string span. -/
lemma lie_h_string_mem {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) (k : Fin (n + 1)) :
    ⁅h, stringVecs (K := K) f m n k⁆ ∈ stringSpan (K := K) f m n := by
  change ⁅h, (LieModule.toEnd K L M f ^ (k : ℕ)) m⁆ ∈ _
  rw [P.lie_h_pow_toEnd_f k]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Each generator of the triple preserves the lowering-string span. -/
lemma lie_generator_string_mem [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K))
    (x : ↥(t.toLieSubalgebra (R := K))) (k : Fin (n + 1)) :
    ⁅x, stringVecs (K := K) f m n k⁆ ∈ stringSpan (K := K) f m n := by
  obtain ⟨c₁, c₂, c₃, hc⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.property
  rw [LieSubalgebra.coe_bracket_of_module, hc, t.lie_e_f]
  simp only [add_lie, smul_lie]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (lie_e_string_mem P k))
    (Submodule.smul_mem _ _ (lie_f_string_mem P k)))
    (Submodule.smul_mem _ _ (lie_h_string_mem P k))

/-- The lowering string spans a submodule for the Lie subalgebra generated by `t`.
The finite-dimensional hypothesis supplies the relation that closes the string after `n + 1`
lowering steps. -/
lemma exists_stringLieSubmodule [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    ∃ N : LieSubmodule K ↥(t.toLieSubalgebra (R := K)) M,
      (N : Submodule K M) = stringSpan f m n := by
  refine ⟨{ __ := stringSpan f m n, lie_mem := ?_ }, rfl⟩
  intro x w hw
  induction hw using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [lie_add]; exact (stringSpan f m n).add_mem hu hv
  | smul c u _ hu => rw [lie_smul]; exact (stringSpan f m n).smul_mem c hu
  | mem u hu =>
    obtain ⟨k, rfl⟩ := hu
    exact lie_generator_string_mem P x k

/-- Irreducibility makes the nonzero lowering-string submodule equal to the whole module. -/
lemma stringSpan_eq_top {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) (N : LieSubmodule K ↥(t.toLieSubalgebra (R := K)) M)
    (hN : (N : Submodule K M) = stringSpan f m n) : N = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hbot | htop
  · exfalso
    apply P.ne_zero
    have hm_mem : m ∈ (N : Submodule K M) := by
      rw [hN]
      exact Submodule.subset_span ⟨⟨0, Nat.succ_pos n⟩, by simp [stringVecs]⟩
    rw [hbot] at hm_mem
    simpa using hm_mem
  · exact htop

/-- In an irreducible module, the lowering string is independent and spans. -/
lemma string_isBasis [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    LinearIndependent K (stringVecs (K := K) f m n) ∧
      Submodule.span K (Set.range (stringVecs (K := K) f m n)) = ⊤ := by
  refine ⟨string_linearIndependent P, ?_⟩
  obtain ⟨N, hN⟩ := exists_stringLieSubmodule P
  have := stringSpan_eq_top P N hN
  rw [this] at hN
  simpa [stringSpan] using hN.symm

/-- Basis theorem, dimension count. -/
lemma finrank_eq_succ [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) :
    Module.finrank K M = n + 1 := by
  obtain ⟨hli, hspan⟩ := string_isBasis P
  have hbasis : Module.Basis (Fin (n + 1)) K M := Module.Basis.mk hli hspan.ge
  simpa using (Module.finrank_eq_card_basis hbasis)

/-- The basis of an irreducible module obtained by lowering a primitive vector. -/
noncomputable def stringBasis [CharZero K] [FiniteDimensional K M]
    {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) : Module.Basis (Fin (n + 1)) K M :=
  Module.Basis.mk (string_isBasis P).1 (string_isBasis P).2.ge

/-- The linear equivalence sending the lowering-string basis to the coordinate basis. -/
noncomputable def stringEquiv [CharZero K] [FiniteDimensional K M]
    {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) : M ≃ₗ[K] StandardSl2Module K n :=
  (stringBasis P).equiv (Pi.basisFun K (Fin (n + 1))) (Equiv.refl _)

/-- The linear equivalence sends each lowering-string vector to the corresponding
coordinate vector. -/
lemma stringEquiv_apply [CharZero K] [FiniteDimensional K M]
    {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K)) (i : Fin (n + 1)) :
    stringEquiv P (stringVecs (K := K) f m n i) = StandardSl2Module.v i := by
  have hb : stringBasis P i = stringVecs (K := K) f m n i := Module.Basis.mk_apply _ _ i
  have hv : Pi.basisFun K (Fin (n + 1)) i = StandardSl2Module.v i := by
    simp [StandardSl2Module.v]
  rw [← hb, ← hv]
  exact (stringBasis P).equiv_apply i (Pi.basisFun K (Fin (n + 1))) (Equiv.refl _)

section StringEquiv

variable [CharZero K] [FiniteDimensional K M] {t : IsSl2Triple h e f}
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M]
    (P : t.HasPrimitiveVectorWith m (n : K))

/-- The raising operators agree at the primitive vector. -/
lemma stringEquiv_e_zero :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅eSub (K := K) t, stringVecs (K := K) f m n 0⁆ =
      ⁅eSub (K := K) t, StandardSl2Module.v (K := K) (n := n) 0⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  change stringEquiv P ⁅e, m⁆ = _
  rw [P.lie_e, map_zero]
  exact (standardSl2ModuleLieRingModule_e_apply_zero (K := K) (n := n) t).symm

/-- The raising operators agree at the string vector with index `j + 1`. -/
lemma stringEquiv_e_succ (j : ℕ) (hj : j < n) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅eSub (K := K) t, stringVecs (K := K) f m n ⟨j + 1, by omega⟩⁆ =
      ⁅eSub (K := K) t, StandardSl2Module.v (K := K) (n := n) ⟨j + 1, by omega⟩⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  change stringEquiv P ⁅e, (LieModule.toEnd K L M f ^ (j + 1)) m⁆ = _
  rw [P.lie_e_pow_succ_toEnd_f j, map_smul,
    show (LieModule.toEnd K L M f ^ j) m = stringVecs (K := K) f m n ⟨j, by omega⟩ from rfl,
    stringEquiv_apply P, standardSl2ModuleLieRingModule_e_apply_pos (K := K) (n := n) t
      ⟨j + 1, by omega⟩ (Nat.succ_pos j)]
  congr 2 <;> simp
  ring

/-- The raising operators agree at every positive string index. -/
lemma stringEquiv_e_pos (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅eSub (K := K) t, stringVecs (K := K) f m n i⁆ =
      ⁅eSub (K := K) t, StandardSl2Module.v (K := K) (n := n) i⁆ := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have key := stringEquiv_e_succ (K := K) P j (by omega)
  rwa [show (⟨j + 1, by omega⟩ : Fin (n + 1)) = i from Fin.ext hj.symm] at key

omit [CharZero K] [FiniteDimensional K M] in
/-- A linear equivalence intertwines two endomorphisms if it does so on a basis. -/
lemma equiv_comm_of_basis {ι V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K M) (Ψ : M ≃ₗ[K] V) (A : M →ₗ[K] M) (B : V →ₗ[K] V)
    (hb : ∀ i, Ψ (A (b i)) = B (Ψ (b i))) (w : M) : Ψ (A w) = B (Ψ w) :=
  congrArg (fun T : M →ₗ[K] V => T w)
    (b.ext hb : Ψ.toLinearMap ∘ₗ A = B ∘ₗ Ψ.toLinearMap)

/-- The coordinate equivalence intertwines `x` once it does so on the string basis. -/
lemma stringEquiv_lie_of_basis (x : ↥(t.toLieSubalgebra (R := K)))
    (hx : letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
      ∀ i, stringEquiv P ⁅x, stringVecs (K := K) f m n i⁆ =
        ⁅x, StandardSl2Module.v (K := K) (n := n) i⁆) (w : M) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅x, w⁆ = ⁅x, stringEquiv P w⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  let := standardSl2ModuleLieModule (K := K) (n := n) t
  refine equiv_comm_of_basis (stringBasis P) (stringEquiv P) (LieModule.toEnd K _ M x)
    (LieModule.toEnd K _ (StandardSl2Module K n) x) (fun i => ?_) w
  simpa [stringBasis, stringEquiv_apply] using hx i

/-- The coordinate equivalence intertwines the raising operator. -/
lemma stringEquiv_e (w : M) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅eSub (K := K) t, w⁆ = ⁅eSub (K := K) t, stringEquiv P w⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  refine stringEquiv_lie_of_basis P _ (fun i => ?_) w
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · obtain rfl : i = 0 := Fin.ext hi
    exact stringEquiv_e_zero P
  · exact stringEquiv_e_pos P i hi

/-- The lowering operators agree at the last string vector. -/
lemma stringEquiv_f_last :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅fSub (K := K) t, stringVecs (K := K) f m n (Fin.last n)⁆ =
      ⁅fSub (K := K) t, StandardSl2Module.v (K := K) (n := n) (Fin.last n)⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  change stringEquiv P ⁅f, (LieModule.toEnd K L M f ^ n) m⁆ = _
  rw [P.lie_f_pow_toEnd_f n, P.pow_toEnd_f_eq_zero_of_eq_nat rfl, map_zero]
  exact (standardSl2ModuleLieRingModule_f_apply_last (K := K) (n := n) t).symm

/-- The lowering operators agree before the last string vector. -/
lemma stringEquiv_f_lt (i : Fin (n + 1)) (hi : (i : ℕ) < n) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅fSub (K := K) t, stringVecs (K := K) f m n i⁆ =
      ⁅fSub (K := K) t, StandardSl2Module.v (K := K) (n := n) i⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  change stringEquiv P ⁅f, stringVecs (K := K) f m n i⁆ = _
  rw [show ⁅f, stringVecs (K := K) f m n i⁆ =
      stringVecs (K := K) f m n ⟨(i : ℕ) + 1, by omega⟩ from P.lie_f_pow_toEnd_f (i : ℕ),
    stringEquiv_apply P, standardSl2ModuleLieRingModule_f_apply_lt (K := K) (n := n) t i hi]

/-- The coordinate equivalence intertwines the lowering operator. -/
lemma stringEquiv_f (w : M) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅fSub (K := K) t, w⁆ = ⁅fSub (K := K) t, stringEquiv P w⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  refine stringEquiv_lie_of_basis P _ (fun i => ?_) w
  rcases eq_or_ne (i : ℕ) n with hi | hi
  · obtain rfl : i = Fin.last n := Fin.ext (by simp [hi])
    exact stringEquiv_f_last P
  · exact stringEquiv_f_lt P i (by omega)

/-- The Cartan operators agree on every string vector. -/
lemma stringEquiv_h_basis (i : Fin (n + 1)) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅hSub (K := K) t, stringVecs (K := K) f m n i⁆ =
      ⁅hSub (K := K) t, StandardSl2Module.v (K := K) (n := n) i⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  change stringEquiv P ⁅h, (LieModule.toEnd K L M f ^ (i : ℕ)) m⁆ = _
  rw [P.lie_h_pow_toEnd_f i, map_smul,
    show (LieModule.toEnd K L M f ^ (i : ℕ)) m = stringVecs (K := K) f m n i from rfl,
    stringEquiv_apply P, standardSl2ModuleLieRingModule_h_apply (K := K) (n := n) t i]

/-- The coordinate equivalence intertwines the Cartan operator. -/
lemma stringEquiv_h (w : M) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅hSub (K := K) t, w⁆ = ⁅hSub (K := K) t, stringEquiv P w⁆ :=
  stringEquiv_lie_of_basis P _ (stringEquiv_h_basis P) w

omit [CharZero K] in
/-- Every element of the generated subalgebra is a combination of `e`, `f`, `h`. -/
lemma exists_decomp (x : ↥(t.toLieSubalgebra (R := K))) :
    ∃ c₁ c₂ c₃ : K, x = c₁ • eSub (K := K) t + c₂ • fSub (K := K) t + c₃ • hSub (K := K) t := by
  obtain ⟨c₁, c₂, c₃, hc⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.property
  refine ⟨c₁, c₂, c₃, Subtype.ext ?_⟩
  change (x : L) = c₁ • e + c₂ • f + c₃ • h
  rw [hc, t.lie_e_f]

/-- The coordinate equivalence intertwines every element of the generated subalgebra. -/
lemma stringEquiv_lie (x : ↥(t.toLieSubalgebra (R := K))) (w : M) :
    letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
    stringEquiv P ⁅x, w⁆ = ⁅x, stringEquiv P w⁆ := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  let := standardSl2ModuleLieModule (K := K) (n := n) t
  obtain ⟨c₁, c₂, c₃, rfl⟩ := exists_decomp (K := K) x
  simp only [add_lie, smul_lie, map_add, map_smul, stringEquiv_e P, stringEquiv_f P,
    stringEquiv_h P]

end StringEquiv

/-- A finite-dimensional irreducible module for the generated `sl₂` subalgebra is
equivalent to a standard highest-weight module. -/
lemma classification [IsAlgClosed K] [CharZero K] [FiniteDimensional K M] (t : IsSl2Triple h e f)
    [LieModule.IsIrreducible K ↥(t.toLieSubalgebra (R := K)) M] :
    ∃ n : ℕ, letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
      Nonempty (M ≃ₗ⁅K, ↥(t.toLieSubalgebra (R := K))⁆ StandardSl2Module K n) := by
  have : Nontrivial M :=
    (LieSubmodule.nontrivial_iff K ↥(t.toLieSubalgebra (R := K)) M).mp inferInstance
  obtain ⟨μ, m₀, -, P⟩ := t.exists_hasPrimitiveVectorWith (R := K) (M := M)
  obtain ⟨n, rfl⟩ := P.exists_nat
  refine ⟨n, ?_⟩
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  exact ⟨{ stringEquiv P with map_lie' := fun {x w} => stringEquiv_lie P x w }⟩

omit [LieModule K L M] in
/-- Uniqueness of the highest weight: the `n` produced by
`classification` is determined by `M` alone, namely `n = finrank K M - 1`.

Unlike `classification`, irreducibility is not actually needed here: only the bare existence of
some `K`-linear equivalence `M ≃ₗ[K] V(n)` (forgetting the Lie-module structure `hn` provides) is
used, via a dimension count. -/
lemma classification_n_eq_finrank_sub_one [CharZero K]
    {t : IsSl2Triple h e f} {n : ℕ}
    (hn : letI := standardSl2ModuleLieRingModule (K := K) (n := n) t
      Nonempty (M ≃ₗ⁅K, ↥(t.toLieSubalgebra (R := K))⁆ StandardSl2Module K n)) :
    n = Module.finrank K M - 1 := by
  let := standardSl2ModuleLieRingModule (K := K) (n := n) t
  obtain ⟨Φ⟩ := hn
  have hfin : Module.finrank K M = Module.finrank K (StandardSl2Module K n) :=
    Φ.toLinearEquiv.finrank_eq
  have hVfin : Module.finrank K (StandardSl2Module K n) = n + 1 := by
    show Module.finrank K (Fin (n + 1) → K) = n + 1
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [hfin, hVfin]
  omega

end PhyslibAlpha.Sl2
