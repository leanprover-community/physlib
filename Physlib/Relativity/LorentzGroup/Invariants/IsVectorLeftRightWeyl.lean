/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
public import Physlib.Relativity.LorentzGroup.Invariants.RankTwo
public import Physlib.Relativity.PauliMatrices.AsTensor
/-!
# Lorentz invariants of a four-vector index and a left-right Weyl pair

Every Lorentz invariant in the span of the components of a family `T^{μ α α'}` carrying one
four-vector index and one opposite-chirality Weyl pair is a multiple of the contraction
against the Pauli matrices

`pauliContraction = σ_μ^{α α'} T^{μ}{}_{α α'}`,

the shape of the fermion kinetic term `ψ̄_{α'} σ̄^{μ α' α} ∂_μ ψ_α`. The theorem is
`exists_smul_pauliContraction_of_invariant`, and `repLorentz_pauliContraction` checks that
the contraction is invariant.

An opposite-chirality Weyl pair carries the `(1/2, 1/2)` representation, which is the
four-vector representation, so the three indices are two four-vector indices, and two of
those admit only the metric trace. The proof makes that literal: contracting the Weyl pair
against the covariant Pauli matrices `PauliMatrix.pauliLower`, which intertwine the two index
laws (`SL2C.sum_pauliLower_mul_sl2c`), turns `T` into a rank-two Lorentz family, invertibly
by Fierz completeness and hence with the same span (B); `RankTwo` supplies the classification,
its metric contraction being the Pauli contraction of `T` (C). Section D gives the model
family, whose Pauli contraction is `PauliMatrix.asTensor`.

The Standard Model's fermion symbols are `Module.Dual`-valued, so their spinor indices carry
the dual laws `(g⁻¹)ᵀ` and `(g⁻¹)ᴴ` (E). As in `IsBiLeftWeyl`, re-indexing the two spinor
slots by the symplectic form `ε` converts them into the fundamental laws for the same
representation; no conjugation twist is needed, the mixed law already carrying one conjugate
factor and `ε` having real entries, and the vector slot keeps the plain Lorentz law. The
re-index does move the contraction, sending the Pauli matrices to their transposes `pauliBar`,
so the invariant in the dual conclusions is `pauliBarContraction`, with scalar `+1` (F, G).
A dual pair with no vector index has no invariant at all (G).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C

/-!

## A. Vector-Weyl families and the Pauli contraction

`IsVectorLeftRightWeyl B repLorentz T` says the group moves the vector index of `T^{μ α α'}`
by the Lorentz matrix, the left Weyl index by the matrix of `g` and the right one by its
complex conjugate.

-/

/-- A sum over families of two four-vector indices is a double sum. -/
lemma sum_pi_fin_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, f ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3), f ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- A family `T` indexed by a four-vector index and a left- and a right-handed Weyl index,
  moved by `repLorentz` as `T^{μ α α'}`: the vector index by the Lorentz matrix, the left
  index by the matrix of `g` and the right index by its complex conjugate, the summed index
  first in each factor. -/
structure IsVectorLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
      ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * (g.1 a.1 l.1 * star (g.1 a.2 l.2))) • T (ν, a)

namespace IsVectorLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
  (hT : IsVectorLeftRightWeyl B repLorentz T)

include hT in
/-- The index law as one matrix on the product index. -/
lemma repLorentz_T' (g : SL(2,ℂ)) (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    repLorentz g (T d) = ∑ e : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      ((((SL2C.toLorentzGroup g).1 e.1 d.1 : ℝ) : ℂ)
        * (g.1 e.2.1 d.2.1 * star (g.1 e.2.2 d.2.2))) • T e := by
  rw [show d = (d.1, d.2) from rfl, hT.repLorentz_T, Fintype.sum_prod_type]

include hT in
/-- Moving a contraction of the Weyl pair at vector index `μ`: the vector index moves by the
  Lorentz matrix and the coefficient function by `IsLeftRightWeyl.act g`. -/
lemma repLorentz_sum_smul (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (c : Fin 2 × Fin 2 → ℂ) :
    repLorentz g (∑ a : Fin 2 × Fin 2, c a • T (μ, a))
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        • ∑ q : Fin 2 × Fin 2, IsLeftRightWeyl.act g c q • T (ν, q) := by
  rw [(repLorentz g).map_sum_smul_of_forall_eq (fun a => T (μ, a)) T
    (fun e a => (((SL2C.toLorentzGroup g).1 e.1 μ : ℝ) : ℂ)
      * (g.1 e.2.1 a.1 * star (g.1 e.2.2 a.2))) (fun a => hT.repLorentz_T' g (μ, a)) c,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, IsLeftRightWeyl.act, Finset.mul_sum]
  exact congrArg (· • T (ν, q)) (Finset.sum_congr rfl fun p _ => by ring)

/-- The Pauli contraction `∑ μ, ∑ a, σ^μ_{a₁ a₂} • T (μ, a)` against the Pauli matrices
  `PauliMatrix.pauliMatrix`: the kinetic-term contraction of a four-vector index against a
  pair of opposite-chirality Weyl indices. -/
noncomputable def pauliContraction : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2,
    PauliMatrix.pauliMatrix μ a.1 a.2 • T (μ, a)

/-!

## B. The reduction to a pair of four-vector indices

Contracting the Weyl pair against the covariant Pauli matrices turns `T` into a family
`vectorPair` of two four-vector indices, which is a rank-two Lorentz family. By Fierz
completeness the contraction is invertible, so the two families have the same span.

-/

/-- The family of two four-vector indices obtained by contracting the Weyl pair of `T`
  against the covariant Pauli matrices. -/
noncomputable def vectorPair : (Fin 2 → Fin 1 ⊕ Fin 3) → B :=
  fun d => ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliLower (d 1) a.1 a.2 • T (d 0, a)

include hT in
/-- The reduced family is a rank-two Lorentz family: the intertwining identity
  `SL2C.sum_pauliLower_mul_sl2c` carries the Weyl pair into a second vector index. -/
lemma isLorentzCovariant_vectorPair :
    IsLorentzCovariant 2 B repLorentz (vectorPair (T := T)) where
  repLorentz_T g l := by
    rw [vectorPair, hT.repLorentz_sum_smul, sum_pi_fin_two]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [IsLeftRightWeyl.act, sum_pauliLower_mul_sl2c]
    rw [Fintype.sum_sum_mul_smul
      (fun (q : Fin 2 × Fin 2) (ρ : Fin 1 ⊕ Fin 3) => PauliMatrix.pauliLower ρ q.1 q.2)
      (fun ρ => (((SL2C.toLorentzGroup g).1 ρ (l 1) : ℝ) : ℂ)) (fun q => T (ν, q)),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [vectorPair, smul_smul, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

omit hT in
/-- Every component of the reduced family lies in the span of the components of `T`. -/
lemma vectorPair_mem_componentSpan (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    vectorPair (T := T) d ∈ componentSpan T :=
  sum_mem fun a _ => Submodule.smul_mem _ _ (mem_componentSpan_self T (d 0, a))

omit hT in
/-- The reduction is invertible: by the Fierz completeness relation each component of
  `T` is recovered from the reduced family. -/
lemma eq_sum_vectorPair (μ : Fin 1 ⊕ Fin 3) (b : Fin 2 × Fin 2) :
    T (μ, b) = ∑ ρ : Fin 1 ⊕ Fin 3,
      ((2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1) • vectorPair (T := T) ![μ, ρ] := by
  calc T (μ, b) = ∑ a : Fin 2 × Fin 2,
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then 1 else 0)) • T (μ, a) := by
        rw [Fintype.sum_prod_type]
        simp [ite_smul, Finset.sum_ite_eq']
    _ = ∑ a : Fin 2 × Fin 2, (∑ ρ : Fin 1 ⊕ Fin 3,
          (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            • T (μ, a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [show (∑ ρ : Fin 1 ⊕ Fin 3,
              (2 : ℂ)⁻¹ * PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2)
            = (2 : ℂ)⁻¹ * ∑ ρ : Fin 1 ⊕ Fin 3,
              PauliMatrix.pauliLower ρ b.2 b.1 * PauliMatrix.pauliLower ρ a.1 a.2 from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => (mul_assoc _ _ _),
          PauliMatrix.sum_pauliLower_mul_pauliLower a.1 a.2 b.1 b.2]
        field_simp
    _ = _ := by
        simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_smul

omit hT in
/-- Every component of `T` lies in the span of the components of the reduced family. -/
lemma mem_componentSpan_vectorPair (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    T d ∈ componentSpan (vectorPair (T := T)) := by
  rw [show T d = T (d.1, d.2) from rfl, eq_sum_vectorPair (T := T) d.1 d.2]
  exact sum_mem fun ρ _ => Submodule.smul_mem _ _ (mem_componentSpan_self _ _)

omit hT in
/-- The reduction does not change the span of the components. -/
lemma componentSpan_vectorPair : componentSpan (vectorPair (T := T)) = componentSpan T :=
  le_antisymm ((componentSpan_le_iff _ _).2 fun d => vectorPair_mem_componentSpan d)
    ((componentSpan_le_iff _ _).2 fun d => mem_componentSpan_vectorPair d)

omit hT in
/-- The metric contraction of the reduced family is exactly the Pauli contraction of `T`: the
  two lowerings of the vector index cancel, so no sign and no scalar appear. -/
lemma metricContraction_vectorPair :
    RankTwo.metricContraction (T := vectorPair (T := T)) = pauliContraction (T := T) := by
  rw [RankTwo.metricContraction, sum_pi_fin_two, pauliContraction]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single ν (fun ρ _ hρ => ?_) (fun hν => absurd (Finset.mem_univ ν) hν)]
  · simp only [vectorPair, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [PauliMatrix.pauliLower_eq_smul, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    rcases ν with ν | ν <;> fin_cases ν <;> norm_num [minkowskiMatrixZ]
  · rw [show minkowskiMatrixZ (![ν, ρ] 0) (![ν, ρ] 1) = 0 from by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [minkowskiMatrixZ, Ne.symm hρ]]
    simp

/-!

## C. The classification of the Lorentz invariants

`RankTwo` classifies the invariants of `vectorPair`, and its metric contraction is the Pauli
contraction of `T`, so every invariant of the span is a multiple of `pauliContraction`.

-/

include hT in
/-- The Pauli contraction is a Lorentz invariant: `RankTwo.repLorentz_metricContraction` read
  through the reduction. -/
lemma repLorentz_pauliContraction (g : SL(2,ℂ)) :
    repLorentz g (pauliContraction (T := T)) = pauliContraction (T := T) := by
  rw [← metricContraction_vectorPair]
  exact RankTwo.repLorentz_metricContraction hT.isLorentzCovariant_vectorPair g

include hT in
/-- Every Lorentz invariant in the span of the components is a multiple of `pauliContraction`. -/
theorem exists_smul_pauliContraction_of_invariant {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • pauliContraction (T := T) := by
  obtain ⟨a, ha⟩ := RankTwo.exists_smul_metricContraction_of_invariant
    hT.isLorentzCovariant_vectorPair (by rwa [componentSpan_vectorPair]) hinv
  exact ⟨a, by rwa [metricContraction_vectorPair] at ha⟩

include hT in
/-- The same modulo a Lorentz-stable subspace `S`: a multiple of `pauliContraction` plus an
  error in `S`. -/
lemma exists_smul_pauliContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • pauliContraction (T := T) + y := by
  obtain ⟨a, y, hy, ha⟩ := RankTwo.exists_smul_metricContraction_of_invariant_subset
    hT.isLorentzCovariant_vectorPair S hS (by rwa [componentSpan_vectorPair]) hinv
  exact ⟨a, y, hy, by rwa [metricContraction_vectorPair] at ha⟩

end IsVectorLeftRightWeyl

/-!

## D. The Pauli tensor as the model example

The tensor product of the complex four-vector representation with the two Weyl
representations carries this law on products of basis vectors, and the Pauli contraction of
that family is `PauliMatrix.asTensor`, which by section C spans its invariants.

-/

open Fermion in
/-- The tensor product of the four-vector and the two Weyl representations carries this index
  law on products of basis vectors. -/
lemma isVectorLeftRightWeyl_pauli :
    IsVectorLeftRightWeyl (ContrℂModule ⊗[ℂ] (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl))
      (ContrℂModule.SL2CRep.tprod (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep))
      (fun d => complexContrBasis d.1 ⊗ₜ[ℂ]
        (LeftHandedWeyl.basis d.2.1 ⊗ₜ[ℂ] RightHandedWeyl.basis d.2.2)) where
  repLorentz_T g μ l := by
    have hC : (ContrℂModule.SL2CRep g) (complexContrBasis μ)
        = ∑ ν, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • complexContrBasis ν := by
      rw [SL2CRep_ρ_basis]
      exact Finset.sum_congr rfl fun ν _ => (algebraMap_smul ℂ _ _).symm
    have hR : (RightHandedWeyl.rep g) (RightHandedWeyl.basis l.2)
        = ∑ y, star (g.1 y l.2) • RightHandedWeyl.basis y := by
      rw [RightHandedWeyl.rep_apply_basis]
      exact Finset.sum_congr rfl fun y _ => by rw [Matrix.map_apply]
    have hinner : (∑ x, g.1 x l.1 • LeftHandedWeyl.basis x) ⊗ₜ[ℂ]
          (∑ y, star (g.1 y l.2) • RightHandedWeyl.basis y)
        = ∑ a : Fin 2 × Fin 2, (g.1 a.1 l.1 * star (g.1 a.2 l.2))
            • (LeftHandedWeyl.basis a.1 ⊗ₜ[ℂ] RightHandedWeyl.basis a.2) := by
      rw [TensorProduct.sum_tmul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, hC, hR, LeftHandedWeyl.rep_apply_basis, hinner,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
      module

open PauliMatrix Fermion in
/-- The Pauli contraction of the model family is `PauliMatrix.asTensor`. -/
lemma pauliContraction_pauli :
    IsVectorLeftRightWeyl.pauliContraction
        (T := fun d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 => complexContrBasis d.1 ⊗ₜ[ℂ]
          (LeftHandedWeyl.basis d.2.1 ⊗ₜ[ℂ] RightHandedWeyl.basis d.2.2))
      = PauliMatrix.asTensor := by
  rw [IsVectorLeftRightWeyl.pauliContraction, asTensor_expand]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.sum_univ_three, Fintype.sum_prod_type, Fin.sum_univ_two,
    pauliMatrix, Matrix.one_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  module

/-!

## E. Dual Weyl indices and the `ε` re-index

A `Module.Dual`-valued symbol carries the dual law on its spinor indices: `IsDualLeftRightWeyl`
for a Weyl pair alone, `IsVectorDualLeftRightWeyl` with a vector index alongside. The
symplectic identities of `Fermions.Weyl.Metric` convert those laws into the fundamental ones.

-/

/-- A family `T` indexed by a dual left- and a dual right-handed Weyl index, moved as
  `T_{α α'}`: the undotted index by the inverse transpose `(g⁻¹)ᵀ`, the dotted one by the
  inverse conjugate transpose `(g⁻¹)ᴴ`. -/
structure IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2) • T a

/-- The same with a four-vector index alongside, moved as `T^μ{}_{α α'}`. The vector index
  keeps the plain Lorentz matrix: in the Standard Model it is a derivative slot, and only
  the value index of a symbol is dualised. -/
structure IsVectorDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2),
    repLorentz g (T (μ, l)) = ∑ (ν : Fin 1 ⊕ Fin 3), ∑ (a : Fin 2 × Fin 2),
      ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2)) • T (ν, a)

open Fermion in
/-- The tensor product of the two dual Weyl representations carries the mixed dual law on
  products of basis vectors. -/
lemma isDualLeftRightWeyl_dualWeyl :
    IsDualLeftRightWeyl (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl)
      (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep)
      (fun l => DualLeftHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualLeftHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

/-- The mixed two-slot form of the symplectic identities `sum_epsilon_mul_inv_transpose` and
  `sum_epsilon_mul_inv_conjTranspose`: moving `(g⁻¹)ᵀ` and `(g⁻¹)ᴴ` across `ε` turns them into
  `g` and its conjugate on the other slots. -/
lemma sum_mixedEpsilon_mul_inv (g : SL(2,ℂ)) (l a : Fin 2 × Fin 2) :
    ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
  have hL : (∑ k₁, epsilon.1 l.1 k₁ * (g.1⁻¹)ᵀ a.1 k₁)
      * (∑ k₂, epsilon.1 l.2 k₂ * (g.1⁻¹)ᴴ a.2 k₂)
      = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
  have hR : (∑ b₁, g.1 b₁ l.1 * epsilon.1 b₁ a.1)
      * (∑ b₂, star (g.1 b₂ l.2) * epsilon.1 b₂ a.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * star (g.1 b.2 l.2))
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
  rw [← hL, ← hR, sum_epsilon_mul_inv_transpose, sum_epsilon_mul_inv_conjTranspose]

/-- The `ε` re-index turns the mixed dual law into the mixed fundamental law for the same
  representation: the symplectic identity `sum_mixedEpsilon_mul_inv` is the only mathematical
  step. -/
lemma IsDualLeftRightWeyl.isLeftRightWeyl_epsReindex {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) :
    IsLeftRightWeyl B repLorentz (epsReindex T) where
  repLorentz_T g l := by
    have h := (repLorentz g).map_sum_smul_of_forall_eq T T
      (fun a k => (g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᴴ a.2 k.2) (hT.repLorentz_T g)
      (fun k => epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
    simp only [sum_mixedEpsilon_mul_inv] at h
    rw [Fintype.sum_sum_mul_smul (fun (a b : Fin 2 × Fin 2) =>
      epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2)] at h
    exact h

/-!

## F. The `ε` re-index of a vector-Weyl family

Re-indexing both spinor slots by `ε` sends a family with the dual law to one with the
fundamental law, without touching the representation, and does not change the span. It
does move the contraction: the Pauli matrices go to their transposes.

-/

/-- The transposes `(σ_μ)ᵀ` of the covariant Pauli matrices, entrywise `(1, -σ₁, σ₂, -σ₃)`. -/
def pauliBar (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (PauliMatrix.pauliLower μ)ᵀ

/-- Conjugating a Pauli matrix by the symplectic form on both spinor slots produces
  `pauliBar` of the same vector index. -/
lemma sum_pauliMatrix_mul_epsilon (μ : Fin 1 ⊕ Fin 3) (k₁ k₂ : Fin 2) :
    ∑ a : Fin 2 × Fin 2, PauliMatrix.pauliMatrix μ a.1 a.2
        * (epsilon.1 a.1 k₁ * epsilon.1 a.2 k₂) = pauliBar μ k₁ k₂ := by
  rcases μ with μ | μ <;> fin_cases μ <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, PauliMatrix.pauliMatrix,
      pauliBar, PauliMatrix.pauliLower, PauliMatrix.pauliSelfAdjoint', SL2C.epsilon_coe]

/-- The `ε` re-index of such a family: the vector index is left alone and both spinor slots
  are sent through the symplectic form. -/
noncomputable def vectorEpsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B) : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B :=
  fun d => ∑ k : Fin 2 × Fin 2, (epsilon.1 d.2.1 k.1 * epsilon.1 d.2.2 k.2) • T (d.1, k)

section VectorReindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  (T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B)

/-- At a fixed vector index the re-index is the `ε` re-index of the Weyl pair. -/
lemma vectorEpsReindex_eq_epsReindex (μ : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) :
    vectorEpsReindex T (μ, l) = epsReindex (fun k => T (μ, k)) l := rfl

/-- The re-index is an involution, slot by slot. -/
lemma vectorEpsReindex_vectorEpsReindex :
    vectorEpsReindex (vectorEpsReindex T) = T := by
  funext d
  obtain ⟨μ, l⟩ := d
  have h : (fun k => vectorEpsReindex T (μ, k)) = epsReindex (fun k => T (μ, k)) := rfl
  rw [vectorEpsReindex_eq_epsReindex, h, epsReindex_epsReindex]

/-- The re-index does not change the span of the components. -/
lemma componentSpan_vectorEpsReindex :
    componentSpan (vectorEpsReindex T) = componentSpan T := by
  refine le_antisymm ((componentSpan_le_iff _ _).2 fun d => ?_)
    ((componentSpan_le_iff _ _).2 fun d => ?_)
  · exact sum_mem fun k _ => Submodule.smul_mem _ _ (mem_componentSpan_self T (d.1, k))
  · have h : T d = vectorEpsReindex (vectorEpsReindex T) d := by
      rw [vectorEpsReindex_vectorEpsReindex]
    rw [h]
    exact sum_mem fun k _ => Submodule.smul_mem _ _
      (mem_componentSpan_self (vectorEpsReindex T) (d.1, k))

end VectorReindex

namespace IsVectorDualLeftRightWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The contraction `∑ μ, ∑ a, pauliBar μ a₁ a₂ • T (μ, a)` against the transposed Pauli
  matrices, the invariant of a vector index against a dual Weyl pair. -/
noncomputable def pauliBarContraction : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ a : Fin 2 × Fin 2, pauliBar μ a.1 a.2 • T (μ, a)

/-- The index law as one matrix on the product index. -/
lemma repLorentz_T' (hT : IsVectorDualLeftRightWeyl B repLorentz T) (g : SL(2,ℂ))
    (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    repLorentz g (T d) = ∑ e : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      ((((SL2C.toLorentzGroup g).1 e.1 d.1 : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ e.2.1 d.2.1 * (g.1⁻¹)ᴴ e.2.2 d.2.2)) • T e := by
  rw [show d = (d.1, d.2) from rfl, hT.repLorentz_T, Fintype.sum_prod_type]

/-- The `ε` re-index turns the mixed dual law into the mixed fundamental law for the same
  representation, the vector slot untouched: `sum_mixedEpsilon_mul_inv` is the only
  mathematical step. -/
lemma isVectorLeftRightWeyl_vectorEpsReindex
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) :
    IsVectorLeftRightWeyl B repLorentz (vectorEpsReindex T) where
  repLorentz_T g μ l := by
    have h := (repLorentz g).map_sum_smul_of_forall_eq (fun k => T (μ, k)) T
      (fun e k => (((SL2C.toLorentzGroup g).1 e.1 μ : ℝ) : ℂ)
        * ((g.1⁻¹)ᵀ e.2.1 k.1 * (g.1⁻¹)ᴴ e.2.2 k.2)) (fun k => hT.repLorentz_T' g (μ, k))
      (fun k => epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
    refine h.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hinner : ∀ b : Fin 2 × Fin 2,
        (∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
          * ((((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
            * ((g.1⁻¹)ᵀ b.1 k.1 * (g.1⁻¹)ᴴ b.2 k.2)))
          = (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ)
            * ∑ a : Fin 2 × Fin 2, (g.1 a.1 l.1 * star (g.1 a.2 l.2))
              * (epsilon.1 a.1 b.1 * epsilon.1 a.2 b.2) := fun b => by
      rw [← sum_mixedEpsilon_mul_inv g l b, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hinner, mul_smul, ← Finset.smul_sum]
    rw [Fintype.sum_sum_mul_smul (fun (b a : Fin 2 × Fin 2) =>
      epsilon.1 a.1 b.1 * epsilon.1 a.2 b.2)
      (fun a => g.1 a.1 l.1 * star (g.1 a.2 l.2)) (fun b => T (ν, b))]
    simp only [← mul_smul]
    rfl

/-- The re-index carries the Pauli contraction of the re-indexed family to the
  `pauliBar` contraction of the original, with no sign or scalar. -/
lemma pauliContraction_vectorEpsReindex :
    IsVectorLeftRightWeyl.pauliContraction (T := vectorEpsReindex T)
      = pauliBarContraction (T := T) := by
  rw [IsVectorLeftRightWeyl.pauliContraction, pauliBarContraction]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [vectorEpsReindex, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, ← sum_pauliMatrix_mul_epsilon μ k.1 k.2]

end IsVectorDualLeftRightWeyl

/-!

## G. The classification of the invariants of the dual families

Transporting sections C and F along the re-index: a dual Weyl pair with no vector index has
no invariant, and with a vector index every invariant is a multiple of the `pauliBar`
contraction.

-/

section DualClassification

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A dual left-handed and a dual right-handed Weyl index with no vector index between them
  have no Lorentz invariant in the span of their components but `0`: the mixed pair is the
  four-vector representation, whose invariants need a second vector index, as in
  `IsVectorDualLeftRightWeyl`. -/
theorem IsDualLeftRightWeyl.eq_zero_of_invariant {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  hT.isLeftRightWeyl_epsReindex.eq_zero_of_invariant (by rwa [componentSpan_epsReindex]) hinv

/-- The same modulo a Lorentz-stable subspace `S`: such an invariant already lies in `S`. -/
theorem IsDualLeftRightWeyl.mem_of_invariant_of_mem_sup {T : Fin 2 × Fin 2 → B}
    (hT : IsDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S :=
  hT.isLeftRightWeyl_epsReindex.mem_of_invariant_of_mem_sup S hS
    (by rwa [componentSpan_epsReindex]) hinv

namespace IsVectorDualLeftRightWeyl

variable {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}

/-- The `pauliBar` contraction of a family with the mixed dual law is Lorentz invariant. -/
lemma repLorentz_pauliBarContraction (hT : IsVectorDualLeftRightWeyl B repLorentz T)
    (g : SL(2,ℂ)) :
    repLorentz g (pauliBarContraction (T := T)) = pauliBarContraction (T := T) := by
  have h := hT.isVectorLeftRightWeyl_vectorEpsReindex.repLorentz_pauliContraction g
  rwa [pauliContraction_vectorEpsReindex] at h

/-- For the mixed dual law, every Lorentz invariant of the span is a multiple of the
  `pauliBar` contraction. This is the kinetic term of a Weyl fermion. -/
theorem exists_smul_pauliBarContraction_of_invariant
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • pauliBarContraction (T := T) := by
  obtain ⟨a, ha⟩ :=
    hT.isVectorLeftRightWeyl_vectorEpsReindex.exists_smul_pauliContraction_of_invariant
      (by rwa [componentSpan_vectorEpsReindex]) hinv
  exact ⟨a, by rwa [pauliContraction_vectorEpsReindex] at ha⟩

/-- The same modulo a Lorentz-stable submodule `S`. -/
theorem exists_smul_pauliBarContraction_of_invariant_subset
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • pauliBarContraction (T := T) + y := by
  obtain ⟨a, y, hy, ha⟩ :=
    hT.isVectorLeftRightWeyl_vectorEpsReindex.exists_smul_pauliContraction_of_invariant_subset
      S hS (by rwa [componentSpan_vectorEpsReindex]) hinv
  exact ⟨a, y, hy, by rwa [pauliContraction_vectorEpsReindex] at ha⟩

end IsVectorDualLeftRightWeyl

end DualClassification

end Lorentz
