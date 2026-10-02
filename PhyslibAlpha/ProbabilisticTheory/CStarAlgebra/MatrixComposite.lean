/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Composite.CompletePositivity
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Commutative
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.QuantumChannel

/-!
# Matrices over a C⋆-algebra as a composite system

## i. Overview

Coupling a quantum system with observables `A` to an `n`-level ancilla gives the `n × n` matrices
over `A`. The self-adjoint ones are the composite observables of the self-adjoint part of `A` with
the `n × n` Hermitian matrices: the product `a ⊗ h` is the matrix `(hᵢⱼ a)`. The positive
matrices form a cone of composite observables that contains every product of positive observables
and is Archimedean. When `A` is commutative, every positive matrix is also in the maximal cone:
applying a character entrywise turns it into a positive scalar matrix.

Applying a map entrywise to matrices is tensoring it with the identity of the ancilla. So complete
positivity of a map, in the sense of positive matrices, is the complete positivity of composite
systems, and for maps out of commutative C⋆-algebras it follows from classicality.

## ii. Key results

- `CStarMatrix.kron` : the matrix `(hᵢⱼ a)`.
- `CStarMatrix.toMatrix` : the matrix of a composite observable.
- `CStarMatrix.kron_nonneg` : products of positive observables are positive matrices.
- `CStarMatrix.matrixCone` : the positive matrices, as a cone of composite observables.
- `CStarMatrix.isArchimedeanTensorCone_matrixCone` : this cone is Archimedean.
- `CStarMatrix.exists_toMatrix_eq` : every self-adjoint matrix is a composite observable.
- `CStarMatrix.mem_maxTensorCone_of_nonneg` : for commutative `A`, positive matrices are in the
  maximal cone.

## iii. Table of contents

- A. The matrix of a composite observable
- B. Positive matrices
- C. Every self-adjoint matrix is a composite observable
- D. Commutative algebras
- E. Applying a map entrywise
- F. Channels out of commutative algebras

-/

@[expose] public section


namespace CStarMatrix
open ProbabilisticTheory
open TensorProduct
open scoped ComplexOrder

variable {n : Type} {A : Type*} [CStarAlgebra A]

/-! ## A. The matrix of a composite observable -/

/-- The matrix `(hᵢⱼ a)`: the observable `a` tensored with the scalar matrix `h`. -/
def kron (h : CStarMatrix n n ℂ) (a : A) : CStarMatrix n n A :=
  ofMatrix fun i j => h i j • a

@[simp]
lemma kron_apply (h : CStarMatrix n n ℂ) (a : A) (i j : n) : kron h a i j = h i j • a := rfl

lemma kron_add_left (h h' : CStarMatrix n n ℂ) (a : A) : kron (h + h') a = kron h a + kron h' a :=
  ext fun i j => show (h i j + h' i j) • a = h i j • a + h' i j • a from add_smul _ _ _

lemma kron_add_right (h : CStarMatrix n n ℂ) (a a' : A) : kron h (a + a') = kron h a + kron h a' :=
  ext fun i j => show h i j • (a + a') = h i j • a + h i j • a' from smul_add _ _ _

lemma kron_smul_left (r : ℝ) (h : CStarMatrix n n ℂ) (a : A) : kron (r • h) a = r • kron h a :=
  ext fun i j => show (r • h i j) • a = r • (h i j • a) from smul_assoc _ _ _

lemma kron_smul_right (r : ℝ) (h : CStarMatrix n n ℂ) (a : A) : kron h (r • a) = r • kron h a :=
  ext fun i j => show h i j • (r • a) = r • (h i j • a) from smul_comm _ _ _

lemma kron_zero_left (a : A) : kron (0 : CStarMatrix n n ℂ) a = 0 :=
  ext fun _ _ => show (0 : ℂ) • a = 0 from zero_smul _ _

lemma kron_zero_right (h : CStarMatrix n n ℂ) : kron h (0 : A) = 0 :=
  ext fun i j => show h i j • (0 : A) = 0 from smul_zero _

lemma map_add' {B : Type*} [AddCommMonoid B] (M N : CStarMatrix n n A) (f : A →+ B) :
    (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => map_add f _ _

variable [Fintype n]

/-- `kron g b` has adjoint-square `kron (g⋆ g) (b⋆ b)`. -/
lemma star_kron_mul_kron (g : CStarMatrix n n ℂ) (b : A) :
    star (kron g b) * kron g b = kron (star g * g) (star b * b) :=
  ext fun i j => by
    simp only [mul_apply, star_apply, kron_apply, star_smul, smul_mul_smul_comm, Finset.sum_smul]

omit [Fintype n] in
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → CStarMatrix n n A) (i j : n) :
    (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j :=
  Matrix.sum_apply i j s f

variable [DecidableEq n] [PartialOrder A] [StarOrderedRing A]

variable (n A) in
/-- The matrix of a composite observable of the self-adjoint part of `A` with the `n × n`
Hermitian matrices. -/
noncomputable def toMatrix :
    Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ)) →ₗ[ℝ] CStarMatrix n n A :=
  TensorProduct.lift <| LinearMap.mk₂ ℝ (fun a h => kron (h : CStarMatrix n n ℂ) (a : A))
    (fun a a' h => by simp [kron_add_right])
    (fun r a h => by simp [kron_smul_right])
    (fun a h h' => by simp [kron_add_left])
    (fun r a h => ext fun i j =>
      show (r • (h : CStarMatrix n n ℂ) i j) • (a : A) = r • ((h : CStarMatrix n n ℂ) i j • (a : A))
      from smul_assoc _ _ _)

@[simp]
lemma toMatrix_tmul (a : selfAdjoint A) (h : selfAdjoint (CStarMatrix n n ℂ)) :
    toMatrix n A (Composite.tmul a h) = kron (h : CStarMatrix n n ℂ) (a : A) := rfl

lemma toMatrix_one_tmul_one :
    toMatrix n A (Composite.tmul (1 : selfAdjoint A) (1 : selfAdjoint (CStarMatrix n n ℂ))) = 1 :=
  ext fun i j => by
    by_cases h : i = j
    · subst h; simp [one_apply_eq]
    · simp [one_apply_ne' (Ne.symm h)]

omit [Fintype n] [DecidableEq n] [PartialOrder A] [StarOrderedRing A] in
lemma isSelfAdjoint_kron {h : CStarMatrix n n ℂ} {a : A} (hh : IsSelfAdjoint h)
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (kron h a) :=
  ext fun i j => by
    rw [star_apply, kron_apply, kron_apply, star_smul, ha.star_eq,
      ← star_apply, hh.star_eq]

lemma isSelfAdjoint_toMatrix (z : Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ))) :
    IsSelfAdjoint (toMatrix n A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a h => exact isSelfAdjoint_kron h.2 a.2
  | add z w hz hw => rw [map_add]; exact hz.add hw

/-! ## B. Positive matrices -/

omit [DecidableEq n] in
/-- **Products of positive observables are positive matrices.** Both factors are sums of
adjoint-squares, and `kron` of adjoint-squares is an adjoint-square. -/
lemma kron_nonneg {h : CStarMatrix n n ℂ} {a : A} (hh : 0 ≤ h) (ha : 0 ≤ a) : 0 ≤ kron h a := by
  rw [StarOrderedRing.nonneg_iff] at hh ha
  induction hh using AddSubmonoid.closure_induction with
  | mem _ hg =>
    obtain ⟨g, rfl⟩ := hg
    induction ha using AddSubmonoid.closure_induction with
    | mem _ hb =>
      obtain ⟨b, rfl⟩ := hb
      rw [← star_kron_mul_kron]; exact star_mul_self_nonneg _
    | zero => rw [kron_zero_right]
    | add _ _ _ _ h₁ h₂ => rw [kron_add_right]; exact add_nonneg h₁ h₂
  | zero => rw [kron_zero_left]
  | add _ _ _ _ h₁ h₂ => rw [kron_add_left]; exact add_nonneg h₁ h₂

variable (n A) in
/-- The positive matrices, as a cone of composite observables. -/
noncomputable def matrixCone :
    PointedCone ℝ (Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ))) where
  carrier := {z | 0 ≤ toMatrix n A z}
  add_mem' {z w} hz hw := by
    simp only [Set.mem_ofPred_eq, map_add] at hz hw ⊢; exact add_nonneg hz hw
  zero_mem' := by simp
  smul_mem' c z hz := by
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [show (c • z) = (c : ℝ) • z from rfl, map_smul]
    exact smul_nonneg c.2 hz

lemma mem_matrixCone {z : Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ))} :
    z ∈ matrixCone n A ↔ 0 ≤ toMatrix n A z := Iff.rfl

/-- The positive matrices contain every product of positive observables. -/
lemma minTensorCone_le_matrixCone :
    minTensorCone (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ)) ≤ matrixCone n A := fun _ hz =>
  minTensorCone_induction (E := selfAdjoint A) (F := selfAdjoint (CStarMatrix n n ℂ))
    (p := fun z => z ∈ matrixCone n A) hz
    (fun _ _ ha hh => kron_nonneg hh ha) (zero_mem _) (fun _ _ => add_mem)
    (fun _ hc _ hz => (matrixCone n A).smul_mem hc hz)

/-- **The positive matrices form an Archimedean cone.** -/
lemma isArchimedeanTensorCone_matrixCone :
    IsArchimedeanTensorCone (E := selfAdjoint A) (F := selfAdjoint (CStarMatrix n n ℂ))
      (matrixCone n A) := by
  intro z hz
  let x : selfAdjoint (CStarMatrix n n A) := ⟨toMatrix n A z, isSelfAdjoint_toMatrix z⟩
  have key : -x ≤ 0 := ArchimedeanOrderUnitSpace.le_zero_of_forall_pos_smul_one_le _ fun ε hε => by
    have h := hz ε hε
    rw [mem_matrixCone, map_add, map_smul, toMatrix_one_tmul_one] at h
    change -(toMatrix n A z) ≤ ε • (1 : CStarMatrix n n A)
    rw [neg_le_iff_add_nonneg, add_comm]; exact h
  exact neg_nonpos.1 key

/-! ## C. Every self-adjoint matrix is a composite observable -/

/-- The matrix unit `eᵢⱼ`. -/
def unit (i j : n) : CStarMatrix n n ℂ := ofMatrix (Matrix.single i j 1)

omit [Fintype n] in
lemma unit_apply (i j p q : n) : unit i j p q = if i = p ∧ j = q then 1 else 0 := by
  simp [unit, ofMatrix_apply, Matrix.single_apply]

omit [Fintype n] in
lemma star_unit (i j : n) : star (unit i j) = unit j i :=
  ext fun p q => by
    rw [star_apply, unit_apply, unit_apply]
    split_ifs <;> simp_all [and_comm]

/-- The Hermitian matrix `(eᵢⱼ + eⱼᵢ) / 2`. -/
noncomputable def symUnit (i j : n) : selfAdjoint (CStarMatrix n n ℂ) :=
  ⟨(2 : ℝ)⁻¹ • (unit i j + unit j i), by
    change star _ = _
    rw [star_smul, star_add, star_unit, star_unit, star_trivial, add_comm]⟩

/-- The Hermitian matrix `i (eᵢⱼ - eⱼᵢ) / 2`. -/
noncomputable def asymUnit (i j : n) : selfAdjoint (CStarMatrix n n ℂ) :=
  ⟨(Complex.I / 2) • (unit i j - unit j i), by
    change star _ = _
    rw [star_smul, star_sub, star_unit, star_unit, star_div₀, Complex.star_def,
      Complex.conj_I, map_ofNat, neg_div, neg_smul, ← smul_neg, neg_sub]⟩

/-- The entry of a matrix, as a function of the matrix. -/
def entry (M : CStarMatrix n n A) (i j : n) : A := M i j

/-- The composite observable whose matrix is `M`. -/
noncomputable def ofMatrixSA (M : CStarMatrix n n A) :
    Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ)) :=
  ∑ i, ∑ j, (Composite.tmul (realPart (entry M i j)) (symUnit i j) +
    Composite.tmul (imaginaryPart (entry M i j)) (asymUnit i j))

omit [Fintype n] [PartialOrder A] [StarOrderedRing A] in
lemma kron_symUnit_apply (i j p q : n) (a : A) :
    kron (symUnit i j : CStarMatrix n n ℂ) a p q =
      (2 : ℝ)⁻¹ • ((if i = p ∧ j = q then a else 0) + (if j = p ∧ i = q then a else 0)) := by
  rw [kron_apply]
  change ((2 : ℝ)⁻¹ • (unit i j p q + unit j i p q)) • a = _
  rw [unit_apply, unit_apply, smul_assoc, add_smul]
  split_ifs <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma kron_asymUnit_apply (i j p q : n) (a : A) :
    kron (asymUnit i j : CStarMatrix n n ℂ) a p q =
      (Complex.I / 2) • ((if i = p ∧ j = q then a else 0) - (if j = p ∧ i = q then a else 0)) := by
  rw [kron_apply]
  change ((Complex.I / 2) • (unit i j p q - unit j i p q)) • a = _
  rw [unit_apply, unit_apply, smul_assoc, sub_smul]
  split_ifs <;> simp

lemma toMatrix_ofMatrixSA (M : CStarMatrix n n A) :
    toMatrix n A (ofMatrixSA M) = ∑ i, ∑ j,
      (kron (symUnit i j : CStarMatrix n n ℂ) (realPart (entry M i j) : A) +
        kron (asymUnit i j : CStarMatrix n n ℂ) (imaginaryPart (entry M i j) : A)) := by
  rw [ofMatrixSA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, toMatrix_tmul, toMatrix_tmul]

lemma toMatrix_ofMatrixSA_apply (M : CStarMatrix n n A) (p q : n) :
    toMatrix n A (ofMatrixSA M) p q =
      (2 : ℝ)⁻¹ • ((realPart (entry M p q) : A) + realPart (entry M q p)) +
        (Complex.I / 2) • ((imaginaryPart (entry M p q) : A) - imaginaryPart (entry M q p)) := by
  rw [toMatrix_ofMatrixSA, sum_apply]
  simp only [sum_apply, add_apply, kron_symUnit_apply, kron_asymUnit_apply]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib, smul_add, smul_sub]
  simp [ite_and, Finset.sum_ite_eq']

/-- **Every self-adjoint matrix over `A` is a composite observable.** -/
lemma exists_toMatrix_eq {M : CStarMatrix n n A} (hM : IsSelfAdjoint M) :
    ∃ z, toMatrix n A z = M := by
  refine ⟨ofMatrixSA M, ext fun p q => ?_⟩
  have hqp : entry M q p = star (entry M p q) := by
    rw [entry, entry, ← star_apply, hM.star_eq]
  rw [toMatrix_ofMatrixSA_apply, hqp, realPart_apply_coe, realPart_apply_coe,
    imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star]
  simp only [← Complex.coe_smul]
  change _ = entry M p q
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]; ring_nf

/-! ## D. Commutative algebras -/

section Commutative

variable {C : Type*} [CommCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A character of `C`, as a positive functional on its observables. -/
noncomputable def characterFunctional (χ : WeakDual.characterSpace ℂ C) : selfAdjoint C →ₚ[ℝ] ℝ :=
  (PositiveLinearMap.ofClass (CommCStarAlgebra.character χ)).restrictSAC

lemma coe_characterFunctional (χ : WeakDual.characterSpace ℂ C) (x : selfAdjoint C) :
    (characterFunctional χ x : ℂ) = χ (x : C) :=
  PositiveLinearMap.coe_restrictSAC_apply _ x

/-- Measuring the first factor with a character is applying the character entrywise. -/
lemma coe_lslice_characterFunctional (χ : WeakDual.characterSpace ℂ C)
    (z : Composite (selfAdjoint C) (selfAdjoint (CStarMatrix n n ℂ))) :
    ((PositiveLinearMap.lslice (characterFunctional χ) z : selfAdjoint (CStarMatrix n n ℂ)) :
      CStarMatrix n n ℂ) = (toMatrix n C z).map χ := by
  induction z using TensorProduct.inductionOn with
  | tmul x h =>
    rw [PositiveLinearMap.lslice_tmul]
    refine ext fun i j => ?_
    change (characterFunctional χ x : ℝ) • (h : CStarMatrix n n ℂ) i j =
      χ ((h : CStarMatrix n n ℂ) i j • (x : C))
    rw [map_smul, smul_eq_mul, ← coe_characterFunctional, Complex.real_smul, mul_comm]
  | add z w hz hw =>
    rw [map_add, AddMemClass.coe_add, hz, hw, map_add]
    exact (map_add' _ _ (χ : C →+ ℂ)).symm

/-- **For commutative `C`, positive matrices are in the maximal cone.** Measuring the ancilla with a
positive functional leaves an observable of `C` on which every character is nonnegative, because
applying a character entrywise keeps a matrix positive. -/
lemma mem_maxTensorCone_of_nonneg {z : Composite (selfAdjoint C) (selfAdjoint (CStarMatrix n n ℂ))}
    (hz : 0 ≤ toMatrix n C z) :
    z ∈ maxTensorCone (selfAdjoint C) (selfAdjoint (CStarMatrix n n ℂ)) := by
  refine mem_maxTensorCone_iff_rslice.2 fun ψ => ?_
  change (0 : C) ≤ _
  refine CommCStarAlgebra.nonneg_iff_forall_character.2 fun χ => ?_
  rw [← coe_characterFunctional, Complex.zero_le_real]
  change 0 ≤ PositiveLinearMap.tensor (characterFunctional χ) ψ z
  rw [PositiveLinearMap.tensor_apply_eq_lslice]
  refine ψ.map_nonneg ?_
  change (0 : CStarMatrix n n ℂ) ≤ _
  rw [coe_lslice_characterFunctional]
  exact map_nonneg (mapₙₐ (R := ℂ) (CommCStarAlgebra.character χ).toNonUnitalStarAlgHom) hz

end Commutative

/-! ## E. Applying a map entrywise -/

section Map

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Applying a positive unital map to the first factor of a composite observable is applying it
entrywise to its matrix. -/
lemma toMatrix_map (f : A →ₚ₁[ℂ] B)
    (z : Composite (selfAdjoint A) (selfAdjoint (CStarMatrix n n ℂ))) :
    toMatrix n B (TensorProduct.map
      (f.restrictSA : Channel (selfAdjoint A) (selfAdjoint B)).toLinearMap LinearMap.id z) =
      (toMatrix n A z).map f := by
  induction z using TensorProduct.inductionOn with
  | tmul x h =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    refine ext fun i j => ?_
    change (h : CStarMatrix n n ℂ) i j • ((f.restrictSA x : selfAdjoint B) : B) =
      f ((h : CStarMatrix n n ℂ) i j • (x : A))
    rw [UnitalPositiveLinearMap.coe_restrictSA_apply, map_smul]
  | add z w hz hw =>
    rw [map_add, map_add, hz, hw, map_add]
    exact (map_add' _ _ (f.toLinearMap.toAddMonoidHom)).symm

end Map

end CStarMatrix

namespace ProbabilisticTheory

open TensorProduct
open scoped ComplexOrder

/-! ## F. Channels out of commutative algebras -/

namespace QuantumChannel

variable {C B : Type*} [CommCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

open CStarMatrix in
/-- Entrywise, a positive unital map out of a commutative C⋆-algebra keeps positive matrices
positive: the input is classical, so the map is completely positive. -/
lemma map_nonneg_of_commutative (f : C →ₚ₁[ℂ] B) {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) C}
    (hM : 0 ≤ M) : 0 ≤ M.map f := by
  obtain ⟨z, rfl⟩ := exists_toMatrix_eq (IsSelfAdjoint.of_nonneg hM)
  let φ : Channel (selfAdjoint C) (selfAdjoint B) := f.restrictSA
  have hC : IsNuclear (selfAdjoint C) := CommCStarAlgebra.isClassical.isNuclear
  have hmax := mem_maxTensorCone_of_nonneg hM
  have h : TensorProduct.map φ.toLinearMap LinearMap.id z ∈ matrixCone (Fin k) B := by
    refine CompositeCone.map_mem_of_isNuclear_left (E := selfAdjoint C) (F := selfAdjoint B)
      (A := selfAdjoint (CStarMatrix (Fin k) (Fin k) ℂ)) hC φ ?_
      isArchimedeanTensorCone_matrixCone minTensorCone_le_matrixCone
    exact hmax
  rw [mem_matrixCone, toMatrix_map] at h
  exact h

/-- **Stinespring's theorem.** A positive unital map out of a commutative C⋆-algebra is a quantum
channel: it is automatically completely positive. -/
noncomputable def ofCommutative (f : C →ₚ₁[ℂ] B) : QuantumChannel C B where
  toLinearMap := f.toLinearMap
  map_cstarMatrix_nonneg' _ _ hM := map_nonneg_of_commutative f hM
  map_one' := map_one f

@[simp]
lemma ofCommutative_apply (f : C →ₚ₁[ℂ] B) (x : C) : ofCommutative f x = f x := rfl

end QuantumChannel

end ProbabilisticTheory
