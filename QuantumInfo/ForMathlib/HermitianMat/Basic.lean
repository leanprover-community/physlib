/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.IsMaximalSelfAdjoint
public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.Tactic.Commutes


@[expose] public section

/-- The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled
with the fact that `Matrix.IsHermitian`. -/
def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))

namespace HermitianMat

variable {α R 𝕜 : Type*} {m n : Type*}
variable [Star R] [TrivialStar R]
variable [RCLike 𝕜]

section addgroup

variable [AddGroup α] [StarAddMonoid α]

theorem eq_IsHermitian : HermitianMat n α  = { m : Matrix n n α // m.IsHermitian} := by
  rfl

@[coe] def mat : HermitianMat n α → Matrix n n α :=
  Subtype.val

instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨mat⟩

@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
  rfl

@[simp]
theorem mat_mk (x : Matrix n n α) (h) : mat ⟨x, h⟩ = x := by
  rfl

@[simp]
theorem mk_mat {A : HermitianMat n α} (h : A.mat.IsHermitian) : ⟨A.mat, h⟩ = A := by
  rfl

/-- Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value
  is actually `IsHermitian`.-/
theorem H (A : HermitianMat n α) : A.mat.IsHermitian :=
  A.2

@[ext] protected theorem ext {A B : HermitianMat n α} : A.mat = B.mat → A = B :=
  Subtype.ext

instance instFun : FunLike (HermitianMat n α) n (n → α) where
  coe M := (M : Matrix n n α)
  coe_injective _ _ h := HermitianMat.ext h

@[simp]
theorem mat_apply {A : HermitianMat n α} {i j : n} : A.mat i j = A i j := by
  rfl

@[simp]
theorem mk_apply (x : Matrix n n α) (h) (i j : n) :
    DFunLike.coe (F := HermitianMat n α) ⟨x, h⟩ i j = x i j := by
  rfl

@[simp]
theorem conjTranspose_mat (A : HermitianMat n α) :
    A.mat.conjTranspose = A.mat :=
  A.H

instance : AddGroup (HermitianMat n α) :=
  AddSubgroup.toAddGroup _

instance [IsEmpty n] : Unique (HermitianMat n α) where
  default := 0
  uniq a := by ext; exact (IsEmpty.false ‹_›).elim

@[simp, norm_cast]
theorem mat_zero : (0 : HermitianMat n α).mat = 0 := by
  rfl

@[simp]
theorem mk_zero (h : (0 : Matrix n n α).IsHermitian) : ⟨0, h⟩ = (0 : HermitianMat n α) := by
  rfl

@[simp]
theorem zero_apply (i j : n) : (0 : HermitianMat n 𝕜) i j = 0 := by
  rfl

@[simp, norm_cast]
theorem mat_add (A B : HermitianMat n α) :
    (A + B).mat = A.mat + B.mat := by
  rfl

@[simp, norm_cast]
theorem mat_sub (A B : HermitianMat n α) :
    (A - B).mat = A.mat - B.mat := by
  rfl

@[simp, norm_cast]
theorem mat_neg (A : HermitianMat n α) :
    (-A).mat = -A.mat := by
  rfl

section smul
variable [SMul R α] [StarModule R α]

instance : SMul R (HermitianMat n α) :=
  ⟨fun c A ↦ ⟨c • A.mat, (IsSelfAdjoint.all _).smul A.H⟩⟩

@[simp, norm_cast]
theorem mat_smul (c : R) (A : HermitianMat n α) :
    (c • A).mat = c • A.mat := by
  rfl

@[simp]
theorem smul_apply (c : R) (A : HermitianMat n α) (i j : n) :
    (c • A) i j = c • A i j := by
  rfl
end smul
section topology

variable [TopologicalSpace α]

instance : TopologicalSpace (HermitianMat n α) :=
  inferInstanceAs (TopologicalSpace (selfAdjoint _))

/- Amusingly, if we don't tag this fun_prop, then fun_prop fails to prove other things! Because
it will look through and see that `HermitianMat.mat` is `Subtype.val` *here*, but not in downstream
applications of the tactic. -/
@[fun_prop]
theorem continuous_mat : Continuous (HermitianMat.mat : HermitianMat n α → Matrix n n α) := by
  fun_prop

lemma continuousOn_iff_coe {X : Type*} [TopologicalSpace X] {s : Set X}
    (f : X → HermitianMat n α) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).mat) s := by
  constructor
  · intro; fun_prop
  · intro h
    rw [continuousOn_iff_continuous_domRestrict] at *
    apply Continuous.subtype_mk h

variable [IsTopologicalAddGroup α]

--In principle, ContinuousAdd and ContinuousNeg just need corresponding instances for α,
-- not all of IsTopologicalAddGroup.

instance : ContinuousAdd (HermitianMat n α) :=
  inferInstanceAs (ContinuousAdd (selfAdjoint _))

instance : ContinuousNeg (HermitianMat n α) :=
  inferInstanceAs (ContinuousNeg (selfAdjoint _))

instance : IsTopologicalAddGroup (HermitianMat n α) where

variable  [TopologicalSpace R] [SMul R α] [ContinuousSMul R α] [StarModule R α]

set_option backward.isDefEq.respectTransparency false in
instance : ContinuousSMul R (HermitianMat n α) where
  continuous_smul := by
    rw [continuous_induced_rng]
    fun_prop

--Shorcut instances:
instance : IsTopologicalAddGroup (HermitianMat n 𝕜) := inferInstance

instance : ContinuousSMul ℝ (HermitianMat n ℂ) := inferInstance

--TODO: Would be good to figure out the general (not just RCLike) version of this.
instance : T3Space (HermitianMat n 𝕜) :=
  inferInstanceAs (T3Space (selfAdjoint _))

end topology

section mulAction
variable [Monoid R] [MulAction R α] [StarModule R α]

instance : MulAction R (HermitianMat n α) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective mat_smul

end mulAction
end addgroup
section addcommgroup

variable [AddCommGroup α] [StarAddMonoid α]

instance : AddCommGroup (HermitianMat n α) :=
  AddSubgroup.toAddCommGroup _

@[simp, norm_cast]
theorem mat_finset_sum (f : ι → HermitianMat n α) (s : Finset ι) :
    (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat := by
  apply AddSubgroup.val_finsetSum

section module

variable [Semiring R] [Module R α] [StarModule R α]

instance : Module R (HermitianMat n α) :=
  inferInstanceAs (Module R (selfAdjoint (Matrix n n α)))

variable [TopologicalSpace α]

/-- The projection from HermitianMat to Matrix, as a continuous linear map. -/
@[simps]
def matₗ : HermitianMat n α →L[R] Matrix n n α where
  toFun := mat
  cont := by fun_prop
  map_add' := by simp
  map_smul' := by simp

end module
end addcommgroup
section ring

variable [NonAssocRing α] [StarRing α] [DecidableEq n]

instance : One (HermitianMat n α) :=
  ⟨1, by
    simp [selfAdjoint.mem_iff, ← Matrix.ext_iff,
      Matrix.one_apply, apply_ite (β := α), eq_comm]⟩

@[simp, norm_cast]
theorem mat_one : (1 : HermitianMat n α).mat = 1 := by
  rfl

@[simp]
theorem mk_one (h : (1 : Matrix n n α).IsHermitian) : ⟨1, h⟩ = (1 : HermitianMat n α) := by
  rfl

@[simp]
theorem one_apply (i j : n) : (1 : HermitianMat n α) i j = (1 : Matrix n n α) i j := by
  rfl

noncomputable instance : AddCommMonoidWithOne (HermitianMat n 𝕜) where

instance [i : Nonempty n] : NeZero (1 : HermitianMat n 𝕜) := by
  constructor
  intro h
  simpa using congr($h i.some i.some)

end ring
section commring

variable [CommRing α] [StarRing α] [DecidableEq m] [Fintype m]
variable (A : HermitianMat m α) (n : ℕ) (z : ℤ)

noncomputable instance instInv : Inv (HermitianMat m α) :=
  ⟨fun x ↦ ⟨x⁻¹, x.H.inv⟩⟩

@[simp, norm_cast]
theorem mat_inv : (A⁻¹).mat = A.mat⁻¹ := by
  rfl

@[simp]
theorem zero_inv : ((0 : HermitianMat m α)⁻¹) = 0 := by
  ext1; simp

@[simp]
theorem one_inv : ((1 : HermitianMat m α)⁻¹) = 1 := by
  ext1; simp

noncomputable instance instPow : Pow (HermitianMat m α) ℕ :=
  ⟨fun x n ↦ ⟨x ^ n, x.H.pow n⟩⟩

@[simp, norm_cast]
theorem mat_pow (n : ℕ) : (A ^ n).mat = A.mat ^ n := by
  rfl

@[simp]
theorem pow_zero : A ^ 0 = 1 := by
  ext1; simp

@[simp]
theorem zero_pow (hn : n ≠ 0): (0 : HermitianMat m α) ^ n = 0 := by
  ext1; simp [hn]

@[simp]
theorem one_pow : ((1 : HermitianMat m α) ^ n) = 1 := by
  ext1; simp

noncomputable instance instZPow : Pow (HermitianMat m α) ℤ :=
  ⟨fun x z ↦ ⟨x ^ z, x.H.zpow z⟩⟩

@[simp]
theorem mat_zpow (z : ℤ) : (A ^ z).mat = A.mat ^ z := by
  rfl

@[simp, norm_cast]
theorem zpow_natCast : A ^ (n : ℤ) = A ^ n := by
  rfl

@[simp]
theorem zpow_zero : A ^ (0 : ℤ) = 1 := by
  ext1; simp

@[simp]
theorem zpow_one : A ^ (1 : ℤ) = A := by
  ext1; simp

@[simp]
theorem one_zpow : ((1 : HermitianMat m α) ^ z) = 1 := by
  ext1; simp

@[simp]
theorem zpow_neg_one : A ^ (-1 : ℤ) = A⁻¹ := by
  ext1; exact A.mat.zpow_neg_one

@[simp]
theorem inv_zpow : A⁻¹ ^ z = (A ^ z)⁻¹ := by
  ext1; exact A.mat.inv_zpow z

add_aesop_rules safe norm (rule_sets := [Commutes])
  [mat_zero, mat_one, mat_smul, mat_add, mat_sub, mat_neg, mat_pow, mat_zpow, mat_inv]

@[aesop safe apply (rule_sets := [Commutes])]
theorem _root_.Matrix.inv_commute {α : Type*} {A : Matrix m m α} [CommRing α] : Commute A⁻¹ A := by
  rcases A.nonsing_inv_cancel_or_zero with h | h
  · simp [Commute, SemiconjBy, h]
  . simp [h]

@[aesop safe apply (rule_sets := [Commutes])]
theorem commute_inv_self : Commute A⁻¹.mat A.mat := by
  commutes

@[aesop safe apply (rule_sets := [Commutes])]
theorem commute_self_inv : Commute A.mat A⁻¹.mat := by
  commutes

end commring
section rclike

variable [Finite n] in
instance FiniteDimensional : FiniteDimensional ℝ (HermitianMat n 𝕜) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))

@[simp]
theorem im_diag_eq_zero (A : HermitianMat n 𝕜) (x : n) :
    RCLike.im (A x x) = 0 := by
  simpa [CharZero.eq_neg_self_iff] using congrArg (RCLike.im <| · x x) A.H.symm

--Repeat it explicitly for Complex.im so that simp can find it
@[simp]
theorem complex_im_eq_zero (A : HermitianMat n ℂ) (x : n) :
    (A x x).im = 0 :=
  A.im_diag_eq_zero x

end rclike

section conj

variable [CommRing α] [StarRing α] [Fintype n]
variable (A : HermitianMat n α)

set_option backward.isDefEq.respectTransparency false in
/-- The Hermitian matrix given by conjugating by a (possibly rectangular) Matrix. If we required `B` to be
square, this would apply to any `Semigroup`+`StarMul` (as proved by `IsSelfAdjoint.conjugate`). But this lets
us conjugate to other sizes too, as is done in e.g. Kraus operators. That is, it's a _heterogeneous_ conjguation.
-/
def conj {m} (B : Matrix m n α) : HermitianMat n α →+ HermitianMat m α where
  toFun A :=
    ⟨B * A.mat * B.conjTranspose, by
    ext
    simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      star_sum, star_mul', star_star, show ∀ (a b : n), star (A.mat b a) = A.mat a b from congrFun₂ A.property]
    rw [Finset.sum_comm]
    congr! 2
    ring⟩
  map_add' _ _ := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_zero' := by simp

theorem conj_apply (B : Matrix m n α) (A : HermitianMat n α) :
    conj B A = ⟨B * A.mat * B.conjTranspose, (conj B A).2⟩ := by
  rfl

@[simp]
theorem conj_apply_mat (B : Matrix m n α) (A : HermitianMat n α) :
    (A.conj B).mat = B * A.mat * B.conjTranspose := by
  rfl

theorem conj_conj {m l} [Fintype m] (B : Matrix m n α) (C : Matrix l m α) :
    (A.conj B).conj C = A.conj (C * B) := by
  ext1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable (B : HermitianMat n α)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem conj_zero [DecidableEq n] : A.conj (0 : Matrix m n α) = 0 := by
  simp [conj_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem conj_one [DecidableEq n] : A.conj 1 = A := by
  simp [conj_apply]

@[simp]
lemma conj_one_unitary [DecidableEq n] (U : Matrix.unitaryGroup n α) :
    conj U.val 1 = 1 := by
  ext1
  have h : U * U.val.conjTranspose = 1 := U.prop.2
  simp [h]

variable (R : Type*) [Star R] [TrivialStar R] [CommSemiring R] [Algebra R α] [StarModule R α]

/-- `HermitianMat.conj` as an `R`-linear map, where `R` is the ring of relevant reals. -/
def conjLinear {m} (B : Matrix m n α) : HermitianMat n α →ₗ[R] HermitianMat m α where
  toAddHom := conj B
  map_smul' _ _ := by
    ext1
    simp

@[simp]
theorem conjLinear_apply (B : Matrix m n α) : conjLinear R B A = conj B A  := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
lemma continuous_conj (ρ : HermitianMat n 𝕜) : Continuous (ρ.conj (m := m) ·) := by
  simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

end conj

section eigenspace

variable [Fintype n] [DecidableEq n] (A : HermitianMat n 𝕜)

instance [i : Nonempty n] : FaithfulSMul ℝ (HermitianMat n 𝕜) where
  eq_of_smul_eq_smul h := by
    simpa [RCLike.smul_re, -mat_apply] using congr(RCLike.re ($(h 1).val i.some i.some))

/-- The continuous linear map associated with a Hermitian matrix. -/
noncomputable def lin : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := A.mat.toEuclideanLin
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp]
theorem isSymmetric : A.lin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.symm.mp A.H

@[simp]
theorem lin_zero : (0 : HermitianMat n 𝕜).lin = 0 := by
  simp [lin]; rfl

@[simp]
theorem lin_one : (1 : HermitianMat n 𝕜).lin = 1 := by
  simp [lin]; rfl

noncomputable def eigenspace (μ : 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Module.End.eigenspace A.lin μ

/-- The kernel of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.ker A.toMat.toEuclideanLin`. Equivalently, the zero-eigenspace. -/
noncomputable def ker : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.ker A.lin.toLinearMap

theorem mem_ker_iff_mulVec_zero (x : EuclideanSpace 𝕜 n) : x ∈ A.ker ↔ A.mat.mulVec x = 0 := by
  simp [ker, LinearMap.mem_ker, lin, Matrix.toLpLin_apply]

/-- The kernel of a Hermitian matrix is its zero eigenspace. -/
theorem ker_eq_eigenspace_zero : A.ker = A.eigenspace 0 := by
  ext
  simp [ker, eigenspace]

@[simp]
theorem ker_zero : (0 : HermitianMat n 𝕜).ker = ⊤ := by
  simp [ker]

@[simp]
theorem ker_one : (1 : HermitianMat n 𝕜).ker = ⊥ := by
  simp [ker]; rfl

theorem ker_pos_smul {c : ℝ} (hc : c ≠ 0) : (c • A).ker = A.ker := by
  ext x
  simp [mem_ker_iff_mulVec_zero, Matrix.smul_mulVec, hc]

/-- The support of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.range A.toMat.toEuclideanLin`. Equivalently, the sum of all nonzero eigenspaces. -/
noncomputable def support : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.range A.lin.toLinearMap

/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem support_eq_sup_eigenspace_nonzero : A.support = ⨆ μ ≠ 0, A.eigenspace μ := by
  exact A.lin.support_eq_sup_eigenspace_nonzero A.isSymmetric

@[simp]
theorem support_zero : (0 : HermitianMat n 𝕜).support = ⊥ := by
  simp [support]

@[simp]
theorem support_one : (1 : HermitianMat n 𝕜).support = ⊤ := by
  simpa [support] using LinearMap.ker_eq_bot_iff_range_eq_top.mp rfl

@[simp]
theorem ker_orthogonal_eq_support : A.kerᗮ = A.support := by
  rw [ker, support]
  convert ContinuousLinearMap.orthogonal_ker A.lin
  simp

@[simp]
theorem support_orthogonal_eq_range : A.supportᗮ = A.ker := by
  rw [ker, support]
  convert! ContinuousLinearMap.orthogonal_range A.lin
  simp

end eigenspace

section diagonal

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n]

variable (𝕜) in
def diagonal (f : n → ℝ) : HermitianMat n 𝕜 :=
  ⟨Matrix.diagonal (f ·),
    by simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]⟩

variable (f g : n → ℝ)

@[simp]
theorem diagonal_mat : (diagonal 𝕜 f).mat = Matrix.diagonal (f · : n → 𝕜) := by
  rfl

@[simp]
theorem diagonal_apply (i j : n) : diagonal 𝕜 f i j = if i = j then (f i : 𝕜) else 0 := by
  rw [← mat_apply, diagonal_mat, Matrix.diagonal_apply]

@[simp]
theorem diagonal_zero : (diagonal 𝕜 0) = (0 : HermitianMat n 𝕜) := by
  ext1; simp

@[simp]
theorem diagonal_one : (diagonal 𝕜 1) = (1 : HermitianMat n 𝕜) := by
  ext; rw [diagonal_mat]; simp

lemma diagonal_add : diagonal 𝕜 (f + g) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp

lemma diagonal_add_apply : diagonal 𝕜 (fun x ↦ f x + g x) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp

lemma diagonal_sub : diagonal 𝕜 (f - g) = diagonal 𝕜 f - diagonal 𝕜 g := by
  ext1; simp

theorem diagonal_mul (c : ℝ) : diagonal 𝕜 (fun x ↦ c * f x) = c • diagonal 𝕜 f := by
  ext1; simp [← Matrix.diagonal_smul]

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_conj_diagonal [Fintype n] :
    (diagonal 𝕜 f).conj (diagonal 𝕜 g) = diagonal 𝕜 (fun i ↦ f i * (g i)^2) := by
  ext1
  simp [diagonal, conj]
  intro
  ring

/--
A Hermitian matrix is equal to its diagonalization conjugated by its eigenvector unitary matrix.
-/
lemma eq_conj_diagonal [Fintype n] (A : HermitianMat n 𝕜) :
    A = (diagonal 𝕜 A.H.eigenvalues).conj A.H.eigenvectorUnitary := by
  ext1
  exact Matrix.IsHermitian.spectral_theorem A.2

end diagonal

section kronecker
open Kronecker

variable {p q : Type*}
variable [CommRing α] [StarRing α]

/-- The kronecker product of two HermitianMats, see `Matrix.kroneckerMap`. -/
def kronecker (A : HermitianMat m α) (B : HermitianMat n α) : HermitianMat (m × n) α where
  val := A.mat ⊗ₖ B.mat
  property := Matrix.kroneckerMap_IsHermitian A.H B.H

@[inherit_doc HermitianMat.kronecker]
scoped[HermitianMat] infixl:100 " ⊗ₖ " => HermitianMat.kronecker

@[simp, norm_cast]
theorem kronecker_mat (A : HermitianMat m α) (B : HermitianMat n α) :
    (A ⊗ₖ B).mat = A.mat ⊗ₖ B.mat := by
  rfl

theorem kronecker_apply (A : HermitianMat m α) (B : HermitianMat n α) (i j : m × n) :
    (A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2 := by
  rfl

@[simp]
theorem zero_kronecker (A : HermitianMat m α) : (0 : HermitianMat n α) ⊗ₖ A = 0 := by
  ext1; simp

@[simp]
theorem kronecker_zero (A : HermitianMat m α) : A ⊗ₖ (0 : HermitianMat n α) = 0 := by
  ext1; simp

variable [DecidableEq m] [DecidableEq n] in
@[simp]
theorem kronecker_one_one : (1 : HermitianMat m α) ⊗ₖ (1 : HermitianMat n α) = 1 := by
  ext1; simp

variable (A B : HermitianMat m α) (C : HermitianMat n α) in
theorem add_kronecker : (A + B) ⊗ₖ C = A ⊗ₖ C + B ⊗ₖ C := by
  ext1; simp [Matrix.add_kronecker]

variable (A : HermitianMat m α) (B C : HermitianMat n α) in
theorem kronecker_add : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C := by
  ext1; simp [Matrix.kronecker_add]

variable (A B : HermitianMat m α) (C : HermitianMat n α) in
theorem sub_kronecker : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext1
  simp only [kronecker_mat, mat_sub]
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

variable (A : HermitianMat m α) (B C : HermitianMat n α) in
theorem kronecker_sub : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext1
  simp only [kronecker_mat, mat_sub]
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]

lemma kronecker_diagonal [DecidableEq m] [DecidableEq n] (d₁ : m → ℝ) (d₂ : n → ℝ) :
    (diagonal 𝕜 d₁ ⊗ₖ diagonal 𝕜 d₂) = diagonal 𝕜 (fun (i : m × n) => d₁ i.1 * d₂ i.2) := by
  ext1
  simp [Matrix.diagonal_kronecker_diagonal]

/--
A ⊗ₖ B always commutes with C ⊗ₖ D if the pairs commute.
-/
--Apply safely. It will almost always work, but there are cases where it's not sound,
-- such as `A = 0`. But these can all get easily simp'ed away anyway.
@[aesop safe apply (rule_sets := [Commutes])]
theorem kron_commute [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A C : HermitianMat m α} {B D : HermitianMat n α}
    (hAC : Commute A.mat C.mat) (hBD : Commute B.mat D.mat):
    Commute (A ⊗ₖ B).mat (C ⊗ₖ D).mat := by
  rw [commute_iff_eq] at hAC hBD ⊢
  simp only [kronecker_mat, ← Matrix.mul_kronecker_mul, hAC, hBD]

/--
A ⊗ₖ 1 always commutes with 1 ⊗ₖ B
-/
@[aesop safe apply (rule_sets := [Commutes])] --redundant but important shortcut
theorem kron_id_commute_id_kro [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : HermitianMat m α) (B : HermitianMat n α) :
    Commute (A ⊗ₖ (1 : HermitianMat n α)).mat ((1 : HermitianMat m α) ⊗ₖ B).mat := by
  commutes

/-
The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates.
-/
lemma kronecker_conj [Fintype m] [Fintype n]
    (A : HermitianMat m α) (B : HermitianMat n α) (C : Matrix p m α) (D : Matrix q n α) :
    (A ⊗ₖ B).conj (C ⊗ₖ D) = (A.conj C) ⊗ₖ (B.conj D) := by
  ext1
  exact Matrix.kronecker_conj_eq A.mat B.mat C D

end kronecker

section more_range_stuff

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

/-
If the range of a Hermitian matrix is contained in its kernel, the matrix is zero.
-/
theorem range_le_ker_imp_zero {A : HermitianMat d 𝕜}
    (h : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin) : A = 0 := by
  rw [HermitianMat.ext_iff, mat_zero]
  ext i j
  have hA_sq : (A.mat * A.mat) = 0 := by
    simp_all only [SetLike.le_def, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff]
    simp_all only [← Matrix.ext_iff, Matrix.mul_apply, mat_apply, Matrix.zero_apply]
    intro i j
    specialize h ( EuclideanSpace.single j 1 )
    simpa [ Matrix.mulVec, dotProduct ] using congr(WithLp.ofLp $(h) i)
  simp_all only [mat_apply, Matrix.zero_apply]
  replace hA_sq := congr_fun ( congr_fun hA_sq i ) i
  simp_all only [Matrix.mul_apply, mat_apply, Matrix.zero_apply] ;
  -- Since $A$ is Hermitian, we have $A i x * A x i = |A i x|^2$.
  have h_abs : ∀ x, (A i x) * (A x i) = ‖A i x‖ ^ 2 := by
    intro x; have := A.2
    simp_all only [val_eq_coe, sq] ;
    have := congr_fun ( congr_fun this i ) x
    simp_all only [Matrix.star_apply, mat_apply, RCLike.star_def] ;
    simp only [← this, mul_comm, RCLike.norm_conj];
    simp [ ← sq, RCLike.mul_conj ];
  simp_rw [h_abs] at hA_sq
  norm_cast at hA_sq
  simp_all [Finset.sum_eq_zero_iff_of_nonneg]

/--
If ker M ⊆ ker A, then range (A Mᴴ) = range A.
-/
theorem _root_.Matrix.range_mul_conjTranspose_of_ker_le_ker {A : Matrix d d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ LinearMap.ker A.toEuclideanLin) :
    LinearMap.range (A * M.conjTranspose).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    use (M.conjTranspose.toEuclideanLin) y;
    simp [Matrix.toEuclideanLin]
  · intro x hx;
    -- Since $x \in \text{range}(A)$, there exists $y \in \text{range}(Mᴴ)$ such that $A y = x$.
    obtain ⟨y, hy⟩ : ∃ y ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), A.toEuclideanLin y = x := by
      have h_range_MH : LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) = (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        have h_orthogonal : (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)))ᗮ = LinearMap.ker (Matrix.toEuclideanLin M) := by
          ext x
          rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
          simp only [Submodule.mem_orthogonal, LinearMap.mem_ker, LinearMap.mem_range]
          constructor
          · intro h
            rw [← inner_self_eq_zero (𝕜 := 𝕜)]
            have : ∀ y, @inner 𝕜 _ _ y (Matrix.toEuclideanLin M x) = 0 := by
              intro y
              rw [← LinearMap.adjoint_inner_left]
              exact h _ ⟨y, rfl⟩
            exact this _
          · intro h y ⟨z, hz⟩
            rw [← hz, LinearMap.adjoint_inner_left, h, inner_zero_right]
        rw [← h_orthogonal, Submodule.orthogonal_orthogonal]
      obtain ⟨ y, rfl ⟩ := hx;
      -- Since $y$ is in the range of $Mᴴ$, we can write $y$ as $y = y_1 + y_2$ where $y_1 \in \text{range}(Mᴴ)$ and $y_2 \in \text{ker}(M)$.
      obtain ⟨y1, y2, hy1, hy2, hy⟩ : ∃ y1 y2 : EuclideanSpace 𝕜 d, y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) ∧ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M) ∧ y = y1 + y2 := by
        have h_decomp : ∀ y : EuclideanSpace 𝕜 d, ∃ y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), ∃ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M), y = y1 + y2 := by
          intro y
          have h_decomp : y ∈ (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose))) ⊔ (LinearMap.ker (Matrix.toEuclideanLin M)) := by
            rw [ h_range_MH ];
            rw [ sup_comm, Submodule.sup_orthogonal_of_hasOrthogonalProjection ];
            exact Submodule.mem_top;
          rw [ Submodule.mem_sup ] at h_decomp ; tauto;
        exact ⟨ _, _, h_decomp y |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.right ⟩;
      exact ⟨ y1, hy1, by rw [ hy, map_add, LinearMap.mem_ker.mp ( h hy2 ) ] ; simp ⟩;
    obtain ⟨ z, rfl ⟩ := hy.1;
    exact ⟨ z, by simpa [ Matrix.toEuclideanLin ] using hy.2 ⟩

theorem conj_ne_zero {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜} (hA : A ≠ 0)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 := by
  by_contra h_contra
  have h_range : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin := by
    have h_range : LinearMap.range (A.mat * M.conjTranspose).toEuclideanLin ≤ LinearMap.ker M.toEuclideanLin := by
      rintro x ⟨y, rfl⟩
      replace h_contra := congr($(h_contra).mat)
      simp_all [Matrix.toLpLin_apply, Matrix.mul_assoc]
    rw [← Matrix.range_mul_conjTranspose_of_ker_le_ker h]
    exact h_range.trans h
  exact hA (range_le_ker_imp_zero h_range)

theorem conj_ne_zero_iff {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 ↔ A ≠ 0  := by
  refine ⟨?_, (conj_ne_zero · h)⟩
  intro h rfl; grind

section spectrum

variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem _root_.Matrix.IsHermitian.spectrum_rcLike {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.ofReal '' spectrum ℝ A = spectrum 𝕜 A := by
  rw [hA.spectrum_eq_image_range, hA.spectrum_real_eq_range_eigenvalues]

/-- We fix a simp-normal form that, for HermitianMat, we always work in terms
of the real spectrum. -/
@[simp]
theorem spectrum_rcLike (A : HermitianMat n 𝕜) :
    spectrum 𝕜 A.mat = RCLike.ofReal '' spectrum ℝ A.mat := by
  exact A.H.spectrum_rcLike.symm

theorem ne_zero_iff_ne_zero_spectrum (A : HermitianMat n 𝕜) :
    A ≠ 0 ↔ ∃ x ∈ spectrum ℝ A.mat, x ≠ 0 := by
  constructor;
  · intro h_nonzero
    contrapose! h_nonzero
    simp only [HermitianMat.ext_iff, mat_zero]
    rw [A.H.spectral_theorem]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [h_nonzero _ <| A.H.spectrum_real_eq_range_eigenvalues.symm ▸ Set.mem_range_self _]
  · rintro ⟨x, hx, hx'⟩ h
    simp [h, spectrum, resolventSet, Algebra.algebraMap_eq_smul_one,
      hx', Matrix.isUnit_iff_isUnit_det] at hx

open scoped Pointwise in
theorem spectrum_prod
  {A : HermitianMat m 𝕜} {B : HermitianMat n 𝕜} :
    spectrum ℝ (A ⊗ₖ B).mat = spectrum ℝ A.mat * spectrum ℝ B.mat :=
  Matrix.spectrum_prod A.H B.H

end spectrum

--Shortcut instance
noncomputable instance : AddCommMonoid (HermitianMat d ℂ) :=
  inferInstance
