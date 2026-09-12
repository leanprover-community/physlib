/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {d d₁ d₂ d₃ m n : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix

/-
The operator norm of a matrix is the operator norm of the linear map it represents, with respect to the Euclidean norm.
-/
/-- The operator norm of a matrix, with respect to the Euclidean norm (l2 norm) on the domain and codomain. -/
noncomputable def Matrix.opNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-
An isometry preserves the Euclidean norm.
-/
theorem Matrix.isometry_preserves_norm (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ( by positivity ) ( by positivity ), Matrix.Isometry ] at *;
  simp [ EuclideanSpace.norm_eq]
  have h_inner : ∀ x y : EuclideanSpace 𝕜 m, inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x y := by
    intro x y
    have h_inner_eq : inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x (toEuclideanLin A.conjTranspose (toEuclideanLin A y)) := by
      simp [ Matrix.toEuclideanLin, inner ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, ];
      simp [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm_cycle]
    simp_all [ Matrix.toEuclideanLin, toLpLin];
  convert congr_arg Real.sqrt ( congr_arg ( fun z => ‖z‖ ) ( h_inner x x ) ) using 1;
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ];
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
theorem Matrix.opNorm_isometry [Nonempty m] (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  have h_opNorm : ∀ x : EuclideanSpace 𝕜 m, ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
    convert Matrix.isometry_preserves_norm A hA;
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun c hc => hc.1 ⟩;
  · aesop;
  · exact ⟨ 1, ⟨zero_le_one, fun x => le_of_eq (by simp [h_opNorm])⟩ ⟩;
  · norm_num +zetaDelta at *;
    intro b hb h; specialize h ( EuclideanSpace.single ( Classical.arbitrary m ) 1 ) ; aesop;

variable (d₁ d₂) in
/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$.
    The output index is `(d1 \times d2) \times d2`. -/
def map_to_tensor_MES : Matrix ((d₁ × d₂) × d₂) d₁ ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0

theorem map_to_tensor_MES_prop (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (map_to_tensor_MES d₁ d₂).conjTranspose * (Matrix.kronecker A (1 : Matrix d₂ d₂ ℂ)) * (map_to_tensor_MES d₁ d₂) =
    A.traceRight := by
  ext i j; simp [map_to_tensor_MES, Matrix.mul_apply]
  simp [ Finset.sum_ite, Matrix.one_apply]
  rw [ Finset.sum_sigma' ];
  rw [ Finset.sum_congr rfl (g := fun x => A ( i, x.1.2 ) ( j, x.1.2 ))]
  · apply Finset.sum_bij (fun x _ => x.1.2)
    · simp
    · aesop
    · simp
    · simp
  · aesop

/-- The isometry V_rho from the paper. -/
noncomputable def V_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix ((dA × dB) × dB) dA ℂ :=
  let ρA_inv_sqrt := ρAB.traceRight⁻¹.sqrt
  let ρAB_sqrt := ρAB.sqrt
  let I_B := (1 : Matrix dB dB ℂ)
  let term1 := ρAB_sqrt.mat ⊗ₖ I_B
  let term2 := map_to_tensor_MES dA dB
  term1 * term2 * ρA_inv_sqrt.mat

open scoped MatrixOrder ComplexOrder

/-- The isometry V_sigma from the paper. -/
noncomputable def V_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dB × (dB × dC)) dC ℂ :=
  (V_rho (σBC.reindex (Equiv.prodComm dB dC))).reindex
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))
    (Equiv.refl _)

/--
V_rho^H * V_rho simplifies to sandwiching the traceRight by the inverse square root.
-/
lemma V_rho_conj_mul_self_eq (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    let ρA := ρAB.traceRight
    let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
    (V_rho ρAB)ᴴ * (V_rho ρAB) = ρA_inv_sqrt * ρAB.traceRight.mat * ρA_inv_sqrt := by
  -- By definition of $V_rho$, we can write out the product $V_rho^H * V_rho$.
  simp [V_rho];
  simp [ ← Matrix.mul_assoc ];
  have h_simp : (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ))ᴴ * (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ)) = Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ) := by
    have h_simp : (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)ᴴ * (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) = ρAB := by
      convert ρAB.sqrt_sq ( show 0 ≤ ρAB from ?_ ) using 1;
      · simp [ HermitianMat.sqrt ];
      · positivity
    ext ⟨ i, j ⟩ ⟨ k, l ⟩
    simp [ ← h_simp, Matrix.mul_apply ]
    ring_nf
    by_cases hij : j = l
    · simp [ hij, Matrix.one_apply ]
      simp [← Finset.sum_filter]
      refine' Finset.sum_bij ( fun x _ => x.1 ) _ _ _ _ <;> simp
      intro a b
      exact Or.inl ( by simpa using congr_fun ( congr_fun ( ρAB.sqrt.2 ) i ) ( a, b ) )
    · simp [ hij, Matrix.one_apply ]
      exact Finset.sum_eq_zero (by aesop)
  simp_all [ mul_assoc, Matrix.mul_assoc ];
  simp [ ← Matrix.mul_assoc, ← map_to_tensor_MES_prop ]

/--
The partial trace (left) of a positive definite matrix is positive definite.
-/
lemma PosDef_traceRight [Nonempty dB] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceRight.mat.PosDef := by
  have h_trace_right_pos_def : ∀ (x : EuclideanSpace ℂ dA), x ≠ 0 → 0 < ∑ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
    intro x hx_ne_zero
    have h_inner_pos : ∀ k : dB, 0 ≤ (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
      have := (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2;
      intro k
      specialize @this ( fun i => if h : i.2 = k then x i.1 else 0 )
      simp_all only [ne_eq, dite_eq_ite, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.mat_apply, mul_ite, mul_zero, HermitianMat.val_eq_coe, Matrix.submatrix_apply]
      convert this ( show ( fun i : dA × dB => if i.2 = k then x i.1 else 0 ) ≠ 0 from fun h => hx_ne_zero <| by ext i; simpa using congr_fun h ( i, k ) ) |> le_of_lt using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : dA => ( i, k ) ) Finset.univ ) ) ]
      · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Set.InjOn, Finset.coe_univ,
          Set.mem_univ, Prod.mk.injEq, and_true, imp_self, implies_true, Finset.sum_image, ↓reduceIte];
        refine' Finset.sum_congr rfl fun i hi => _;
        refine' congr_arg _ ( Finset.sum_bij ( fun j _ => ( j, k ) ) _ _ _ _ ) <;> simp
      · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, ne_eq, Finset.sum_ite,
          Finset.sum_const_zero, add_zero, mul_eq_zero, map_eq_zero, ite_eq_right_iff, forall_const,
          Prod.forall, Prod.mk.injEq, not_and, forall_eq];
        exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm;
    obtain ⟨k, hk⟩ : ∃ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) > 0 := by
      have := @(Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 ( fun i => x i.1 * ( if i.2 = Classical.arbitrary dB then 1 else 0 ) )
      simp_all only [ne_eq, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.val_eq_coe, Matrix.submatrix_apply, HermitianMat.mat_apply, mul_ite, mul_one, mul_zero]
      contrapose! this
      simp_all only [ne_eq, funext_iff, Pi.zero_apply, ite_eq_right_iff, Prod.forall, forall_eq,
        not_forall, Finset.sum_ite, Finset.sum_const_zero, add_zero] ;
      constructor
      · rw [← Function.ne_iff]
        change _ ≠ 0
        simpa using hx_ne_zero
      convert this ( Classical.arbitrary dB ) using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ.image fun i : dA => ( i, Classical.arbitrary dB ) ) ) ]
      · simp only [Finset.coe_univ, Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq,
          Finset.sum_image, ↓reduceIte, gt_iff_lt]
        congr! 3;
        refine' Finset.sum_bij ( fun y hy => y.1 ) _ _ _ _ <;> simp
      · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, ne_eq, mul_eq_zero,
          map_eq_zero, ite_eq_right_iff, forall_const, Prod.forall, Prod.mk.injEq, not_and, forall_eq]
        exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm ▸ rfl
    exact lt_of_lt_of_le hk ( Finset.single_le_sum ( fun k _ => h_inner_pos k ) ( Finset.mem_univ k ) );
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine' ⟨A.traceRight.2, fun x hx => _ ⟩;
  · convert h_trace_right_pos_def (WithLp.toLp 2 x) (by simpa using hx) using 1;
    unfold HermitianMat.traceRight
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, HermitianMat.mat_mk, HermitianMat.val_eq_coe]
    simp only [Matrix.mulVec, dotProduct, mul_comm, Matrix.submatrix_apply, HermitianMat.mat_apply];
    simp only [Matrix.traceRight, HermitianMat.mat_apply, Matrix.of_apply, mul_comm, Finset.mul_sum]
    rw [Finset.sum_comm_cycle]

lemma PosDef_traceLeft [Nonempty dA] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceLeft.mat.PosDef := by
  exact PosDef_traceRight (A.reindex (Equiv.prodComm _ _)) (hA.reindex _)

/--
V_rho is an isometry.
-/
theorem V_rho_isometry [Nonempty dB] (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (V_rho ρAB)ᴴ * (V_rho ρAB) = 1 := by
  -- Since ρA is positive definite, we can use the fact that ρA_inv_sqrt * ρA * ρA_inv_sqrt = I.
  have h_pos_def : (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) * (ρAB.traceRight : Matrix dA dA ℂ) * (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) = 1 := by
    convert HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one _;
    exact PosDef_traceRight _ hρ
  rw [← h_pos_def]
  exact V_rho_conj_mul_self_eq ρAB hρ

/--
V_sigma is an isometry.
-/
theorem V_sigma_isometry [Nonempty dB] (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 := by
  rw [V_sigma, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    V_rho_isometry (σBC.reindex (Equiv.prodComm dB dC))
      (by rw [HermitianMat.mat_reindex]; exact hσ.reindex _)]
  simp

/-
Definition of W_mat with correct reindexing.
-/
open HermitianMat
open scoped MatrixOrder

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

/-- The operator W from the paper, defined as a matrix product. -/
noncomputable def W_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  let ρA := ρAB.traceRight
  let σC := σBC.traceLeft
  let ρAB_sqrt := (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)
  let σC_inv_sqrt := (σC⁻¹.sqrt : Matrix dC dC ℂ)
  let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
  let σBC_sqrt := (σBC.sqrt : Matrix (dB × dC) (dB × dC) ℂ)

  let term1 := ρAB_sqrt ⊗ₖ σC_inv_sqrt
  let term2 := ρA_inv_sqrt ⊗ₖ σBC_sqrt
  let term2_reindexed := term2.reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

  term1 * term2_reindexed

/--
The operator norm of a matrix product is at most the product of the operator norms.
-/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
    ext; simp [toEuclideanLin]
  simp only [Matrix.opNorm, h_comp]
  exact ContinuousLinearMap.opNorm_comp_le (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B))

theorem Matrix.opNorm_reindex_proven {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (e : m ≃ l) (f : n ≃ p) (A : Matrix m n 𝕜) :
    Matrix.opNorm (A.reindex e f) = Matrix.opNorm A := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun c hc => hc.1 ⟩;
    · refine' ⟨ norm_nonneg _, fun x => _ ⟩;
      convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( Matrix.toEuclideanLin A ) ) (WithLp.toLp 2 ( fun i => x ( f i ) )) using 1;
      · simp [ Matrix.toEuclideanLin, EuclideanSpace.norm_eq ];
        rw [ ← Equiv.sum_comp e.symm ] ; aesop;
      · simp [ EuclideanSpace.norm_eq, Matrix.opNorm ];
        exact Or.inl ( by rw [ ← Equiv.sum_comp f ] );
  · refine' ContinuousLinearMap.opNorm_le_bound _ _ fun a => _;
    · exact ContinuousLinearMap.opNorm_nonneg _;
    · convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( toEuclideanLin ( Matrix.reindex e f A ) ) ) (WithLp.toLp 2 ( fun i => a ( f.symm i ) )) using 1;
      · simp [ EuclideanSpace.norm_eq, Matrix.toEuclideanLin ];
        rw [ ← Equiv.sum_comp e.symm ]
        simp [ Matrix.mulVec, dotProduct ] ;
      · congr! 2;
        simp [ EuclideanSpace.norm_eq]
        conv_lhs => rw [ ← Equiv.sum_comp f.symm ] ;

/--
Define U_rho as the Kronecker product of V_rho and the identity.
-/
noncomputable def U_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix (((dA × dB) × dB) × dC) (dA × dC) ℂ :=
  Matrix.kronecker (V_rho ρAB) (1 : Matrix dC dC ℂ)

/--
Define U_sigma as the Kronecker product of the identity and V_sigma.
-/
noncomputable def U_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dA × (dB × (dB × dC))) (dA × dC) ℂ :=
  Matrix.kronecker (1 : Matrix dA dA ℂ) (V_sigma σBC)

/--
The operator norm of the conjugate transpose is equal to the operator norm.
-/
theorem Matrix.opNorm_conjTranspose_eq_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.opNorm Aᴴ = Matrix.opNorm A := by
  unfold Matrix.opNorm
  rw [← ContinuousLinearMap.adjoint.norm_map (toEuclideanLin A).toContinuousLinearMap]
  rw [toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem isometry_mul_conjTranspose_le_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1) :
    V * V.conjTranspose ≤ 1 := by
  have h_pos : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp [ sub_mul, mul_sub, ← Matrix.mul_assoc ];
    simp [ Matrix.mul_assoc, hV ];
  have h_pos : (1 - V * Vᴴ) = (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) := by
    simp_all [ Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul ];
  have h_pos : Matrix.PosSemidef (1 - V * Vᴴ) := by
    rw [ h_pos ] at *; apply Matrix.posSemidef_conjTranspose_mul_self;
  exact Matrix.le_iff.mpr h_pos

/-
If `A†A = I` and `B†B = I` (both isometries into the same space), then `||(A†B)|| ≤ 1`,
  equivalently `(A†B)†(A†B) ≤ I`.
-/
theorem conjTranspose_isometry_mul_isometry_le_one {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix k m ℂ) (B : Matrix k n ℂ)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A.conjTranspose * B).conjTranspose * (A.conjTranspose * B) ≤ 1 := by
  have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ 1 := by
    have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ (Bᴴ * B) := by
      have h_le : (A * Aᴴ) ≤ 1 := by
        apply isometry_mul_conjTranspose_le_one A hA;
      -- Apply the fact that if $X \leq Y$, then $CXC^* \leq CYC^*$ for any matrix $C$.
      have h_conj : ∀ (C : Matrix n k ℂ) (X Y : Matrix k k ℂ), X ≤ Y → C * X * Cᴴ ≤ C * Y * Cᴴ :=
        fun C X Y a => Matrix.PosSemidef.mul_mul_conjTranspose_mono C a
      simpa [ Matrix.mul_assoc ] using h_conj Bᴴ ( A * Aᴴ ) 1 h_le;
    aesop;
  simpa [ Matrix.mul_assoc ] using h_le

/-! ### Helper lemmas for operator_ineq_SSA -/

/- Reindexing preserves the HermitianMat ordering. -/
theorem HermitianMat.reindex_le_reindex_iff {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (e : d ≃ d₂) (A B : HermitianMat d ℂ) :
    A.reindex e ≤ B.reindex e ↔ A ≤ B := by
  constructor <;> intro h <;> rw [HermitianMat.le_iff] at * <;> aesop;

/- Inverse of a Kronecker product of HermitianMat. -/
theorem HermitianMat.inv_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    [A.NonSingular] [B.NonSingular] :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = 1 := by
    have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = (A.mat * A⁻¹.mat) ⊗ₖ (B.mat * B⁻¹.mat) := by
      ext i j; simp [ Matrix.mul_apply, Matrix.kroneckerMap ] ;
      simp only [mul_assoc, Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [ ← Finset.sum_product' ] ; congr ; ext ; ring!;
    aesop;
  refine' Subtype.ext ( Matrix.inv_eq_right_inv h_inv )

/- Inverse of a reindexed HermitianMat. -/
theorem HermitianMat.inv_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂) :
    (A.reindex e)⁻¹ = A⁻¹.reindex e := by
  ext1
  simp

/- Kronecker of PosDef matrices is PosDef. -/
theorem HermitianMat.PosDef_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    (A ⊗ₖ B).mat.PosDef := by
  exact Matrix.PosDef.kron hA hB

/- Reindex of PosDef is PosDef. -/
theorem HermitianMat.PosDef_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂)
    (hA : A.mat.PosDef) :
    (A.reindex e).mat.PosDef := by
  convert! hA.reindex e

/-- The sandwich matrix S used in the proof of intermediate_ineq.
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
private noncomputable def S_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ σBC.sqrt.mat).reindex
    (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

/- W†W = S * (ρ_AB ⊗ σ_C⁻¹) * S, i.e. W†W equals the conj of LHS by S.
This follows from: W = (ρAB^½ ⊗ σC^{-½}) * S, so W†W = S† * (ρAB^½ ⊗ σC^{-½})† * (ρAB^½ ⊗ σC^{-½}) * S
= S * (ρAB ⊗ σC⁻¹) * S (using sqrt_sq and Hermiticity of S).
-/
private lemma W_mat_sq_eq_conj [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    (W_mat ρAB σBC)ᴴ * (W_mat ρAB σBC) =
      S_mat ρAB σBC * (ρAB ⊗ₖ (σBC.traceLeft)⁻¹).mat * S_mat ρAB σBC := by
  unfold W_mat S_mat;
  simp [ Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker ];
  have h_simp : (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) * (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) = ρAB ∧ (σBC.traceLeft⁻¹.sqrt : Matrix dC dC ℂ) * (σBC.traceLeft⁻¹.sqrt : Matrix dC dC ℂ) = σBC.traceLeft⁻¹ := by
    constructor;
    · exact sqrt_sq (by positivity)
    · convert sqrt_sq ( show 0 ≤ ( σBC.traceLeft⁻¹ : HermitianMat dC ℂ ) from ?_ ) using 1;
      have h_inv_pos : (σBC.traceLeft⁻¹ : HermitianMat dC ℂ).mat.PosDef := by
        have h_inv_pos : (σBC.traceLeft : Matrix dC dC ℂ).PosDef := by
          exact PosDef_traceLeft σBC hσ;
        convert! h_inv_pos.inv using 1;
      convert! h_inv_pos.posSemidef using 1;
      exact zero_le_iff;
  have h_simp : (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ (σBC.traceLeft⁻¹.sqrt : Matrix dC dC ℂ) * (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ (σBC.traceLeft⁻¹.sqrt : Matrix dC dC ℂ) = (ρAB : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ (σBC.traceLeft⁻¹ : Matrix dC dC ℂ) := by
    have h_simp : ∀ (A B C D : Matrix (dA × dB) (dA × dB) ℂ) (E F : Matrix dC dC ℂ), (A ⊗ₖ E) * (B ⊗ₖ F) = (A * B) ⊗ₖ (E * F) := by
      exact fun A B C D E F => Eq.symm (Matrix.mul_kronecker_mul A B E F);
    aesop;
  simp_all [ ← Matrix.mul_assoc ]

/- **Step 2**: S * (ρ_A ⊗ σ_BC⁻¹).reindex * S = I.
This follows from (ρ_A^{-½} * ρ_A * ρ_A^{-½}) ⊗ (σ_BC^½ * σ_BC⁻¹ * σ_BC^½) = I ⊗ I = I.
-/
private lemma S_mat_conj_rhs_eq_one [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    S_mat ρAB σBC * ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm).mat *
      S_mat ρAB σBC = 1 := by
  have h_comm : Commute (σBC.sqrt.mat) (σBC⁻¹.mat) := by
    have h_comm : Commute (σBC.sqrt.mat) (σBC.mat) := by
      exact commute_sqrt_left rfl;
    have h_comm_inv : Commute (σBC.sqrt.mat) (σBC.mat) → Commute (σBC.sqrt.mat) (σBC⁻¹.mat) := by
      intro h_comm
      have h_comm_inv : Commute (σBC.sqrt.mat) (σBC.mat) → Commute (σBC.sqrt.mat) (σBC.mat⁻¹) := by
        intro h_comm
        have h_inv : σBC.mat⁻¹ * σBC.sqrt.mat = σBC.sqrt.mat * σBC.mat⁻¹ := by
          have h_inv : σBC.mat⁻¹ * σBC.sqrt.mat * σBC.mat = σBC.sqrt.mat := by
            simp [ mul_assoc, h_comm.eq ];
            rw [ ← mul_assoc, Matrix.nonsing_inv_mul _ ];
            · rw [ one_mul ];
            · exact isUnit_iff_ne_zero.mpr hσ.det_pos.ne';
          have h_inv : σBC.mat⁻¹ * σBC.sqrt.mat * σBC.mat * σBC.mat⁻¹ = σBC.sqrt.mat * σBC.mat⁻¹ := by
            rw [h_inv];
          convert h_inv using 1 ; simp [ mul_assoc, hσ.det_pos.ne' ]
        exact h_inv.symm;
      convert! h_comm_inv h_comm using 1;
    exact h_comm_inv h_comm;
  have h_comm : σBC.sqrt.mat * σBC⁻¹.mat * σBC.sqrt.mat = σBC.mat * σBC⁻¹.mat := by
    rw [ mul_assoc, ← h_comm.eq ];
    rw [ ← Matrix.mul_assoc, HermitianMat.sqrt_sq ];
    convert hσ.posSemidef using 1;
    exact zero_le_iff;
  have h_comm : ρAB.traceRight⁻¹.sqrt.mat * ρAB.traceRight.mat * ρAB.traceRight⁻¹.sqrt.mat = 1 := by
    have h_comm : ρAB.traceRight.mat.PosDef := by
      apply_rules [ PosDef_traceRight ];
    convert sqrt_inv_mul_self_mul_sqrt_inv_eq_one h_comm using 1;
  convert congr_arg₂ ( fun x y => Matrix.kronecker x y |> Matrix.reindex ( Equiv.prodAssoc dA dB dC ).symm ( Equiv.prodAssoc dA dB dC ).symm ) h_comm ( show ( σBC.sqrt.mat * σBC⁻¹.mat * σBC.sqrt.mat ) = 1 from ?_ ) using 1;
  · unfold S_mat; simp [ *, Matrix.mul_assoc ] ;
    ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ Matrix.mul_apply, Matrix.kroneckerMap_apply ] ; ring_nf
    simp only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul];
    simp only [← Finset.sum_product'];
    refine' Finset.sum_bij ( fun x _ => ( x.1.2, x.2.2, x.1.1, x.2.1 ) ) _ _ _ _ <;> simp;
    exact fun _ _ _ _ _ _ => Or.inl <| by ring;
  · ext ⟨ i, j ⟩ ⟨ k, l ⟩
    simp [Matrix.one_apply]
    aesop
  · have := hσ.det_pos.ne'
    have := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hσ.det_pos.ne')
    aesop;

/- Key factorization: W_mat = (F ⊗ I_C) * (I_A ⊗ G).reindex, where
  F = ρAB.sqrt * (ρA⁻¹.sqrt ⊗ I_B) and G = (I_B ⊗ σC⁻¹.sqrt) * σBC.sqrt.
  This expresses W as a "contraction over the shared B index". -/
private lemma W_mat_eq_factored
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    W_mat ρAB σBC =
      let F := ρAB.sqrt.mat * (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))
      let G := ((1 : Matrix dB dB ℂ) ⊗ₖ σBC.traceLeft⁻¹.sqrt.mat) * σBC.sqrt.mat
      (F ⊗ₖ (1 : Matrix dC dC ℂ)) *
        ((1 : Matrix dA dA ℂ) ⊗ₖ G).reindex
          (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm := by
  -- By definition of matrix multiplication and the properties of the Kronecker product, we can expand both sides.
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩; simp [Matrix.mul_apply, Matrix.kroneckerMap, Matrix.one_apply, Matrix.reindex];
  unfold W_mat; simp [ Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex ] ;
  simp [ Finset.sum_ite, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm];
  simp [ Finset.sum_filter, Finset.sum_sigma' ];
  rw [ ← Finset.sum_filter ];
  refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ ⟨ a', x.1.2 ⟩, c ⟩, ⟨ ⟨ x.1.2, x.2 ⟩, x.1 ⟩ ⟩ ) _ _ _ _ <;> simp;
  aesop

/- Connection between F and V_rho via the MES:
(F ⊗ I_B) * MES = V_rho, where F = ρAB.sqrt * (ρA⁻¹.sqrt ⊗ I_B).-/
private lemma F_tensor_MES_eq_V_rho
    (ρAB : HermitianMat (dA × dB) ℂ) :
    let F := ρAB.sqrt.mat * (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))
    (F ⊗ₖ (1 : Matrix dB dB ℂ)) * map_to_tensor_MES dA dB = V_rho ρAB := by
  ext ⟨i, j⟩ k; simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, map_to_tensor_MES];
  unfold V_rho; simp [ Matrix.mul_apply, Matrix.kroneckerMap_apply, map_to_tensor_MES ] ;
  simp [ Finset.sum_ite, Matrix.one_apply, mul_comm, Finset.mul_sum]
  rw [ Finset.sum_sigma' ] ; simp [ eq_comm, Finset.filter_filter ] ;
  refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ ⟨ k, j ⟩, j ⟩, x, j ⟩ ) _ _ _ _ <;> simp [ eq_comm ];
  · aesop ( simp_config := { singlePass := true } ) ;
  · intro a; rw [ Finset.sum_eq_single ⟨ ( a, j ), j ⟩ ] <;> aesop;

section Wmat_calculation

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

abbrev BigIdx (dA dB dC : Type*) := ((dA × dB) × dB) × (dB × dC)
abbrev SmallIdx (dA dB dC : Type*) := (dA × dB) × dC
abbrev MidIdx (dA dB dC : Type*) := (dA × dB) × (dB × (dB × dC))

/-- The associator equivalence (no swap needed).
    Maps (((dA×dB)×dB)×(dB×dC)) to ((dA×dB)×(dB×(dB×dC))). -/
private def assoc_equiv (dA dB dC : Type*) :
    BigIdx dA dB dC ≃ MidIdx dA dB dC :=
  Equiv.prodAssoc (dA × dB) dB (dB × dC)

variable (dA dB dC) in
private def T₁_mat (ρAB : HermitianMat (dA × dB) ℂ) :
    Matrix (BigIdx dA dB dC) (SmallIdx dA dB dC) ℂ :=
  (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ)).reindex
    (Equiv.refl _) (Equiv.prodAssoc dA dB dC).symm

variable (dA dB dC) in
private def T₂_mat (σBC : HermitianMat (dB × dC) ℂ) :
    Matrix (SmallIdx dA dB dC) (MidIdx dA dB dC) ℂ :=
  (1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ (V_sigma σBC)ᴴ

private def PERM_mat (dA dB dC : Type*) [Fintype dA] [Fintype dB] [Fintype dC]
    [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] :
    Matrix (MidIdx dA dB dC) (BigIdx dA dB dC) ℂ :=
  (1 : Matrix (BigIdx dA dB dC) (BigIdx dA dB dC) ℂ).reindex
    (assoc_equiv dA dB dC) (Equiv.refl _)

private lemma T₁_isometry [Nonempty dB]
    (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (T₁_mat dA dB dC ρAB)ᴴ * (T₁_mat dA dB dC ρAB) = 1 := by
  have h_kron : (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ))ᴴ *
      (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ)) = 1 := by
    have hV := V_rho_isometry ρAB hρ
    convert congr_arg (fun m => Matrix.kroneckerMap (· * ·) m (1 : Matrix (dB × dC) (dB × dC) ℂ)) hV using 1
    · ext i j
      simp [Matrix.mul_apply, Matrix.kroneckerMap, Matrix.one_apply]
      by_cases hij : i.2 = j.2 <;> simp [hij, Finset.sum_ite]
      · exact Finset.sum_bij (fun x _ ↦ x.1) (by aesop) (by aesop) (by aesop) (by aesop)
      · exact Finset.sum_eq_zero (by aesop)
    · ext i j
      simp [Matrix.one_apply]
      aesop
  rw [T₁_mat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    h_kron, Matrix.submatrix_one_equiv]

private lemma T₂_sq_le_one [Nonempty dB]
    (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (T₂_mat dA dB dC σBC)ᴴ * (T₂_mat dA dB dC σBC) ≤ 1 := by
  have hT₂_isometry : (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 :=
    V_sigma_isometry σBC hσ
  convert isometry_mul_conjTranspose_le_one (Matrix.kronecker (1 : Matrix (dA × dB) (dA × dB) ℂ) (V_sigma σBC)) _ using 1
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.mul_apply]
    ring_nf
    unfold T₂_mat
    simp [Matrix.one_apply]
    ring_nf
    congr! 2
    · exact eq_comm
    · aesop
  · convert congr_arg (Matrix.kronecker (1 : Matrix (dA × dB) (dA × dB) ℂ)) hT₂_isometry using 1
    · ext ⟨ i, j ⟩ ⟨ k, l ⟩
      simp [ Matrix.mul_apply]
      ring_nf
      simp [ Matrix.one_apply, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
      split_ifs <;> simp_all [ Finset.sum_ite ]
      subst i
      refine' Finset.sum_bij ( fun x _ => x.2 ) _ _ _ _
      · aesop
      · aesop
      · aesop
      · aesop
    · aesop

private lemma PERM_isometry : (PERM_mat dA dB dC)ᴴ * PERM_mat dA dB dC = 1 := by
  simp [PERM_mat]

/-- Element-wise identity: W_mat = ∑_{b*} V_rho * V_sigma†.
    This is the key computation from Eq. (6) of Lin-Kim-Hsieh. -/
private lemma W_mat_entry (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (i j : SmallIdx dA dB dC) :
    W_mat ρAB σBC i j =
      ∑ b_star : dB,
        V_rho ρAB ((i.1, b_star)) j.1.1 *
        (V_sigma σBC)ᴴ i.2 (b_star, (j.1.2, j.2)) := by
  obtain ⟨⟨a, b⟩, c⟩ := i
  obtain ⟨⟨a', b'⟩, c'⟩ := j
  simp only [W_mat, V_sigma, V_rho, map_to_tensor_MES]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Matrix.of_apply, Equiv.prodAssoc_apply,
    Equiv.prodComm_apply, Equiv.prodComm_symm, Equiv.refl_apply, Equiv.refl_symm,
    Equiv.prodCongr_apply, Equiv.prodCongr_symm,
    Equiv.symm_trans_apply,
    Prod.swap, Equiv.symm_symm,  Prod.map_apply]
  simp only [apply_ite star, star_zero, mul_ite, mul_one, mul_zero, star_mul', star_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [show Finset.univ (α := (dA × dB) × dC) =
    (Finset.univ ×ˢ Finset.univ : Finset ((dA × dB) × dC))
    from Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  rw [show Finset.univ (α := dA × dB) =
    (Finset.univ ×ˢ Finset.univ : Finset (dA × dB))
    from Finset.univ_product_univ.symm]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_comm (s := Finset.univ (α := dA))]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- Goal: LHS (triple sum, clean) = RHS (sums with ite conditions)
  -- Strategy: simplify ite sums on RHS, relate reindex terms, match.
  -- Step 1: collapse ite sums using Finset.sum_eq_single
  -- Convert ↑A i j to A i j throughout
  simp only [HermitianMat.mat_apply]
  -- Collapse ite sums: ρ part
  have h_ite_rho : ∀ (i : dA) (x : dB) (f : dA × dB → ℂ),
      (∑ i_1 : (dA × dB) × dB, if i_1.1.1 = i ∧ i_1.1.2 = i_1.2 then if x = i_1.2 then f i_1.1 else 0 else 0) =
      f (i, x) := by
    intro i x f; rw [Finset.sum_eq_single ⟨(i, x), x⟩]
    · simp
    · intro ⟨⟨a₀, b₀⟩, b₁⟩ _ hne; split_ifs with h h2 <;> simp_all [Prod.mk.injEq]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [h_ite_rho]
  -- σ part: pull out constant factor, then collapse
  simp_rw [← Finset.sum_mul]
  -- Now the σ inner sum has the same shape as h_ite_rho but for dC×dB
  have h_ite_sigma : ∀ (i : dC) (x : dB) (f : dC × dB → ℂ),
      (∑ i_1 : (dC × dB) × dB, if i_1.1.1 = i ∧ i_1.1.2 = i_1.2 then if x = i_1.2 then f i_1.1 else 0 else 0) =
      f (i, x) := by
    intro i x f; rw [Finset.sum_eq_single ⟨(i, x), x⟩]
    · simp
    · intro ⟨⟨a₀, b₀⟩, b₁⟩ _ hne; split_ifs with h h2 <;> simp_all [Prod.mk.injEq]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Collapse σ ite sum using conv to navigate into the RHS
  conv_rhs =>
    arg 2; ext x_outer
    arg 2; arg 2; ext x_1
    arg 1
    rw [h_ite_sigma x_1 x_outer (fun p => star ((σBC.reindex (Equiv.prodComm dB dC)).sqrt (c', b') p))]
  -- Now relate reindexed σBC terms to original terms
  -- cfc_reindex: (A.reindex e).sqrt = A.sqrt.reindex e
  simp only [show (σBC.reindex (Equiv.prodComm dB dC)).sqrt =
    σBC.sqrt.reindex (Equiv.prodComm dB dC) from
    σBC.cfc_reindex Real.sqrt (Equiv.prodComm dB dC)]
  -- traceRight of reindex(prodComm) = traceLeft
  simp only [show (σBC.reindex (Equiv.prodComm dB dC)).traceRight = σBC.traceLeft from by
    ext i j; simp only [HermitianMat.traceRight, HermitianMat.traceLeft,
      Matrix.traceRight, Matrix.traceLeft, HermitianMat.reindex,
      Matrix.reindex_apply, HermitianMat.mat_mk, Matrix.of_apply,
      Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]]
  -- Hermiticity
  have h1 : σBC.sqrt.matᴴ = σBC.sqrt.mat := σBC.sqrt.2
  have h2 : σBC.traceLeft⁻¹.sqrt.matᴴ = σBC.traceLeft⁻¹.sqrt.mat := σBC.traceLeft⁻¹.sqrt.2
  -- Expand product of sums and match
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Both sides are triple sums with the same structure. Match element-wise.
  refine Finset.sum_congr rfl fun x_bd _ => Finset.sum_congr rfl fun x_1 _ =>
    Finset.sum_congr rfl fun x_2 _ => ?_
  -- Now a single-term equality
  -- star of reindexed entry: def-eq gives star(σBC.sqrt (b',c') (x_bd,x_2))
  -- then Hermiticity gives σBC.sqrt (x_bd,x_2) (b',c')
  have hs1 : star ((σBC.sqrt.reindex (Equiv.prodComm dB dC)) (c', b') (x_2, x_bd)) =
      σBC.sqrt (x_bd, x_2) (b', c') :=
    CStarMatrix.star_apply_of_isSelfAdjoint h1
  have hs2 : star (σBC.traceLeft⁻¹.sqrt x_2 c) = σBC.traceLeft⁻¹.sqrt c x_2 :=
    CStarMatrix.star_apply_of_isSelfAdjoint h2
  rw [hs1, hs2]; ring

/-- Element-wise identity: RHS = ∑_{b*} V_rho * V_sigma†. -/
private lemma RHS_entry (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (i j : SmallIdx dA dB dC) :
    (T₂_mat dA dB dC σBC * PERM_mat dA dB dC * T₁_mat dA dB dC ρAB) i j =
      ∑ b_star : dB,
        V_rho ρAB ((i.1, b_star)) j.1.1 *
        (V_sigma σBC)ᴴ i.2 (b_star, (j.1.2, j.2)) := by
  obtain ⟨⟨a, b⟩, c⟩ := i
  obtain ⟨⟨a', b'⟩, c'⟩ := j
  simp only [Matrix.mul_apply, T₂_mat, T₁_mat, PERM_mat, assoc_equiv,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.reindex_apply,
    Equiv.prodAssoc_symm_apply, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.prodAssoc_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [mul_ite, mul_one, mul_zero]
  have h_inner : ∀ (x : BigIdx dA dB dC),
    (∑ x_1 : MidIdx dA dB dC,
      if (a, b) = x_1.1
      then if ((x_1.1, x_1.2.1), x_1.2.2) = x then star (V_sigma σBC x_1.2 c) else 0
      else 0) =
    if x.1.1 = (a, b) then star (V_sigma σBC (x.1.2, x.2) c) else 0 := by
    intro ⟨⟨p, q⟩, r⟩
    rw [Finset.sum_eq_single ⟨(a, b), (q, r)⟩]
    · simp [eq_comm]
    · intro ⟨s, ⟨t, u⟩⟩ _ hne; split_ifs with h1 h2 <;> try rfl
      exfalso; apply hne; ext <;> grind only
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [h_inner, ite_mul, zero_mul]
  rw [show Finset.univ (α := BigIdx dA dB dC) = (Finset.univ ×ˢ Finset.univ : Finset (((dA × dB) × dB) × (dB × dC)))
    from Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show Finset.univ (α := (dA × dB) × dB) = (Finset.univ ×ˢ Finset.univ : Finset ((dA × dB) × dB))
    from Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  simp only [RCLike.star_def, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  simp_rw [mul_comm]

private lemma W_mat_eq_three_factors [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    W_mat ρAB σBC =
      T₂_mat dA dB dC σBC * PERM_mat dA dB dC * T₁_mat dA dB dC ρAB := by
  ext i j
  rw [W_mat_entry, RHS_entry]

/-- Core inequality: W†W ≤ I.
This is the key step, following from the isometry argument:
V_rho ⊗ I_C and I_A ⊗ V_sigma are isometries, their cross product has norm ≤ 1,
and the result can be related to W_mat through the MES computation (Eq. 6 in Lin-Kim-Hsieh). -/
theorem W_mat_sq_le_one [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    (W_mat ρAB σBC)ᴴ * (W_mat ρAB σBC) ≤ 1 := by
  rw [W_mat_eq_three_factors]
  have h_T₂ := T₂_sq_le_one (dA := dA) σBC hσ
  have h_step1 : (PERM_mat dA dB dC)ᴴ * ((T₂_mat dA dB dC σBC)ᴴ * (T₂_mat dA dB dC σBC)) *
      PERM_mat dA dB dC ≤ 1 := by
    calc _ ≤ (PERM_mat dA dB dC)ᴴ * 1 * PERM_mat dA dB dC :=
          Matrix.PosSemidef.conjTranspose_mul_mul_mono _ h_T₂
        _ = 1 := by rw [Matrix.mul_one, PERM_isometry]
  calc _ = (T₁_mat dA dB dC ρAB)ᴴ * ((PERM_mat dA dB dC)ᴴ *
          ((T₂_mat dA dB dC σBC)ᴴ * (T₂_mat dA dB dC σBC)) *
          PERM_mat dA dB dC) * (T₁_mat dA dB dC ρAB) := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ ≤ (T₁_mat dA dB dC ρAB)ᴴ * 1 * (T₁_mat dA dB dC ρAB) :=
        Matrix.PosSemidef.conjTranspose_mul_mul_mono _ h_step1
      _ = 1 := by rw [Matrix.mul_one, T₁_isometry _ hρ]

end Wmat_calculation

/- S_mat is invertible (since ρ_A and σ_BC are positive definite). -/
private lemma S_mat_isUnit [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    IsUnit (S_mat ρAB σBC) := by
  rw [ Matrix.isUnit_iff_isUnit_det ];
  -- Since ρAB and σBC are positive definite, their square roots are also invertible.
  have h_inv_sqrt : IsUnit (ρAB.traceRight⁻¹.sqrt.mat.det) ∧ IsUnit (σBC.sqrt.mat.det) := by
    constructor;
    · have h_det_ne_zero : ∀ (A : HermitianMat (dA) ℂ), A.mat.PosDef → (A.sqrt).mat.det ≠ 0 := by
        intro A hA
        have h_det_ne_zero : (A.sqrt).mat.PosDef := by
          exact sqrt_posDef hA;
        exact h_det_ne_zero.det_pos.ne';
      exact isUnit_iff_ne_zero.mpr ( h_det_ne_zero _ <| by simpa using PosDef_traceRight _ hρ |> fun h => h.inv );
    · have h_inv_sqrt : σBC.sqrt.mat.PosDef := by
        exact sqrt_posDef hσ;
      exact isUnit_iff_ne_zero.mpr h_inv_sqrt.det_pos.ne';
  unfold S_mat;
  simp_all [ Matrix.det_kronecker]

/-- The intermediate operator inequality: ρ_AB ⊗ σ_C⁻¹ ≤ (ρ_A ⊗ σ_BC⁻¹).reindex(assoc⁻¹).
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
theorem intermediate_ineq [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB ⊗ₖ (σBC.traceLeft)⁻¹ ≤
      (ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm := by
  have h_sorted : (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ σBC.sqrt.mat).reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm * (ρAB ⊗ₖ (σBC.traceLeft)⁻¹).mat * (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ σBC.sqrt.mat).reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm ≤ (1 : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ) := by
    convert W_mat_sq_le_one ρAB σBC hρ hσ using 1;
    convert! W_mat_sq_eq_conj ρAB σBC hρ hσ |> Eq.symm using 1;
  convert h_sorted using 1;
  rw [HermitianMat.le_iff];
  rw [ ← S_mat_conj_rhs_eq_one ρAB σBC hρ hσ ];
  simp only [ Matrix.posSemidef_iff_dotProduct_mulVec ]
  constructor <;> intro h <;> simp_all
  · convert! h_sorted using 1;
    convert! S_mat_conj_rhs_eq_one ρAB σBC hρ hσ using 1;
  · have := S_mat_isUnit ρAB σBC hρ hσ;
    cases' this.nonempty_invertible with u hu;
    have h_pos_semidef : Matrix.PosSemidef ((S_mat ρAB σBC)⁻¹ * (S_mat ρAB σBC * ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm).mat * S_mat ρAB σBC - S_mat ρAB σBC * (ρAB ⊗ₖ (σBC.traceLeft)⁻¹).mat * S_mat ρAB σBC) * (S_mat ρAB σBC)⁻¹ᴴ) := by
      exact Matrix.PosSemidef.mul_mul_conjTranspose_same h (S_mat ρAB σBC)⁻¹;
    simp_all [ Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub ];
    simp_all [ Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian ];
    have h_conj : (S_mat ρAB σBC)ᴴ = S_mat ρAB σBC := by
      unfold S_mat; simp [ Matrix.conjTranspose_kronecker, Matrix.conjTranspose_submatrix ] ;
    simp_all [  Matrix.conjTranspose_nonsing_inv ]

open HermitianMat in
/-- **Operator extension of SSA** (Main result of Lin-Kim-Hsieh).
  For positive definite ρ_AB and σ_BC:
  `ρ_A⁻¹ ⊗ σ_BC ≤ ρ_AB⁻¹ ⊗ σ_C`
  where ρ_A = Tr_B(ρ_AB) and σ_C = Tr_B(σ_BC), and the RHS is reindexed
  via the associator `(dA × dB) × dC ≃ dA × (dB × dC)`. -/
theorem operator_ineq_SSA [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB.traceRight⁻¹ ⊗ₖ σBC ≤
      (ρAB⁻¹ ⊗ₖ σBC.traceLeft).reindex (Equiv.prodAssoc dA dB dC) := by
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ ≤ (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ := by
    apply HermitianMat.inv_antitone;
    · apply HermitianMat.PosDef_kronecker ρAB (σBC.traceLeft)⁻¹ hρ (PosDef_traceLeft σBC hσ).inv;
    · exact intermediate_ineq ρAB σBC hρ hσ;
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ = (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm := by
    have h_inv_symm : (ρAB.traceRight ⊗ₖ σBC⁻¹)⁻¹ = ρAB.traceRight⁻¹ ⊗ₖ (σBC⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker _ _ using 1;
      · infer_instance;
      · exact ⟨ ⟨ Classical.arbitrary dB, Classical.arbitrary dC ⟩ ⟩;
      · have h_trace_right_pos_def : (ρAB.traceRight).mat.PosDef := by
          exact PosDef_traceRight ρAB hρ
        exact ⟨by exact PosDef_traceRight ρAB hρ |>.isUnit⟩
      · have h_inv_symm : σBC⁻¹.NonSingular := by
          have h_inv_symm : σBC.NonSingular := by
            exact nonSingular_of_posDef hσ
          exact nonSingular_iff_inv.mpr h_inv_symm;
        exact h_inv_symm;
    convert congr_arg ( fun x : HermitianMat _ _ => x.reindex ( Equiv.prodAssoc dA dB dC ).symm ) h_inv_symm using 1;
    · apply HermitianMat.inv_reindex
    · convert rfl;
      apply HermitianMat.ext;
      convert! Matrix.nonsing_inv_nonsing_inv _ _;
      exact isUnit_iff_ne_zero.mpr ( hσ.det_pos.ne' );
  have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ (σBC.traceLeft⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker ρAB ( σBC.traceLeft⁻¹ ) using 1;
      · exact nonSingular_of_posDef hρ;
      · have h_inv_symm : σBC.traceLeft.mat.PosDef := by
          exact PosDef_traceLeft σBC hσ;
        -- Since σBC.traceLeft is positive definite, its inverse is also positive definite, and hence non-singular.
        have h_inv_pos_def : (σBC.traceLeft⁻¹).mat.PosDef := by
          convert! h_inv_symm.inv using 1;
        exact nonSingular_of_posDef h_inv_pos_def;
    convert h_inv_symm using 1;
    have h_inv_symm : (σBC.traceLeft⁻¹)⁻¹ = σBC.traceLeft := by
      have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
        have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
          have h_inv_symm : σBC.traceLeft.mat.PosDef := by
            exact PosDef_traceLeft σBC hσ
          convert! Matrix.nonsing_inv_mul _ _;
          exact isUnit_iff_ne_zero.mpr h_inv_symm.det_pos.ne';
        exact h_inv_symm
      have h_inv_symm : (σBC.traceLeft⁻¹ : HermitianMat dC ℂ).mat⁻¹ = σBC.traceLeft.mat := by
        rw [ Matrix.inv_eq_right_inv h_inv_symm ];
      exact Eq.symm (HermitianMat.ext (id (Eq.symm h_inv_symm)));
    rw [h_inv_symm];
  have h_inv_symm : (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm ≤ ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    aesop;
  convert! HermitianMat.reindex_le_reindex_iff ( Equiv.prodAssoc dA dB dC ) _ _ |>.2 h_inv_symm using 1

open scoped InnerProductSpace RealInnerProductSpace

/-! ### Weak monotonicity and SSA proof infrastructure -/
section SSA_proof

open HermitianMat in
private lemma hermitianMat_log_inv_eq_neg
    (A : HermitianMat d₁ ℂ) [A.NonSingular] : A⁻¹.log = -A.log := by
  -- By the property of continuous functional calculus, the logarithm of the inverse of a matrix is the negative of the logarithm of the matrix.
  have h_log_inv : A⁻¹.log = A.cfc (Real.log ∘ (·⁻¹)) := by
    have h_log_inv : A⁻¹ = A.cfc (·⁻¹) := by
      exact Eq.symm HermitianMat.cfc_inv;
    rw [ h_log_inv, HermitianMat.log ];
    exact Eq.symm (HermitianMat.cfc_comp A (fun x => x⁻¹) Real.log);
  simp [ HermitianMat.log ];
  convert! congr_arg ( fun f => A.cfc f ) ( show Real.log ∘ ( fun x => x⁻¹ ) = -Real.log from funext fun x => ?_ ) using 1
  · exact Eq.symm (HermitianMat.cfc_neg A Real.log);
  · by_cases hx : x = 0 <;> simp [ hx, Real.log_inv ]

private lemma PosDef_assoc'_traceRight
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    ρ.assoc'.traceRight.M.mat.PosDef := by
  have _ := ρ.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  rw [MState.traceRight_M, MState.assoc'_M]
  exact PosDef_traceRight _ (HermitianMat.PosDef_reindex _ _ hρ)

/-- The version of `inner_marginal_logs` where the first marginal's log is replaced by the log of
an arbitrary Hermitian matrix `X`. -/
private lemma inner_marginal_logs' [Nonempty dA] [Nonempty dB] (ρ : MState (dA × dB))
    (X : HermitianMat dA ℂ) :
    ⟪(-X.log) ⊗ₖ (1 : HermitianMat dB ℂ) +
     (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    -⟪X.log, ρ.traceRight.M⟫ - Sᵥₙ ρ.traceLeft := by
  rw [inner_add_left, HermitianMat.inner_kron_one, HermitianMat.inner_one_kron,
    Sᵥₙ_eq_neg_trace_log, inner_neg_left, MState.traceRight_M, MState.traceLeft_M]
  ring

private lemma inner_marginal_logs [Nonempty dA] [Nonempty dB] (ρ : MState (dA × dB)) :
    ⟪(-ρ.traceRight.M.log) ⊗ₖ (1 : HermitianMat dB ℂ) +
     (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  rw [inner_marginal_logs' ρ ρ.traceRight.M, Sᵥₙ_eq_neg_trace_log ρ.traceRight]

private lemma inner_marginal_logs_assoc' [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (X : HermitianMat (d₁ × d₂) ℂ) :
    ⟪((-X.log) ⊗ₖ (1 : HermitianMat d₃ ℂ) +
     (1 : HermitianMat (d₁ × d₂) ℂ) ⊗ₖ ρ.traceLeft.M.traceLeft.log).reindex
      (Equiv.prodAssoc d₁ d₂ d₃), ρ.M⟫ =
    -⟪X.log, ρ.assoc'.traceRight.M⟫ - Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [HermitianMat.reindex_inner, ← MState.assoc'_M, ← MState.traceLeft_M,
    ← MState.traceLeft_assoc']
  exact inner_marginal_logs' ρ.assoc' X

private lemma wm_inner_lhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪(-ρ.assoc'.traceRight.M.traceRight.log) ⊗ₖ (1 : HermitianMat (d₂ × d₃) ℂ) +
     (1 : HermitianMat d₁ ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  rw [← MState.traceRight_M, MState.traceRight_right_assoc']
  exact inner_marginal_logs ρ

private lemma wm_inner_rhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪((-ρ.assoc'.traceRight.M.log) ⊗ₖ (1 : HermitianMat d₃ ℂ) +
     (1 : HermitianMat (d₁ × d₂) ℂ) ⊗ₖ ρ.traceLeft.M.traceLeft.log).reindex
      (Equiv.prodAssoc d₁ d₂ d₃), ρ.M⟫ =
    Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [HermitianMat.reindex_inner, ← MState.assoc'_M, ← MState.traceLeft_M,
    ← MState.traceLeft_assoc']
  exact inner_marginal_logs ρ.assoc'

/-- Weak monotonicity (form 2) for positive definite states:
    S(ρ₁₂) + S(ρ₂₃) ≥ S(ρ₁) + S(ρ₃).
    Proved by applying operator_ineq_SSA, taking log, then inner product with ρ. -/
private lemma Sᵥₙ_wm_pd [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  -- Set up marginals and their PD properties
  have h₁₂ := PosDef_assoc'_traceRight ρ hρ
  have h₂₃ : ρ.traceLeft.M.mat.PosDef := by
    rw [MState.traceLeft_M]
    exact PosDef_traceLeft ρ.M hρ
  have : ρ.assoc'.traceRight.M.NonSingular := nonSingular_of_posDef h₁₂
  have : ρ.traceLeft.M.NonSingular := nonSingular_of_posDef h₂₃
  have : ρ.assoc'.traceRight.M.traceRight.NonSingular :=
    nonSingular_of_posDef (PosDef_traceRight _ h₁₂)
  have : ρ.traceLeft.M.traceLeft.NonSingular :=
    nonSingular_of_posDef (PosDef_traceLeft _ h₂₃)
  -- Step 1: Operator inequality
  have h_op := operator_ineq_SSA ρ.assoc'.traceRight.M ρ.traceLeft.M h₁₂ h₂₃
  -- Step 2: Take log
  have h_lhs_pd : (ρ.assoc'.traceRight.M.traceRight⁻¹ ⊗ₖ ρ.traceLeft.M).mat.PosDef :=
    HermitianMat.PosDef_kronecker _ _ (PosDef_traceRight _ h₁₂).inv h₂₃
  have h_log := HermitianMat.log_mono h_lhs_pd h_op
  -- Step 3: Simplify logs
  rw [HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  rw [HermitianMat.reindex_log, HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  -- Step 4: Take inner product with ρ.M (≥ 0)
  have h_inner := HermitianMat.inner_mono ρ.nonneg h_log
  -- Step 5: Use commutativity to match wm_inner_lhs/rhs forms
  rw [HermitianMat.inner_comm, HermitianMat.inner_comm ρ.M] at h_inner
  rw [wm_inner_lhs ρ, wm_inner_rhs ρ] at h_inner
  linarith

lemma MState.approx_by_pd
    (ρ : MState d₁) :
    ∃ (ρn : ℕ → MState d₁), (∀ n, (ρn n).M.mat.PosDef) ∧
      Filter.Tendsto ρn Filter.atTop (nhds ρ) := by
  have h_ne1 := ρ.nonempty
  -- Define the sequence of PD states ρn as the mixture of ρ with the uniform state at weight εn = 1/(n+2).
  set εn : ℕ → ℝ := fun n => 1 / (n + 2)
  set ρn : ℕ → MState d₁ := fun n => Mixable.mix ⟨εn n, by
    exact ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩⟩ (MState.uniform) ρ
  refine' ⟨ ρn, _, _ ⟩;
  · intro n
    have h_pos_def : (ρn n).M = (1 - εn n) • ρ.M + εn n • (MState.uniform (d := d₁)).M := by
      simp only [ρn, MState.mix_M]
      exact add_comm _ _
    have h_pos_def : ∀ (A : Matrix d₁ d₁ ℂ), A.PosSemidef → ∀ (B : Matrix d₁ d₁ ℂ), B.PosDef → ∀ (ε : ℝ), 0 < ε ∧ ε < 1 → (1 - ε) • A + ε • B ∈ {M : Matrix d₁ d₁ ℂ | M.PosDef} := by
      intro A hA B hB ε hε
      simp only [ Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.posDef_iff_dotProduct_mulVec ] at *
      constructor <;> simp_all
      · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
      · intro x hx_ne_zero
        have h_pos : 0 < (1 - ε) * (star x ⬝ᵥ A *ᵥ x) + ε * (star x ⬝ᵥ B *ᵥ x) := by
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| mod_cast hε.2.le ) <| mod_cast hA.2 x ) <| mul_pos ( mod_cast hε.1 ) <| mod_cast hB.2 hx_ne_zero;
        convert h_pos using 1 ; simp [ Matrix.add_mulVec ] ; ring_nf!
        simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, sub_mul, mul_sub ] ; ring!;
    convert! h_pos_def _ _ _ _ _ ⟨ _, _ ⟩ <;> norm_num [ * ];
    congr! 1
    exact ρ.psd
    · exact uniform_posDef;
    · exact one_div_pos.mpr ( by linarith );
    · exact div_lt_one ( by positivity ) |>.2 ( by linarith )
  · -- Show that the sequence ρn converges to ρ.
    have h_conv : Filter.Tendsto (fun n => εn n • (MState.uniform : MState d₁).M + (1 - εn n) • ρ.M) Filter.atTop (nhds ρ.M) := by
      exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.smul ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( Filter.Tendsto.smul ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ) ( by simp );
    rw [MState.toMat_IsEmbedding.toIsInducing.tendsto_nhds_iff]
    have h_comp : (DensityOp.M ∘ ρn)
        = fun n => εn n • (MState.uniform : MState d₁).M + (1 - εn n) • ρ.M := by
      funext n
      simp [ρn, MState.mix_M]
    rw [h_comp]
    exact h_conv

@[fun_prop]
lemma MState.traceLeft_continuous :
    Continuous (MState.traceLeft : MState (d₁ × d₂) → MState d₂) := by
  -- Since the matrix traceLeft is continuous, the function that maps a state to its partial trace is also continuous.
  have h_traceLeft_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂) ℂ => ρ.traceLeft) := by
    have h_cont : Continuous (fun ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ => ρ.traceLeft) := by
      exact continuous_pi fun _ => continuous_pi fun _ => continuous_finsetSum _ fun _ _ => continuous_apply _ |> Continuous.comp <| continuous_apply _ |> Continuous.comp <| continuous_id';
    convert h_cont.comp ( show Continuous fun ρ : HermitianMat ( d₁ × d₂ ) ℂ => ρ.1 from ?_ ) using 1;
    · constructor <;> intro h <;> rw [ continuous_induced_rng ] at * <;> aesop;
    · fun_prop;
  exact continuous_induced_rng.mpr ( by continuity )

@[fun_prop]
lemma MState.traceRight_continuous :
    Continuous (MState.traceRight : MState (d₁ × d₂) → MState d₁) := by
  rw [ continuous_iff_continuousAt ];
  intro ρ
  simp [ContinuousAt] at *;
  rw [ tendsto_nhds ] at *;
  intro s hs hρs;
  rcases hs with ⟨ t, ht, rfl ⟩;
  -- The traceRight map is continuous, so the preimage of an open set under traceRight is open.
  have h_traceRight_cont : Continuous (HermitianMat.traceRight : HermitianMat (d₁ × d₂) ℂ → HermitianMat d₁ ℂ) := by
    -- The traceRight map is a linear map, hence continuous.
    have h_traceRight_linear : ∃ (f : HermitianMat (d₁ × d₂) ℂ →ₗ[ℝ] HermitianMat d₁ ℂ), ∀ A, f A = A.traceRight := by
      refine' ⟨ _, _ ⟩;
      refine' { .. };
      exact fun A => A.traceRight;
      all_goals simp [ HermitianMat.traceRight ];
      · exact fun x y => rfl;
      · aesop
    obtain ⟨ f, hf ⟩ := h_traceRight_linear;
    convert f.continuous_of_finiteDimensional;
    exact funext fun A => hf A ▸ rfl;
  have := h_traceRight_cont.isOpen_preimage t ht;
  refine Filter.mem_of_superset (this.preimage continuous_induced_dom |> IsOpen.mem_nhds <| ?_)
    fun x hx => ?_
  · simpa [MState.traceRight_M] using hρs
  · simpa [MState.traceRight_M] using hx

@[fun_prop]
lemma MState.assoc'_continuous :
    Continuous (MState.assoc' : MState (d₁ × d₂ × d₃) → MState ((d₁ × d₂) × d₃)) := by
  -- The reindex function is continuous because it is a composition of continuous functions (permutations).
  have h_reindex_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂ × d₃) ℂ => ρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm) := by
    apply continuous_induced_rng.mpr;
    fun_prop (disch := norm_num);
  rw [continuous_induced_rng]
  have h : (DensityOp.M ∘ (MState.assoc' : MState (d₁ × d₂ × d₃) → MState ((d₁ × d₂) × d₃)))
      = (fun ρ : HermitianMat (d₁ × d₂ × d₃) ℂ => ρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm)
        ∘ DensityOp.M := funext fun ρ ↦ MState.assoc'_M ρ
  rw [h]
  exact h_reindex_cont.comp Continuous_HermitianMat

/-- Weak monotonicity, version with partial traces. -/
lemma Sᵥₙ_wm (ρ : MState (d₁ × d₂ × d₃)) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  have h_ne123 := ρ.nonempty
  obtain ⟨ ρn, hρn_pos, hρn ⟩ := MState.approx_by_pd ρ;
  -- Apply the inequality for each ρn and then take the limit.
  have h_lim : Filter.Tendsto (fun n => Sᵥₙ (ρn n).traceRight + Sᵥₙ (ρn n).traceLeft.traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft)) ∧ Filter.Tendsto (fun n => Sᵥₙ (ρn n).assoc'.traceRight + Sᵥₙ (ρn n).traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft)) := by
    constructor <;> refine' Filter.Tendsto.add _ _;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp hρn );
    · exact Sᵥₙ_continuous.comp ( MState.traceLeft_continuous.comp ( MState.traceLeft_continuous ) ) |> fun h => h.continuousAt.tendsto.comp hρn;
    · convert! Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp ( MState.assoc'_continuous.continuousAt.tendsto.comp hρn ) ) using 1;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceLeft_continuous.continuousAt.tendsto.comp hρn );
  have ⟨_, hn23⟩ := nonempty_prod.mp h_ne123
  have ⟨_, _⟩ := nonempty_prod.mp hn23
  exact le_of_tendsto_of_tendsto' h_lim.1 h_lim.2 fun n => Sᵥₙ_wm_pd _ ( hρn_pos n )

/-- Permutation to relabel (A×B×C)×R as A×(B×C×R). -/
private def perm_A_BCR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ dA × (dB × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (a, (b,c,r))
  invFun x := let (a, (b,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The BCR state: trace out A from the purification of ρ_ABC. -/
private def ρBCR (ρ : MState (dA × dB × dC)) : MState (dB × dC × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel (perm_A_BCR' dA dB dC).symm).traceLeft

private lemma S_BC_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).assoc'.traceRight = Sᵥₙ ρ.traceLeft := by
  -- By definition of ρBCR, we know that its BC-marginal is equal to the BC-marginal of ρ.
  have h_marginal : (ρBCR ρ).assoc'.traceRight = ρ.traceLeft := by
    unfold ρBCR MState.traceLeft MState.traceRight MState.assoc';
    simp [ MState.assoc, MState.SWAP, MState.relabel, MState.pure, perm_A_BCR' ];
    unfold reindex HermitianMat.traceLeft HermitianMat.traceRight; ext
    simp
    simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix ];
    have := ρ.purify_spec;
    replace this := congr_arg ( fun x => x.M.val ) this ; simp_all [ MState.traceRight, MState.pure ];
    simp [ ← this, Matrix.traceRight, Matrix.vecMulVec ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  rw [h_marginal]

/-- Equivalence to relabel the purification as (dA × dB) × (dC × R). -/
private def perm_AB_CR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/- The CR-marginal of ρBCR equals the traceLeft of the AB|CR-relabeled purification. -/
private lemma BCR_traceLeft_eq_purify_traceLeft (ρ : MState (dA × dB × dC)) :
    (ρBCR ρ).traceLeft =
    ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceLeft := by
  ext ⟨c, r⟩ ⟨c', r'⟩
  simp [ρBCR, MState.traceLeft_M, MState.relabel_M, HermitianMat.traceLeft_apply,
    HermitianMat.reindex_apply, perm_A_BCR', perm_AB_CR', Fintype.sum_prod_type]
  exact Finset.sum_comm

/- The traceRight of the AB|CR-relabeled purification has same entropy as ρ.assoc'.traceRight. -/
private lemma purify_AB_traceRight_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight =
    Sᵥₙ ρ.assoc'.traceRight := by
  have h_purify : ∀ (i j : dA × dB × dC),
      ρ.M i j = ∑ r : dA × dB × dC, ρ.purify (i, r) * (starRingEnd ℂ) (ρ.purify (j, r)) := by
    intro i j
    conv_lhs => rw [← ρ.purify_spec]
    simp only [MState.traceRight_M, HermitianMat.traceRight_apply, MState.pure_M_apply]
  have h_traceRight : ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight
      = ρ.assoc'.traceRight := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp [MState.traceRight_M, MState.relabel_M, MState.assoc'_M, HermitianMat.traceRight_apply,
      HermitianMat.reindex_apply, perm_AB_CR', Fintype.sum_prod_type, Matrix.vecMulVec_apply,
      Bra.eq_conj]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [h_purify]
    simp [Fintype.sum_prod_type]
  rw [h_traceRight]

/-- The CR-marginal of ρBCR has the same entropy as the AB-marginal of ρ. -/
private lemma S_CR_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft = Sᵥₙ ρ.assoc'.traceRight := by
  rw [BCR_traceLeft_eq_purify_traceLeft]
  rw [Sᵥₙ_pure_complement ρ.purify (perm_AB_CR' dA dB dC).symm]
  exact purify_AB_traceRight_eq ρ

private lemma S_B_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  unfold ρBCR;
  unfold MState.traceLeft MState.traceRight MState.relabel MState.pure;
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, perm_A_BCR' ];
  unfold Matrix.traceLeft Matrix.traceRight; simp [Matrix.vecMulVec ] ;
  -- By definition of purification, we know that ρ.purify is a purification of ρ.m.
  have h_purify : ∀ (i j : dA × dB × dC), ρ.m i j = ∑ r : dA × dB × dC, ρ.purify (i, r) * (starRingEnd ℂ) (ρ.purify (j, r)) := by
    intro i j
    have := ρ.purify_spec;
    replace this := congr_arg ( fun m => m.M i j ) this
    simp_all [MState.traceRight]
    exact this.symm
  simp only [Finset.sum_sigma', h_purify];
  congr! 3;
  ext i₂ j₂
  simp
  ring_nf
  refine' Finset.sum_bij ( fun x _ => ⟨ x.fst.1, x.snd, x.fst.2 ⟩ ) _ _ _ _ <;> simp
  · grind
  · grind

private lemma S_R_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft.traceLeft = Sᵥₙ ρ := by
  have h_trace : (ρBCR ρ).traceLeft.traceLeft = (MState.pure ρ.purify).traceLeft := by
    unfold ρBCR MState.traceLeft;
    ext i j;
    simp [ HermitianMat.traceLeft];
    simp [ perm_A_BCR', Matrix.traceLeft ];
    simp [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ( x.snd.snd, x.snd.fst, x.fst ) ) _ _ _ _ <;> simp
    grind;
  rw [h_trace, Sᵥₙ_of_partial_eq, ρ.purify_spec]

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  have _ := ρ₁₂₃.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  -- Apply weak monotonicity to ρBCR, then substitute purification identities
  have h_wm := Sᵥₙ_wm (ρBCR ρ₁₂₃)
  rw [S_BC_of_BCR_eq, S_CR_of_BCR_eq, S_B_of_BCR_eq, S_R_of_BCR_eq] at h_wm
  linarith

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  -- Pad the bipartite state with a trivial middle factor and apply strong subadditivity.
  let e : d₁ × Unit × d₂ ≃ d₁ × d₂ :=
    ⟨fun x ↦ (x.1, x.2.2), fun x ↦ (x.1, ⟨(), x.2⟩), fun x ↦ by simp, fun x ↦ by simp⟩
  have h := Sᵥₙ_strong_subadditivity (ρ.relabel e)
  dsimp only at h
  have h₃ : (ρ.relabel e).assoc'.traceRight = ρ.traceRight.relabel (Equiv.prodPUnit d₁) := by
    ext ⟨a, u⟩ ⟨a', u'⟩
    simp [MState.traceRight_M, MState.assoc'_M, MState.relabel_M, HermitianMat.traceRight_apply,
      HermitianMat.reindex_apply, e]
  have h₄ : (ρ.relabel e).traceLeft = ρ.traceLeft.relabel (Equiv.punitProd d₂) := by
    ext ⟨u, c⟩ ⟨u', c'⟩
    simp [MState.traceLeft_M, MState.relabel_M, HermitianMat.traceLeft_apply,
      HermitianMat.reindex_apply, e]
  rw [Sᵥₙ_relabel, Sᵥₙ_unit_zero (ρ.relabel e).traceLeft.traceRight, h₃, h₄,
    Sᵥₙ_relabel, Sᵥₙ_relabel] at h
  linarith

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    MState.relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity (ρ : MState (dA × dB × dC)) :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  show (0 : ℝ) ≤ qConditionalEnt ρ.assoc'.traceRight +
    qConditionalEnt ρ.SWAP.assoc.traceLeft.SWAP
  have hwm := Sᵥₙ_wm ρ.SWAP.assoc.SWAP.assoc
  have h1 : ρ.SWAP.assoc.SWAP.assoc.traceRight = ρ.traceLeft.traceLeft := by
    ext i j
    simp [HermitianMat.traceLeft_apply]
  have h2 : ρ.SWAP.assoc.SWAP.assoc.traceLeft.traceLeft = ρ.traceLeft.traceRight := by
    ext i j
    simp [HermitianMat.traceLeft_apply, HermitianMat.traceRight_apply]
  have h3 : ρ.SWAP.assoc.SWAP.assoc.traceLeft = ρ.assoc'.traceRight := by
    ext i j
    simp [HermitianMat.traceLeft_apply, HermitianMat.traceRight_apply,
      HermitianMat.reindex_apply]
  have h4 : ρ.SWAP.assoc.SWAP.assoc.assoc'.traceRight = ρ.SWAP.assoc.traceLeft := by
    ext i j
    simp [HermitianMat.traceLeft_apply, HermitianMat.reindex_apply]
  have h6 : ρ.SWAP.assoc.traceLeft.SWAP.traceLeft = ρ.traceLeft.traceLeft := by
    ext i j
    simp [HermitianMat.traceLeft_apply]
  rw [h1, h2, h3, h4] at hwm
  simp only [qConditionalEnt, MState.traceRight_left_assoc', h6, Sᵥₙ_of_SWAP_eq]
  linarith

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  have := Sᵥₙ_le_log_d ρ.traceRight
  have := Sᵥₙ_le_log_d ρ.assoc'.traceRight.traceRight
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  have := Sᵥₙ_le_log_d ρ.traceLeft.traceLeft
  grind [qcmi, qConditionalEnt, MState.traceRight_left_assoc']

/-! ### The operator form of data processing for the partial trace

Strong subadditivity, in the operator form `operator_ineq_SSA`, compares `ρABC` with the
marginals of `ρ`. Replacing the marginal `ρAB` there by an arbitrary positive definite `τ` and
pairing against `ρ` gives an inequality that only involves `τ` through `log τ`; taking `ρ` to be
the purification of a state on `dA × dB` collapses the three-party statement into a two-party one.
The result, `inner_log_traceRight_le`, is what makes the relative entropy monotone under the
partial trace. -/

/-- Strong subadditivity, paired against a positive definite `τ` on the first two factors, in
the special case that the underlying state is positive definite. -/
theorem inner_log_le_pd [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef)
    {τ : HermitianMat (d₁ × d₂) ℂ} (hτ : τ.mat.PosDef) :
    -⟪τ.traceRight.log, ρ.traceRight.M⟫ - Sᵥₙ ρ.traceLeft ≤
    -⟪τ.log, ρ.assoc'.traceRight.M⟫ - Sᵥₙ ρ.traceLeft.traceLeft := by
  have h₂₃ : ρ.traceLeft.M.mat.PosDef := by
    rw [MState.traceLeft_M]
    exact PosDef_traceLeft ρ.M hρ
  have : τ.NonSingular := nonSingular_of_posDef hτ
  have : ρ.traceLeft.M.NonSingular := nonSingular_of_posDef h₂₃
  have : τ.traceRight.NonSingular := nonSingular_of_posDef (PosDef_traceRight _ hτ)
  have : ρ.traceLeft.M.traceLeft.NonSingular := nonSingular_of_posDef (PosDef_traceLeft _ h₂₃)
  have h_op := operator_ineq_SSA τ ρ.traceLeft.M hτ h₂₃
  have h_lhs_pd : (τ.traceRight⁻¹ ⊗ₖ ρ.traceLeft.M).mat.PosDef :=
    HermitianMat.PosDef_kronecker _ _ (PosDef_traceRight _ hτ).inv h₂₃
  have h_log := HermitianMat.log_mono h_lhs_pd h_op
  rw [HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  rw [HermitianMat.reindex_log, HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  have h_inner := HermitianMat.inner_mono ρ.nonneg h_log
  rw [HermitianMat.inner_comm, HermitianMat.inner_comm ρ.M] at h_inner
  rw [inner_marginal_logs' ρ τ.traceRight, inner_marginal_logs_assoc' ρ τ] at h_inner
  linarith

/-- Strong subadditivity, paired against a positive definite `τ` on the first two factors. -/
theorem inner_log_le (ρ : MState (d₁ × d₂ × d₃))
    {τ : HermitianMat (d₁ × d₂) ℂ} (hτ : τ.mat.PosDef) :
    -⟪τ.traceRight.log, ρ.traceRight.M⟫ - Sᵥₙ ρ.traceLeft ≤
    -⟪τ.log, ρ.assoc'.traceRight.M⟫ - Sᵥₙ ρ.traceLeft.traceLeft := by
  have h_ne123 := ρ.nonempty
  have ⟨_, hn23⟩ := nonempty_prod.mp h_ne123
  have ⟨_, _⟩ := nonempty_prod.mp hn23
  obtain ⟨ρn, hρn_pos, hρn⟩ := MState.approx_by_pd ρ
  have hL : Continuous fun σ : MState (d₁ × d₂ × d₃) ↦
      -⟪τ.traceRight.log, σ.traceRight.M⟫ - Sᵥₙ σ.traceLeft := by
    fun_prop
  have hR : Continuous fun σ : MState (d₁ × d₂ × d₃) ↦
      -⟪τ.log, σ.assoc'.traceRight.M⟫ - Sᵥₙ σ.traceLeft.traceLeft := by
    fun_prop
  exact le_of_tendsto_of_tendsto' (hL.continuousAt.tendsto.comp hρn)
    (hR.continuousAt.tendsto.comp hρn) fun n => inner_log_le_pd _ (hρn_pos n) hτ

/-- A monotonicity inequality for the partial trace: for any positive definite `τ`, the
quantity `⟪ρ, log τ⟫ + Sᵥₙ ρ` does not decrease under taking the marginal. This is the
operator form of the data processing inequality for the partial trace. -/
theorem inner_log_traceRight_le (ρ : MState (dA × dB)) {τ : HermitianMat (dA × dB) ℂ}
    (hτ : τ.mat.PosDef) :
    ⟪ρ.M, τ.log⟫ + Sᵥₙ ρ ≤ ⟪ρ.traceRight.M, τ.traceRight.log⟫ + Sᵥₙ ρ.traceRight := by
  obtain ⟨_, _⟩ := nonempty_prod.mp ρ.nonempty
  set Ψ : MState ((dA × dB) × (dA × dB)) := MState.pure ρ.purify with hΨ
  set ω : MState (dA × dB × (dA × dB)) :=
    Ψ.relabel (Equiv.prodAssoc dA dB (dA × dB)).symm with hω
  have hassoc : ω.assoc' = Ψ := by
    ext i j
    simp [hω, MState.assoc'_M, MState.relabel_M]
  have h := inner_log_le ω hτ
  rw [hassoc, hΨ, ρ.purify_spec] at h
  have h1 : ω.traceRight = ρ.traceRight := by
    rw [← MState.traceRight_right_assoc' ω, hassoc, hΨ, ρ.purify_spec]
  have h2 : Sᵥₙ ω.traceLeft = Sᵥₙ ρ.traceRight := by
    rw [hω, hΨ, Sᵥₙ_pure_complement]
    rw [← hΨ, ← hω, h1]
  have h3 : Sᵥₙ ω.traceLeft.traceLeft = Sᵥₙ ρ := by
    rw [← MState.traceLeft_assoc', hassoc, hΨ, Sᵥₙ_of_partial_eq, ρ.purify_spec]
  rw [h1, h2, h3] at h
  rw [HermitianMat.inner_comm ρ.M, HermitianMat.inner_comm ρ.traceRight.M]
  linarith

section basis_free

/-! ### Basis-free forms

The results above are stated for a system whose index type is a product. These are their
counterparts for a state on an honest tensor product of Hilbert spaces. Each is obtained from the
index-level statement by picking an arbitrary preferred basis on each factor (`StdBasis.some`) and
transporting; the index-level quantity is insensitive to that choice, so nothing is lost. -/

open scoped TensorProduct

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

namespace DensityOp

/-- Strong subadditivity on a tripartite system. -/
theorem Sᵥₙ_strong_subadditivity (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    Sᵥₙ ρ + Sᵥₙ ρ.traceLeft.traceRight ≤
      Sᵥₙ ((ρ.congr (TensorProduct.assocIsometry ℂ E F G).symm).traceRight) + Sᵥₙ ρ.traceLeft := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [← MState.assoc'_transport, MState.traceRight_transport, MState.traceLeft_transport,
    MState.traceRight_transport, Sᵥₙ_transport, Sᵥₙ_transport, Sᵥₙ_transport, Sᵥₙ_transport]
  have := _root_.Sᵥₙ_strong_subadditivity μ
  dsimp only at this
  linarith

/-- "Ordinary" subadditivity of von Neumann entropy. -/
theorem Sᵥₙ_subadditivity (ρ : DensityOp (E ⊗[ℂ] F)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [MState.traceRight_transport, MState.traceLeft_transport, Sᵥₙ_transport, Sᵥₙ_transport,
    Sᵥₙ_transport]
  exact _root_.Sᵥₙ_subadditivity μ

/-- Araki-Lieb triangle inequality on von Neumann entropy. -/
theorem Sᵥₙ_triangle_subaddivity (ρ : DensityOp (E ⊗[ℂ] F)) :
    |Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft| ≤ Sᵥₙ ρ := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [MState.traceRight_transport, MState.traceLeft_transport, Sᵥₙ_transport, Sᵥₙ_transport,
    Sᵥₙ_transport]
  exact _root_.Sᵥₙ_triangle_subaddivity μ

/-- Weak monotonicity of quantum conditional entropy: `S(E|F) + S(E|G) ≥ 0`. -/
theorem Sᵥₙ_weak_monotonicity (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    0 ≤ ((ρ.congr (TensorProduct.assocIsometry ℂ E F G).symm).traceRight).qConditionalEnt +
      ((((ρ.congr (TensorProduct.commIsometry ℂ E (F ⊗[ℂ] G))).congr
        (TensorProduct.assocIsometry ℂ F G E)).traceLeft).congr
        (TensorProduct.commIsometry ℂ G E)).qConditionalEnt := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [← MState.assoc'_transport, ← MState.SWAP_transport, ← MState.assoc_transport,
    MState.traceLeft_transport, ← MState.SWAP_transport, MState.traceRight_transport,
    qConditionalEnt_transport, qConditionalEnt_transport]
  have := _root_.Sᵥₙ_weak_monotonicity μ
  dsimp only at this
  linarith

/-- Strong subadditivity, stated in terms of conditional entropies:
`S(E|FG) ≤ S(E|F)`. -/
theorem qConditionalEnt_strong_subadditivity (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    ρ.qConditionalEnt ≤
      ((ρ.congr (TensorProduct.assocIsometry ℂ E F G).symm).traceRight).qConditionalEnt := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [← MState.assoc'_transport, MState.traceRight_transport, qConditionalEnt_transport,
    qConditionalEnt_transport]
  exact _root_.qConditionalEnt_strong_subadditivity μ

/-- Strong subadditivity, stated in terms of quantum mutual information:
`I(E:FG) ≥ I(E:F)`. -/
theorem qMutualInfo_strong_subadditivity (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    ((ρ.congr (TensorProduct.assocIsometry ℂ E F G).symm).traceRight).qMutualInfo ≤
      ρ.qMutualInfo := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [← MState.assoc'_transport, MState.traceRight_transport, qMutualInfo_transport,
    qMutualInfo_transport]
  exact _root_.qMutualInfo_strong_subadditivity μ

/-- The quantum conditional mutual information is nonnegative. -/
theorem qcmi_nonneg (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) : 0 ≤ ρ.qcmi := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [qcmi_transport]
  exact _root_.qcmi_nonneg μ

/-- The quantum conditional mutual information `I(E;G|F)` is at most `2 log (dim E)`. -/
theorem qcmi_le_2_log_dim (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    ρ.qcmi ≤ 2 * Real.log (Module.finrank ℂ E) := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [qcmi_transport]
  simpa using _root_.qcmi_le_2_log_dim μ

/-- The quantum conditional mutual information `I(E;G|F)` is at most `2 log (dim G)`. -/
theorem qcmi_le_2_log_dim' (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) :
    ρ.qcmi ≤ 2 * Real.log (Module.finrank ℂ G) := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  let := StdBasis.some ℂ G
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  rw [qcmi_transport]
  simpa using _root_.qcmi_le_2_log_dim' μ

end DensityOp

end basis_free

/- The chain rule for quantum conditional mutual information:
`I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.

It should be something like this, but it's hard to track the indices correctly:
theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
    let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
    let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
      ((CPTPOp.id ⊗ₖ CPTPOp.assoc').compose (CPTPOp.assoc.compose (CPTPOp.SWAP ⊗ₖ CPTPOp.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  admit
-/
