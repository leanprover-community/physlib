/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.ClassicalInfo.Entropy

/-!
Quantum notions of information and entropy.

We start with quantities of _entropy_, namely the von Neumann entropy and its derived quantities:
 * Quantum conditional entropy, `qConditionalEnt`
 * Quantum mutual information, `qMutualInfo`
 * Coherent information, `coherentInfo`
 * Quantum conditional mutual information, `qcmi`.
and then prove facts about them.
-/

@[expose] public section

/- # TODO / Goals:

--QConditionalEnt chain rule

--Quantum discord

--Entanglement:
-- * Entanglement entropy
-- * Entanglement of formation
-- * Relative entropy of entanglement
-- * Squashed entanglement
-- * Negativity (+ facts here: https://www.quantiki.org/wiki/strong-sub-additivity)
-- * Distillable entanglement (One way, Two way, --> Coherent Information)
-- * Entanglement cost (!= EoF, prove; asymptotically == EoF.)
-- Bound entanglement (Prop)

-- https://arxiv.org/pdf/quant-ph/0406162

--https://en.wikipedia.org/wiki/Von_Neumann_entropy#Properties
--  in particular https://www.quantiki.org/wiki/strong-sub-additivity

--https://en.wikipedia.org/wiki/Quantum_relative_entropy#Relation_to_other_quantum_information_quantities

--QMutualInfo is symmetric

--TODO:
-- * Classical conditional entropy is nonnegative
-- * Not true of qConditionalEnt
-- * These measures track their classical values on `MState.ofClassical` states
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}

open scoped InnerProductSpace RealInnerProductSpace

section entropy

section operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- Von Neumann entropy of a mixed state: the trace of `-ρ log ρ`, where the operator function is
given by the continuous functional calculus.

This makes no reference to a basis. `Sᵥₙ_eq_Hₛ_spectrum` identifies it with the Shannon entropy of
the spectrum, and `Sᵥₙ_eq_trace_cfc_negMulLog` is the matrix analogue. -/
def Sᵥₙ (ρ : DensityOp E) : ℝ :=
  (ρ.op.cfc Real.negMulLog).trace

/-- **Matrix analogue of `Sᵥₙ`**: the von Neumann entropy is the trace of `x ↦ -x * log x` applied
to the density matrix through the continuous functional calculus. -/
theorem Sᵥₙ_eq_trace_cfc_negMulLog (ρ : DensityOp E) :
    Sᵥₙ ρ = ((ρ.M : HermitianMat ι ℂ).cfc Real.negMulLog).trace := by
  simp only [Sᵥₙ, ← HermitianOp.trace_toMat (ι := ι), HermitianOp.toMat_cfc]
  rfl

/-- **Matrix analogue of `Sᵥₙ`**, phrased with the continuous functional calculus on the raw
density matrix rather than on a `HermitianMat`. -/
theorem Sᵥₙ_eq_re_trace_matrix_cfc (ρ : DensityOp E) :
    Sᵥₙ ρ = (cfc Real.negMulLog (ρ.m : Matrix ι ι ℂ)).trace.re := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog (ι := ι), HermitianMat.trace, HermitianMat.mat_cfc,
    IsMaximalSelfAdjoint.RCLike_selfadjMap, RCLike.re_to_complex, DensityOp.mat_M]

/-- The von Neumann entropy is unchanged by reading a state on a different space with the same
preferred index type. -/
@[simp]
theorem Sᵥₙ_transport {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [StdBasis ℂ F ι]
    (ρ : DensityOp E) : Sᵥₙ (ρ.transport F) = Sᵥₙ ρ := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog (ι := ι), Sᵥₙ_eq_trace_cfc_negMulLog (ι := ι),
    DensityOp.M_transport]

end operator

/-- The von Neumann entropy is the Shannon entropy of the spectrum. -/
theorem Sᵥₙ_eq_Hₛ_spectrum (ρ : MState d) : Sᵥₙ ρ = Hₛ ρ.spectrum := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog (ι := d), ← HermitianMat.sum_eigenvalues_eq_trace, Hₛ]
  obtain ⟨e, he⟩ := ρ.M.cfc_eigenvalues (f := Real.negMulLog)
  refine Finset.sum_equiv e (by simp) fun i _ ↦ ?_
  rw [congrFun he i]
  simp [H₁, MState.spectrum, ProbDistribution.mk', ProbDistribution.prob]

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def qConditionalEnt (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft

/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- The Coherent Information of a state ρ passing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def coherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := Λ.prod (CPTPOp.id (dIn := d₁)) ρPure
  (- qConditionalEnt ρImg)

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ

section bipartite

/-! ### Basis-free forms of the composite-system entropies

The definitions above are stated for a system whose index type is a product; these are their
counterparts for a state on an honest tensor product, together with the "matrix analogue"
theorems identifying the two through `DensityOp.transport`. -/

open scoped TensorProduct

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

namespace DensityOp

section Defs

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- The quantum conditional entropy `S(E|F) = S(EF) - S(F)` of a state on `E ⊗ F`. -/
def qConditionalEnt (ρ : DensityOp (E ⊗[ℂ] F)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft

/-- The quantum mutual information `I(E:F) = S(E) + S(F) - S(EF)` of a state on `E ⊗ F`. -/
def qMutualInfo (ρ : DensityOp (E ⊗[ℂ] F)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- The quantum conditional mutual information `I(E;G|F) = S(E|F) - S(E|FG)` of a state on
`E ⊗ (F ⊗ G)`. -/
def qcmi (ρ : DensityOp (E ⊗[ℂ] (F ⊗[ℂ] G))) : ℝ :=
  ((ρ.congr (TensorProduct.assocIsometry ℂ E F G).symm).traceRight).qConditionalEnt -
    ρ.qConditionalEnt

end Defs

end DensityOp

section Analogue

variable [StdBasis ℂ E dA] [StdBasis ℂ F dB] [StdBasis ℂ G dC]

/-- **Matrix analogue of `DensityOp.qConditionalEnt`.** -/
@[simp]
theorem qConditionalEnt_transport (ρ : MState (dA × dB)) :
    (ρ.transport (E ⊗[ℂ] F)).qConditionalEnt = qConditionalEnt ρ := by
  rw [DensityOp.qConditionalEnt, qConditionalEnt, MState.traceLeft_transport, Sᵥₙ_transport,
    Sᵥₙ_transport]

/-- **Matrix analogue of `DensityOp.qMutualInfo`.** -/
@[simp]
theorem qMutualInfo_transport (ρ : MState (dA × dB)) :
    (ρ.transport (E ⊗[ℂ] F)).qMutualInfo = qMutualInfo ρ := by
  rw [DensityOp.qMutualInfo, qMutualInfo, MState.traceLeft_transport, MState.traceRight_transport,
    Sᵥₙ_transport, Sᵥₙ_transport, Sᵥₙ_transport]

/-- **Matrix analogue of `DensityOp.qcmi`.** -/
@[simp]
theorem qcmi_transport (ρ : MState (dA × dB × dC)) :
    (ρ.transport (E ⊗[ℂ] (F ⊗[ℂ] G))).qcmi = qcmi ρ := by
  rw [DensityOp.qcmi, qcmi, ← MState.assoc'_transport, MState.traceRight_transport,
    qConditionalEnt_transport, qConditionalEnt_transport]

end Analogue

end bipartite

/-- von Neumman entropy is nonnegative. -/
theorem Sᵥₙ_nonneg (ρ : MState d) : 0 ≤ Sᵥₙ ρ :=
  (Hₛ_nonneg _).trans (Sᵥₙ_eq_Hₛ_spectrum ρ).ge

/-- von Neumman entropy is at most log d. -/
theorem Sᵥₙ_le_log_d (ρ : MState d) : Sᵥₙ ρ ≤ Real.log (Finset.card Finset.univ (α := d)):=
  (Sᵥₙ_eq_Hₛ_spectrum ρ).trans_le (Hₛ_le_log_d _)

/-- von Neumman entropy of pure states is zero. -/
@[simp]
theorem Sᵥₙ_of_pure_zero (ψ : Ket d) : Sᵥₙ (MState.pure ψ) = 0 := by
  obtain ⟨i, hi⟩ := MState.spectrum_pure_eq_constant ψ
  rw [Sᵥₙ_eq_Hₛ_spectrum, hi, Hₛ_constant_eq_zero]

set_option backward.isDefEq.respectTransparency false in
theorem Sᵥₙ_eq_neg_trace_log (ρ : MState d) : Sᵥₙ ρ = -⟪ρ.M.log, ρ.M⟫ := by
  open HermitianMat in
  rw [log, inner_eq_re_trace]
  nth_rw 2 [← cfc_id ρ.M]
  rw [← mat_cfc_mul]
  simp only [Sᵥₙ_eq_Hₛ_spectrum, Hₛ, H₁, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rw [← trace_eq_re_trace, ← sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := ρ.M.cfc_eigenvalues (Real.log * id)
  apply Finset.sum_equiv e.symm (by simp)
  simp [MState.spectrum, ProbDistribution.mk', he, mul_comm]

@[simp]
theorem Sᵥₙ_unit_zero [Unique d] (ρ : MState d) : Sᵥₙ ρ = 0 := by
  refine le_antisymm ?_ (Sᵥₙ_nonneg ρ)
  simpa using Sᵥₙ_le_log_d ρ

/-- Von Neumann entropy is invariant under relabeling of the basis. -/
@[simp]
theorem Sᵥₙ_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Sᵥₙ (ρ.relabel e) = Sᵥₙ ρ := by
  simp [Sᵥₙ_eq_neg_trace_log]

/-- Von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
@[simp]
theorem Sᵥₙ_of_SWAP_eq (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.SWAP = Sᵥₙ ρ := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Sᵥₙ_eq_Hₛ_spectrum]
  apply Hₛ_eq_of_multiset_map_eq
  exact ρ.multiset_spectrum_relabel_eq (Equiv.prodComm d₁ d₂).symm

/-- Von Neumann entropy is unchanged under assoc. -/
@[simp]
theorem Sᵥₙ_of_assoc_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Sᵥₙ_eq_Hₛ_spectrum]
  apply Hₛ_eq_of_multiset_map_eq
  apply ρ.multiset_spectrum_relabel_eq

/-- Von Neumann entropy is unchanged under assoc'. -/
@[simp]
theorem Sᵥₙ_of_assoc'_eq (ρ : MState (d₁ × (d₂ × d₃))) : Sᵥₙ ρ.assoc' = Sᵥₙ ρ := by
  rw [← Sᵥₙ_of_assoc_eq, ρ.assoc_assoc']

@[fun_prop]
theorem selfAdjointMap_Continuous {𝕜 : Type*} [RCLike 𝕜] :
    Continuous (IsMaximalSelfAdjoint.selfadjMap : 𝕜 →+ ℝ) := by
  rw [IsMaximalSelfAdjoint.RCLike_selfadjMap]
  fun_prop

@[fun_prop]
theorem Sᵥₙ_continuous : Continuous (Sᵥₙ (E := EuclideanSpace ℂ d)) := by
  rw [funext (Sᵥₙ_eq_trace_cfc_negMulLog (ι := d))]
  fun_prop

section partial_trace_pure
--TODO Cleanup

/--
Convert a vector on a product space to a matrix.
-/
def vecToMat {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] (v : d₁ × d₂ → ℂ) : Matrix d₁ d₂ ℂ :=
  Matrix.of (fun i j => v (i, j))

/--
The right partial trace of a pure state is the product of the matrix representation
and its conjugate transpose.
-/
private lemma traceRight_eq_mul_conjTranspose (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceRight.M.val = (vecToMat ψ.vec) * (vecToMat ψ.vec).conjTranspose := by
  unfold vecToMat; aesop;

/-
The left partial trace of a pure state is the product of the transpose of the
matrix representation and its conjugate.
-/
lemma traceLeft_eq_transpose_mul_conj (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceLeft.M.val = (vecToMat ψ.vec).transpose * (vecToMat ψ.vec).map star := by
  unfold vecToMat; aesop;

/--
The left partial trace of `vecToMat` is the transpose of M^H * M.
-/
private lemma traceLeft_eq_transpose_conjTranspose_mul (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceLeft.M.val =
    ((vecToMat ψ.vec).conjTranspose * (vecToMat ψ.vec)).transpose := by
  rw [traceLeft_eq_transpose_mul_conj]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/--
Shannon entropy is determined by the multiset of non-zero probabilities.
-/
private lemma Hₛ_eq_of_nonzero_multiset_eq {α β : Type*} [Fintype α] [Fintype β]
  (d₁ : ProbDistribution α) (d₂ : ProbDistribution β)
  (h : (Finset.univ.val.map d₁.prob).filter (· ≠ 0) = (Finset.univ.val.map d₂.prob ).filter (· ≠ 0)) :
    Hₛ d₁ = Hₛ d₂ := by
  -- By reindexing the sums, we can show that the Shannon entropies are equal.
  simp [Hₛ]
  -- Since the multisets of non-zero probabilities are equal, their sums are equal.
  have h_sum_eq : ∑ x ∈ Finset.univ.filter (fun x => d₁.prob x ≠ 0), H₁ (d₁.prob x) = ∑ x ∈ Finset.univ.filter (fun x => d₂.prob x ≠ 0), H₁ (d₂.prob x) := by
    convert congr_arg ( fun m => m.map ( fun x => H₁ x ) |> Multiset.sum ) h using 1;
    · simp [ Finset.sum, Multiset.filter_map ];
    · simp [ Finset.sum, Multiset.filter_map ];
  rwa [Finset.sum_filter_of_ne, Finset.sum_filter_of_ne] at h_sum_eq
  · aesop
  · aesop

/--
If two polynomials differ by a factor of X^k, their non-zero roots are the same.
-/
private lemma nonzero_roots_eq_of_charpoly_eq_X_pow {R : Type*} [CommRing R] [IsDomain R]
  [DecidableEq R] (p q : Polynomial R) (k : ℕ) (h : p = Polynomial.X ^ k * q) :
    p.roots.filter (· ≠ 0) = q.roots.filter (· ≠ 0) := by
  by_cases hq : q = 0 <;> simp_all [ Polynomial.roots_mul, Polynomial.X_ne_zero ]

/--
The non-zero eigenvalues of AB and BA are the same.
-/
private lemma nonzero_eigenvalues_eq_of_mul_comm {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  have h_roots : (Polynomial.X ^ Fintype.card m * (Matrix.charpoly (A * B))).roots.filter (· ≠ 0) = (Polynomial.X ^ Fintype.card n * (Matrix.charpoly (B * A))).roots.filter (· ≠ 0) := by
    rw [A.charpoly_mul_comm' B]
  convert h_roots using 1
  · simp [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero]
  · simp [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero]

/--
If two states have the same non-zero eigenvalues (spectrum probabilities), they have
the same von Neumann entropy.
-/
private lemma Sᵥₙ_eq_of_nonzero_eigenvalues_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂)
    (h : (Finset.univ.val.map ρ₁.spectrum.prob).filter (· ≠ 0) =
      (Finset.univ.val.map ρ₂.spectrum.prob).filter (· ≠ 0)) :
    Sᵥₙ ρ₁ = Sᵥₙ ρ₂ := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Sᵥₙ_eq_Hₛ_spectrum]
  exact Hₛ_eq_of_nonzero_multiset_eq _ _ h

/--
Filtering non-zero elements commutes with mapping `RCLike.ofReal` for multisets.
-/
private lemma multiset_filter_map_ofReal_eq {R : Type*} [RCLike R] (M : Multiset ℝ) :
    (M.map (RCLike.ofReal : ℝ → R)).filter (· ≠ 0) = (M.filter (· ≠ 0)).map RCLike.ofReal := by
  simp [Multiset.filter_map]

/-
The non-zero roots of the characteristic polynomial are the non-zero eigenvalues mapped
to complex numbers.
-/
private lemma charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    A.charpoly.roots.filter (· ≠ 0) = ((Finset.univ.val.map hA.eigenvalues).filter (· ≠ 0)).map RCLike.ofReal := by
  convert congr_arg _ ?_;
  rw [ multiset_filter_map_ofReal_eq ];
  -- Since A is Hermitian, its characteristic polynomial is equal to the product of (X - eigenvalue) over all eigenvalues.
  have h_charpoly : A.charpoly = Multiset.prod (Multiset.map (fun i => Polynomial.X - Polynomial.C (RCLike.ofReal (hA.eigenvalues i))) (Finset.univ.val)) := by
    convert! Matrix.IsHermitian.charpoly_eq hA using 1;
  rw [ h_charpoly, Polynomial.roots_multiset_prod ];
  · simp [ Multiset.bind_map ];
  · simp [ Polynomial.X_sub_C_ne_zero ]

/--
Mapping `RCLike.ofReal` over a multiset is injective.
-/
private lemma multiset_map_ofReal_injective {R : Type*} [RCLike R] {M N : Multiset ℝ} :
    M.map (RCLike.ofReal : ℝ → R) = N.map RCLike.ofReal ↔ M = N := by
  exact ⟨fun h ↦ by simpa using congr(($h).map RCLike.re), fun h ↦ by rw [h]⟩

/--
If the non-zero roots of the characteristic polynomials of two states are equal,
their von Neumann entropies are equal.
-/
private lemma Sᵥₙ_eq_of_charpoly_roots_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂)
    (h : (ρ₁.M.1.charpoly.roots.filter (· ≠ 0)) = (ρ₂.M.1.charpoly.roots.filter (· ≠ 0))) :
    Sᵥₙ ρ₁ = Sᵥₙ ρ₂ := by
  convert Sᵥₙ_eq_of_nonzero_eigenvalues_eq ρ₁ ρ₂ _;
  have h_spectrum_eq_aux : (Matrix.charpoly (ρ₁.M.1)).roots.filter (· ≠ 0) = (Multiset.map (fun i => ρ₁.spectrum.prob i) Finset.univ.val).filter (· ≠ 0) ∧ (Matrix.charpoly (ρ₂.M.1)).roots.filter (· ≠ 0) = (Multiset.map (fun i => ρ₂.spectrum.prob i) Finset.univ.val).filter (· ≠ 0) := by
    constructor;
    · convert charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero _ _;
      any_goals exact ρ₁.M.isSelfAdjoint;
      simp [ ProbDistribution.prob, MState.spectrum ];
      simp [ Multiset.filter_map, ProbDistribution.mk' ];
      simp [ Subtype.ext_iff ];
    · convert charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero ρ₂.M.1 (HermitianMat.H ρ₂.M) using 1;
      simp [ ProbDistribution.prob, MState.spectrum ];
      simp [ Multiset.filter_map, ProbDistribution.mk' ];
      simp [ Subtype.ext_iff ];
  norm_num +zetaDelta at *;
  rw [ h_spectrum_eq_aux.1, h_spectrum_eq_aux.2 ] at h;
  exact Multiset.map_injective ( by intros a b; aesop ) h

end partial_trace_pure

/-- von Neumman entropies of the left- and right- partial trace of pure states are equal. -/
theorem Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) :
    Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight := by
  apply Sᵥₙ_eq_of_charpoly_roots_eq
  rw [traceLeft_eq_transpose_conjTranspose_mul, traceRight_eq_mul_conjTranspose,
    ← Matrix.charpoly_transpose]
  exact nonzero_eigenvalues_eq_of_mul_comm _ _

/-- Quantum conditional entropy is symmetric for pure states. -/
@[simp]
theorem qConditionalEnt_of_pure_symm (ψ : Ket (d₁ × d₂)) :
    qConditionalEnt (MState.pure ψ).SWAP = qConditionalEnt (MState.pure ψ) := by
  simp [qConditionalEnt, Sᵥₙ_of_partial_eq]

/-- Quantum mutual information is symmetric. -/
@[simp]
theorem qMutualInfo_symm (ρ : MState (d₁ × d₂)) :
    qMutualInfo ρ.SWAP = qMutualInfo ρ := by
  simp [qMutualInfo, add_comm]

/-- For a pure state, the entropy of one subsystem equals the entropy of its complement,
even after relabeling. -/
@[simp]
theorem Sᵥₙ_pure_complement (ψ : Ket d₁) (e : d₂ × d₃ ≃ d₁) :
    Sᵥₙ ((MState.pure ψ).relabel e).traceLeft = Sᵥₙ ((MState.pure ψ).relabel e).traceRight := by
  obtain ⟨ψ', hψ'⟩ := MState.relabel_pure_exists ψ e
  simp only [hψ', Sᵥₙ_of_partial_eq]

end entropy
