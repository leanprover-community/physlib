/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.Relative
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.HermitianMat.LiebConcavity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open HermitianMat
open scoped InnerProductSpace RealInnerProductSpace Topology

/-!
# DPI (Data Processing Inequality)

The Data Processing Inequality (DPI) for the sandwiched Rényi relative entropy, and
as a consequence, the quantum relative entropy.

## Proof structure (for α > 1)

Following Leditzky–Rouzé–Datta (arXiv:1306.5920), the proof proceeds as follows:

1. Define the **trace functional** `Q̃_α(ρ‖σ) = Tr[(σ^γ ρ σ^γ)^α]` where `γ = (1 - α) / (2α)`.
   The sandwiched Rényi divergence satisfies `D̃_α(ρ‖σ) = log(Q̃_α(ρ‖σ)) / (α - 1)`.

2. The DPI for `D̃_α` reduces to **monotonicity of `Q̃_α` under partial trace**:
   `Q̃_α(ρ_AB‖σ_AB) ≥ Q̃_α(ρ_A‖σ_A)` for `α > 1`.

3. This monotonicity is proved via the **twirling argument**:
   - `Q̃_α` is invariant under joint unitary conjugation.
   - `Q̃_α` is jointly convex for `α > 1` (Frank–Lieb).
   - A twirling set of unitaries `{V_i}` averages any state to a product with the
     maximally mixed state.
   - `Q̃_α` is invariant under tensoring with a fixed state.

4. The general DPI for CPTP maps follows via **Stinespring dilation**:
   any CPTP map can be decomposed as ancilla preparation + unitary + partial trace.
-/

open scoped Matrix ComplexOrder
open BigOperators

/-! ## The Sandwiched Trace Functional -/

/-- The sandwiched trace functional `Q̃_α(ρ‖σ) = Tr[(σ^γ ρ σ^γ)^α]` where `γ = (1-α)/(2α)`.
This is the quantity underlying the sandwiched Rényi divergence:
`D̃_α(ρ‖σ) = log(Q̃_α(ρ‖σ)) / (α - 1)`.

Note: the `conj` operation gives `A.conj B = B * A.mat * B†`, and since `σ^γ` is Hermitian
(self-adjoint), `B† = B`, so `ρ.M.conj (σ.M ^ γ).mat = σ^γ * ρ * σ^γ`. -/
noncomputable def sandwichedTraceFunctional (α : ℝ) (ρ σ : MState d) : ℝ :=
  let γ := (1 - α) / (2 * α)
  ((ρ.M.conj (σ.M ^ γ).mat) ^ α).trace

notation "Q̃_" α "(" ρ "‖" σ ")" => sandwichedTraceFunctional α ρ σ

/-! ## Properties of the Trace Functional -/

/-
The sandwiched Rényi divergence equals `log(Q̃_α) / (α - 1)` for `α > 0`, `α ≠ 1`,
when `σ.M.ker ≤ ρ.M.ker`.
-/
theorem sandwichedRelRentropy_eq_log_traceFunctional (hα₀ : 0 < α) (hα₁ : α ≠ 1)
    (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ‖σ) = ENNReal.ofReal (Real.log (Q̃_ α(ρ‖σ)) / (α - 1)) := by
  have hQ : Q̃_ α(ρ‖σ) = ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := rfl
  have hnn : 0 ≤ Real.log (Q̃_ α(ρ‖σ)) / (α - 1) := by
    rw [hQ]
    simpa only [if_neg hα₁] using sandwichedRelRentropy_nonneg hα₀ hker
  rw [MState.sandwichedRelRentropy_eq_matrix, dif_pos hα₀, dif_pos hker,
    ENNReal.ofReal_eq_coe_nnreal hnn]
  congr! 1
  apply NNReal.coe_injective
  show (if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1))
    = Real.log (Q̃_ α(ρ‖σ)) / (α - 1)
  rw [if_neg hα₁, hQ]

/-
`Q̃_α(ρ‖σ)` is nonneg when `α > 0`.
-/
theorem sandwichedTraceFunctional_nonneg (ρ σ : MState d) :
    0 ≤ Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional]
  apply trace_nonneg
  apply rpow_nonneg
  positivity

/-- The trace functional is strictly positive when the kernel condition holds. Under
`σ.M.ker ≤ ρ.M.ker` (i.e. `supp(ρ) ⊆ supp(σ)`), the sandwich `σ^γ ρ σ^γ ≠ 0`
because ρ has support inside σ's support. -/
theorem sandwichedTraceFunctional_pos
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    0 < Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional]
  apply trace_pos
  apply rpow_pos
  apply conj_pos ρ.pos
  grw [← hker]
  exact ker_rpow_le_of_nonneg σ.nonneg

/-! ## Unitary Invariance

`Q̃_α(UρU†‖UσU†) = Q̃_α(ρ‖σ)` for any unitary `U`.

Here, `conj U.val A` denotes `U * A * U†`, so "conjugating ρ and σ by
the same unitary" means applying `conj U.val` to both. -/

/-
The trace functional is invariant under joint unitary conjugation:
`Tr[(U σ U†)^γ (U ρ U†) (U σ U†)^γ)^α] = Tr[(σ^γ ρ σ^γ)^α]`.
This corresponds to equation (2.3) in the paper.
Proved using `rpow_conj_unitary` (f(UXU†) = U f(X) U†) and `conj_conj`.
-/
theorem sandwichedTraceFunctional_conj_unitary_hermitian
    (U : Matrix.unitaryGroup d ℂ) (A B : HermitianMat d ℂ) :
    let γ := (1 - α) / (2 * α)
    ((A.conj U.val).conj ((B.conj U.val) ^ γ).mat ^ α).trace =
      ((A.conj (B ^ γ).mat) ^ α).trace := by
  have h_conj_conj : ∀ (A B : HermitianMat d ℂ) (U : Matrix.unitaryGroup d ℂ),
      (conj U.val A).conj ((conj U.val B).mat) = conj U.val (A.conj B.mat) := by
    intros A B U
    simp [conj]
    have h_unitary : ∀ (U : Matrix.unitaryGroup d ℂ), U.val * U.val.conjTranspose = 1 := by
      exact fun U => U.2.2
    simp [← mul_assoc]
    have := h_unitary U; simp_all [Matrix.mul_assoc, mul_eq_one_comm.mp this]
  simp_all [conj_apply_mat, rpow_conj_unitary]

/-- The trace functional is invariant under joint unitary conjugation of MStates. -/
theorem sandwichedTraceFunctional_conj_unitary_MState
    (U : Matrix.unitaryGroup d ℂ) (ρ σ : MState d) :
    Q̃_ α(ρ.uConj U‖σ.uConj U) = Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional, sandwichedTraceFunctional, MState.uConj_M, MState.uConj_M]
  exact sandwichedTraceFunctional_conj_unitary_hermitian U ρ.M σ.M

/-! ## Joint Convexity for α > 1

The trace functional `Q̃_α` is jointly convex for `α > 1`. This is proved by
Frank and Lieb via a variational formula and strict convexity of trace functions.

### Trace functions convexity

The following result is used in the proof: for a convex function `g : ℝ → ℝ`,
the map `A ↦ Tr[g(A)]` on Hermitian matrices is convex (Carlen, Theorem 2.10).  -/

namespace HermitianMat

end HermitianMat

/-! ### Variational formula for the trace functional
Following Frank–Lieb, for `α > 1` we define
  `f_α(H, ρ, σ) = α · Tr[ρ · H] − (α−1) · Tr[(σ^{−γ} H σ^{−γ})^{α/(α−1)}]`
where `γ = (1−α)/(2α)` (so `−γ = (α−1)/(2α) > 0`).
Key facts (each stated as a lemma below):
1. `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)` for α > 1.
2. For fixed `H`, `f_α` is linear in `ρ` (hence convex).
3. For fixed `H`, `f_α` is convex in `σ` (uses Lieb concavity).
4. Therefore `f_α` is jointly convex in `(ρ, σ)` for fixed `H`.
5. The supremum of jointly convex functions is jointly convex.
-/

/-- The variational function `f_α(H, ρ, σ) = α · ⟪ρ, H⟫ − (α−1) · Tr[(σ^{−γ} H σ^{−γ})^{α/(α−1)}]`
where `γ = (1−α)/(2α)`. For fixed `H ≥ 0`, this is linear in `ρ` and convex in `σ`.
Frank–Lieb show that `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)` for `α > 1`. -/
noncomputable def f_alpha (α : ℝ) (H : HermitianMat d ℂ) (ρ σ : MState d) : ℝ :=
  let γ : ℝ := (1 - α) / (2 * α)
  α * ⟪ρ.M, H⟫_ℝ - (α - 1) * ((H.conj (σ.M ^ (-γ)).mat) ^ (α / (α - 1))).trace

/-- The optimizer in the variational formula: `H_hat = σ^γ (σ^γ ρ σ^γ)^{α−1} σ^γ`
where `γ = (1−α)/(2α)`. -/
noncomputable def H_hat (α : ℝ) (ρ σ : MState d) : HermitianMat d ℂ :=
  let γ := (1 - α) / (2 * α)
  ((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).conj (σ.M ^ γ).mat

/-
**Step 1a**: The optimizer `H_hat` is PSD.
-/
theorem H_hat_nonneg (ρ σ : MState d) : 0 ≤ H_hat α ρ σ := by
  apply conj_nonneg
  apply rpow_nonneg
  positivity

/--
For a PSD Hermitian matrix B whose kernel contains A's kernel, conjugating B by A's
support projection leaves B unchanged.
-/
private lemma conj_supportProj_eq_of_ker_le (A B : HermitianMat d ℂ) (hker : A.ker ≤ B.ker) :
    B.conj (A.supportProj).mat = B := by
  ext i j
  simp [*, conj]
  suffices h_conj : A.supportProj.mat * B.mat * A.supportProj.mat = B.mat by
    exact congr($h_conj i j)
  have h_unitary := mul_supportProj_of_ker_le hker
  apply_fun Matrix.conjTranspose at h_unitary ⊢
  · simp_all only [Matrix.conjTranspose_mul, conjTranspose_mat]
  · exact Matrix.conjTranspose_injective

/--
The kernel of σ is contained in the kernel of (ρ.conj (σ^γ))^{α-1} when γ ≠ 0 and α > 1.
-/
private lemma ker_sigma_le_ker_conj_rpow (ρ σ : MState d) {γ : ℝ} (hγ : γ ≠ 0) (hα1 : α - 1 ≠ 0) :
    σ.M.ker ≤ ((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).ker := by
  rw [ker_rpow_eq_of_nonneg (by positivity) hα1]
  intro x hx
  have h_ker_rpow : x ∈ (σ.M ^ γ).ker := by
    rwa [ker_rpow_eq_of_nonneg σ.nonneg hγ]
  simp_all [ker, lin]

/-- Sub-lemma for Step 1b: the conj of H_hat by σ^{−γ} simplifies to (ρ.M.conj (σ^γ).mat)^{α−1}.
This uses σ^{−γ} · σ^γ = identity (on support) to cancel the outer σ^γ factors. -/
theorem H_hat_conj_sigma (hα : 1 < α) (ρ σ : MState d) :
    let γ := (1 - α) / (2 * α)
    (H_hat α ρ σ).conj (σ.M ^ (-γ)).mat = (ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1) := by
  intro γ
  have hγ : γ ≠ 0 := by
    simp only [γ]; rw [div_ne_zero_iff]; exact ⟨by linarith, by linarith⟩
  have hα1 : α - 1 ≠ 0 := by linarith
  show (((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).conj (σ.M ^ γ).mat).conj (σ.M ^ (-γ)).mat =
    (ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)
  rw [conj_conj]
  rw [rpow_neg_mul_rpow_eq_supportProj σ.nonneg hγ]
  exact conj_supportProj_eq_of_ker_le σ.M _ (ker_sigma_le_ker_conj_rpow ρ σ hγ hα1)


/-
Sub-lemma for Step 1b: the inner product ⟪ρ.M, H_hat⟫ equals Tr[(σ^γ ρ σ^γ)^α].
By cyclicity of trace: Tr[ρ · σ^γ · (σ^γ ρ σ^γ)^{α−1} · σ^γ] = Tr[(σ^γ ρ σ^γ)^α].
-/
theorem inner_rho_H_hat (hα : 1 < α) (ρ σ : MState d) :
    let γ := (1 - α) / (2 * α)
    ⟪ρ.M, H_hat α ρ σ⟫_ℝ = ((ρ.M.conj (σ.M ^ γ).mat) ^ α).trace := by
  unfold H_hat; simp [inner_def]
  have h_cyclic : (ρ.m * (σ.M ^ ((1 - α) / (2 * α))).mat *
      ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ (α - 1)).mat *
      (σ.M ^ ((1 - α) / (2 * α))).mat).trace =
      ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
    have h_cyclic : (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat).mat *
        ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ (α - 1)).mat =
        ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).mat := by
      have := @mat_rpow_add
      specialize this (show 0 ≤ conj (σ.M ^ ((1 - α) / (2 * α))).mat ρ.M from ?_)
        (show (1 : ℝ) + (α - 1) ≠ 0 from by linarith)
      · positivity
      · aesop
    convert congr_arg Matrix.trace h_cyclic using 1
    · rw [← Matrix.trace_mul_comm]; simp [Matrix.mul_assoc]
    · simp [trace]
      norm_num [Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      convert Complex.ofReal_re (((conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α) i i).re
      simp [Complex.ext_iff]
  simp_all [← Matrix.mul_assoc]

/-
**Step 1b**: Evaluating `f_α` at the optimizer `H_hat` gives `Q̃_α(ρ‖σ)`.
This is the key computation that verifies the variational formula at the optimizer.
Proof: f_α(H_hat, ρ, σ) = α · Tr[(σ^γ ρ σ^γ)^α] - (α-1) · Tr[(σ^γ ρ σ^γ)^α] = Tr[(σ^γ ρ σ^γ)^α] = Q̃.
-/
theorem f_alpha_at_optimizer (hα : 1 < α) (ρ σ : MState d) :
    f_alpha α (H_hat α ρ σ) ρ σ = Q̃_ α(ρ‖σ) := by
  have h_inner : ⟪ρ.M, H_hat α ρ σ⟫_ℝ = ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
    exact inner_rho_H_hat hα ρ σ
  have h_conj : (H_hat α ρ σ).conj (σ.M ^ ((α - 1) / (2 * α))).mat =
      (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ (α - 1) := by
    convert H_hat_conj_sigma (hα := hα) (ρ := ρ) (σ := σ) using 1
    ring_nf!
  unfold f_alpha sandwichedTraceFunctional
  simp_all [sub_div]
  rw [← rpow_mul]; norm_num [show α ≠ 0 by positivity, show α - 1 ≠ 0 by linarith]
  · rw [mul_div_cancel₀ _ (by linarith)]; ring
  · apply_rules [conj_nonneg]
    exact ρ.nonneg

/--
For PSD `A` and `γ ≠ 0`, the product `A^γ * A^{-γ}` equals the support projection
of `A`. This is because `x^γ * x^{-γ} = if x = 0 then 0 else 1` for `x ≥ 0`.
-/
lemma rpow_mul_neg_rpow_eq_supportProj {A : HermitianMat d ℂ}
    (hA : 0 ≤ A) (γ : ℝ) (hγ : γ ≠ 0) :
    (A ^ γ).mat * (A ^ (-γ)).mat = A.supportProj.mat := by
  rw [supportProj_eq_cfc]
  rw [rpow_eq_cfc, rpow_eq_cfc]
  rw [← mat_cfc_mul_apply]
  refine congr_arg _ (cfc_congr_of_nonneg hA ?_)
  intro x (hx : 0 ≤ x)
  rcases eq_or_ne x 0 with hx' | hx'
  · simp [hx', hγ]
  · simp [hx', Real.rpow_neg hx]
    exact mul_inv_cancel₀ (by positivity)

/--
The support projection of `A` acts as identity on `B` when `A.ker ≤ B.ker`.
Since `A.supportProj` projects onto `ker(A)⊥` and `B` is zero on `ker(A)`,
the projection preserves `B`.
-/
lemma supportProj_mul_of_ker_le {A B : HermitianMat d ℂ}
    (hker : A.ker ≤ B.ker) :
    A.supportProj.mat * B.mat = B.mat := by
  contrapose! hker
  simp_all [SetLike.le_def]
  -- Since $B$ is not in the kernel of $A$, there exists some $x \in \ker(A)$ such that $Bx \neq 0$.
  obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℂ d, A.mat *ᵥ x = 0 ∧ B.mat *ᵥ x ≠ 0 := by
    contrapose! hker
    have h_support : ∀ x : EuclideanSpace ℂ d, B.mat *ᵥ x = B.mat *ᵥ (A.supportProj.mat *ᵥ x) := by
      intro x
      have h_support : x.ofLp = A.supportProj.mat *ᵥ x.ofLp + A.kerProj.mat *ᵥ x.ofLp := by
        have h_support : A.supportProj.mat + A.kerProj.mat = 1 := by
          simp [add_comm]
          simp [← Matrix.ext_iff]
          intro i j; exact (by
          have h_support : A.kerProj + A.supportProj = 1 := by
            exact kerProj_add_supportProj A
          convert! congr_arg (fun f => f i j) h_support using 1)
        rw [← Matrix.add_mulVec, h_support, Matrix.one_mulVec]
      have hsup : B.mat *ᵥ (A.kerProj.mat *ᵥ x.ofLp) = 0 := by
        convert hker _ _
        have h_support : A.mat * A.kerProj.mat = 0 := by
          have h_support : A.mat * A.kerProj.mat = A.mat * (1 - A.supportProj.mat) := by
            congr
            have h_support : A.kerProj + A.supportProj = 1 := by
              exact kerProj_add_supportProj A
            exact eq_sub_of_add_eq <| congr_arg Subtype.val h_support
          rw [h_support, mul_sub, mul_one, sub_eq_zero]
          exact Eq.symm (mul_supportProj_of_ker_le fun ⦃x⦄ a => a)
        convert congr_arg (fun m => m *ᵥ x.ofLp) h_support using 1
        · simp
        · simp
      convert congr_arg (fun y => B.mat *ᵥ y) h_support using 1
      simp [Matrix.mulVec_add, hsup]
    have h_support : B.mat = B.mat * A.supportProj.mat := by
      ext i j
      convert congr_fun (h_support (EuclideanSpace.single j 1)) i using 1
      · simp [Matrix.mulVec, dotProduct]
      · simp [Matrix.mulVec, dotProduct]
        rfl
    have h_support : B.mat = B.mat.conjTranspose := by
      exact B.2.symm
    have h_support : (B.mat * A.supportProj.mat).conjTranspose = A.supportProj.mat * B.mat := by
      simp [Matrix.conjTranspose_mul]
    lia
  refine ⟨x, ?_, ?_⟩
  · simpa [ker, lin, funext_iff, Matrix.toLpLin] using hx.1
  · rw [mem_ker_iff_mulVec_zero]
    exact hx.right

/--
Under the support condition `σ.M.ker ≤ ρ.M.ker` (i.e., supp(ρ) ⊆ supp(σ)),
conjugation by `σ^γ` and `σ^{-γ}` preserves the inner product:
`⟪ρ.M, H⟫ = ⟪σ^γ ρ σ^γ, σ^{-γ} H σ^{-γ}⟫`. This holds because the kernel condition
ensures `ρ` is supported on `supp(σ)`, where `σ^γ σ^{-γ}` acts as the identity.
-/
lemma inner_eq_inner_conj_of_ker_le (ρ σ : MState d)
    (H : HermitianMat d ℂ) (hker : σ.M.ker ≤ ρ.M.ker) (γ : ℝ) (hγ : γ ≠ 0) :
    ⟪ρ.M, H⟫_ℝ = ⟪ρ.M.conj (σ.M ^ γ).mat, H.conj (σ.M ^ (-γ)).mat⟫_ℝ := by
  -- Since σ^γ σ^-γ acts as the identity on the support of ρ, we can simplify
  have h_support :
      (σ.M ^ γ).mat * (σ.M ^ (-γ)).mat = σ.M.supportProj.mat ∧
      (σ.M ^ (-γ)).mat * (σ.M ^ γ).mat = σ.M.supportProj.mat :=
    ⟨rpow_mul_neg_rpow_eq_supportProj σ.nonneg γ hγ,
     by simpa using rpow_mul_neg_rpow_eq_supportProj σ.nonneg (-γ) (neg_ne_zero.mpr hγ)⟩
  simp only [inner_def, conj_apply_mat]
  have h_support :
      σ.M.supportProj.mat * ρ.M.mat = ρ.M.mat ∧
      ρ.M.mat * σ.M.supportProj.mat = ρ.M.mat := by
    exact ⟨supportProj_mul_of_ker_le hker, mul_supportProj_of_ker_le hker⟩
  have h_trace_cyclic :
      Matrix.trace ((σ.M ^ γ).mat * ρ.M.mat * (σ.M ^ γ).mat *
        (σ.M ^ (-γ)).mat * H.mat * (σ.M ^ (-γ)).mat) =
      Matrix.trace ((σ.M ^ (-γ)).mat * (σ.M ^ γ).mat * ρ.M.mat *
        (σ.M ^ γ).mat * (σ.M ^ (-γ)).mat * H.mat) := by
    rw [← Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  simp_all [mul_assoc, Matrix.trace_mul_comm ((σ.M ^ γ).mat)]
  simp_all [← mul_assoc]

/-- **Step 1c**: `H_hat` is a maximizer: for all `H ≥ 0`, `f_α(H) ≤ f_α(H_hat)`.
This uses the trace Young inequality: for PSD `A, B` and conjugate exponents `p, q > 1`,
`⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q`.
Applied with `A = σ^γ ρ σ^γ`, `B = σ^{-γ} H σ^{-γ}`, `p = α`, `q = α/(α-1)`,
the inner product identity `⟪ρ, H⟫ = ⟪A, B⟫` (under the support condition) yields
`f_α(H) ≤ Tr[A^α] = Q̃_α(ρ‖σ) = f_α(H_hat)`.
Note: the support condition `σ.M.ker ≤ ρ.M.ker` (i.e., supp(ρ) ⊆ supp(σ)) is necessary.
Without it, the theorem is false: taking ρ orthogonal to σ gives Q̃_α = 0 but
`f_α(H) = α · Tr[ρH] > 0` for appropriate H. -/
theorem f_alpha_le_at_optimizer (hα : 1 < α) (ρ σ : MState d)
    (H : HermitianMat d ℂ) (hH : 0 ≤ H) (hker : σ.M.ker ≤ ρ.M.ker) :
    f_alpha α H ρ σ ≤ f_alpha α (H_hat α ρ σ) ρ σ := by
  rw [f_alpha_at_optimizer hα]
  -- Goal: f_alpha α H ρ σ ≤ Q̃_α(ρ‖σ)
  set γ : ℝ := (1 - α) / (2 * α) with hγ_def
  have hγ : γ ≠ 0 := by
    intro h; have h1 : (1 - α) / (2 * α) = 0 := hγ_def ▸ h
    have h2 : (2 : ℝ) * α ≠ 0 := by positivity
    rw [div_eq_zero_iff] at h1; rcases h1 with h1 | h1 <;> linarith
  set A := ρ.M.conj (σ.M ^ γ).mat
  set B := H.conj (σ.M ^ (-γ)).mat
  have hA_nn : 0 ≤ A := conj_nonneg _ ρ.nonneg
  have hB_nn : 0 ≤ B := conj_nonneg _ hH
  have h_inner : ⟪ρ.M, H⟫_ℝ = ⟪A, B⟫_ℝ :=
    inner_eq_inner_conj_of_ker_le ρ σ H hker γ hγ
  have hpq : 1 / α + 1 / (α / (α - 1)) = 1 := by field_simp; ring
  have h_young := trace_young A B hA_nn hB_nn α (α / (α - 1)) hα hpq
  have hα_pos : (0 : ℝ) < α := by linarith
  have hαm1_pos : (0 : ℝ) < α - 1 := by linarith
  -- Multiply h_young by α and simplify
  have h_scaled : α * ⟪A, B⟫_ℝ ≤
      (A ^ α).trace + (α - 1) * (B ^ (α / (α - 1))).trace := by
    have := mul_le_mul_of_nonneg_left h_young hα_pos.le
    have h_simp : α * ((A ^ α).trace / α + (B ^ (α / (α - 1))).trace / (α / (α - 1))) =
        (A ^ α).trace + (α - 1) * (B ^ (α / (α - 1))).trace := by
      field_simp
    linarith
  -- Goal is definitionally: α * ⟪ρ.M, H⟫ - (α-1) * (B ^ (α/(α-1))).trace ≤ (A ^ α).trace
  -- which follows from h_scaled and h_inner
  change α * ⟪ρ.M, H⟫_ℝ - (α - 1) * (B ^ (α / (α - 1))).trace ≤ (A ^ α).trace
  have h_inner_scaled : α * ⟪ρ.M, H⟫_ℝ = α * ⟪A, B⟫_ℝ := by rw [h_inner]
  linarith [h_scaled, h_inner_scaled]

/--
**Step 1 (Variational formula)**: For `α > 1`, the trace functional equals the
supremum of `f_α` over all PSD `H`:
  `Q̃_α(ρ‖σ) = ⨆ (H : HermitianMat d ℂ) (_ : 0 ≤ H), f_alpha α H ρ σ`.
The optimizer is `H_hat = σ^γ (σ^γ ρ σ^γ)^{α−1} σ^γ`.
-/
theorem traceFunctional_eq_iSup_f_alpha (hα : 1 < α) (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    Q̃_ α(ρ‖σ) = ⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 ρ σ := by
  rw [@ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · intro i
    rw [← f_alpha_at_optimizer hα ρ σ]
    exact f_alpha_le_at_optimizer hα ρ σ i i.2 hker
  · intro w hw
    exact ⟨⟨H_hat α ρ σ, H_hat_nonneg ρ σ⟩, hw.trans_le (f_alpha_at_optimizer hα ρ σ ▸ le_rfl)⟩

/-- (Convexity in σ): For fixed `H ≥ 0` and `ρ`, and `α > 1`, the map
`σ ↦ f_alpha α H ρ σ` is convex. The key is that for `p = α/(α−1) > 1`:
• `A ↦ Tr[A^p]` is convex on PSD matrices (trace function convexity, Theorem 2.10 of Carlen),
• `σ ↦ σ^{−γ} H σ^{−γ}` is *concave* in `σ` by Lieb concavity (since `−γ = (α−1)/(2α) ∈ (0,½)`),
• The composition of a convex non-decreasing function with a concave function is convex,
  but we actually need the sign: the second term has a factor `−(α−1) < 0` which
  flips concave → convex.
More precisely: `σ ↦ Tr[(σ^{−γ} H σ^{−γ})^p]` is concave (by Lieb + trace function convexity),
so `σ ↦ −(α−1) · Tr[(σ^{−γ} H σ^{−γ})^p]` is convex. -/
theorem f_alpha_convex_in_sigma (hα : 1 < α) (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    (ρ : MState d) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (σs : ι → MState d) (σ_mix : MState d)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M) :
    f_alpha α H ρ σ_mix ≤ ∑ i, w i * f_alpha α H ρ (σs i) := by
  have hα_pos : 0 < α - 1 := by linarith
  -- Define the σ-dependent trace function on HermitianMat
  let s := (α - 1) / (2 * α)
  let p := α / (α - 1)
  let F : HermitianMat d ℂ → ℝ := fun σ => ((H.conj (σ ^ s).mat) ^ p).trace
  -- f_alpha relates to F via: f_alpha α H ρ σ = α * ⟪ρ.M, H⟫ - (α-1) * F(σ.M)
  -- because -γ = -((1-α)/(2α)) = (α-1)/(2α) = s
  have hf_eq : ∀ σ : MState d, f_alpha α H ρ σ = α * ⟪ρ.M, H⟫_ℝ - (α - 1) * F σ.M := by
    intro σ
    show _ = α * ⟪ρ.M, H⟫_ℝ - (α - 1) *
      ((H.conj (σ.M ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace
    unfold f_alpha; ring_nf
  simp_rw [hf_eq]
  -- Reduce to concavity: ∑ w_i * F(σ_i.M) ≤ F(σ_mix.M)
  suffices h : ∑ i, w i * F (σs i).M ≤ F σ_mix.M by
    have h1 : ∑ i, w i * ((α - 1) * F (σs i).M) = (α - 1) * ∑ i, w i * F (σs i).M := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul, h1]
    linarith [mul_le_mul_of_nonneg_left h (le_of_lt hα_pos)]
  -- Apply ConcaveOn.le_map_sum from trace_conj_rpow_concave
  have hF_concave : ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ} F :=
    trace_conj_rpow_concave hα H hH
  have h_jensen := hF_concave.le_map_sum
    (t := Finset.univ) (w := w) (p := fun i => (σs i).M)
    (fun i _ => hw_nonneg i)
    (by simp [hw_sum])
    (fun i _ => (σs i).nonneg)
  rw [← hσ_mix] at h_jensen
  convert! h_jensen using 1

/-
**Step 4 (Joint convexity of f_α)**: For fixed `H ≥ 0` and `α > 1`, the map
`(ρ, σ) ↦ f_alpha α H ρ σ` is jointly convex. This follows from Steps 2 and 3:
f_α decomposes as a function linear in ρ (independent of σ) plus a function convex
in σ (independent of ρ).
-/
theorem f_alpha_jointly_convex (hα : 1 < α) (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M) :
    f_alpha α H ρ_mix σ_mix ≤ ∑ i, w i * f_alpha α H (ρs i) (σs i) := by
  convert f_alpha_convex_in_sigma hα H hH ρ_mix _ _ _ _ using 1
  any_goals assumption
  constructor <;> intro h
  · exact fun σ_mix hσ_mix =>
    f_alpha_convex_in_sigma hα H hH ρ_mix w hw_nonneg hw_sum σs σ_mix hσ_mix
  · apply (h σ_mix hσ_mix).trans
    unfold f_alpha
    simp [hρ_mix]
    simp [sum_inner, inner_smul_left, mul_sub, sub_mul, mul_comm, mul_left_comm, Finset.mul_sum]
    simp [← Finset.mul_sum, ← Finset.sum_mul, hw_sum]

/-
The range of `H ↦ f_alpha α H ρ σ` over PSD `H` is bounded above.
This follows from the variational formula: the supremum equals `Q̃_α(ρ‖σ)`,
which is a finite real number.
-/
theorem f_alpha_bddAbove (hα : 1 < α) (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    BddAbove (Set.range (fun H : {H : HermitianMat d ℂ // 0 ≤ H} => f_alpha α H.1 ρ σ)) := by
  exact ⟨_, Set.forall_mem_range.mpr fun H => f_alpha_le_at_optimizer hα ρ σ _ H.2 hker⟩

/-
**Step 5 (Sup preserves convexity)**: The supremum over `H ≥ 0` of the jointly
convex `f_alpha α H` is jointly convex. This is a standard fact: for each `H`,
`f_alpha α H (ρ_mix) (σ_mix) ≤ ∑ wᵢ f_alpha α H (ρᵢ) (σᵢ) ≤ ∑ wᵢ sup_H f_alpha ...`,
so taking sup on the left gives the result.
-/
theorem iSup_f_alpha_jointly_convex (hα : 1 < α)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M)
    (hker : ∀ i, (σs i).M.ker ≤ (ρs i).M.ker) :
    (⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 ρ_mix σ_mix) ≤
      ∑ i, w i * (⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 (ρs i) (σs i)) := by
  apply ciSup_le
  intro H
  have h_sum : f_alpha α H.1 ρ_mix σ_mix ≤ ∑ i, w i * (f_alpha α H.1 (ρs i) (σs i)) := by
    apply f_alpha_jointly_convex hα H.1 H.2 w hw_nonneg hw_sum ρs σs ρ_mix σ_mix hρ_mix hσ_mix
  exact h_sum.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (le_ciSup (f_alpha_bddAbove hα (ρs i) (σs i) (hker i)) H) (hw_nonneg i))

/-- If for all i, ker(σs i) ≤ ker(ρs i), then ker(∑ w i • σs i) ≤ ker(∑ w i • ρs i),
provided all weights are nonneg and all matrices are PSD. -/
theorem HermitianMat.ker_weighted_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (ρs σs : ι → HermitianMat d ℂ)
    (hρs_nonneg : ∀ i, 0 ≤ ρs i)
    (hσs_nonneg : ∀ i, 0 ≤ σs i)
    (hker : ∀ i, (σs i).ker ≤ (ρs i).ker) :
    (∑ i, w i • σs i).ker ≤ (∑ i, w i • ρs i).ker := by
  rw [ker_sum, ker_sum]
  · refine iInf_mono fun i ↦ ?_
    by_cases hi : w i = 0
    · simp [hi]
    · simp_all [ker_pos_smul]
  · exact fun i => smul_nonneg (hw_nonneg i) (hρs_nonneg i)
  · exact fun i => smul_nonneg (hw_nonneg i) (hσs_nonneg i)

/-- The trace functional `Q̃_α` is jointly convex for `α > 1`.
This is Proposition 3 of the paper, originally from Frank–Lieb.
The proof uses the variational formula:
  `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)`
where `f_α(H, ρ, σ) = α · Tr[ρ H] - (α-1) · Tr[(σ^{-γ} H σ^{-γ})^{α/(α-1)}]`
is jointly convex in `(ρ, σ)` for fixed `H` (since the first term is linear and
the second uses the convexity of trace functions). The supremum of jointly convex
functions is jointly convex. -/
theorem sandwichedTraceFunctional_jointly_convex (hα : 1 < α) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M)
    (hker : ∀ i, (σs i).M.ker ≤ (ρs i).M.ker) :
    Q̃_ α(ρ_mix‖σ_mix) ≤ ∑ i, w i * Q̃_ α(ρs i‖σs i) := by
  have hker' : σ_mix.M.ker ≤ ρ_mix.M.ker := by
    rw [hρ_mix, hσ_mix]
    exact ker_weighted_sum_le w hw_nonneg _ _ (fun i => (ρs i).nonneg) (fun i => (σs i).nonneg) hker
  rw [traceFunctional_eq_iSup_f_alpha hα ρ_mix σ_mix hker']
  calc ⨆ H : {H : HermitianMat d ℂ // 0 ≤ H}, f_alpha α H.1 ρ_mix σ_mix
      ≤ ∑ i, w i * (⨆ H : {H : HermitianMat d ℂ // 0 ≤ H}, f_alpha α H.1 (ρs i) (σs i)) :=
        iSup_f_alpha_jointly_convex hα w hw_nonneg hw_sum ρs σs ρ_mix σ_mix hρ_mix hσ_mix hker
    _ = ∑ i, w i * Q̃_ α(ρs i‖σs i) := by
        congr 1; ext i
        rw [traceFunctional_eq_iSup_f_alpha hα (ρs i) (σs i) (hker i)]

/-! ### Twirling Construction Helpers
We construct a twirling set using κ = Perm dB × (dB → Bool).
For each (σ, f), the unitary V(σ,f) is the product of a sign-diagonal matrix
(with entries ±1 determined by f) and a permutation matrix.
The averaging property follows from:
1. Sign averaging: summing over f kills off-diagonal entries
2. Permutation averaging: summing over σ uniformizes diagonal entries
-/

/-
A diagonal matrix with ±1 entries (determined by a Bool function) is unitary.
-/
private lemma signDiag_mem_unitaryGroup (f : dB → Bool) :
    Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) ∈ Matrix.unitaryGroup dB ℂ := by
  constructor
  · ext i j; by_cases hi : i = j <;> simp [hi]
    · split_ifs <;> simp [*, Matrix.one_apply]
    · rw [Matrix.diagonal_apply_ne _ (.symm hi)]
      simp
  · ext i j; by_cases hi : i = j <;> simp [hi]
    · split_ifs <;> simp [*, Matrix.one_apply]
    · rw [Matrix.diagonal_apply_ne _ (.symm hi)]
      simp

/-- The product of a ±1 diagonal matrix and a permutation matrix is unitary. -/
private lemma twirlingU_mem_unitaryGroup (σ : Equiv.Perm dB) (f : dB → Bool) :
    Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) * σ.permMatrix ℂ ∈
      Matrix.unitaryGroup dB ℂ :=
  mul_mem (signDiag_mem_unitaryGroup f) (σ.permMatrix_mem_unitaryGroup)

/-- The twirling unitary for a given permutation and sign function. -/
private def twirlingU (σ : Equiv.Perm dB) (f : dB → Bool) : Matrix.unitaryGroup dB ℂ :=
  ⟨Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) * σ.permMatrix ℂ,
   twirlingU_mem_unitaryGroup σ f⟩

/-
Entry of the conjugation by a twirling unitary:
  (X.conj (twirlingU σ f))_{pq} = sign(f,p) * sign(f,q) * X_{σp, σq}.
-/
private lemma twirlingU_conj_entry (X : HermitianMat dB ℂ) (σ : Equiv.Perm dB) (f : dB → Bool)
    (p q : dB) :
    (X.conj (twirlingU σ f : Matrix dB dB ℂ)) p q =
      (if f p then (-1 : ℂ) else 1) * (if f q then (-1 : ℂ) else 1) * X (σ p) (σ q) := by
  have h_conj_apply : ∀ u : Matrix.unitaryGroup dB ℂ, (conj u.val X).mat =
      u.val * X.mat * u.val.conjTranspose := by
    intro u
    simp_all only [conj_apply_mat]
  convert! congr_fun (congr_fun (h_conj_apply (twirlingU σ f)) p) q using 1
  unfold twirlingU
  simp [Matrix.mul_apply, Matrix.diagonal]
  simp [Finset.sum_ite]
  rw [Finset.sum_eq_single (σ q)]
  · simp_all only [conj_apply_mat, implies_true, Equiv.symm_apply_apply, ↓reduceIte]
    split
    next h =>
      simp_all only [map_neg, map_one, mul_neg, mul_one, neg_neg]
      split
      next h_1 => simp_all only [neg_neg]
      next h_1 => simp_all only [Bool.not_eq_true]
    next h => simp_all only [Bool.not_eq_true, map_one, mul_one]
  · aesop
  · simp

/-
Summing the sign product over all Bool functions.
  For p = q, each term is 1, giving 2^(card dB).
  For p ≠ q, terms cancel in pairs (flip f at p).
-/
private lemma sum_sign_prod (p q : dB) :
    ∑ f : dB → Bool, ((if f p then (-1 : ℂ) else 1) * (if f q then (-1 : ℂ) else 1)) =
      if p = q then (2 ^ Fintype.card dB : ℕ) else 0 := by
  split_ifs with h
  · simp +contextual [h]
  simp +contextual
  -- By pairing each function with its p-flip, we can see that the sum of each pair is zero.
  have h_pair :
      ∑ f : dB → Bool, (if f q then -if f p then -1 else 1 else if f p then -1 else 1 : ℂ) =
      ∑ f : dB → Bool, - (if f q then -if f p then -1 else 1 else if f p then -1 else 1 : ℂ) := by
    apply Finset.sum_bij (fun f _ => Function.update f p (¬f p)) (by simp)
    · intro a₁ _ a₂ _ h; ext x; by_cases hx : x = p
      · replace h := congr_fun h x
        subst hx
        simp_all only [Finset.mem_univ, Bool.not_eq_true, Bool.decide_eq_false,
          Function.update_self, Bool.not_eq_eq_eq_not, Bool.not_not]
      · replace h := congr_fun h x
        simp_all only [Finset.mem_univ, Bool.not_eq_true, Bool.decide_eq_false, ne_eq,
          not_false_eq_true, Function.update_of_ne]
    · exact fun b _ => ⟨Function.update b p (decide ¬b p = true), Finset.mem_univ _, by simp⟩
    · grind
  rw [Finset.sum_neg_distrib] at h_pair
  linear_combination h_pair / 2

/-
Summing X_{σ(p), σ(p)} over all permutations σ.
  For each target k, exactly (card dB - 1)! permutations send p to k.
-/
private lemma sum_perm_diag_entry (X : HermitianMat dB ℂ) (p : dB) :
    ∑ σ : Equiv.Perm dB, X (σ p) (σ p) =
      ((Fintype.card dB - 1).factorial : ℂ) * ∑ k : dB, X k k := by
  -- For each fixed k, the number of permutations σ with σ p = k is (card dB - 1)!
  have h_card (k : dB) : (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = k)).card =
      (Nat.factorial (Fintype.card dB - 1) : ℕ) := by
    have h_fixed : Finset.card (Finset.filter (fun σ : Equiv.Perm dB => σ p = k) Finset.univ) =
        Finset.card (Finset.univ : Finset (Equiv.Perm dB)) / Fintype.card dB := by
      have h_card : ∀ k : dB, (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = k)).card =
          (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = p)).card := by
        intro k
        apply Finset.card_bij (fun σ _ => Equiv.swap p k * σ)
        · intro a ha
          simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.coe_mul,
            Function.comp_apply, Equiv.swap_apply_right, and_self]
        · simp
        · simp
          exact fun b hb => ⟨Equiv.swap p k * b, by simp [hb], by simp⟩
      have hc2 : (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = p)).card * Fintype.card dB =
          Finset.card (Finset.univ : Finset (Equiv.Perm dB)) := by
        have hc : ∑ k : dB, (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = k)).card =
            Finset.card (Finset.univ : Finset (Equiv.Perm dB)) := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
        simp_all [mul_comm]
      rw [← hc2, h_card k, Nat.mul_div_cancel _ (Fintype.card_pos_iff.mpr ⟨p⟩)]
    rcases n : Fintype.card dB with (_ | _ | n) <;> simp_all [Nat.factorial_succ, Fintype.card_perm]
    exact absurd n (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨p⟩))
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ σ : Equiv.Perm dB, X (σ p) (σ p) = ∑ k : dB, ∑ σ ∈ Finset.univ.filter
      (fun σ : Equiv.Perm dB => σ p = k), X k k := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    intro x a
    simp_all only [Finset.mem_univ, Finset.sum_ite_eq, ↓reduceIte]
  simp_all [Finset.mul_sum]

/-
The sum formula for twirling: summing the conjugation entries over all (σ, f) pairs.
-/
private lemma twirling_sum_eq [Nonempty dB] (X : HermitianMat dB ℂ) (p q : dB) :
    ∑ i : Equiv.Perm dB × (dB → Bool), (X.conj (twirlingU i.1 i.2 : Matrix dB dB ℂ)) p q =
      if p = q then ((Fintype.card dB - 1).factorial * 2 ^ Fintype.card dB : ℕ) * ∑ k, X k k
      else 0 := by
  -- Rewrite the sum as a double sum over σ and f using Finset.sum_product'.
  have h_double_sum : ∑ i : Equiv.Perm dB × (dB → Bool),
      ((conj (twirlingU i.1 i.2 : Matrix dB dB ℂ)) X) p q =
    ∑ σ : Equiv.Perm dB, ∑ f : dB → Bool, ((if f p then (-1 : ℂ) else 1) *
        (if f q then (-1 : ℂ) else 1) * X (σ p) (σ q)) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun i _ => (i.1, i.2)) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp [twirlingU_conj_entry]
  split_ifs with h
  · simp_all [← Finset.mul_sum]
    have := sum_perm_diag_entry X q; simp_all [mul_assoc, mul_comm]
  · rw [h_double_sum, Finset.sum_eq_zero]
    intro σ _
    rw [← Finset.sum_mul, sum_sign_prod p q]
    simp_all only [mul_ite, mul_neg, mul_one, ite_mul, neg_mul, one_mul, Finset.mem_univ, reduceIte,
      CharP.cast_eq_zero, zero_mul]

/-
The identity for the twirling set, stated for κ = Perm dB × (dB → Bool).
-/
private lemma twirling_identity [Nonempty dB] (X : HermitianMat dB ℂ) :
    (Fintype.card (Equiv.Perm dB × (dB → Bool)) : ℝ)⁻¹ •
      ∑ i : Equiv.Perm dB × (dB → Bool), X.conj (twirlingU i.1 i.2 : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ) := by
  ext p q
  simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_pi]
  ring_nf
  convert congr_arg ((2⁻¹ ^ Fintype.card dB * (Fintype.card dB |> Nat.factorial : ℂ)⁻¹) * ·)
      (twirling_sum_eq X p q) using 1
  · norm_num [Matrix.one_apply]
    convert! Or.inl rfl
    induction (Finset.univ : Finset (Equiv.Perm dB × (dB → Bool))) using Finset.induction
    · simp_all only [Finset.sum_empty, HermitianMat.zero_apply]
    · rename_i a s a_1 a_2
      obtain ⟨fst, snd⟩ := a
      simp only [not_false_eq_true, Finset.sum_insert, *]
      rfl
  · norm_num [Matrix.one_apply]
    rw [show X.trace = ∑ k, X k k from X.trace_eq_trace]
    rcases n : Fintype.card dB with (_ | n)
    · simp_all
    · simp_all [Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm]
      simp [Nat.factorial_ne_zero]

/-! ## Twirling Set

A twirling set for a finite-dimensional system `dB` is a set of unitary matrices
`{V_i}` on `dB` (indexed by some finite type `κ`) such that the average
`(1/|κ|) Σ_i V_i X V_i†` equals `Tr(X) · (1/dim(dB))` for all `X`.
When applied as `1_A ⊗ V_i` on a bipartite system `dA × dB`, this gives:
`(1/|κ|) Σ_i (1_A ⊗ V_i) ρ_AB (1_A ⊗ V_i)† = ρ_A ⊗ π_B`
where `π_B = 1/dim(dB)` is the maximally mixed state.

The standard construction uses the Heisenberg–Weyl (discrete Weyl) operators. -/

/-- A twirling set for the system `dB` exists: there is a finite collection of unitaries
whose average conjugation action twirls any matrix to a multiple of the identity.
Specifically, `(1/|κ|) Σ_i V_i X V_i† = (Tr X / dim dB) · I` for all Hermitian X on dB.
The standard construction uses the discrete Heisenberg-Weyl group of order `|dB|²`. -/
private lemma exists_twirling_unitaries [Nonempty dB] :
    ∃ (κ : Type) (_ : Fintype κ) (_ : Nonempty κ) (V : κ → Matrix.unitaryGroup dB ℂ),
      ∀ (X : HermitianMat dB ℂ),
        (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
          (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ) := by
  use Shrink (Equiv.Perm dB × (dB → Bool)), inferInstance, inferInstance
  use fun i => twirlingU ((equivShrink _).symm i).1 ((equivShrink _).symm i).2
  intro X
  rw [Fintype.card_shrink]
  convert twirling_identity X using 2
  refine Finset.sum_bij (fun i _ => (equivShrink _).symm i) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
    exact fun a b => ⟨_, Equiv.apply_symm_apply _ _⟩
  · simp


-- /-- Twirling on a bipartite system: applying `1_A ⊗ V_i` and averaging produces the
-- partial trace tensored with the maximally mixed state. -/
-- theorem twirling_bipartite [Nonempty dB]
--     (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
--     (hV : ∀ (X : HermitianMat dB ℂ),
--       (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
--         (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
--     (A : HermitianMat (dA × dB) ℂ) :
--     (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ,
--       A.conj (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) (V i : Matrix dB dB ℂ)) =
--       A.traceRight ⊗ₖ ((Fintype.card dB : ℝ)⁻¹ • (1 : HermitianMat dB ℂ)) := by
--   not needed...

/-! ## Tensor Invariance

`Q̃_α(ρ ⊗ τ ‖ σ ⊗ τ) = Q̃_α(ρ ‖ σ)` for any state `τ`.
This corresponds to equation (2.4) in the paper. -/

/-
The trace functional is multiplicative over tensor products:
`Q̃_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q̃_α(ρ₁‖σ₁) · Q̃_α(ρ₂‖σ₂)`.
-/
theorem sandwichedTraceFunctional_mul
    (ρ₁ σ₁ : MState dA) (ρ₂ σ₂ : MState dB) :
    Q̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = Q̃_ α(ρ₁‖σ₁) * Q̃_ α(ρ₂‖σ₂) := by
  exact sandwiched_term_product ρ₁ σ₁ ρ₂ σ₂ α ((1 - α) / (2 * α))

/-
The trace functional of a state with itself equals 1.
This follows from the calculation: `γ = (1-α)/(2α)` gives `2γ + 1 = 1/α`,
so `σ^γ · σ · σ^γ = σ^(2γ+1) = σ^(1/α)`, and `(σ^(1/α))^α = σ^1`,
whose trace equals 1 since σ is a state.
-/
theorem sandwichedTraceFunctional_self (hα : 0 < α) (ρ : MState d) :
    Q̃_ α(ρ‖ρ) = 1 := by
  by_cases h : α = 1
  · subst h; simp [sandwichedTraceFunctional]
  · unfold sandwichedTraceFunctional
    have := ρ.pos
    have h_simp : (ρ.M.conj (ρ.M ^ ((1 - α) / (2 * α))).mat) =
        ρ.M ^ (1 + 2 * ((1 - α) / (2 * α))) := by
      rw [← conj_rpow]
      · rw [rpow_one]
      · exact le_of_lt this
      · exact div_ne_zero (sub_ne_zero_of_ne (Ne.symm h)) (mul_ne_zero two_ne_zero hα.ne')
      · nlinarith [mul_div_cancel₀ (1 - α) (by positivity : (2 * α) ≠ 0)]
    have h_simp : (ρ.M ^ (1 + 2 * ((1 - α) / (2 * α)))) ^ α =
        ρ.M ^ ((1 + 2 * ((1 - α) / (2 * α))) * α) := by
      rw [← rpow_mul]
      exact le_of_lt this
    field_simp at *
    simp_all only [add_sub_cancel, one_div, rpow_one, DensityOp.tr]

/-- The trace functional is invariant under tensoring with a fixed state.
This follows from multiplicativity (`sandwichedTraceFunctional_mul`) and
the self-trace-functional being 1 (`sandwichedTraceFunctional_self`). -/
theorem sandwichedTraceFunctional_tensor_invariant (hα : 0 < α)
    (ρ σ : MState dA) (τ : MState dB) :
    Q̃_ α(ρ ⊗ᴹ τ‖σ ⊗ᴹ τ) = Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional_mul, sandwichedTraceFunctional_self hα, mul_one]

/-! ## Twirling MState Helpers

Helper lemmas for constructing MStates via the twirling argument. -/

/-- The MState obtained by conjugating a bipartite state by `1_A ⊗ V` where `V` is a unitary
on the `B` system. This is `(1_A ⊗ V) ρ_AB (1_A ⊗ V)†`. -/
def MState.conjTensorUnitary (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    MState (dA × dB) :=
  ρ.uConj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V)

/-- The twirled MState: averaging conjugation by `1_A ⊗ V_i` over all elements of
the twirling set gives `ρ_A ⊗ uniform_B`. We state the HermitianMat-level
equality needed for the joint convexity argument. -/
theorem MState.conjTensorUnitary_M (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    (ρ.conjTensorUnitary V).M = ρ.M.conj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V).val :=
  MState.uConj_M ρ _

/-- The trace functional is invariant under `1_A ⊗ V` conjugation. -/
theorem sandwichedTraceFunctional_conj_tensorUnitary
    (ρ σ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    Q̃_ α(ρ.conjTensorUnitary V‖σ.conjTensorUnitary V) = Q̃_ α(ρ‖σ) := by
  exact sandwichedTraceFunctional_conj_unitary_MState _ ρ σ

section twirling

variable {dA dB : Type*}
variable [Fintype dA] [Fintype dB]
variable [DecidableEq dA] [DecidableEq dB]
open scoped InnerProductSpace RealInnerProductSpace HermitianMat Matrix

omit [DecidableEq dB] in
-- The ((a₁,b₁),(a₂,b₂)) entry of (1⊗V)*M*(1⊗V)†
-- equals (V * block_{a₁,a₂} * V†)_{b₁,b₂}.
lemma conj_kron_one_entry (M : Matrix (dA × dB) (dA × dB) ℂ)
    (V : Matrix dB dB ℂ) (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) V * M *
     (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) V).conjTranspose) (a₁, b₁) (a₂, b₂) =
    (V * (Matrix.of fun b₁' b₂' => M (a₁, b₁') (a₂, b₂')) * V.conjTranspose) b₁ b₂ := by
  norm_num [Matrix.mul_apply, Matrix.adjugate_apply, Matrix.det_apply', Matrix.trace]
  simp [Matrix.one_apply, Finset.sum_ite]
  apply Finset.sum_bij (fun x _ => x.2)
  · simp
  · simp
  · simp
  simp
  intro a b rfl
  left
  apply Finset.sum_bij (fun x _ => x.2)
  · simp
  · simp
  · simp
  simp +contextual

/-
For a Hermitian matrix, the twirling identity at the entry level.
Extracts from hV the entry-level equation.
-/
lemma twirling_hermitian_entry
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (X : HermitianMat dB ℂ) (b₁ b₂ : dB) :
    ∑ i : κ, ((V i).val * X.val * (V i).val.conjTranspose) b₁ b₂ =
    (X.val.trace / (Fintype.card dB : ℂ)) * (Fintype.card κ : ℂ) *
      (if b₁ = b₂ then 1 else 0) := by
  replace hV := congr_arg (fun s => s.val b₁ b₂) (hV X); simp_all [div_eq_inv_mul]
  convert congr_arg (fun x : ℂ => x * Fintype.card κ) hV using 1 <;> ring_nf
  · by_cases h : Fintype.card κ = 0 <;> simp_all [conj]
    · rw [Fintype.card_eq_zero_iff] at h
      simp_all only [Finset.univ_eq_empty, Finset.sum_empty]
    · classical induction (Finset.univ : Finset κ) using Finset.induction
      · simp_all [Matrix.mul_assoc]
      · simp_all [Matrix.mul_assoc]
        rfl
  · simp [Matrix.one_apply, mul_assoc, mul_comm]
    simp [Matrix.trace, trace]
    congr! 2
    exact Finset.sum_congr rfl fun _ _ => by simp [Complex.ext_iff]
/-
Extension of the twirling property from HermitianMat to general matrices.
-/
lemma twirling_general_matrix
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (X : Matrix dB dB ℂ) (b₁ b₂ : dB) :
    ∑ i : κ, ((V i).val * X * (V i).val.conjTranspose) b₁ b₂ =
    (X.trace / (Fintype.card dB : ℂ)) * (Fintype.card κ : ℂ) *
      (if b₁ = b₂ then 1 else 0) := by
  -- Decompose X into Hermitian and anti-Hermitian parts.
  set X_herm : Matrix dB dB ℂ := (1 / 2 : ℂ) • (X + X.conjTranspose)
  set X_anti_herm : Matrix dB dB ℂ := (1 / (2 * Complex.I) : ℂ) • (X - X.conjTranspose)
  have h_decomp : X = X_herm + Complex.I • X_anti_herm := by
    ext i j; norm_num [X_herm, X_anti_herm]; ring_nf
    norm_num; ring
  -- Apply thetwirling property to X_herm and X_anti_herm.
  have h_tw_h : ∑ i : κ, ((V i).val * X_herm * (V i).val.conjTranspose) b₁ b₂ =
      (X_herm.trace / (Fintype.card dB)) * (Fintype.card κ) * (if b₁ = b₂ then 1 else 0) := by
    convert twirling_hermitian_entry κ V hV ⟨X_herm, _⟩ b₁ b₂ using 1
    simp +zetaDelta at *
    ext i j; simp [Matrix.conjTranspose_apply]; ring
  have h_tw_a : ∑ i : κ, ((V i).val * X_anti_herm * (V i).val.conjTranspose) b₁ b₂ =
      (X_anti_herm.trace / (Fintype.card dB)) * (Fintype.card κ) * (if b₁ = b₂ then 1 else 0) := by
    convert twirling_hermitian_entry κ V hV ⟨X_anti_herm, ?_⟩ b₁ b₂ using 1
    ext i j; simp [X_anti_herm, Matrix.conjTranspose_apply]; ring
  rw [h_decomp]
  convert congr_arg₂ (· + ·) h_tw_h (congr_arg (fun x : ℂ => Complex.I * x) h_tw_a) using 1
  <;> simp [mul_add, add_mul, mul_assoc, Finset.mul_sum, Finset.sum_add_distrib]
  ring_nf
  split_ifs <;> ring

/-- The MState obtained by conjugating a bipartite state by `1_A ⊗ V`. -/
def MState.conjTensorUnitary' (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    MState (dA × dB) :=
  ρ.uConj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V)

-- Entry-level form of the conjTensorUnitary.
lemma conjTensorUnitary'_entry (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ)
    (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (ρ.conjTensorUnitary' V).M.val (a₁, b₁) (a₂, b₂) =
    ((V : Matrix dB dB ℂ) * (Matrix.of fun b₁' b₂' => ρ.M.val (a₁, b₁') (a₂, b₂')) *
     (V : Matrix dB dB ℂ).conjTranspose) b₁ b₂ := by
  simp only [MState.conjTensorUnitary', MState.uConj_M, HermitianMat.val_eq_coe,
    HermitianMat.conj_apply_mat]
  apply conj_kron_one_entry

-- The RHS entry: (ρ.traceRight ⊗ᴹ uniform).M at ((a₁,b₁),(a₂,b₂)).
lemma prod_traceRight_uniform_entry [Nonempty dB] (ρ : MState (dA × dB))
    (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (ρ.traceRight ⊗ᴹ MState.uniform).M.val (a₁, b₁) (a₂, b₂) =
    ρ.M.val.traceRight a₁ a₂ * ((Fintype.card dB : ℂ)⁻¹ * if b₁ = b₂ then 1 else 0) := by
  unfold MState.traceRight MState.uniform
  unfold MState.ofClassical
  unfold diagonal
  unfold MState.prod
  unfold kronecker
  simp [Matrix.kroneckerMap_apply]
  rw [Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero]

theorem twirling_average_eq [Nonempty dB]
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (ρ : MState (dA × dB)) :
    ∑ i : κ, ((Fintype.card κ : ℝ)⁻¹ • (ρ.conjTensorUnitary' (V i)).M) =
      (ρ.traceRight ⊗ᴹ MState.uniform).M := by
  -- Apply the twirling hypothesis to each term in the sum.
  have h_sum : ∀ a₁ a₂ : dA, ∀ b₁ b₂ : dB, (∑ i, (1 / (Fintype.card κ : ℂ)) •
      (ρ.conjTensorUnitary' (V i)).M.val (a₁, b₁) (a₂, b₂)) =
      (ρ.M.val.traceRight a₁ a₂) * (1 / (Fintype.card dB : ℂ)) * (if b₁ = b₂ then 1 else 0) := by
    intro a₁ a₂ b₁ b₂
    have h_sum : ∑ i : κ, ((V i : Matrix dB dB ℂ) * (Matrix.of fun b₁' b₂' =>
        ρ.M.val (a₁, b₁') (a₂, b₂')) * (V i : Matrix dB dB ℂ).conjTranspose) b₁ b₂ =
        (ρ.M.val.traceRight a₁ a₂) * (Fintype.card κ : ℂ) * (1 / (Fintype.card dB : ℂ)) *
        (if b₁ = b₂ then 1 else 0) := by
      convert twirling_general_matrix κ V hV
        (Matrix.of fun b₁' b₂' => ρ.M.val (a₁, b₁') (a₂, b₂')) b₁ b₂ using 1
      simp [Matrix.trace]
      ring_nf!
    convert congr_arg (fun x : ℂ => (1 / (Fintype.card κ : ℂ)) * x) h_sum using 1
    · norm_num [conjTensorUnitary'_entry]
      ring_nf
      rw [Finset.mul_sum]
    · norm_num [conjTensorUnitary'_entry]
      by_cases h : Fintype.card κ = 0 <;> simp_all [mul_assoc, mul_comm, mul_left_comm]
      specialize hV 1; norm_num at hV
  convert h_sum using 1
  constructor <;> intro h
  · exact h_sum
  · ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    convert h a₁ a₂ b₁ b₂ using 1
    · classical induction (Finset.univ : Finset κ) using Finset.induction
      · simp_all
      · simp_all
        convert! congr_arg₂ (· + ·) rfl ‹_› using 1
        simp [Algebra.smul_def]
    · convert! prod_traceRight_uniform_entry ρ a₁ a₂ b₁ b₂ using 1
      ring

end twirling

/-! ## Monotonicity Under Partial Trace (α > 1)

The main intermediate result: for `α > 1`, the trace functional `Q̃_α` is monotone
under partial trace:
`Q̃_α(ρ_AB ‖ σ_AB) ≥ Q̃_α(ρ_A ‖ σ_A)`.

The proof uses the twirling argument:
1. By unitary invariance, `Q̃_α(ρ_AB‖σ_AB) = Q̃_α(V_i ρ_AB V_i†‖V_i σ_AB V_i†)` for each `i`.
2. Averaging: `Q̃_α(ρ_AB‖σ_AB) = (1/|κ|) Σ_i Q̃_α(V_i ρ_AB V_i†‖V_i σ_AB V_i†)`.
3. By joint convexity (α > 1): `≥ Q̃_α((1/|κ|) Σ_i V_i ρ_AB V_i†‖(1/|κ|) Σ_i V_i σ_AB V_i†)`.
4. By twirling: `= Q̃_α(ρ_A ⊗ π_B ‖ σ_A ⊗ π_B)`.
5. By tensor invariance: `= Q̃_α(ρ_A ‖ σ_A)`. -/

/-- If `σ.M.ker ≤ ρ.M.ker`, then `(σ.conj B).ker ≤ (ρ.conj B).ker` for any matrix `B`.
This follows from `ker_conj` (which expresses `(A.conj B).ker` as a `comap`) and
`Submodule.comap_mono`. -/
lemma ker_conj_le_of_ker_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A.ker ≤ B.ker)
    (C : Matrix n n ℂ) : (A.conj C).ker ≤ (B.conj C).ker := by
  rw [ker_conj hA, ker_conj hB]
  exact Submodule.comap_mono h

/-- Unitary conjugation preserves the kernel ordering between MStates.
If `σ.M.ker ≤ ρ.M.ker`, then `(σ.conjTensorUnitary V).M.ker ≤ (ρ.conjTensorUnitary V).M.ker`. -/
lemma MState.ker_conjTensorUnitary_le {dA dB : Type*} [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ σ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ)
    (hker : σ.M.ker ≤ ρ.M.ker) :
    (σ.conjTensorUnitary V).M.ker ≤ (ρ.conjTensorUnitary V).M.ker := by
  simp only [MState.conjTensorUnitary_M]
  exact ker_conj_le_of_ker_le σ.nonneg ρ.nonneg hker _

/-- Monotonicity of the trace functional under partial trace for `α > 1`.
Equation (2.8) of the paper (second line). -/
theorem sandwichedTraceFunctional_mono_traceRight [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) (hker : σ.M.ker ≤ ρ.M.ker) :
    Q̃_ α(ρ.traceRight‖σ.traceRight) ≤ Q̃_ α(ρ‖σ) := by
  -- Obtain the twirling unitaries
  obtain ⟨κ, hκ_fin, hκ_ne, V, hV⟩ := exists_twirling_unitaries (dB := dB)
  let : Fintype κ := hκ_fin
  let : Nonempty κ := hκ_ne
  -- By unitary invariance, Q̃_α(ρ‖σ) = Q̃_α(V_i ρ V_i†‖V_i σ V_i†) for each i
  have h_inv (i) : Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) = Q̃_ α(ρ‖σ) :=
    sandwichedTraceFunctional_conj_tensorUnitary ρ σ (V i)
  -- Step 2: Q̃_α(ρ‖σ) = Σ_i (1/|κ|) * Q̃_α(V_i ρ V_i†‖V_i σ V_i†)
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h_avg : Q̃_ α(ρ‖σ) = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ *
      Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) := by
    simp only [h_inv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  -- Step 3: By joint convexity (α > 1)
  have hw_sum : ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard_ne
  set ρ_mix := ρ.traceRight ⊗ᴹ MState.uniform (d := dB)
  set σ_mix := σ.traceRight ⊗ᴹ MState.uniform (d := dB)
  have hρ_mix : ρ_mix.M = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ • (ρ.conjTensorUnitary (V i)).M :=
    (twirling_average_eq κ V hV ρ).symm
  have hσ_mix : σ_mix.M = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ • (σ.conjTensorUnitary (V i)).M :=
    (twirling_average_eq κ V hV σ).symm
  have h_convex := sandwichedTraceFunctional_jointly_convex hα
    (fun (_ : κ) => (Fintype.card κ : ℝ)⁻¹) (by intro; positivity) hw_sum
    (fun i => ρ.conjTensorUnitary (V i)) (fun i => σ.conjTensorUnitary (V i))
    ρ_mix σ_mix hρ_mix hσ_mix
    (fun i => MState.ker_conjTensorUnitary_le ρ σ (V i) hker)
  -- Step 4 + 5: Q̃_α(ρ_A ⊗ π_B‖σ_A ⊗ π_B) = Q̃_α(ρ_A‖σ_A) by tensor invariance
  have h_tensor : Q̃_ α(ρ_mix‖σ_mix) = Q̃_ α(ρ.traceRight‖σ.traceRight) :=
    sandwichedTraceFunctional_tensor_invariant (by linarith) ρ.traceRight σ.traceRight .uniform
  -- Combine
  calc Q̃_ α(ρ.traceRight‖σ.traceRight)
      = Q̃_ α(ρ_mix‖σ_mix) := h_tensor.symm
    _ ≤ ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ *
      Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) := h_convex
    _ = Q̃_ α(ρ‖σ) := h_avg.symm

/-! ## DPI for Sandwiched Rényi Divergence Under Partial Trace -/

/-- The "tensor product" of a vector v with basis vector e_b:
    (v ⊗ e_b)(a, b') = v(a) if b' = b, else 0 -/
private def vecTensorBasis (v : dA → ℂ) (b : dB) : (dA × dB) → ℂ :=
  fun ⟨a, b'⟩ => if b' = b then v a else 0

omit [DecidableEq dA] in
/-- Key identity: ⟨v, (Tr_B A)v⟩ = ∑_b ⟨v⊗e_b, A(v⊗e_b)⟩ -/
private lemma inner_traceRight_eq_sum_inner_vecTensorBasis
    (A : Matrix (dA × dB) (dA × dB) ℂ) (v : dA → ℂ) :
    star v ⬝ᵥ A.traceRight *ᵥ v =
    ∑ b : dB, star (vecTensorBasis v b) ⬝ᵥ A *ᵥ (vecTensorBasis v b) := by
  simp [Matrix.traceRight, Matrix.mulVec, dotProduct]
  simp [vecTensorBasis, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  simp [Finset.mul_sum _ _ _, mul_assoc, mul_comm]
  intro x
  rw [Finset.sum_comm]
  congr
  ext y
  rw [Finset.sum_comm, Finset.sum_comm, Finset.sum_eq_single y]
  · simp
  · simp +contextual
  · simp

omit [DecidableEq dA] in
/-- If A.mulVec(v⊗e_b) = 0 for all b, then (Tr_B A) *ᵥ v = 0 -/
private lemma traceRight_mulVec_zero_of_vecTensorBasis_zero
    (A : Matrix (dA × dB) (dA × dB) ℂ) (v : dA → ℂ)
    (h : ∀ b : dB, A *ᵥ (vecTensorBasis v b) = 0) :
    A.traceRight *ᵥ v = 0 := by
  ext i
  simp_all [funext_iff, Matrix.mulVec, dotProduct]
  convert Finset.sum_congr rfl fun j _ => h j i j using 1
  any_goals exact Finset.univ
  · unfold Matrix.traceRight vecTensorBasis; simp [Finset.sum_ite]
    simp [Finset.sum_mul, Finset.sum_sigma']
    apply Finset.sum_bij (fun x _ => ⟨x.2, x.1, x.2⟩)
    · simp
    · rintro ⟨fst, snd⟩ ha₁ ⟨fst_1, snd_1⟩  ha₂ ⟨rfl, ⟨rfl, right⟩⟩
      rfl
    · intro ⟨fst, ⟨fst_1, snd⟩⟩ a
      simp_all only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, Sigma.mk.injEq,
        heq_eq_eq, Prod.mk.injEq, exists_const, Sigma.exists, exists_eq_left, and_true, exists_eq]
    · simp
  · norm_num

/-- The kernel condition `σ.M.ker ≤ ρ.M.ker` is preserved under partial trace.
This follows because `supp(ρ) ⊆ supp(σ)` implies `supp(Tr_B ρ) ⊆ supp(Tr_B σ)`:
if `v ∈ supp(Tr_B ρ)`, then `⟨v, (Tr_B ρ) v⟩ > 0`, so for some basis vector `e_b`
we have `v ⊗ e_b ∈ supp(ρ) ⊆ supp(σ)`, hence `⟨v, (Tr_B σ) v⟩ ≥ ⟨v ⊗ e_b, σ (v ⊗ e_b)⟩ > 0`. -/
theorem ker_le_traceRight {ρ σ : MState (dA × dB)}
    (hker : σ.M.ker ≤ ρ.M.ker) :
    σ.traceRight.M.ker ≤ ρ.traceRight.M.ker := by
  simp only [MState.traceRight_M]
  intro v hv
  rw [mem_ker_iff_mulVec_zero] at hv ⊢
  have hv' : σ.M.mat.traceRight *ᵥ v.ofLp = 0 := by
    rwa [traceRight_mat] at hv
  have hin : star v.ofLp ⬝ᵥ σ.M.mat.traceRight *ᵥ v.ofLp = 0 := by
    rw [hv']; simp [dotProduct]
  rw [inner_traceRight_eq_sum_inner_vecTensorBasis] at hin
  have hσ_psd := zero_le_iff.mp σ.nonneg
  have h_each_zero : ∀ b : dB,
      star (vecTensorBasis v.ofLp b) ⬝ᵥ σ.M.mat *ᵥ (vecTensorBasis v.ofLp b) = 0 := by
    have h_nonneg : ∀ b, (0 : ℂ) ≤
        star (vecTensorBasis v.ofLp b) ⬝ᵥ σ.M.mat *ᵥ (vecTensorBasis v.ofLp b) :=
      fun b => hσ_psd.dotProduct_mulVec_nonneg _
    intro b
    exact Finset.sum_eq_zero_iff_of_nonneg (fun b _ => h_nonneg b) |>.mp hin b (Finset.mem_univ _)
  have h_σ_zero : ∀ b : dB, σ.M.mat *ᵥ (vecTensorBasis v.ofLp b) = 0 :=
    fun b => (hσ_psd.dotProduct_mulVec_zero_iff _).mp (h_each_zero b)
  have h_ρ_zero : ∀ b : dB, ρ.M.mat *ᵥ (vecTensorBasis v.ofLp b) = 0 := by
    intro b
    have hmem_σ : (WithLp.toLp 2 (vecTensorBasis v.ofLp b) : EuclideanSpace ℂ _) ∈ σ.M.ker := by
      rw [mem_ker_iff_mulVec_zero]; exact h_σ_zero b
    have hmem_ρ := hker hmem_σ
    rwa [mem_ker_iff_mulVec_zero] at hmem_ρ
  exact traceRight_mulVec_zero_of_vecTensorBasis_zero ρ.M.mat v.ofLp h_ρ_zero

/-- The sandwiched Rényi divergence is monotone under partial trace for `α > 1`.
This follows from monotonicity of the trace functional together with the fact that
`D̃_α = log(Q̃_α) / (α - 1)` and both `log` and `1/(α-1)` are order-preserving for α > 1. -/
theorem sandwichedRenyiEntropy_mono_traceRight [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB))
    (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ.traceRight‖σ.traceRight) ≤ D̃_ α(ρ‖σ) := by
  have hα₀ : 0 < α := by linarith
  have hα₁ : α ≠ 1 := hα.ne'
  have hker_tr := ker_le_traceRight hker
  -- Rewrite both sides as log(Q̃) / (α - 1)
  rw [sandwichedRelRentropy_eq_log_traceFunctional hα₀ hα₁ hker,
      sandwichedRelRentropy_eq_log_traceFunctional hα₀ hα₁ hker_tr]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by linarith : 0 < α - 1).le
  exact Real.log_le_log (sandwichedTraceFunctional_pos ρ.traceRight σ.traceRight hker_tr)
    (sandwichedTraceFunctional_mono_traceRight hα ρ σ hker)

/-! ## DPI via Stinespring Dilation -/

/-
The sandwiched Rényi divergence is invariant under unitary conjugation.
-/
theorem sandwichedRenyiEntropy_conj_unitary (hα : 0 < α) (ρ σ : MState d)
    (U : Matrix.unitaryGroup d ℂ) :
    D̃_ α(ρ.uConj U‖σ.uConj U) = D̃_ α(ρ‖σ) := by
  -- Since unitary conjugation preserves the kernel, the condition σ.M.ker ≤ ρ.M.ker is
  -- equivalent to (σ.uConj U).M.ker ≤ (ρ.uConj U).M.ker.
  have h_kernel : σ.M.ker ≤ ρ.M.ker ↔ (σ.uConj U).M.ker ≤ (ρ.uConj U).M.ker := by
    have hk (A : HermitianMat d ℂ) : (A.conj U.val).ker = A.ker.map (U.val.toEuclideanLin) := by
      ext x
      simp [conj]
      constructor <;> intro hx
      all_goals generalize_proofs at *
      · use (U.val.conjTranspose.toEuclideanLin x)
        simp_all [ker, Matrix.toEuclideanLin]
        simp_all [lin, Matrix.toLpLin]
        have h_unitary : (U.val * U.val.conjTranspose) = 1 := by
          exact U.2.2
        generalize_proofs at *; (
        apply_fun (U.val.conjTranspose *ᵥ ·) at hx
        simp_all [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        simp_all [← Matrix.mul_assoc, mul_eq_one_comm.mp h_unitary])
      · obtain ⟨y, hy, rfl⟩ := hx; simp_all [Matrix.toEuclideanLin, Matrix.mul_assoc]
        simp_all [ker, Matrix.toLpLin]
        simp_all [lin]
        simp_all [Matrix.toLpLin, Matrix.mulVec, funext_iff]
        simp_all [Matrix.mul_apply, dotProduct]
        -- Since U is unitary, we have ∑_{x_3} ⟨U_{x_3 x}, U_{x_3 x_1⟩ = δ_{x x_1}.
        have h_unitary : ∀ x x_1, ∑ x_3, (starRingEnd ℂ) (U.val x_3 x) * U.val x_3 x_1 =
            if x = x_1 then 1 else 0 := by
          intro x x_1
          have this := congr_fun (congr_fun U.2.1 x) x_1
          simp_all [Matrix.mul_apply, Matrix.one_apply]
        simp_all [mul_assoc, Finset.sum_mul]
        intro x; rw [Finset.sum_comm]; simp_all [← Finset.mul_sum]
    simp [hk, MState.uConj]
    constructor <;> intro h <;> simp_all [SetLike.le_def]
    · exact fun x hx => ⟨x, h hx, rfl⟩
    · intro x hx
      obtain ⟨y, hy, hy'⟩ := h x hx
      obtain ⟨⟩ : y = x := by
        apply_fun (U.val⁻¹).mulVec at hy'
        simp_all [Matrix.mulVec_mulVec]
        exact PiLp.ext (congrFun hy')
      exact hy
  rw [MState.sandwichedRelRentropy_eq_matrix, MState.sandwichedRelRentropy_eq_matrix,
    dif_pos hα, dif_pos hα]
  by_cases h : σ.M.ker ≤ ρ.M.ker
  swap
  · rw [dif_neg h, dif_neg fun hc ↦ h (h_kernel.mpr hc)]
  rw [dif_pos (h_kernel.mp h), dif_pos h, ENNReal.coe_inj]
  apply NNReal.coe_injective
  show (if α = 1 then ⟪(ρ.uConj U).M, (ρ.uConj U).M.log - (σ.uConj U).M.log⟫
        else (((ρ.uConj U).M.conj
          ((σ.uConj U).M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1))
      = (if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
        else ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1))
  split_ifs with hα₁
  · rw [MState.uConj_M, MState.uConj_M, log_conj_unitary, log_conj_unitary, ← map_sub,
      inner_conj_unitary]
  · exact congrArg (· / (α - 1))
      (congrArg Real.log (sandwichedTraceFunctional_conj_unitary_MState U ρ σ))

/-
The sandwiched Rényi divergence is invariant under tensoring with a fixed pure state:
`D̃_α(ρ ⊗ |ψ⟩⟨ψ| ‖ σ ⊗ |ψ⟩⟨ψ|) = D̃_α(ρ ‖ σ)`.
-/
theorem sandwichedRenyiEntropy_tensor_pure (hα : 0 < α) (ρ σ : MState d₁) (ψ : Ket d₂) :
    D̃_ α(ρ ⊗ᴹ MState.pure ψ‖σ ⊗ᴹ MState.pure ψ) = D̃_ α(ρ‖σ) := by
  simp [hα]

/-- The sandwiched Rényi divergence is invariant under SWAP. -/
@[simp]
theorem sandwichedRenyiEntropy_SWAP (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.SWAP‖σ.SWAP) = D̃_ α(ρ‖σ) := by
  exact sandwichedRelRentropy_relabel ρ σ _

/-
Monotonicity of the sandwiched Rényi divergence under traceRight for `α > 1`,
without the kernel condition. When the kernel condition fails, `D̃_α = ⊤` and
the inequality is trivial.
-/
theorem sandwichedRenyiEntropy_mono_traceRight' [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.traceRight‖σ.traceRight) ≤ D̃_ α(ρ‖σ) := by
  by_cases hker : σ.M.ker ≤ ρ.M.ker
  · exact sandwichedRenyiEntropy_mono_traceRight hα ρ σ hker
  · rw [MState.sandwichedRelRentropy_eq_matrix α ρ σ, dif_pos (by linarith : (0 : ℝ) < α),
      dif_neg hker]
    exact le_top

/-- Monotonicity of the sandwiched Rényi divergence under `traceLeft` for `α > 1`.
Follows from `sandwichedRenyiEntropy_mono_traceRight'` + SWAP invariance. -/
theorem sandwichedRenyiEntropy_mono_traceLeft [Nonempty dA]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.traceLeft‖σ.traceLeft) ≤ D̃_ α(ρ‖σ) := by
  -- traceLeft = SWAP.traceRight, and SWAP preserves the SRD
  rw [← MState.traceRight_SWAP, ← MState.traceRight_SWAP]
  calc D̃_ α(ρ.SWAP.traceRight‖σ.SWAP.traceRight)
      ≤ D̃_ α(ρ.SWAP‖σ.SWAP) :=
        sandwichedRenyiEntropy_mono_traceRight' hα ρ.SWAP σ.SWAP
    _ = D̃_ α(ρ‖σ) := sandwichedRenyiEntropy_SWAP ρ σ

/-- Helper: The Stinespring preparation `CPTPOp.prepDefault` equals tensoring with a fixed pure
state.
TODO: PULLOUT to a more reasonable place. -/
theorem prepDefault_eq_tensor_pure [Inhabited d₂] (ρ : MState d₁) :
    (CPTPOp.prepDefault : CPTPMap d₁ (d₁ × d₂ × d₂)) ρ =
      ρ ⊗ᴹ MState.pure (Ket.basis (default : d₂ × d₂)) := by
  apply DensityOp.ext_m
  rw [CPTPOp.mat_coe_eq_apply_mat, MState.prod_m]
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  exact CPTPOp.prep_append_map_entry ρ.m a₁ b₁ a₂ b₂

/-- The Data Processing Inequality for the Sandwiched Rényi relative entropy (α > 1).
Every CPTP map `Φ` satisfies `D̃_α(Φρ‖Φσ) ≤ D̃_α(ρ‖σ)`.

The proof uses the Stinespring representation (see `CPTPOp.exists_purify`):
every CPTP map can be written as ancilla preparation + unitary conjugation + partial trace.
Since the sandwiched Rényi divergence is invariant under the first two operations
(by additivity and relabel invariance) and monotone under partial trace
(by `sandwichedRenyiEntropy_mono_traceRight`), the DPI follows. -/
theorem sandwichedRenyiEntropy_DPI_gt_one (hα : 1 < α) (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  have _ : Nonempty d₁ := MState.nonempty ρ
  have _ : Nonempty d₂ := MState.nonempty (Φ ρ)
  have : Inhabited d₂ := Classical.inhabited_of_nonempty ‹_›
  let ψ₀ : Ket (d₂ × d₂) := Ket.basis default
  let τ := MState.pure ψ₀
  obtain ⟨U, hU⟩ := Φ.purify_IsUnitary
  let prep : CPTPMap d₁ (d₁ × d₂ × d₂) := CPTPOp.prepDefault
  calc D̃_ α(Φ ρ‖Φ σ)
    _ = D̃_ α(MState.traceLeft (MState.traceLeft (Φ.purify (prep ρ)))‖
            MState.traceLeft (MState.traceLeft (Φ.purify (prep σ)))) := by
        have h_trace (ξ) : Φ ξ =
            MState.traceLeft (MState.traceLeft (Φ.purify (prep ξ))) := by
          show Φ ξ = MState.traceLeft (MState.traceLeft
            (Φ.purify (CPTPOp.prepDefault (dIn := d₁) (dOut := d₂) ξ)))
          conv_lhs => rw [Φ.purify_trace]
          simp only [CPTPOp.compose_eq, CPTPOp.traceLeft_eq_MState_traceLeft]
        rw [h_trace ρ, h_trace σ]
    _ = D̃_ α(MState.traceLeft (MState.traceLeft (MState.uConj (ρ ⊗ᴹ τ) U))‖
             MState.traceLeft (MState.traceLeft (MState.uConj (σ ⊗ᴹ τ) U))) := by
        have h_app (ξ) : Φ.purify ξ = MState.uConj ξ U :=
          (congr($hU ξ)).trans (CPTPOp.ofUnitary_eq_conj U ξ)
        show D̃_ α(MState.traceLeft (MState.traceLeft
              (Φ.purify (CPTPOp.prepDefault (dIn := d₁) (dOut := d₂) ρ)))‖
            MState.traceLeft (MState.traceLeft
              (Φ.purify (CPTPOp.prepDefault (dIn := d₁) (dOut := d₂) σ)))) = _
        rw [prepDefault_eq_tensor_pure ρ, prepDefault_eq_tensor_pure σ, h_app, h_app]
    _ ≤ D̃_ α(MState.traceLeft (MState.uConj (ρ ⊗ᴹ τ) U)‖
             MState.traceLeft (MState.uConj (σ ⊗ᴹ τ) U)) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ ≤ D̃_ α(MState.uConj (ρ ⊗ᴹ τ) U‖MState.uConj (σ ⊗ᴹ τ) U) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ = D̃_ α(ρ ⊗ᴹ τ‖σ ⊗ᴹ τ) :=
        sandwichedRenyiEntropy_conj_unitary (by positivity) _ _ _
    _ = D̃_ α(ρ‖σ) :=
        sandwichedRenyiEntropy_tensor_pure (by positivity) ρ σ ψ₀

/-
The DPI for the sandwiched Rényi divergence at α = 1 (the quantum relative entropy).
This follows from the α > 1 case by taking a limit, using the continuity of
`α ↦ D̃_α(ρ‖σ)` established in `sandwichedRelRentropy.continuousOn`.
-/
theorem sandwichedRenyiEntropy_DPI_eq_one (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ 1(Φ ρ‖Φ σ) ≤ D̃_ 1(ρ‖σ) := by
  -- Since α → D_α(ρ‖σ) is continuous on (0, ∞), we can take the limit as α → 1.
  have h_cont :
      Filter.Tendsto (fun α : ℝ => D̃_ α(Φ ρ‖Φ σ)) (𝓝[>] 1) (𝓝 (D̃_ 1(Φ ρ‖Φ σ))) ∧
      Filter.Tendsto (fun α : ℝ => D̃_ α(ρ‖σ)) (𝓝[>] 1) (𝓝 (D̃_ 1(ρ‖σ))) := by
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds (sandwichedRelRentropy.continuousOn (Φ ρ) (Φ σ) |>
        ContinuousOn.continuousAt <| Ioi_mem_nhds zero_lt_one)
    · exact tendsto_nhdsWithin_of_tendsto_nhds (sandwichedRelRentropy.continuousOn ρ σ |>
        ContinuousOn.continuousAt <| Ioi_mem_nhds zero_lt_one)
  exact le_of_tendsto_of_tendsto h_cont.1 h_cont.2 <| Filter.eventually_of_mem
    self_mem_nhdsWithin fun x hx => sandwichedRenyiEntropy_DPI_gt_one hx ρ σ Φ

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved following the approach of Frank–Lieb and Leditzky–Rouzé–Datta. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  rcases hα.lt_or_eq with hα | rfl
  · exact sandwichedRenyiEntropy_DPI_gt_one hα ρ σ Φ
  · exact sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-! ## Joint Convexity of the Relative Entropy

Joint convexity of the (Umegaki) quantum relative entropy is derived from joint convexity
of the trace functional `Q̃_α` (`sandwichedTraceFunctional_jointly_convex`) by letting
`α → 1⁺`, in the same way that `sandwichedRenyiEntropy_DPI_eq_one` follows from the
`α > 1` case.

For `α > 1` and states with compatible kernels, `log x ≤ x - 1` gives
`D̃_α(ρ‖σ) = log (Q̃_α(ρ‖σ)) / (α - 1) ≤ (Q̃_α(ρ‖σ) - 1) / (α - 1)`, and the difference
quotient on the right is jointly convex in `(ρ, σ)` because `Q̃_α` is. As `α → 1⁺`, the
left-hand side tends to `𝐃(ρ‖σ)` (by `sandwichedRelRentropy.continuousOn`), and the
difference quotient tends to `𝐃(ρ‖σ)` as well (since `Q̃_α = exp ((α - 1) D̃_α)` and
`exp x ≤ 1 + x + x²` for `|x| ≤ 1`), so the convex combination passes to the limit.
-/

/-- As `α → 1⁺`, the sandwiched Rényi relative entropy `D̃_α(ρ‖σ)` tends to the relative
entropy `𝐃(ρ‖σ) = D̃_1(ρ‖σ)`, by continuity of `α ↦ D̃_α` on `(0, ∞)`. -/
theorem sandwichedRelRentropy_tendsto_qRelativeEnt (ρ σ : MState d) :
    Filter.Tendsto (fun α : ℝ => D̃_ α(ρ‖σ)) (𝓝[>] 1) (𝓝 𝐃(ρ‖σ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds
    ((sandwichedRelRentropy.continuousOn ρ σ).continuousAt (Ioi_mem_nhds zero_lt_one))

/-- As `α → 1⁺`, the difference quotient `(Q̃_α(ρ‖σ) - 1) / (α - 1)` is eventually bounded
above by a function tending to `𝐃(ρ‖σ).toReal`. This is the key estimate for transferring
joint convexity of the trace functional `Q̃_α` to the relative entropy `𝐃` in
`qRelativeEnt_joint_convexity`. -/
private lemma sandwichedTraceFunctional_sub_one_div_eventually_le
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    ∃ u : ℝ → ℝ, Filter.Tendsto u (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) ∧
      ∀ᶠ α in 𝓝[>] 1, (Q̃_ α(ρ‖σ) - 1) / (α - 1) ≤ u α := by
  set r : ℝ → ℝ := fun α => Real.log (Q̃_ α(ρ‖σ)) / (α - 1) with hr_def
  have h_ne : 𝐃(ρ‖σ) ≠ ⊤ := qRelativeEnt_ne_top_iff.mpr hker
  have h_r_nonneg : ∀ α : ℝ, 1 < α → 0 ≤ r α := by
    intro α hα
    have h := sandwichedRelRentropy_nonneg (ρ := ρ) (σ := σ) (α := α) (by linarith) hker
    rw [if_neg hα.ne'] at h
    simpa [hr_def, sandwichedTraceFunctional] using h
  have h_eq : ∀ α : ℝ, 1 < α → D̃_ α(ρ‖σ) = ENNReal.ofReal (r α) := fun α hα =>
    sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker
  -- `r` tends to `𝐃(ρ‖σ).toReal`, by continuity of `α ↦ D̃_α(ρ‖σ)` at `α = 1`.
  have h_r_tendsto : Filter.Tendsto r (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) := by
    refine Filter.Tendsto.congr' ?_ ((ENNReal.tendsto_toReal h_ne).comp
      (sandwichedRelRentropy_tendsto_qRelativeEnt ρ σ))
    filter_upwards [self_mem_nhdsWithin] with α (hα : 1 < α)
    simp only [Function.comp_apply, h_eq α hα, ENNReal.toReal_ofReal (h_r_nonneg α hα)]
  have h_eps : Filter.Tendsto (fun α : ℝ => (α - 1) * r α) (𝓝[>] 1) (𝓝 0) := by
    have h₁ : Filter.Tendsto (fun α : ℝ => α - 1) (𝓝[>] 1) (𝓝 0) := by
      simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using h₁.mul h_r_tendsto
  refine ⟨fun α => r α + ((α - 1) * r α) * r α, ?_, ?_⟩
  · simpa using h_r_tendsto.add (h_eps.mul h_r_tendsto)
  · -- Eventually `|(α - 1) * r α| ≤ 1`, so `exp x - 1 ≤ x + x²` applies with
    -- `x = (α - 1) * r α = log (Q̃_α)`.
    have h_small : ∀ᶠ α in 𝓝[>] 1, |(α - 1) * r α| ≤ 1 :=
      h_eps.eventually (Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 one_pos)
        fun x hx => by simpa [Real.dist_0_eq_abs] using hx)
    filter_upwards [self_mem_nhdsWithin, h_small] with α (hα : 1 < α) h_abs
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(ρ‖σ) := sandwichedTraceFunctional_pos ρ σ hker
    have h_log : Real.log (Q̃_ α(ρ‖σ)) = (α - 1) * r α := by
      simp only [hr_def]
      field_simp
    have h_exp : Q̃_ α(ρ‖σ) = Real.exp ((α - 1) * r α) := by
      rw [← h_log, Real.exp_log hQ_pos]
    have h_bound : Q̃_ α(ρ‖σ) - 1 ≤ (α - 1) * r α + ((α - 1) * r α) ^ 2 := by
      have h₂ := Real.abs_exp_sub_one_sub_id_le h_abs
      have h₃ := le_abs_self (Real.exp ((α - 1) * r α) - 1 - (α - 1) * r α)
      rw [h_exp]
      linarith
    calc (Q̃_ α(ρ‖σ) - 1) / (α - 1)
        ≤ ((α - 1) * r α + ((α - 1) * r α) ^ 2) / (α - 1) :=
          div_le_div_of_nonneg_right h_bound hα1.le
      _ = r α + ((α - 1) * r α) * r α := by
          field_simp

/-- A binary `Mixable` mixture of states, written as a weighted sum of matrices over
`Fin 2` — the form consumed by `sandwichedTraceFunctional_jointly_convex` and
`HermitianMat.ker_weighted_sum_le`. -/
private lemma mix_M_eq_weighted_sum (p : Prob) (τ₁ τ₂ : MState d) :
    (p [τ₁ ↔ τ₂]).M = ∑ i, ![(p : ℝ), 1 - (p : ℝ)] i • (![τ₁, τ₂] i).M := by
  simp [Fin.sum_univ_two]

/-- A binary mixture preserves the support condition (kernel inclusion) of its
components. -/
private lemma ker_mix_le (p : Prob) {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := by
  rw [mix_M_eq_weighted_sum, mix_M_eq_weighted_sum]
  exact HermitianMat.ker_weighted_sum_le _
    (by intro i; fin_cases i <;> simp) _ _
    (fun i => (![ρ₁, ρ₂] i).nonneg) (fun i => (![σ₁, σ₂] i).nonneg)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Binary case of the joint convexity of the trace functional `Q̃_α` for `α > 1`
(`sandwichedTraceFunctional_jointly_convex`), stated for a `Mixable` mixture. -/
private lemma sandwichedTraceFunctional_mix_le (hα : 1 < α) (p : Prob)
    {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      (p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂) := by
  simpa [Fin.sum_univ_two] using sandwichedTraceFunctional_jointly_convex hα
    ![(p : ℝ), 1 - (p : ℝ)]
    (by intro i; fin_cases i <;> simp)
    (by simp [Fin.sum_univ_two]) ![ρ₁, ρ₂] ![σ₁, σ₂]
    (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
    (mix_M_eq_weighted_sum p ρ₁ ρ₂) (mix_M_eq_weighted_sum p σ₁ σ₂)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Joint convexity of the quantum relative entropy.

This is stated using `Mixable`, rather than `ConvexOn`, because `MState d`
is not an `AddCommMonoid`.
-/
theorem qRelativeEnt_joint_convexity :
    ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
      𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  intro ρ₁ ρ₂ σ₁ σ₂ p
  -- Degenerate mixing weights: the mixture is just one of the two pairs.
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  have hp0' : (0 : ℝ) < p := Prob.zero_lt_coe hp0
  have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne Prob.coe_le_one fun h => hp1 (Subtype.ext h)
  -- If either relative entropy on the right is `⊤`, the bound is trivial.
  by_cases hker₁ : σ₁.M.ker ≤ ρ₁.M.ker
  swap
  · have h_ne : ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, Prob.ofNNReal_toNNReal, ENNReal.ofReal_eq_zero]
      exact not_le.mpr hp0'
    rw [qRelativeEnt_eq_top_iff.mpr hker₁, ENNReal.mul_top h_ne, top_add]
    exact le_top
  by_cases hker₂ : σ₂.M.ker ≤ ρ₂.M.ker
  swap
  · have h_ne : (1 : ENNReal) - ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, tsub_eq_zero_iff_le, Prob.ofNNReal_toNNReal, not_le,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp0'.le |>.mpr hp1'
    rw [qRelativeEnt_eq_top_iff.mpr hker₂, ENNReal.mul_top h_ne, add_top]
    exact le_top
  -- Main case: `0 < p < 1` and both kernel conditions hold, so both `𝐃`s are finite.
  obtain ⟨u₁, hu₁, hb₁⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₁ σ₁ hker₁
  obtain ⟨u₂, hu₂, hb₂⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₂ σ₂ hker₂
  have hker_mix : (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := ker_mix_le p hker₁ hker₂
  -- As `α → 1⁺`, `D̃_α` of the mixture tends to `𝐃` of the mixture...
  have h_lhs := sandwichedRelRentropy_tendsto_qRelativeEnt (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
  -- ...and the convex combination of the majorants tends to the convex combination of the `𝐃`s.
  have h_rhs : Filter.Tendsto
      (fun α : ℝ => ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α)) (𝓝[>] 1)
      (𝓝 (p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂))) := by
    -- The limit is the `ENNReal`-valued convex combination of the two finite `𝐃`s,
    -- rewritten via `ofReal` of the corresponding real combination.
    have h_id : ENNReal.ofReal ((p : ℝ) * (𝐃(ρ₁‖σ₁)).toReal
        + (1 - (p : ℝ)) * (𝐃(ρ₂‖σ₂)).toReal) = p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
      have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by simp
      rw [ENNReal.ofReal_add (mul_nonneg p.zero_le_coe ENNReal.toReal_nonneg)
          (mul_nonneg h1p ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul p.zero_le_coe, ENNReal.ofReal_mul h1p,
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₁),
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₂),
        ENNReal.ofReal_sub 1 p.zero_le_coe, ENNReal.ofReal_one]
      simp only [← Prob.ofNNReal_toNNReal]
    rw [← h_id]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hu₁.const_mul (p : ℝ)).add (hu₂.const_mul (1 - (p : ℝ))))
  -- The pointwise bound for `α > 1`, from joint convexity of `Q̃_α` and `log x ≤ x - 1`.
  have h_ev : ∀ᶠ α in 𝓝[>] 1, D̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α) := by
    filter_upwards [self_mem_nhdsWithin, hb₁, hb₂] with α (hα : 1 < α) h₁ h₂
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) :=
      sandwichedTraceFunctional_pos _ _ hker_mix
    rw [sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker_mix]
    apply ENNReal.ofReal_le_ofReal
    calc Real.log (Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂])) / (α - 1)
        ≤ (((p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂)) - 1) / (α - 1) :=
          div_le_div_of_nonneg_right ((Real.log_le_sub_one_of_pos hQ_pos).trans
            (sub_le_sub_right (sandwichedTraceFunctional_mix_le hα p hker₁ hker₂) 1)) hα1.le
      _ = (p : ℝ) * ((Q̃_ α(ρ₁‖σ₁) - 1) / (α - 1)) +
          (1 - (p : ℝ)) * ((Q̃_ α(ρ₂‖σ₂) - 1) / (α - 1)) := by
          field_simp
          ring
      _ ≤ (p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ hp0'.le)
            (mul_le_mul_of_nonneg_left h₂ (by linarith))
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ev

section BasisFree

/-! ## Basis-free forms

The data processing inequality above is stated for states indexed by a type. This is its
counterpart for states on an abstract finite-dimensional Hilbert space, obtained by picking an
arbitrary preferred basis on each side (`StdBasis.some`) and transporting; the relative entropies
are insensitive to that choice, so nothing is lost. -/

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

namespace DensityOp

/-- The Data Processing Inequality for the sandwiched Rényi relative entropy. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : DensityOp E) (Φ : CPTPOp E F) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  let := StdBasis.some ℂ E
  let := StdBasis.some ℂ F
  obtain ⟨μ, rfl⟩ := ρ.exists_transport_eq
  obtain ⟨ν, rfl⟩ := σ.exists_transport_eq
  have h := _root_.sandwichedRenyiEntropy_DPI hα μ ν
    (Φ.transport (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ F)))
  rw [CPTPOp.transport_apply, CPTPOp.transport_apply, sandwichedRelRentropy_transport] at h
  exact h.trans_eq (sandwichedRelRentropy_transport (F := E) α μ ν).symm

/-- The Data Processing Inequality for the quantum relative entropy. -/
theorem qRelativeEnt_DPI (ρ σ : DensityOp E) (Φ : CPTPOp E F) : 𝐃(Φ ρ‖Φ σ) ≤ 𝐃(ρ‖σ) :=
  sandwichedRenyiEntropy_DPI le_rfl ρ σ Φ

end DensityOp

end BasisFree
