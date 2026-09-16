/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Inner
public import QuantumInfo.ForMathlib.HermitianMat.NonSingular
public import QuantumInfo.ForMathlib.Isometry

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Topology.TietzeExtension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Matrix operations on HermitianMats with the CFC -/

@[expose] public section
namespace HermitianMat

noncomputable section CFC

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X]
variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (q r : ℝ)

/- Adding this to the `CStarAlgebra` aesop set allows `cfc_tac` to use it. -/
omit [Fintype d] [DecidableEq d] in
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem isSelfAdjoint : IsSelfAdjoint A.mat := by
  exact A.H

/- Adding this to `fun_prop` allows `cfc_cont_tac` to use it. -/
@[fun_prop]
theorem continuousOn_finite {α β : Type*} (f : α → β) (S : Set α)
    [TopologicalSpace α] [TopologicalSpace β] [T1Space α] [Finite S] : ContinuousOn f S := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_of_discreteTopology

@[simp]
theorem conjTranspose_cfc : (cfc f A.mat).conjTranspose = cfc f A.mat := by
  exact cfc_predicate f A.mat

protected def cfc : HermitianMat d 𝕜 :=
  ⟨cfc f A.mat, cfc_predicate _ _⟩

theorem cfc_eq : A.cfc f = ⟨cfc f A.mat, cfc_predicate f A.mat⟩ := by
  rfl

@[simp]
theorem mat_cfc : (A.cfc f).mat = _root_.cfc f A.mat := by
  rfl

section congr

variable {f g A}

theorem cfc_eq_cfc_iff_eqOn (f g : ℝ → ℝ) :
    A.cfc f = A.cfc g ↔ Set.EqOn f g (spectrum ℝ A.mat) := by
  rw [HermitianMat.ext_iff, mat_cfc, mat_cfc]
  exact _root_.cfc_eq_cfc_iff_eqOn A.H

nonrec theorem cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.mat)) :
    A.cfc f = A.cfc g := by
  ext1
  exact cfc_congr hfg

/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_nonneg (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  open MatrixOrder in
  exact spectrum_nonneg_of_nonneg (a := A.mat) hA

open ComplexOrder in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.mat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

end congr
section commute
variable {A B : HermitianMat d 𝕜}

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.cfc_left (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat B.mat := by
  exact hAB.cfc_real f

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.cfc_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.cfc f).mat :=
  (hAB.symm.cfc_left f).symm

theorem cfc_commute (f g : ℝ → ℝ) (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat (B.cfc g).mat := by
  exact (hAB.cfc_right g).cfc_left f

@[aesop safe apply (rule_sets := [Commutes])]
theorem cfc_self_commute (A : HermitianMat d 𝕜) (f g : ℝ → ℝ) :
    Commute (A.cfc f).mat (A.cfc g).mat := by
  commutes

end commute

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : (A.reindex e).cfc f = (A.cfc f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [mat_cfc, mat_reindex]
  exact Matrix.cfc_reindex f e

theorem spectrum_cfc_eq_image (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    spectrum ℝ (A.cfc f).mat = f '' (spectrum ℝ A.mat) := by
  exact cfc_map_spectrum f A.mat

set_option backward.isDefEq.respectTransparency false in
/--
Spectral decomposition of `A.cfc f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj : (A.cfc f).mat =
    ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  rw [A.mat_cfc, A.H.cfc_eq, Matrix.IsHermitian.cfc]
  have h : ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix d d 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 := by
    ext i j ; by_cases hij : i = j <;> simp [ hij ];
    · simp [ Matrix.sum_apply, Matrix.single ];
      simp [ Algebra.smul_def ];
    · rw [Finset.sum_apply, Finset.sum_apply]
      simp_all
  rw [h]
  simp [Matrix.single, Matrix.mul_assoc]
  congr! 1
  ext j k
  simp [Matrix.mul_apply,Finset.mul_sum, Finset.smul_sum, smul_ite, smul_zero]

--Ensure we get this instance:
/-- info: locallyCompact_of_proper -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency false in
#synth LocallyCompactSpace (HermitianMat d 𝕜)

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec theorem cfc_id : A.cfc id = A := by
  simpa [HermitianMat.ext_iff] using cfc_id ℝ A.mat

@[simp]
nonrec theorem cfc_id' : A.cfc (·) = A :=
  cfc_id A

nonrec theorem cfc_add : A.cfc (f + g) = A.cfc f + A.cfc g := by
  ext1; exact cfc_add ..

theorem cfc_add_apply : A.cfc (fun x ↦ f x + g x) = A.cfc f + A.cfc g :=
  cfc_add A f g

nonrec theorem cfc_sub : A.cfc (f - g) = A.cfc f - A.cfc g := by
  ext1; exact cfc_sub ..

theorem cfc_sub_apply : A.cfc (fun x ↦ f x - g x) = A.cfc f - A.cfc g :=
  cfc_sub A f g

nonrec theorem cfc_neg : A.cfc (-f) = -A.cfc f := by
  ext1; exact cfc_neg ..

theorem cfc_neg_apply : A.cfc (fun x ↦ -f x) = -A.cfc f :=
  cfc_neg A f

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem mat_cfc_mul : (A.cfc (f * g)).mat = A.cfc f * A.cfc g := by
  simp only [mat_cfc]
  exact cfc_mul ..

theorem mat_cfc_mul_apply : (A.cfc (fun x ↦ f x * g x)).mat = A.cfc f * A.cfc g := by
  exact mat_cfc_mul ..

nonrec theorem cfc_comp : A.cfc (g ∘ f) = (A.cfc f).cfc g := by
  ext1; exact cfc_comp ..

theorem cfc_comp_apply : A.cfc (fun x ↦ g (f x)) = (A.cfc f).cfc g :=
  cfc_comp A f g

nonrec theorem cfc_conj : (A.cfc f).conj (A.cfc g) = A.cfc (f * g^2) := by
  ext1
  simp only [conj_apply, mat_cfc, mat_mk, conjTranspose_cfc]
  rw [← cfc_mul, ← cfc_mul, Pi.mul_def, Pi.pow_def]
  grind only

@[simp]
theorem cfc_diagonal (g : d → ℝ) : (diagonal 𝕜 g).cfc f = diagonal 𝕜 (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

theorem cfc_conj_unitary (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).cfc f = (A.cfc f).conj U := by
  ext1
  exact Matrix.cfc_conj_unitary f U

@[simp]
nonrec theorem cfc_const : (A.cfc (fun _ ↦ r)) = r • 1 := by
  ext1
  simp only [mat_cfc, mat_smul, mat_one]
  rw [cfc_const r A.mat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec theorem cfc_const_mul_id : A.cfc (fun x ↦ r * x) = r • A := by
  ext1
  rw [mat_cfc, mat_smul, cfc_const_mul_id r A.mat]

@[simp]
nonrec theorem cfc_const_mul : A.cfc (fun x ↦ r * f x) = r • A.cfc f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec theorem cfc_apply_zero : (0 : HermitianMat d 𝕜).cfc f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec theorem cfc_apply_one : (1 : HermitianMat d 𝕜).cfc f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

theorem cfc_pow {n : ℕ} : A.cfc (· ^ n) = A ^ n := by
  ext1
  induction n
  · simp
  · simp_rw [pow_succ, mat_pow, mat_cfc_mul_apply, pow_succ, cfc_id']
    congr

set_option backward.isDefEq.respectTransparency false in
theorem cfc_nonneg_iff : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  open MatrixOrder in
  rw [cfc_eq, ← Subtype.coe_le_coe, ZeroMemClass.coe_zero]
  rw [_root_.cfc_nonneg_iff f A.mat, A.H.spectrum_real_eq_range_eigenvalues]
  grind

open ComplexOrder in
theorem cfc_posDef : (A.cfc f).mat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  simpa using h (e.symm i)

variable {A f} in
/-- If a rael function preserves nonnegativity, the CFC preserves PSDness. -/
theorem cfc_nonneg_of_nonneg (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [cfc_nonneg_iff]
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact fun i ↦ hf _ (hA i)

set_option backward.isDefEq.respectTransparency false in
theorem cfc_nonSingular (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) : NonSingular (A.cfc f) := by
  rw [nonSingular_iff_eigenvalue_ne_zero]
  obtain ⟨e, he⟩ := cfc_eigenvalues f A
  simpa [he] using fun i ↦ hf (e i)


set_option backward.isDefEq.respectTransparency false in
theorem trace_mul_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (A.mat * (A.cfc f).mat).trace = ∑ i, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  conv_lhs => rw [A.eq_conj_diagonal]
  rw [cfc_conj_unitary]
  simp [conj, Matrix.mul_assoc, A.H.eigenvectorUnitary.val.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

theorem norm_eq_sum_eigenvalues_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = ∑ i, (A.H.eigenvalues i)^2 := by
  rw [← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow, norm_eq_trace_sq]
  conv_lhs => change (A ^ 2).mat.trace; rw [(A ^ 2).H.trace_eq_sum_eigenvalues]
  simp only [map_sum, map_pow]
  rw [← cfc_pow]
  obtain ⟨e, he⟩ := cfc_eigenvalues (· ^ 2) A
  simp only [he, Function.comp_apply, map_pow]
  exact e.sum_comp (fun x ↦ (algebraMap ℝ 𝕜) (A.H.eigenvalues x) ^ 2)

variable {A} in
theorem lt_smul_of_norm_lt {r : ℝ} (h : ‖A‖ ≤ r) : A ≤ r • 1 := by
  rcases lt_or_ge r 0 with _ | hr
  · have := norm_nonneg A
    order
  rcases isEmpty_or_nonempty d
  · exact le_of_subsingleton
  have h' := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [norm_eq_sum_eigenvalues_sq] at h'
  nth_rw 1 [← cfc_const A, ← cfc_id A]
  rw [le_iff, ← cfc_sub]
  rw [(HermitianMat.H _).posSemidef_iff_eigenvalues_nonneg]
  intro i; rw [Pi.zero_apply]
  obtain ⟨e, he⟩ := cfc_eigenvalues ((fun x ↦ r) - id) A
  rw [he]; clear he
  dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [sub_nonneg]
  apply le_of_sq_le_sq _ hr
  refine le_trans ?_ h'
  exact Finset.single_le_sum (f := fun x ↦ (A.H.eigenvalues x)^2) (by intros; positivity) (Finset.mem_univ _)

theorem ball_subset_Icc : Metric.ball A r ⊆ Set.Icc (A - r • 1) (A + r • 1) := by
  intro x
  simp only [Metric.mem_ball, dist_eq_norm, Set.mem_Icc, tsub_le_iff_right]
  intro h
  constructor
  · rw [← norm_neg] at h
    grw [← lt_smul_of_norm_lt h.le]
    simp
  · grw [← lt_smul_of_norm_lt h.le]
    simp

theorem spectrum_subset_of_mem_Icc (A B : HermitianMat d 𝕜) :
    ∃ a b, ∀ x, A ≤ x ∧ x ≤ B → spectrum ℝ x.mat ⊆ Set.Icc a b := by
  use ⨅ i, A.H.eigenvalues i, ⨆ i, B.H.eigenvalues i
  rintro x ⟨hl, hr⟩
  exact A.H.spectrum_subset_of_mem_Icc B.H hl hr

--TODO: Generalize this to real matrices (really, RCLike) too. The theorem below
-- gives it for complex matrices only.
-- @[fun_prop]
-- protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
--     Continuous (cfc · f : HermitianMat d 𝕜 → HermitianMat d 𝕜) := by
--   rcases isEmpty_or_nonempty d
--   · sorry
--   rw [Metric.continuous_iff] at hf ⊢
--   intro x ε hε
--   have _ : Nonempty (spectrum ℝ x.toMat) := by
--     sorry
--   replace hf b := hf b ε hε
--   choose fc hfc₀ hfc using hf
--   let δ : ℝ := ⨆ e : spectrum ℝ x.toMat, fc e
--   refine ⟨δ, ?_, ?_⟩
--   · --This whole block should just be `positivity`. TODO fix.
--     dsimp [δ]
--     --Why doesn't just `classical` make this happen automatically?
--     replace h_fin := Fintype.ofFinite (spectrum ℝ x.toMat)
--     rw [← Finset.sup'_univ_eq_ciSup, gt_iff_lt, Finset.lt_sup'_iff]
--     simp [hfc₀]
--   intro a ha
--   simp only [dist, AddSubgroupClass.subtype_apply, val_eq_coe, cfc_toMat] at ha ⊢
--   sorry

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (HermitianMat.cfc · f : HermitianMat d ℂ → HermitianMat d ℂ) := by
  unfold HermitianMat.cfc
  suffices Continuous (fun A : HermitianMat d ℂ ↦ _root_.cfc f A.mat) by
    fun_prop
  have h_compact_cover := LocallyCompactSpace.local_compact_nhds (X := HermitianMat d ℂ)
  apply continuous_of_continuousOn_iUnion_of_isOpen (ι := HermitianMat d ℂ × {x : ℝ // 0 < x})
    (s := fun ab ↦ Metric.ball ab.1 ab.2)
  · rintro ⟨A, r, hr⟩
    apply ContinuousOn.mono ?_ (ball_subset_Icc A r)
    obtain ⟨a, b, hab⟩ := spectrum_subset_of_mem_Icc (A - r • 1) (A + r • 1)
    open ComplexOrder in
    refine ContinuousOn.cfc (s := fun _ ↦ Set.Icc a b) (t := Set.Icc (A - r • 1) (A + r • 1)) (A := CStarMatrix d d ℂ) f ?_ (by fun_prop) ?_ (fun x _ ↦ x.H)
    · intro _ _
      exact isCompact_Icc
    · simp only [Set.mem_Icc]
      exact fun _ _ ↦ eventually_nhdsWithin_of_forall hab
  · simp
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use ⟨x, 1⟩
    simp

open ComplexOrder in
theorem Matrix.PosDef.spectrum_subset_Ioi {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.PosDef) : spectrum ℝ A ⊆ Set.Ioi 0 := by
  intro x hx;
  -- Since $A$ is positive definite, all its eigenvalues are positive.
  have h_eigenvalues_pos : ∀ i : d, 0 < hA.1.eigenvalues i := by
    exact hA.eigenvalues_pos;
  have h_spectrum_eq_range : spectrum ℝ A = Set.range (hA.1.eigenvalues) := by
    exact Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA.left;
  aesop

/--
If f is a continuous family of functions parameterized by x, then (fun x => A.cfc (f x)) is also continuous.
-/
@[fun_prop]
theorem continuous_cfc_fun {f : X → ℝ → ℝ} (hf : ∀ i, Continuous (f · i)) :
    Continuous (fun x ↦ A.cfc (f x)) := by
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  fun_prop

variable {f : X → ℝ → ℝ} {S : Set X}
/--
ContinuousOn variant for when all the matrices (A x) have a spectrum in a set T, and f is continuous on a set S.
-/
@[fun_prop]
theorem continuousOn_cfc_fun {T : Set ℝ}
  (hf : ∀ i ∈ T, ContinuousOn (f · i) S) (hA : spectrum ℝ A.mat ⊆ T) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_continuous_domRestrict] at hf ⊢
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  unfold Set.domRestrict at hf
  apply continuous_finsetSum _
  rw [A.H.spectrum_real_eq_range_eigenvalues] at hA
  refine fun i _ ↦ Continuous.smul (hf _ (by grind)) (by fun_prop)

section joint_continuity

--TODO Cleanup

/--
Bound the Frobenius norm of a functional calculus application.
-/
lemma norm_cfc_le_sqrt_card_mul_bound {A : HermitianMat d ℂ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ spectrum ℝ A.mat, ‖f x‖ ≤ C) :
    ‖A.cfc f‖ ≤ Real.sqrt (Fintype.card d) * C := by
  rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ];
  -- Recall that the Frobenius norm of a Hermitian matrix is the square root of the sum of the squares of its eigenvalues.
  have h_frobenius_eigenvalues : ∀ (M : HermitianMat d ℂ), ‖M‖ ^ 2 = ∑ i ∈ Finset.univ, (M.H.eigenvalues i) ^ 2 := by
    exact fun M => norm_eq_sum_eigenvalues_sq M;
  -- Applying the bound on the eigenvalues to the Frobenius norm.
  have h_bound : ∑ i ∈ Finset.univ, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ (Fintype.card d) * C ^ 2 := by
    have h_bound : ∀ i, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ C ^ 2 := by
      intro i
      have h_eigenvalue_bound : |(A.cfc f).H.eigenvalues i| ≤ C := by
        obtain ⟨ x, hx, hx' ⟩ : (A.cfc f).H.eigenvalues i ∈ f '' spectrum ℝ A.mat := by
          have h_bound := (A.cfc f).H.eigenvalues_mem_spectrum_real i
          rwa [spectrum_cfc_eq_image A f] at h_bound
        specialize hf x hx
        aesop;
      nlinarith only [ abs_le.mp h_eigenvalue_bound ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => h_bound _ ) ( by simp );
  rw [ h_frobenius_eigenvalues, Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( Fintype.card d : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ]

/-
The norm of the difference of two functional calculus applications is bounded by `sqrt(d)` times the sup norm of the difference of the functions.
-/
lemma norm_cfc_sub_cfc_le_sqrt_card {A : HermitianMat d ℂ} {f g : ℝ → ℝ} :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖ := by
  rw [ ← HermitianMat.cfc_sub ];
  refine' le_trans ( norm_cfc_le_sqrt_card_mul_bound _ _ ) _;
  exact ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖;
  · exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _;
  · intro x hx
    apply le_csSup;
    · -- The supremum of a finite set of real numbers is finite.
      have h_finite : Set.Finite (spectrum ℝ A.mat) := by
        exact Set.toFinite _;
      obtain ⟨ M, hM ⟩ := h_finite.exists_finset_coe;
      refine' ⟨ ∑ x ∈ M, ‖f x - g x‖, Set.forall_mem_range.2 fun x => _ ⟩;
      rw [ ← hM ];
      rw [ @ciSup_eq_ite ];
      split_ifs <;> [ exact Finset.single_le_sum ( fun x _ => norm_nonneg ( f x - g x ) ) ( by assumption ) ; exact le_trans ( by norm_num ) ( Finset.sum_nonneg fun x _ => norm_nonneg ( f x - g x ) ) ];
    · exact ⟨ x, by aesop ⟩;
  · rfl

/-
If f and g are close on T, and the spectrum of A is in T, then A.cfc f and A.cfc g are close.
-/
lemma norm_cfc_sub_le_of_sup_le {A : HermitianMat d ℂ} {f g : ℝ → ℝ} {T : Set ℝ} {ε : ℝ}
    (hT : spectrum ℝ A.mat ⊆ T) (hε : 0 ≤ ε) (h_sup : ∀ x ∈ T, ‖f x - g x‖ ≤ ε) :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ε := by
  refine' le_trans ( norm_cfc_sub_cfc_le_sqrt_card ) _;
  gcongr;
  refine' ciSup_le fun x => _;
  exact Real.iSup_le (fun i => h_sup x (hT i)) hε

/--
If $f$ is jointly continuous on $S \times T$ and $T$ is compact, then $x \mapsto f(x, \cdot)$ is continuous into the space of bounded functions on $T$ with the uniform norm.
-/
lemma dist_lt_of_continuous' {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {S : Set X} {T : Set ℝ}
    (hT : IsCompact T)
    (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
    {x₀ : X} (hx₀ : x₀ ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U ∩ S, ∀ t ∈ T, ‖f x t - f x₀ t‖ < ε := by
  by_contra h_contra;
  -- For each $t \in T$, by continuity at $(x₀, t)$, there exist neighborhoods $U_t$ of $x₀$ and $V_t$ of $t$ such that for all $x \in U_t \cap S$ and $t' \in V_t \cap T$, $|f(x, t') - f(x₀, t)| < \epsilon/2$.
  have h_cont : ∀ t ∈ T, ∃ U_t ∈ nhds x₀, ∃ V_t ∈ nhds t, ∀ x ∈ U_t ∩ S, ∀ t' ∈ V_t ∩ T, ‖f x t' - f x₀ t‖ < ε / 2 := by
    intro t ht
    have h_cont_t : ∀ᶠ (p : X × ℝ) in nhds (x₀, t), p ∈ S ×ˢ T → ‖f p.1 p.2 - f x₀ t‖ < ε / 2 := by
      have := hf ( x₀, t ) ⟨ hx₀, ht ⟩;
      have := this.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) );
      rw [ eventually_nhdsWithin_iff ] at this; aesop;
    rcases mem_nhds_prod_iff.mp h_cont_t with ⟨ U, hU, V, hV, hUV ⟩;
    exact ⟨ U, hU, V, hV, fun x hx t' ht' => hUV ( Set.mk_mem_prod hx.1 ht'.1 ) ⟨ hx.2, ht'.2 ⟩ ⟩;
  choose! U hU V hV hUV using h_cont;
  -- Since $T$ is compact, cover it by finitely many $V_{t_i}$. Let $U = \bigcap U_{t_i}$.
  obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset ℝ, (∀ t ∈ t_fin, t ∈ T) ∧ T ⊆ ⋃ t ∈ t_fin, V t := by
    have := hT.elim_nhds_subcover V fun t ht => hV t ht;
    tauto;
  refine h_contra ⟨⋂ t ∈ t_fin, U t, ?_, ?_⟩
  · exact Filter.biInter_mem ( Finset.finite_toSet t_fin ) |>.2 fun t ht => hU t ( ht_fin.1 t ht );
  · intro x hx t ht
    obtain ⟨t', ht'_fin, ht'_t⟩ : ∃ t' ∈ t_fin, t ∈ V t' := by
      simpa using ht_fin.2 ht;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x ⟨ Set.mem_iInter₂.1 hx.1 t' ht'_fin, hx.2 ⟩ t ⟨ ht'_t, ht ⟩;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x₀ ⟨ mem_of_mem_nhds ( hU t' ( ht_fin.1 t' ht'_fin ) ), hx₀ ⟩ t ⟨ ht'_t, ht ⟩;
    exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ], by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ] ⟩

set_option backward.isDefEq.respectTransparency false in
/--
The functional calculus is continuous on matrices with spectrum in a compact set.
-/
lemma continuousOn_cfc_of_compact {K : Set ℝ} {g : ℝ → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K) :
    ContinuousOn (fun (A : HermitianMat d ℂ) ↦ A.cfc g) {A | spectrum ℝ A.mat ⊆ K} := by
  by_contra! h_contra;
  -- By Stone-Weierstrass, there exists a sequence of polynomials `p_n` converging uniformly to `g` on `K`.
  obtain ⟨p_n, hp_n⟩ : ∃ p_n : ℕ → Polynomial ℝ, (∀ n, ∀ x ∈ K, |(p_n n).eval x - g x| ≤ 1 / (n + 1)) := by
    have h_stone_weierstrass : ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x ∈ K, |p.eval x - g x| < ε := by
      have := @exists_polynomial_near_of_continuousOn;
      obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, K ⊆ Set.Icc a b := by
        exact ⟨ hK.bddBelow.some, hK.bddAbove.some, fun x hx => ⟨ hK.bddBelow.choose_spec hx, hK.bddAbove.choose_spec hx ⟩ ⟩;
      -- Extend $g$ to a continuous function on $[a, b]$.
      obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) ∧ ∀ x ∈ K, f x = g x := by
        have := @ContinuousMap.exists_restrict_eq;
        specialize this ( show IsClosed K from hK.isClosed ) ( ContinuousMap.mk ( fun x => g x ) <| by exact continuousOn_iff_continuous_domRestrict.mp hg );
        exact ⟨ _, this.choose.continuous.continuousOn, fun x hx => by simpa using congr_arg ( fun f => f ⟨ x, hx ⟩ ) this.choose_spec ⟩;
      exact fun ε εpos => by rcases this a b f hf.1 ε εpos with ⟨ p, hp ⟩ ; exact ⟨ p, fun x hx => by simpa only [ hf.2 x hx ] using hp x ( hab hx ) ⟩ ;
    exact ⟨ fun n => Classical.choose ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n x hx => le_of_lt ( Classical.choose_spec ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ) x hx ) ⟩;
  -- The sequence `A ↦ A.cfc (p_n)` converges uniformly to `A ↦ A.cfc g` on `{A | spectrum A ⊆ K}`.
  have h_uniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ < ε := by
    -- By the properties of the functional calculus, we have `‖A.cfc p_n - A.cfc g‖ ≤ sqrt(d) * ‖p_n - g‖_{∞, K}`.
    have h_uniform_bound : ∀ n, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * (1 / (n + 1)) := by
      intro n A hA
      have h_uniform_bound : ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, |(p_n n).eval x - g x| := by
        exact norm_cfc_sub_cfc_le_sqrt_card;
      refine' le_trans h_uniform_bound ( mul_le_mul_of_nonneg_left _ ( Real.sqrt_nonneg _ ) );
      refine' ciSup_le fun x => _;
      field_simp;
      by_cases hx : x ∈ spectrum ℝ A.mat <;> simp_all
      exact le_trans ( mul_le_mul_of_nonneg_right ( hp_n n x ( hA hx ) ) ( by positivity ) ) ( by nlinarith [ mul_inv_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] );
    exact fun ε εpos => ⟨ Nat.ceil ( ε⁻¹ * Real.sqrt ( Fintype.card d ) ), fun n hn A hA => lt_of_le_of_lt ( h_uniform_bound n A hA ) ( by rw [ mul_one_div, div_lt_iff₀ ] <;> nlinarith [ Nat.ceil_le.mp hn, inv_pos.mpr εpos, mul_inv_cancel₀ εpos.ne', Real.sqrt_nonneg ( Fintype.card d ), Real.sq_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ] ) ⟩;
  -- The uniform limit of continuous functions is continuous.
  have h_cont : ContinuousOn (fun A : HermitianMat d ℂ => A.cfc g) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
    have h_seq_cont : ∀ n, ContinuousOn (fun A : HermitianMat d ℂ => A.cfc (fun x => (p_n n).eval x)) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
      fun_prop
    refine' Metric.continuousOn_iff.mpr _;
    intro A hA ε εpos
    obtain ⟨N, hN⟩ := h_uniform (ε / 3) (by linarith)
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ a ∈ {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K}, dist a A < δ → ‖a.cfc (fun x => (p_n N).eval x) - A.cfc (fun x => (p_n N).eval x)‖ < ε / 3 := by
      have := Metric.continuousOn_iff.mp ( h_seq_cont N ) A hA ( ε / 3 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun a ha ha' => by simpa only [ dist_eq_norm ] using this.choose_spec.2 a ha ha' ⟩;
    refine' ⟨ δ, δpos, fun a ha ha' => _ ⟩;
    have := hN N le_rfl a ha;
    have := hN N le_rfl A hA;
    rw [ dist_eq_norm ];
    rw [ show a.cfc g - A.cfc g = ( a.cfc g - a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc g ) by abel1 ];
    exact lt_of_le_of_lt ( norm_add₃_le .. ) ( by linarith [ norm_sub_rev ( a.cfc g ) ( a.cfc fun x => Polynomial.eval x ( p_n N ) ), norm_sub_rev ( A.cfc fun x => Polynomial.eval x ( p_n N ) ) ( A.cfc g ), hδ a ha ha' ] );
  contradiction

end joint_continuity

set_option backward.isDefEq.respectTransparency false in
theorem continuous_cfc_joint_compact {X d : Type*} [TopologicalSpace X] [Fintype d] [DecidableEq d]
  {f : X → ℝ → ℝ} {A : X → HermitianMat d ℂ} {S : Set X} {T : Set ℝ}
  (hT : IsCompact T)
  (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
  (hA₁ : ∀ x ∈ S, spectrum ℝ (A x).mat ⊆ T)
  (hA₂ : ContinuousOn (fun x ↦ A x) S) :
    ContinuousOn (fun x ↦ (A x).cfc (f x)) S := by
  intro x x_in_S
  have h_eps_delta : ContinuousWithinAt (fun y => (A y).cfc (f x)) S x := by
    refine ContinuousOn.continuousWithinAt ?_ x_in_S
    exact (continuousOn_cfc_of_compact hT (hf.uncurry_left x x_in_S)).comp hA₂ hA₁
  rw [ ContinuousWithinAt ] at *;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε ε_pos
  obtain ⟨U, hU₁, hU₂⟩ : ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, ‖(A y).cfc (f y) - (A y).cfc (f x)‖ ≤ Real.sqrt (Fintype.card d) * (ε / (2 * Real.sqrt (Fintype.card d) + 1)) := by
    have h_eps_delta₁ : ∀ ε > 0, ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, ‖(A y).cfc (f y) - (A y).cfc (f x)‖ ≤ Real.sqrt (Fintype.card d) * ε := by
      intro ε ε_pos
      obtain ⟨U, hU₁, hU₂⟩ := dist_lt_of_continuous' (f := f) hT hf x_in_S ε_pos
      use U, hU₁
      intro y hy
      apply norm_cfc_sub_le_of_sup_le (hA₁ y hy.right) ε_pos.le
      intro t ht
      exact le_of_lt (hU₂ y hy t ht)
    exact h_eps_delta₁ _ (by positivity)
  filter_upwards [ h_eps_delta ( ε / 2 ) ( half_pos ε_pos ), self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU₁ ] with y hy₁ hy₂ hy₃
  apply lt_of_le_of_lt (dist_triangle _ ((A y).cfc (f x)) _)
  nlinarith [hU₂ y ⟨ hy₃, hy₂ ⟩,
    Real.sqrt_nonneg ( Fintype.card d : ℝ ),
    mul_div_cancel₀ ε ( show ( 2 * Real.sqrt ( Fintype.card d : ℝ ) + 1 ) ≠ 0 by positivity ),
    norm_nonneg ( ( A y ).cfc ( f y ) - ( A y ).cfc ( f x ) ),
    norm_nonneg ( ( A y ).cfc ( f x ) - ( A x ).cfc ( f x ) ),
    dist_eq_norm ( ( A y ).cfc ( f y ) ) ( ( A y ).cfc ( f x ) ),
    dist_eq_norm ( ( A y ).cfc ( f x ) ) ( ( A x ).cfc ( f x ) )]

open scoped Matrix.Norms.Frobenius
/-
PROBLEM
Eigenvalues of a `HermitianMat` are bounded by its (Frobenius) norm.
PROVIDED SOLUTION
Use `norm_eq_sum_eigenvalues_sq` which gives `‖A‖² = Σᵢ (A.H.eigenvalues i)²`. Since `(A.H.eigenvalues i)² ≤ Σⱼ (A.H.eigenvalues j)² = ‖A‖²`, we get `|A.H.eigenvalues i| ≤ ‖A‖`.
-/
lemma eigenvalue_norm_le (A : HermitianMat d ℂ) (i : d) :
    |A.H.eigenvalues i| ≤ ‖A‖ := by
  have h_eigenvalue_bound : |A.H.eigenvalues i| ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [ norm_eq_sum_eigenvalues_sq A ];
    simp [pow_two];
    exact Finset.single_le_sum ( fun i _ => mul_self_nonneg ( A.H.eigenvalues i ) ) ( Finset.mem_univ i );
  nlinarith [ norm_nonneg A ]

/--
The spectrum of a `HermitianMat` is contained in the closed ball of radius `‖A‖` around 0.
-/
lemma spectrum_subset_closedBall (A : HermitianMat d ℂ) :
    spectrum ℝ A.mat ⊆ Metric.closedBall (0 : ℝ) ‖A‖ := by
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  simp [Metric.mem_closedBall, dist_zero_right, eigenvalue_norm_le]
/-
PROBLEM
Upper semicontinuity of the spectrum of a Hermitian matrix: if the spectrum of `A₀` is contained
in an open set `U`, then the spectrum of any Hermitian matrix sufficiently close to `A₀` is also
contained in `U`. This follows from the openness of the set of invertible matrices and compactness.
PROVIDED SOLUTION
The proof uses the resolvent approach and compactness.
1. Let M = ‖A₀‖ + 1. For B in a ball of radius 1 around A₀, ‖B‖ ≤ M, so spectrum ℝ B.mat ⊆ Metric.closedBall 0 M (by spectrum_subset_closedBall and the triangle inequality for norms).
2. Let K = Metric.closedBall (0 : ℝ) M \ U. Then K is compact (closed and bounded minus open = closed and bounded in ℝ). And K ∩ spectrum ℝ A₀.mat = ∅ (since spectrum ℝ A₀.mat ⊆ U).
3. For each t ∈ K: t ∉ spectrum ℝ A₀.mat. By the definition of spectrum, A₀.mat - algebraMap ℝ (Matrix d d ℂ) t is a unit. The set of units is open (Units.isOpen, since Matrix d d ℂ has HasSummableGeomSeries). The map B ↦ B.mat - algebraMap ℝ _ t is continuous. So there exist δ_t > 0 and ε_t > 0 such that for ‖B - A₀‖ < δ_t and |s - t| < ε_t, B.mat - algebraMap ℝ _ s is a unit, meaning s ∉ spectrum ℝ B.mat.
4. By compactness of K (it's compact since it's a closed subset of the compact ball): finitely many ε-balls B(t_j, ε_{t_j}) cover K. Let δ = min(1, min_j δ_{t_j}).
5. For B with ‖B - A₀‖ < δ: spectrum ℝ B.mat ⊆ Metric.closedBall 0 M (by step 1) and spectrum ℝ B.mat ∩ K = ∅ (by step 4). So spectrum ℝ B.mat ⊆ Metric.closedBall 0 M \ K ⊆ U.
Note: we need to connect spectrum ℝ B.mat (the real spectrum) to IsUnit in the complex matrix ring. Use that for self-adjoint elements, t ∈ spectrum ℝ A.mat iff algebraMap ℝ (Matrix d d ℂ) t ∈ spectrum ℂ A.mat, and the resolvent set is open. We can use spectrum.isOpen_resolventSet or the characterization via IsUnit.
-/
set_option backward.isDefEq.respectTransparency false in
lemma spectrum_subset_of_isOpen (A₀ : HermitianMat d ℂ) (U : Set ℝ)
    (hU : IsOpen U) (hAU : spectrum ℝ A₀.mat ⊆ U) :
    ∀ᶠ B in nhds A₀, spectrum ℝ B.mat ⊆ U := by
  -- Let `M = ‖A₀‖ + 1`. For `B` with `‖B - A₀‖ < 1` we get `‖B‖ ≤ M`, so `σ(B) ⊆ closedBall 0 M`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ B : HermitianMat d ℂ, ‖B - A₀‖ < 1 →
      spectrum ℝ B.mat ⊆ Metric.closedBall 0 M := by
    use ‖A₀‖ + 1
    intro B hB
    have h_norm : ‖B‖ ≤ ‖A₀‖ + 1 := by
      have := norm_sub_norm_le B A₀; linarith
    exact (spectrum_subset_closedBall B).trans (Metric.closedBall_subset_closedBall h_norm)
  -- `K = closedBall 0 M \ U` is compact and disjoint from `σ(A₀)`.
  set K : Set ℝ := Metric.closedBall 0 M \ U
  have hK_compact : IsCompact K := IsCompact.diff (ProperSpace.isCompact_closedBall _ _) hU
  have hK_disjoint : K ∩ spectrum ℝ A₀.mat = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => hx.1.2 <| hAU hx.2
  -- For each `t ∈ K` there are `δ_t, ε_t > 0` such that `‖B - A₀‖ < δ_t` and `|s - t| < ε_t`
  -- make `B.mat - s` a unit: units are open and `A₀.mat - t` is one.
  have h_unitary : ∀ t ∈ K, ∃ δ_t > 0, ∃ ε_t > 0, ∀ B : HermitianMat d ℂ, ‖B - A₀‖ < δ_t →
      ∀ s : ℝ, |s - t| < ε_t → IsUnit (B.mat - algebraMap ℝ (Matrix d d ℂ) s) := by
    intro t ht
    have h_unitary : IsUnit (A₀.mat - algebraMap ℝ (Matrix d d ℂ) t) := by
      simp_all [Set.ext_iff, spectrum.mem_iff]
      simpa using hK_disjoint t ht |> IsUnit.neg |> IsUnit.mul <| isUnit_one
    have h_unitary_open : IsOpen {B : Matrix d d ℂ | IsUnit B} := Units.isOpen
    have h_unitary_cont : Continuous (fun p : HermitianMat d ℂ × ℝ =>
        p.1.mat - algebraMap ℝ (Matrix d d ℂ) p.2) := by
      refine' Continuous.sub _ _ <;> fun_prop (disch := solve_by_elim)
    obtain ⟨ε, ε_pos, hε⟩ :=
      Metric.isOpen_iff.mp (h_unitary_open.preimage h_unitary_cont) (A₀, t) h_unitary
    exact ⟨ε, ε_pos, ε, ε_pos, fun B hB s hs => hε (show (B, s) ∈ Metric.ball (A₀, t) ε from by
      simp only [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · simpa [dist_eq_norm] using hB
      · simpa [dist_eq_norm] using hs)⟩
  -- Compactness gives a finite subcover of `ε`-balls; set `δ = min 1 (min_j δ_j)`.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ K, ∃ ε_t > 0, ∀ B : HermitianMat d ℂ, ‖B - A₀‖ < δ →
      ∀ s : ℝ, |s - t| < ε_t → IsUnit (B.mat - algebraMap ℝ (Matrix d d ℂ) s) := by
    choose! δ hδ ε hε h using h_unitary
    have := hK_compact.elim_nhds_subcover (fun t => Metric.ball t (ε t))
      fun t ht => Metric.ball_mem_nhds t (hε t ht)
    simp_all [Set.subset_def]
    obtain ⟨t, ht₁, ht₂⟩ := this
    obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ i ∈ t, δ_min ≤ δ i := by
      by_cases ht : t.Nonempty <;> simp_all [Finset.Nonempty]
      · exact ⟨Finset.min' (t.image δ) ⟨_, Finset.mem_image_of_mem δ ht.choose_spec⟩,
          by have := Finset.min'_mem (t.image δ) ⟨_, Finset.mem_image_of_mem δ ht.choose_spec⟩; aesop,
          fun i hi => Finset.min'_le _ _ (Finset.mem_image_of_mem δ hi)⟩
      · exact ⟨1, zero_lt_one⟩
    refine' ⟨Min.min δ_min 1, lt_min hδ_min_pos zero_lt_one, fun x hx => _⟩
    obtain ⟨i, hi, hi'⟩ := ht₂ x hx
    exact ⟨ε i - |x - i|, sub_pos.mpr (by simp_all [abs_sub_comm]; exact hi'),
      fun B hB s hs => h i (ht₁ i hi) B (lt_of_lt_of_le hB (min_le_of_left_le (hδ_min i hi))) s
        (by rw [abs_lt] at *; constructor <;> linarith [abs_le.mp (show |x - i| ≤ |x - i| by rfl)])⟩
  -- For `B` with `‖B - A₀‖ < δ`, any `t ∈ σ(B)` lies outside `K`.
  have h_not_in_K : ∀ B : HermitianMat d ℂ, ‖B - A₀‖ < δ → ∀ t ∈ spectrum ℝ B.mat, t ∉ K := by
    intro B hB t ht htK
    obtain ⟨ε_t, hε_t_pos, hε_t⟩ := hδ t htK
    have h_unit : IsUnit (B.mat - algebraMap ℝ (Matrix d d ℂ) t) :=
      hε_t B hB t (by simpa using hε_t_pos)
    exact ht (by have h1 := h_unit.neg; simp_all; exact h1)
  filter_upwards [Metric.ball_mem_nhds A₀ (show 0 < Min.min δ 1 by positivity)] with B hB using
    fun t ht => Classical.not_not.1 fun h => h_not_in_K B
      (lt_of_lt_of_le (by simpa [dist_eq_norm] using hB) (min_le_left _ _)) t ht
      ⟨hM B (lt_of_lt_of_le (by simpa [dist_eq_norm] using hB) (min_le_right _ _)) ht, h⟩

/-
PROBLEM
The CFC is continuous in the matrix argument when the function is continuous on a set containing
the spectra, even when that set is not compact. This generalizes `continuousOn_cfc_of_compact`.
The proof uses Tietze extension from the finite spectrum to a compact interval, applies the
compact version, and bounds the error using upper semicontinuity of the spectrum.
PROVIDED SOLUTION
The proof uses Tietze extension and the compact version `continuousOn_cfc_of_compact`.
Step 1: Extend g from the finite set spectrum(A₀) to all of ℝ via Tietze.
The spectrum `Λ := spectrum ℝ A₀.mat` is finite (it equals `Set.range A₀.H.eigenvalues`), hence closed.
The restriction of g to Λ is continuous (any function on a finite set is continuous in a T1 space, using `continuousOn_finite`).
By `ContinuousMap.exists_restrict_eq`, there exists a continuous function `h : C(ℝ, ℝ)` with `h = g` on Λ.
Step 2: (A₀).cfc g = (A₀).cfc h, since g = h on spectrum(A₀) (by `cfc_congr`).
Step 3: Show `B ↦ B.cfc h` is continuous at A₀.
Let M = ‖A₀‖ + 1 and K = Set.Icc (-M) M. Since h is continuous on ℝ and hence on K, and K is compact, by `continuousOn_cfc_of_compact`, the map `B ↦ B.cfc h` is continuous on `{B | spectrum ℝ B.mat ⊆ K}`. Since `{B | spectrum ℝ B.mat ⊆ T} ∩ (Metric.ball A₀ 1) ⊆ {B | spectrum ℝ B.mat ⊆ K}` (because for B near A₀, ‖B‖ ≤ M, so spectrum B ⊆ [-M, M] = K by spectrum_subset_closedBall), the map is ContinuousWithinAt at A₀.
Step 4: Show `‖B.cfc g - B.cfc h‖ → 0` as B → A₀ within `{B | σ(B) ⊆ T}`.
The function `|g - h|` is 0 on Λ = spectrum(A₀). For each eigenvalue λᵢ ∈ Λ ⊆ T:
- g is continuous on T at λᵢ
- h is continuous everywhere
So `|g(t) - h(t)| = |g(t) - g(λᵢ) + h(λᵢ) - h(t)|` is small for t near λᵢ with t ∈ T.
Define U_ε = {t ∈ ℝ | ∀ λ ∈ Λ, if |t - λ| < some δ then |g(t) - h(t)| < ε for t ∈ T} ∪ (complement of a ball around Λ).
Actually, more precisely: the set V_ε = {t : ℝ | t ∈ T → |g(t) - h(t)| < ε} is an open set containing Λ (since |g - h| = 0 on Λ and both are continuous at each point of Λ along T).
By `spectrum_subset_of_isOpen`, for B near A₀, spectrum(B) ⊆ V_ε.
Since spectrum(B) ⊆ T, for t ∈ spectrum(B), |g(t) - h(t)| < ε.
So ‖B.cfc g - B.cfc h‖ ≤ sqrt(d) * ε by `norm_cfc_sub_le_of_sup_le`.
Step 5: Combine. By the triangle inequality:
‖B.cfc g - A₀.cfc g‖ ≤ ‖B.cfc g - B.cfc h‖ + ‖B.cfc h - A₀.cfc h‖
Both terms → 0, so the map is ContinuousWithinAt.
Use `Metric.continuousWithinAt_iff` and an ε/2 argument.
-/
set_option backward.isDefEq.respectTransparency false in
lemma continuousWithinAt_cfc_of_continuousOn {T : Set ℝ} {g : ℝ → ℝ}
    {A₀ : HermitianMat d ℂ}
    (hg : ContinuousOn g T) (hA₀ : spectrum ℝ A₀.mat ⊆ T) :
    ContinuousWithinAt (fun B ↦ B.cfc g) {B | spectrum ℝ B.mat ⊆ T} A₀ := by
  have h_ext : ∃ h : ℝ → ℝ, Continuous h ∧ ∀ x ∈ spectrum ℝ A₀.mat, h x = g x := by
    have h_finite : Set.Finite (spectrum ℝ A₀.mat) := by
      exact Set.toFinite _
    generalize_proofs at *; (
    have h_cont : ContinuousOn g (spectrum ℝ A₀.val) := by
      exact hg.mono hA₀
    generalize_proofs at *; (
    have := @ContinuousMap.exists_restrict_eq ℝ;
    specialize this ( show IsClosed ( spectrum ℝ A₀.val ) from h_finite.isClosed ) ( ContinuousMap.mk ( fun x => g x ) <| by exact continuousOn_iff_continuous_domRestrict.mp h_cont ) ; rcases this with ⟨ h, hh ⟩ ; exact ⟨ h, h.continuous, fun x hx => by simpa using congr_arg ( fun f => f ⟨ x, hx ⟩ ) hh ⟩ ;));
  obtain ⟨h, hh_cont, hh_eq⟩ := h_ext;
  have h_cfc_cont : ContinuousWithinAt (fun B => B.cfc h) {B : HermitianMat d ℂ | spectrum ℝ B.mat ⊆ T} A₀ := by
    exact Continuous.continuousWithinAt (HermitianMat.cfc_continuous hh_cont)
  have h_diff_small : ∀ ε > 0, ∃ U ∈ nhds A₀, ∀ B ∈ U ∩ {B : HermitianMat d ℂ | spectrum ℝ B.mat ⊆ T}, ‖B.cfc g - B.cfc h‖ < ε := by
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ T, ∀ y ∈ spectrum ℝ A₀.mat, |x - y| < δ → |g x - h x| < ε / (Real.sqrt (Fintype.card d) + 1) := by
      have h_diff_small : ∀ y ∈ spectrum ℝ A₀.mat, ∃ δ > 0, ∀ x ∈ T, |x - y| < δ → |g x - h x| < ε / (Real.sqrt (Fintype.card d) + 1) := by
        intro y hy
        have h_diff_small : Filter.Tendsto (fun x => |g x - h x|) (nhdsWithin y T) (nhds 0) := by
          have h_diff_small : Filter.Tendsto (fun x => g x - h x) (nhdsWithin y T) (nhds (g y - h y)) := by
            exact Filter.Tendsto.sub ( hg.continuousWithinAt ( hA₀ hy ) ) ( hh_cont.continuousWithinAt );
          simpa [ hh_eq y hy ] using h_diff_small.abs;
        have := Metric.tendsto_nhdsWithin_nhds.mp h_diff_small ( ε / ( Real.sqrt ( Fintype.card d ) + 1 ) ) ( div_pos ε_pos ( add_pos_of_nonneg_of_pos ( Real.sqrt_nonneg _ ) zero_lt_one ) ) ; aesop;
      choose! δ hδ_pos hδ using h_diff_small;
      have h_finite : Set.Finite (spectrum ℝ A₀.mat) := by
        exact Set.toFinite _;
      obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ y ∈ spectrum ℝ A₀.mat, δ_min ≤ δ y := by
        by_cases h_empty : spectrum ℝ A₀.mat = ∅;
        · exact ⟨ 1, zero_lt_one, by simp [ h_empty ] ⟩;
        · have := h_finite.toFinset.exists_min_image δ;
          exact Exists.elim ( this ( Finset.nonempty_of_ne_empty ( by simpa [ Set.ext_iff ] using h_empty ) ) ) fun x hx => ⟨ δ x, hδ_pos x ( by simpa using hx.1 ), fun y hy => hx.2 _ ( h_finite.mem_toFinset.mpr hy ) ⟩;
      exact ⟨ δ_min, hδ_min_pos, fun x hx y hy hxy => hδ y hy x hx ( lt_of_lt_of_le hxy ( hδ_min y hy ) ) ⟩;
    -- By the spectrum_subset_of_isOpen lemma, there exists a neighborhood U of A₀ such that the spectrum of B is within δ of the spectrum of A₀ for all B in U.
    obtain ⟨U, hU⟩ : ∃ U ∈ nhds A₀, ∀ B ∈ U, spectrum ℝ B.mat ⊆ {x | ∃ y ∈ spectrum ℝ A₀.mat, |x - y| < δ} := by
      have h_spectrum_subset : ∀ᶠ B in nhds A₀, spectrum ℝ B.mat ⊆ Metric.thickening δ (spectrum ℝ A₀.mat) := by
        have h_open : IsOpen (Metric.thickening δ (spectrum ℝ A₀.mat)) := by
          exact Metric.isOpen_thickening
        have := spectrum_subset_of_isOpen A₀ ( Metric.thickening δ ( spectrum ℝ A₀.mat ) ) h_open ( Metric.self_subset_thickening δ_pos _ ) ; aesop;
      generalize_proofs at *; (
      exact ⟨ _, h_spectrum_subset, fun B hB => fun x hx => by simpa [ dist_eq_norm ] using Metric.mem_thickening_iff.mp ( hB hx ) ⟩)
    generalize_proofs at *; (
    refine' ⟨ U, hU.1, fun B hB => _ ⟩
    have h_diff_small : ∀ x ∈ spectrum ℝ B.mat, |g x - h x| ≤ ε / (Real.sqrt (Fintype.card d) + 1) := by
      exact fun x hx => le_of_lt ( hδ x ( hB.2 hx ) _ ( hU.2 B hB.1 hx |> Classical.choose_spec |> And.left ) ( hU.2 B hB.1 hx |> Classical.choose_spec |> And.right ) ) |> le_trans <| by norm_num;
    generalize_proofs at *; (
    have h_diff_small : ‖B.cfc g - B.cfc h‖ ≤ Real.sqrt (Fintype.card d) * (ε / (Real.sqrt (Fintype.card d) + 1)) := by
      apply_rules [ norm_cfc_sub_le_of_sup_le ];
      · positivity;
      · exact fun x hx => hx
    generalize_proofs at *; (
    exact h_diff_small.trans_lt ( by rw [ mul_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( Fintype.card d : ℝ ), Real.sq_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ] ))));
  rw [ Metric.continuousWithinAt_iff ] at *;
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cfc_cont (ε / 2) (half_pos hε)
  obtain ⟨U, hU_nhds, hU⟩ := h_diff_small (ε / 2) (half_pos hε)
  use Min.min δ (Metric.mem_nhds_iff.mp hU_nhds).choose
  simp [hδ_pos];
  refine' ⟨ _, _ ⟩
  all_goals generalize_proofs at *;
  · exact ‹∃ ε, 0 < ε ∧ Metric.ball A₀ ε ⊆ U›.choose_spec.1;
  · intro x hx hx' hx''
    have hd1 := hδ hx hx'
    have hd2 := hU x ⟨(Metric.mem_nhds_iff.mp hU_nhds).choose_spec.2 hx'', hx⟩
    have h_eq : A₀.cfc g = A₀.cfc h := by
      exact cfc_congr (show Set.EqOn g h (spectrum ℝ A₀.mat) from fun x hx => hh_eq x hx ▸ rfl) ▸ rfl
    rw [dist_eq_norm, h_eq]
    calc ‖x.cfc g - A₀.cfc h‖
        = ‖(x.cfc g - x.cfc h) + (x.cfc h - A₀.cfc h)‖ := by congr 1; abel
      _ ≤ ‖x.cfc g - x.cfc h‖ + ‖x.cfc h - A₀.cfc h‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add hd2
          rwa [dist_eq_norm] at hd1
      _ = ε := add_halves ε

/-
PROBLEM
For `f` jointly continuous on `S ×ˢ T` and the spectrum of `A y` contained in `T`, the difference
`f(y,t) - f(x₀,t)` can be made uniformly small on `spectrum (ℝ) (A y).mat` for `y` near `x₀`.
This is the non-compact replacement for `dist_lt_of_continuous'`: instead of uniform convergence
on a fixed compact set, we get uniform convergence on the (moving, finite) spectrum.
PROVIDED SOLUTION
Constructive proof. The key steps:
Step 1: For each eigenvalue λᵢ := (A x₀).H.eigenvalues i (which is in T by hA₁), the function f is continuous at (x₀, λᵢ) within S ×ˢ T. So there exist open neighborhoods U_i of x₀ and V_i of λᵢ such that for all (y, t) ∈ (U_i ∩ S) × (V_i ∩ T), we have ‖f y t - f x₀ t‖ < ε. Here's how to get this:
- hf (x₀, λᵢ) gives ContinuousWithinAt at (x₀, λᵢ) within S ×ˢ T
- Apply this to the ε-ball around f(x₀, λᵢ), use that f(x₀, λᵢ) - f(x₀, λᵢ) = 0 to get ‖f y t - f x₀ λᵢ‖ < ε/2
- Similarly, hf at (x₀, λᵢ) restricted to {x₀} × T gives ‖f x₀ t - f x₀ λᵢ‖ < ε/2
- Triangle inequality: ‖f y t - f x₀ t‖ < ε
- Use `mem_nhds_prod_iff` to extract U_i and V_i from the product neighborhood
Step 2: The open set W := ⋃ᵢ V_i contains spectrum(A x₀) (since each λᵢ ∈ V_i and spectrum = range of eigenvalues). W is open as a union of open sets. By `spectrum_subset_of_isOpen (A x₀) W`, we get ∀ᶠ B in nhds (A x₀), spectrum ℝ B.mat ⊆ W.
Step 3: By ContinuousWithinAt of A at x₀ (from hA₂), and the filter from step 2, we get: ∀ᶠ y in nhdsWithin x₀ S, spectrum ℝ (A y).mat ⊆ W. Convert this to ∃ U' ∈ nhds x₀, ∀ y ∈ U' ∩ S, spectrum(A y) ⊆ W.
Step 4: Take U = U' ∩ ⋂ᵢ U_i (finite intersection since d is Fintype). For y ∈ U ∩ S and t ∈ spectrum(A y):
- t ∈ T (by hA₁)
- spectrum(A y) ⊆ W (by step 3), so t ∈ V_i for some i
- y ∈ U_i ∩ S
- So ‖f y t - f x₀ t‖ < ε (by step 1)
Use `by_contra` and arrive at contradiction, or construct the neighborhood directly using `Filter.inter_mem` and `Filter.iInter_mem` (since d is Fintype, the index set is finite).
IMPORTANT: To get the open sets V_i, use `ContinuousWithinAt` of f at (x₀, λᵢ) which gives an eventually filter statement, then extract using `mem_nhdsWithin_iff_exists_mem_nhds_inter` and `mem_nhds_prod_iff`.
For the continuity of A composed with spectrum_subset_of_isOpen: use `ContinuousWithinAt.eventually` or compose the filter. Specifically: `(hA₂ x₀ hx₀).eventually (spectrum_subset_of_isOpen (A x₀) W hW_open hW_contains)` gives `∀ᶠ y in nhdsWithin x₀ S, spectrum(A y) ⊆ W`. Then use `Filter.Eventually.exists_mem` to get U'.
-/
lemma dist_lt_of_continuous_spectrum {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {A : X → HermitianMat d ℂ} {S : Set X} {T : Set ℝ}
    (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
    (hA₁ : ∀ x ∈ S, spectrum ℝ (A x).mat ⊆ T)
    (hA₂ : ContinuousOn (fun x ↦ A x) S)
    {x₀ : X} (hx₀ : x₀ ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds x₀, ∀ y ∈ U ∩ S, ∀ t ∈ spectrum ℝ (A y).mat, ‖f y t - f x₀ t‖ < ε := by
      by_contra h_contra;
      -- For each eigenvalue λᵢ := (A x₀).H.eigenvalues i (which is in T by hA₁), the function f is continuous at (x₀, λᵢ) within S ×ˢ T. So there exist open neighborhoods U_i of x₀ and V_i of λᵢ such that for all (y, t) ∈ (U_i ∩ S) × (V_i ∩ T), we have ‖f y t - f x₀ t‖ < ε.
      obtain ⟨U_i, V_i, hU_i, hV_i, h_cont⟩ : ∃ (U_i : d → Set X) (V_i : d → Set ℝ), (∀ i, IsOpen (U_i i)) ∧ (∀ i, IsOpen (V_i i)) ∧ (∀ i, x₀ ∈ U_i i) ∧ (∀ i, (A x₀).H.eigenvalues i ∈ V_i i) ∧ (∀ i, ∀ y ∈ U_i i ∩ S, ∀ t ∈ V_i i ∩ T, ‖f y t - f x₀ t‖ < ε) := by
        have h_cont : ∀ i, ∃ (U_i : Set X) (V_i : Set ℝ), IsOpen U_i ∧ IsOpen V_i ∧ x₀ ∈ U_i ∧ (A x₀).H.eigenvalues i ∈ V_i ∧ ∀ y ∈ U_i ∩ S, ∀ t ∈ V_i ∩ T, ‖f y t - f x₀ t‖ < ε := by
          intro i
          generalize_proofs at *; (
          have h_cont : ContinuousWithinAt (fun p : X × ℝ => f p.1 p.2 - f x₀ p.2) (S ×ˢ T) (x₀, (A x₀).H.eigenvalues i) := by
            have hmemT : (A x₀).H.eigenvalues i ∈ T :=
              hA₁ x₀ hx₀ ((A x₀).H.eigenvalues_mem_spectrum_real i)
            have h1 : ContinuousWithinAt (fun p : X × ℝ => f p.1 p.2) (S ×ˢ T)
                (x₀, (A x₀).H.eigenvalues i) := hf (x₀, (A x₀).H.eigenvalues i) ⟨hx₀, hmemT⟩
            have hg : ContinuousWithinAt (fun q : ℝ => f x₀ q) T ((A x₀).H.eigenvalues i) :=
              (hf (x₀, (A x₀).H.eigenvalues i) ⟨hx₀, hmemT⟩).comp
                (continuousWithinAt_const.prodMk continuousWithinAt_id) (fun q hq => ⟨hx₀, hq⟩)
            have h2 : ContinuousWithinAt (fun p : X × ℝ => f x₀ p.2) (S ×ˢ T)
                (x₀, (A x₀).H.eigenvalues i) :=
              hg.comp (f := Prod.snd) (x := (x₀, (A x₀).H.eigenvalues i))
                continuousWithinAt_snd (fun p hp => hp.2)
            exact h1.sub h2 )
          generalize_proofs at *; (
          have := h_cont.eventually ( Metric.ball_mem_nhds _ hε )
          simp_all [ dist_eq_norm ]
          (
          rw [ eventually_nhdsWithin_iff ] at this
          generalize_proofs at *; (
          rcases mem_nhds_prod_iff.mp this with ⟨ U, V, hU, hV, h ⟩
          generalize_proofs at *; (
          exact ⟨ interior U, isOpen_interior, interior hU, isOpen_interior, mem_interior_iff_mem_nhds.mpr V, mem_interior_iff_mem_nhds.mpr hV, fun y hy hyS t ht htT => h ( Set.mk_mem_prod ( interior_subset hy ) ( interior_subset ht ) ) ⟨ hyS, htT ⟩ ⟩))))
        generalize_proofs at *; (
        choose U_i V_i hU_i hV_i hx₀_i hV_i_i h_cont_i using h_cont; exact ⟨ U_i, V_i, hU_i, hV_i, hx₀_i, hV_i_i, h_cont_i ⟩ ;);
      -- The open set W := ⋃ᵢ V_i contains spectrum(A x₀) (since each λᵢ ∈ V_i and spectrum = range of eigenvalues). W is open as a union of open sets.
      set W := ⋃ i, V_i i with hW_def
      have hW_open : IsOpen W := by
        exact isOpen_iUnion hV_i
      have hW_spectrum : spectrum ℝ (A x₀).mat ⊆ W := by
        intro t ht
        obtain ⟨i, hi⟩ : ∃ i, t = (A x₀).H.eigenvalues i := by
          have h_eigenvalues : spectrum ℝ (A x₀).mat = Set.range (A x₀).H.eigenvalues :=
            (A x₀).H.spectrum_real_eq_range_eigenvalues
          generalize_proofs at *; (
          exact h_eigenvalues.subset ht |> Exists.imp fun i hi => hi.symm)
        aesop
      have hW_subset : ∀ᶠ B in nhds (A x₀), spectrum ℝ B.mat ⊆ W := by
        exact spectrum_subset_of_isOpen (A x₀) W hW_open hW_spectrum
      have hW_subset_S : ∀ᶠ y in nhdsWithin x₀ S, spectrum ℝ (A y).mat ⊆ W := by
        exact Filter.mem_of_superset ( hA₂.continuousWithinAt hx₀ |> fun h => h.eventually ( hW_subset ) ) fun y hy => hy
      obtain ⟨U', hU'⟩ : ∃ U' ∈ nhds x₀, ∀ y ∈ U' ∩ S, spectrum ℝ (A y).mat ⊆ W := by
        obtain ⟨ U', hU' ⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW_subset_S; use U'; aesop;
      obtain ⟨U'', hU''⟩ : ∃ U'' ∈ nhds x₀, ∀ i, U'' ⊆ U_i i := by
        exact ⟨ ⋂ i, U_i i, Filter.mem_of_superset ( Filter.iInter_mem.mpr fun i => IsOpen.mem_nhds ( hU_i i ) ( h_cont.1 i ) ) fun x hx => by aesop, fun i => Set.iInter_subset _ i ⟩
      set U := U' ∩ U'' with hU_def
      have hU_mem : U ∈ nhds x₀ := by
        exact Filter.inter_mem hU'.1 hU''.1
      have hU_subset : ∀ y ∈ U ∩ S, spectrum ℝ (A y).mat ⊆ W := by
        exact fun y hy => hU'.2 y ⟨ hy.1.1, hy.2 ⟩ |> Set.Subset.trans <| by simp [ hW_def ] ;
      have hU_cont : ∀ y ∈ U ∩ S, ∀ t ∈ spectrum ℝ (A y).mat, ‖f y t - f x₀ t‖ < ε := by
        intro y hy t ht
        obtain ⟨i, hi⟩ : ∃ i, t ∈ V_i i := by
          exact Set.mem_iUnion.mp ( hU_subset y hy ht ) |> Exists.imp fun i => by tauto;
        have h_cont_i : ‖f y t - f x₀ t‖ < ε := by
          exact h_cont.2.2 i y ⟨ hU''.2 i ( by aesop ), hy.2 ⟩ t ⟨ hi, hA₁ y hy.2 ht ⟩ |> fun h => by simpa using h;
        exact h_cont_i
      exact h_contra ⟨U, hU_mem, hU_cont⟩

/-
PROBLEM
Joint continuity of the functional calculus, without requiring compactness of `T`.
This generalizes `continuous_cfc_joint_compact` by removing the `IsCompact T` hypothesis.
The compactness is unnecessary because the spectrum of a `HermitianMat` (which is
finite-dimensional) is always finite and hence compact. The proof works by reducing to
the compact case locally: at each point `x₀ ∈ S`, the spectrum of `A x₀` is finite and
contained in a compact interval `K = [-M, M]`, and the compact version is applied with a
continuous extension of `f x₀` from the finite spectrum to `K`.
PROVIDED SOLUTION
The proof follows the same structure as `continuous_cfc_joint_compact` but uses the non-compact helpers `dist_lt_of_continuous_spectrum` and `continuousWithinAt_cfc_of_continuousOn` instead of `dist_lt_of_continuous'` and `continuousOn_cfc_of_compact`.
Fix x ∈ S. Show ContinuousWithinAt.
Step 1: Show `ContinuousWithinAt (fun y => (A y).cfc (f x)) S x`.
The function f x (i.e., f(x, ·)) is continuous on T: this follows from `hf.uncurry_left x x_in_S` which gives `ContinuousOn (f x) T`.
By `continuousWithinAt_cfc_of_continuousOn` with g = f x and T = T:
  `ContinuousWithinAt (fun B ↦ B.cfc (f x)) {B | spectrum ℝ B.mat ⊆ T} (A x)`.
Compose with `hA₂.continuousWithinAt x_in_S` and `hA₁`:
  `ContinuousWithinAt (fun y => (A y).cfc (f x)) S x`.
Note: We need that `fun y => A y` maps `S` into `{B | spectrum ℝ B.mat ⊆ T}`, which follows from `hA₁`.
Step 2: Use the triangle inequality, exactly as in `continuous_cfc_joint_compact`:
Decompose the goal using:
  dist ((A y).cfc (f y)) ((A x).cfc (f x)) ≤ dist ((A y).cfc (f y)) ((A y).cfc (f x)) + dist ((A y).cfc (f x)) ((A x).cfc (f x))
For the first term (f varies, A = A(y)):
Use `dist_lt_of_continuous_spectrum` (our new helper) to get: for any ε > 0, there exists U ∈ nhds x such that for y ∈ U ∩ S and t ∈ spectrum(A y), ‖f y t - f x t‖ < ε.
Then by `norm_cfc_sub_le_of_sup_le`, ‖(A y).cfc (f y) - (A y).cfc (f x)‖ ≤ sqrt(d) * ε.
For the second term (A varies, f = f(x)):
Use step 1 directly (ContinuousWithinAt of B ↦ B.cfc (f x)).
Combine with the same nlinarith/ε-δ argument as in `continuous_cfc_joint_compact`.
In code, the proof structure should mirror continuous_cfc_joint_compact closely, just replacing:
- `dist_lt_of_continuous' hT hf x_in_S ε_pos` with `dist_lt_of_continuous_spectrum hf hA₁ hA₂ x_in_S ε_pos`
- `continuousOn_cfc_of_compact hT (hf.uncurry_left x x_in_S)` with `continuousWithinAt_cfc_of_continuousOn (hf.uncurry_left x x_in_S) (hA₁ x x_in_S)` composed with hA₂ and hA₁.
-/
set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
theorem continuous_cfc_joint {X d : Type*} [TopologicalSpace X] [Fintype d] [DecidableEq d]
  {f : X → ℝ → ℝ} {A : X → HermitianMat d ℂ} {S : Set X} {T : Set ℝ}
  (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
  (hA₁ : ∀ x ∈ S, spectrum ℝ (A x).mat ⊆ T)
  (hA₂ : ContinuousOn (fun x ↦ A x) S) :
    ContinuousOn (fun x ↦ (A x).cfc (f x)) S := by
      by_contra h_not_cont_at_x₀
      generalize_proofs at *;
      have h_cont : ∀ x₀ ∈ S, ContinuousWithinAt (fun x => (A x).cfc (f x)) S x₀ := by
        intro x₀ hx₀
        have h_cont : ContinuousWithinAt (fun x => (A x).cfc (f x₀)) S x₀ := by
          have h_cont : ContinuousWithinAt (fun B => B.cfc (f x₀)) {B | spectrum ℝ B.mat ⊆ T} (A x₀) := by
            apply_rules [ continuousWithinAt_cfc_of_continuousOn, hf.uncurry_left x₀ hx₀ ]
          generalize_proofs at *; (
          exact h_cont.comp ( hA₂.continuousWithinAt hx₀ ) ( by aesop ) |> ContinuousWithinAt.mono <| by aesop;)
        generalize_proofs at *; (
        -- By the triangle inequality, we can bound the distance between $(A x).cfc (f x)$ and $(A x₀).cfc (f x₀)$.
        have h_triangle : ∀ᶠ x in nhdsWithin x₀ S, ‖(A x).cfc (f x) - (A x).cfc (f x₀)‖ ≤ Real.sqrt (Fintype.card d) * (⨆ t ∈ spectrum ℝ (A x).mat, ‖f x t - f x₀ t‖) := by
          refine' Filter.Eventually.of_forall fun x => _;
          exact norm_cfc_sub_cfc_le_sqrt_card
        generalize_proofs at *; (
        -- By the properties of the supremum, we can bound the distance between $(A x).cfc (f x)$ and $(A x₀).cfc (f x₀)$.
        have h_sup : Filter.Tendsto (fun x => ⨆ t ∈ spectrum ℝ (A x).mat, ‖f x t - f x₀ t‖) (nhdsWithin x₀ S) (nhds 0) := by
          have h_sup : ∀ ε > 0, ∃ U ∈ nhdsWithin x₀ S, ∀ x ∈ U, ∀ t ∈ spectrum ℝ (A x).mat, ‖f x t - f x₀ t‖ < ε := by
            intro ε ε_pos
            generalize_proofs at *; (
            have := dist_lt_of_continuous_spectrum hf hA₁ hA₂ hx₀ ε_pos
            generalize_proofs at *; (
            obtain ⟨ U, hU₁, hU₂ ⟩ := this; exact ⟨ U ∩ S, mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨ U, hU₁, by simp ⟩, fun x hx t ht => hU₂ x ⟨ hx.1, hx.2 ⟩ t ht ⟩ ;))
          generalize_proofs at *; (
          refine' Metric.tendsto_nhds.mpr _;
          intro ε ε_pos; rcases h_sup ( ε / 2 ) ( half_pos ε_pos ) with ⟨ U, hU₁, hU₂ ⟩ ; filter_upwards [ hU₁ ] with x hx; simp_all [ dist_eq_norm ] ; (
          rw [ abs_of_nonneg ( Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _ ) ] ; refine' lt_of_le_of_lt ( ciSup_le fun t => _ ) ( half_lt_self ε_pos ) ; by_cases ht : t ∈ spectrum ℝ ( A x |> HermitianMat.mat ) <;> simp_all [ abs_lt ] ;
          · exact abs_le.mpr ⟨ by linarith [ hU₂ x hx t ht ], by linarith [ hU₂ x hx t ht ] ⟩;
          · linarith [ ε_pos ]))
        generalize_proofs at *; (
        have h_final : Filter.Tendsto (fun x => ‖(A x).cfc (f x) - (A x).cfc (f x₀)‖) (nhdsWithin x₀ S) (nhds 0) := by
          exact squeeze_zero_norm' ( by filter_upwards [ h_triangle ] with x hx; simpa using hx ) ( by simpa using h_sup.const_mul _ ) |> fun h => h.trans ( by simp ) ;
        generalize_proofs at *; (
        convert h_cont.add ( show ContinuousWithinAt ( fun x => ( A x |> HermitianMat.cfc ) ( f x ) - ( A x |> HermitianMat.cfc ) ( f x₀ ) ) S x₀ from ?_ ) using 1 ; aesop
        generalize_proofs at *; (
        exact tendsto_zero_iff_norm_tendsto_zero.mpr h_final |> fun h => h.trans ( by simp) ;)))))
      generalize_proofs at *; (
      exact h_not_cont_at_x₀ <| fun x hx => h_cont x hx |> ContinuousWithinAt.mono <| by simp;)

/-- Specialization of `continuousOn_cfc_fun` for nonsingular matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonsingular {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≠ 0, ContinuousOn (f · i) S) [NonSingular A] :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := {0}ᶜ)
  · exact hf
  · grind [nonSingular_zero_notMem_spectrum]

/-- Specialization of `continuousOn_cfc_fun` for positive semidefinite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonneg {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≥ 0, ContinuousOn (f · i) S) (hA : 0 ≤ A) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ici 0)
  · exact hf
  · rw [zero_le_iff] at hA
    exact hA.pos_of_mem_spectrum

open ComplexOrder in
/-- Specialization of `continuousOn_cfc_fun` for positive definite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_posDef {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i > 0, ContinuousOn (f · i) S) (hA : A.mat.PosDef) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ioi 0)
  · exact hf
  · exact Matrix.PosDef.spectrum_subset_Ioi hA

variable {A B : HermitianMat d 𝕜} (f : ℝ → ℝ)

/--
The inverse of the CFC is the CFC of the inverse function.
-/
lemma inv_cfc_eq_cfc_inv (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) :
    (A.cfc f)⁻¹ = A.cfc (fun u ↦ (f u)⁻¹) := by
  suffices (A.cfc f).mat⁻¹ = (A.cfc (fun u ↦ 1 / f u)).mat by
    ext1
    simpa using this
  have h_def : (A.cfc f).mat = ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  have h_subst : (A.cfc (fun u ↦ 1 / f u)).mat = ∑ i, (1 / f (A.H.eigenvalues i)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A fun u ↦ 1 / f u;
  have h_inv : (A.cfc f).mat * (A.cfc (fun u ↦ 1 / f u)).mat = 1 := by
    -- Since the eigenvectorUnitary is unitary, we have that the product of the projections is the identity matrix.
    have h_unitary : A.H.eigenvectorUnitary.val * A.H.eigenvectorUnitary.val.conjTranspose = 1 := by
      simp [ Matrix.IsHermitian.eigenvectorUnitary ];
    have h_inv : ∀ i j, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) * (A.H.eigenvectorUnitary.val * (Matrix.single j j 1) * A.H.eigenvectorUnitary.val.conjTranspose) = if i = j then A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose else 0 := by
      simp [ ← Matrix.mul_assoc ];
      intro i j; split_ifs <;> simp_all [ Matrix.mul_assoc, mul_eq_one_comm.mp h_unitary ] ;
    simp_all [ Finset.sum_mul, Finset.mul_sum ];
    have h_sum : ∑ i, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) = A.H.eigenvectorUnitary.val * (∑ i, Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose := by
      simp [ Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc ];
    simp_all [ Matrix.single ];
    convert h_unitary using 2;
    ext i j; simp [ Matrix.mul_apply]
    simp [ Matrix.sum_apply, Finset.filter_eq', Finset.filter_and ];
    rw [ Finset.sum_eq_single j ] <;> aesop;
  rw [ Matrix.inv_eq_right_inv h_inv ];

theorem cfc_inv [NonSingular A] : A.cfc (fun u ↦ u⁻¹) = A⁻¹ := by
  simpa using (inv_cfc_eq_cfc_inv id nonSingular_eigenvalue_ne_zero).symm

section integral

open MeasureTheory
open scoped Matrix.Norms.Frobenius

omit [DecidableEq d] in
set_option backward.isDefEq.respectTransparency false in
/--
The integral of a Hermitian matrix function commutes with `toMat`.
-/
lemma integral_toMat (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ}
  (hA : IntervalIntegrable A μ T₁ T₂) :
    (∫ t in T₁..T₂, A t ∂μ).mat = ∫ t in T₁..T₂, (A t).mat ∂μ := by
  exact ((matₗ (R := ℝ)).intervalIntegral_comp_comm hA).symm

set_option backward.isDefEq.respectTransparency false in
/--
A sum of scaled constant matrices is integrable if the scalar functions are integrable.
-/
lemma intervalIntegrable_sum_smul_const (T₁ T₂ : ℝ) {μ : Measure ℝ} (g : ℝ → d → ℝ)
    (P : d → Matrix d d 𝕜) (hg : ∀ i, IntervalIntegrable (fun t ↦ g t i) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ ∑ i, g t i • P i) μ T₁ T₂ := by
  simp_all [intervalIntegrable_iff]
  exact integrable_finsetSum _ fun i _ ↦ Integrable.smul_const (hg i) _

set_option backward.isDefEq.respectTransparency false in
/--
A function to Hermitian matrices is integrable iff its matrix values are integrable.
-/
lemma intervalIntegrable_toMat_iff (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ} :
    IntervalIntegrable (fun t ↦ (A t).mat) μ T₁ T₂ ↔ IntervalIntegrable A μ T₁ T₂ := by
  --TODO Cleanup
  simp [ intervalIntegrable_iff ];
  constructor <;> intro h;
  · -- Since `toMat` is a linear isometry, the integrability of `A.toMat` implies the integrability of `A`.
    have h_toMat_integrable : IntegrableOn (fun t ↦ (A t).mat) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
      intro h_toMat_integrable
      have h_toMat_linear : ∃ (L : HermitianMat d 𝕜 →ₗ[ℝ] Matrix d d 𝕜), ∀ x, L x = x.mat := by
        refine' ⟨ _, _ ⟩;
        refine' { .. };
        exacts [ fun x ↦ x.mat, fun x y ↦ rfl, fun m x ↦ rfl, fun x ↦ rfl ];
      obtain ⟨L, hL⟩ := h_toMat_linear;
      have h_toMat_linear : IntegrableOn (fun t ↦ L (A t)) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
        intro h_toMat_integrable
        have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), ∀ x, L_inv (L x) = x := by
          have h_toMat_linear : Function.Injective L := by
            intro x y hxy;
            simp_all only [HermitianMat.ext_iff]
          have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), L_inv.comp L = LinearMap.id := by
            exact IsSemisimpleModule.extension_property L h_toMat_linear LinearMap.id;
          exact ⟨ h_toMat_linear.choose, fun x ↦ by simpa using LinearMap.congr_fun h_toMat_linear.choose_spec x ⟩;
        obtain ⟨ L_inv, hL_inv ⟩ := h_toMat_linear;
        have h_toMat_linear : IntegrableOn (fun t ↦ L_inv (L (A t))) (Set.uIoc T₁ T₂) μ := by
          exact ContinuousLinearMap.integrable_comp ( L_inv.toContinuousLinearMap ) h_toMat_integrable;
        aesop;
      aesop;
    exact h_toMat_integrable h;
  · apply h.norm.mono'
    · have := h.aestronglyMeasurable;
      fun_prop
    · filter_upwards with t using le_rfl

set_option backward.isDefEq.respectTransparency false in
/--
The CFC of an integrable function family is integrable.
-/
lemma integrable_cfc (T₁ T₂ : ℝ) (f : ℝ → ℝ → ℝ) {μ : Measure ℝ}
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ A.cfc (f t)) μ T₁ T₂ := by
  have h_expand : ∀ t, (A.cfc (f t)).mat = ∑ i, f t (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact fun t ↦ cfc_toMat_eq_sum_smul_proj A (f t);
  rw [ ← intervalIntegrable_toMat_iff ];
  rw [ funext h_expand ];
  apply intervalIntegrable_sum_smul_const
  exact hf

/--
The integral of the CFC is the CFC of the integral.
-/
lemma integral_cfc_eq_cfc_integral (T₁ T₂ : ℝ) {μ : Measure ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    ∫ t in T₁..T₂, A.cfc (f t) ∂μ = A.cfc (fun u ↦ ∫ t in T₁..T₂, f t u ∂μ) := by
  ext1
  rw [ integral_toMat ];
  · rw [ intervalIntegral.integral_congr fun t ht ↦
        HermitianMat.cfc_toMat_eq_sum_smul_proj A ( f t ), intervalIntegral.integral_finsetSum ];
    · rw [ Finset.sum_congr rfl fun i _ ↦ intervalIntegral.integral_smul_const _ _ ];
      exact Eq.symm (cfc_toMat_eq_sum_smul_proj A fun u ↦ ∫ (t : ℝ) in T₁..T₂, f t u ∂μ);
    · simp_all [ intervalIntegrable_iff ];
      exact fun i ↦ ( hf i ).smul_const _
  · exact integrable_cfc T₁ T₂ f hf

end integral

theorem cfc_pos_of_pos {A : HermitianMat d 𝕜} {f : ℝ → ℝ} (hA : 0 < A)
    (hf : ∀ i > 0, 0 < f i) (hf₂ : 0 ≤ f 0) : 0 < A.cfc f := by
  have h_pos := (posSemidef_iff_spectrum_nonneg A).mp hA.le
  have h_f_pos : ∃ x ∈ spectrum ℝ (A.cfc f).mat, x ≠ 0 := by
    obtain ⟨ x, hx₁, hx₂ ⟩ := ne_zero_iff_ne_zero_spectrum A |>.1 hA.ne'
    exact ⟨ f x, by simpa using HermitianMat.spectrum_cfc_eq_image A f ▸ Set.mem_image_of_mem f hx₁,
        by cases lt_or_gt_of_ne hx₂ <;>
        linarith [ hf x ( lt_of_le_of_ne ( h_pos x hx₁ ) ( Ne.symm hx₂ ) ) ] ⟩;
  have h_f_nonneg : 0 ≤ A.cfc f := by
    rw [HermitianMat.posSemidef_iff_spectrum_nonneg];
    rw [ HermitianMat.spectrum_cfc_eq_image ];
    rintro _ ⟨ x, hx, rfl ⟩ ; exact if hx0 : x = 0 then by
        simpa [ hx0 ] using hf₂ else hf x ( lt_of_le_of_ne ( h_pos x hx ) ( Ne.symm hx0 ) ) |>
        le_of_lt;
  have h_f_nonzero : A.cfc f ≠ 0 := by
    contrapose! h_f_pos;
    simp [h_f_pos, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Algebra.algebraMap_eq_smul_one]
  exact lt_of_le_of_ne h_f_nonneg h_f_nonzero.symm

set_option backward.isDefEq.respectTransparency false in
/-- If two matrices A and B commute, then they is a common matrix with which they are both CFCs of.
This is a variant of the common theorem that "commuting matrices can be simultaneously diagonalized." -/
theorem _root_.Commute.exists_HermitianMat_cfc (hAB : Commute A.mat B.mat) :
    ∃ C : HermitianMat d 𝕜, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

open ComplexOrder in
theorem cfc_le_cfc_of_PosDef (hfg : ∀ i, 0 < i → f i ≤ g i) (hA : A.mat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, cfc_nonneg_iff]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

open ComplexOrder in
variable {f} in
/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem cfc_le_cfc_of_commute_monoOn (hf : MonotoneOn f (Set.Ioi 0))
  (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, cfc_nonneg_iff] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [cfc_posDef] at hA
    exact hA i
  · rw [cfc_posDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem cfc_le_cfc_of_commute (hf : Monotone f) (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, cfc_nonneg_iff] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
open ComplexOrder in
theorem cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.mat.PosDef } := by
  exact False.elim hf_is_operator_convex

section uncategorized_cleanup

open ComplexOrder in
theorem inv_ge_one_of_le_one (hA : A.mat.PosDef) (h : A ≤ 1) : 1 ≤ A⁻¹ := by
  -- Since $A$ is positive definite and $A \leq 1$, we have $A.cfc (fun x => x⁻¹ - 1) \geq 0$.
  have h_cfc_nonneg : 0 ≤ A.cfc (fun x => x⁻¹ - 1) := by
    have h_cfc_nonneg : ∀ i, 0 ≤ (A.H.eigenvalues i)⁻¹ - 1 := by
      have h_pos : ∀ i, 0 < A.H.eigenvalues i ∧ A.H.eigenvalues i ≤ 1 := by
        -- Since $A$ is positive definite, all its eigenvalues are positive.
        have h_pos : ∀ i, 0 < A.H.eigenvalues i := by
          exact fun i => Matrix.PosDef.eigenvalues_pos hA i;
        -- Since $A \leq 1$, for any eigenvalue $\lambda_i$ of $A$, we have $\lambda_i \leq 1$.
        have h_le_one : ∀ i, A.H.eigenvalues i ≤ 1 := by
          have h_le_one : ∀ i, A.H.eigenvalues i ≤ 1 := by
            intro i
            have h_eigenvalue : A.mat.PosSemidef := by
              exact hA.posSemidef
            have h_eigenvalue_le_one : ∀ x : d → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.mat.mulVec x) / (star x ⬝ᵥ x) ≤ 1 := by
              intro x hx_ne_zero
              have h_eigenvalue_le_one : (star x ⬝ᵥ (1 - A.mat).mulVec x) ≥ 0 := by
                exact Matrix.PosSemidef.dotProduct_mulVec_nonneg h x
              generalize_proofs at *; (
              rw [ div_le_iff₀ ] <;> simp_all [ Matrix.sub_mulVec, dotProduct_sub ])
            generalize_proofs at *; (
            have := h_eigenvalue_le_one ( A.H.eigenvectorBasis i ) ?_ <;> simp_all [ div_le_iff₀,  ];
            · have := Matrix.IsHermitian.mulVec_eigenvectorBasis ( show Matrix.IsHermitian ( A : Matrix d d _ ) from ‹_› ) i; simp_all [ dotProduct_comm ] ;
              by_cases h : ( A.H.eigenvectorBasis i |> WithLp.ofLp ) ⬝ᵥ star ( A.H.eigenvectorBasis i |> WithLp.ofLp ) = 0 <;> simp_all [ div_le_iff₀ ] ; (
              exact absurd h ( by exact ne_of_apply_ne ( fun x => ‖x‖ ) ( by simp ) ));
            · exact fun h => by simpa [ h ] using ( A.H.eigenvectorBasis.orthonormal.ne_zero i ) ;)
          generalize_proofs at *; (
          exact h_le_one)
        exact fun i => ⟨h_pos i, h_le_one i⟩;
      exact fun i => sub_nonneg_of_le ( one_le_inv₀ ( h_pos i |>.1 ) |>.2 ( h_pos i |>.2 ) );
    exact (cfc_nonneg_iff A fun x => x⁻¹ - 1).mpr h_cfc_nonneg;
  -- Since $A.cfc (fun x => x⁻¹ - 1) \geq 0$, we have $A.cfc (fun x => x⁻¹) \geq 1$.
  have h_cfc_ge_one : A.cfc (fun x => x⁻¹) ≥ 1 := by
    have h_cfc_sub : A.cfc (fun x => x⁻¹ - 1) = A.cfc (fun x => x⁻¹) - A.cfc (fun _ => 1) := by
      exact cfc_sub_apply A Inv.inv fun x => 1;
    aesop;
  convert h_cfc_ge_one.le using 1;
  convert cfc_inv.symm;
  exact nonSingular_of_posDef hA

/-- The trace of cfc(f, A) equals the sum of f applied to eigenvalues. -/
lemma trace_cfc_eq (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    (A.cfc f).trace = ∑ i, f (A.H.eigenvalues i) := by
  have h1 := HermitianMat.trace_eq_trace (A.cfc f)
  obtain ⟨e, he⟩ := HermitianMat.cfc_eigenvalues f A
  have h2 := (A.cfc f).H.trace_eq_sum_eigenvalues
  rw [he] at h2
  simp [Function.comp] at h2
  rw [HermitianMat.mat_cfc] at h1
  rw [h2] at h1
  have h3 : (Complex.ofReal) (A.cfc f).trace = Complex.ofReal (∑ i, f (A.H.eigenvalues (e i))) := by
    convert! h1 using 1
    simp
  have h4 := Complex.ofReal_injective h3
  rw [h4]
  exact Equiv.sum_comp e (fun x => f (A.H.eigenvalues x))

end uncategorized_cleanup

lemma mulVec_eq_zero_iff_inner_eigenvector_zero
    (A : HermitianMat d ℂ) (x : EuclideanSpace ℂ d) :
    A.mat.mulVec x = 0 ↔ ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
  -- Since the eigenvectors form an orthonormal basis, we can express x as a linear combination of these eigenvectors.
  obtain ⟨c, hc⟩ : ∃ c : d → ℂ, x = ∑ i, c i • A.H.eigenvectorBasis i := by
    have := A.H.eigenvectorBasis.sum_repr x;
    exact ⟨ _, this.symm ⟩;
  -- By definition of $A$, we know that $A.mulVec (x.ofLp) = \sum_{i} c_i \lambda_i e_i$.
  have h_mulVec : A.val.mulVec (x.ofLp) = ∑ i, c i • (A.H.eigenvalues i) • (A.H.eigenvectorBasis i) := by
    have h_mulVec : ∀ i, A.val.mulVec (A.H.eigenvectorBasis i) = (A.H.eigenvalues i) • (A.H.eigenvectorBasis i) := by
      intro i
      have := A.H.mulVec_eigenvectorBasis i
      aesop;
    convert congr_arg ( fun y => ( ∑ i, c i • y i ) ) ( funext fun i => h_mulVec i ) using 1;
    · simp [ hc, ];
      ext i; rw [ Matrix.mulVec, dotProduct ]
      simp [ Finset.mul_sum _ _ _, mul_assoc, mul_comm ]
      rw [ Finset.sum_comm ]
      simp [ Matrix.mulVec, dotProduct, mul_comm, Finset.mul_sum _ _ _ ]
    · ext i; simp [ Finset.sum_apply ] ;
  constructor;
  · intro h i hi
    have h_inner : inner ℂ (A.H.eigenvectorBasis i) (∑ j, c j • (A.H.eigenvalues j) • (A.H.eigenvectorBasis j)) = 0 := by
      convert congr_arg ( fun x => inner ℂ ( A.H.eigenvectorBasis i ) x ) ( show ( ∑ j, c j • A.H.eigenvalues j • A.H.eigenvectorBasis j ) = 0 from ?_ ) using 1;
      · simp [ inner_zero_right ];
      · ext j; replace h := congr_fun h j; aesop;
    simp_all
    convert congr_arg ( fun x : ℂ => x / ( A.H.eigenvalues i ) ) h_inner using 1 <;> norm_num [ Finset.sum_div _ _ _, hi ];
    refine' Finset.sum_congr rfl fun j _ => _ ; by_cases hj : A.H.eigenvalues j = 0 <;> simp_all [ mul_div_assoc ] ; ring_nf;
    · by_cases hij : i = j <;> simp_all [ ];
    · by_cases hij : i = j <;> simp_all [  inner_self_eq_norm_sq_to_K ];
  · intro h
    have h_zero_coeffs : ∀ i, A.H.eigenvalues i ≠ 0 → c i = 0 := by
      intro i hi; specialize h i hi; simp_all
      rw [ Finset.sum_eq_single i ] at h <;> simp_all [ orthonormal_iff_ite.mp ( A.H.eigenvectorBasis.orthonormal ) ];
      aesop;
    simp_all
    exact Finset.sum_eq_zero fun i _ => by by_cases hi : A.H.eigenvalues i = 0 <;> simp [ hi, h_zero_coeffs i ] ;

open InnerProductSpace in
lemma cfc_mulVec_expansion (A : HermitianMat d ℂ) (f : ℝ → ℝ) (x : EuclideanSpace ℂ d) :
    (A.cfc f).mat.mulVec x = ∑ i, (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x • A.H.eigenvectorBasis i := by
  ext i; simp [ Matrix.mulVec, dotProduct ] ; ring_nf
  -- By definition of $cfc$, we know that $(A.cfc f).i j = \sum_k f(\lambda_k) \langle e_k, e_i \rangle \langle e_j, e_k \rangle$.
  have h_cfc_def : (A.cfc f).mat i = ∑ k, f (A.H.eigenvalues k) • (A.H.eigenvectorBasis k).ofLp i • star (A.H.eigenvectorBasis k).ofLp := by
    -- By definition of $cfc$, we know that $(A.cfc f).i j = \sum_k f(\lambda_k) \langle e_k, e_i \rangle \langle e_j, e_k \rangle$ follows directly from the definition of $cfc$.
    have h_cfc_def : (A.cfc f).mat = ∑ k, f (A.H.eigenvalues k) • (A.H.eigenvectorUnitary.val * (Matrix.single k k 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
      convert cfc_toMat_eq_sum_smul_proj A f using 1;
    convert congr_fun h_cfc_def i using 1;
    simp [ funext_iff, Matrix.single ];
    simp [ Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, mul_assoc ];
    intro x; congr; ext y; simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ] ; ring_nf
    rw [ Finset.sum_eq_single y ] <;> aesop;
  simp_all [mul_comm, mul_left_comm ] ; ring_nf
  convert! congr_arg ( fun y => ∑ j, x.ofLp j * y j ) h_cfc_def using 1
  simp [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ]
  ring_nf!
  rw [ Finset.sum_comm, Finset.sum_congr rfl ]
  intros
  simp [ mul_assoc, inner ]
  ring_nf!
  simp only [Finset.mul_sum _ _ _, mul_assoc]

section ker_cfc

variable {A : HermitianMat d ℂ} {f : ℝ → ℝ} {s : Set ℝ}

lemma ker_cfc_le_ker_on_set
    (hs : spectrum ℝ A.mat ⊆ s)
    (h : ∀ i ∈ s, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  intro x hx
  have h_inner : ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    have h_inner_zero : (A.cfc f).mat.mulVec x = 0 := by
      exact (mem_ker_iff_mulVec_zero (A.cfc f) x).mp hx
    have h_inner_zero_expansion : ∑ i, (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x • A.H.eigenvectorBasis i = 0 := by
      convert h_inner_zero using 1;
      rw [ cfc_mulVec_expansion ];
      exact Iff.symm (WithLp.ofLp_eq_zero 2)
    have h_inner_zero_coeff : ∀ i, f (A.H.eigenvalues i) • inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
      intro i
      have h_inner_zero_coeff_i : f (A.H.eigenvalues i) • inner ℂ (A.H.eigenvectorBasis i) x = inner ℂ (A.H.eigenvectorBasis i) (∑ j, (f (A.H.eigenvalues j) : ℂ) • inner ℂ (A.H.eigenvectorBasis j) x • A.H.eigenvectorBasis j) := by
        simp [  orthonormal_iff_ite.mp ( A.H.eigenvectorBasis.orthonormal ) ]
      rw [h_inner_zero_coeff_i, h_inner_zero_expansion]
      simp [inner_zero_right] -- This line is just to prevent the proof from being completed prematurely. In a real proof, this line would be replaced with the actual proof steps.
    have h_inner_zero_final : ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
      -- Since $A.H.eigenvalues i \neq 0$, by hypothesis $h$, we have $f(A.H.eigenvalues i) \neq 0$.
      have h_f_nonzero : ∀ i, A.H.eigenvalues i ≠ 0 → f (A.H.eigenvalues i) ≠ 0 := by
        intro i hi; specialize h ( A.H.eigenvalues i ) ( hs <| by
          exact Matrix.IsHermitian.eigenvalues_mem_spectrum_real (H A) i ) ; contrapose! hi; aesop;
      generalize_proofs at *; (
      exact fun i hi => by simpa [ h_f_nonzero i hi ] using h_inner_zero_coeff i;) -- This line is just to prevent the proof from being completed prematurely. In a real proof, this line would be replaced with the actual proof steps.
    exact h_inner_zero_final;
  convert mulVec_eq_zero_iff_inner_eigenvector_zero A x |>.2 h_inner using 1;
  exact mem_ker_iff_mulVec_zero A x

lemma ker_cfc_le_ker (h : ∀ i, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  exact ker_cfc_le_ker_on_set (Set.subset_univ _) (by simpa using h)

lemma ker_cfc_le_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_cfc_le_ker_on_set hA h

lemma ker_le_ker_cfc_on_set (hs : spectrum ℝ A.mat ⊆ s) (h : ∀ i ∈ s, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  intro x hx
  have h_inner_zero : ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    intro i hi
    have h_inner_zero : A.mat.mulVec x = 0 := by
      exact (mem_ker_iff_mulVec_zero A x).mp hx;
    have := mulVec_eq_zero_iff_inner_eigenvector_zero A x; aesop;
  have h_mulVec_zero : (A.cfc f).mat.mulVec x = ∑ i, (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x • A.H.eigenvectorBasis i := by
    convert cfc_mulVec_expansion A f x using 1;
  convert h_mulVec_zero using 1
  simp_all [ funext_iff] ;
  ext i; specialize h_mulVec_zero i; simp_all [ lin, Matrix.mulVec ] ;
  refine' Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : A.H.eigenvalues j = 0 <;> simp_all
  exact Or.inl ( h _ ( hs (Matrix.IsHermitian.eigenvalues_mem_spectrum_real (H A) j ) ) hj )

lemma ker_le_ker_cfc (h : ∀ i, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  exact ker_le_ker_cfc_on_set (Set.subset_univ _) (by simpa using h)

lemma ker_le_ker_cfc_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_le_ker_cfc_on_set hA h

theorem ker_cfc_eq_ker (h : ∀ i, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker ?_) (ker_le_ker_cfc ?_)
  <;> grind only

theorem ker_cfc_eq_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker_nonneg hA ?_) (ker_le_ker_cfc_nonneg hA ?_)
  <;> grind only

end ker_cfc
end CFC
