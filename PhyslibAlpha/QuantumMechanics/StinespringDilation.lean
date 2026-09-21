/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Physlib.Meta.TODO.Basic
public import Mathlib
/-!
# Stinespring dilation
-/

@[expose] public section
noncomputable section

TODO "There is a different version of the Stienspring dilation in
  `QuantumInfo.Channels.CPTP`. We should unify the the version here with that one.
  Some of the definitions here are more general then the ones in `QuantumInfo` as they
  do not restrict to `ℂ`. This is something we should modify in `QuantumInfo`."

open Matrix MatrixOrder ComplexOrder RCLike TensorProduct Kronecker

/-- Completely positive map given by a (not necessarily minimal) Kraus family. -/
def krausApply {R : Type*} [Mul R] [Star R] [AddCommMonoid R]
    {q r : Type*} [Fintype q] [Fintype r]
    (K : r → Matrix q q R) (ρ : Matrix q q R) : Matrix q q R :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- Kraus operator preserves PSD property. -/
lemma krausApply.posSemidef {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [AddLeftMono R]
    {q r : Type*} [Fintype q] [Fintype r]
    (K : r → Matrix q q R)
    {ρ : Matrix q q R} (hρ : ρ.PosSemidef) :
    (krausApply K ρ).PosSemidef :=
  posSemidef_sum _ fun _ _ => hρ.mul_mul_conjTranspose_same _

/-- Quantum channel. -/
def QuantumChannel {R : Type*} [Mul R] [One R] [Star R] [AddCommMonoid R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q]
    (K : r → Matrix q q R) :=
  ∑ i, (K i)ᴴ * K i = 1

/-- Quantum operation.  -/
def QuantumOperation {R : Type*} [RCLike R]
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q]
    (K : r → Matrix q q R) := ∑ i, (K i)ᴴ * K i ≤ 1

/-- Density matrix. -/
def densityMatrix {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (d : Type*) [Fintype d] :=
  {ρ : Matrix d d R // ρ.PosSemidef ∧ ρ.trace = 1}

/-- Density matrices are closed under real convex combinations. -/
def densityMatrix.convexComb {R : Type*} [RCLike R]
    {d : ℕ} (ρ₀ ρ₁ : densityMatrix (Fin d) (R := R)) {t : R}
    (hp₀ : 0 ≤ t) (hp₁ : 0 ≤ 1 - t) : densityMatrix (Fin d) (R := R) :=
  ⟨t • ρ₀.1 + (1 - t) • ρ₁.1, by
  constructor
  · exact (ρ₀.2.1.smul hp₀).add (ρ₁.2.1.smul hp₁)
  · rw [trace_add, trace_smul, smul_eq_mul, trace_smul, ρ₀.2.2, ρ₁.2.2]
    simp⟩

/-- Also known as `partialTraceRight`. -/
def tr₂ {R : Type*} [Ring R] {m n m' : Type*} [Fintype n]
    (ρ : Matrix (m × n) (m' × n) R) : Matrix m m' R :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- `stinespringOp` is often written as `V`. -/
def stinespringOp {R : Type*} [Ring R]
    {m r : Type*} [Fintype r] [DecidableEq r]
  (K : r → Matrix m m R) : Matrix (m × r) m R :=
  let V₀ : Matrix (m × r) (m × Fin 1) R :=
    ∑ i, K i ⊗ₖ single i (0 : Fin 1) (1 : R)
  fun x y => V₀ x (y,0)

/-- Entrywise formula for the Stinespring isometry: its `((x₁, x₂), y)` entry is `K x₂ x₁ y`. -/
theorem stinespringOp_apply {R : Type*} [Ring R] {m r : Type*} [Fintype r] [DecidableEq r]
    (K : r → Matrix m m R) (x : m × r) (y : m) :
    stinespringOp K x y = K x.2 x.1 y := by
  unfold stinespringOp
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply]

/-- The Stinespring dilation. -/
def stinespringDilation {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (K : r → Matrix m m R)
    (ρ : Matrix m m R) :=
  let V := stinespringOp K;
  V * ρ * Vᴴ

/-- The partial trace of the Stinespring dilation. -/
def stinespringForm {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (K : r → Matrix m m R) :=
  fun ρ => tr₂ (stinespringDilation K ρ)

/-- A useful identity for Stinespring dilations. -/
lemma stinespringOp_adjoint_mul_self {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (K : r → Matrix m m R) :
    ∑ i, star K i * K i = (stinespringOp K)ᴴ * stinespringOp K := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Matrix.sum_apply]
  simp only [conjTranspose_apply]
  simp only [stinespringOp, Pi.star_apply, Matrix.mul_apply, star_apply, single, Fin.isValue,
    Matrix.sum_apply, kroneckerMap_apply, of_apply, and_true, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte];
  erw [ Finset.sum_product, Finset.sum_comm ]

/-- A useful identity for completely positive, trace non-increasing maps. -/
lemma stinespringForm_CPTNI {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (K : r → Matrix m m R)
  (hK : ∑ i, (K i)ᴴ * K i ≤ 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) ≤ 1 := by
  convert hK
  rw [← stinespringOp_adjoint_mul_self]
  rfl

/-- The Stinespring operator of a completely positive, trace-preserving maps
is an isometry. (Note that `stinespringOp K` is not a square matrix in general.) -/
lemma stinespringForm_CPTP_isometry {R : Type*} [Ring R] [StarRing R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
  {K : r → Matrix m m R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) :
  (stinespringOp K)ᴴ * (stinespringOp K) = 1 := by
  rw [← hK]
  rw [← stinespringOp_adjoint_mul_self]
  rfl

/--
Proving the columns of `V = stinespringOp K` are independent is a step
on the way to constructing the unitary dilation. -/
lemma stinespringOrtho {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
  Orthonormal (𝕜 := R)
      fun j : m => WithLp.toLp 2 fun i : m × r => stinespringOp K i j := by
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    have h₁ : (((stinespringOp K)ᴴ * stinespringOp K) i j)
      = ((1 : Matrix m m R) i j) := by
      rw [stinespringForm_CPTP_isometry hK]
    rw [mul_apply] at h₁
    by_cases g₀ : i = j
    · subst i
      simp only [conjTranspose_apply, star_def, one_apply_eq] at h₁
      rw [← h₁]
      simp only [inner_self_eq_norm_sq_to_K]
      generalize stinespringOp K = α
      simp only [↓reduceIte]
      simp_rw [RCLike.conj_mul]
      norm_cast
      exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 fun i ↦ α i j)
    · rw [ite_eq_right g₀]
      have : (1 : Matrix m m R) i j = 0 := by
        exact one_apply_ne' fun a ↦ g₀ (id (Eq.symm a))
      rw [this] at h₁
      rw [← h₁]
      simp only [inner, conjTranspose_apply, star_def]
      congr
      ext x
      ring_nf

/-- `m` will of course be finite and bounded by `n` here,
but no need to assume or prove that.
-/
lemma basisCard {R : Type*} [RCLike R] {n m : Type*} [Fintype n] {s : Matrix n m R}
    (ho : Orthonormal R fun j ↦ WithLp.toLp 2 fun i ↦ s i j) :
    Fintype.card n =
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  Fintype.card_coe _ ▸ (Nat.cast_inj.mp  <|
    (rank_eq_card_basis <| PiLp.basisFun _ _ _).symm.trans <|
     rank_eq_card_basis
    ho.toSubtypeRange.exists_orthonormalBasis_extension.choose_spec.choose.toBasis)

/-- Calculating the cardinality of the orthonormal basis obtained by
extending the Stinespring orthonormal set, the columns of `stinespringOp K`. -/
lemma stinespringCard {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {K : r → Matrix m m R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    Fintype.card (m × r) = (stinespringOrtho
    hK).toSubtypeRange.exists_orthonormalBasis_extension.choose.card :=
  basisCard <| stinespringOrtho hK



open Finset in
/-- We need the 1 matrix, which we don't seem to have for an arbitrary
`[Fintype m]`.
Since we are comparing `Fin r` and `Fin (r-1)` we also cannot too
easily use an arbitrary `[Fintype r] [Zero r]`.
-/
theorem complCard {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    let 𝓞 := fun j ↦ WithLp.toLp 2 fun i ↦ stinespringOp K i j;
    let theRange := Submodule.span R (Set.range 𝓞);
    let u' := (exists_orthonormalBasis R theRangeᗮ).choose;
      Fintype.card (Fin m × Fin (r-1)) = #u' := by
    obtain ⟨s,hs⟩ : ∃ s, r = s + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero ?_
      have := z.2
      omega
    subst hs
    intro 𝓞 theRange u'
    let u : Finset theRange :=
        (Set.range fun i => (⟨𝓞 i, Submodule.subset_span ⟨i, rfl⟩⟩)).toFinset
    have hind := (stinespringOrtho hK).linearIndependent
    have hinj := hind.injective
    have h₀ : #u = m := by
        simp only [u, Set.toFinset_range]
        have : m = #(Finset.univ : Finset (Fin m)) := by simp
        simp_rw [this]
        apply card_image_of_injective
        intro i j h
        apply hinj
        simp only [Subtype.mk.injEq, WithLp.toLp.injEq, 𝓞] at h ⊢
        exact h
    have h₁ : m * (s + 1) = #u + #u' := by
        have := Submodule.finrank_add_finrank_orthogonal theRange
        simp only [finrank_euclideanSpace, Fintype.card_prod,
          Fintype.card_fin] at this
        rw [← this]
        congr
        all_goals apply Module.finrank_eq_card_finset_basis
        · simp only [theRange, u, Set.toFinset_range, mem_image, mem_univ, true_and]
          apply (Module.Basis.span hind).reindex
          apply Equiv.ofBijective
            fun i => ⟨⟨𝓞 i, Submodule.mem_span_of_mem <| by simp [𝓞]⟩, by use i⟩
          constructor
          · intro i j h
            exact hinj (by aesop)
          · intro x
            have ⟨a,ha⟩ := x.2
            use a
            simp_rw [ha]
        · exact (exists_orthonormalBasis R _).choose_spec.choose.toBasis
    simp only [add_tsub_cancel_right, Fintype.card_prod, Fintype.card_fin]
    linarith

/--
See discussion at https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/succAbove.20and.20predAbove.20lemmas/with/584270574
-/
def Fin.predAboveOfNe {n : ℕ} {k i : Fin n}
    (h : i ≠ k) : Fin (n - 1) := by
  by_cases H : i.1 > k.1
  · exact ⟨i.1 - 1, by omega⟩
  · exact ⟨i.1, by omega⟩

/-- A "missing lemma" for `Fin` types. -/
lemma Fin.predAboveOfNe_injective (n : ℕ) (k x y : Fin n)
    (hx : x ≠ k) (hy : y ≠ k)
    (heq : Fin.predAboveOfNe hx = Fin.predAboveOfNe hy) : x = y := by
  unfold predAboveOfNe at heq
  split_ifs at heq
  all_goals
  · simp only [mk.injEq] at heq
    omega


/-- The way this is written, `Fin r` and `Fin (r-1)` both occur
so it is tricky to go to a general `Fintype`.
-/
def onbPart {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r) {z : Fin r} (hx : ¬x.2 = z) :
  -- if we make it `r+2` then the `x.2≠0` becomes unused.
  Fin m × Fin r → R := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    have (w : Fin m × Fin (r-1)) :=
        ((exists_orthonormalBasis R theRangeᗮ).choose_spec.choose
        (Finset.equivOfCardEq (complCard hK z) ⟨w, Finset.mem_univ _⟩)).1.1
    apply this
    exact (x.1, Fin.predAboveOfNe hx)

/- The custom in quantum information theory is to use
|e₁>< e₁| as ancillary; we allow an arbitrary (standard) basis vector.
-/
lemma onbPart_inner {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) {z : Fin r}
    {y : Fin m × Fin r} (hy : ¬y.2 = z)
    {x : Fin m × Fin r} (hx : ¬x.2 = z)
    (h : y ≠ x) :
    inner R (WithLp.toLp 2 <| onbPart hK y hy)
            (WithLp.toLp 2 <| onbPart hK x hx) = 0 := by
    let theRange := Submodule.span R <| Set.range
        fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    let α := (exists_orthonormalBasis R theRangeᗮ).choose_spec
    have := α.choose.orthonormal.2
    simp only [Pairwise, ne_eq, Submodule.coe_inner, Subtype.forall,
      Subtype.mk.injEq] at this
    have h₁ := this (WithLp.toLp 2 <| onbPart hK y hy)
        (by simp [onbPart]) (by
            simp only [onbPart, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp)
        (WithLp.toLp 2 <| onbPart hK x hx)
        (by simp [onbPart]) (by
            simp only [onbPart, WithLp.toLp_ofLp, Subtype.coe_eta]
            rw [α.choose_spec]
            simp) (by
                simp only [onbPart, WithLp.toLp_ofLp, SetLike.coe_eq_coe]
                rw [α.choose_spec]
                simp only [SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq,
                  Subtype.mk.injEq, Prod.mk.injEq, not_and]
                intro hyz
                contrapose! h
                have : y.2.1 ≠ z := Fin.val_ne_of_ne hy
                have : x.2.1 ≠ z := Fin.val_ne_of_ne hx
                have : y.2.1 = x.2.1 := by
                    suffices y.2 = x.2 by rw [this]
                    apply Fin.predAboveOfNe_injective
                    omega
                have : y.2 = x.2 := by omega
                exact Prod.ext hyz this)
    rw [← h₁]
    simp_rw [α.choose_spec]

/-- The vectors in the Stinespring orthonormal basis have norm 1. -/
lemma onbPart_norm {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (x : Fin m × Fin r)
    {z : Fin r} (hx : ¬x.2 = z) :
    ‖WithLp.toLp 2 <| onbPart hK x hx‖ = 1 :=
  let theRange := Submodule.span R <| Set.range
      fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
  (exists_orthonormalBasis R theRangeᗮ).choose_spec.choose.orthonormal.1 _



/-- Also known as `unitaryDilation`. Respects x,y order. -/
def Ud {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    Matrix (Fin m × Fin r) (Fin m × Fin r) R := by
  intro x y
  by_cases hy : y.2 = z
  · exact stinespringOp K x y.1
  · exact onbPart hK y hy x


/-- This generalization of Stinespring dilation has the right
"shape" but otherwise nothing specific to it. -/
def generalDilation {R : Type*}
    {m r : Type*} [DecidableEq r]
    (z : r)
    (S : Matrix (m × r) m R)
    (M : Matrix (m × r) (m × r) R) :
    Matrix (m × r) (m × r) R := fun x y =>
  ite (y.2 = z) (S x y.1) (M x y)


/-- A general, not necessarily unitary, dilation. -/
def dilation {R : Type*} [Ring R]
    {m r : Type*} [Fintype r] [DecidableEq r]
    (K : r → Matrix m m R) (z : r) (M : Matrix (m × r) (m × r) R) :
    Matrix (m × r) (m × r) R := generalDilation z (stinespringOp K) (M)



/-- One version of orthonormality of `stinespringOp`. -/
theorem Ud_orthonormal₁ {R : Type*} [RCLike R] {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    Orthonormal R fun y ↦ if hy : y.2 = z then WithLp.toLp 2 fun i ↦ stinespringOp K i y.1
    else WithLp.toLp 2 fun i ↦ onbPart hK y hy i := by
  constructor
  · intro i
    simp only
    split_ifs with g₀
    · apply (stinespringOrtho hK).1
    · apply onbPart_norm
  · intro i j h
    simp only
    let theRange := Submodule.span R <| Set.range
          fun j => WithLp.toLp 2 fun i ↦ stinespringOp K i j
    split_ifs with g₀ g₁ g₂
    · apply (stinespringOrtho hK).2
      contrapose! h
      refine Prod.ext_iff.mpr ?_
      constructor
      · tauto
      · rw [g₀,g₁]
    · -- use that they came from `theRange`, `theRangeᗮ` respectively.
      have h₀ : (WithLp.toLp 2 fun i_1 ↦ stinespringOp K i_1 i.1) ∈ theRange := by
          unfold theRange
          generalize stinespringOp K = α
          apply Submodule.mem_span_of_mem
          simp
      have h₁ : (WithLp.toLp 2 fun i ↦ onbPart hK j g₁ i) ∈ theRangeᗮ := by
          unfold theRange
          simp [onbPart]
      exact h₁ _ h₀
    · have h₀' : (WithLp.toLp 2 fun i_1 ↦ stinespringOp K i_1 j.1) ∈ theRange := by
          unfold theRange
          generalize stinespringOp K = α
          apply Submodule.mem_span_of_mem
          simp
      have h₁ :  (WithLp.toLp 2 fun t ↦ onbPart hK i g₀ t) ∈ theRangeᗮ := by
          unfold theRange
          simp [onbPart]
      have := h₁ _ h₀'
      generalize (WithLp.toLp 2 fun i_1 ↦ onbPart hK i g₀ i_1) = α at *
      generalize (WithLp.toLp 2 fun i ↦ stinespringOp K i j.1) = β at *
      exact inner_eq_zero_symm.mp (h₁ β h₀')
    · exact onbPart_inner hK g₀ g₂ h


/-- The Stinespring dilation columns form an orthonormal basis. -/
theorem Ud_orthonormal₂ {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
  (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    Orthonormal R fun y ↦
      WithLp.toLp 2 fun i ↦ if hy : y.2 = z then stinespringOp K i y.1 else onbPart hK y hy i := by
    have h₀ := Ud_orthonormal₁ hK z
    constructor
    · intro i
      have := h₀.1 i
      rw [← this]
      congr
      ext y
      simp only
      split_ifs with g₀ <;> simp
    · intro _ _ hij
      have := h₀.2 hij
      simp only at this ⊢
      rw [← this]
      split_ifs at * with g₀ g₁ <;> rfl

/-- If `β` has length 1 then the dot product of `β` with itself is 1. -/
lemma smul_self_one_of_norm_one {R : Type*} [RCLike R]
    {t : Type*} [Fintype t] {β : t → R} (hj : ‖WithLp.toLp 2 β‖ = 1) :
  ∑ x, (starRingEnd R) (β x) * β x = 1 := by
      refine Eq.symm ((fun {z w} ↦ RCLike.ext_iff.mpr) ?_)
      constructor
      · simp only [one_re, map_sum, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
        rw [← one_pow 2]
        rw [← hj]
        simp_rw [← RCLike.norm_sq_eq_def]
        exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 β)
      · simp only [one_im, map_sum, mul_im, conj_re, conj_im, neg_mul]
        symm
        apply Fintype.sum_eq_zero
        ring_nf
        simp

/-- A matrix whose columns are orthonormal is unitary. -/
theorem unitary_of_orthonormal {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    (α : Matrix (m × r) (m × r) R)
  (h₀ : Orthonormal R fun i ↦ WithLp.toLp 2 (α i)) : α * star α = 1 := by
    ext i j
    rw [mul_apply]
    apply star_injective
    simp only [star_apply, star_def, star_sum, star_mul', RingHomCompTriple.comp_apply,
      RingHom.id_apply]
    by_cases H : i = j
    · subst i
      simp only [one_apply_eq, map_one]
      exact smul_self_one_of_norm_one <| h₀.1 _
    · rw [one_apply_ne' <| H ∘ Eq.symm, map_zero]
      convert h₀.2 H
      simp only [inner]
      congr
      ext l
      nth_rw 1 [mul_comm]
      rfl

/-- The transpose of the unitary dilation is unitary. -/
lemma Ud_unitaryT {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    (Ud hK z)ᵀ ∈ unitary _ := by
  have H₀ := unitary_of_orthonormal (Ud hK z)ᵀ
    <| Ud_orthonormal₂ hK z
  constructor
  · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp H₀
  · exact H₀


/-- The unitary dilation `Ud` is in fact unitary. -/
lemma Ud_unitary {R : Type*} [RCLike R]
    {m r : ℕ} {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    (Ud hK z) ∈ unitary _ := by
     have := Ud_unitaryT hK z
     generalize Ud hK z = U at *
     have :  star U * U = 1 := by
       have := this.2
       have : (Uᵀ * star Uᵀ)ᵀ = 1ᵀ := transpose_inj.mpr this
       simp only [transpose_mul, transpose_transpose, transpose_one] at this
       have : (star Uᵀ)ᵀ = star U := by
         exact Eq.symm (Matrix.ext fun i ↦ congrFun rfl)
       rw [← this]
       tauto
     constructor
     · exact this
     · exact (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp this

open Kronecker TensorProduct

/-- Taking the partial trace of a tensor product with a matrix of trace 1 is the
identity map. -/
lemma tr₂_e₀Xe₀ {R : Type*} [RCLike R]
    {m w : Type*} [Fintype w]
    (e : Matrix w w R) (htr : e.trace = 1)
    (ρ : Matrix m m R) :
    tr₂ (ρ ⊗ₖ e) = ρ := by
  unfold tr₂ kroneckerMap
  simp only [of_apply]
  ext i j
  have :  ∑ x, ρ i j * e x x
    = ρ i j * ∑ x,  e x x := by  rw [Finset.mul_sum]
  rw [this]
  unfold trace at htr
  simp only [diag_apply] at htr
  rw [htr]
  simp

/-- The Stinespring unitary form. -/
def stinespringUnitaryForm {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r)
    (ρ : Matrix (Fin m) (Fin m) R) :
    (Matrix (Fin m) (Fin m) R) :=
    let U := Ud hK z
    tr₂ (U * (ρ ⊗ₖ (single z z 1)) * Uᴴ)

/-- The Stinespring unitary form, general version. -/
def stinespringUnitaryFormE {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) (e : Matrix (Fin r) (Fin r) R)
    (ρ : Matrix (Fin m) (Fin m) R) :
    (Matrix (Fin m) (Fin m) R) :=
    let U := Ud hK z
    tr₂ (U * (ρ ⊗ₖ e) * Uᴴ)

/-- Trace-free version of the Stinespring Dilation Theorem. -/
theorem tracefree_version {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    {K : r → Matrix m m R}
    (ρ : Matrix m m R) :
    let K' := fun i x y => star <| K i y x; let U := (stinespringOp K');
    Uᴴ * (ρ ⊗ₖ (1 : Matrix r r R)) * U = stinespringForm K ρ := by
  show (stinespringOp fun i => (K i)ᴴ)ᴴ * (ρ ⊗ₖ (1 : Matrix r r R)) *
      (stinespringOp fun i => (K i)ᴴ) = stinespringForm K ρ
  ext x y
  simp only [stinespringForm, stinespringDilation, tr₂, Matrix.mul_apply]
  simp only [conjTranspose_apply]
  simp only [stinespringOp_apply, conjTranspose_apply, star_star, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_comm

/-- A Heisberg picture / Schrödinger picture view of the Stinespring dilation. -/
theorem heisenberg_schrõdinger {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    {K : r → Matrix m m R}
    (ρ : Matrix m m R) :
  let K' := fun i x y => star <| K i y x
  let U := (stinespringOp K'); let V := stinespringOp K
  let schrõdinger := tr₂ (V * ρ * Vᴴ); -- evolve the state forward: V = V(t), ρ = ρ(0)
  let heisenberg := Uᴴ * (ρ ⊗ₖ (1 : Matrix r r R)) * U;
  -- ρ ⊗ₖ 1 is an "observable"; evolve it backward
    schrõdinger = heisenberg := by
    intro K' U
    rw [tracefree_version]
    rfl

/-- A further generalization of `stinespringGeneralForm`. -/
def generalForm {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (z : r)
    (S : Matrix (m × r) m R)
    (M : Matrix (m × r) (m × r) R) :=
    let U := generalDilation z S M
    fun ρ => tr₂ (U * (ρ ⊗ₖ (single z z 1)) * Uᴴ)

/-- General form of the Stinespring dilation. -/
def stinespringGeneralForm {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (K : r → Matrix m m R) (z : r)
    (M : Matrix (m × r) (m × r) R) :=
    let U := dilation K z M
    fun ρ => tr₂ (U * (ρ ⊗ₖ (single z z 1)) * Uᴴ)

/-- Even more general form of the Stinespring dilation. -/
def stinespringGeneralFormE {R : Type*} [RCLike R]
    {m r : Type*} [Fintype r] [DecidableEq r] [Fintype m]
    (K : r → Matrix m m R) (z : r) (e : Matrix r r R)
    (M : Matrix (m × r) (m × r) R) :=
    let U := dilation K z M
    fun ρ => tr₂ (U * (ρ ⊗ₖ e) * Uᴴ)


/-- When we plug in `M = Ud hK`
into the general `stinespringGeneralForm`,
then we do get
`stinespringUnitaryForm hK`.
-/
theorem unitaryForm_of_general {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    stinespringGeneralForm K z (Ud hK z) =
    stinespringUnitaryForm hK z := by
  have h : dilation K z (Ud hK z) = Ud hK z := by
    ext x y
    by_cases hy : y.2 = z <;> simp [dilation, generalDilation, Ud, hy]
  funext ρ
  simp only [stinespringGeneralForm, stinespringUnitaryForm]
  rw [h]

/-- The Stinespring unitary form as a general form applied to the unitary dilation. -/
theorem unitaryForm_of_general_e {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) (e : Matrix (Fin r) (Fin r) R) :
    stinespringGeneralFormE K z e (Ud hK z) =
    stinespringUnitaryFormE hK z e := by
  have h : dilation K z (Ud hK z) = Ud hK z := by
    ext x y
    by_cases hy : y.2 = z <;> simp [dilation, generalDilation, Ud, hy]
  funext ρ
  simp only [stinespringGeneralFormE, stinespringUnitaryFormE]
  rw [h]


/--
Note we don't need any special properties of M,
and we don't need K to be CPTP.

Uses `Fin` types because of the use of
`Fin.sum_univ_succAbove` in the proof.
-/
lemma stinespringGeneralForm_works {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) (z : Fin r)
    (M : Matrix (Fin m × Fin r) (Fin m × Fin r) R) :
    stinespringGeneralForm K z M = krausApply K := by
      funext ρ
      ext i j
      simp only [stinespringGeneralForm, krausApply, tr₂, Matrix.sum_apply, Matrix.mul_apply,
        conjTranspose_apply, Finset.sum_mul]
      simp [dilation, generalDilation, stinespringOp_apply, kroneckerMap_apply,
        Matrix.single_apply, apply_ite star, ite_and, Fintype.sum_prod_type, mul_ite, ite_mul,
        Finset.sum_ite_eq]
      simp only [@eq_comm _ z]
      have hite : ∀ (c : Prop) [Decidable c] (A B C : R),
          (if c then (if c then A else B) else (if c then C else 0)) = if c then A else 0 := by
        intro c _ A B C
        split_ifs <;> rfl
      simp_rw [hite]
      simp [Finset.sum_ite_eq']


/--
Notice that unitarity is a side property, it is not why
the Stinespring form works.

Here `z` is the coordinate used for the ancilla.
-/
lemma stinespringUnitaryForm_works {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r) :
    stinespringUnitaryForm hK z = krausApply K := by
  rw [← stinespringGeneralForm_works K z (Ud hK z) ]
  rw [unitaryForm_of_general]

/-- The "orthogonal" CPTP completion of a CPTNI map.
`Vtilde` is an alternative name for `krausCompletion`.
-/
def krausCompletion {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m × Fin (r+1)) (Fin m) R := fun x => dite (x.2 < r)
  (fun H => stinespringOp K ⟨x.1, ⟨x.2, H⟩⟩)
  fun _ => (CFC.sqrt (1 - (stinespringOp K)ᴴ * (stinespringOp K)) : Matrix _ _ _) x.1

/-- The Gram matrix of the Stinespring isometry is `∑ i, (K i)ᴴ * K i`. -/
theorem stinespringOp_gram {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) :
    (stinespringOp K)ᴴ * stinespringOp K = ∑ i, star (K i) * K i := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.conjTranspose_apply, stinespringOp_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x1 _
  simp [Matrix.star_apply]

/-- Mar 14, 2026 by Bjørn for 4.27
June 13, 2026 by Aristotle for 4.31 including
`stinespringOp_gram` and `stinespringOp_apply`. -/
lemma krausCompletion_isometry_of_TNI {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, star K i * K i ≤ 1) :
    (krausCompletion K)ᴴ * krausCompletion K = 1 := by
  set S := stinespringOp K with hS
  -- `Sᴴ * S = ∑ i, (K i)ᴴ * K i`, hence `1 - Sᴴ * S` is positive semidefinite.
  have hgram : Sᴴ * S = ∑ i, star (K i) * K i := stinespringOp_gram K
  have h0 : 0 ≤ 1 - Sᴴ * S := by rw [hgram]; exact sub_nonneg.mpr hK
  -- `W` is the (selfadjoint) square root of `1 - Sᴴ * S`, completing the isometry.
  set W := CFC.sqrt (1 - Sᴴ * S) with hW
  have hWsa : Wᴴ = W := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hWW : Wᴴ * W = 1 - Sᴴ * S := by
    rw [hWsa]; exact CFC.sqrt_mul_sqrt_self _ h0
  -- The first `r` blocks of the completion are the blocks of `S`.
  have hcast : ∀ (x : Fin m) (i : Fin r) (c : Fin m),
      krausCompletion K (x, i.castSucc) c = S (x, i) c := by
    intro x i c
    rw [hS]
    unfold krausCompletion
    rw [dite_eq_left (by exact i.isLt)]
    congr 1
  -- The last block of the completion is `W`.
  have hlast : ∀ (x : Fin m) (c : Fin m),
      krausCompletion K (x, Fin.last r) c = W x c := by
    intro x c
    rw [hW, hS]
    unfold krausCompletion
    rw [dite_eq_right (by simp)]
  -- `Cᴴ * C = Sᴴ * S + Wᴴ * W` by splitting the row sum into the first `r` blocks and the last.
  have key : (krausCompletion K)ᴴ * krausCompletion K = Sᴴ * S + Wᴴ * W := by
    ext a b
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    have hSsum : (∑ p : Fin m × Fin r, star (S p a) * S p b)
        = ∑ x, ∑ i, star (S (x, i) a) * S (x, i) b := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Fin.sum_univ_castSucc]
    rw [Finset.sum_add_distrib, hSsum]
    congr 1
    · apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro i _
      rw [hcast x i a, hcast x i b]
    · apply Finset.sum_congr rfl; intro x _
      rw [hlast x a, hlast x b]
  -- Finally `Sᴴ * S + Wᴴ * W = Sᴴ * S + (1 - Sᴴ * S) = 1`.
  rw [key, hWW]
  abel


/-- A unital operator. -/
def unital {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) := ∑ i, K i * star (K i) = 1

/-- A subunital operator. -/
def subunital {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R) := ∑ i, K i * star (K i) ≤ 1


/-- The identity `Tr_B (A ⨂ B) = Tr(B) · A` -/
lemma partialTrace_tensor {R : Type*} [RCLike R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    tr₂ (A ⊗ₖ B) = (trace B) • A  := by
  unfold tr₂ trace kroneckerMap
  simp only [of_apply, diag_apply]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have := @Finset.sum_mul (a := A i j) (ι := Fin n)
    (s := Finset.univ) (f := fun k => B k k) _ _
  rw [this]
  simp_rw [mul_comm]

/-- A unitary dilation view of the application of a Kraus operator. -/
lemma krausApply_of_tensor {R : Type*} [RCLike R] {m r : ℕ}
    {K : Fin r → Matrix (Fin m) (Fin m) R}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (z : Fin r)
    (ρ α : Matrix (Fin m) (Fin m) R) (β : Matrix (Fin r) (Fin r) R)
    (hβ : β.trace = 1) (h : (Ud hK z) * (ρ ⊗ₖ (single z z 1)) * (Ud hK z)ᴴ = α ⊗ₖ β) :
    krausApply K ρ = α := by
  rw [← stinespringUnitaryForm_works hK]
  · unfold stinespringUnitaryForm
    simp only
    rw [h]
    rw [partialTrace_tensor]
    rw [hβ]
    simp

/-- Trace of partial trace equals trace. -/
lemma trace_tr₂ {R : Type*} [RCLike R] {m n : ℕ}
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) R) :
    trace ρ = trace (tr₂ ρ) := Fintype.sum_prod_type fun x ↦ ρ x x


/-- The Kraus completion as a map from
operations to channels. -/
def krausCompletionChannelMap {R : Type*} [RCLike R] {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R} (hK : QuantumOperation K) :
    {K : Fin (r+1) → Matrix (Fin q) (Fin q) R | QuantumChannel K} := by
  constructor
  swap
  · exact fun i x => krausCompletion K (x, i)
  · unfold QuantumChannel
    rw [← krausCompletion_isometry_of_TNI hK]
    ext x y
    rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm, Matrix.sum_apply]
    congr


/-- The "not orthogonal" CPTP completion of a CPTNI map. -/
lemma CPTP_of_CPTNI {R : Type*} [RCLike R]
    {q r : ℕ}
    {K : Fin r → Matrix (Fin q) (Fin q) R}
    (hq : QuantumOperation K) :
    ∃ K' : Fin (r+1) → Matrix (Fin q) (Fin q) R,
    QuantumChannel K' ∧
    ∀ i, ∀ H : i ≠ Fin.last r, K' i = K ⟨i.1, Fin.val_lt_last H⟩ := by
  use (fun i x => krausCompletion K (x, i))
  constructor
  · exact (krausCompletionChannelMap hq).2
  · unfold krausCompletion stinespringOp
    simp only [ne_eq, Fin.isValue]
    intro i H
    split_ifs with g₀
    · unfold kroneckerMap single
      simp only [Fin.isValue, of_apply, mul_ite, mul_one, mul_zero]
      have (j : Fin q × Fin 1) : (0 = j.2) = True := by
        have := j.2.2
        simp only [Fin.isValue, eq_iff_iff, iff_true]
        omega
      simp_rw [this]
      ext a b
      erw [Finset.sum_apply]
      erw [Finset.sum_fn]
      simp
    · exact False.elim <| H <| Fin.eq_last_of_not_lt g₀

/-- Partial trace on the left of a tensor product. -/
def partialTraceLeft {R : Type*} [RCLike R]
    {m n : Type*} [Fintype m]
    (ρ : Matrix (m × n)
                (m × n) R) : Matrix (n) (n) R :=
fun i j => ∑ k : m, ρ (k, i) (k, j)

/-- A version of the Stinespring Dilation Theorem. -/
theorem stinespringForm_eq {R : Type*} [RCLike R] {m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin m) R)
    (ρ : Matrix (Fin m) (Fin m) R) :
    tr₂ (stinespringDilation K ρ) = krausApply K ρ := by
  ext i j
  simp only [tr₂, stinespringDilation, krausApply, Matrix.sum_apply, Matrix.mul_apply,
    conjTranspose_apply, stinespringOp_apply, Finset.sum_mul]
