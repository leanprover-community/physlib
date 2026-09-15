/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.JensenOperatorInequality
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem

@[expose] public section

namespace GeneralizedPerspectiveFunction

universe u

open LownerHeinzTheorem
open JensenOperatorInequality

section Convexity

variable {E F G : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]
variable [Preorder G] [AddCommMonoid G] [Module ℝ G]

/-- Joint convexity of a two-variable map on prescribed domains in each argument. -/
def JointlyConvexOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂

/-- Joint convexity of a two-variable map without domain restrictions. -/
def JointlyConvex (Φ : E → F → G) : Prop :=
  JointlyConvexOn (Set.univ : Set E) (Set.univ : Set F) Φ

/-- Joint concavity of a two-variable map on prescribed domains in each argument. -/
def JointlyConcaveOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
      ≤ Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)

/-- Joint concavity of a two-variable map without domain restrictions. -/
def JointlyConcave (Φ : E → F → G) : Prop :=
  JointlyConcaveOn (Set.univ : Set E) (Set.univ : Set F) Φ

end Convexity

section Definition

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `h(B)^(1/2)` defined by real continuous functional calculus. -/
noncomputable def hSqrt (h : ℝ → ℝ) (B : L ℋ) : L ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) B

/-- The operator `h(B)^(-1/2)` defined by real continuous functional calculus. -/
noncomputable def hInvSqrt (h : ℝ → ℝ) (B : L ℋ) : L ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) B

/--
The generalized perspective function
`(fΔh)(A, B) = h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2)`.

This definition is intended to be used when `A` is Hermitian and `h(B)` is positive/invertible.
-/
noncomputable def GeneralizedPerspective (f h : ℝ → ℝ) (A B : L ℋ) : L ℋ :=
  hSqrt h B * cfcR f (hInvSqrt h B * A * hInvSqrt h B) * hSqrt h B

/-- Infix notation for generalized perspective: `(f Δ h) A B = GeneralizedPerspective f h A B`. -/
scoped infixl:70 " Δ " => GeneralizedPerspective

end Definition

section Theorem25Forward

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- Positive semidefinite operators. -/
def psdSet : Set (L ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ici (0 : ℝ)}

/-- Strictly positive operators. -/
def pdSet : Set (L ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)}

private lemma spectrum_convexCombo_Ioi {A B : L ℋ} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      simpa [rC] using
        add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

omit [Nontrivial ℋ] in
private lemma cfcR_sq_eq {g k : ℝ → ℝ} {A : L ℋ}
    (hA : IsSelfAdjoint A)
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = 1) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = (1 : L ℋ) := by
  rw [← cfc_mul (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
      (f := g) (g := k) (a := A) hg hk, ← cfc_const_one ℝ A]
  apply cfc_congr
  intro x hx
  simpa using hmul x hx

omit [Nontrivial ℋ] in
private lemma cfcR_mul_eq {g k m : ℝ → ℝ} {A : L ℋ}
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = m x) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = cfcR (ℋ := ℋ) m A := by
  rw [← cfc_mul (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
      (f := g) (g := k) (a := A) hg hk]
  apply cfc_congr
  intro x hx
  simpa using hmul x hx

private lemma hpow_continuousOn
    (h : ℝ → ℝ) (p : ℝ)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    ContinuousOn (fun x : ℝ ↦ (h x) ^ p) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hg : ContinuousWithinAt (fun y : ℝ ↦ y ^ p) (Set.Ioi (0 : ℝ)) (h x) :=
    (Real.continuousAt_rpow_const (h x) p (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  exact hg.comp (hcont x hx) (by
    intro y hy
    exact hpos y hy)

omit [Nontrivial ℋ] in
private lemma hSqrt_selfAdjoint (h : ℝ → ℝ) (B : L ℋ) :
    IsSelfAdjoint (hSqrt (ℋ := ℋ) h B) := by
  dsimp [hSqrt, cfcR]
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hInvSqrt_selfAdjoint (h : ℝ → ℝ) (B : L ℋ) :
    IsSelfAdjoint (hInvSqrt (ℋ := ℋ) h B) := by
  dsimp [hInvSqrt, cfcR]
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hInvSqrt_eq_one
    {h : ℝ → ℝ} {B : L ℋ}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hInvSqrt (ℋ := ℋ) h B = (1 : L ℋ) := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hinv :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((-1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((1 : ℝ) / 2) * (h x) ^ ((-1 : ℝ) / 2) = 1 := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt, hInvSqrt] using cfcR_sq_eq (ℋ := ℋ) (A := B) hB hsqrt hinv hmul

omit [Nontrivial ℋ] in
private lemma hInvSqrt_mul_hSqrt_eq_one
    {h : ℝ → ℝ} {B : L ℋ}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hInvSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = (1 : L ℋ) := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hinv :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((-1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((-1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = 1 := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt, hInvSqrt] using cfcR_sq_eq (ℋ := ℋ) (A := B) hB hinv hsqrt hmul

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hSqrt_eq
    {h : ℝ → ℝ} {B : L ℋ}
    (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = cfcR (ℋ := ℋ) h B := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = h x := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt] using cfcR_mul_eq (ℋ := ℋ) (A := B) hsqrt hsqrt hmul

omit [Nontrivial ℋ] in
private lemma conj_le_conj {X Y T : L ℋ} (hXY : X ≤ Y) (hT : IsSelfAdjoint T) :
    T * X * T ≤ T * Y * T := by
  have hnonneg : 0 ≤ Y - X := sub_nonneg.mpr hXY
  have hconj : 0 ≤ T * (Y - X) * T := by
    simpa using hT.conjugate_nonneg hnonneg
  have hsub : T * (Y - X) * T = T * Y * T - T * X * T := by
    simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
  exact sub_nonneg.mp (by simpa [hsub] using hconj)

-- The generalized-perspective normalization expands several nested CFC products.
private theorem theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    {f h : ℝ → ℝ}
    (hcoreV : CondV (ℋ := ℋ) f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  rcases hA₁ with ⟨hA₁_sa, hA₁_spec⟩
  rcases hA₂ with ⟨hA₂_sa, hA₂_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  let A : L ℋ := (1 - θ) • A₁ + θ • A₂
  let B : L ℋ := (1 - θ) • B₁ + θ • B₂
  have hA₁_nonneg : (0 : L ℋ) ≤ A₁ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₁ (ha := hA₁_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₁_spec hx
  have hA₂_nonneg : (0 : L ℋ) ≤ A₂ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₂ (ha := hA₂_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₂_spec hx
  have hB_sa : IsSelfAdjoint B := by
    dsimp [B]
    simpa using (IsSelfAdjoint.all (1 - θ)).smul hB₁_sa |>.add ((IsSelfAdjoint.all θ).smul hB₂_sa)
  have hB_spec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_convexCombo_Ioi (ℋ := ℋ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
  have hB_conc :
      (1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂ ≤ cfcR (ℋ := ℋ) h B := by
    have hconc' := hconc
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc'
    have hneg :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B ≤
          (1 - θ) • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₁ +
            θ • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₂ := by
      simpa [B] using
        hconc' (A := B₁) (B := B₂) (t := θ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
    simpa [cfcR, cfc_neg, smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using
      neg_le_neg hneg
  let S : L ℋ := hSqrt (ℋ := ℋ) h B
  let IR : L ℋ := hInvSqrt (ℋ := ℋ) h B
  let S₁ : L ℋ := hSqrt (ℋ := ℋ) h B₁
  let S₂ : L ℋ := hSqrt (ℋ := ℋ) h B₂
  let IR₁ : L ℋ := hInvSqrt (ℋ := ℋ) h B₁
  let IR₂ : L ℋ := hInvSqrt (ℋ := ℋ) h B₂
  let T₁ : L ℋ := Real.sqrt (1 - θ) • (S₁ * IR)
  let T₂ : L ℋ := Real.sqrt θ • (S₂ * IR)
  let M₁ : L ℋ := IR₁ * A₁ * IR₁
  let M₂ : L ℋ := IR₂ * A₂ * IR₂
  have hS_sa : IsSelfAdjoint S := hSqrt_selfAdjoint (ℋ := ℋ) h B
  have hIR_sa : IsSelfAdjoint IR := hInvSqrt_selfAdjoint (ℋ := ℋ) h B
  have hS₁_sa : IsSelfAdjoint S₁ := hSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hS₂_sa : IsSelfAdjoint S₂ := hSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hIR₁_sa : IsSelfAdjoint IR₁ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hIR₂_sa : IsSelfAdjoint IR₂ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hSIR : S * IR = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hIRS : IR * S = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hS₁IR₁ : S₁ * IR₁ = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hIR₁S₁ : IR₁ * S₁ = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hS₂IR₂ : S₂ * IR₂ = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hIR₂S₂ : IR₂ * S₂ = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hM₁_nonneg : (0 : L ℋ) ≤ M₁ := by
    dsimp [M₁]
    simpa [mul_assoc] using hIR₁_sa.conjugate_nonneg hA₁_nonneg
  have hM₂_nonneg : (0 : L ℋ) ≤ M₂ := by
    dsimp [M₂]
    simpa [mul_assoc] using hIR₂_sa.conjugate_nonneg hA₂_nonneg
  have hM₁_sa : IsSelfAdjoint M₁ := IsSelfAdjoint.of_nonneg hM₁_nonneg
  have hM₂_sa : IsSelfAdjoint M₂ := IsSelfAdjoint.of_nonneg hM₂_nonneg
  have hM₁_spec : spectrum ℝ M₁ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₁_nonneg hx
  have hM₂_spec : spectrum ℝ M₂ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₂_nonneg hx
  have hT₁ :
      star T₁ * T₁ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
    calc
      star T₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) • (IR * (S₁ * S₁) * IR) := by
              simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * S₁) * IR) := by
              rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₁) hB₁_spec hcont hpos]
  have hT₂ :
      star T₂ * T₂ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
    calc
      star T₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) • (IR * (S₂ * S₂) * IR) := by
              simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * S₂) * IR) := by
              rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₂) hB₂_spec hcont hpos]
  have hTsum : star T₁ * T₁ + star T₂ * T₂ ≤ (1 : L ℋ) := by
    rw [hT₁, hT₂]
    have hmid :
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
          ≤ IR * cfcR (ℋ := ℋ) h B * IR := by
      calc
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
            = IR * ((1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂) * IR := by
                simp [mul_add, add_mul, mul_assoc]
        _ ≤ IR * cfcR (ℋ := ℋ) h B * IR := conj_le_conj (ℋ := ℋ) hB_conc hIR_sa
    have hunit : IR * cfcR (ℋ := ℋ) h B * IR = (1 : L ℋ) := by
      calc
        IR * cfcR (ℋ := ℋ) h B * IR = IR * (S * S) * IR := by
          rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B) hB_spec hcont hpos]
        _ = (IR * S) * (S * IR) := by simp [mul_assoc]
        _ = 1 := by simp [hIRS, hSIR]
    exact hmid.trans_eq hunit
  have hterm₁ :
      star T₁ * M₁ * T₁ = (1 - θ) • (IR * A₁ * IR) := by
    calc
      star T₁ * M₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
                simp [T₁, M₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * A₁ * IR) := by
            rw [show IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR =
                IR * (((S₁ * IR₁) * A₁) * (IR₁ * S₁)) * IR by simp [mul_assoc]]
            rw [hS₁IR₁, hIR₁S₁]
            simp [mul_assoc]
  have hterm₂ :
      star T₂ * M₂ * T₂ = θ • (IR * A₂ * IR) := by
    calc
      star T₂ * M₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) •
              (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
                simp [T₂, M₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * A₂ * IR) := by
            rw [show IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR =
                IR * (((S₂ * IR₂) * A₂) * (IR₂ * S₂)) * IR by simp [mul_assoc]]
            rw [hS₂IR₂, hIR₂S₂]
            simp [mul_assoc]
  have hleft_inner :
      star T₁ * M₁ * T₁ + star T₂ * M₂ * T₂ = IR * A * IR := by
    rw [hterm₁, hterm₂]
    simp [A, mul_add, add_mul, mul_assoc]
  have hcore :=
    hcoreV (A := M₁) (B := M₂) (X := T₁) (Y := T₂) hM₁_sa hM₂_sa hM₁_spec hM₂_spec hTsum
  have houter := conj_le_conj (ℋ := ℋ) hcore hS_sa
  rw [hleft_inner] at houter
  have hright₁ :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) := by
    calc
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
                simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = (1 - θ) • ((f Δ h) A₁ B₁) := by
            rfl
  have hright₂ :
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        θ • ((f Δ h) A₂ B₂) := by
    calc
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S
          = (Real.sqrt θ * Real.sqrt θ) •
              (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
                simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = θ • ((f Δ h) A₂ B₂) := by
            rfl
  have hright :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁ + star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) + θ • ((f Δ h) A₂ B₂) := by
    rw [mul_add, add_mul, hright₁, hright₂]
  have hleft :
      S * cfcR (ℋ := ℋ) f (IR * A * IR) * S = (f Δ h) A B := by
    rfl
  simpa [hleft, hright] using houter

-- Restricted forward form of Theorem 2.5 on the positive cone.
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd
    {f h : ℝ → ℝ}
    (hf : CondIAll.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hcoreV : CondV (ℋ := ℋ) f :=
    theorem_2_5_2_i_all_imp_v (ℋ := ℋ) (f := f) hf
  exact theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    (ℋ := ℋ) (f := f) (h := h) hcoreV hconc hcont hpos

-- Restricted localized forward form of Theorem 2.5 on the positive cone.
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
    {f h : ℝ → ℝ}
    (hf : CondIciAll.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hcoreV : CondV (ℋ := ℋ) f :=
    theorem_2_5_2_i_ici_all_imp_v (ℋ := ℋ) (f := f) hf
  exact theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    (ℋ := ℋ) (f := f) (h := h) hcoreV hconc hcont hpos

omit [Nontrivial ℋ] in
private lemma generalizedPerspective_neg
    (f h : ℝ → ℝ) (A B : L ℋ) :
    ((fun x : ℝ ↦ -f x) Δ h) A B = -((f Δ h) A B) := by
  simp [GeneralizedPerspective, cfcR, cfc_neg, mul_assoc]

omit [Nontrivial ℋ] in
private lemma jointlyConvexOn_neg
    {s : Set (L ℋ)} {t : Set (L ℋ)} {Φ : L ℋ → L ℋ → L ℋ}
    (hΦ : JointlyConvexOn s t (fun A B ↦ -Φ A B)) :
    JointlyConcaveOn s t Φ := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hneg := hΦ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hneg' :
      -Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) ≤
        -((1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂) := by
    simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hneg
  exact (neg_le_neg_iff.mp hneg')

/-- Restricted forward form of Corollary 2.6 on the positive cone. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveAll.{u} f)
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hfneg : CondIAll.{u} (fun x : ℝ ↦ -f x) := by
    refine ⟨?_, ?_⟩
    · intro K _ _ _ _
      exact (hfconc (K := K))
    · simpa using (neg_nonpos.mpr hf0)
  have hconv_neg :
      JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
        (fun A B ↦ -((f Δ h) A B)) := by
    simpa [generalizedPerspective_neg] using
      (theorem_2_5_forward_jointlyConvexOn_psd_pd
        (ℋ := ℋ) (f := fun x : ℝ ↦ -f x) (h := h) hfneg hconc hcont hpos)
  exact jointlyConvexOn_neg (ℋ := ℋ) hconv_neg

/-- Restricted localized forward form of Corollary 2.6 on the positive cone. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hfcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hfneg : CondIciAll.{u} (fun x : ℝ ↦ -f x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K _ _ _ _
      exact (hfconc (K := K))
    · exact hfcont.neg
    · simpa using (neg_nonpos.mpr hf0)
  have hconv_neg :
      JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
        (fun A B ↦ -((f Δ h) A B)) := by
    simpa [generalizedPerspective_neg] using
      (theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
        (ℋ := ℋ) (f := fun x : ℝ ↦ -f x) (h := h) hfneg hconc hcont hpos)
  exact jointlyConvexOn_neg (ℋ := ℋ) hconv_neg

end Theorem25Forward

-- GeneralizedPerspectiveFunction Page 1 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- For any qudit ℋ, any A ∈ Herm(ℋ), any B ∈ Pd(ℋ),
-- any real-valued continuous function f, any positive-valued continuous function h>0,
-- (fΔh)(A,B) := h(B)^{1/2} f(h(B)^{-1/2} A h(B)^{-1/2}) h(B)^{1/2}

-- Theorem 2.5 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≤ 0, and h is a continuous function with h > 0.
-- If f is operator convex and h is operator concave,
-- then fΔh is jointly convex

end GeneralizedPerspectiveFunction

-- Corollary 2.6 https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≥ 0, and h is a continuous function with h > 0.
-- If f is operator convcave and h is operator concave,
-- then fΔh is jointly concave
