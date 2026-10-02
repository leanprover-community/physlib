/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.CandidateGenerator

/-!

# The unitary group preserves the domain of its generator

## i. Overview

A strongly continuous unitary group preserves the domain of its candidate generator `T` and commutes
with it there. So the orbit of a vector in the domain is differentiable at every time `s`, with
derivative `i T (U s ψ)`.

## ii. Key results

- `stoneCandidateDomain_translate` : the group preserves the domain.
- `stoneCandidateGenerator_translate` : the generator commutes with the group.
- `stoneCandidateGenerator_hasDerivAt` : orbits of domain vectors are differentiable at every time.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

omit [CompleteSpace H] in
include hUmul in
/-- `U t (U s ψ)` and `U s (U t ψ)` agree as functions of `s`, since `s + t = t + s`. -/
lemma stoneCandidateGenerator_translate_comm (ψ : H) (t : ℝ) :
    (fun s : ℝ => (U t : H →L[ℂ] H) (U s ψ)) = (fun s : ℝ => (U s : H →L[ℂ] H) (U t ψ)) := by
  funext s
  have h1 : (U t : H →L[ℂ] H) (U s ψ) = U (t + s) ψ := by
    rw [hUmul t s, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have h2 : (U s : H →L[ℂ] H) (U t ψ) = U (s + t) ψ := by
    rw [hUmul s t, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [h1, h2, add_comm t s]

omit [CompleteSpace H] in
include hUmul in
/-- If `ψ`'s orbit is differentiable at `0` with witness `φ`, then `U t ψ`'s orbit is again
differentiable at `0`, with witness `U t φ` — the group law turns the fixed continuous linear map
`U t` applied to `ψ`'s derivative witness into a derivative witness for `U t ψ`. -/
lemma stoneCandidateGenerator_translate_hasDerivAt {ψ φ : H} (t : ℝ)
    (hφ : HasDerivAt (fun s : ℝ => U s ψ) φ 0) :
    HasDerivAt (fun s : ℝ => U s (U t ψ)) (U t φ) 0 := by
  let L' : H →L[ℝ] H := (U t).restrictScalars ℝ
  have hconst : HasDerivAt (fun _ : ℝ => L') 0 0 := hasDerivAt_const 0 L'
  have happly := hconst.clm_apply hφ
  have happly' : HasDerivAt (fun s : ℝ => (U t : H →L[ℂ] H) (U s ψ)) (U t φ) 0 := by
    simpa [L'] using happly
  rw [stoneCandidateGenerator_translate_comm hUmul ψ t] at happly'
  exact happly'

omit [CompleteSpace H] in
include hUmul in
/-- The candidate domain is invariant under every `U t`. -/
lemma stoneCandidateDomain_translate {ψ : H} (hψ : stoneCandidateDomainPred (U := U) ψ)
    (t : ℝ) : stoneCandidateDomainPred (U := U) (U t ψ) := by
  obtain ⟨φ, hφ⟩ := hψ
  exact ⟨U t φ, stoneCandidateGenerator_translate_hasDerivAt hUmul t hφ⟩

omit [CompleteSpace H] in
include hUmul in
/-- The candidate domain, packaged as a `Submodule`-invariance statement under every `U t`. -/
lemma stoneCandidateDomain_translate_mem (ψ : stoneCandidateDomain (U := U) hUmul) (t : ℝ) :
    (U t (ψ : H)) ∈ stoneCandidateDomain (U := U) hUmul :=
  stoneCandidateDomain_translate hUmul ψ.property t

omit [CompleteSpace H] in
include hUmul in
/-- The candidate generator commutes with the group it was built from: for `ψ` in `T.domain`,
`U t ψ` is again in `T.domain`, and `T (U t ψ) = U t (T ψ)`. -/
lemma stoneCandidateGenerator_translate (ψ : stoneCandidateDomain (U := U) hUmul) (t : ℝ) :
    stoneCandidateGenerator (U := U) hUmul
        ⟨U t (ψ : H), stoneCandidateDomain_translate_mem hUmul ψ t⟩ =
      U t (stoneCandidateGenerator (U := U) hUmul ψ) := by
  set φ := stoneCandidateDeriv hUmul ψ with hφ_def
  have hφ : HasDerivAt (fun s : ℝ => U s (ψ : H)) φ 0 := stoneCandidateDeriv_spec hUmul ψ
  have htψ : HasDerivAt (fun s : ℝ => U s (U t (ψ : H))) (U t φ) 0 :=
    stoneCandidateGenerator_translate_hasDerivAt hUmul t hφ
  have hderiv_eq : stoneCandidateDeriv hUmul
      ⟨U t (ψ : H), stoneCandidateDomain_translate_mem hUmul ψ t⟩ = U t φ :=
    HasDerivAt.unique
      (stoneCandidateDeriv_spec hUmul ⟨U t (ψ : H), stoneCandidateDomain_translate_mem hUmul ψ t⟩)
      htψ
  show (-Complex.I) • stoneCandidateDeriv hUmul
      ⟨U t (ψ : H), stoneCandidateDomain_translate_mem hUmul ψ t⟩ = U t ((-Complex.I) • φ)
  rw [hderiv_eq, map_smul]

omit [CompleteSpace H] in
include hUmul in
/-- The orbit of a domain vector is differentiable at every time `s`, with derivative `i T (U s ψ)`.
-/
lemma stoneCandidateGenerator_hasDerivAt (ψ : stoneCandidateDomain (U := U) hUmul) (s : ℝ) :
    HasDerivAt (fun r : ℝ => U r (ψ : H))
      (Complex.I • U s (stoneCandidateGenerator (U := U) hUmul ψ)) s := by
  set φ := stoneCandidateDeriv hUmul ψ with hφ_def
  have hφ : HasDerivAt (fun r : ℝ => U r (ψ : H)) φ 0 := stoneCandidateDeriv_spec hUmul ψ
  have hshift : HasDerivAt (fun r : ℝ => U (r - s) (ψ : H)) φ s := by
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) s).sub_const s
    simpa [Function.comp_def] using hφ.scomp_of_eq s hsub (by ring)
  let L : H →L[ℂ] H := U s
  let L' : H →L[ℝ] H := L.restrictScalars ℝ
  have hconst : HasDerivAt (fun _ : ℝ => L') 0 s := hasDerivAt_const s L'
  have happly := hconst.clm_apply hshift
  have happly' : HasDerivAt (fun r : ℝ => L' (U (r - s) (ψ : H))) (L' φ) s := by
    simpa using happly
  have hcongr : HasDerivAt (fun r : ℝ => U r (ψ : H)) (L' φ) s := by
    apply happly'.congr_of_eventuallyEq
    filter_upwards [] with r
    show U r (ψ : H) = L' (U (r - s) (ψ : H))
    have hL'_eq : L' (U (r - s) (ψ : H)) = (U s : H →L[ℂ] H) (U (r - s) (ψ : H)) := rfl
    rw [hL'_eq]
    have hgroup := hUmul s (r - s)
    have hrs : s + (r - s) = r := by ring
    calc
      U r (ψ : H) = U (s + (r - s)) (ψ : H) := by rw [hrs]
      _ = (U s * U (r - s)) (ψ : H) := by rw [hgroup]
      _ = (U s : H →L[ℂ] H) (U (r - s) (ψ : H)) := by
            rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hLφ : L' φ = U s φ := rfl
  rw [hLφ] at hcongr
  have hTψ : stoneCandidateGenerator (U := U) hUmul ψ = (-Complex.I) • φ := rfl
  have : U s φ = Complex.I • U s (stoneCandidateGenerator (U := U) hUmul ψ) := by
    rw [hTψ, map_smul, smul_smul]
    norm_num
  rwa [this] at hcongr

end
end QuantumMechanics

end ProbabilisticTheory
