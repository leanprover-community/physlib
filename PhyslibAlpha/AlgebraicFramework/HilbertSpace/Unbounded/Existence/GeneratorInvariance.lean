/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.CandidateGenerator

/-!
# The candidate Stone generator's domain is invariant under its own group

Toward the *reconstruction* half of Stone's theorem (`U t = exp(-it Hgen)`, not attempted by
`StoneGenerator.lean`, which only gives existence of `Hgen`): the first genuinely new
ingredient reconstruction needs is that the candidate generator `T := stoneCandidateGenerator
hUmul` commutes with the group it was built from, i.e. `U` preserves `T`'s domain and
`T (U t ψ) = U t (T ψ)` for `ψ ∈ T.domain`. Consequently `U`'s orbit through any `ψ ∈ T.domain` is
differentiable at *every* time, not just `t = 0`, with derivative `i • T (U t ψ)` — matching the
shape of `Unbounded.Flow.Stone`'s `expUnitaryGroup_hasDerivAt` for the spectral-integral group, and
the natural next input toward an ODE-uniqueness argument identifying the two.

## Main definitions

- `stoneCandidateGenerator_translate_hasDerivAt` : `U t` applied to the `t = 0` derivative witness
  of `ψ`'s orbit is again a `t = 0` derivative witness, this time for `U t ψ`'s orbit.
- `stoneCandidateDomain_translate` : `T.domain` is invariant under every `U t`.
- `stoneCandidateGenerator_translate` : `T` commutes with `U t` on `T.domain`.
- `stoneCandidateGenerator_hasDerivAt` : the orbit of `ψ ∈ T.domain` is differentiable at every
  real time `s`, with derivative `i • T (U s ψ)`.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

omit [CompleteSpace H] in
include hUmul in
/-- `U t (U s ψ)` and `U s (U t ψ)` agree as functions of `s`, since `s + t = t + s`. -/
theorem stoneCandidateGenerator_translate_comm (ψ : H) (t : ℝ) :
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
theorem stoneCandidateGenerator_translate_hasDerivAt {ψ φ : H} (t : ℝ)
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
theorem stoneCandidateDomain_translate {ψ : H} (hψ : stoneCandidateDomainPred (U := U) ψ)
    (t : ℝ) : stoneCandidateDomainPred (U := U) (U t ψ) := by
  obtain ⟨φ, hφ⟩ := hψ
  exact ⟨U t φ, stoneCandidateGenerator_translate_hasDerivAt hUmul t hφ⟩

omit [CompleteSpace H] in
include hUmul in
/-- The candidate domain, packaged as a `Submodule`-invariance statement under every `U t`. -/
theorem stoneCandidateDomain_translate_mem (ψ : stoneCandidateDomain (U := U) hUmul) (t : ℝ) :
    (U t (ψ : H)) ∈ stoneCandidateDomain (U := U) hUmul :=
  stoneCandidateDomain_translate hUmul ψ.property t

omit [CompleteSpace H] in
include hUmul in
/-- The candidate generator commutes with the group it was built from: for `ψ` in `T.domain`,
`U t ψ` is again in `T.domain`, and `T (U t ψ) = U t (T ψ)`. -/
theorem stoneCandidateGenerator_translate (ψ : stoneCandidateDomain (U := U) hUmul) (t : ℝ) :
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
/-- The orbit of `ψ ∈ T.domain` is differentiable at every real time `s`, not just `s = 0`, with
derivative `i • T (U s ψ)` — the "everywhere differentiable" form of Stone's generator relation,
matching `Unbounded.Flow.Stone.expUnitaryGroup_hasDerivAt`'s shape for the spectral-integral
group. This is exactly the ingredient an ODE-uniqueness argument identifying `U` with the
spectral-integral group generated by `T`'s essential self-adjoint closure would need on both
sides. -/
theorem stoneCandidateGenerator_hasDerivAt (ψ : stoneCandidateDomain (U := U) hUmul) (s : ℝ) :
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
