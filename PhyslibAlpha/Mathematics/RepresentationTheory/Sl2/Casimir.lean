/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.NoncommRing
/-!
# The Casimir of an sl₂ triple

An `sl₂` triple vanishes on the generalized kernel of its Casimir, a polynomial image of `M`.

## i. Overview

Let `(h, e, f)` be an `sl₂` triple in a complex Lie algebra `L` acting on a finite-dimensional
module `M`. The Casimir endomorphism `C = h² + 2h + 4fe` commutes with `e`, `f` and `h`, so its
generalized kernel is stable under all three. On an irreducible representation of highest weight
`n` the Casimir is the scalar `n² + 2n`, which vanishes only for the trivial representation. This
file proves the corresponding statement without any appeal to complete reducibility. On the
generalized kernel of `C`, the three generators act by zero.

The argument works with eigenvalues of `h`. If `μ` is an eigenvalue of `h` and `μ + 2` is not,
then an eigenvector for `μ` is killed by `e`. It is therefore a primitive vector, so `μ = n` is a
natural number, and `C` acts on it by `n² + 2n`. Nilpotency of `C` forces `n = 0`. Walking up the
chain `μ, μ + 2, …` shows that every eigenvalue of `h` is a non-positive even integer, and the
same argument for the triple `(-h, f, e)`, which has the same Casimir, shows that it is also
non-negative. So `h` has only the eigenvalue zero and is nilpotent. Since `h - 2` is then
injective and `(h - 2)ᵏ e = e hᵏ`, the operator `e` vanishes, and likewise `f`. Finally
`h = ⁅e, f⁆` vanishes too.

Independently, for any endomorphism `C` of a finite-dimensional vector space, the projection onto
the generalized kernel of `C` along the Fitting complement `⋂ₖ range Cᵏ` is `q(C)` for a polynomial
`q` with constant term `1`. Combining the two, `q(C)` maps `M` onto the joint kernel of `e`, `f`
and `h` and fixes it. Because `q(0) = 1`, the projection differs from the identity by a polynomial
in the action of the Lie algebra without constant term.

## ii. Key results

- `IsSl2Triple.casimir` : the Casimir endomorphism `h² + 2h + 4fe`.
- `IsSl2Triple.commute_casimir_e`, `IsSl2Triple.commute_casimir_f`,
  `IsSl2Triple.commute_casimir_h` : the Casimir commutes with the triple.
- `IsSl2Triple.toEnd_eq_zero_of_isNilpotent_casimir` : a nilpotent Casimir forces the triple to
  act by zero.
- `IsSl2Triple.lie_eq_zero_of_mem_maxGenEigenspace` : the triple acts by zero on the generalized
  kernel of the Casimir.
- `Module.End.exists_polynomial_maxGenEigenspace_zero_proj` : the projection onto a generalized
  kernel along the Fitting complement is a polynomial with constant term `1`.
- `IsSl2Triple.exists_polynomial_casimir_proj` : a polynomial in the Casimir with constant term `1`
  projects `M` onto the invariants of the triple.

## iii. Table of contents

- A. The Casimir endomorphism
  - A.1. Commutation relations of the triple
  - A.2. The Casimir commutes with the triple
- B. A nilpotent Casimir forces a trivial action
  - B.1. Primitive vectors
  - B.2. Eigenvalues of `h`
  - B.3. Vanishing of the triple
  - B.4. Endomorphisms satisfying the `sl₂` relations
- C. The generalized kernel of the Casimir
- D. The projection onto a generalized kernel
- E. The projection onto the invariants of the triple

## iv. References

- J. E. Humphreys, Introduction to Lie Algebras and Representation Theory.

-/

@[expose] public section

open LieModule Module Module.End Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

/-!

## A. The Casimir endomorphism

-/

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M]

/-- The Casimir endomorphism `h² + 2h + 4fe` of the elements `h`, `e` and `f` acting on `M`.
When `(h, e, f)` is an `sl₂` triple it commutes with all three, and on the irreducible
representation of highest weight `n` it is the scalar `n² + 2n`. -/
def casimir (R M : Type*) {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M] (h e f : L) : Module.End R M :=
  toEnd R L M h * toEnd R L M h + 2 • toEnd R L M h + 4 • (toEnd R L M f * toEnd R L M e)

variable {h e f : L} (t : IsSl2Triple h e f)
include t

/-!

### A.1. Commutation relations of the triple

-/

/-- The bracket `[h, e] = 2 e` on `M`. -/
lemma toEnd_h_mul_e_sub : toEnd ℂ L M h * toEnd ℂ L M e - toEnd ℂ L M e * toEnd ℂ L M h =
    2 • toEnd ℂ L M e := by
  rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_h_e_nsmul, map_nsmul]

/-- The bracket `[h, f] = -2 f` on `M`. -/
lemma toEnd_h_mul_f_sub : toEnd ℂ L M h * toEnd ℂ L M f - toEnd ℂ L M f * toEnd ℂ L M h =
    -(2 • toEnd ℂ L M f) := by
  rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

/-- The bracket `[e, f] = h` on `M`. -/
lemma toEnd_e_mul_f_sub : toEnd ℂ L M e * toEnd ℂ L M f - toEnd ℂ L M f * toEnd ℂ L M e =
    toEnd ℂ L M h := by
  rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_e_f]

/-!

### A.2. The Casimir commutes with the triple

-/

/-- The Casimir commutes with the action of `e`. -/
lemma commute_casimir_e : Commute (casimir ℂ M h e f) (toEnd ℂ L M e) := by
  have ha := sub_eq_zero.mpr (t.toEnd_h_mul_e_sub (M := M))
  have hb := sub_eq_zero.mpr (t.toEnd_e_mul_f_sub (M := M))
  set H := toEnd ℂ L M h
  set E := toEnd ℂ L M e
  set F := toEnd ℂ L M f
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have : casimir ℂ M h e f * E - E * casimir ℂ M h e f =
      H * (H * E - E * H - 2 • E) + (H * E - E * H - 2 • E) * H
        - 4 • ((E * F - F * E - H) * E) := by
    simp only [casimir]
    noncomm_ring
  rw [this, ha, hb]
  simp

/-- The Casimir commutes with the action of `f`. -/
lemma commute_casimir_f : Commute (casimir ℂ M h e f) (toEnd ℂ L M f) := by
  have hc := sub_eq_zero.mpr (t.toEnd_h_mul_f_sub (M := M))
  have hb := sub_eq_zero.mpr (t.toEnd_e_mul_f_sub (M := M))
  set H := toEnd ℂ L M h
  set E := toEnd ℂ L M e
  set F := toEnd ℂ L M f
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have : casimir ℂ M h e f * F - F * casimir ℂ M h e f =
      H * (H * F - F * H - -(2 • F)) + (H * F - F * H - -(2 • F)) * H
        + 4 • (F * (E * F - F * E - H)) := by
    simp only [casimir]
    noncomm_ring
  rw [this, hc, hb]
  simp

/-- The Casimir commutes with the action of `h`. -/
lemma commute_casimir_h : Commute (casimir ℂ M h e f) (toEnd ℂ L M h) := by
  have ha := sub_eq_zero.mpr (t.toEnd_h_mul_e_sub (M := M))
  have hc := sub_eq_zero.mpr (t.toEnd_h_mul_f_sub (M := M))
  set H := toEnd ℂ L M h
  set E := toEnd ℂ L M e
  set F := toEnd ℂ L M f
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have : casimir ℂ M h e f * H - H * casimir ℂ M h e f =
      -4 • ((H * F - F * H - -(2 • F)) * E + F * (H * E - E * H - 2 • E)) := by
    simp only [casimir]
    noncomm_ring
  rw [this, ha, hc]
  simp

/-- The triple `(-h, f, e)` has the same Casimir as `(h, e, f)`. -/
lemma casimir_symm : casimir ℂ M (-h) f e = casimir ℂ M h e f := by
  have hb := sub_eq_zero.mpr (t.toEnd_e_mul_f_sub (M := M))
  rw [← sub_eq_zero]
  have : casimir ℂ M (-h) f e - casimir ℂ M h e f =
      4 • (toEnd ℂ L M e * toEnd ℂ L M f - toEnd ℂ L M f * toEnd ℂ L M e - toEnd ℂ L M h) := by
    simp only [casimir, map_neg]
    noncomm_ring
  rw [this, hb, smul_zero]

/-!

## B. A nilpotent Casimir forces a trivial action

### B.1. Primitive vectors

-/

/-- The Casimir acts on a primitive vector of weight `μ` by the scalar `μ² + 2μ`. -/
lemma casimir_apply_of_hasPrimitiveVectorWith {m : M} {μ : ℂ} (P : t.HasPrimitiveVectorWith m μ) :
    casimir ℂ M h e f m = (μ ^ 2 + 2 * μ) • m := by
  simp only [casimir, LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    toEnd_apply_apply, P.lie_h, P.lie_e, lie_smul, lie_zero, smul_zero, add_zero]
  module

variable [FiniteDimensional ℂ M]

/-- If the Casimir is nilpotent, every primitive vector has weight zero. -/
lemma eq_zero_of_hasPrimitiveVectorWith (hC : IsNilpotent (casimir ℂ M h e f)) {m : M} {μ : ℂ}
    (P : t.HasPrimitiveVectorWith m μ) : μ = 0 := by
  obtain ⟨n, rfl⟩ := P.exists_nat
  have hev : (casimir ℂ M h e f).HasEigenvalue ((n : ℂ) ^ 2 + 2 * n) :=
    hasEigenvalue_of_hasEigenvector
      ⟨mem_eigenspace_iff.mpr (t.casimir_apply_of_hasPrimitiveVectorWith P), P.ne_zero⟩
  have h0 : ((n ^ 2 + 2 * n : ℕ) : ℂ) = 0 := by
    exact_mod_cast (hev.isNilpotent_of_isNilpotent hC).eq_zero
  have : n ^ 2 + 2 * n = 0 := by exact_mod_cast h0
  simp_all

/-!

### B.2. Eigenvalues of `h`

-/

/-- If the Casimir is nilpotent, an eigenvalue `μ` of `h` such that `μ + 2` is not an eigenvalue
is zero, since its eigenvectors are primitive. -/
lemma eq_zero_of_not_hasEigenvalue_add_two (hC : IsNilpotent (casimir ℂ M h e f)) {μ : ℂ}
    (hμ : (toEnd ℂ L M h).HasEigenvalue μ) (hμ2 : ¬ (toEnd ℂ L M h).HasEigenvalue (μ + 2)) :
    μ = 0 := by
  obtain ⟨m, hm⟩ := hμ.exists_hasEigenvector
  have hm' : ⁅h, m⁆ = μ • m := by simpa using hm.apply_eq_smul
  have he : ⁅e, m⁆ = 0 := by
    by_contra hne
    refine hμ2 (hasEigenvalue_of_hasEigenvector (x := ⁅e, m⁆) ⟨?_, hne⟩)
    rw [mem_eigenspace_iff, toEnd_apply_apply]
    simpa using t.lie_h_pow_toEnd_e hm' 1
  exact t.eq_zero_of_hasPrimitiveVectorWith hC ⟨hm.2, hm', he⟩

/-- If the Casimir is nilpotent, every eigenvalue of `h` is a non-positive even integer. -/
lemma exists_nat_add_eq_zero (hC : IsNilpotent (casimir ℂ M h e f)) {μ : ℂ}
    (hμ : (toEnd ℂ L M h).HasEigenvalue μ) : ∃ n : ℕ, μ + 2 * n = 0 := by
  have hfin : {k : ℕ | (toEnd ℂ L M h).HasEigenvalue (μ + 2 * k)}.Finite :=
    (toEnd ℂ L M h).finite_hasEigenvalue.preimage fun a _ b _ hab ↦ by simpa using hab
  obtain ⟨k, hk⟩ := hfin.exists_notMem
  obtain ⟨n, hn, hn1⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k ↦ ¬ (toEnd ℂ L M h).HasEigenvalue (μ + 2 * k)) (by simpa using hμ) ⟨k, hk⟩
  refine ⟨n, t.eq_zero_of_not_hasEigenvalue_add_two hC (not_not.mp hn) ?_⟩
  convert hn1 using 2
  push_cast
  ring

/-- If the Casimir is nilpotent, the only eigenvalue of `h` is zero. -/
lemma hasEigenvalue_eq_zero (hC : IsNilpotent (casimir ℂ M h e f)) {μ : ℂ}
    (hμ : (toEnd ℂ L M h).HasEigenvalue μ) : μ = 0 := by
  obtain ⟨n, hn⟩ := t.exists_nat_add_eq_zero hC hμ
  have hμ' : (toEnd ℂ L M (-h)).HasEigenvalue (-μ) := by
    obtain ⟨m, hm⟩ := hμ.exists_hasEigenvector
    refine hasEigenvalue_of_hasEigenvector ⟨?_, hm.2⟩
    simp [hm.apply_eq_smul]
  obtain ⟨n', hn'⟩ := t.symm.exists_nat_add_eq_zero (by rwa [t.casimir_symm]) hμ'
  have h0 : ((n + n' : ℕ) : ℂ) = 0 := by push_cast; linear_combination (hn + hn') / 2
  have : n = 0 := by have := Nat.cast_eq_zero.mp h0; omega
  simpa [this] using hn

/-- If the Casimir is nilpotent, so is the action of `h`. -/
lemma isNilpotent_toEnd_h (hC : IsNilpotent (casimir ℂ M h e f)) :
    IsNilpotent (toEnd ℂ L M h) := by
  have htop : (toEnd ℂ L M h).maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff, ← iSup_maxGenEigenspace_eq_top (toEnd ℂ L M h)]
    refine iSup_le fun μ ↦ ?_
    by_cases hμ : μ = 0
    · rw [hμ]
    refine le_of_eq_of_le (not_not.mp fun hne ↦ hμ (t.hasEigenvalue_eq_zero hC ?_)) bot_le
    exact (hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).mp hne
  refine ((LinearMap.charpoly_nilpotent_tfae (toEnd ℂ L M h)).out 1 3).mpr fun m ↦ ?_
  have hm : m ∈ (toEnd ℂ L M h).maxGenEigenspace 0 := htop ▸ Submodule.mem_top
  simpa [zero_smul, sub_zero] using (mem_maxGenEigenspace _ _ _).mp hm

/-!

### B.3. Vanishing of the triple

-/

omit [FiniteDimensional ℂ M] in
/-- If `h` acts nilpotently, then `e` acts by zero, since `(h - 2)ᵏ e = e hᵏ` and `h - 2` is
injective. -/
lemma toEnd_e_eq_zero_of_isNilpotent (hH : IsNilpotent (toEnd ℂ L M h)) :
    toEnd ℂ L M e = 0 := by
  obtain ⟨k, hk⟩ := hH
  set H := toEnd ℂ L M h
  set E := toEnd ℂ L M e
  have hsc : SemiconjBy E H (H - 2 • (1 : Module.End ℂ M)) := by
    rw [SemiconjBy, ← sub_eq_zero]
    have : E * H - (H - 2 • (1 : Module.End ℂ M)) * E = -(H * E - E * H - 2 • E) := by noncomm_ring
    rw [this, sub_eq_zero.mpr (t.toEnd_h_mul_e_sub (M := M)), neg_zero]
  have hinj : Function.Injective ⇑(H - 2 • (1 : Module.End ℂ M)) := by
    refine (injective_iff_map_eq_zero _).mpr fun w hw ↦ ?_
    by_contra hne
    have hev : H.HasEigenvalue 2 := hasEigenvalue_of_hasEigenvector ⟨?_, hne⟩
    · exact two_ne_zero (hev.isNilpotent_of_isNilpotent ⟨k, hk⟩).eq_zero
    rw [mem_eigenspace_iff, two_smul]
    simpa [sub_eq_zero, two_smul] using hw
  ext m
  have hm := congr($(hsc.pow_right k) m)
  simp only [mul_apply_eq_comp, hk, LinearMap.zero_apply, map_zero] at hm
  rw [FunLike.coe_pow_eq_iterate] at hm
  exact (hinj.iterate k) (by rw [← hm, LinearMap.zero_apply, Function.iterate_fixed (map_zero _)])

/-- If the Casimir is nilpotent, then `e`, `f` and `h` all act by zero. -/
lemma toEnd_eq_zero_of_isNilpotent_casimir (hC : IsNilpotent (casimir ℂ M h e f)) :
    toEnd ℂ L M e = 0 ∧ toEnd ℂ L M f = 0 ∧ toEnd ℂ L M h = 0 := by
  have hH := t.isNilpotent_toEnd_h hC
  have hE := t.toEnd_e_eq_zero_of_isNilpotent hH
  have hF := t.symm.toEnd_e_eq_zero_of_isNilpotent (M := M) (by simpa using hH.neg)
  refine ⟨hE, hF, ?_⟩
  rw [← t.lie_e_f, LieHom.map_lie, hE, zero_lie]

end IsSl2Triple

/-!

### B.4. Endomorphisms satisfying the `sl₂` relations

-/

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Three endomorphisms `H`, `E`, `F` satisfying the `sl₂` relations, whose Casimir is nilpotent,
all vanish. Unlike an `IsSl2Triple`, this allows `H = 0`, which is needed when restricting the
action to an invariant subspace. -/
lemma eq_zero_of_sl2_relations {H E F : Module.End ℂ V} (hHE : H * E - E * H = 2 • E)
    (hHF : H * F - F * H = -(2 • F)) (hEF : E * F - F * E = H)
    (hC : IsNilpotent (H * H + 2 • H + 4 • (F * E))) : E = 0 ∧ F = 0 ∧ H = 0 := by
  by_cases hH : H = 0
  · subst hH
    simp only [zero_mul, mul_zero, sub_zero, zero_eq_neg] at hHE hHF
    have hE : (2 : ℂ) • E = 0 := by rw [two_smul, ← two_nsmul, ← hHE]
    have hF : (2 : ℂ) • F = 0 := by rw [two_smul, ← two_nsmul, hHF]
    exact ⟨(smul_eq_zero.mp hE).resolve_left two_ne_zero,
      (smul_eq_zero.mp hF).resolve_left two_ne_zero, rfl⟩
  · have t : IsSl2Triple H E F := ⟨hH, hEF, hHE, hHF⟩
    simpa using t.toEnd_eq_zero_of_isNilpotent_casimir (M := V)
      (by simpa [IsSl2Triple.casimir] using hC)

end Module.End

namespace IsSl2Triple

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  {h e f : L} (t : IsSl2Triple h e f)
include t

/-!

## C. The generalized kernel of the Casimir

-/

/-- The triple acts by zero on the generalized kernel of its Casimir. -/
lemma lie_eq_zero_of_mem_maxGenEigenspace {v : M}
    (hv : v ∈ (casimir ℂ M h e f).maxGenEigenspace 0) :
    ⁅e, v⁆ = 0 ∧ ⁅f, v⁆ = 0 ∧ ⁅h, v⁆ = 0 := by
  have hE : ∀ w ∈ (casimir ℂ M h e f).maxGenEigenspace 0, toEnd ℂ L M e w ∈ _ :=
    fun _ hw ↦ mapsTo_maxGenEigenspace_of_comm (t.commute_casimir_e (M := M)) 0 hw
  have hF : ∀ w ∈ (casimir ℂ M h e f).maxGenEigenspace 0, toEnd ℂ L M f w ∈ _ :=
    fun _ hw ↦ mapsTo_maxGenEigenspace_of_comm (t.commute_casimir_f (M := M)) 0 hw
  have hH : ∀ w ∈ (casimir ℂ M h e f).maxGenEigenspace 0, toEnd ℂ L M h w ∈ _ :=
    fun _ hw ↦ mapsTo_maxGenEigenspace_of_comm (t.commute_casimir_h (M := M)) 0 hw
  have hN := isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (casimir ℂ M h e f) 0
  obtain ⟨h1, h2, h3⟩ := Module.End.eq_zero_of_sl2_relations
    (H := (toEnd ℂ L M h).restrict hH) (E := (toEnd ℂ L M e).restrict hE)
    (F := (toEnd ℂ L M f).restrict hF)
    (by ext w; simpa using congr($(t.toEnd_h_mul_e_sub (M := M)) w.1))
    (by ext w; simpa using congr($(t.toEnd_h_mul_f_sub (M := M)) w.1))
    (by ext w; simpa using congr($(t.toEnd_e_mul_f_sub (M := M)) w.1))
    (by
      convert hN using 1
      refine LinearMap.ext fun w ↦ Subtype.ext ?_
      change _ = (casimir ℂ M h e f - algebraMap ℂ (Module.End ℂ M) 0) w.1
      simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
        Submodule.coe_add, Submodule.coe_smul_of_tower, LinearMap.coe_restrict_apply]
      simp [casimir])
  refine ⟨?_, ?_, ?_⟩
  · simpa using congr(($(h1) ⟨v, hv⟩ : M))
  · simpa using congr(($(h2) ⟨v, hv⟩ : M))
  · simpa using congr(($(h3) ⟨v, hv⟩ : M))

end IsSl2Triple

/-!

## D. The projection onto a generalized kernel

-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A vector lies in the generalized kernel of `C` if some power of `C` kills it. -/
lemma mem_maxGenEigenspace_zero_iff (C : Module.End K V) (v : V) :
    v ∈ C.maxGenEigenspace 0 ↔ ∃ k : ℕ, (C ^ k) v = 0 := by
  simp

/-- If `Xᵇ g` annihilates `C` and `g` is coprime to `X`, then `Cᵇ` already kills every vector killed
by some power of `C`. -/
lemma pow_apply_eq_zero_of_isCoprime {C : Module.End K V} {b k : ℕ} {g : K[X]}
    (hcop : IsCoprime X g) (hzero : aeval C (X ^ b * g) = 0) {v : V} (hv : (C ^ k) v = 0) :
    (C ^ b) v = 0 := by
  obtain ⟨u, w, huw⟩ := hcop.pow_left (m := k)
  have hpoly : (X ^ b : K[X]) = u * X ^ b * X ^ k + w * (X ^ b * g) := by
    linear_combination (-X ^ b) * huw
  have := congr((aeval C $hpoly) v)
  simpa [map_mul, aeval_X_pow, mul_apply_eq_comp, hv, hzero] using this

variable [FiniteDimensional K V]

/-- Every endomorphism of a finite-dimensional space is annihilated by a polynomial `Xᵇ g` with
`0 < b` and `g` coprime to `X`. -/
lemma exists_aeval_X_pow_mul_eq_zero (C : Module.End K V) :
    ∃ (b : ℕ) (g : K[X]), 0 < b ∧ IsCoprime X g ∧ aeval C (X ^ b * g) = 0 := by
  have hp : X * LinearMap.charpoly C ≠ 0 :=
    mul_ne_zero X_ne_zero (LinearMap.charpoly_monic C).ne_zero
  obtain ⟨g, hpg, hg⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  simp only [map_zero, sub_zero] at hpg hg
  refine ⟨rootMultiplicity 0 (X * LinearMap.charpoly C), g,
    (rootMultiplicity_pos hp (x := 0)).mpr (by simp), irreducible_X.coprime_iff_not_dvd.mpr hg, ?_⟩
  rw [← hpg, map_mul, LinearMap.aeval_self_charpoly, mul_zero]

/-- The projection onto the generalized kernel of `C` along the Fitting complement
`⋂ₖ range Cᵏ` is `q(C)` for a polynomial `q` with constant term `1`. -/
lemma exists_polynomial_maxGenEigenspace_zero_proj (C : Module.End K V) :
    ∃ q : K[X], q.coeff 0 = 1 ∧ (∀ v ∈ C.maxGenEigenspace 0, aeval C q v = v) ∧
      (∀ v, aeval C q v ∈ C.maxGenEigenspace 0) ∧
      (∀ v ∈ ⨅ k : ℕ, LinearMap.range (C ^ k), aeval C q v = 0) := by
  obtain ⟨b, g, hb, hcop, hzero⟩ := C.exists_aeval_X_pow_mul_eq_zero
  obtain ⟨u, w, huw⟩ := hcop.pow_left (m := b)
  have hq : w * g = 1 - u * X ^ b := by linear_combination huw
  have hkill : aeval C (w * g) * C ^ b = 0 := by
    rw [← aeval_X_pow (R := K), ← map_mul, show w * g * X ^ b = w * (X ^ b * g) by ring, map_mul,
      hzero, mul_zero]
  refine ⟨w * g, ?_, fun v hv ↦ ?_, fun v ↦ ?_, fun v hv ↦ ?_⟩
  · rw [hq, coeff_sub, AddMonoidAlgebra.coeff_one_zero, coeff_mul_X_pow',
      ite_eq_right (by omega), sub_zero]
  · obtain ⟨k, hk⟩ := (C.mem_maxGenEigenspace_zero_iff v).mp hv
    rw [hq, map_sub, map_one, map_mul, aeval_X_pow, LinearMap.sub_apply, mul_apply_eq_comp,
      pow_apply_eq_zero_of_isCoprime hcop hzero hk, map_zero, sub_zero, one_apply_eq_self]
  · refine (C.mem_maxGenEigenspace_zero_iff _).mpr ⟨b, ?_⟩
    rw [← mul_apply_eq_comp, ← aeval_X_pow (R := K), ← map_mul,
      show X ^ b * (w * g) = w * g * X ^ b by ring, map_mul, aeval_X_pow, hkill,
      LinearMap.zero_apply]
  · obtain ⟨y, rfl⟩ := (Submodule.mem_iInf _).mp hv b
    rw [← mul_apply_eq_comp, hkill, LinearMap.zero_apply]

end Module.End

namespace IsSl2Triple

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  {h e f : L} (t : IsSl2Triple h e f)
include t

/-!

## E. The projection onto the invariants of the triple

-/

/-- There is a polynomial `q` with constant term `1` such that `q(C)`, for `C` the Casimir, maps
`M` into the joint kernel of `e`, `f` and `h` and fixes every vector killed by `e` and `f`. -/
lemma exists_polynomial_casimir_proj :
    ∃ q : ℂ[X], q.coeff 0 = 1 ∧
      (∀ v, ⁅e, aeval (casimir ℂ M h e f) q v⁆ = 0 ∧ ⁅f, aeval (casimir ℂ M h e f) q v⁆ = 0 ∧
        ⁅h, aeval (casimir ℂ M h e f) q v⁆ = 0) ∧
      (∀ v : M, ⁅e, v⁆ = 0 → ⁅f, v⁆ = 0 → aeval (casimir ℂ M h e f) q v = v) := by
  obtain ⟨q, h0, hfix, hmem, -⟩ := (casimir ℂ M h e f).exists_polynomial_maxGenEigenspace_zero_proj
  refine ⟨q, h0, fun v ↦ t.lie_eq_zero_of_mem_maxGenEigenspace (hmem v), fun v he hf ↦ hfix v ?_⟩
  have hh : ⁅h, v⁆ = 0 := by rw [← t.lie_e_f, lie_lie, he, hf, lie_zero, lie_zero, sub_zero]
  refine ((casimir ℂ M h e f).mem_maxGenEigenspace_zero_iff v).mpr ⟨1, ?_⟩
  simp [casimir, he, hh]

end IsSl2Triple
