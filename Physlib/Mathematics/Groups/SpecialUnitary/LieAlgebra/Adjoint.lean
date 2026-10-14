/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Basic
/-!

# The adjoint representation of `SU(n)`

The adjoint representation of `SU(n)` and its complexification, defined as `x ↦ g x g†`, and
the irreducibility of the latter.

## i. Overview

We define the adjont representation of `SU(n)` on its Lie algebra `su(n)` and its complexification.
The adjoint is defined by conjugation, `x ↦ g x g†`. It preserves the bracket, and its kernel is
the centre of `SU(n)`, the scalar matrices (A.1, A.2). On the underlying matrices of the
complexification the adjoint action of any unitary matrix, and in particular of any permutation of
the coordinates, is realised by an element of `SU(n)`; diagonal elements of `SU(n)` act on the
entries by phases (A.3). The complex adjoint representation is irreducible for `2 ≤ n` (C.1),
and hence, by Schur's lemma over an algebraically closed field, that every endomorphism of the
complexification commuting with the adjoint action is a multiple of the identity (C.2).

## ii. Key results

- `SULieAlgebra.adjoint` : the adjoint representation on `su(n)`.
- `SULieAlgebra.adjointℂ` : the adjoint representation on the complexification.
- `SULieAlgebra.adjoint_eq_iff` : the adjoint representation is faithful modulo the centre.
- `SULieAlgebra.isIrreducible_adjointℂ` : the complex adjoint representation is irreducible.
- `SULieAlgebra.end_eq_smul_id_of_commute_adjointℂ` : Schur's lemma for the complex adjoint
  representation.

## iii. Table of contents

- A. The adjoint representation
  - A.1. The real adjoint representation
  - A.2. The complex adjoint representation
  - A.3. The action on the underlying matrices
- B. The relation to single-entry elements
- C. Irreducibility and Schur's lemma
  - C.1. Irreducibility
  - C.2. Schur's lemma

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct

namespace SULieAlgebra

/-!

## A. The adjoint representation

-/

/-!

### A.1. The real adjoint representation

-/

/-- The adjoint representation `x ↦ g x g†` of `SU(n)` on its real Lie algebra `su(n)`. -/
noncomputable def adjoint {n : ℕ} :
    Representation ℝ (specialUnitaryGroup (Fin n) ℂ) (SULieAlgebra n ℂ) :=
  conj.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The underlying matrix of `adjoint g x` is `g x g†`. -/
@[simp]
lemma adjoint_val {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x : SULieAlgebra n ℂ) :
    (adjoint g x).1 = g.1 * x.1 * star g.1 := rfl

/-- The adjoint representation preserves the bracket, so `SU(n)` acts on `su(n)` by Lie algebra
  automorphisms. -/
lemma adjoint_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjoint g ⁅x, y⁆ = ⁅adjoint g x, adjoint g y⁆ :=
  conj_lie _ x y

/-- The kernel of the adjoint representation is the centre of `SU(n)`: `g` acts trivially exactly
  when it is a scalar matrix `c 1`. -/
lemma adjoint_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  have hg := (mem_specialUnitaryGroup_iff.mp g.2).1
  constructor
  · intro h
    -- `g x g† = x` for all `x`, so `g` commutes with `su(n)` and hence with every matrix
    have hx (x : SULieAlgebra n ℂ) : Commute g.1 x.1 := by
      have hx := congrArg Subtype.val (LinearMap.congr_fun h x)
      rw [adjoint_val, Module.End.one_apply] at hx
      calc g.1 * x.1 = g.1 * x.1 * star g.1 * g.1 := by
            rw [Matrix.mul_assoc _ (star g.1), hg.1, Matrix.mul_one]
        _ = x.1 * g.1 := by rw [hx]
    have hcen : g.1 ∈ Set.center (Matrix (Fin n) (Fin n) ℂ) :=
      Semigroup.mem_center_iff.mpr fun N => (commute_of_forall_commute_val hx N).symm.eq
    rw [Matrix.center_eq_range] at hcen
    obtain ⟨c, hc⟩ := hcen
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hcomm : g.1 * x.1 = x.1 * g.1 := by
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [adjoint_val, Module.End.one_apply, hcomm, Matrix.mul_assoc, hg.2, Matrix.mul_one]

/-- Two elements of `SU(n)` have the same adjoint action exactly when they differ by a scalar:
  the adjoint representation is faithful on `SU(n)` modulo its centre. -/
lemma adjoint_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = adjoint h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  have hh := (mem_specialUnitaryGroup_iff.mp h.2).1
  have hval : (g * h⁻¹).1 = g.1 * star h.1 := rfl
  have key : adjoint g = adjoint h ↔ adjoint (g * h⁻¹) = 1 := by
    constructor
    · intro hgh
      rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
    · intro h1
      rw [← one_mul (adjoint h), ← h1, ← map_mul, inv_mul_cancel_right]
  rw [key, adjoint_eq_one_iff, hval]
  refine exists_congr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [← Matrix.mul_one g.1, ← hh.1, ← Matrix.mul_assoc, hc, Matrix.smul_mul, Matrix.one_mul]
  · rw [hc, Matrix.smul_mul, hh.2]

/-!

### A.2. The complex adjoint representation

-/

/-- The adjoint representation of `SU(n)` on the complexification `ℂ ⊗[ℝ] su(n)`: the
  complexification of the adjoint representation `adjoint` on `su(n)`. -/
noncomputable def adjointℂ {n : ℕ} :
    Representation ℂ (specialUnitaryGroup (Fin n) ℂ) (Complexification n) :=
  (Module.End.baseChangeHom ℝ ℂ (SULieAlgebra n ℂ) : Module.End ℝ _ →* Module.End ℂ _).comp
    adjoint

@[simp]
lemma adjointℂ_tmul {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (z : ℂ) (x : SULieAlgebra n ℂ) :
    adjointℂ g (z ⊗ₜ x) = z ⊗ₜ adjoint g x := rfl

/-- The complex adjoint representation preserves the bracket of the complexification, so `SU(n)`
  acts on `ℂ ⊗[ℝ] su(n)` by Lie algebra automorphisms. -/
lemma adjointℂ_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (A B : Complexification n) :
    adjointℂ g ⁅A, B⁆ = ⁅adjointℂ g A, adjointℂ g B⁆ := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, adjointℂ_tmul, adjointℂ_tmul, adjointℂ_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, adjoint_lie]
    | add B B' hB hB' =>
      rw [lie_add (L := Complexification n), map_add, hB, hB', map_add,
        lie_add (L := Complexification n)]
  | add A A' hA hA' =>
    rw [add_lie (L := Complexification n), map_add, hA, hA', map_add,
      add_lie (L := Complexification n)]

/-- The kernel of the complex adjoint representation is the centre of `SU(n)`, as for the real
  adjoint representation. -/
lemma adjointℂ_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  rw [← adjoint_eq_one_iff]
  refine ⟨fun h => LinearMap.ext fun x => Subtype.ext ?_, fun h => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun h (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, Module.End.one_apply, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul,
      one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = 1
    rw [h, map_one]

/-- Two elements of `SU(n)` have the same complex adjoint action exactly when they differ by a
  scalar, as for the real adjoint representation. -/
lemma adjointℂ_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = adjointℂ h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  rw [← adjoint_eq_iff]
  refine ⟨fun hgh => LinearMap.ext fun x => Subtype.ext ?_, fun hgh => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun hgh (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = Module.End.baseChangeHom ℝ ℂ _ (adjoint h)
    rw [hgh]

/-!

### A.3. The action on the underlying matrices

-/

/-- The adjoint representation conjugates the matrix, `M ↦ g M g†`. -/
@[simp]
lemma toMatrixℂ_adjointℂ {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    toMatrixℂ (adjointℂ g A) = g.1 * toMatrixℂ A * star g.1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    rw [adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, adjoint_val, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

/-- Conjugation by any unitary matrix is the adjoint action of an element of `SU(n)`: a
  unitary matrix agrees with an element of `SU(n)` up to a phase, which conjugation does not
  see. -/
lemma exists_toMatrixℂ_adjointℂ_eq_unitary {n : ℕ} (U : unitaryGroup (Fin n) ℂ) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, ∀ A : Complexification n,
      toMatrixℂ (adjointℂ g A) = U.1 * toMatrixℂ A * star U.1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun A => Subsingleton.elim _ _⟩
  have hd : Complex.normSq U.1.det = 1 := by
    exact_mod_cast Complex.normSq_eq_conj_mul_self.trans
      (Unitary.star_mul_self_of_mem (det_of_mem_unitary U.2))
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = (U.1.det)⁻¹ := ⟨_, Complex.cpow_nat_inv_pow _ hn.ne'⟩
  have hc1 : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg c)
      hn.ne').1 (by rw [← map_pow, hc, map_inv₀, hd, inv_one]), Complex.ofReal_one]
  refine ⟨⟨c • U.1, mem_specialUnitaryGroup_iff.2 ⟨mem_unitaryGroup_iff.2 ?_, ?_⟩⟩, fun A => ?_⟩
  · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1, mem_unitaryGroup_iff.1 U.2,
      one_smul]
  · rw [det_smul, Fintype.card_fin, hc, inv_mul_cancel₀ fun h => by simp [h] at hd]
  · rw [toMatrixℂ_adjointℂ]
    change c • U.1 * toMatrixℂ A * star (c • U.1) = _
    rw [star_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1, one_smul]

/-- The adjoint action realises any permutation `σ` of the coordinates: some element of `SU(n)`
  moves the entry `(x, y)` of every matrix to `(σ x, σ y)`. -/
lemma exists_toMatrixℂ_adjointℂ_apply_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, ∀ A x y,
      toMatrixℂ (adjointℂ g A) (σ x) (σ y) = toMatrixℂ A x y := by
  have hP : Equiv.Perm.permMatrix ℂ σ⁻¹ ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, inv_inv,
      ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_eq_unitary ⟨_, hP⟩
  refine ⟨g, fun A x y => ?_⟩
  rw [hg]
  change (Equiv.Perm.permMatrix ℂ σ⁻¹ * toMatrixℂ A * star (Equiv.Perm.permMatrix ℂ σ⁻¹))
    (σ x) (σ y) = _
  rw [star_eq_conjTranspose, conjTranspose_permMatrix, inv_inv, Equiv.Perm.permMatrix,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

/-- The adjoint action of a diagonal element of `SU(n)` scales the entry at `(x, y)` of the
  matrix by `d x * star (d y)`. -/
lemma toMatrixℂ_adjointℂ_apply_of_diagonal {n} {g : specialUnitaryGroup (Fin n) ℂ}
    {d : Fin n → ℂ} (hg : g.1 = diagonal d) (A : Complexification n) (x y : Fin n) :
    toMatrixℂ (adjointℂ g A) x y = d x * star (d y) * toMatrixℂ A x y := by
  rw [toMatrixℂ_adjointℂ, hg, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
    diagonal_mul, Pi.star_apply]
  ring

lemma toMatrixℂ_adjointℂ_trace {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    (toMatrixℂ (adjointℂ g A)).trace = (toMatrixℂ A).trace := by
  rw [toMatrixℂ_adjointℂ, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc,
    (mem_specialUnitaryGroup_iff.mp g.2).1.1, Matrix.mul_one]

/-!

## B. The relation to single-entry elements

-/

/-- All the off-diagonal matrix units `singleℂ` lie in one adjoint orbit -/
lemma exists_adjointℂ_singleℂ_eq_singleℂ {n : ℕ} {i j p q : Fin n} (hij : i ≠ j) (hpq : p ≠ q) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, adjointℂ g (singleℂ i j hij) = singleℂ p q hpq := by
  obtain ⟨σ, hσi, hσj⟩ : ∃ σ : Equiv.Perm (Fin n), σ i = p ∧ σ j = q := by
    refine ⟨Equiv.swap (Equiv.swap i p j) q * Equiv.swap i p, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
        (fun h => hij ((Equiv.swap i p).injective ((Equiv.swap_apply_left i p).trans h))) hpq]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_apply_perm σ
  refine ⟨g, toMatrixℂ_injective (Matrix.ext fun u v => ?_)⟩
  simpa only [singleℂ, toMatrixℂ_ofTracelessℂ, single_apply, Equiv.apply_symm_apply,
    Equiv.eq_symm_apply, hσi, hσj] using hg (singleℂ i j hij) (σ.symm u) (σ.symm v)

/-- If the matrix of `A` has a non-zero entry at the off-diagonal position `(p, q)`, then
  `singleℂ p q h` lies in the span of the adjoint orbit of `A`. -/
lemma singleℂ_mem_span_range_adjointℂ {n : ℕ} {p q : Fin n} (h : p ≠ q)
    {A : Complexification n} (hA : toMatrixℂ A p q ≠ 0) :
    singleℂ p q h ∈ Submodule.span ℂ (Set.range fun g => adjointℂ g A) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hinv : ζ⁻¹ = starRingEnd ℂ ζ := Complex.inv_eq_conj (hζ.norm'_eq_one (by norm_num))
  have hphase (a b : ℤ) : ζ ^ a * star (ζ ^ b) = ζ ^ (a - b) := by
    simp [← hinv, zpow_sub₀ hζ0, div_eq_mul_inv]
  have hgeom (m : ℤ) (hm : ¬ (5 : ℤ) ∣ m) : ∑ k ∈ Finset.range 5, (ζ ^ m) ^ k = 0 := by
    have h1 : ζ ^ m ≠ 1 := by rw [Ne, hζ.zpow_eq_one_iff_dvd]; exact_mod_cast hm
    rw [geom_sum_eq h1, ← zpow_natCast (ζ ^ m) 5, ← _root_.zpow_mul,
      (hζ.zpow_eq_one_iff_dvd _).2 ⟨m, by push_cast; ring⟩, sub_self, zero_div]
  set e : Fin n → ℤ := fun x => if x = p then 1 else if x = q then -1 else 0 with he
  obtain ⟨g, hg⟩ : ∃ g : specialUnitaryGroup (Fin n) ℂ, g.1 = diagonal fun x => ζ ^ e x := by
    refine ⟨⟨diagonal (fun x => ζ ^ e x), mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩⟩, rfl⟩
    · simp [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, ← hinv,
        zpow_ne_zero _ hζ0]
    · simp [he, apply_ite (ζ ^ · : ℤ → ℂ), Finset.prod_ite, Finset.filter_eq', hζ0, h.symm]
  have hgk (k : ℕ) (x y : Fin n) :
      toMatrixℂ (adjointℂ (g ^ k) A) x y = (ζ ^ (e x - e y)) ^ k * toMatrixℂ A x y := by
    rw [toMatrixℂ_adjointℂ_apply_of_diagonal (show (g ^ k).1 = diagonal fun x => (ζ ^ e x) ^ k from
      by rw [SubmonoidClass.coe_pow, hg]; exact diagonal_pow _ k), star_pow, ← mul_pow, hphase]
  have hcollect (m : ℤ) (c : ℂ) : ∑ k ∈ Finset.range 5, ((5 : ℂ)⁻¹ * (ζ ^ (-2 : ℤ)) ^ k) *
      ((ζ ^ m) ^ k * c) = (5 : ℂ)⁻¹ * (∑ k ∈ Finset.range 5, (ζ ^ (m - 2)) ^ k) * c := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show m - 2 = -2 + m by ring, zpow_add₀ hζ0, mul_pow]; ring
  have hentry (x y : Fin n) : ∑ k ∈ Finset.range 5, ((5 : ℂ)⁻¹ * (ζ ^ (-2 : ℤ)) ^ k) *
      ((ζ ^ (e x - e y)) ^ k * toMatrixℂ A x y) = single p q (toMatrixℂ A p q) x y := by
    rw [hcollect]
    by_cases hxy : x = p ∧ y = q
    · obtain ⟨rfl, rfl⟩ := hxy
      rw [single_apply_same, show e x - e y - 2 = 0 by simp [he, h.symm]]; norm_num
    · rw [single_apply_of_ne (c := _) (h := mt (And.imp Eq.symm Eq.symm) hxy), hgeom, mul_zero,
        zero_mul]
      simp only [he]; split_ifs <;> omega
  rw [← Submodule.smul_mem_iff _ hA, show toMatrixℂ A p q • singleℂ p q h =
      ∑ k ∈ Finset.range 5, ((5 : ℂ)⁻¹ * (ζ ^ (-2 : ℤ)) ^ k) • adjointℂ (g ^ k) A from
    toMatrixℂ_injective (Matrix.ext fun x y => by
      simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hgk, hentry,
        singleℂ, toMatrixℂ_ofTracelessℂ, single_apply, mul_ite, mul_one, mul_zero])]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g ^ k, rfl⟩)

/-- The adjoint action of some element of `SU(n)` — the rotation by `π / 4` in the `(p, q)`-plane —
  changes an element whose matrix is the diagonal matrix `d` only in the `(p, q)`-block, by
  `(d p - d q) / 2` times `singleℂ p q h + singleℂ q p h.symm - diagDiffℂ p q`. -/
lemma exists_adjointℂ_eq_of_toMatrixℂ_eq_diagonal {n : ℕ} {p q : Fin n} (h : p ≠ q)
    {A : Complexification n} {d : Fin n → ℂ} (hA : toMatrixℂ A = diagonal d) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ, adjointℂ g A =
      A + ((d p - d q) / 2) • (singleℂ p q h + singleℂ q p h.symm - diagDiffℂ p q) := by
  set s : ℂ := (((√2)⁻¹ : ℝ) : ℂ)
  have hs : s ^ 2 = 1 / 2 := by simp [s, ← Complex.ofReal_pow]
  set U : Matrix (Fin n) (Fin n) ℂ := 1 - single p p 1 - single q q 1 +
    s • (single p p 1 + single p q 1 + single q p 1 - single q q 1) with hU
  have hUs : star U = U := by simp [hU, s, star_eq_conjTranspose]; module
  have hUU : U * U = 1 := by
    simp only [hU, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ h,
      single_mul_single_of_ne _ _ _ _ h.symm, mul_one]
    match_scalars <;> first | ring1 | linear_combination 2 * hs
  have hds (i j : Fin n) : diagonal d * single i j (1 : ℂ) = d i • single i j 1 :=
    Matrix.ext fun x y => by by_cases hc : i = x <;> simp [diagonal_mul, single_apply, hc]
  have hsd (i j : Fin n) : single i j (1 : ℂ) * diagonal d = d j • single i j 1 :=
    Matrix.ext fun x y => by by_cases hc : j = y <;> simp [mul_diagonal, single_apply, hc]
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_eq_unitary
    ⟨U, mem_unitaryGroup_iff.2 (by rw [hUs, hUU])⟩
  refine ⟨g, toMatrixℂ_injective ?_⟩
  rw [hg]; change U * toMatrixℂ A * star U = _; rw [hUs, hA]
  simp only [map_add, map_smul, map_sub, singleℂ, diagDiffℂ, toMatrixℂ_ofTracelessℂ, hA, hU,
    mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
    hds, hsd, single_mul_single_same, single_mul_single_of_ne _ _ _ _ h,
    single_mul_single_of_ne _ _ _ _ h.symm, mul_one, smul_zero]
  match_scalars <;> first
    | ring1 | linear_combination (d p + d q) * hs | linear_combination (d p - d q) * hs

/-- The difference of two diagonal entries lies in the adjoint orbit of the sum of the two
  elements supported at the corresponding off-diagonal entries. -/
lemma exists_diagDiffℂ_eq_adjointℂ_singleℂ_add_singleℂ {n : ℕ} {p q : Fin n} (h : p ≠ q) :
    ∃ g : specialUnitaryGroup (Fin n) ℂ,
      diagDiffℂ p q = adjointℂ g (singleℂ p q h + singleℂ q p h.symm) := by
  have hdiag : toMatrixℂ (diagDiffℂ p q) = diagonal fun x => toMatrixℂ (diagDiffℂ p q) x x :=
    Matrix.ext fun x y => by
      rcases eq_or_ne x y with rfl | hxy
      · rw [diagonal_apply_eq]
      · rw [diagonal_apply_ne _ hxy]
        simp only [diagDiffℂ, toMatrixℂ_ofTracelessℂ, Matrix.sub_apply, sub_zero,
          single_apply_of_ne _ _ (1 : ℂ) x y fun hc => hxy (hc.1.symm.trans hc.2)]
  have hc : (toMatrixℂ (diagDiffℂ p q) p p - toMatrixℂ (diagDiffℂ p q) q q) / 2 = 1 := by
    simp [diagDiffℂ, h, h.symm]
  obtain ⟨g, hg⟩ := exists_adjointℂ_eq_of_toMatrixℂ_eq_diagonal h hdiag
  have hg' : adjointℂ g (diagDiffℂ p q) = singleℂ p q h + singleℂ q p h.symm := by
    simp only [hg, hc, one_smul]; abel
  exact ⟨g⁻¹, by rw [← hg', Representation.inv_self_apply]⟩

/-- The span of the adjoint orbit of a non-zero element contains an element supported at a single
  off-diagonal entry. -/
lemma exists_singleℂ_mem_span_range_adjointℂ {n : ℕ} {A : Complexification n} (hA : A ≠ 0) :
    ∃ (p q : Fin n) (h : p ≠ q),
      singleℂ p q h ∈ Submodule.span ℂ (Set.range fun g => adjointℂ g A) := by
  obtain ⟨x, y, hxy, hne⟩ | hdiag := em (∃ x y : Fin n, x ≠ y ∧ toMatrixℂ A x y ≠ 0)
  · exact ⟨x, y, hxy, singleℂ_mem_span_range_adjointℂ hxy hne⟩
  push Not at hdiag
  obtain ⟨d, hAd⟩ : ∃ d, toMatrixℂ A = diagonal d :=
    ⟨(toMatrixℂ A).diag, Matrix.ext fun x y => by
      by_cases hxy : x = y <;> simp [Matrix.diag, hxy, hdiag]⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1
    (show d ≠ 0 from fun hd => hA (toMatrixℂ_injective (by simp [hAd, hd])))
  obtain ⟨p, q, hpq, hne⟩ : ∃ p q, p ≠ q ∧ d p ≠ d q := by
    by_contra hc
    push Not at hc
    have hsum : ∑ x, d x = 0 := by rw [← Matrix.trace_diagonal d, ← hAd, trace_toMatrixℂ]
    rw [Finset.sum_congr rfl fun x _ => (eq_or_ne x i).elim (fun hx => hx ▸ rfl)
      fun hx => hc x i hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    have hn : n = 0 := Nat.cast_eq_zero.1 ((mul_eq_zero.1 hsum).resolve_right hi)
    exact absurd i.isLt (by omega)
  obtain ⟨g, hg⟩ := exists_adjointℂ_eq_of_toMatrixℂ_eq_diagonal hpq hAd
  have hentry : toMatrixℂ (adjointℂ g A) p q ≠ 0 := by
    rw [show toMatrixℂ (adjointℂ g A) p q = (d p - d q) / 2 from by
      rw [hg]; simp [singleℂ, diagDiffℂ, hAd, hpq, hpq.symm]]
    exact div_ne_zero (sub_ne_zero.2 hne) two_ne_zero
  refine ⟨p, q, hpq, Submodule.span_mono ?_ (singleℂ_mem_span_range_adjointℂ hpq hentry)⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨k * g, by simp only [map_mul, Module.End.mul_apply]⟩

/-!

## C. Irreducibility and Schur's lemma

### C.1. Irreducibility

The complex adjoint representation has no proper non-zero subrepresentations.

-/

/-- The complex adjoint representation of `SU(n)` is irreducible for `2 ≤ n`. -/
lemma isIrreducible_adjointℂ {n : ℕ} (hn : 2 ≤ n) : (adjointℂ (n := n)).IsIrreducible := by
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hne : singleℂ (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hij ≠ 0 := fun h0 => by
    simpa [singleℂ, toMatrixℂ_ofTracelessℂ] using
      congrArg (fun A => toMatrixℂ A ⟨0, by omega⟩ ⟨1, by omega⟩) h0
  have hbot : (⊥ : Subrepresentation (adjointℂ (n := n))) ≠ ⊤ := fun h => hne <|
    (Submodule.mem_bot ℂ).1 ((congrArg Subrepresentation.toSubmodule h).ge Submodule.mem_top)
  have : Nontrivial (Subrepresentation (adjointℂ (n := n))) := ⟨⊥, ⊤, hbot⟩
  refine ⟨fun W => (eq_or_ne W ⊥).imp id fun hW => ?_⟩
  obtain ⟨A, hAW, hA0⟩ := (Submodule.ne_bot_iff _).1
    fun h => hW (Subrepresentation.toSubmodule_injective h)
  have horb : Submodule.span ℂ (Set.range fun g => adjointℂ g A) ≤ W.toSubmodule :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun g => W.apply_mem_toSubmodule g hAW
  obtain ⟨p, q, hpq, hmem⟩ := exists_singleℂ_mem_span_range_adjointℂ hA0
  have hoff : ∀ (r s : Fin n) (h : r ≠ s), singleℂ r s h ∈ W.toSubmodule := fun r s h => by
    obtain ⟨g, hg⟩ := exists_adjointℂ_singleℂ_eq_singleℂ hpq h
    exact hg ▸ W.apply_mem_toSubmodule g (horb hmem)
  refine Subrepresentation.toSubmodule_injective
    (submodule_eq_top_of_singleℂ_mem_of_diagDiffℂ_mem hoff fun r s => ?_)
  rcases eq_or_ne r s with rfl | h
  · rw [show diagDiffℂ r r = 0 from toMatrixℂ_injective (by simp [diagDiffℂ])]
    exact Submodule.zero_mem _
  obtain ⟨g, hg⟩ := exists_diagDiffℂ_eq_adjointℂ_singleℂ_add_singleℂ h
  exact hg ▸ W.apply_mem_toSubmodule g (add_mem (hoff r s h) (hoff s r h.symm))

/-!

### C.2. Schur's lemma

-/

/-- An endomorphism of the complexification commuting with the adjoint action is a scalar. -/
lemma end_eq_smul_id_of_commute_adjointℂ {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : ∀ A : Complexification n, A = 0 := by
      interval_cases n
      · exact fun A => toMatrixℂ_injective (Subsingleton.elim _ _)
      · exact fun A => toMatrixℂ_injective (Matrix.ext fun x y => by
          simpa [Subsingleton.elim x 0, Subsingleton.elim y 0, Matrix.trace_fin_one] using
            trace_toMatrixℂ A)
    exact ⟨0, LinearMap.ext fun A => (h0 (T A)).trans (by simp)⟩
  · have := isIrreducible_adjointℂ hn
    obtain ⟨μ, hμ⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := adjointℂ (n := n))).2 ⟨T, hT⟩
    exact ⟨μ, LinearMap.ext fun A => by simpa using (DFunLike.congr_fun hμ A).symm⟩

end SULieAlgebra
