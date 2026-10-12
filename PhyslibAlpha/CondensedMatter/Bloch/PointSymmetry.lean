/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Brillouin
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Symmetry of the Bloch matrices of a crystal

The Bloch matrices of a symmetric crystal at momenta in one orbit of the point group are
conjugate, and at a momentum fixed by a symmetry they commute with it.

## i. Overview

Take a crystal with translation group `G` and the finite set `F` of sites in a cell, and a
translation-invariant Hamiltonian on `ℓ²(G, ℂ^F)` given by hopping matrices `T r`. Its Bloch
matrix at a momentum `χ` is `b(χ) = ∑_r χ(r) T r`. A symmetry `s = (A, σ, b)` moves the site `i`
of the cell `n` to the site `σ i` of the cell `A n + b i`. On the Fourier transform
`ψ̂(χ) = ∑_n χ(n) ψ(n)` it acts by
`(U_s ψ)^(χ) = V_s(χ) ψ̂(χ ∘ A)`, where the fibre matrix `V_s(χ)` is the monomial matrix with the
entry `χ(b i)` at `(σ i, i)`. The symmetry carries the fibre at `χ ∘ A` to the fibre at
`s • χ = χ ∘ A⁻¹`. The fibre matrices satisfy the cocycle identity
`V_{st}(χ) = V_s(χ) V_t(s⁻¹ • χ)`, and they are unitary. The phases `χ(b i)` come from the
offsets `b i` of the sites: for a symmetry that is a pure rotation or reflection of a crystal
with one site per cell they are absent, and a screw axis or glide plane is what makes them
momentum dependent.

The Hamiltonian commutes with `U_s` exactly when `V_s(s • χ) b(χ) = b(s • χ) V_s(s • χ)` for all
`χ`, which is what *covariance* of the symbol means. It holds when the hopping is invariant
under the symmetry, `T (A r + b i - b j) (σ i) (σ j) = T r i j`. Two consequences follow. Along
an orbit of the point group, the Bloch matrices are unitarily equivalent, so their eigenvalues
are the same: the bands are functions on the irreducible zone. At a momentum fixed by `s`, the
Bloch matrix commutes with `V_s(χ)`, so its eigenspaces are representation spaces of the little
group, and an eigenvalue of a Hermitian Bloch matrix has multiplicity at least the least
dimension of an invariant subspace: the degeneracies forced by symmetry.

## ii. Key results

- `fibreMatrix` : the monomial matrix of a symmetry at a momentum.
- `fibreMatrix_mul` : the cocycle identity.
- `fibreMatrix_unitary` : the fibre matrices are unitary.
- `hoppingSymbol` : the Bloch matrix of a family of hopping matrices.
- `IsCovariant`, `isCovariant_of_invariant` : invariant hopping has a covariant symbol.
- `eigenvalues_eq_of_covariant` : the bands agree at momenta related by a symmetry.
- `bandsOnZone` : the bands are functions on the irreducible zone.
- `uniformHopping`, `isCovariant_uniformHopping` : uniform hopping on a periodic graph is covariant
  under all its bond-preserving symmetries.
- `iUnion_spectrum_eq_of_covers` : the spectrum is the union over an irreducible zone.
- `two_le_finrank_of_no_common_eigenvector` : a criterion for twofold degeneracy.
- `le_finrank_eigenspace`, `le_finrank_eigenspace_of_littleGroup` : the multiplicity of an
  eigenvalue at a momentum fixed by the symmetries is at least the least dimension of an
  invariant subspace.

## iii. Table of contents

- A. The fibre matrices
- B. The symbol of a hopping family
- C. Bands on the irreducible zone
- D. The little group at a momentum
- E. Hopping from a graph and its symmetries
- F. Restricting to a set of representatives

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Bloch

open CondensedMatter.Crystal
open scoped Matrix

variable {G F : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [Fintype F] [DecidableEq F]

/-! ## A. The fibre matrices -/

/-- The fibre matrix of a symmetry `s = (A, σ, b)` at the momentum `χ`: the monomial matrix with
the entry `χ(b i)` at `(σ i, i)`. -/
noncomputable def fibreMatrix (s : CellSymmetry G F) (χ : BrillouinZone G) :
    Matrix F F ℂ :=
  Matrix.of fun j i => if j = s.perm i then (χ (Multiplicative.ofAdd (s.shift i)) : ℂ) else 0

omit [DiscreteTopology G] in
omit [Fintype F] in
lemma fibreMatrix_apply (s : CellSymmetry G F) (χ : BrillouinZone G) (j i : F) :
    fibreMatrix s χ j i = if j = s.perm i then (χ (Multiplicative.ofAdd (s.shift i)) : ℂ) else 0 :=
  rfl

/-- **The cocycle identity** for the fibre matrices: `V_{st}(χ) = V_s(χ) V_t(s⁻¹ • χ)`. -/
lemma fibreMatrix_mul (s t : CellSymmetry G F) (χ : BrillouinZone G) :
    fibreMatrix (s * t) χ = fibreMatrix s χ * fibreMatrix t (s⁻¹ • χ) := by
  ext j i
  rw [Matrix.mul_apply, Finset.sum_eq_single (t.perm i)]
  · have hlin : ((s⁻¹ • χ) (Multiplicative.ofAdd (t.shift i)) : ℂ) =
        χ (Multiplicative.ofAdd (s.linear (t.shift i))) := rfl
    simp only [fibreMatrix_apply, CellSymmetry.perm_mul, CellSymmetry.shift_mul, hlin]
    by_cases h : j = s.perm (t.perm i)
    · simp only [h, ite_true, ofAdd_add, map_mul, Circle.coe_mul, mul_comm]
    · simp [h]
  · intro k _ hk
    simp [fibreMatrix_apply, hk]
  · exact fun h => absurd (Finset.mem_univ _) h

private lemma circle_mul_star (z : Circle) : (z : ℂ) * star (z : ℂ) = 1 := by
  rw [Complex.star_def, Complex.mul_conj]
  simp

omit [DiscreteTopology G] in
/-- The fibre matrices are unitary. -/
lemma fibreMatrix_mul_conjTranspose (s : CellSymmetry G F) (χ : BrillouinZone G) :
    fibreMatrix s χ * (fibreMatrix s χ)ᴴ = 1 := by
  ext j l
  rw [Matrix.mul_apply, Finset.sum_eq_single (s.perm.symm j)]
  · simp only [Matrix.conjTranspose_apply, fibreMatrix_apply, Equiv.apply_symm_apply, ite_true,
      Matrix.one_apply]
    by_cases h : j = l
    · subst h
      simpa [Complex.star_def] using circle_mul_star (χ (Multiplicative.ofAdd (s.shift
        (s.perm.symm j))))
    · simp [h, Ne.symm h]
  · intro k _ hk
    have : j ≠ s.perm k := fun h => hk (by rw [h]; simp)
    simp [fibreMatrix_apply, this]
  · exact fun h => absurd (Finset.mem_univ _) h

omit [DiscreteTopology G] in
/-- The fibre matrices are unitary. -/
lemma fibreMatrix_conjTranspose_mul (s : CellSymmetry G F) (χ : BrillouinZone G) :
    (fibreMatrix s χ)ᴴ * fibreMatrix s χ = 1 :=
  mul_eq_one_comm.1 (fibreMatrix_mul_conjTranspose s χ)

/-! ## B. The symbol of a hopping family -/

/-- The Bloch matrix `b(χ) = ∑_r χ(r) T r` of a finite family of hopping matrices. -/
noncomputable def hoppingSymbol (T : G →₀ Matrix F F ℂ) (χ : BrillouinZone G) : Matrix F F ℂ :=
  T.sum fun r M => (χ (Multiplicative.ofAdd r) : ℂ) • M

/-- A family of hopping matrices is invariant under a symmetry `(A, σ, b)` when
`T (A r + b i - b j) (σ i) (σ j) = T r i j`: the amplitude to hop from `j` to `i` across `r`
equals the amplitude between the transformed sites across the transformed displacement. -/
def IsInvariant (T : G →₀ Matrix F F ℂ) (s : CellSymmetry G F) : Prop :=
  ∀ r i j, T (s.linear r + s.shift i - s.shift j) (s.perm i) (s.perm j) = T r i j

/-- A symbol `b` on the Brillouin zone is covariant under a symmetry when the fibre matrix
intertwines it: `V_s(s • χ) b(χ) = b(s • χ) V_s(s • χ)`. -/
def IsCovariant (b : BrillouinZone G → Matrix F F ℂ) (s : CellSymmetry G F) : Prop :=
  ∀ χ, fibreMatrix s (s • χ) * b χ = b (s • χ) * fibreMatrix s (s • χ)

/-- The entries of a hopping family at a fixed pair of orbitals, as a finitely supported function
of the displacement. -/
noncomputable def entry (T : G →₀ Matrix F F ℂ) (i j : F) : G →₀ ℂ :=
  Finsupp.mapRange (fun M : Matrix F F ℂ => M i j) rfl T

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
lemma hoppingSymbol_apply (T : G →₀ Matrix F F ℂ) (χ : BrillouinZone G) (i j : F) :
    hoppingSymbol T χ i j = (entry T i j).sum fun r m => (χ (Multiplicative.ofAdd r) : ℂ) * m := by
  classical
  rw [hoppingSymbol, Finsupp.sum, Matrix.sum_apply,
    Finsupp.sum_of_support_subset (entry T i j) Finsupp.support_mapRange (fun r m =>
      (χ (Multiplicative.ofAdd r) : ℂ) * m) (fun r _ => by simp)]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, entry]
  rfl

omit [Fintype F] in
omit [DecidableEq F] in
lemma smul_apply_linear (s : CellSymmetry G F) (χ : BrillouinZone G) (r : G) :
    (s • χ) (Multiplicative.ofAdd (s.linear r)) = χ (Multiplicative.ofAdd r) := by
  rw [Crystal.smul_apply, AddEquiv.symm_apply_apply]

/-- **Invariant hopping has a covariant Bloch symbol.** -/
lemma isCovariant_of_invariant {T : G →₀ Matrix F F ℂ} {s : CellSymmetry G F}
    (hT : IsInvariant T s) : IsCovariant (hoppingSymbol T) s := by
  classical
  intro χ'
  set χ := s • χ' with hχ
  ext a c
  obtain ⟨i, rfl⟩ := s.perm.surjective a
  have hL : (fibreMatrix s χ * hoppingSymbol T χ') (s.perm i) c =
      (χ (Multiplicative.ofAdd (s.shift i)) : ℂ) * hoppingSymbol T χ' i c := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [fibreMatrix_apply]
    · intro k _ hk
      have : s.perm i ≠ s.perm k := fun h => hk (s.perm.injective h).symm
      simp [fibreMatrix_apply, this]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hR : (hoppingSymbol T χ * fibreMatrix s χ) (s.perm i) c =
      hoppingSymbol T χ (s.perm i) (s.perm c) * (χ (Multiplicative.ofAdd (s.shift c)) : ℂ) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s.perm c)]
    · simp [fibreMatrix_apply]
    · intro k _ hk
      simp [fibreMatrix_apply, hk]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hL, hR]
  let e : G ≃ G := s.linear.toEquiv.trans (Equiv.addRight (s.shift i - s.shift c))
  have he : ∀ r', e r' = s.linear r' + s.shift i - s.shift c := fun r' => by
    simp [e, add_sub_assoc]
  have hE : Finsupp.equivMapDomain e.symm (entry T (s.perm i) (s.perm c)) = entry T i c := by
    ext r'
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
    simp only [entry]
    rw [he]
    exact hT r' i c
  rw [hoppingSymbol_apply, hoppingSymbol_apply, ← hE, Finsupp.sum_equivMapDomain, Finsupp.mul_sum,
    Finsupp.sum_mul]
  refine Finsupp.sum_congr fun r _ => ?_
  set m := entry T (s.perm i) (s.perm c) r
  set r' := e.symm r with hr'
  have hr : r = s.linear r' + s.shift i - s.shift c := by
    rw [hr', ← he, Equiv.apply_symm_apply]
  have h1 : (χ' (Multiplicative.ofAdd r') : ℂ) = χ (Multiplicative.ofAdd (s.linear r')) := by
    rw [hχ, smul_apply_linear]
  have h2 : Multiplicative.ofAdd r * Multiplicative.ofAdd (s.shift c) =
      Multiplicative.ofAdd (s.linear r') * Multiplicative.ofAdd (s.shift i) := by
    rw [← ofAdd_add, ← ofAdd_add]
    congr 1
    rw [hr]
    abel
  have hχr : (χ (Multiplicative.ofAdd r) : ℂ) * (χ (Multiplicative.ofAdd (s.shift c)) : ℂ) =
      (χ' (Multiplicative.ofAdd r') : ℂ) * (χ (Multiplicative.ofAdd (s.shift i)) : ℂ) := by
    rw [h1, ← Circle.coe_mul, ← Circle.coe_mul,
      ← map_mul χ (Multiplicative.ofAdd r) (Multiplicative.ofAdd (s.shift c)),
      ← map_mul χ (Multiplicative.ofAdd (s.linear r')) (Multiplicative.ofAdd (s.shift i)), h2]
  linear_combination (-m) * hχr

/-! ## C. Bands on the irreducible zone -/

/-- A covariant symbol is conjugated by the fibre matrix between a momentum and its image. -/
lemma conj_of_covariant {b : BrillouinZone G → Matrix F F ℂ} {s : CellSymmetry G F}
    (hb : IsCovariant b s) (χ : BrillouinZone G) :
    b (s • χ) = fibreMatrix s (s • χ) * b χ * (fibreMatrix s (s • χ))ᴴ := by
  rw [hb χ, Matrix.mul_assoc, fibreMatrix_mul_conjTranspose, Matrix.mul_one]

/-- The Bloch matrices at related momenta have the same characteristic polynomial. -/
lemma charpoly_eq_of_covariant {b : BrillouinZone G → Matrix F F ℂ} {s : CellSymmetry G F}
    (hb : IsCovariant b s) (χ : BrillouinZone G) :
    (b (s • χ)).charpoly = (b χ).charpoly := by
  rw [conj_of_covariant hb χ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    fibreMatrix_conjTranspose_mul, Matrix.one_mul]

/-- **The bands agree at momenta related by a symmetry.** If the Bloch matrices are Hermitian,
their eigenvalues at `χ` and `s • χ` coincide. -/
lemma eigenvalues_eq_of_covariant {b : BrillouinZone G → Matrix F F ℂ}
    (hH : ∀ χ, (b χ).IsHermitian) {s : CellSymmetry G F} (hb : IsCovariant b s)
    (χ : BrillouinZone G) : (hH (s • χ)).eigenvalues = (hH χ).eigenvalues :=
  (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hH _) (hH _)).2
    (charpoly_eq_of_covariant hb χ)

/-- **The bands are functions on the irreducible zone.** For a symbol that is covariant under all
bond-preserving symmetries of a crystal, the eigenvalues of the Bloch matrices depend only on the
orbit of the momentum under the point group. -/
noncomputable def bandsOnZone {g : PeriodicGraph (Crystal.ofUnitCell G F)}
    {b : BrillouinZone G → Matrix F F ℂ} (hH : ∀ χ, (b χ).IsHermitian)
    (hb : ∀ s : g.symmetries, IsCovariant b s) : g.IrreducibleZone → (F → ℝ) :=
  Quotient.lift (fun χ => (hH χ).eigenvalues) fun χ ψ h => by
    obtain ⟨p, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective p
    exact eigenvalues_eq_of_covariant hH (hb s) ψ

/-! ## D. The little group at a momentum -/

/-- At a momentum fixed by a symmetry, the Bloch matrix commutes with its fibre matrix. -/
lemma commute_of_smul_eq {b : BrillouinZone G → Matrix F F ℂ} {s : CellSymmetry G F}
    (hb : IsCovariant b s) {χ : BrillouinZone G} (hχ : s • χ = χ) :
    fibreMatrix s χ * b χ = b χ * fibreMatrix s χ := by
  have := hb χ
  rwa [hχ] at this

/-- **Symmetry-enforced degeneracy.** If `M` commutes with a set of matrices and every nonzero
subspace invariant under them has dimension at least `m`, every eigenspace of `M` has dimension
at least `m`. -/
lemma le_finrank_eigenspace (M : Matrix F F ℂ) (S : Set (Matrix F F ℂ))
    (hcomm : ∀ V ∈ S, V * M = M * V) {m : ℕ}
    (hS : ∀ W : Submodule ℂ (F → ℂ), W ≠ ⊥ → (∀ V ∈ S, ∀ w ∈ W, V.mulVec w ∈ W) →
      m ≤ Module.finrank ℂ W) (μ : ℂ) (hμ : ∃ v : F → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v) :
    m ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' M) μ) := by
  refine hS _ ?_ ?_
  · obtain ⟨v, hv, h⟩ := hμ
    refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact h
  · intro V hV w hw
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm V hV, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]

/-- **Degeneracy forced by the little group.** For a symbol covariant under the bond-preserving
symmetries of a crystal, if every nonzero subspace of `ℂ^F` invariant under the fibre matrices of
the little group at `χ` has dimension at least `m`, every eigenspace of the Bloch matrix at `χ` has
dimension at least `m`. -/
lemma le_finrank_eigenspace_of_littleGroup {g : PeriodicGraph (Crystal.ofUnitCell G F)}
    {b : BrillouinZone G → Matrix F F ℂ} (hb : ∀ s : g.symmetries, IsCovariant b s)
    (χ : BrillouinZone G) {m : ℕ}
    (hS : ∀ W : Submodule ℂ (F → ℂ), W ≠ ⊥ →
      (∀ s ∈ g.littleGroup χ, ∀ w ∈ W, (fibreMatrix (s : CellSymmetry G F) χ).mulVec w ∈ W) →
      m ≤ Module.finrank ℂ W) (μ : ℂ) (hμ : ∃ v : F → ℂ, v ≠ 0 ∧ (b χ).mulVec v = μ • v) :
    m ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (b χ)) μ) := by
  refine le_finrank_eigenspace (b χ) {V | ∃ s ∈ g.littleGroup χ,
    V = fibreMatrix (s : CellSymmetry G F) χ} ?_ (fun W hW hinv => hS W hW fun s hs w hw =>
      hinv _ ⟨s, hs, rfl⟩ w hw) μ hμ
  rintro _ ⟨s, hs, rfl⟩
  exact commute_of_smul_eq (hb s) ((g.mem_littleGroup χ s).1 hs)

/-! ## E. Hopping from a graph and its symmetries -/

section Uniform

open scoped Classical

variable [Finite F]

/-- Hopping with the amplitude `t` between any two bonded sites of a periodic graph: the entry
`(i, j)` of the matrix at the displacement `r` is `t` when the site `j` of a cell is bonded to the
site `i` of the cell displaced by `r`. -/
noncomputable def uniformHopping (g : PeriodicGraph (Crystal.ofUnitCell G F)) (t : ℂ) :
    G →₀ Matrix F F ℂ :=
  haveI := Fintype.ofFinite F
  Finsupp.onFinset (Finset.univ.biUnion fun j => (g.neighbors ⟨0, j⟩).image CellSite.cell)
    (fun r => Matrix.of fun i j => if g.Bonded j i r then t else 0) (by
      intro r hr
      obtain ⟨i, j, hij⟩ : ∃ i j, (if g.Bonded j i r then t else 0) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hr (by ext i j; exact hcon i j)
      have hb : g.Bonded j i r := by
        by_contra hnb
        exact hij (ite_eq_right hnb)
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2
        ⟨⟨r, i⟩, (g.mem_neighbors _ _).2 hb, rfl⟩⟩)

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
omit [TopologicalSpace G] in
lemma uniformHopping_apply (g : PeriodicGraph (Crystal.ofUnitCell G F)) (t : ℂ) (r : G) (i j : F) :
    uniformHopping g t r i j = if g.Bonded j i r then t else 0 := rfl

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
omit [TopologicalSpace G] in
/-- **Uniform hopping is invariant under every bond-preserving symmetry.** -/
lemma isInvariant_uniformHopping (g : PeriodicGraph (Crystal.ofUnitCell G F)) (t : ℂ)
    {s : CellSymmetry G F} (hs : s ∈ g.symmetries) : IsInvariant (uniformHopping g t) s := by
  intro r i j
  rw [uniformHopping_apply, uniformHopping_apply]
  exact if_congr ((PeriodicGraph.mem_symmetries_iff g s).1 hs j i r).symm rfl rfl

/-- **Uniform hopping has a covariant Bloch symbol under every bond-preserving symmetry.** -/
lemma isCovariant_uniformHopping (g : PeriodicGraph (Crystal.ofUnitCell G F)) (t : ℂ)
    (s : g.symmetries) : IsCovariant (hoppingSymbol (uniformHopping g t)) s :=
  isCovariant_of_invariant (isInvariant_uniformHopping g t s.2)

end Uniform

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
/-- If `(T r)ᴴ = T (-r)` for all `r`, the Bloch matrices are Hermitian. -/
lemma isHermitian_hoppingSymbol {T : G →₀ Matrix F F ℂ} (hT : ∀ r, (T r)ᴴ = T (-r))
    (χ : BrillouinZone G) : (hoppingSymbol T χ).IsHermitian := by
  classical
  set S : Finset G := T.support ∪ T.support.image Neg.neg with hS
  have hexp : hoppingSymbol T χ = ∑ r ∈ S, (χ (Multiplicative.ofAdd r) : ℂ) • T r := by
    rw [hoppingSymbol, Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_left (fun r _ hr => by
      simp [Finsupp.notMem_support_iff.mp hr])
  have hneg : ∀ r ∈ S, -r ∈ S := by
    intro r hr
    rw [hS, Finset.mem_union, Finset.mem_image] at hr ⊢
    rcases hr with h | ⟨x, hx, rfl⟩
    · exact Or.inr ⟨r, h, rfl⟩
    · exact Or.inl (by simpa using hx)
  rw [Matrix.IsHermitian, hexp, Matrix.conjTranspose_sum]
  refine Finset.sum_equiv (Equiv.neg G) (fun r => ⟨hneg r, fun h => by simpa using hneg _ h⟩)
    (fun r _ => ?_)
  rw [Matrix.conjTranspose_smul, hT, Equiv.neg_apply]
  congr 1
  rw [ofAdd_neg, map_inv, Circle.coe_inv_eq_conj]
  rfl

section UniformHermitian

open scoped Classical

variable [Finite F]

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
omit [TopologicalSpace G] in
/-- Bonds are symmetric: the bond from `i` to `j` across `d` is the bond from `j` to `i` across
`-d`. -/
lemma bonded_symm (g : PeriodicGraph (Crystal.ofUnitCell G F)) (i j : F) (d : G) :
    g.Bonded i j d ↔ g.Bonded j i (-d) := by
  have h := PeriodicGraph.adj_iff_bonded g d 0 j i
  rw [zero_sub] at h
  change g.toSimpleGraph.Adj ⟨0, i⟩ ⟨d, j⟩ ↔ _
  rw [g.toSimpleGraph.adj_comm]
  exact h

omit [DiscreteTopology G] in
omit [Fintype F] in
omit [DecidableEq F] in
/-- Uniform real hopping gives Hermitian Bloch matrices at every momentum. -/
lemma isHermitian_hoppingSymbol_uniform (g : PeriodicGraph (Crystal.ofUnitCell G F)) (t : ℝ)
    (χ : BrillouinZone G) : (hoppingSymbol (uniformHopping g (t : ℂ)) χ).IsHermitian := by
  refine isHermitian_hoppingSymbol (fun r => ?_) χ
  ext i j
  simp only [Matrix.conjTranspose_apply, uniformHopping_apply]
  have : g.Bonded i j r ↔ g.Bonded j i (-r) := bonded_symm g i j r
  simp only [this]
  split_ifs <;> simp [Complex.conj_ofReal]

end UniformHermitian

/-! ## F. Restricting to a set of representatives -/

/-- A set of momenta covers the orbits of the point group when every momentum is carried into it by
some element of the point group. An irreducible zone is a set that covers the orbits. -/
def CoversOrbits (g : PeriodicGraph (Crystal.ofUnitCell G F)) (D : Set (BrillouinZone G)) : Prop :=
  ∀ χ : BrillouinZone G, ∃ p : g.pointGroup, p • χ ∈ D

/-- The spectrum of a Bloch matrix is the set of its eigenvalues. -/
lemma spectrum_eq_range_eigenvalues {M : Matrix F F ℂ} (hM : M.IsHermitian) :
    spectrum ℂ M = ((↑) : ℝ → ℂ) '' Set.range hM.eigenvalues :=
  hM.spectrum_eq_image_range

/-- **The spectra of the Bloch matrices at related momenta agree.** -/
lemma spectrum_eq_of_covariant {b : BrillouinZone G → Matrix F F ℂ}
    (hH : ∀ χ, (b χ).IsHermitian) {s : CellSymmetry G F} (hb : IsCovariant b s)
    (χ : BrillouinZone G) : spectrum ℂ (b (s • χ)) = spectrum ℂ (b χ) := by
  rw [spectrum_eq_range_eigenvalues (hH _), spectrum_eq_range_eigenvalues (hH _),
    eigenvalues_eq_of_covariant hH hb χ]

/-- **The spectrum over the whole Brillouin zone is the spectrum over an irreducible zone.** If a
symbol is covariant under the bond-preserving symmetries, it suffices to take the union of the
spectra of its Bloch matrices over a set of momenta that covers the orbits of the point group. -/
lemma iUnion_spectrum_eq_of_covers {g : PeriodicGraph (Crystal.ofUnitCell G F)}
    {b : BrillouinZone G → Matrix F F ℂ} (hH : ∀ χ, (b χ).IsHermitian)
    (hb : ∀ s : g.symmetries, IsCovariant b s) {D : Set (BrillouinZone G)}
    (hD : CoversOrbits g D) :
    (⋃ χ : BrillouinZone G, spectrum ℂ (b χ)) = ⋃ χ ∈ D, spectrum ℂ (b χ) := by
  refine Set.Subset.antisymm ?_ (Set.iUnion₂_subset fun χ _ => Set.subset_iUnion
    (fun χ => spectrum ℂ (b χ)) χ)
  refine Set.iUnion_subset fun χ => ?_
  obtain ⟨p, hp⟩ := hD χ
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective p
  have hps : p • χ = (s : CellSymmetry G F) • χ := by rw [← hs]; rfl
  refine Set.Subset.trans ?_ (Set.subset_iUnion₂ (p • χ) hp)
  rw [hps]
  exact (spectrum_eq_of_covariant hH (hb s) χ).symm.le

omit [DecidableEq F] in
/-- **A criterion for twofold degeneracy.** If the matrices in `S` have no common eigenvector, every
nonzero invariant subspace has dimension at least `2`. Combined with
`le_finrank_eigenspace_of_littleGroup`, this forces every eigenvalue of the Bloch matrix at a
momentum whose little group has no common eigenvector in `ℂ^F` to be at least twofold degenerate. -/
lemma two_le_finrank_of_no_common_eigenvector (S : Set (Matrix F F ℂ))
    (h : ¬∃ v : F → ℂ, v ≠ 0 ∧ ∀ V ∈ S, ∃ c : ℂ, V.mulVec v = c • v)
    (W : Submodule ℂ (F → ℂ)) (hW : W ≠ ⊥) (hinv : ∀ V ∈ S, ∀ w ∈ W, V.mulVec w ∈ W) :
    2 ≤ Module.finrank ℂ W := by
  by_contra hl
  push Not at hl
  have hpos : 0 < Module.finrank ℂ W := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hW
    have : Nonempty W := ⟨⟨w, hw⟩⟩
    have : Nontrivial W := ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have h1 : Module.finrank ℂ W = 1 := by omega
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  refine h ⟨(v : F → ℂ), fun h0 => hv0 (Subtype.ext h0), fun V hV => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨V.mulVec (v : F → ℂ), hinv V hV v v.2⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

end CondensedMatter.Bloch
