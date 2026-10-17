/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Bands

/-!

# Hopping operators and their Bloch matrices

The finite-range translation-invariant operators are the operators whose symbol is a trigonometric
polynomial.

## i. Overview

An operator `∑_r π(r) ι(A_r)` with finitely many matrices `A_r` couples each point to finitely many
other points through the matrices `A_r`. The general theory of `BlochFloquet` applies to it: its
symbol is the Bloch matrix `b(χ) = ∑_r χ(r) A_r`, a trigonometric polynomial, and the operator is
the integral of its Bloch matrix. This covers tight-binding Hamiltonians, the dynamical matrices of
harmonic lattices, adjacency operators of periodic graphs, and the transfer operators of
translation-invariant classical lattice models alike.

## ii. Key results

- `UnitaryRep.hopping` : the finite-range translation-invariant operator with matrices `A_r`.
- `UnitaryRep.blochMatrix` : its Bloch matrix.
- `UnitaryRep.blochHom_blochMatrix` : the operator is the integral of its Bloch matrix.
- `UnitaryRep.spectrum_hopping_subset` : the spectrum is contained in the union of the bands.
- `UnitaryRep.symmetrize` : the Hermitian completion of a family of hopping matrices.
- `UnitaryRep.isHermitian_blochMatrix` : the Bloch matrix of a Hermitian hopping family is
  Hermitian at every crystal momentum.

## iii. Table of contents

- A. The hopping operator and its Bloch matrix
- B. The spectrum
- C. Hermitian hopping

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology WeakDual
open scoped ComplexOrder CStarAlgebra InnerProductSpace Matrix

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]
variable {N : ℕ} (ι : Matrix (Fin N) (Fin N) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (hι : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (g : Multiplicative G),
  Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) (ι M))

/-! ## A. The hopping operator and its Bloch matrix -/

/-- A translation-invariant hopping operator `∑_r π(r) ι(A_r)` with finitely many matrices `A_r`,
the amplitude of hopping by the lattice vector `r` between orbitals. -/
def hopping (A : G →₀ Matrix (Fin N) (Fin N) ℂ) : H →L[ℂ] H :=
  A.sum fun r M => ((π (Multiplicative.ofAdd r) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * ι M

/-- The Bloch matrix `b(χ) = ∑_r χ(r) A_r` of a hopping operator, a continuous matrix-valued
function on the Brillouin zone. -/
def blochMatrix (A : G →₀ Matrix (Fin N) (Fin N) ℂ) :
    C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ) where
  toFun χ := A.sum fun r M => ((χ (Multiplicative.ofAdd r) : Circle) : ℂ) • M
  continuous_toFun := by
    refine continuous_finsetSum _ fun r _ => ?_
    exact (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G)
      (Multiplicative.ofAdd r)).smul continuous_const

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma blochMatrix_apply (A : G →₀ Matrix (Fin N) (Fin N) ℂ)
    (χ : PontryaginDual (Multiplicative G)) :
    blochMatrix A χ = A.sum fun r M => ((χ (Multiplicative.ofAdd r) : Circle) : ℂ) • M := rfl

include hι

/-- **The hopping operator is the integral of its Bloch matrix.** -/
lemma blochHom_blochMatrix (A : G →₀ Matrix (Fin N) (Fin N) ℂ) :
    blochHom π ι hι (blochMatrix A) = hopping π ι A := by
  have hentry : ∀ i j : Fin N, calculus π (entry (blochMatrix A) i j) =
      ∑ r ∈ A.support, A r i j • ((π (Multiplicative.ofAdd r) : unitary (H →L[ℂ] H)) :
        H →L[ℂ] H) := by
    intro i j
    have : entry (blochMatrix A) i j = ∑ r ∈ A.support, A r i j •
        (⟨fun χ => ((χ (Multiplicative.ofAdd r) : Circle) : ℂ),
          TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G)
            (Multiplicative.ofAdd r)⟩ : C(PontryaginDual (Multiplicative G), ℂ)) := by
      ext χ
      simp [entry, blochMatrix_apply, Finsupp.sum, Matrix.sum_apply, mul_comm]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, calculus_character]
  show blochOp π ι (blochMatrix A) = hopping π ι A
  simp only [blochOp, hentry, Finset.sum_mul, smul_mul_assoc]
  rw [hopping, Finsupp.sum]
  calc ∑ i, ∑ j, ∑ r ∈ A.support, (A r i j • ((π (Multiplicative.ofAdd r) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H)) * ι (Matrix.single i j 1)
      = ∑ r ∈ A.support, ∑ i, ∑ j, (A r i j • ((π (Multiplicative.ofAdd r) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H)) * ι (Matrix.single i j 1) := by
        simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin N))) (t := A.support)]
    _ = _ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have hA : ι (A r) = ∑ i, ∑ j, A r i j • ι (Matrix.single i j 1) := by
          conv_lhs => rw [Matrix.matrix_eq_sum_single (A r)]
          simp only [map_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have : Matrix.single i j (A r i j) = A r i j • Matrix.single i j (1 : ℂ) := by
            rw [Matrix.smul_single]; simp
          rw [this, map_smul]
        rw [hA, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm]

/-! ## B. The spectrum -/

include hι

/-- The spectrum of a finite-range translation-invariant operator is contained in the union of the
spectra of its Bloch matrices. -/
lemma spectrum_hopping_subset (A : G →₀ Matrix (Fin N) (Fin N) ℂ) :
    spectrum ℂ (hopping π ι A) ⊆
      ⋃ χ : PontryaginDual (Multiplicative G), spectrum ℂ (blochMatrix A χ) := by
  rw [← blochHom_blochMatrix π ι hι A]
  exact spectrum_blochHom_subset π ι hι _


/-! ## C. Hermitian hopping -/

omit hι

omit [DiscreteTopology G] [BorelSpace (PontryaginDual (Multiplicative G))]
  [MeasurableSpace (PontryaginDual (Multiplicative G))] in
/-- The Hermitian completion of a family of hopping matrices: the amplitude for hopping by `r` is
`A r` plus the adjoint of the amplitude for hopping back by `-r`. -/
def symmetrize (A : G →₀ Matrix (Fin N) (Fin N) ℂ) : G →₀ Matrix (Fin N) (Fin N) ℂ :=
  A + (A.equivMapDomain (Equiv.neg G)).mapRange Matrix.conjTranspose Matrix.conjTranspose_zero

omit [DiscreteTopology G] [BorelSpace (PontryaginDual (Multiplicative G))]
  [MeasurableSpace (PontryaginDual (Multiplicative G))] [TopologicalSpace G] in
lemma symmetrize_apply (A : G →₀ Matrix (Fin N) (Fin N) ℂ) (r : G) :
    symmetrize A r = A r + (A (-r))ᴴ := by
  simp [symmetrize, Finsupp.equivMapDomain_apply]

omit [DiscreteTopology G] [BorelSpace (PontryaginDual (Multiplicative G))]
  [MeasurableSpace (PontryaginDual (Multiplicative G))] [TopologicalSpace G] in
/-- A symmetrized family of hopping matrices satisfies `(A r)ᴴ = A (-r)`. -/
lemma conjTranspose_symmetrize (A : G →₀ Matrix (Fin N) (Fin N) ℂ) (r : G) :
    (symmetrize A r)ᴴ = symmetrize A (-r) := by
  rw [symmetrize_apply, symmetrize_apply, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose,
    neg_neg, add_comm]

omit [DiscreteTopology G] [BorelSpace (PontryaginDual (Multiplicative G))]
  [MeasurableSpace (PontryaginDual (Multiplicative G))] in
/-- **Hermitian hopping gives Hermitian Bloch matrices.** If `(A r)ᴴ = A (-r)` for every `r`, then
the Bloch matrix `∑_r χ(r) A_r` is Hermitian at every crystal momentum `χ`. -/
lemma isHermitian_blochMatrix (A : G →₀ Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ r, (A r)ᴴ = A (-r)) (χ : PontryaginDual (Multiplicative G)) :
    (blochMatrix A χ).IsHermitian := by
  classical
  set S : Finset G := A.support ∪ A.support.image Neg.neg with hS
  have hsum : ∀ f : G → Matrix (Fin N) (Fin N) ℂ, (∀ r ∉ A.support, f r = 0) →
      A.sum (fun r _ => f r) = ∑ r ∈ S, f r := by
    intro f hf
    exact Finset.sum_subset (Finset.subset_union_left) (fun r _ hr => hf r hr)
  have hexp : blochMatrix A χ = ∑ r ∈ S, ((χ (Multiplicative.ofAdd r) : Circle) : ℂ) • A r := by
    rw [blochMatrix_apply]
    exact hsum (fun r => ((χ (Multiplicative.ofAdd r) : Circle) : ℂ) • A r)
      (fun r hr => by simp [Finsupp.notMem_support_iff.mp hr])
  rw [Matrix.IsHermitian, hexp, Matrix.conjTranspose_sum]
  have hneg : ∀ r ∈ S, -r ∈ S := by
    intro r hr
    rw [hS, Finset.mem_union, Finset.mem_image] at hr ⊢
    rcases hr with h | ⟨x, hx, rfl⟩
    · exact Or.inr ⟨r, h, rfl⟩
    · exact Or.inl (by simpa using hx)
  refine Finset.sum_equiv (Equiv.neg G) (fun r => ⟨hneg r, fun h => by simpa using hneg _ h⟩)
    (fun r _ => ?_)
  rw [Matrix.conjTranspose_smul, hA, Equiv.neg_apply]
  congr 1
  rw [ofAdd_neg, map_inv, Circle.coe_inv_eq_conj]
  rfl

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
