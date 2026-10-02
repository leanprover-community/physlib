/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
/-!

# Lorentz co vectors

In this module we define Lorentz vectors as real Lorentz tensors with a single up index.
We create an API around Lorentz vectors to make working with them as easy as possible.

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open Complex
open TensorProduct

noncomputable section

namespace Lorentz

/-- Real covariant Lorentz vector. -/
@[implicit_reducible]
def CoVector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

/- As for `Vector`, `CoVector d` is applied directly as a function throughout the library;
  marking it implicit-reducible lets such applications typecheck at implicit transparency. -/

namespace CoVector

instance {d} : AddCommMonoid (CoVector d) :=
  inferInstanceAs (AddCommMonoid (Fin 1 ⊕ Fin d → ℝ))

instance {d} : Module ℝ (CoVector d) :=
  inferInstanceAs (Module ℝ (Fin 1 ⊕ Fin d → ℝ))

instance {d} : AddCommGroup (CoVector d) :=
  inferInstanceAs (AddCommGroup (Fin 1 ⊕ Fin d → ℝ))

instance {d} : FiniteDimensional ℝ (CoVector d) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 1 ⊕ Fin d → ℝ))

/-- The equivalence between `CoVector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    CoVector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  (WithLp.linearEquiv _ _ _).symm

@[ext]
lemma eq_of_apply_eq {d : ℕ} {v w : CoVector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  exact h i

instance (d : ℕ) : Norm (CoVector d) where
  norm := fun v => ‖equivEuclid d v‖

lemma norm_eq_equivEuclid (d : ℕ) (v : CoVector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (CoVector d) where
  dist_self x := by simp [norm_eq_equivEuclid]
  dist_comm x y := by
    simpa [norm_eq_equivEuclid, ← dist_eq_norm_neg_add] using
      dist_comm (equivEuclid d x) (equivEuclid d y)
  dist_triangle x y z := by
    simpa [norm_eq_equivEuclid, ← dist_eq_norm_neg_add] using dist_triangle
      ((equivEuclid d) x) ((equivEuclid d) y) ((equivEuclid d) z)
  eq_of_dist_eq_zero {x y} := by
    simp only [norm_eq_equivEuclid, map_add]
    intro h
    apply (equivEuclid d).injective
    simp at h
    rw [← neg_add_eq_zero, h]

instance isNormedSpace (d : ℕ) : NormedSpace ℝ (CoVector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)

open InnerProductSpace

instance (d : ℕ) : Inner ℝ (CoVector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ

lemma inner_eq_equivEuclid (d : ℕ) (v w : CoVector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl

/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (CoVector d) where
  norm_sq_eq_re_inner v := by
    simp only [inner_eq_equivEuclid, norm_eq_equivEuclid]
    exact InnerProductSpace.norm_sq_eq_re_inner (equivEuclid d v)
  conj_inner_symm x y := by
    simp only [inner_eq_equivEuclid]
    exact InnerProductSpace.conj_inner_symm (equivEuclid d x) (equivEuclid d y)
  add_left x y z := by
    simp only [inner_eq_equivEuclid, map_add]
    exact InnerProductSpace.add_left (equivEuclid d x) (equivEuclid d y) (equivEuclid d z)
  smul_left x y r := by
    simp only [inner_eq_equivEuclid, map_smul]
    exact InnerProductSpace.smul_left (equivEuclid d x) (equivEuclid d y) r

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (CoVector d) (CoVector d) := chartedSpaceSelf (CoVector d)

instance {d} : CoeFun (CoVector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl

@[simp]
lemma apply_add {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl

@[simp]
lemma apply_sub {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by rfl

@[simp]
lemma apply_sum {d : ℕ} {ι : Type} [Fintype ι] (f : ι → CoVector d) (i : Fin 1 ⊕ Fin d) :
    (∑ j, f j) i = ∑ j, f j i := Finset.sum_apply i Finset.univ f

@[simp]
lemma neg_apply {d : ℕ} (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : CoVector d) i = 0 := rfl

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (CoVector d) :=
  Pi.basisFun ℝ _

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  rw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

lemma basis_repr_apply {d : ℕ} (p : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  rw [Pi.basisFun_repr]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : CoVector d →ₗ[ℝ] CoVector d) (p : CoVector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

end CoVector

end Lorentz
