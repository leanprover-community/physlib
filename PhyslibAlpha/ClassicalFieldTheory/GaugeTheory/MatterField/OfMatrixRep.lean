/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.DerivRep
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.GaugeJetAction
public import PhyslibAlpha.Mathematics.ForMathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.CStarAlgebra.Matrix
/-!
# Matter fields from matrix representations of a global gauge group

Continuous representations of a global gauge group by complex matrices, and the matter fields
they define.

## i. Overview

A model-building table says how a field transforms by writing down a matrix. The field has an
internal index `ι`, and a gauge transformation acts on it by an invertible `ι × ι` complex
matrix. Such a matrix representation of the global gauge group `G` is a continuous
homomorphism `G.group →ₜ* (Matrix ι ι ℂ)ˣ`. Its derivative `GlobalGaugeGroup.derivMat ρ c` is
the matrix by which an element `c` of the Lie algebra acts. It is the matrix version of
`GlobalGaugeGroup.derivRep`, and is characterised by the exponential law
`ρ (exp (t c)) = exp (t derivMat ρ c)`.

The representations named in a table are assembled from a few pieces. These are the trivial
representation, the Kronecker product `MatrixRep.kron` and the twist `MatrixRep.charge` by a
power of a character of the gauge group. The derivative of each is computed from the
exponential law.

A matrix representation `ρ` on `ι` gives a matter field on any target space
`V ≃ S ⊗ (ι → ℂ)`, where `S` carries a representation of the Lorentz group. The gauge group
acts by `ρ` on the internal index and the Lorentz group on `S`. This is
`MatterField.ofMatrixRep`. Its action of the Lie algebra is the derivative of `ρ`, and its jet
action is then fixed by the derivative.

## ii. Key results

- `GlobalGaugeGroup.derivMat` : the derivative of a matrix representation, a matrix for each
  element of the Lie algebra.
- `GlobalGaugeGroup.apply_eq_exp_derivMat`, `GlobalGaugeGroup.derivMat_eq_of` : the exponential
  law, and the uniqueness of the derivative.
- `GlobalGaugeGroup.MatrixRep.trivial`, `GlobalGaugeGroup.MatrixRep.kron`,
  `GlobalGaugeGroup.MatrixRep.charge` : the trivial representation, the Kronecker product and
  the charge twist.
- `GlobalGaugeGroup.MatrixRep.derivMat_trivial`, `GlobalGaugeGroup.MatrixRep.derivMat_kron`,
  `GlobalGaugeGroup.MatrixRep.derivMat_charge` : their derivatives.
- `GlobalGaugeGroup.MatrixRep.valEnd` : the endomorphism of `V ≃ S ⊗ (ι → ℂ)` defined by a
  matrix on the internal index.
- `GlobalGaugeGroup.MatrixRep.repLorentz` : the Lorentz action on `V ≃ S ⊗ (ι → ℂ)`, which
  commutes with every `valEnd`.
- `GlobalGaugeGroup.MatterField.ofMatrixRep` : the matter field of a matrix
  representation.
- `GlobalGaugeGroup.MatterField.ofMatrixRep_repAlgebra` : its action of the Lie algebra
  is the derivative of the matrix representation.

## iii. Table of contents

- A. The derivative of a matrix representation
- B. The standard constructions
- C. Endomorphisms from matrices
- D. The matter field of a matrix representation

## iv. References

* None.

-/

@[expose] public section

open TensorProduct MatrixGroups Matrix NormedSpace Kronecker

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-!

## A. The derivative of a matrix representation

A continuous representation of `G` by invertible matrices is differentiated by viewing the
matrices as continuous linear maps of Euclidean space, where `GlobalGaugeGroup.derivRep`
applies.

-/

section Derivative

variable {G : GlobalGaugeGroup κ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The continuous homomorphism of unit groups induced by a continuous monoid homomorphism. -/
noncomputable def unitsMapHom {M N : Type} [Monoid M] [Monoid N] [TopologicalSpace M]
    [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f, Continuous.units_map f hf⟩

/-- The algebra map from complex matrices to the continuous linear endomorphisms of Euclidean
  space, a matrix acting on vectors. -/
noncomputable def matrixCLM :
    Matrix ι ι ℂ →ₐ[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  AlgHom.ofClass (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))

lemma matrixCLM_injective : Function.Injective (matrixCLM (ι := ι)) :=
  EquivLike.injective (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))

lemma matrixCLM_surjective : Function.Surjective (matrixCLM (ι := ι)) :=
  EquivLike.surjective (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))

lemma continuous_matrixCLM : Continuous (matrixCLM (ι := ι)) :=
  (matrixCLM (ι := ι)).toLinearMap.continuous_of_finiteDimensional

set_option backward.isDefEq.respectTransparency false in
/-- The map `matrixCLM` commutes with the exponential of a real multiple of a matrix. -/
lemma matrixCLM_exp_smul (t : ℝ) (A : Matrix ι ι ℂ) :
    matrixCLM (exp (t • A)) = exp (t • matrixCLM A) := by
  let _ : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    .restrictScalars ℚ ℝ _
  open scoped Norms.Operator in
  rw [map_exp (matrixCLM (ι := ι)) continuous_matrixCLM, ← Complex.coe_smul, map_smul]
  congr 1

/-- A matrix representation of the global gauge group `G`, as a representation on Euclidean
  space. -/
noncomputable def clmRep (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ) :
    G.group →ₜ* (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)ˣ :=
  (unitsMapHom (matrixCLM (ι := ι) : Matrix ι ι ℂ →* _) continuous_matrixCLM).comp ρ

variable (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ)

/-- The derivative of a continuous matrix representation `ρ` of the global gauge group. It is the
  matrix by which an element `c` of the Lie algebra acts, with
  `ρ (exp (t c)) = exp (t derivMat ρ c)`. -/
noncomputable def derivMat (c : G.lieSubalgebra) : Matrix ι ι ℂ :=
  Classical.choose (matrixCLM_surjective (derivRep (clmRep ρ) c))

lemma matrixCLM_derivMat (c : G.lieSubalgebra) :
    matrixCLM (derivMat ρ c) = derivRep (clmRep ρ) c :=
  Classical.choose_spec (matrixCLM_surjective (derivRep (clmRep ρ) c))

/-- The matrix representation maps the one-parameter subgroup of a generator `c` to the
  exponential of its derivative, `ρ (exp (t c)) = exp (t derivMat ρ c)`. -/
lemma apply_eq_exp_derivMat {c : G.lieSubalgebra} {t : ℝ} {g : G.group}
    (hg : ((g : GL κ ℂ) : Matrix κ κ ℂ) = exp (t • (c : Matrix κ κ ℂ))) :
    ((ρ g : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) = exp (t • derivMat ρ c) := by
  refine matrixCLM_injective ?_
  rw [matrixCLM_exp_smul, matrixCLM_derivMat]
  exact apply_eq_exp_derivRep (clmRep ρ) hg

/-- The derivative of a matrix representation at `c` is the unique matrix `Z` with
  `ρ (exp (t c)) = exp (t Z)` for all `t`. -/
lemma derivMat_eq_of {c : G.lieSubalgebra} {Z : Matrix ι ι ℂ}
    (hZ : ∀ (t : ℝ) (g : G.group),
      ((g : GL κ ℂ) : Matrix κ κ ℂ) = exp (t • (c : Matrix κ κ ℂ)) →
        ((ρ g : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) = exp (t • Z)) :
    derivMat ρ c = Z := by
  refine matrixCLM_injective ?_
  rw [matrixCLM_derivMat]
  refine derivRep_eq_of _ fun t g hg => ?_
  rw [← matrixCLM_exp_smul]
  exact congrArg matrixCLM (hZ t g hg)

end Derivative

namespace MatrixRep

variable {G : GlobalGaugeGroup κ} {ι ι₁ ι₂ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

/-!

## B. The standard constructions

A character of the gauge group, such as the hypercharge phase, twists a representation by an
integer power. The derivative of a character `χ` at `c` is a number `z` with
`χ (exp (t c)) = exp (t z)`.

-/

/-- The trivial representation on one internal index. Every gauge transformation acts as the
  identity. -/
noncomputable def trivial : G.group →ₜ* (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  ⟨1, continuous_const⟩

/-- The derivative of the trivial representation is zero. -/
lemma derivMat_trivial (c : G.lieSubalgebra) : derivMat (trivial (G := G)) c = 0 :=
  derivMat_eq_of _ fun t _ _ => by
    show (1 : Matrix (Fin 1) (Fin 1) ℂ) = exp (t • (0 : Matrix (Fin 1) (Fin 1) ℂ))
    rw [smul_zero, exp_zero]

/-- The Kronecker product of matrices, as a monoid homomorphism on pairs. -/
def kroneckerMonoidHom :
    Matrix ι₁ ι₁ ℂ × Matrix ι₂ ι₂ ℂ →* Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ where
  toFun p := p.1 ⊗ₖ p.2
  map_one' := one_kronecker_one
  map_mul' p q := mul_kronecker_mul p.1 q.1 p.2 q.2

lemma continuous_kroneckerMonoidHom :
    Continuous (kroneckerMonoidHom (ι₁ := ι₁) (ι₂ := ι₂)) :=
  continuous_pi fun i => continuous_pi fun j => by
    change Continuous fun a : Matrix ι₁ ι₁ ℂ × Matrix ι₂ ι₂ ℂ => a.1 i.1 j.1 * a.2 i.2 j.2
    fun_prop

/-- The Kronecker product of two matrix representations, acting on the product of their
  internal indices. -/
noncomputable def kron (ρ₁ : G.group →ₜ* (Matrix ι₁ ι₁ ℂ)ˣ) (ρ₂ : G.group →ₜ* (Matrix ι₂ ι₂ ℂ)ˣ) :
    G.group →ₜ* (Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ)ˣ :=
  ⟨(Units.map kroneckerMonoidHom).comp
    ((MulEquiv.prodUnits (M := Matrix ι₁ ι₁ ℂ) (N := Matrix ι₂ ι₂ ℂ)).symm.toMonoidHom.comp
      (ρ₁.prod ρ₂).toMonoidHom),
    by
    change Continuous (Units.map kroneckerMonoidHom ∘
      (MulEquiv.prodUnits (M := Matrix ι₁ ι₁ ℂ) (N := Matrix ι₂ ι₂ ℂ)).symm ∘ (ρ₁.prod ρ₂))
    exact (Continuous.units_map kroneckerMonoidHom continuous_kroneckerMonoidHom).comp
      ((Homeomorph.prodUnits (α := Matrix ι₁ ι₁ ℂ) (β := Matrix ι₂ ι₂ ℂ)).symm.continuous.comp
        (ρ₁.prod ρ₂).continuous)⟩

/-- A gauge transformation acts on the Kronecker product by the Kronecker product of its two
  actions. -/
lemma kron_val (ρ₁ : G.group →ₜ* (Matrix ι₁ ι₁ ℂ)ˣ) (ρ₂ : G.group →ₜ* (Matrix ι₂ ι₂ ℂ)ˣ)
    (g : G.group) :
    ((kron ρ₁ ρ₂ g : (Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ)ˣ) : Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ) =
      (ρ₁ g : Matrix ι₁ ι₁ ℂ) ⊗ₖ (ρ₂ g : Matrix ι₂ ι₂ ℂ) := rfl

/-- The derivative of the Kronecker product of two representations is the Kronecker sum of
  their derivatives. -/
lemma derivMat_kron (ρ₁ : G.group →ₜ* (Matrix ι₁ ι₁ ℂ)ˣ) (ρ₂ : G.group →ₜ* (Matrix ι₂ ι₂ ℂ)ˣ)
    (c : G.lieSubalgebra) :
    derivMat (kron ρ₁ ρ₂) c =
      derivMat ρ₁ c ⊗ₖ (1 : Matrix ι₂ ι₂ ℂ) + (1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ derivMat ρ₂ c := by
  refine derivMat_eq_of _ fun t g hg => ?_
  rw [kron_val, apply_eq_exp_derivMat ρ₁ hg, apply_eq_exp_derivMat ρ₂ hg, smul_add,
    ← smul_kronecker, ← kronecker_smul, exp_kronecker_one_add_one_kronecker]

/-- The scalar matrices, as a homomorphism of unit groups from the nonzero complex numbers. -/
noncomputable def scalarUnits (ι : Type) [Fintype ι] [DecidableEq ι] :
    ℂˣ →* (Matrix ι ι ℂ)ˣ :=
  Units.map (algebraMap ℂ (Matrix ι ι ℂ)).toMonoidHom

lemma continuous_scalarUnits (ι : Type) [Fintype ι] [DecidableEq ι] :
    Continuous (scalarUnits ι) :=
  Continuous.units_map _ (Algebra.linearMap ℂ (Matrix ι ι ℂ)).continuous_of_finiteDimensional

/-- Scalar matrices commute with every invertible matrix. -/
lemma mul_scalarUnits_comm (U : (Matrix ι ι ℂ)ˣ) (z : ℂˣ) :
    U * scalarUnits ι z = scalarUnits ι z * U :=
  Units.ext (Algebra.commutes (z : ℂ) (U : Matrix ι ι ℂ)).symm

/-- The twist of a matrix representation `ρ` by the `n`-th power of a character `χ`. A gauge
  transformation `g` acts by `χ(g)ⁿ ρ(g)`. This is how a field of charge `n` under a `U(1)`
  factor is built from its neutral part. -/
noncomputable def charge (n : ℤ) (χ : G.group →ₜ* ℂˣ) (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ) :
    G.group →ₜ* (Matrix ι ι ℂ)ˣ where
  toMonoidHom :=
    { toFun g := scalarUnits ι (χ g ^ n) * ρ g
      map_one' := by simp
      map_mul' g h := by
        show scalarUnits ι (χ (g * h) ^ n) * ρ (g * h) =
          (scalarUnits ι (χ g ^ n) * ρ g) * (scalarUnits ι (χ h ^ n) * ρ h)
        rw [map_mul χ g h, mul_zpow, map_mul (scalarUnits ι), map_mul ρ g h,
          ← Commute.mul_mul_mul_comm (mul_scalarUnits_comm _ _)] }
  continuous_toFun :=
    ((continuous_scalarUnits ι).comp ((map_continuous χ).zpow n)).mul (map_continuous ρ)

/-- A gauge transformation acts on the charge twist by the scalar `χ(g)ⁿ` times its action
  on `ρ`. -/
lemma charge_val (n : ℤ) (χ : G.group →ₜ* ℂˣ) (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ) (g : G.group) :
    ((charge n χ ρ g : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) =
      ((χ g ^ n : ℂˣ) : ℂ) • (ρ g : Matrix ι ι ℂ) :=
  (Algebra.smul_def _ _).symm

/-- The derivative of the charge twist. If `z` is the derivative of the character `χ` at `c`,
  that is `χ (exp (t c)) = exp (t z)`, the derivative of the twist is `dρ + (n z) 1`. -/
lemma derivMat_charge (n : ℤ) (χ : G.group →ₜ* ℂˣ) (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ)
    {c : G.lieSubalgebra} {z : ℂ}
    (hχ : ∀ (t : ℝ) (g : G.group),
      ((g : GL κ ℂ) : Matrix κ κ ℂ) = exp (t • (c : Matrix κ κ ℂ)) →
        ((χ g : ℂˣ) : ℂ) = Complex.exp (t * z)) :
    derivMat (charge n χ ρ) c = derivMat ρ c + ((n : ℂ) * z) • (1 : Matrix ι ι ℂ) := by
  refine derivMat_eq_of _ fun t g hg => ?_
  rw [charge_val, Units.val_zpow_eq_zpow_val, hχ t g hg, apply_eq_exp_derivMat ρ hg,
    ← Complex.exp_int_mul, smul_add, ← smul_assoc, exp_add_smul_one, Complex.real_smul]
  congr 2
  ring

/-!

## C. Endomorphisms from matrices

The target space of a field is `V ≃ S ⊗ (ι → ℂ)`, where the gauge group acts on the internal
index `ι` and the Lorentz group on `S`. A matrix on `ι` then acts on `V` with `S` untouched.
On a normed target space it acts by a continuous linear map, and a matrix representation
becomes a continuous representation on `V`.

-/

section ValEnd

variable {S : Type} [AddCommGroup S] [Module ℂ S] {V : Type} [AddCommGroup V] [Module ℂ V]
  (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ))

/-- The endomorphism of the target space `V ≃ S ⊗ (ι → ℂ)` defined by a complex matrix on
  the internal index, as an algebra map. -/
noncomputable def valEndAlgHom : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ V :=
  (e.symm.conjAlgEquiv (R := ℂ)).toAlgHom.comp <|
    (Module.End.lTensorAlgHom ℂ (ι → ℂ) S).comp
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] Module.End ℂ (ι → ℂ)).toAlgHom

/-- The endomorphism of the target space `V ≃ S ⊗ (ι → ℂ)` defined by a complex matrix on
  the internal index, with the Lorentz factor untouched. -/
noncomputable def valEnd (B : Matrix ι ι ℂ) : V →ₗ[ℂ] V := valEndAlgHom e B

lemma valEnd_apply (B : Matrix ι ι ℂ) (d : V) :
    valEnd e B d = e.symm (LinearMap.lTensor S (Matrix.toLin' B) (e d)) := rfl

/-- A matrix on the internal index acts on a pure tensor through its action on the vector. -/
lemma valEnd_apply_symm_tmul (B : Matrix ι ι ℂ) (s : S) (v : ι → ℂ) :
    valEnd e B (e.symm (s ⊗ₜ[ℂ] v)) = e.symm (s ⊗ₜ[ℂ] (B.mulVec v)) := by
  rw [valEnd_apply, LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul, Matrix.toLin'_apply]

lemma valEnd_add (A B : Matrix ι ι ℂ) : valEnd e (A + B) = valEnd e A + valEnd e B :=
  map_add (valEndAlgHom e) A B

lemma valEnd_smul (z : ℂ) (A : Matrix ι ι ℂ) : valEnd e (z • A) = z • valEnd e A :=
  map_smul (valEndAlgHom e) z A

lemma valEnd_zero : valEnd e (0 : Matrix ι ι ℂ) = 0 := map_zero (valEndAlgHom e)

lemma valEnd_neg (A : Matrix ι ι ℂ) : valEnd e (-A) = -valEnd e A :=
  map_neg (valEndAlgHom e) A

lemma valEnd_multiset_sum (m : Multiset (Matrix ι ι ℂ)) :
    valEnd e m.sum = (m.map (valEnd e)).sum :=
  map_multiset_sum (valEndAlgHom e) m

lemma valEnd_mul (A B : Matrix ι ι ℂ) : valEnd e (A * B) = valEnd e A ∘ₗ valEnd e B :=
  map_mul (valEndAlgHom e) A B

lemma valEnd_one : valEnd e (1 : Matrix ι ι ℂ) = LinearMap.id := map_one (valEndAlgHom e)

/-- The Lorentz action on the target space `V ≃ S ⊗ (ι → ℂ)`, the given action on the Lorentz
  factor `S` transported through the identification. -/
noncomputable def repLorentz (ρ : Representation ℂ SL(2,ℂ) S) : Representation ℂ SL(2,ℂ) V :=
  (MonoidHom.ofClass (e.symm.conjAlgEquiv (R := ℂ))).comp
    (ρ.tprod (Representation.trivial ℂ SL(2,ℂ) (ι → ℂ)))

omit [Fintype ι] [DecidableEq ι] in
/-- The Lorentz action on a pure tensor acts on the Lorentz factor. -/
lemma repLorentz_apply_symm_tmul (ρ : Representation ℂ SL(2,ℂ) S) (Λ : SL(2,ℂ)) (s : S)
    (v : ι → ℂ) : repLorentz e ρ Λ (e.symm (s ⊗ₜ[ℂ] v)) = e.symm (ρ Λ s ⊗ₜ[ℂ] v) := by
  simp [repLorentz, Representation.tprod_apply]

/-- A matrix on the internal index commutes with the Lorentz action, since the two act on
  different tensor factors. This is how the gauge action of a field commutes with its Lorentz
  action. -/
lemma valEnd_comm_repLorentz (ρ : Representation ℂ SL(2,ℂ) S) (B : Matrix ι ι ℂ) (Λ : SL(2,ℂ))
    (v : V) : valEnd e B (repLorentz e ρ Λ v) = repLorentz e ρ Λ (valEnd e B v) := by
  obtain ⟨t, rfl⟩ : ∃ t, v = e.symm t := ⟨e v, (e.symm_apply_apply v).symm⟩
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add]
  | tmul s w =>
    rw [repLorentz_apply_symm_tmul, valEnd_apply_symm_tmul, valEnd_apply_symm_tmul,
      repLorentz_apply_symm_tmul]

end ValEnd

section ValEndCLM

variable {S : Type} [AddCommGroup S] [Module ℂ S]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ))

/-- A matrix on the internal index, as a continuous linear endomorphism of a normed target
  space `V ≃ S ⊗ (ι → ℂ)`. -/
noncomputable def valEndCLM : Matrix ι ι ℂ →ₐ[ℂ] (V →L[ℂ] V) :=
  (Module.End.toContinuousLinearMap V).toAlgHom.comp (valEndAlgHom e)

lemma continuous_valEndCLM : Continuous (valEndCLM e) :=
  (valEndCLM e).toLinearMap.continuous_of_finiteDimensional

/-- The continuous representation of the global gauge group on `V` by the matrices of a matrix
  representation on the internal index. -/
noncomputable def valEndRep (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ) : G.group →ₜ* (V →L[ℂ] V)ˣ :=
  (unitsMapHom (valEndCLM e : Matrix ι ι ℂ →* (V →L[ℂ] V)) (continuous_valEndCLM e)).comp ρ

end ValEndCLM

end MatrixRep

/-!

## D. The matter field of a matrix representation

A matrix representation `ρ` gives a matter field on any normed target space
`V ≃ S ⊗ (ι → ℂ)`, with the gauge group acting by `ρ` on the internal index and the Lorentz
group on `S`. Its action of the Lie algebra is the derivative of `ρ`.

-/

namespace MatterField

open MatrixRep

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Type} [AddCommGroup S] [Module ℂ S]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ)) {G : GlobalGaugeGroup κ}

/-- The matter field of a matrix representation `ρ`, on a target space `V ≃ S ⊗ (ι → ℂ)`.
  The global gauge group acts by `ρ` on the internal index and the Lorentz group through
  `repL` on `S`. The field has mass weight `w` and statistics `σ`. -/
noncomputable def ofMatrixRep (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ)
    (repL : Representation ℂ SL(2,ℂ) S) (w : ℕ) (σ : FieldStatistic) : G.MatterField where
  V := V
  rep := valEndRep e ρ
  repLorentz := MatrixRep.repLorentz e repL
  massWeight := w
  statistic := σ

variable (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ) (repL : Representation ℂ SL(2,ℂ) S) (w : ℕ)
  (σ : FieldStatistic)

set_option backward.isDefEq.respectTransparency false in
/-- The Lie algebra representation of the matter field of a matrix representation is the
  derivative of the matrix representation, acting on the internal index. -/
lemma lieAlgebraRep_ofMatrixRep (c : G.lieSubalgebra) :
    lieAlgebraRep (ofMatrixRep e ρ repL w σ) c = valEndCLM e (derivMat ρ c) := by
  let _ : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℝ _
  refine lieAlgebraRep_eq_of _ fun t g hg => ?_
  change valEndCLM e (ρ g : Matrix ι ι ℂ) = _
  open scoped Norms.Operator in
  rw [apply_eq_exp_derivMat ρ hg, map_exp (valEndCLM e) (continuous_valEndCLM e),
    ← Complex.coe_smul, ← Complex.coe_smul, map_smul]

/-- The action of the Lie algebra on the matter field of a matrix representation is the
  derivative of the representation, acting on the internal index. -/
lemma ofMatrixRep_repAlgebra (c : G.lieSubalgebra) :
    (ofMatrixRep e ρ repL w σ).repAlgebra c = valEnd e (derivMat ρ c) := by
  rw [repAlgebra_apply]
  exact congrArg ContinuousLinearMap.toLinearMap (lieAlgebraRep_ofMatrixRep e ρ repL w σ c)

end MatterField

end GlobalGaugeGroup
