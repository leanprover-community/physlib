/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Basic.Complex.Basic
public import Physlib.Relativity.Tensors.Conjugation.Basic

/-!

# SUSY N=1 chiral sector: index, configuration, and conjugation data

The index data, field configuration and conjugation of the N=1 chiral sector, as a tensor species.

## i. Overview

The chiral scalars are indexed by a finite type `ι`, and a configuration is a point of `ι → ℂ`
(`ChiralScalarConfiguration`). The anti-chiral scalars are the complex conjugates of this
configuration, not independent field data. A tensor index carries one of four colours
(`ChiralColor`): holomorphic or anti-holomorphic, crossed with up or down. The four colours have
four carriers: `chiralUp` the vectors `ι → ℂ`, `chiralDown` their dual, and `antiUp` and
`antiDown` the conjugate modules of these two (`ConjModule`, in which `i` acts as `−i`).

The dual colour `τ` flips variance and keeps holomorphy, and two indices contract only when their
colours are `τ`-related, so `g^{IJ̄} D_I W D̄_J̄ W̄` type-checks. The conjugate colour `bar` flips
holomorphy and keeps variance. Contraction is the δ pairing of coordinate vectors: the basis at
`τ c` is the dual basis of the basis at `c` (`chiralTensor.instHasContrDualBases`), so a
contraction is a sum over `ι`. Every colour carries the trivial representation of `Unit`.

`chiralTensor` packages this data as a `ConjTensorSpecies`. It gives the chiral sector the generic
tensor API, and the conjugation map `conjT` in which reality and Hermiticity are stated.

## ii. Key results

- `SUSY.N1.ChiralScalarConfiguration` : the configuration space `ι → ℂ`.
- `SUSY.N1.ChiralColor` : the four colours, with the dual involution `ChiralColor.tau`.
- `SUSY.N1.chiralTensor` : the chiral sector as a `ConjTensorSpecies`.
- `SUSY.N1.chiralTensor.instHasContrDualBases` : the chiral species has dual bases at dual
    colours, matched by the identity on `ι`.

## iii. Table of contents

- A. The chiral scalar configuration
- B. The chiral colours and the dual involution
- C. Carrier, representation, and basis
- D. The δ structure on based finite modules
- E. The chiral-index tensor species
- F. Conjugation

## iv. References

* None.
-/

@[expose] public section
open TensorProduct Module ComplexConjugate
noncomputable section

namespace SUSY.N1

/-!
## A. The chiral scalar configuration

-/

/-- The chiral scalar configuration: a complex value for each chiral label, the sector's only field
data. An `abbrev`, so Mathlib's function-space lemmas apply to it directly. -/
abbrev ChiralScalarConfiguration (ChiralIndexingType : Type*) := ChiralIndexingType → ℂ

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-!
## B. The chiral colours and the dual involution

-/

/-- The four colours of a chiral-sector index: holomorphy (`chiral` or `anti`) crossed with
variance (`up` or `down`). -/
inductive ChiralColor | chiralUp | chiralDown | antiUp | antiDown
deriving DecidableEq

namespace ChiralColor

/-- The dual colour: flips variance and keeps holomorphy. Two indices contract exactly when their
colours are `τ`-related. -/
def tau : ChiralColor → ChiralColor
  | chiralUp => chiralDown
  | chiralDown => chiralUp
  | antiUp => antiDown
  | antiDown => antiUp

/-- The conjugate colour: flips holomorphy and keeps variance. It commutes with `tau`
(`bar_tau`). -/
def bar : ChiralColor → ChiralColor
  | chiralUp => antiUp
  | antiUp => chiralUp
  | chiralDown => antiDown
  | antiDown => chiralDown

@[simp] lemma bar_bar (c : ChiralColor) : bar (bar c) = c := by cases c <;> rfl

@[simp] lemma bar_tau (c : ChiralColor) : bar (tau c) = tau (bar c) := by cases c <;> rfl

end ChiralColor

variable {ι}

/-!
## C. Carrier, representation, and basis

`chiralUp` and `chiralDown` carry `ι → ℂ` and its dual; `antiUp` and `antiDown` carry their
conjugate modules. The representation is trivial over `Unit`, and every basis is indexed by `ι`.

-/

/-- The carrier of each colour: `ι → ℂ` and its dual on the holomorphic side, and their conjugate
modules (`ConjModule`, where `i` acts as `−i`) on the anti-holomorphic side. -/
abbrev chiralModule : ChiralColor → Type
  | .chiralUp   => ι → ℂ
  | .chiralDown => Module.Dual ℂ (ι → ℂ)
  | .antiUp     => ConjModule (ι → ℂ)
  | .antiDown   => ConjModule (Module.Dual ℂ (ι → ℂ))

instance instAddCommGroupChiralModule : ∀ c, AddCommGroup (chiralModule (ι := ι) c)
  | .chiralUp | .chiralDown | .antiUp | .antiDown => inferInstance

noncomputable instance instModuleChiralModule : ∀ c, Module ℂ (chiralModule (ι := ι) c)
  | .chiralUp | .chiralDown | .antiUp | .antiDown => inferInstance

/-- The representation of each colour: trivial, over the trivial group `Unit`. -/
def chiralRep : (c : ChiralColor) → Representation ℂ Unit (chiralModule (ι := ι) c) :=
  fun _ => Representation.trivial ℂ Unit _

/-- The standard basis of `ι → ℂ`. -/
def piBasis : Basis ι ℂ (ι → ℂ) := Pi.basisFun ℂ ι

/-- The basis of each colour's carrier, indexed by `ι`: `piBasis`, its dual basis, and the
conjugate of each. -/
noncomputable def chiralBasis : (c : ChiralColor) → Basis ι ℂ (chiralModule (ι := ι) c)
  | .chiralUp   => piBasis
  | .chiralDown => piBasis.dualBasis
  | .antiUp     => Basis.conj piBasis
  | .antiDown   => Basis.conj piBasis.dualBasis

/-!
## D. The δ structure on based finite modules

The contraction and unit of the species are the δ structure in basis coordinates. A contraction
pairs two based modules `(M, b)` and `(N, b')` sharing the index `ι`:
`(x, y) ↦ ∑_I (b x)_I (b' y)_I` (`deltaContr₂`), with cap `∑_I b_I ⊗ b'_I` (`deltaCap₂`). The
species has no `WithMetric` instance: the metric of the chiral sector is the Kähler metric
`g_{IJ̄}`, built downstream.

-/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- The δ pairing `(x, y) ↦ ∑_I (b x)_I (b' y)_I` of two based modules sharing the index `ι`,
built from Mathlib's `Basis.toDual`. -/
def deltaBil₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M →ₗ[ℂ] N →ₗ[ℂ] ℂ :=
  b.toDual.compl₂ (b'.equiv b (Equiv.refl ι)).toLinearMap

/-- `deltaBil₂ b b' x y = ∑_I (b x)_I (b' y)_I`. -/
lemma deltaBil₂_apply (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (y : N) :
    deltaBil₂ b b' x y = ∑ I, b.equivFun x I * b'.equivFun y I := by
  rw [deltaBil₂, LinearMap.compl₂_apply, LinearEquiv.coe_coe]
  conv_lhs => rw [← b'.sum_equivFun y]
  simp_rw [map_sum, map_smul, Basis.equiv_apply, Equiv.refl_apply, Basis.toDual_eq_equivFun,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

/-- The two-module δ contraction `M ⊗ N → ℂ`. -/
def deltaContr₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M ⊗[ℂ] N →ₗ[ℂ] ℂ :=
  TensorProduct.lift (deltaBil₂ b b')

/-- `deltaContr₂ b b' (x ⊗ₜ y) = ∑_I (b x)_I (b' y)_I`. -/
lemma deltaContr₂_tmul (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (y : N) :
    deltaContr₂ b b' (x ⊗ₜ[ℂ] y) = ∑ I, b.equivFun x I * b'.equivFun y I := by
  rw [deltaContr₂, TensorProduct.lift.tmul, deltaBil₂_apply]

/-- `deltaContr₂ b b' (x ⊗ₜ b' J) = x_J`: pairing with the second basis reads off a coordinate. -/
lemma deltaContr₂_tmul_basis (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (J : ι) :
    deltaContr₂ b b' (x ⊗ₜ[ℂ] b' J) = b.equivFun x J := by
  simp [deltaContr₂_tmul, Basis.equivFun_self]

/-- `deltaContr₂ b b' (b I ⊗ₜ b' J) = δ_{IJ}`: the two bases are δ-dual. -/
lemma deltaContr₂_basis_basis (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (I J : ι) :
    deltaContr₂ b b' (b I ⊗ₜ[ℂ] b' J) = if I = J then 1 else 0 := by
  rw [deltaContr₂_tmul_basis, Basis.equivFun_self]

/-- `deltaContr₂ b b' (x ⊗ₜ y) = deltaContr₂ b' b (y ⊗ₜ x)`: swapping slots swaps the two bases. -/
lemma deltaContr₂_comm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) (y : N) :
    deltaContr₂ b b' (x ⊗ₜ[ℂ] y) = deltaContr₂ b' b (y ⊗ₜ[ℂ] x) := by
  rw [deltaContr₂_tmul, deltaContr₂_tmul]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

/-- The two-module δ cap `∑_I b_I ⊗ b'_I ∈ M ⊗ N`. -/
def deltaCap₂ (b : Basis ι ℂ M) (b' : Basis ι ℂ N) : M ⊗[ℂ] N := ∑ I, b I ⊗ₜ[ℂ] b' I

omit [DecidableEq ι] in
/-- `comm (deltaCap₂ b b') = deltaCap₂ b' b`: swapping the two factors swaps the two bases. -/
lemma deltaCap₂_comm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    TensorProduct.comm ℂ M N (deltaCap₂ b b') = deltaCap₂ b' b := by
  rw [deltaCap₂, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [TensorProduct.comm_tmul]

omit [DecidableEq ι] in
/-- The `unit_symm` law (two-module, `toSpanSingleton` form): `deltaCap₂ b' b` is the swap of
`deltaCap₂ b b'`. -/
lemma deltaUnit₂_symm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1 =
      LinearMap.lTensor N (LinearEquiv.refl ℂ M).toLinearMap
        (TensorProduct.comm ℂ M N (LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b b') 1)) := by
  simp only [LinearMap.toSpanSingleton_apply_one]
  rw [deltaCap₂_comm]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.lTensor_id, LinearMap.id_coe, id_eq]

/-- The snake identity (two-module, `contr_unit` law): contracting `x ∈ M` into the `M`-leg of
`deltaCap₂ b' b ∈ N ⊗ M` returns `x`. -/
lemma deltaContr₂_unit (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) :
    (TensorProduct.lid ℂ M) ((deltaContr₂ b b').rTensor M
      ((TensorProduct.assoc ℂ M N M).symm
        (x ⊗ₜ[ℂ] LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1))) = x := by
  rw [LinearMap.toSpanSingleton_apply_one, deltaCap₂, TensorProduct.tmul_sum, map_sum, map_sum,
    map_sum]
  conv_rhs => rw [← b.sum_equivFun x]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    deltaContr₂_tmul_basis]

/-!
## E. The chiral-index tensor species

-/

/-- The chiral-index tensor species with its conjugation. Its contraction is the δ pairing of a
colour with its dual `τ c`, its unit the δ cap, and its conjugation flips holomorphy by
`ChiralColor.bar`. -/
def chiralTensor : ConjTensorSpecies ℂ ChiralColor Unit (chiralModule (ι := ι)) (fun _ => ι)
    (chiralRep (ι := ι)) (chiralBasis (ι := ι)) where
  τ := ChiralColor.tau
  τ_involution c := by cases c <;> rfl
  -- `contr` pairs a colour with its variance dual `τ c` (distinct carriers, e.g. `ι → ℂ`
  -- against its dual); `unit` is the δ cap across those two carriers.
  contr c := { deltaContr₂ (chiralBasis c) (chiralBasis (ChiralColor.tau c)) with
      isIntertwining' g := by ext v; simp [Representation.tprod_apply, chiralRep] }
  unit c := { LinearMap.toSpanSingleton ℂ _
        (deltaCap₂ (chiralBasis (ChiralColor.tau c)) (chiralBasis c)) with
      isIntertwining' g := by ext; simp [Representation.tprod_apply, chiralRep, deltaCap₂] }
  -- Each coherence law reduces, by case analysis on `c`, to the matching abstract two-module
  -- δ lemma.
  contr_tmul_symm c x y := by cases c <;> exact deltaContr₂_comm _ _ _ _
  unit_symm c := by cases c <;> exact deltaUnit₂_symm _ _
  contr_unit c x := by cases c <;> exact deltaContr₂_unit _ _ x
  conj_basis_equivariant := by simp [chiralRep, Finsupp.single_apply]
  -- Conjugation data: `bar` flips holomorphy, the index set is shared (`rfl`), `star δ = δ`.
  bar := ChiralColor.bar
  bar_involution := ChiralColor.bar_bar
  bar_tau := ChiralColor.bar_tau
  barIdx_eq _ := rfl
  conj_contrComm := by
    intro d x₁ x₂
    -- The contraction at every colour is the real δ pairing of two `ι`-bases, so `star` fixes it.
    -- The `key` lemma evaluates both sides by `deltaContr₂_basis_basis` (a syntactic rewrite to
    -- `if x₁ = x₂ then 1 else 0`), so the heavy `Basis.conj`/`dualBasis` carriers are never
    -- `whnf`'d.
    have key : ∀ {M₁ M₁' M₂ M₂' : Type} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₁']
        [Module ℂ M₁'] [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₂'] [Module ℂ M₂']
        (B₁ : Basis ι ℂ M₁) (B₁' : Basis ι ℂ M₁') (B₂ : Basis ι ℂ M₂) (B₂' : Basis ι ℂ M₂'),
        star (deltaContr₂ B₁ B₁' (B₁ x₁ ⊗ₜ[ℂ] B₁' x₂))
          = deltaContr₂ B₂ B₂' (B₂ x₁ ⊗ₜ[ℂ] B₂' x₂) := by
      intro M₁ M₁' M₂ M₂' _ _ _ _ _ _ _ _ B₁ B₁' B₂ B₂'
      rw [deltaContr₂_basis_basis, deltaContr₂_basis_basis]; split <;> simp
    cases d <;> exact key _ _ _ _

/-- The chiral contraction of two basis vectors is the Kronecker δ. -/
lemma chiralTensor_contr_chiralBasis (d : ChiralColor) (x₁ x₂ : ι) :
    (chiralTensor (ι := ι)).contr d
        (chiralBasis (ι := ι) d x₁ ⊗ₜ[ℂ] chiralBasis (ι := ι) ((chiralTensor (ι := ι)).τ d) x₂)
      = if x₁ = x₂ then 1 else 0 := by
  cases d <;> exact deltaContr₂_basis_basis _ _ x₁ x₂

/-- The chiral species has dual bases at dual colours, matched by the identity on `ι`. -/
instance chiralTensor.instHasContrDualBases :
    TensorSpecies.HasContrDualBases (chiralTensor (ι := ι)).toTensorSpecies where
  exists_matching c := ⟨Equiv.refl ι, chiralTensor_contr_chiralBasis c⟩

/-- The dual-label matching of the chiral species is the identity. -/
@[simp]
lemma contrDualIdxEquiv_eq_refl (c : ChiralColor) :
    TensorSpecies.HasContrDualBases.contrDualIdxEquiv (chiralTensor (ι := ι)).toTensorSpecies c =
      Equiv.refl ι :=
  TensorSpecies.HasContrDualBases.contrDualIdxEquiv_eq_of_isContrDualMatching
    (chiralTensor_contr_chiralBasis c)

/-!
## F. Conjugation

Conjugation is part of `chiralTensor` (§E), and the framework supplies the map `conjT` and its
laws (`conjT_conjT`, `conjT_contrT`, `conjT_eq_permT_iff`). This section normalizes `conjT` for
the two shapes the sector conjugates, the scalar `W` and the holomorphic covector `D_I W`, and
checks on components that it is complex conjugation.

-/

section Conjugation

open TensorSpecies TensorSpecies.Tensor ConjTensorSpecies ChiralColor

/-!
The following normalize the output of `(chiralTensor (ι := ι)).conjT` back to the
canonical colour lists for scalar and anti-holomorphic covector tensors respectively.

-/

/-- Conjugation of a scalar tensor, normalized back to the scalar colour list `![]`. -/
def conjScalar (t : (chiralTensor (ι := ι)).Tensor ![]) :
    (chiralTensor (ι := ι)).Tensor ![] :=
  permT id ⟨Function.bijective_id, fun i => by fin_cases i⟩
    ((chiralTensor (ι := ι)).conjT t)

/-- Conjugation of a holomorphic covector, normalized to the anti-holomorphic covector colour
list `![antiDown]`. -/
def conjChiralCovector
    (t : (chiralTensor (ι := ι)).Tensor ![chiralDown]) :
    (chiralTensor (ι := ι)).Tensor ![antiDown] :=
  permT ![0] ⟨by decide, fun i => by fin_cases i; rfl⟩
    ((chiralTensor (ι := ι)).conjT t)

set_option backward.isDefEq.respectTransparency false in
/-- For scalar tensors, `toScalar` of the normalized tensor conjugate is the complex conjugate of
`toScalar`. -/
lemma toScalar_conjScalar (t : (chiralTensor (ι := ι)).Tensor ![]) :
    (conjScalar t).toScalar = star t.toScalar := by
  rw [conjScalar, toScalar_permT]
  rw [toScalar_eq_repr, toScalar_eq_repr]
  change componentMap (S := (chiralTensor (ι := ι)).toTensorSpecies)
      ((chiralTensor (ι := ι)).bar ∘ ![]) ((chiralTensor (ι := ι)).conjT t) (fun j => Fin.elim0 j) =
    star ((basis (S := (chiralTensor (ι := ι)).toTensorSpecies) ![]).repr t (fun j => Fin.elim0 j))
  erw [ConjTensorSpecies.componentMap_conjT (S := chiralTensor (ι := ι))]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Component formula for the holomorphic covector conjugate: the `![I]` basis component of
`conjChiralCovector t` is the complex conjugate of the `![I]` component of `t`. -/
lemma repr_conjChiralCovector
    (t : (chiralTensor (ι := ι)).Tensor ![chiralDown]) (I : ι) :
    (basis (S := (chiralTensor (ι := ι)).toTensorSpecies) ![antiDown]).repr
        (conjChiralCovector t) ![I] =
      star ((basis (S := (chiralTensor (ι := ι)).toTensorSpecies) ![chiralDown]).repr t ![I]) := by
  rw [conjChiralCovector, permT_basis_repr_symm_apply]
  change componentMap (S := (chiralTensor (ι := ι)).toTensorSpecies)
      ((chiralTensor (ι := ι)).bar ∘ ![chiralDown]) ((chiralTensor (ι := ι)).conjT t) _ = _
  erw [ConjTensorSpecies.componentMap_conjT (S := chiralTensor (ι := ι))]
  apply congrArg star
  apply congrArg (fun idx => componentMap (S := (chiralTensor (ι := ι)).toTensorSpecies)
    ![chiralDown] t idx)
  funext i
  fin_cases i
  rfl

/-- Conjugation of a holomorphic covector is additive. -/
@[simp]
lemma conjChiralCovector_add
    (t₁ t₂ : (chiralTensor (ι := ι)).Tensor ![chiralDown]) :
    conjChiralCovector (t₁ + t₂) = conjChiralCovector t₁ + conjChiralCovector t₂ := by
  simp [conjChiralCovector, map_add]

/-- Conjugation of a holomorphic covector is conjugate-linear: a scalar `r` pulls out as
`star r`. -/
@[simp]
lemma conjChiralCovector_smul (r : ℂ)
    (t : (chiralTensor (ι := ι)).Tensor ![chiralDown]) :
    conjChiralCovector (r • t) = star r • conjChiralCovector t := by
  simp [conjChiralCovector]

end Conjugation

end SUSY.N1

end

end
