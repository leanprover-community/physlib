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

## i. Overview

This file fixes the data that indexes the scalars of the N=1 chiral sector,
makes their contractions type-safe, and equips them with conjugation.

A single finite type `ι` indexes the chiral scalars (written `ChiralIndexingType`
in signatures) — the only index type. Variance (upper versus lower) and holomorphy
(a scalar versus its complex conjugate) are not separate index types but the two
axes of a four-element type `ChiralColor`, the product of `chiral`/`anti` with
`up`/`down`. Each axis is realized as a genuine carrier distinction, not a label:
variance as a module versus its dual (`ι → ℂ` versus `Module.Dual ℂ (ι → ℂ)`),
holomorphy as a module versus its complex conjugate (`ConjModule`, where `i` acts
as `−i`).

The dual-colour involution `τ` flips variance and preserves holomorphy. Two
indices may contract exactly when their colours are `τ`-related, so a holomorphic
index pairs only with a holomorphic index of the opposite variance, and a
conjugate ("barred") index only with a conjugate index of the opposite variance.
This is the discipline that makes the F-term contraction `g^{IJ̄} D_I W D̄_J̄ W̄`
type-check.

The physical field content is the configuration `ChiralScalarConfiguration ι =
ι → ℂ`, carrying `2 · Fintype.card ι` real degrees of freedom. The anti-chiral
scalars are the complex conjugates of this data, never an independent
configuration.

The index data is packaged as a `ConjTensorSpecies` over `ChiralColor`, each colour carrying its
distinct carrier from above. Complex conjugation is the conjugate-linear identity
`conjEquiv : M ≃ₛₗ[starRingEnd ℂ] ConjModule M` on each carrier (anti basis `Basis.conj`); the
species' holomorphy flip (`conjEquiv`, hence `conjT`) is built from it. Every
colour carries the trivial representation over the trivial group `Unit`, so the chiral scalars hold
no charge. Contracting a colour against its `τ`-dual is the dot product of the two coordinate
vectors, the Kronecker `δ_{IJ}` on basis labels: `contr` is that pairing `V c ⊗ V (τ c) → ℂ`, `unit`
its cap in `V (τ c) ⊗ V c`, and `metric` the cap `∑_I b_I ⊗ b_I` in `V c ⊗ V c`. This instance
equips the chiral sector with the framework's generic tensor API (`.Tensor`, `.contrT`, …).

Conjugation is intrinsic species data: a `ConjTensorSpecies` is a `TensorSpecies`
extended with the conjugate-colour involution `ChiralColor.bar` and its coherence. The framework
then supplies the map `conjT` (conjugate the components and flip each index's holomorphy by `bar`)
and its laws. `bar` is the holomorphy dual, distinct from and commuting with the
variance dual `τ`; it is not used in contraction.

Conjugation enters wherever reality does. It is what lets one state that the
Kähler metric is Hermitian (`conjT g` equals `g` with its two indices swapped),
that the anti-chiral sector is the complex conjugate of the chiral one
(`D̄_J̄ W̄ = conjT (D_I W)`), and hence that the F-term `g^{IJ̄} D_I W D̄_J̄ W̄`
is real. The species can express none of these alone.

## ii. Key results

- `SUSY.N1.ChiralScalarConfiguration` : the scalar configuration space `ι → ℂ`,
    where `ι` is the finite type indexing the chiral scalars. This is the only
    field data in the sector.
- `SUSY.N1.ChiralColor` : the four colours `chiral`/`anti` × `up`/`down`, with the
    dual-colour involution `ChiralColor.tau`.
- `SUSY.N1.chiralTensor` : the `ConjTensorSpecies` assembled from the above, whose
    `τ`-discipline makes the F-term contraction type-safe and whose `bar` carries the
    chiral-antichiral conjugation in which reality and Hermiticity conditions are phrased.

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

/-- The chiral scalar configuration: a complex value for each chiral label. This is
the sector's only field data. Declared as an `abbrev` so that unification sees
through it to `ChiralIndexingType → ℂ` and applies Mathlib's function-space calculus
lemmas directly. -/
abbrev ChiralScalarConfiguration (ChiralIndexingType : Type*) := ChiralIndexingType → ℂ

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-!
## B. The chiral colours and the dual involution

-/

/-- The four colours carried by a chiral-sector index: holomorphy (`chiral` versus
`anti`, a scalar versus its complex conjugate) crossed with variance (`up` versus
`down`, contravariant versus covariant). Carrying both axes here lets the single index
type `ι` label the scalars. -/
inductive ChiralColor | chiralUp | chiralDown | antiUp | antiDown
deriving DecidableEq

namespace ChiralColor

/-- The dual colour: flips variance and preserves holomorphy. Two indices may contract
exactly when their colours are `τ`-related, so `V^I` pairs only with `V_I` (same
holomorphy, opposite variance) and never with a conjugate index. -/
def tau : ChiralColor → ChiralColor
  | chiralUp => chiralDown
  | chiralDown => chiralUp
  | antiUp => antiDown
  | antiDown => antiUp

/-- The conjugate colour: flips holomorphy (`chiral`↔`anti`) and preserves variance. Complex
conjugation sends an index to its conjugate carrier, so `bar` swaps `chiral*` with `anti*`.
Distinct from the variance dual `tau`; the two commute (`bar_tau`). -/
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

A `TensorSpecies` takes, for each colour `c`, a carrier module, a group representation on it, and a
basis. The carrier depends on *both* axes: variance gives the vector/dual distinction (`ι → ℂ`
versus `Module.Dual ℂ (ι → ℂ)`) and holomorphy the conjugate-module distinction (`ConjModule …`,
where `i` acts as `−i`), so all four colours have distinct carriers. The representation is trivial
over the trivial group `Unit` (no charge) for every colour; each basis is indexed by `ι` —
`piBasis`, its dual `piBasis.dualBasis`, and the `Basis.conj` of each. Variance (`τ`) sends a
carrier to its dual; conjugation (`bar`) sends it to its conjugate module.

-/

/-- The carrier module of each colour, distinct for all four: the holomorphic vectors `ι → ℂ` and
their dual `Module.Dual ℂ (ι → ℂ)` on the chiral side, and the conjugate module `ConjModule …` of
each (where `i` acts as `−i`) on the anti side. Variance is the vector/dual axis, holomorphy the
conjugate-module axis; both are genuine carrier data, not labels tracked separately. -/
abbrev chiralModule : ChiralColor → Type
  | .chiralUp   => ι → ℂ
  | .chiralDown => Module.Dual ℂ (ι → ℂ)
  | .antiUp     => ConjModule (ι → ℂ)
  | .antiDown   => ConjModule (Module.Dual ℂ (ι → ℂ))

instance instAddCommGroupChiralModule : ∀ c, AddCommGroup (chiralModule (ι := ι) c)
  | .chiralUp | .chiralDown | .antiUp | .antiDown => inferInstance

noncomputable instance instModuleChiralModule : ∀ c, Module ℂ (chiralModule (ι := ι) c)
  | .chiralUp | .chiralDown | .antiUp | .antiDown => inferInstance

/-- The representation on each colour, taken trivial over the trivial group `Unit`: the chiral
scalars carry no charge in this sector. -/
def chiralRep : (c : ChiralColor) → Representation ℂ Unit (chiralModule (ι := ι) c) :=
  fun _ => Representation.trivial ℂ Unit _

/-- The standard basis of the vector carrier `ι → ℂ` (the indicator functions); the basis of
`chiralUp` and the reference basis for the δ pairing. -/
def piBasis : Basis ι ℂ (ι → ℂ) := Pi.basisFun ℂ ι

/-- The basis of each colour's carrier, all indexed by `ι`: `piBasis` on the holomorphic vectors,
its dual `piBasis.dualBasis` on the holomorphic covectors, and the `Basis.conj` of each on the
anti-holomorphic side (coordinates `star`-ed). -/
noncomputable def chiralBasis : (c : ChiralColor) → Basis ι ℂ (chiralModule (ι := ι) c)
  | .chiralUp   => piBasis
  | .chiralDown => piBasis.dualBasis
  | .antiUp     => Basis.conj piBasis
  | .antiDown   => Basis.conj piBasis.dualBasis

/-!
## D. The δ structure on based finite modules

The contraction, unit, and metric are one δ structure in basis coordinates. Here `metric` is the
`TensorSpecies` field of that name — the δ index-raising tensor `δ^{IJ}` — and is *not* the physical
Kähler metric `g_{IJ̄}`, which is built downstream on top of this sector. A contraction pairs a
colour with its variance dual `τ c`, whose carriers are *distinct* (a module and its dual, or their
conjugates) but share the index `ι`, so the pairing is the dot product *across two based modules*
`(M, b)` and `(N, b')`, `(x, y) ↦ ∑_I (b x)_I (b' y)_I`, with cap `∑_I b_I ⊗ b'_I ∈ M ⊗ N`. The
single-colour cap `deltaCap` (`b = b'`) is what `metric c` uses, since its two slots are the same
colour; the two-module pairing `deltaContr₂`/`deltaCap₂` is what `contr` and `unit` use. The δ data
stays within one holomorphy and needs no conjugation; conjugation is carried instead by the tensor
`conjT` (§F).

-/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The δ cap `∑_I b_I ⊗ b_I`: the rank-2 tensor in `M ⊗ M` with two upper indices, whose
components in the basis `b` are `δⁱʲ`. It is an element of `M ⊗ M` (the inverse-metric "cap"),
not a linear map, and serves as the `metric` field of the species (whose two slots share a
colour). -/
def deltaCap (b : Basis ι ℂ M) : M ⊗[ℂ] M := ∑ I, b I ⊗ₜ[ℂ] b I

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- The δ pairing between two based modules sharing the index `ι`: the dot product of coordinate
vectors `(x, y) ↦ ∑_I (b x)_I (b' y)_I`. Built from Mathlib's `Basis.toDual b` (the canonical δ map
`M → Module.Dual M`, sending `b` to its dual basis) precomposed on the second slot with the basis
transport `b' ≃ b`. -/
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

/-- The `contr_metric` law (two-module): contracting the inner `M`/`N` legs of
`deltaCap b ⊗ deltaCap b'` yields `deltaCap₂ b' b`. -/
lemma deltaContr₂_metric (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    (TensorProduct.comm ℂ M N ((TensorProduct.lid ℂ N).lTensor M
      (((deltaContr₂ b b').rTensor N).lTensor M
        (((TensorProduct.assoc ℂ M N N).symm.toLinearMap.lTensor M)
          ((TensorProduct.assoc ℂ M M (N ⊗[ℂ] N))
            (LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1 ⊗ₜ[ℂ]
              LinearMap.toSpanSingleton ℂ _ (deltaCap b') 1)))))) =
      LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1 := by
  rw [LinearMap.toSpanSingleton_apply_one, LinearMap.toSpanSingleton_apply_one,
    LinearMap.toSpanSingleton_apply_one]
  conv_lhs => rw [deltaCap, deltaCap, TensorProduct.sum_tmul]
  conv_rhs => rw [deltaCap₂]
  simp only [TensorProduct.tmul_sum, map_sum]
  simp [TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.comm_tmul, deltaContr₂_basis_basis, ite_smul]
  simp [TensorProduct.ite_tmul, Finset.sum_ite_eq]

/-!
## E. The chiral-index tensor species

-/

/-- The chiral-index tensor species, bundled with its conjugation. Its four colours
`chiral`/`anti` × `up`/`down` carry the four distinct carriers of §C. `contr c` is the two-module δ
pairing of a colour against its variance dual `τ c` (`V c ⊗ V (τ c) → ℂ`); `unit c` is the δ cap
across those two carriers; `metric c` is the single-colour δ cap `∑_I b_I ⊗ b_I`. Each
`TensorSpecies` coherence law reduces, by case analysis on the colour, to the corresponding abstract
two-module δ lemma of §D. The conjugation flips holomorphy (`ChiralColor.bar`) while preserving
variance; every basis is indexed by `ι`, so `barIdx_eq` is `rfl`, and `conj_contrComm` is
`star δ = δ`. Instantiating `ConjTensorSpecies` this way gives the chiral sector both
the framework's generic tensor API and its conjugation API (`conjT` and its laws) on one object. -/
def chiralTensor : ConjTensorSpecies ℂ ChiralColor Unit (chiralModule (ι := ι)) (fun _ => ι)
    (chiralRep (ι := ι)) (chiralBasis (ι := ι)) where
  τ := ChiralColor.tau
  τ_involution c := by cases c <;> rfl
  -- `contr` pairs a colour with its variance dual `τ c` (distinct carriers, e.g. `ι → ℂ`
  -- against its dual); `unit` is the δ cap across those two carriers; `metric` the δ cap of a
  -- colour with itself.
  contr c := { deltaContr₂ (chiralBasis c) (chiralBasis (ChiralColor.tau c)) with
      isIntertwining' g := by ext v; simp [Representation.tprod_apply, chiralRep] }
  unit c := { LinearMap.toSpanSingleton ℂ _
        (deltaCap₂ (chiralBasis (ChiralColor.tau c)) (chiralBasis c)) with
      isIntertwining' g := by ext; simp [Representation.tprod_apply, chiralRep, deltaCap₂] }
  metric c := { LinearMap.toSpanSingleton ℂ _ (deltaCap (chiralBasis c)) with
      isIntertwining' g := by ext; simp [Representation.tprod_apply, chiralRep, deltaCap] }
  -- Each coherence law reduces, by case analysis on `c`, to the matching abstract two-module
  -- δ lemma.
  contr_tmul_symm c x y := by cases c <;> exact deltaContr₂_comm _ _ _ _
  unit_symm c := by cases c <;> exact deltaUnit₂_symm _ _
  contr_unit c x := by cases c <;> exact deltaContr₂_unit _ _ x
  conj_basis_equivariant := by simp [chiralRep, Finsupp.single_apply]
  contr_metric c := by cases c <;> exact deltaContr₂_metric _ _
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

/-!
## F. Conjugation

Reality is a physical input the bare species cannot express: that the anti-chiral fields are the
complex conjugates of the chiral ones, that the Kähler metric is Hermitian, that the F-term
potential is real. Each is a statement that some quantity equals its own conjugate, so it can only
be phrased once conjugation is available. This section exposes that operation for the two shapes the
sector actually conjugates — the scalar `W` and the holomorphic covector `D_I W` — and certifies on
components that it is honest complex conjugation.

Conjugation is bundled into `chiralTensor` itself (§E): as a `ConjTensorSpecies` it carries `bar`
beside `τ`, and the framework supplies the conjugation map `conjT` and its laws (`conjT_smul`,
`conjT_conjT`, `conjT_contrT`, `conjT_eq_permT_iff`) once, abstractly, against any
`ConjTensorSpecies`. The chiral sector's conjugation flips holomorphy (`ChiralColor.bar`) while
preserving variance, and through `chiralTensor.conjT` the reality and Hermiticity conditions are
phrased. The basis index type `ι` is the same for every colour, so the identification `barIdx_eq`
is `rfl` and the component reindexing is the identity.

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
/-- For scalar tensors, `toField` of the normalized tensor conjugate is the complex conjugate of
`toField`. -/
lemma toField_conjScalar (t : (chiralTensor (ι := ι)).Tensor ![]) :
    (conjScalar t).toField = star t.toField := by
  rw [conjScalar, toField_permT]
  rw [toField_eq_repr, toField_eq_repr]
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
