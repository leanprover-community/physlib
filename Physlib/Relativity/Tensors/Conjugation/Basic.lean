/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.RankTwo
public import Physlib.Mathematics.Modules.ConjModule
public import Physlib.Mathematics.ForMathlib.SesquilinearForm

/-!

# Conjugation structure on a tensor species

## i. Overview

Each index of a tensor carries a colour naming the representation it transforms in. A species
already has the variance dual `τ c`, the colour an index must meet to contract. Conjugation adds a
second involution, the conjugate colour `bar c`: the colour an index transforms in after complex
conjugation. A spinor index is the textbook example: complex conjugation sends a left-handed Weyl
spinor to a right-handed one, `(ψ_α)* = ψ̄_α̇`, so `bar` swaps the left- and right-handed colours
while fixing a real vector colour. Variance is untouched, so `bar` commutes with `τ`. In an N=1
chiral sector `bar` swaps chiral and anti-chiral indices.

`conjT` conjugates a tensor at the basis level: `star` each coordinate in the species basis and
place it at the conjugate colour. Reality and Hermiticity are stated through it: a tensor is real
when conjugation fixes it, and a metric is Hermitian when conjugating it swaps its two indices.

Conjugation is intrinsic species data, not a detachable add-on: a `ConjTensorSpecies` is a
`TensorSpecies` bundled (`extends`) with the conjugate-colour involution `bar` and the coherence
the recipe needs. `bar c` shares basis labels with `c` (`barIdx_eq`) and the contraction
coefficients survive `star` (`conj_contrComm`), which together make conjugation commute with
contraction. `conjT` is then `conj`-semilinear, involutive, and commutes with contraction; the
last makes reality and Hermiticity compatible with raising and lowering indices.

At the single-index level, `conjEquiv : V c ≃ₛₗ V (bar c)` realises this conjugation: it reads a
vector's coordinates, conjugates them with `ConjModule.starFinsupp`, and re-seats them at the
conjugate colour. It rests on the conjugate module `ConjModule`
(`Physlib.Mathematics.Modules.ConjModule`), the same vectors with the scalar action twisted by
conjugation (`i` acts as `−i`). Equipping the conjugate colours with such conjugate-module
carriers is what makes a metric `V c ⊗ V (bar c) → k` genuinely bilinear and `IsHermitian` an
honest conjugate-transpose.

## ii. Key results

- `ConjTensorSpecies` is a tensor species bundled with its conjugation.
- `ConjTensorSpecies.conjT` is the conjugation of a tensor.
- `ConjTensorSpecies.conjT_conjT` proves that conjugation is an involution.
- `ConjTensorSpecies.conjT_contrT` proves that conjugation commutes with contraction.
- `ConjTensorSpecies.conjT_eq_permT_iff` is the componentwise criterion for
  `conjT t = permT σ h t'`, the workhorse for proving reality and Hermiticity conditions.
- `ConjTensorSpecies.conjEquiv` is the single-slot conjugate-linear isomorphism `V c ≃ₛₗ V (bar c)`.
- `ConjTensorSpecies.IsHermitian` is the structural conjugate-transpose condition on a metric slot.
- `ConjTensorSpecies.toSquareMatrix` is the square component matrix of a rank-two tensor whose
  second colour is the conjugate of its first;
  `ConjTensorSpecies.conjT_eq_permT_swap_iff_toSquareMatrix_isHermitian` says that conjugation swaps
  the two slots of `M` exactly when this matrix is Hermitian.
- `ConjTensorSpecies.isContrDualMatching_bar` and `ConjTensorSpecies.dualIdxEquiv_bar` say that
  conjugation preserves which basis labels pair to `1` under contraction: the basis vectors of
  `bar c` and `τ (bar c)` with labels `i` and `j` contract to `1` exactly when those of `c` and
  `τ c` with the same labels do.
- `ConjTensorSpecies.conjSingleT` is the conjugation of a one-slot tensor, at the colour
  `![bar x]`; `ConjTensorSpecies.conjSingleT_basis` is its action on basis vectors.
- `ConjTensorSpecies.toSesqForm` is the sesquilinear form `s, t ↦ M(t, s̄)` of a rank-two tensor
  `M` with `bar (c 0) = c 1`. Hermiticity of `M` is Hermiticity of this form, Mathlib's
  `LinearMap.IsSymm`;
  `ConjTensorSpecies.isSymm_toSesqForm_iff_conjT_eq_permT` and
  `ConjTensorSpecies.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian` are its tensor and matrix
  forms.
- `ConjTensorSpecies.isPosDef_toSesqForm_iff_toSquareMatrix_posDef`: `M` is positive-definite, i.e.
  its form is (`LinearMap.IsPosDef`), exactly when its square component matrix is `Matrix.PosDef`.

## iii. Table of contents

- A. The conjugation structure
- B. The conjugation of vectors
- C. Conjugation of tensors
- D. The involution law
- E. Commutation with contraction
- F. Hermitian pairings
- G. Dual bases under conjugation
- H. The sesquilinear form of a tensor
- I. Positive-definite tensors

-/

@[expose] public section
noncomputable section

open Module TensorSpecies TensorSpecies.Tensor

/-!

## A. The conjugation structure

A `ConjTensorSpecies` bundles a `TensorSpecies` (`extends`) with the conjugation data.
Conjugation is defined at the basis level, where it is "`star` the components" (§B). Four of the
new fields are
bookkeeping on colours and index sets, trivial to supply per instance: `bar` (the conjugate-colour
involution), `bar_involution`, `bar_tau` (it commutes with `τ`), and `barIdx_eq` (a colour and its
conjugate share basis labels). The one substantive field is `conj_contrComm`, that the contraction
coefficients are unchanged by `star`; this is what makes conjugation commute with contraction (§D),
and for a real (δ) contraction it is `star δ = δ`.

-/

/-- A tensor species bundled with a conjugation. Beyond the `TensorSpecies` it `extends`, it carries
the conjugate-colour involution `bar`, the index-set identification `barIdx_eq`, and the
contraction-coherence `conj_contrComm`. Also carries `bar_involution` and `bar_tau` (that `bar` is
involutive and commutes with the variance dual). -/
structure ConjTensorSpecies (k : Type) [CommRing k] [StarRing k] (C : Type) (G : Type) [Group G]
    (V : C → Type) [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    (basisIdx : C → Type) [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    (rep : (c : C) → Representation k G (V c)) (b : (c : C) → Basis (basisIdx c) k (V c))
    extends TensorSpecies k C G V basisIdx rep b where
  /-- The conjugate colour: the colour an index transforms in under complex conjugation; preserves
  variance (commutes with `τ`). -/
  bar : C → C
  /-- `bar` is an involution. -/
  bar_involution : Function.Involutive bar
  /-- `bar` commutes with the variance dual `τ`. -/
  bar_tau : ∀ c, bar (toTensorSpecies.τ c) = toTensorSpecies.τ (bar c)
  /-- Conjugation fixes the index set: the conjugate colour reuses the same basis labels.
  Conjugation conjugates components in an adapted basis; it never permutes labels, so the label
  sets of `c` and `bar c` coincide. -/
  barIdx_eq : ∀ c, basisIdx (bar c) = basisIdx c
  /-- Conjugation is equivariant: it preserves the action of the group. -/
  conj_basis_equivariant : ∀ (c : C) (g : G) (i j : basisIdx c),
      (b c).repr (rep c g (b c i)) j = star ((b (bar c)).repr
      (rep (bar c) g (b (bar c) (Equiv.cast (barIdx_eq c).symm i)))
      (Equiv.cast (barIdx_eq c).symm j))
  /-- Conjugation is compatible with contraction at the basis level: `star` of the contraction
  coefficient at colour `d` equals the coefficient at the conjugate colour `bar d`, with basis
  labels carried over by `barIdx_eq`. For a real (δ) contraction this is `star δ = δ`. -/
  conj_contrComm : ∀ (d : C) (x₁ : basisIdx d) (x₂ : basisIdx (toTensorSpecies.τ d)),
      star (toTensorSpecies.contr d (b d x₁ ⊗ₜ[k] b (toTensorSpecies.τ d) x₂))
        = toTensorSpecies.contr (bar d) (b (bar d) ((Equiv.cast (barIdx_eq d)).symm x₁) ⊗ₜ[k]
            b (toTensorSpecies.τ (bar d)) (basisIdxCongr (bar_tau d)
              ((Equiv.cast (barIdx_eq (toTensorSpecies.τ d))).symm x₂)))

namespace ConjTensorSpecies

open Tensor

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b)

/-- If `bar a = d`, then `bar (τ d) = τ a`. -/
lemma bar_tau_of_bar {a d : C} (hbar : S.bar a = d) : S.bar (S.τ d) = S.τ a :=
  (S.bar_tau d).trans (congrArg S.τ ((congrArg S.bar hbar).symm.trans (S.bar_involution a)))

/-!

## B. The conjugation of vectors

`conjEquiv` is the conjugate-linear isomorphism `V c ≃ₛₗ[starRingEnd k] V (bar c)`: read off the
coordinates of a vector in the species basis, conjugate them (`star`), and re-seat them as the
coordinates at the conjugate colour (the index sets agree by `barIdx_eq`). It is the single-slot
shadow of `conjT`, packaged as a bundled equivalence so the Hermitian-metric layer can apply it to a
metric slot. Semilinearity is built in via the coordinate `star`; invertibility is `star`'s
involutivity together with `bar`'s.

-/

/-- The conjugate-linear slot isomorphism `V c ≃ₛₗ[starRingEnd k] V (bar c)`: conjugate the
coordinates in the species basis and relabel to the conjugate colour via `barIdx_eq`. -/
def conjEquiv {c : C} : V c ≃ₛₗ[starRingEnd k] V (S.bar c) :=
  ((b c).repr.trans (ConjModule.starFinsupp (k := k))).trans
    ((Finsupp.domLCongr (Equiv.cast (S.barIdx_eq c).symm)).trans (b (S.bar c)).repr.symm)

/-- `conjEquiv` on a basis vector: `b c i ↦ b (bar c) i` (relabelled through `barIdx_eq`), since the
basis coordinates of `b c i` are the indicator at `i` and `star` fixes `0` and `1`. -/
@[simp] lemma conjEquiv_basis {c : C} (i : basisIdx c) :
    S.conjEquiv (b c i) = b (S.bar c) (Equiv.cast (S.barIdx_eq c).symm i) := by
  simp [conjEquiv, ConjModule.starFinsupp, Finsupp.domLCongr_apply, Finsupp.mapRange_single]

lemma conjEquiv_basis_repr {c : C} (v : V c) (φ : basisIdx (S.bar c)) :
    (b (S.bar c)).repr (S.conjEquiv v) φ
      = star ((b c).repr v (Equiv.cast (S.barIdx_eq c) φ)) := by
  simp only [conjEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    ConjModule.starFinsupp]
  rfl

lemma conjEquiv_equivariant {c : C} (g : G) (v : V c) :
    S.conjEquiv (rep c g v) = rep (S.bar c) g (S.conjEquiv v) := by
  rw [← (b c).sum_repr v]
  simp only [map_sum, map_smul, LinearEquiv.map_smulₛₗ, conjEquiv_basis, Equiv.cast_apply]
  congr
  funext x
  congr 1
  generalize_proofs h1 h2
  apply (b (S.bar c)).repr.injective
  ext j'
  obtain ⟨j, rfl⟩ := (Equiv.cast (S.barIdx_eq c).symm).surjective j'
  simpa [conjEquiv_basis_repr] using congrArg star (S.conj_basis_equivariant c g x j)

/-!

## C. Conjugation of tensors

We define the conjugation map `conjT` through its action on components, record that it conjugates
components in place (`componentMap_conjT`), and show it is `conj`-semilinear and additive.

Conventions for the index notation in this file. Indices are written in slot order: in `M_{IJ̄}`,
`I` is the first slot (Lean slot `0`, colour `c 0`) and `J̄` the second (slot `1`, colour
`c 1 = bar (c 0)`). As a tensor, `g = g_{IJ̄} dφᴵ ⊗ dφ̄^J̄` takes a holomorphic vector in its first
slot and an antiholomorphic one in its second: `g(u, v̄) = g_{IJ̄} uᴵ v̄^J̄`. An index of a
conjugate colour carries a bar or a dot (`Ī`, `α̇`), and conjugation adds a bar to each index,
removing it from an index that already has one.

For chiral scalar fields `φᴵ`, the basis vectors are the derivatives `e_I = ∂/∂φᴵ`, and their
conjugates `ē_Ī = ∂/∂φ̄^Ī`. A Kähler metric is `g_{IJ̄} = ∂_I ∂_J̄ K = g(e_I, ē_J̄)`. Holomorphic
index first is the standard convention, used throughout; it is a choice, since
`∂_I ∂_J̄ K = ∂_J̄ ∂_I K` (Schwarz's theorem).

-/

/-- Reindex component labels of `bar ∘ c` back to `c`, slotwise via the cast `barIdx_eq`. -/
def componentReindex {n : ℕ} (c : Fin n → C) :
    ComponentIdx (S := S.toTensorSpecies) (fun i => S.bar (c i)) ≃
      ComponentIdx (S := S.toTensorSpecies) c :=
  Equiv.piCongrRight fun i => Equiv.cast (S.barIdx_eq (c i))

/-- Conjugation of a tensor: conjugate the components and reindex the basis to the conjugate
colours.  -/
def conjT {n : ℕ} {c : Fin n → C} : S.Tensor c →ₛₗ[starRingEnd k]
    S.Tensor (fun i => S.bar (c i)) where
  toFun t := ofComponents (fun i => S.bar (c i))
    (fun b => star (componentMap c t (S.componentReindex c b)))
  map_add' t₁ t₂ := by
    apply componentMap_ext
    intro b
    simp  [map_add, Pi.add_apply, star_add]
  map_smul' r t := by
    apply componentMap_ext
    intro b
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', componentMap_ofComponents]
    rfl

lemma conjT_apply {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    S.conjT t = ofComponents (fun i => S.bar (c i))
      (fun b => star (componentMap c t (S.componentReindex c b))) :=
  rfl

/-- Components of a conjugated tensor: the `star` of the original components, reindexed. -/
@[simp] lemma componentMap_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c)
    (b : ComponentIdx (S := S.toTensorSpecies) (fun i => S.bar (c i))) :
    componentMap (fun i => S.bar (c i)) (S.conjT t) b
      = star (componentMap c t (S.componentReindex c b)) := by
  simp [conjT_apply, componentMap_ofComponents]

/-- Conjugating a rank-two tensor conjugates each component and bars both indices:
`(T̄)_{ĪJ̄} = (T_{IJ})*`, where barring a barred index removes the bar. For example, `ψ_α χ_β` goes
to `ψ̄_α̇ χ̄_β̇`, and a tensor `M_{IJ̄}` goes to `(M̄)_{ĪJ} = (M_{IJ̄})*`. -/
lemma toMatrix_conjT {cs : Fin 2 → C} (t : S.Tensor cs) :
    toMatrix (S.conjT t) = ((toMatrix t).map star).submatrix
      (Equiv.cast (S.barIdx_eq (cs 0))) (Equiv.cast (S.barIdx_eq (cs 1))) := by
  ext x y
  simp only [toMatrix_apply, Matrix.submatrix_apply, Matrix.map_apply,
    ← componentMap_eq_repr, componentMap_conjT]
  exact congrArg _ (congrArg _ (funext fun i => by fin_cases i <;> rfl))


lemma conjT_basis {n : ℕ} {c : Fin n → C} (i : ComponentIdx (S := S.toTensorSpecies) c) :
    S.conjT (basis c i) = basis (fun i => S.bar (c i)) ((S.componentReindex c).symm i) := by
  apply componentMap_ext
  intro b
  simp [componentMap_conjT]
  simp only [componentMap_eq_repr, Basis.repr_self, componentReindex, Finsupp.single_apply]
  split_ifs with h h2 h3
  · simp
  · subst h
    simp at h2
  · subst h3
    simp at h
  · simp

/-- Conjugation of a vector, `vᴵ ↦ v̄^Ī = (vᴵ)*`, landing at the conjugate colour. For example, a
left-handed Weyl spinor `ψ_α` goes to the right-handed `ψ̄_α̇`. -/
def conjSingleT (x : C) : S.Tensor ![x] →ₛₗ[starRingEnd k] S.Tensor ![S.bar x] :=
  (permT (S := S.toTensorSpecies) (c := fun i => S.bar ((![x] : Fin 1 → C) i))
    (c1 := ![S.bar x]) id (by simp [IsReindexing])).comp S.conjT

/-- Conjugation sends the basis vector `e_I` to `ē_Ī`, the basis vector of the conjugate colour with
the same label. -/
lemma conjSingleT_basis (x : C) (z : basisIdx x) :
    S.conjSingleT x (basis ![x] (ComponentIdx.single.symm z)) =
      basis ![S.bar x] (ComponentIdx.single.symm (cast (S.barIdx_eq x).symm z)) := by
  rw [conjSingleT, LinearMap.comp_apply, conjT_basis, permT_basis]
  congr 1 with m
  fin_cases m
  rfl

lemma conjT_pure {n : ℕ} {c : Fin n → C} (p : Tensor.Pure S.toTensorSpecies c) :
    S.conjT p.toTensor = Pure.toTensor (fun i => S.conjEquiv (p i)) := by
  apply componentMap_ext
  intro φ
  simp only [componentMap_conjT, componentMap_pure, Pure.componentMap_apply]
  simp [Pure.component]
  congr
  funext x
  rw [S.conjEquiv_basis_repr]
  rfl


/-- Componentwise criterion for `conjT t = permT σ h t'`. The conjugate of `t` equals the
recolouring `permT σ h t'` exactly when, at every component, the `star`-conjugated reindexed
component of `t` matches the corresponding component of `permT σ h t'`. This packages the
`componentMap_conjT` expansion and the `repr`/`componentMap` bridge that the reality and Hermiticity
proofs downstream would otherwise repeat by hand; the caller is left only with the species-specific
permutation bookkeeping on the right-hand side. -/
lemma conjT_eq_permT_iff {n m : ℕ} {c : Fin n → C} {c' : Fin m → C}
    {σ : Fin n → Fin m} (h : IsReindexing c' (fun i => S.bar (c i)) σ)
    (t : S.Tensor c) (t' : S.Tensor c') :
    S.conjT t = permT σ h t' ↔
      ∀ φ : ComponentIdx (S := S.toTensorSpecies) (fun i => S.bar (c i)),
        star (componentMap c t (S.componentReindex c φ))
          = (Tensor.basis (fun i => S.bar (c i))).repr (permT σ h t') φ := by
  constructor
  · intro H φ
    rw [← H, ← componentMap_eq_repr, componentMap_conjT]
  · intro H
    apply componentMap_ext
    intro φ
    rw [componentMap_conjT]
    exact H φ

lemma conjT_equivariant {n : ℕ} {c : Fin n → C} (g : G) (t : S.Tensor c) :
    S.conjT (g • t) = g • S.conjT t := by
  induction' t using induction_on_basis with b r t ht t1 t2 ht1 ht2
  · simp [basis_apply, actionT_pure, conjT_pure, Pure.actionP_eq, conjEquiv_equivariant]
  · simp
  · simp [LinearMap.map_smulₛₗ, actionT_smul, ht]
  · simp [ht1, ht2]

/-!

## D. The involution law

We prove `conjT_conjT`: conjugating a tensor twice returns it, up to the identity recolouring
`bar ∘ bar ∘ c = c`. The supporting lemmas reconcile the iterated basis-label casts.

-/

/-- Undoing the two cast reindexings (at `bar c` then at `c`) on a label of the doubly-conjugated
colour returns the `bar_involution` cast. Free from `barIdx_eq` by `cast_cast` + proof
irrelevance, with no coherence field needed. -/
private lemma barIdx_involutive_symm (c : C) (y : basisIdx (S.bar (S.bar c))) :
    Equiv.cast (S.barIdx_eq c) (Equiv.cast (S.barIdx_eq (S.bar c)) y)
      = basisIdxCongr (S.bar_involution c) y := by
  simp only [basisIdxCongr, Equiv.cast_apply, cast_cast]

/-- The identity permutation satisfies `IsReindexing` from `c` to `bar ∘ bar ∘ c`, as `bar` is an
involution. -/
lemma isReindexing_bar_bar {n : ℕ} (c : Fin n → C) :
    IsReindexing c (fun i => S.bar (S.bar (c i))) (id : Fin n → Fin n) :=
  ⟨Function.bijective_id, fun i => (S.bar_involution (c i)).symm⟩

/-- Conjugation is an involution: conjugating twice returns the original tensor, up to the
`bar_involution` recolouring (the identity permutation `permT`). -/
lemma conjT_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    S.conjT (S.conjT t)
      = permT id (S.isReindexing_bar_bar c) t := by
  apply componentMap_ext
  intro φ
  rw [componentMap_conjT, componentMap_conjT, star_star]
  rw [componentMap_eq_repr (fun i => S.bar (S.bar (c i))), permT_basis_repr_symm_apply,
    ← componentMap_eq_repr c]
  refine congrArg (fun ψ => (componentMap c) t ψ) ?_
  funext i
  have hinv : (IsReindexing.inv id (S.isReindexing_bar_bar c)) i = i :=
    IsReindexing.inv_apply_apply id _ i
  show Equiv.cast (S.barIdx_eq (c i)) (Equiv.cast (S.barIdx_eq (S.bar (c i))) (φ i)) = _
  rw [S.barIdx_involutive_symm]
  exact basisIdxCongr_heq_arg _ _ (by rw [hinv])

/-!

## E. Commutation with contraction

We prove `conjT_contrT`: conjugation commutes with contracting two dual-coloured slots. The
contraction expands as a sum over the contracted index pair, and `conj_contrComm` matches the
conjugated coefficients to those on the `bar`-images.

-/

/-- Slots with dual colour in `c` have dual colour in `bar ∘ c`, as `bar` commutes with `τ`. -/
lemma contrCond_bar {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) :
    i ≠ j ∧ S.τ ((S.bar ∘ c) i) = (S.bar ∘ c) j :=
  ⟨h.1, by rw [Function.comp_apply, Function.comp_apply, ← S.bar_tau, h.2]⟩

/-- Conjugation commutes with contraction: conjugating a contracted tensor equals contracting the
conjugate on the `bar`-images of the same two slots. -/
lemma conjT_contrT {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : S.Tensor c) :
    S.conjT (contrT n i j h t)
      = contrT n i j (S.contrCond_bar h) (S.conjT t) := by
  apply componentMap_ext
  intro φ
  rw [componentMap_conjT, componentMap_eq_repr, Tensor.contrT_basis_repr_apply]
  have hrhs := Tensor.contrT_basis_repr_apply (S := S.toTensorSpecies) (c := fun i => S.bar (c i))
    (i := i) (j := j) (S.contrCond_bar h) (S.conjT t) φ
  rw [componentMap_eq_repr]
  refine Eq.trans ?_ hrhs.symm
  rw [star_sum]
  -- `componentReindex` carries the `bar`-side contraction section onto the `c`-side one: it
  -- commutes with `dropPair` definitionally, so the section bijection is just `subtypeEquiv`.
  have hmem : ∀ a : ComponentIdx (S := S.toTensorSpecies) (S.bar ∘ c),
      a ∈ ComponentIdx.DropPairSection φ ↔
        S.componentReindex c a ∈
          ComponentIdx.DropPairSection (S.componentReindex (c ∘ i.succSuccAbove j) φ) := by
    intro a
    simp only [ComponentIdx.DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Equiv.apply_eq_iff_eq (S.componentReindex (c ∘ i.succSuccAbove j))).symm
  refine (Finset.sum_equiv (Equiv.subtypeEquiv (S.componentReindex c) hmem)
    ?_ ?_).symm
  · exact fun _ => iff_of_true (Finset.mem_attach _ _) (Finset.mem_attach _ _)
  intro b'' _
  simp only [Equiv.subtypeEquiv_apply]
  rw [← componentMap_eq_repr (fun i => S.bar (c i)), componentMap_conjT, componentMap_eq_repr c t,
    star_mul']
  congr 1
  rw [S.conj_contrComm (c i) ((S.componentReindex c b''.1) i)
        (basisIdxCongr (by rw [h.2]) ((S.componentReindex c b''.1) j)),
    show (S.componentReindex c b''.1) i = Equiv.cast (S.barIdx_eq (c i)) (b''.1 i) from rfl,
    show (S.componentReindex c b''.1) j = Equiv.cast (S.barIdx_eq (c j)) (b''.1 j) from rfl,
    Equiv.symm_apply_apply]
  congr 2
  exact congrArg (b (S.τ (S.bar (c i)))) (basisIdxCongr_heq_arg _ _
    (HEq.symm ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)))))


/-!

## F. Hermitian pairings

A metric slot pairs a colour `c` with its conjugate `bar c`. `IsHermitian` is the structural form of
`g_{IJ̄} = conj g_{JĪ}`: conjugating and swapping the two slots through `conjEquiv` returns `g`'s
`star`. Because `V c` and `V (bar c)` are genuinely different modules this is the honest
conjugate-transpose, not a bare `g = g.flip`. The condition is fixed here as `IsHermitian`; a
downstream metric layer instantiates it for a concrete pairing.

A tensor `M_{IJ̄}` with one index and one conjugate index, such as a Kähler metric `g_{IJ̄}`, has
the matrix of components `(M_{IJ̄})` (`toSquareMatrix`), regarded as a square matrix over the labels
of `I`. Its entries are the components themselves. Lean needs this step because the labels of a
colour and of its conjugate are different types, identified by `barIdx_eq`, and Hermiticity,
positive-definiteness and the inverse are defined only for square matrices. `M` is Hermitian,
`(M_{IJ̄})* = M_{JĪ}`, exactly when this matrix is.

-/

open scoped TensorProduct in
/-- A pairing `g : V c ⊗ V (bar c) → k` is Hermitian when conjugating and swapping its two slots
via `conjEquiv` returns its `star`: `g (x ⊗ y) = star (g (conjEquiv.symm y ⊗ conjEquiv x))`. -/
def IsHermitian {c : C} (g : V c ⊗[k] V (S.bar c) →ₗ[k] k) : Prop :=
  ∀ (x : V c) (y : V (S.bar c)),
    g (x ⊗ₜ[k] y) = star (g (S.conjEquiv.symm y ⊗ₜ[k] S.conjEquiv x))

/-- The matrix `(M_{IJ̄})`, with entries unchanged, regarded as a square matrix over the labels of
`I`. Lean needs this step because the labels of a colour and of its conjugate are different types,
identified by `barIdx_eq`; only for a square matrix are Hermiticity, positive-definiteness and the
inverse defined. Convention: the unbarred index is the row and the barred index the column, entry
`(I, J)` being `M_{IJ̄}`, as physicists write the matrix. For a Kähler metric `g_{IJ̄}` it is the
usual matrix `(g_{IJ̄})`. -/
def toSquareMatrix {c : Fin 2 → C} (M : S.Tensor c) (hbar : S.bar (c 0) = c 1 := by rfl) :
    Matrix (basisIdx (c 0)) (basisIdx (c 0)) k :=
  (toMatrix M).reindex (Equiv.refl _) (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)))

lemma toSquareMatrix_apply {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (M : S.Tensor c)
    (i j : basisIdx (c 0)) :
    S.toSquareMatrix M hbar i j =
      toMatrix M i ((Equiv.cast (hbar ▸ S.barIdx_eq (c 0))).symm j) :=
  rfl

/-- `toMatrix M` is `toSquareMatrix M` with its columns labelled by `J̄` instead of `J`. -/
lemma toMatrix_eq_submatrix_toSquareMatrix {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (M : S.Tensor c) :
    toMatrix M =
      (S.toSquareMatrix M hbar).submatrix id (Equiv.cast (hbar ▸ S.barIdx_eq (c 0))) :=
  ((Matrix.reindex (Equiv.refl _) (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)))).symm_apply_apply
    (toMatrix M)).symm

/-- For `M_{IJ̄}`, the conjugate `(M̄)_{ĪJ} = (M_{IJ̄})*` and the swapped tensor `M_{JĪ}` have the
same index types, a barred index then an ordinary one. They are equal, `(M_{IJ̄})* = M_{JĪ}`,
exactly when the matrix `(M_{IJ̄})` is Hermitian. A Kähler metric satisfies this. -/
lemma conjT_eq_permT_swap_iff_toSquareMatrix_isHermitian {c : Fin 2 → C}
    (hbar : S.bar (c 0) = c 1) (M : S.Tensor c) :
    S.conjT M = permT ![1, 0] (IsReindexing.swap_of_eq hbar.symm
      ((congrArg S.bar hbar).symm.trans (S.bar_involution (c 0))).symm) M ↔
    (S.toSquareMatrix M hbar).IsHermitian := by
  obtain ⟨a, d, rfl⟩ : ∃ a d, c = ![a, d] := ⟨c 0, c 1, by funext i; fin_cases i <;> rfl⟩
  change S.bar a = d at hbar
  subst hbar
  unfold toSquareMatrix
  rw [← toMatrix_injective.eq_iff, toMatrix_conjT,
    toMatrix_permT_swap rfl (S.bar_involution a).symm]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Matrix.IsHermitian, ← Matrix.ext_iff, ← Matrix.ext_iff]
  have hbb : basisIdx a = basisIdx (S.bar (S.bar a)) := by rw [S.bar_involution]
  change (∀ (i : basisIdx (S.bar a)) (j : basisIdx (S.bar (S.bar a))),
      star (toMatrix M (cast (S.barIdx_eq a) i) (cast (S.barIdx_eq (S.bar a)) j)) =
        toMatrix M (cast hbb.symm j) i) ↔
    ∀ i j : basisIdx a, star (toMatrix M j (cast (S.barIdx_eq a).symm i)) =
      toMatrix M i (cast (S.barIdx_eq a).symm j)
  constructor
  · intro H i j
    simpa [cast_cast] using H (cast (S.barIdx_eq a).symm j) (cast hbb i)
  · intro H i j
    simpa [cast_cast] using H (cast hbb.symm j) (cast (S.barIdx_eq a) i)

open HasContrDualBases in
/-- The matrix of `g_{IJ̄} t^{J̄K}` is the product of the square matrix `(g_{IJ̄})` and the matrix
`(t^{J̄K})`, with the rows of `(t^{J̄K})` labelled by `J`. -/
lemma toMatrix_contractInnerT_eq_toSquareMatrix_mul [HasContrDualBases S.toTensorSpecies]
    {cs ds : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (h : S.τ (cs 1) = ds 0) (M : S.Tensor cs)
    (t : S.Tensor ds) :
    toMatrix (contractInnerT h M t) =
      S.toSquareMatrix M hbar * (toMatrix t).submatrix
        (dualIdxEquiv h ∘ (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm)
        (id : basisIdx (ds 1) → _) := by
  refine (toMatrix_contractInnerT h M t).trans ?_
  rw [S.toMatrix_eq_submatrix_toSquareMatrix hbar M]
  exact Matrix.submatrix_id_mul_right _ (t.toMatrix.submatrix (dualIdxEquiv h) id) id
    (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0)))

/-!

## G. Dual bases under conjugation

A lower index contracts with an upper one, and the bases are dual: `e_α` contracted with `e^β` gives
`δ_α^β`. This section shows that the conjugate bases are dual in the same way: `ē_α̇` contracted
with `ē^β̇` gives `δ_α̇^β̇`. For example, for a vector `vᴵ` and a covector `w_I`,
`(vᴵ w_I)* = v̄^Ī w̄_Ī`: the conjugate contraction pairs the same labels. This follows because
contraction commutes with conjugation (`conj_contrComm`).

-/

open HasContrDualBases in
/-- The conjugate bases are dual: if `e_α` contracted with `e^β` is `δ_α^β`, then `ē_α̇` contracted
with `ē^β̇` is `δ_α̇^β̇`. -/
lemma isContrDualMatching_bar [HasContrDualBases S.toTensorSpecies] (d : C) :
    IsContrDualMatching S.toTensorSpecies (S.bar d)
      ((basisIdxCongr (S.bar_tau d)).symm.trans ((Equiv.cast (S.barIdx_eq (S.τ d))).trans
        ((contrDualIdxEquiv S.toTensorSpecies d).trans (Equiv.cast (S.barIdx_eq d)).symm))) := by
  intro y₁ y₂
  have key := S.conj_contrComm d (Equiv.cast (S.barIdx_eq d) y₁)
    (Equiv.cast (S.barIdx_eq (S.τ d)) ((basisIdxCongr (S.bar_tau d)).symm y₂))
  rw [contr_basis_eq_ite] at key
  simp only [Equiv.symm_apply_apply, basisIdxCongr_symm, basisIdxCongr_apply_apply,
    basisIdxCongr_rfl] at key
  rw [← key]
  simp only [Equiv.trans_apply, basisIdxCongr_symm, Equiv.eq_symm_apply]
  split_ifs <;> simp

open HasContrDualBases in
/-- `dualIdxEquiv` sends a lower label `α` to the upper label `α` it contracts with to `1`.
Conjugation commutes with this: the dotted label `α̇` pairs with the dotted upper label `α̇`. -/
lemma dualIdxEquiv_bar [Nontrivial k] [HasContrDualBases S.toTensorSpecies] {c1 c2 c3 : C}
    (h : S.τ c1 = c2) (h' : S.τ (S.bar c1) = c3) (hbar : S.bar c2 = c3) (x : basisIdx c1) :
    dualIdxEquiv h' (cast (S.barIdx_eq c1).symm x) =
      cast (hbar ▸ S.barIdx_eq c2).symm (dualIdxEquiv h x) := by
  subst h hbar
  rw [dualIdxEquiv_apply, dualIdxEquiv_apply,
    contrDualIdxEquiv_eq_of_isContrDualMatching (S.isContrDualMatching_bar c1)]
  simp only [basisIdxCongr, ← Equiv.cast_symm, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.cast_apply, cast_cast, cast_eq, Equiv.cast_refl, Equiv.refl_apply]

open HasContrDualBases in
/-- Removing a bar and lowering an index commute on labels. From a label of the upper barred index
`J̄`, removing the bar and then lowering gives the same label of the lower index `J` as lowering and
then removing the bar.
```
upper J̄ (τ d)  → remove bar →  upper J (τ a)
      ↓ lower                        ↓ lower
lower J̄ (d)    → remove bar →  lower J (a)
```
The left-hand side of the statement goes across the top and down, the right-hand side down and
across the bottom. -/
lemma dualIdxEquiv_bar_tau [Nontrivial k] [HasContrDualBases S.toTensorSpecies] {a d : C}
    (hbar : S.bar a = d) (j : basisIdx (S.τ d)) :
    dualIdxEquiv (S.τ_τ_apply a)
        ((Equiv.cast (S.bar_tau_of_bar hbar ▸ S.barIdx_eq (S.τ d))).symm j) =
      Equiv.cast (hbar ▸ S.barIdx_eq a) ((dualIdxEquiv (rfl : S.τ d = S.τ d)).symm j) := by
  subst hbar
  obtain ⟨x, rfl⟩ : ∃ x, dualIdxEquiv (rfl : S.τ (S.bar a) = S.τ (S.bar a))
      ((Equiv.cast (S.barIdx_eq a)).symm x) = j :=
    ⟨Equiv.cast (S.barIdx_eq a) ((dualIdxEquiv rfl).symm j), by
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    ← dualIdxEquiv_symm (rfl : S.τ a = S.τ a) (S.τ_τ_apply a), Equiv.symm_apply_eq]
  have h' := S.dualIdxEquiv_bar (rfl : S.τ a = S.τ a) (rfl : S.τ (S.bar a) = S.τ (S.bar a))
    (S.bar_tau a) x
  simp only [dualIdxEquiv_apply, basisIdxCongr, Equiv.cast_apply] at h' ⊢
  rw [Equiv.symm_apply_eq]
  simpa only [← Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq] using h'

/-!

## H. The sesquilinear form of a tensor

A tensor `g_{IJ̄}` with one index and one conjugate index, such as a Kähler metric, defines a
Hermitian form on vectors of one colour. By the slot conventions of §C, `g` takes a holomorphic
vector `u` in its first slot and an antiholomorphic vector in its second,
`g(u, v̄) = g_{IJ̄} uᴵ v̄^J̄`. To pair two vectors `s, t` of the same colour, one of them is
conjugated so that it fits the second slot.

Convention. We use Mathlib's sesquilinear forms, so that Mathlib's results on Hermitian and
positive-definite forms apply. A Mathlib form `⟨s, t⟩` is conjugate-linear in its left argument `s`.
So `s` is the vector that is conjugated: `s̄` goes into the second, barred slot of `g`, and `t` goes
unchanged into the first slot,

`⟨s, t⟩ = g(t, s̄) = g_{IJ̄} tᴵ s̄^J̄`.

The order of the arguments of `⟨s, t⟩` is thus opposite to the order of the slots of `g`. Physics
usually writes the form the other way round, `g_{IJ̄} uᴵ v̄^J̄`, conjugate-linear in its right
argument `v`. This does not change norms or Hermiticity: `⟨t, t⟩ = g_{IJ̄} tᴵ t̄^J̄` is the norm
squared of the kinetic term `g_{IJ̄} ∂φᴵ ∂φ̄^J̄`. It does change the matrix: on the basis
`e_I = ∂/∂φᴵ`, `⟨e_I, e_J⟩ = g(e_J, ē_I) = g_{JĪ}`, the transpose of `(g_{IJ̄})`.

`g` is Hermitian, `(g_{IJ̄})* = g_{JĪ}`, exactly when its form is (`LinearMap.IsSymm`,
`⟨s, t⟩* = ⟨t, s⟩`), and positive-definite, `⟨t, t⟩ > 0` for `t ≠ 0`, exactly when its form is
(`LinearMap.IsPosDef`). On a concrete species the colour conditions hold by `rfl`, so the form of
`g` on vectors of colour `x` is written `S.toSesqForm x g`.

-/

open HasContrDualBases
open scoped Matrix

/-- The Hermitian form `⟨s, t⟩ = M(t, s̄) = M_{IJ̄} tᴵ s̄^J̄` of a tensor `M_{IJ̄}`, on vectors
`s, t`. Convention: as in Mathlib it is conjugate-linear in its left argument `s`; `s̄` fills the
second, barred slot of `M` and `t` the first, so the argument order is opposite to the slot order.
-/
def toSesqForm (x : C) {c : Fin 2 → C} (M : S.Tensor c) (hbar : S.bar (c 0) = c 1 := by rfl)
    (hx : S.τ x = c 0 := by rfl) : S.Tensor ![x] →ₗ⋆[k] S.Tensor ![x] →ₗ[k] k :=
  (toLinearMap₂ x (S.bar x) M hx (by rw [← hbar, ← hx, S.bar_tau])).flip.comp (S.conjSingleT x)

/-- Since the left argument of the form fills the second slot of `M` (`toSesqForm`),
`⟨e_I, e_J⟩ = M(e_J, ē_I) = M_{JĪ}`: the matrix of the form is the transpose of `(M_{IJ̄})`. For a
Kähler metric, `⟨∂_I, ∂_J⟩ = ∂_J ∂_Ī K = g_{JĪ}`. -/
lemma toMatrix₂_toSesqForm [HasContrDualBases S.toTensorSpecies] {x : C} {c : Fin 2 → C}
    (hbar : S.bar (c 0) = c 1) (hx : S.τ x = c 0) (M : S.Tensor c) :
    LinearMap.toMatrix₂ ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx)))
        ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx)))
        (S.toSesqForm x M hbar hx) = (S.toSquareMatrix M hbar)ᵀ := by
  nontriviality k
  have hy : S.τ (S.bar x) = c 1 := by rw [← hbar, ← hx, S.bar_tau]
  ext i j
  have h := congrFun (congrFun (toMatrix₂_toLinearMap₂ hx hy M) j)
    (dualIdxEquiv hy (cast (S.barIdx_eq x).symm ((dualIdxEquiv hx).symm i)))
  rw [LinearMap.toMatrix₂_apply, Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    S.dualIdxEquiv_bar hx hy hbar, Equiv.apply_symm_apply] at h
  rw [LinearMap.toMatrix₂_apply, toSesqForm, LinearMap.comp_apply, LinearMap.flip_apply,
    Module.Basis.reindex_apply, Module.Basis.reindex_apply, Equiv.symm_trans_apply,
    Equiv.symm_trans_apply, conjSingleT_basis, Matrix.transpose_apply, toSquareMatrix_apply]
  exact h

/-- `⟨s, t⟩* = ⟨t, s⟩` for all `s, t` exactly when `(M_{IJ̄})* = M_{JĪ}`. -/
lemma isSymm_toSesqForm_iff_toSquareMatrix_isHermitian [HasContrDualBases S.toTensorSpecies]
    {x : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (hx : S.τ x = c 0) (M : S.Tensor c) :
    (S.toSesqForm x M hbar hx).IsSymm ↔ (S.toSquareMatrix M hbar).IsHermitian := by
  rw [LinearMap.isSymm_iff_isHermitian_toMatrix
    ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx))), toMatrix₂_toSesqForm,
    Matrix.isHermitian_transpose_iff]

/-- `⟨s, t⟩* = ⟨t, s⟩` for all `s, t` exactly when the conjugate of `M` equals `M` with its two
indices swapped, `(M_{IJ̄})* = M_{JĪ}`. -/
lemma isSymm_toSesqForm_iff_conjT_eq_permT [HasContrDualBases S.toTensorSpecies]
    {x : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (hx : S.τ x = c 0) (M : S.Tensor c) :
    (S.toSesqForm x M hbar hx).IsSymm ↔ S.conjT M = permT ![1, 0] (IsReindexing.swap_of_eq hbar.symm
      ((congrArg S.bar hbar).symm.trans (S.bar_involution (c 0))).symm) M := by
  rw [isSymm_toSesqForm_iff_toSquareMatrix_isHermitian,
    conjT_eq_permT_swap_iff_toSquareMatrix_isHermitian]

/-!

## I. Positive-definite tensors

-/

section PosDef

variable [PartialOrder k]

/-- The form is positive-definite, Hermitian with `M_{IJ̄} tᴵ t̄^J̄ > 0` for every `t ≠ 0`, exactly
when the matrix `(M_{IJ̄})` is. A Kähler metric is positive-definite, which makes kinetic terms
positive. -/
lemma isPosDef_toSesqForm_iff_toSquareMatrix_posDef [HasContrDualBases S.toTensorSpecies]
    {x : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (hx : S.τ x = c 0) (M : S.Tensor c) :
    (S.toSesqForm x M hbar hx).IsPosDef ↔ (S.toSquareMatrix M hbar).PosDef := by
  rw [LinearMap.isPosDef_iff_posDef_toMatrix
    ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx))), toMatrix₂_toSesqForm,
    Matrix.PosDef.transpose_iff]

end PosDef

section Field

variable {k : Type} [Field k] [StarRing k] [PartialOrder k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b)

/-- Over a field, the matrix `(M_{IJ̄})` of a positive-definite tensor is invertible. -/
lemma isUnit_det_toSquareMatrix_of_isPosDef [HasContrDualBases S.toTensorSpecies] {x : C}
    {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (hx : S.τ x = c 0) {M : S.Tensor c}
    (hM : (S.toSesqForm x M hbar hx).IsPosDef) :
    IsUnit (S.toSquareMatrix M hbar).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    ((S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef hbar hx M).1 hM).isUnit

end Field

end ConjTensorSpecies
end
end
