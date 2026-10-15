/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.UnitTensorContraction
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
- `ConjTensorSpecies.squareMatrixOf` is the square component matrix of `M : ![a, bar a]`;
  `ConjTensorSpecies.conjT_eq_permT_swap_iff_isHermitian` says that conjugation swaps the two slots
  of `M` exactly when this matrix is Hermitian.
- `ConjTensorSpecies.isContrDualMatching_bar` proves that the dual-label matching at `d`, carried to
  `bar d` through `barIdx_eq`, satisfies the δ law there; `ConjTensorSpecies.dualIdxEquiv_bar`
  says that `dualIdxEquiv` commutes with conjugation.
- `ConjTensorSpecies.conjSingleT` is the conjugation of a one-slot tensor, at the colour
  `![bar x]`; `ConjTensorSpecies.conjSingleT_basis` is its action on basis vectors.
- `ConjTensorSpecies.toSesqForm` is the sesquilinear form `s, t ↦ M(t, s̄)` of a tensor
  `M : ![a, bar a]`. Hermiticity of `M` is Hermiticity of this form, Mathlib's `LinearMap.IsSymm`;
  `ConjTensorSpecies.isSymm_toSesqForm_iff_conjT_eq_permT` and
  `ConjTensorSpecies.isSymm_toSesqForm_iff_isHermitian` are its tensor and matrix forms.
- `ConjTensorSpecies.isPosDef_toSesqForm_iff_posDef`: `M` is positive-definite, i.e. its form is
  (`LinearMap.IsPosDef`), exactly when its square component matrix is `Matrix.PosDef`.
- `ConjTensorSpecies.inverseT` is the inverse of a rank-two tensor. Its square component matrix
  is the inverse of that of `M` (`squareMatrixOf_inverseT`), so it stays Hermitian and
  positive-definite (`isSymm_toSesqForm_inverseT`, `isPosDef_toSesqForm_inverseT`).
- `ConjTensorSpecies.nondegenerate_toSesqForm_iff` identifies invertibility of the component
  matrix with nondegeneracy of the sesquilinear form.
- `ConjTensorSpecies.crossToEnd_right_injective`: contraction with `M` is injective when its
  component matrix is invertible. Then `crossToEnd_inverseT` and `crossToEnd_inverseT_left` are the
  contraction laws of the inverse and `eq_inverseT` its uniqueness.

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
- J. The inverse of a nondegenerate tensor
  - J.1. The inverse
  - J.2. Over a field
  - J.3. Over `RCLike` scalars

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

/-- The component matrix of a conjugated rank-two tensor is the entrywise `star` of the original,
with labels carried over by `barIdx_eq`. -/
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

/-- Conjugation of a one-slot tensor, at the colour `![bar x]`: `conjT` followed by the identity
reindexing from `fun i => bar (![x] i)`. -/
def conjSingleT (x : C) : S.Tensor ![x] →ₛₗ[starRingEnd k] S.Tensor ![S.bar x] :=
  (permT (S := S.toTensorSpecies) (c := fun i => S.bar ((![x] : Fin 1 → C) i))
    (c1 := ![S.bar x]) id (by simp [IsReindexing])).comp S.conjT

/-- Conjugation sends the basis vector of a label of `x` to the basis vector of the same label,
read at `bar x` through `barIdx_eq`. -/
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

For a tensor `M : ![a, bar a]`, identifying the labels of `bar a` with those of `a` (`barIdx_eq`)
makes its component matrix square (`squareMatrixOf`). Conjugation swaps the two slots of `M`,
`M_{IJ̄} = conj M_{JĪ}`, exactly when this matrix is Hermitian.

-/

open scoped TensorProduct in
/-- A pairing `g : V c ⊗ V (bar c) → k` is Hermitian when conjugating and swapping its two slots
via `conjEquiv` returns its `star`: `g (x ⊗ y) = star (g (conjEquiv.symm y ⊗ conjEquiv x))`. -/
def IsHermitian {c : C} (g : V c ⊗[k] V (S.bar c) →ₗ[k] k) : Prop :=
  ∀ (x : V c) (y : V (S.bar c)),
    g (x ⊗ₜ[k] y) = star (g (S.conjEquiv.symm y ⊗ₜ[k] S.conjEquiv x))

/-- The component matrix of `M : ![a, bar a]` as a square matrix over the labels of `a`, the
labels of `bar a` identified with those of `a` (`barIdx_eq`). -/
def squareMatrixOf {a d : C} (M : S.Tensor ![a, d]) (hbar : S.bar a = d := by rfl) :
    Matrix (basisIdx a) (basisIdx a) k :=
  (toMatrix M).reindex (Equiv.refl _) (Equiv.cast (hbar ▸ S.barIdx_eq a))

lemma squareMatrixOf_apply {a d : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d])
    (i j : basisIdx a) :
    S.squareMatrixOf M hbar i j = toMatrix M i ((Equiv.cast (hbar ▸ S.barIdx_eq a)).symm j) :=
  rfl

/-- The component matrix of `M` is recovered from `squareMatrixOf` by carrying the column labels
back to `bar a`. -/
lemma toMatrix_eq_submatrix_squareMatrixOf {a d : C} (hbar : S.bar a = d)
    (M : S.Tensor ![a, d]) :
    toMatrix M = (S.squareMatrixOf M hbar).submatrix id (Equiv.cast (hbar ▸ S.barIdx_eq a)) := by
  rw [squareMatrixOf, Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.refl_symm,
    Equiv.coe_refl, Function.id_comp, Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- Conjugation swaps the two slots of `M : ![a, bar a]`, `M_{IJ̄} = conj M_{JĪ}`, exactly when its
square component matrix is Hermitian. -/
lemma conjT_eq_permT_swap_iff_isHermitian {a d : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d]) :
    S.conjT M = permT ![1, 0] (IsReindexing.swap_of_eq hbar.symm
      ((congrArg S.bar hbar).symm.trans (S.bar_involution a)).symm) M ↔
    (S.squareMatrixOf M hbar).IsHermitian := by
  subst hbar
  rw [squareMatrixOf, ← toMatrix_injective.eq_iff, toMatrix_conjT,
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

/-!

## G. Dual bases under conjugation

For a species with dual bases, `conj_contrComm` carries the δ law at a colour `d` to the δ law at
`bar d`. Over a nontrivial ring the matching satisfying the δ law is unique, so the matching at
`bar d` is the one at `d`, carried through `barIdx_eq` and `bar_tau`.

-/

open HasContrDualBases in
/-- The dual-label matching at `d`, carried to `bar d` through `barIdx_eq` and `bar_tau`, satisfies
the δ law at `bar d`. -/
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
/-- The label identification of a contraction commutes with conjugation: contracting `bar c1`
against `bar c2` matches the conjugates of the labels `c1` and `c2` match. -/
lemma dualIdxEquiv_bar [Nontrivial k] [HasContrDualBases S.toTensorSpecies] {c1 c2 : C}
    (h : S.τ c1 = c2) (h' : S.τ (S.bar c1) = S.bar c2) (x : basisIdx c1) :
    dualIdxEquiv h' (cast (S.barIdx_eq c1).symm x) =
      cast (S.barIdx_eq c2).symm (dualIdxEquiv h x) := by
  subst h
  rw [dualIdxEquiv_apply, dualIdxEquiv_apply,
    contrDualIdxEquiv_eq_of_isContrDualMatching (S.isContrDualMatching_bar c1)]
  simp only [basisIdxCongr, ← Equiv.cast_symm, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.cast_apply, cast_cast, cast_eq, Equiv.cast_refl, Equiv.refl_apply]

/-!

## H. The sesquilinear form of a tensor

A tensor `M : ![a, bar a]` defines the sesquilinear form `s, t ↦ M(t, s̄)` on one-slot tensors of
the dual colour: the bilinear map of `M` (`Tensor.toLinearMap₂`) with its arguments swapped and
`s` conjugated (`conjSingleT`), so the form is conjugate-linear in its first argument, as in
Mathlib. Conjugation is all this level adds. Its colour condition is `bar a = d`, next to the
duality condition `τ x = a` of the bilinear map; for a concrete species both hold by `rfl` and are
filled in, so the form of `M` on tensors of colour `x` is written `S.toSesqForm x M`. The matrix of
the form in the basis labelled by `a` through `dualIdxEquiv` is the transposed component matrix
of `M`.

`M` is Hermitian when this form is. For a sesquilinear form Mathlib calls this `LinearMap.IsSymm`,
`conj (B s t) = B t s`. Mathlib's bridges between forms and matrices identify it with
`Matrix.IsHermitian` of the square component matrix, and so with conjugation swapping the two slots
of `M`. Likewise `M` is positive-definite when its form is (`LinearMap.IsPosDef`).

-/

open HasContrDualBases
open scoped Matrix

/-- The sesquilinear form `s, t ↦ M(t, s̄)` of `M : ![a, bar a]` on one-slot tensors `s, t` of a
colour `x` dual to `a`. -/
def toSesqForm (x : C) {a d : C} (M : S.Tensor ![a, d]) (hbar : S.bar a = d := by rfl)
    (hx : S.τ x = a := by rfl) : S.Tensor ![x] →ₗ⋆[k] S.Tensor ![x] →ₗ[k] k :=
  (toLinearMap₂ x (S.bar x) M hx (by rw [← hbar, ← hx, S.bar_tau])).flip.comp (S.conjSingleT x)

/-- The matrix of `toSesqForm` in the basis of one-slot tensors labelled by `a` (through
`dualIdxEquiv`) is the transposed square component matrix of `M`. -/
lemma toMatrix₂_toSesqForm [HasContrDualBases S.toTensorSpecies] {x a d : C}
    (hbar : S.bar a = d) (hx : S.τ x = a) (M : S.Tensor ![a, d]) :
    LinearMap.toMatrix₂ ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx)))
        ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx)))
        (S.toSesqForm x M hbar hx) = (S.squareMatrixOf M hbar)ᵀ := by
  nontriviality k
  subst hbar
  have hy : S.τ (S.bar x) = S.bar a := by rw [← hx, S.bar_tau]
  ext i j
  have h := congrFun (congrFun (toMatrix₂_toLinearMap₂ hx hy M) j)
    (dualIdxEquiv hy (cast (S.barIdx_eq x).symm ((dualIdxEquiv hx).symm i)))
  rw [LinearMap.toMatrix₂_apply, Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    S.dualIdxEquiv_bar hx hy, Equiv.apply_symm_apply] at h
  rw [LinearMap.toMatrix₂_apply, toSesqForm, LinearMap.comp_apply, LinearMap.flip_apply,
    Module.Basis.reindex_apply, Module.Basis.reindex_apply, Equiv.symm_trans_apply,
    Equiv.symm_trans_apply, conjSingleT_basis, Matrix.transpose_apply, squareMatrixOf_apply]
  exact h

/-- The sesquilinear form of `M` is Hermitian (`LinearMap.IsSymm`) exactly when the square
component matrix of `M` is. -/
lemma isSymm_toSesqForm_iff_isHermitian [HasContrDualBases S.toTensorSpecies]
    {x a d : C} (hbar : S.bar a = d) (hx : S.τ x = a) (M : S.Tensor ![a, d]) :
    (S.toSesqForm x M hbar hx).IsSymm ↔ (S.squareMatrixOf M hbar).IsHermitian := by
  rw [LinearMap.isSymm_iff_isHermitian_toMatrix
    ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx))), toMatrix₂_toSesqForm,
    Matrix.isHermitian_transpose_iff]

/-- The sesquilinear form of `M` is Hermitian (`LinearMap.IsSymm`) exactly when conjugation swaps
the two slots of `M`, `M_{IJ̄} = conj M_{JĪ}`. -/
lemma isSymm_toSesqForm_iff_conjT_eq_permT [HasContrDualBases S.toTensorSpecies]
    {x a d : C} (hbar : S.bar a = d) (hx : S.τ x = a) (M : S.Tensor ![a, d]) :
    (S.toSesqForm x M hbar hx).IsSymm ↔ S.conjT M = permT ![1, 0] (IsReindexing.swap_of_eq hbar.symm
      ((congrArg S.bar hbar).symm.trans (S.bar_involution a)).symm) M := by
  rw [isSymm_toSesqForm_iff_isHermitian, conjT_eq_permT_swap_iff_isHermitian]

/-!

## I. Positive-definite tensors

-/

section PosDef

variable [PartialOrder k]

/-- The sesquilinear form of `M` is positive-definite (`LinearMap.IsPosDef`) exactly when the square
component matrix of `M` is. -/
lemma isPosDef_toSesqForm_iff_posDef [HasContrDualBases S.toTensorSpecies]
    {x a d : C} (hbar : S.bar a = d) (hx : S.τ x = a) (M : S.Tensor ![a, d]) :
    (S.toSesqForm x M hbar hx).IsPosDef ↔ (S.squareMatrixOf M hbar).PosDef := by
  rw [LinearMap.isPosDef_iff_posDef_toMatrix
    ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx))), toMatrix₂_toSesqForm,
    Matrix.PosDef.transpose_iff]

end PosDef

/-!

## J. The inverse of a nondegenerate tensor

### J.1. The inverse

The inverse of `M : ![a, bar a]` is the tensor at the dual colours `![τ (bar a), τ a]` whose
component matrix is the inverse of that of `M`. It is Hermitian when `M` is. When the component
matrix is invertible, contraction with `M` is injective, and the inverse is the two-sided inverse of
`M` under contraction (J.3), in the form of the hypotheses of `crossToSlotEquiv`.

-/

/-- The colours of the inverse are again a colour and its conjugate. -/
lemma bar_tau_of_bar {a d : C} (hbar : S.bar a = d) : S.bar (S.τ d) = S.τ a :=
  (S.bar_tau d).trans (congrArg S.τ ((congrArg S.bar hbar).symm.trans (S.bar_involution a)))

variable [HasContrDualBases S.toTensorSpecies]

/-- The inverse of `M : ![a, bar a]`, at the dual colours: its component matrix is the inverse of
the component matrix of `M`, labels carried across by `dualIdxEquiv`. It is zero when that matrix's
determinant is not a unit; the contraction laws assume `IsUnit` of the determinant. -/
def inverseT {a d : C} (M : S.Tensor ![a, d]) (hbar : S.bar a = d := by rfl) :
    S.Tensor ![S.τ d, S.τ a] :=
  fromMatrixT (S := S.toTensorSpecies) (S.τ d) (S.τ a)
    ((S.squareMatrixOf M hbar)⁻¹.submatrix
      (Equiv.cast (hbar ▸ S.barIdx_eq a) ∘ (dualIdxEquiv (rfl : S.τ d = S.τ d)).symm)
      (dualIdxEquiv (S.τ_τ_apply a)))

/-- The component matrix of the inverse is the inverse component matrix, relabelled. -/
lemma toMatrix_inverseT {a d : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d]) :
    toMatrix (S.inverseT M hbar) =
      (S.squareMatrixOf M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq a) ∘ (dualIdxEquiv (rfl : S.τ d = S.τ d)).symm)
        (dualIdxEquiv (S.τ_τ_apply a)) :=
  toMatrix_fromMatrixT _ _ _

/-- The labels of the two slots of the inverse, carried to the labels of `a`, agree: through the
conjugate-label identification and the dual matching at `τ a`, and through the dual matching at
`d`. -/
lemma dualIdxEquiv_cast_symm_eq [Nontrivial k] {a d : C} (hbar : S.bar a = d)
    (j : basisIdx (S.τ d)) :
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
  have h' := S.dualIdxEquiv_bar (rfl : S.τ a = S.τ a) (S.bar_tau a).symm x
  simp only [dualIdxEquiv_apply, basisIdxCongr, Equiv.cast_apply] at h' ⊢
  simpa only [← Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq] using
    congrArg (cast (S.barIdx_eq (S.τ a))) h'

/-- The square component matrix of the inverse is the inverse of that of `M`, with the labels of
`τ d` carried to those of `a` on both axes. -/
lemma squareMatrixOf_inverseT {a d : C} (hbar : S.bar a = d)
    (M : S.Tensor ![a, d]) :
    S.squareMatrixOf (S.inverseT M hbar) (S.bar_tau_of_bar hbar) =
      (S.squareMatrixOf M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq a) ∘ (dualIdxEquiv (rfl : S.τ d = S.τ d)).symm)
        (Equiv.cast (hbar ▸ S.barIdx_eq a) ∘ (dualIdxEquiv (rfl : S.τ d = S.τ d)).symm) := by
  nontriviality k
  rw [squareMatrixOf, toMatrix_inverseT, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_id]
  exact congrArg _ (funext (S.dualIdxEquiv_cast_symm_eq hbar))

/-- The inverse of a Hermitian tensor is Hermitian: if the sesquilinear form of `M` is Hermitian
(`LinearMap.IsSymm`), so is that of its inverse. -/
lemma isSymm_toSesqForm_inverseT {x y a d : C} (hbar : S.bar a = d)
    (hx : S.τ x = a) (hy : S.τ y = S.τ d) {M : S.Tensor ![a, d]}
    (hM : (S.toSesqForm x M hbar hx).IsSymm) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsSymm := by
  rw [isSymm_toSesqForm_iff_isHermitian] at hM ⊢
  rw [squareMatrixOf_inverseT]
  exact hM.inv.submatrix _

/-- Contraction with `M` is injective on rank-two tensors when the component matrix of `M` is
invertible. -/
lemma crossToEnd_right_injective {a d c : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d])
    (hM : IsUnit (S.squareMatrixOf M hbar).det) :
    Function.Injective (crossToEnd (Fin.last 1) (0 : Fin 2) rfl M (cB := ![S.τ d, c])) := by
  intro Q Q' h
  have h := congrArg toMatrixMap h
  -- `toMatrixMap_crossToEnd_pair` keys through the `Fin.append` colour list only with this option.
  set_option backward.isDefEq.respectTransparency false in
  rw [toMatrixMap_crossToEnd_pair (c1 := d) (c2 := S.τ d) rfl,
    toMatrixMap_crossToEnd_pair (c1 := d) (c2 := S.τ d) rfl,
    S.toMatrix_eq_submatrix_squareMatrixOf hbar M] at h
  set N := S.squareMatrixOf M hbar
  set β := Equiv.cast (hbar ▸ S.barIdx_eq a)
  -- Move the relabelling `β` across the product, then cancel `N` on the left.
  have key : ∀ Z : Matrix (basisIdx d) (basisIdx c) k,
      N.submatrix id β * Z = N * Z.submatrix β.symm id := fun Z => by
    simpa only [Matrix.submatrix_id_id] using Matrix.submatrix_id_mul_right N Z id β
  rw [key, key] at h
  have h2 := congrArg (fun X : Matrix (basisIdx a) (basisIdx c) k => N⁻¹ * X) h
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hM] at h2
  refine toMatrixMap_injective ?_
  ext z w
  simpa [toMatrix_apply] using congrFun (congrFun h2 (β ((dualIdxEquiv rfl).symm z))) w

end ConjTensorSpecies

/-!

### J.2. Over a field

Over a field, invertibility of the component matrix is nondegeneracy of the sesquilinear form,
which holds when the form is positive-definite (`LinearMap.IsPosDef.nondegenerate`). The inverse of
a positive-definite tensor is positive-definite.

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases

variable {k : Type} [Field k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- The sesquilinear form of `M` is nondegenerate exactly when its
component matrix is invertible. -/
lemma nondegenerate_toSesqForm_iff {x a d : C} (hbar : S.bar a = d) (hx : S.τ x = a)
    (M : S.Tensor ![a, d]) : (S.toSesqForm x M hbar hx).Nondegenerate ↔
      IsUnit (S.squareMatrixOf M hbar).det := by
  rw [LinearMap.nondegenerate_iff_isUnit_det_toMatrix₂
    ((basis ![x]).reindex (ComponentIdx.single.trans (dualIdxEquiv hx))), toMatrix₂_toSesqForm,
    Matrix.det_transpose]

section PosDef

variable [PartialOrder k]

/-- The inverse of a positive-definite tensor is positive-definite: if the sesquilinear form of `M`
is positive-definite (`LinearMap.IsPosDef`), so is that of its inverse. -/
lemma isPosDef_toSesqForm_inverseT {x y a d : C} (hbar : S.bar a = d) (hx : S.τ x = a)
    (hy : S.τ y = S.τ d) {M : S.Tensor ![a, d]} (hM : (S.toSesqForm x M hbar hx).IsPosDef) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsPosDef := by
  rw [isPosDef_toSesqForm_iff_posDef] at hM ⊢
  rw [squareMatrixOf_inverseT]
  exact hM.inv.submatrix ((Equiv.injective _).comp (Equiv.injective _))

end PosDef

end ConjTensorSpecies

/-!

### J.3. Over `RCLike` scalars

The unit tensor needs `RCLike` scalars, so the contraction laws and uniqueness of the inverse are
stated over `RCLike k`.

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases
open scoped Matrix

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- `M` contracted with its inverse is the unit tensor, when its component matrix is invertible. -/
lemma crossToEnd_inverseT {a d : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d])
    (hM : IsUnit (S.squareMatrixOf M hbar).det) :
    crossToEnd (Fin.last 1) (0 : Fin 2) rfl M (S.inverseT M hbar) =
      permT id (IsReindexing.unitTensor_pair (S := S.toTensorSpecies) (d := d)
        (S.τ_τ_apply a)) (unitTensor (S := S.toTensorSpecies) (S.τ a)) := by
  refine toMatrixMap_injective ?_
  have hMN := S.toMatrix_eq_submatrix_squareMatrixOf hbar M
  -- `toMatrixMap_crossToEnd_pair` keys through the `Fin.append` colour list only with this option,
  -- and the casts it leaves in the result are the ones the final index step cancels.
  set_option backward.isDefEq.respectTransparency false in
  rw [toMatrixMap_crossToEnd_pair (c1 := d) (c2 := S.τ d) rfl,
    toMatrixMap_permT_unitTensor (S := S.toTensorSpecies) (σ := id) (S.τ a) (fun _ => rfl),
    toMatrix_inverseT,
    Matrix.submatrix_submatrix]
  set N := S.squareMatrixOf M hbar
  have hr : (⇑(Equiv.cast (hbar ▸ S.barIdx_eq a)) ∘ ⇑(dualIdxEquiv (rfl : S.τ d = S.τ d)).symm) ∘
      ⇑(dualIdxEquiv (rfl : S.τ d = S.τ d)) = ⇑(Equiv.cast (hbar ▸ S.barIdx_eq a)) := by
    funext z
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hMN, hr, Function.comp_id, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hM]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, Matrix.one_apply]
  refine if_congr ?_ rfl rfl
  simp only [dualIdxEquiv_apply, basisIdxCongr, Equiv.cast_apply]
  constructor <;> rintro rfl <;> simp

/-- The inverse contracted with `M` is the unit tensor, when the component matrix of `M` is
invertible. -/
lemma crossToEnd_inverseT_left {a d : C} (hbar : S.bar a = d)
    (M : S.Tensor ![a, d])
    (hM : IsUnit (S.squareMatrixOf M hbar).det) :
    crossToEnd (Fin.last 1) (0 : Fin 2) (S.τ_τ_apply a) (S.inverseT M hbar) M =
      permT id (IsReindexing.unitTensor_pair (S := S.toTensorSpecies) (d := S.τ a)
        (rfl : S.τ d = S.τ d)) (unitTensor (S := S.toTensorSpecies) d) := by
  refine toMatrixMap_injective ?_
  have hMN := S.toMatrix_eq_submatrix_squareMatrixOf hbar M
  rw [toMatrixMap_crossToEnd_pair (c1 := S.τ a) (c2 := a) (S.τ_τ_apply a),
    toMatrixMap_permT_unitTensor (S := S.toTensorSpecies) (σ := id) d (fun _ => rfl),
    toMatrix_inverseT]
  set N := S.squareMatrixOf M hbar
  rw [hMN, Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id,
    Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hM]
  ext x y
  simp only [Matrix.submatrix_apply, Function.comp_apply, Matrix.one_apply]
  refine if_congr ?_ rfl rfl
  rw [EmbeddingLike.apply_eq_iff_eq]
  simp only [dualIdxEquiv, Equiv.symm_trans_apply, Equiv.symm_symm]
  rfl

/-- The inverse is unique: a tensor whose contraction with `M` is the unit tensor is
`inverseT M`, when the component matrix of `M` is invertible. -/
lemma eq_inverseT {a d : C} (hbar : S.bar a = d) (M : S.Tensor ![a, d])
    (hM : IsUnit (S.squareMatrixOf M hbar).det)
    {Q : S.Tensor ![S.τ d, S.τ a]}
    (hQ : crossToEnd (Fin.last 1) (0 : Fin 2) rfl M Q =
      permT id (IsReindexing.unitTensor_pair (S := S.toTensorSpecies) (d := d)
        (S.τ_τ_apply a)) (unitTensor (S := S.toTensorSpecies) (S.τ a))) :
    Q = S.inverseT M hbar :=
  S.crossToEnd_right_injective hbar M hM (hQ.trans (S.crossToEnd_inverseT hbar M hM).symm)

end ConjTensorSpecies
end
end
