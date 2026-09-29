/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basis
public import Physlib.Mathematics.ConjModule

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
conjugate colour. It rests on the conjugate module `ConjModule` (`Physlib.Mathematics.ConjModule`),
the same vectors with the scalar action twisted by conjugation (`i` acts as `−i`). Equipping the
conjugate colours with such conjugate-module carriers is what makes a metric `V c ⊗ V (bar c) → k`
genuinely bilinear and `IsHermitian` an honest conjugate-transpose.

## ii. Key results

- `ConjTensorSpecies` is a tensor species bundled with its conjugation.
- `ConjTensorSpecies.conjT` is the conjugation of a tensor.
- `ConjTensorSpecies.conjT_conjT` proves that conjugation is an involution.
- `ConjTensorSpecies.conjT_contrT` proves that conjugation commutes with contraction.
- `ConjTensorSpecies.conjT_eq_permT_iff` is the componentwise criterion for
  `conjT t = permT σ h t'`, the workhorse for proving reality and Hermiticity conditions.
- `ConjTensorSpecies.conjEquiv` is the single-slot conjugate-linear isomorphism `V c ≃ₛₗ V (bar c)`.
- `ConjTensorSpecies.IsHermitian` is the structural conjugate-transpose condition on a metric slot.

## iii. Table of contents

- A. The conjugation structure
- B. The conjugation of vectors
- C. Conjugation of tensors
- D. The involution law
- E. Commutation with contraction
- F. Hermitian pairings

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

TODO "Extend `complexLorentzTensor` to a  `ConjTensorSpecies`."
TODO "Extend `realLorentzTensor` to a `ConjTensorSpecies`."
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
  erw [← componentMap_eq_repr (S.bar ∘ c), componentMap_conjT, componentMap_eq_repr c t,
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

-/

open scoped TensorProduct in
/-- A pairing `g : V c ⊗ V (bar c) → k` is Hermitian when conjugating and swapping its two slots
via `conjEquiv` returns its `star`: `g (x ⊗ y) = star (g (conjEquiv.symm y ⊗ conjEquiv x))`. -/
def IsHermitian {c : C} (g : V c ⊗[k] V (S.bar c) →ₗ[k] k) : Prop :=
  ∀ (x : V c) (y : V (S.bar c)),
    g (x ⊗ₜ[k] y) = star (g (S.conjEquiv.symm y ⊗ₜ[k] S.conjEquiv x))

end ConjTensorSpecies
end
end
