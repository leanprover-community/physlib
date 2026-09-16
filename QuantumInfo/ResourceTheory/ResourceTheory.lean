/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
module

public import QuantumInfo.ResourceTheory.FreeState

@[expose] public section

/-- A quantum resource theory extends a `FreeStateTheory` with a collection of free operations. It is
required that any state we can always prepare for free must be free, and this is all then the resource
theory is "minimal", but we can have a more restricted set of operations. -/
class ResourceTheory (ι : Type*) extends FreeStateTheory ι where
  freeOps i j : Set (CPTPMap (H i) (H j))
  /-- Free operations in a ResourceTheory are nongenerating: they only create a free states from a free state. -/
  nongenerating {i j : ι} {f} (h : f ∈ freeOps i j) : ∀ ρ, IsFree ρ → IsFree (f ρ)
  --We might need to require some more closure properties on `freeOps`, like closure under tensor product...?
  --For now we just require that they include the identity and composition, so that we have at least a category.
  /-- The identity operation is free -/
  free_id i : CPTPOp.id ∈ freeOps i i
  /-- Free operations are closed under composition -/
  free_comp {i j k} (Y : freeOps j k) (X : freeOps i j) : Y.1.compose X.1 ∈ freeOps i k

/-- A `ResourceTheory` whose index type is also a `UnitalPretheory`, so that there is a unit
object `1` and the product `i * j` of objects. This is the setting in which tensoriality of the
free operations can be stated. -/
class UnitalResourceTheory (ι : Type*) extends ResourceTheory ι, UnitalPretheory ι

namespace ResourceTheory
open ResourcePretheory
open FreeStateTheory

variable {ι : Type*}

/-- Given a `FreeStateTheory`, there is a maximal set of free operations compatible with the free states.
That is the set of all operations that don't generate non-free states from free states. We
call this the maximal resource theory. -/
@[instance_reducible]
def maximal [FreeStateTheory ι] : ResourceTheory ι where
  freeOps i j := { f | ∀ ρ, IsFree ρ → IsFree (f ρ)}
  nongenerating := id
  free_id _ _ _ := by rwa [CPTPOp.id_MState]
  free_comp Y X ρ h := by
    rw [CPTPOp.compose_eq]
    exact Y.prop _ (X.prop ρ h)

/-- A resource theory `IsMaximal` if it includes all non-generating operations. -/
def IsMaximal (r : ResourceTheory ι) : Prop :=
  ∀ (i j), r.freeOps i j = { f | ∀ ρ, IsFree ρ → IsFree (f ρ)}

/-- A resource theory `IsTensorial` if it includes tensor products of operations, creating
free states, and discarding. This implies that includes a unit object. -/
structure IsTensorial [UnitalResourceTheory ι] : Prop where
  prod : ∀ {i j k l : ι} {f g}, f ∈ freeOps i k → g ∈ freeOps j l →
    (f ⊗ᶜᵖᵣ g) ∈ freeOps (i * j) (k * l)
  create : ∀ {i : ι} (ρ), IsFree ρ → CPTPOp.replacement ρ ∈ freeOps 1 i
  destroy : ∀ (i : ι), CPTPOp.destroy ∈ freeOps i 1

/-- The theory `ResourceTheory.maximal` always `IsMaximal`. -/
theorem maximal_IsMaximal [FreeStateTheory ι] : IsMaximal (maximal (ι := ι)) :=
  fun _ _ ↦ rfl

-- --Helper theorem for ResourceTheory.mk_of_ops
-- private lemma convex_states_of_convex_ops [ResourcePretheory ι] (O : ∀ (i j : ι), Set (CPTPMap (H i) (H j)))
--   (h_convex : ∀ {i j}, Convex ℝ (CPTPOp.choi '' O i j)) (i : ι) :
--     Convex ℝ (DensityOp.M '' fun ρ ↦ ∀ {j} σ, ∃ f, O j i f ∧ f σ = ρ) := by
--   intro _ hx _ hy a b ha hb hab
--   rw [Set.mem_image] at hx hy ⊢
--   obtain ⟨x,hx1,hx2⟩ := hx
--   obtain ⟨y,hy1,hy2⟩ := hy
--   use Mixable.mix_ab ha hb hab x y
--   constructor
--   · change forall _, _
--     intro j σ
--     obtain ⟨fx,⟨hfx1,hfx2⟩⟩ := hx1 σ
--     obtain ⟨fy,⟨hfy1,hfy2⟩⟩ := hy1 σ
--     use Mixable.mix_ab ha hb hab fx fy
--     constructor
--     · specialize h_convex ⟨fx, hfx1, rfl⟩ ⟨fy, hfy1, rfl⟩ ha hb hab
--       rw [Set.mem_image] at h_convex
--       obtain ⟨w,hw1,hw2⟩ := h_convex
--       have : w = Mixable.mix_ab ha hb hab fx fy := by
--         apply CPTPOp.choi_ext
--         convert hw2
--         --Should be a theorem
--         simp only [Mixable.mix_ab, Mixable.mkT]
--         exact CPTPOp.choi_of_CPTP_of_choi (a • fx.choi + b • fy.choi)
--       exact this ▸ hw1
--     · --Should be a theorem about CPTPOp.instMixable, really. Also, this proof is terrible.
--       subst x y
--       simp only [Mixable.mix_ab, Mixable.mkT, MState.instMixable, CPTPOp.instMFunLike,
--         CPTPOp.CPTP_of_choi_PSD_Tr, CPTPOp.mk, MatrixMap.of_choi_matrix, Mixable.to_U]
--       ext
--       change (Finset.sum _ _) = ((_ : ℂ) + _)
--       simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
--       simp_rw [mul_add, Finset.sum_add_distrib]
--       congr
--       · sorry
--       · sorry
--   · rw [Mixable.mix_ab, Mixable.mkT, MState.instMixable, ← hx2, ← hy2]
--     rfl

-- /-- A `ResourceTheory` can be constructed from a set of operations (satisfying appropriate axioms of closure),
-- and then the free states are taken to be the set of states that can be prepared from any initial state.
-- -/
-- def mk_of_ops [ResourcePretheory ι] (O : ∀ (i j : ι), Set (CPTPMap (H i) (H j)))
--     (h_id : ∀ i, CPTPOp.id ∈ O i i) --Operations include identity
--     (h_comp : ∀ {i j k} (Y : O j k) (X : O i j), Y.1.compose X.1 ∈ O i k) --Operations include compositions
--     (h_closed : ∀ {i j}, IsClosed (O i j)) -- Operations are topologically closed
--     (h_convex : ∀ {i j}, Convex ℝ (CPTPOp.choi '' O i j)) -- (The choi matrices of) operations are convex
--     (h_prod : ∀ {i j k l f g} (hf : f ∈ O i k) (hg : g ∈ O j l), (f ⊗ᶜᵖᵣ g) ∈ O (prod i j) (prod k l)) --Closed under products
--     (h_fullRank : ∀ {i : ι}, sorry) --Some statement about having full rank states as output
--     (h_appendFree : ∀ {i j k : ι}, sorry) --Some statement that appending free states is free
--     : ResourceTheory ι where
--   freeOps := O
--   free_id := h_id
--   free_comp := h_comp

--   IsFree {i} ρ := ∀ {j} σ, ∃ f, O j i f ∧ f σ = ρ
--   free_closed := sorry
--   free_convex {i} := convex_states_of_convex_ops O @h_convex i
--   free_prod {i j ρ σ} hρ hσ k ρ₀ := by
--     obtain ⟨f,hf1⟩ := hρ ρ
--     obtain ⟨g,hg⟩ := hσ σ
--     sorry
--   free_fullRank := sorry
--   nongenerating := by
--     intro i j f hf ρ hFree k σ
--     obtain ⟨g,hg1,hg2⟩ := hFree σ
--     use f.compose g
--     constructor
--     · exact h_comp ⟨f,hf⟩ ⟨g,hg1⟩
--     · simp only [CPTPOp.compose_eq, hg2]


-- /-- A `ResourceTheory` provides a category structure -/
-- instance instQRTCategory (ι : Type*) [ResourceTheory ι] : CategoryTheory.Category ι where
--   Hom x y := freeOps x y
--   id := fun _ ↦ ⟨CPTPOp.id, free_id _⟩
--   comp f g := ⟨CPTPOp.compose g.1 f.1, free_comp g f⟩
--   id_comp X := by simp
--   comp_id := by simp
--   assoc := fun f g h ↦ by simpa using CPTPOp.compose_assoc h.1 g.1 f.1

-- open ComplexOrder in
-- /-- The 'fully free' quantum resource theory: the category is all finite Hilbert spaces, all maps are
-- free and all states are free. Marked noncomputable because we use `Fintype.ofFinite`. -/
-- noncomputable def fullyFreeQRT : ResourceTheory { ι : Type // Finite ι ∧ Nonempty ι} where
--     H := Subtype.val
--     FinH := fun i ↦ have := i.prop.left; Fintype.ofFinite i
--     DecEqH := fun i a b ↦ Classical.propDecidable (a = b)
--     NonemptyH := fun i ↦ i.prop.right

--     prod := fun ⟨i,⟨hi,hi2⟩⟩ ⟨j,⟨hj,hj2⟩⟩ ↦ ⟨i × j, ⟨Finite.instProd, instNonemptyProd⟩⟩
--     prodEquiv := fun ⟨_,⟨_,_⟩⟩ ⟨_,⟨_,_⟩⟩ ↦ Equiv.refl _

--     IsFree := Set.univ
--     free_closed := isClosed_univ
--     free_convex {i} := by
--       -- convert MState.convex (H i) --For DensityOp.m, not DensityOp.M
--       sorry
--     free_prod _ _ := trivial
--     free_fullRank := by
--       intro i
--       have := i.prop.left
--       have := i.prop.right
--       let _ := Fintype.ofFinite i
--       let _ : DecidableEq i := fun _ _ ↦ Classical.propDecidable _
--       use MState.uniform --use the fully mixed state
--       --The fact that the fully mixed state is PosDef should be stated somewhere else... TODO
--       suffices Matrix.PosDef (@MState.uniform (d := i.val) _ _ this).M.toMat by
--         change _ ∧ True
--         rw [and_true]
--         exact this
--       simp only [MState.uniform, MState.ofClassical, Distribution.uniform_def, Set.univ]
--       classical apply Matrix.PosDef.diagonal
--       intro
--       rw [Finset.card_univ, one_div, Complex.ofReal_inv]
--       exact RCLike.inv_pos_of_pos (Nat.cast_pos'.mpr Fintype.card_pos)

--     freeOps _ _ := Set.univ
--     nongenerating _ _ _ := trivial
--     free_id := Set.mem_univ
--     free_comp _ _ := Set.mem_univ _

-- end ResourceTheory
