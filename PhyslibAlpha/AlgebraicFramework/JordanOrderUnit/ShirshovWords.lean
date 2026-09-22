/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Fin.Basic

/-!
# Alternating-block words in two letters

Infrastructure for formalizing A.I. Shirshov's proof that the free Jordan algebra on two
generators is special (`On special J-rings`, Mat. Sbornik 38 (1956), 149–166; English translation
by M.R. Bremner and M.V. Kochetov in *Selected Works of A.I. Shirshov*, Birkhäuser, 2009).

Shirshov's proof works with associative words in two letters `a`, `b`, organized by their
**height**: `aˢ`/`bʳ` have height 1, `aˢbʳ`/`bʳaˢ` have height 2, and in general a word
`a^{n₁}b^{m₁}a^{n₂}b^{m₂}⋯` (or the same starting with `b`) has height equal to its number
of maximal same-letter blocks. Rather than recovering this block structure from a raw
`List (Fin 2)` by a run-length-encoding pass (needing its own correctness lemmas before anything
else can start), a word is represented *directly* as its block list: an alternating list of
`(letter, positive multiplicity)` pairs, `BWord`. This is the same data with none of the
decoding work, since every construction in Shirshov's paper builds words block-by-block already.

## Main definitions

- `BWord` : an associative word in the letters `Fin 2`, as an alternating list of
  `(letter, positive run length)` pairs.
- `BWord.height` : the number of blocks, `Shirshov`'s notion of height.
- `BWord.bar` : Shirshov's reduction `α ↦ ᾱ` (his overline, defined just before his equation
  (5)): peel the trailing block off and move it to the front, merging it into the new front
  block if the two share a letter. **Not an involution** and **not full word-reversal** — it
  strictly drops height on words of height `≥ 3`, which is exactly what makes it usable as the
  base case
  of a recursion on height in Shirshov's construction of the `*`-map (his equation (5), not yet
  formalized here).

-/

@[expose] public section

/-- An associative word in two letters, represented directly by its block decomposition: an
alternating list of `(letter, positive multiplicity)` pairs. Two consecutive blocks are required
to carry different letters (`chain'`) and every multiplicity is positive (`pos`) — together these
say the list really is the block decomposition of *some* word, not an arbitrary list of pairs. -/
structure BWord where
  /-- The blocks `(d₁,m₁), (d₂,m₂), …` represent the word `d₁^m₁ d₂^m₂ ⋯`. -/
  blocks : List (Fin 2 × ℕ)
  /-- Every block has positive multiplicity. -/
  pos : ∀ p ∈ blocks, 0 < p.2
  /-- Consecutive blocks carry different letters. -/
  chain : blocks.IsChain (fun p q => p.1 ≠ q.1)

namespace BWord

/-- Two `BWord`s are equal iff their block lists are equal: the side conditions are `Prop`s. -/
@[ext] theorem ext {w₁ w₂ : BWord} (h : w₁.blocks = w₂.blocks) : w₁ = w₂ := by
  cases w₁; cases w₂; congr

/-- **Shirshov's height**: the number of maximal same-letter blocks. Words `aˢ`/`bʳ` (a single
block) have height 1; `aˢbʳ`/`bʳaˢ` have height 2; and so on. -/
def height (w : BWord) : ℕ := w.blocks.length

/-- **Shirshov's total degree**: the word's length as a string in `a`, `b`, i.e. the sum of all
block multiplicities. -/
def degree (w : BWord) : ℕ := (w.blocks.map Prod.snd).sum

/-- The single-block word consisting of `m` copies of the letter `d`. Undefined (well, defined but
not a genuine `BWord` witness) unless `m > 0`; callers supply the positivity proof. -/
def ofRun (d : Fin 2) (m : ℕ) (hm : 0 < m) : BWord where
  blocks := [(d, m)]
  pos p hp := by simp only [List.mem_singleton] at hp; simpa [hp] using hm
  chain := List.isChain_singleton _

@[simp] theorem ofRun_blocks (d : Fin 2) (m : ℕ) (hm : 0 < m) :
    (ofRun d m hm).blocks = [(d, m)] := rfl

@[simp] theorem height_ofRun (d : Fin 2) (m : ℕ) (hm : 0 < m) : (ofRun d m hm).height = 1 := rfl

/-- The empty word (degree 0, height 0). Not part of Shirshov's `S` (his words are nonempty), but
a convenient junk value for total recursive functions below. -/
instance : Inhabited BWord := ⟨⟨[], by simp, List.isChain_nil⟩⟩

/-- Prepend a block to a `BWord`'s block list, merging it into the existing front block if they
share a letter, and otherwise consing it on. This is exactly the list-level operation `bar` needs
at its one possible merge point (see the module docstring): the *only* place a merge can happen
when moving a trailing block to the front is between the newly-moved block and the old front
block, since the rest of the list is already alternating. -/
def consMerge (d : Fin 2) (m : ℕ) (_hm : 0 < m) (rest : List (Fin 2 × ℕ)) :
    List (Fin 2 × ℕ) :=
  match rest with
  | [] => [(d, m)]
  | (d', m') :: tl => if d = d' then (d, m + m') :: tl else (d, m) :: rest

theorem chain_consMerge {d : Fin 2} {m : ℕ} (hm : 0 < m) {rest : List (Fin 2 × ℕ)}
    (hrest : rest.IsChain (fun p q => p.1 ≠ q.1)) :
    (consMerge d m hm rest).IsChain (fun p q => p.1 ≠ q.1) := by
  rcases rest with _ | ⟨⟨d', m'⟩, tl⟩
  · simp only [consMerge]; exact List.isChain_singleton (d, m)
  · simp only [consMerge]
    split_ifs with hd
    · obtain ⟨h1, h2⟩ := List.isChain_cons.mp hrest
      exact List.isChain_cons.mpr ⟨by simpa [hd] using h1, h2⟩
    · exact hrest.cons_of_ne_nil (List.cons_ne_nil _ _) hd

theorem pos_consMerge {d : Fin 2} {m : ℕ} (hm : 0 < m) {rest : List (Fin 2 × ℕ)}
    (hpos : ∀ p ∈ rest, 0 < p.2) :
    ∀ p ∈ consMerge d m hm rest, 0 < p.2 := by
  rcases rest with _ | ⟨⟨d', m'⟩, tl⟩
  · simpa [consMerge] using hm
  · simp only [consMerge]
    split_ifs with hd
    · intro p hp
      rw [List.mem_cons] at hp
      rcases hp with hp | hp
      · simp [hp]; omega
      · exact hpos p (List.mem_cons_of_mem _ hp)
    · intro p hp
      rw [List.mem_cons] at hp
      rcases hp with hp | hp
      · simpa [hp] using hm
      · exact hpos p hp

/-- Every block of `w.blocks.dropLast` is a block of `w.blocks`. -/
theorem pos_dropLast (w : BWord) : ∀ p ∈ w.blocks.dropLast, 0 < p.2 :=
  fun p hp => w.pos p (List.dropLast_subset _ hp)

/-- The initial segment of a `BWord`'s block list is itself a valid (alternating) block list:
dropping the last block cannot break the alternation of what remains. -/
theorem chain_dropLast (w : BWord) :
    w.blocks.dropLast.IsChain (fun p q => p.1 ≠ q.1) := by
  by_cases he : w.blocks = []
  · simp [he]
  · have happ := List.dropLast_append_getLast (l := w.blocks) he
    have hchain := w.chain
    rw [← happ] at hchain
    exact (List.isChain_append.mp hchain).1

/-- **Shirshov's reduction `α ↦ ᾱ`**, defined just before his equation (5): if `w` has height
`≤ 1` it is unchanged; otherwise the trailing block is peeled off and moved to the front, merging
with the (new) front block if they share a letter. Non-increasing on height, and in fact
strictly height-decreasing on words of height `≥ 3` (not proved here) — hence usable as a
recursion measure. **Not** an involution and **not** full word-reversal (module docstring). -/
def bar (w : BWord) : BWord :=
  if h : w.blocks.length ≤ 1 then w
  else
    have hne : w.blocks ≠ [] := fun he => by simp [he] at h
    let last := w.blocks.getLast hne
    ⟨consMerge last.1 last.2 (w.pos last (List.getLast_mem hne)) w.blocks.dropLast,
      pos_consMerge _ (pos_dropLast w), chain_consMerge _ (chain_dropLast w)⟩

@[simp] theorem bar_of_height_le_one {w : BWord} (h : w.blocks.length ≤ 1) : bar w = w := by
  simp [bar, h]

/-- The block count of `consMerge`'s output is either the same as, or exactly one less than, the
block count of `rest` plus one (merging drops it by one, consing keeps it). -/
theorem length_consMerge_le {d : Fin 2} {m : ℕ} (hm : 0 < m) (rest : List (Fin 2 × ℕ)) :
    (consMerge d m hm rest).length ≤ rest.length + 1 := by
  rcases rest with _ | ⟨⟨d', m'⟩, tl⟩
  · simp [consMerge]
  · simp only [consMerge]
    split_ifs with hd <;> simp

/-- **`bar` never increases height.** Combined with the strict decrease on height `≥ 3` (not yet
needed and not proved here — the recursive `*`-map only needs non-strict monotonicity along with
the height-1/height-2 base cases), this is the basic sanity fact making `bar` usable as a
recursive-call argument. -/
theorem height_bar_le (w : BWord) : (bar w).height ≤ w.height := by
  unfold height bar
  split_ifs with h
  · exact le_refl _
  · have hne : w.blocks ≠ [] := fun he => by simp [he] at h
    have hpos : 0 < w.blocks.length := List.length_pos_iff.mpr hne
    have hlen : w.blocks.dropLast.length + 1 = w.blocks.length := by
      rw [List.length_dropLast]; omega
    calc (consMerge (w.blocks.getLast hne).1 (w.blocks.getLast hne).2
          (w.pos _ (List.getLast_mem hne)) w.blocks.dropLast).length
        ≤ w.blocks.dropLast.length + 1 := length_consMerge_le _ _
      _ = w.blocks.length := hlen

end BWord
