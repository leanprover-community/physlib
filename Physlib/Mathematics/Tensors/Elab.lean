/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Inverse
public import Physlib.Mathematics.Tensors.Tensorial
/-!

# Index notation

Tensor expressions with named indices, such as `{T | μ ν ⊗ U | ν ρ}ᵀ` for `T^μ_ν U^ν_ρ`.

## i. Overview

A tensor `T` of a species `S` with colors `![c₀, …, cₙ₋₁]` is written `T | μ₀ … μₙ₋₁`, one name
per slot. The heights of the indices are not written, since the colors fix them. A real Lorentz
tensor `T : S.Tensor ![⟨vec, up⟩, ⟨vec, down⟩]`, with components `T^μ_ν`, is written `T | μ ν`.

An expression `{…}ᵀ` is a tensor in `S.Tensor ![…]`, or a proposition if it is an equation. The
names are bound only inside the braces. Each construct is an operation of the species.

- `A ⊗ B` is `S.tmulEquiv _ _ (A ⊗ₜ B)`.
- A name written twice in a product is contracted. All pairs of the product are contracted in one
  `Tensor.contr σ`, with the relabeling `σ` generated from the names. The two slots of a pair must
  have dual colors, and the first one written is the first argument of `S.contr`.
- The free indices are numbered `0, 1, …` in the order written. The result is a tensor on `Fin m`
  with a literal color list `![…]`.
- `A + B` and `A = B` relabel `B` by `S.reindex` when its names come in another order. Each name
  must have the same color on both sides.
- `↓μ` lowers an upper index and `↑μ` raises a lower one, by `S.toDualAt`, so `{v | ↓ν}ᵀ` is
  `v_ν = v^μ g_μν`. This needs an instance `S.HasForm` at the kind of the slot, and a visible
  variance, as in `⟨κ, .up⟩`.
- A term `m : M` with an instance `Tensorial S c M`, such as a Lorentz vector, is read as
  `Tensorial.toTensor m`.
- Scalars, group elements and negatives are ordinary terms in front of `|`, as in `r • T | μ ν`,
  `Λ • T | μ ν` and `-T | μ ν`. A compound expression is scaled by nesting it, as in
  `r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ`. The form `-(T | μ ν)` is a parse error.

Parentheses, each side of a sum and a nested `{…}ᵀ` are contracted before they enter an enclosing
product, so the names they contract are free again outside. Thus `{(T | μ μ) ⊗ U | μ ρ}ᵀ` is
`(T^λ_λ) U^μ_ρ`. Within one product a name appears at most twice.

When the expected type is known, the result is fitted to it. On a tensor type with other slots,
such as `Fin 1 ⊕ Fin 1` for `Fin 2`, the free indices are placed on those slots in the order
written. On a type `M` with an instance `Tensorial S c M`, the result is read back by
`Tensorial.toTensor.symm`. So `({v | ↓μ}ᵀ : CoVector d)` is the covector `v_μ`, and
`({x | μ ⊗ y | ν}ᵀ : Vector d ⊗ Vector d)` is `x ⊗ₜ y`.

Every tensor needs literal slots and colors. Its slot type is built from `Fin n` and `⊕` with a
literal `n`, and its colors are a literal list `![a, b, …]` or `prodColors` of such lists. General
lemmas over a variable color family are therefore stated without the notation. A tensor `s` with
no slots is written `s |` with a space after the bar, since Mathlib reads `|x|` as an absolute
value.

For an upper color `c`, the inverse forms `g^μν g_νρ = δ^μ_ρ` are written
`{S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ`, which is
`contr_formTensor_formTensor` (section C).

## ii. Key results

- `{…}ᵀ` : index notation, elaborated by `elabTensorIndex`.
- `tensor_components` : reduces an equation of tensors to an equation of their components.
- `tensor_regroup` : proves an equation of two sums of contractions of the same factors, grouped
  or ordered differently, with the same signs and scalars.
- `tensor_slots` : proves an equation of two chains of lowerings and raisings of the same tensor.

## iii. Table of contents

- A. Syntax
- B. Elaboration
  - B.1. Slot types
  - B.2. The steps of an expression
  - B.3. The elaborator
  - B.4. Components
  - B.5. Regrouping contractions
  - B.6. Chains of lowerings and raisings
- C. Examples

## iv. References

-/

public meta section

open Lean Meta Elab Term

namespace Tensors.Notation

/-!

## A. Syntax

-/

/-- An index of a tensor in index notation. -/
declare_syntax_cat tensorIndex
/-- A named index. -/
syntax ident : tensorIndex
/-- A named upper index lowered with the invariant form, as `v_μ` from `v^μ`. -/
syntax "↓" ident : tensorIndex
/-- A named lower index raised with the invariant form, as `α^μ` from `α_μ`. -/
syntax "↑" ident : tensorIndex

/-- A tensor expression in index notation. -/
declare_syntax_cat tensorIndexExpr
/-- A tensor with a name on each slot. -/
syntax term "|" (ppSpace tensorIndex)* : tensorIndexExpr
/-- An equation. -/
syntax:40 tensorIndexExpr "=" tensorIndexExpr:41 : tensorIndexExpr
/-- A product. -/
syntax:70 tensorIndexExpr "⊗" tensorIndexExpr:71 : tensorIndexExpr
/-- A sum. -/
syntax:65 tensorIndexExpr "+" tensorIndexExpr:66 : tensorIndexExpr
/-- Parentheses. -/
syntax "(" tensorIndexExpr ")" : tensorIndexExpr

/-- Index notation. -/
syntax (name := tensorIndexSyntax) "{" tensorIndexExpr "}ᵀ" : term

/-!

## B. Elaboration

### B.1. Slot types

-/

/-- A slot type built from `Fin n`, `Unit` and `⊕`. Its slots are numbered `0, 1, …` in order. -/
inductive Slots where
  /-- `Fin n`. -/
  | fin (n : Nat)
  /-- `Unit`. -/
  | unit
  /-- `a ⊕ b`. -/
  | sum (a b : Slots)
deriving BEq

/-- The number of slots. -/
def Slots.size : Slots → Nat
  | .fin n => n
  | .unit => 1
  | .sum a b => a.size + b.size

/-- The slot type as a term. -/
def Slots.type : Slots → TermElabM Term
  | .fin n => `(Fin $(quote n))
  | .unit => `(Unit)
  | .sum a b => do `($(← a.type) ⊕ $(← b.type))

/-- The slot number `i` as a term. -/
def Slots.elem : Slots → Nat → TermElabM Term
  | .fin n, i => `(($(quote i) : Fin $(quote n)))
  | .unit, _ => `(())
  | .sum a b, i =>
    if i < a.size then do `(Sum.inl $(← a.elem i)) else do `(Sum.inr $(← b.elem (i - a.size)))

/-- The function on a slot type taking the values `vs` in slot order, built from vector literals on
`Fin n`, constants on `Unit` and `comb` on `⊕`. -/
def Slots.fn (comb : Name) : Slots → List Term → TermElabM Term
  | .fin _, vs => `(![$(vs.toArray),*])
  | .unit, vs => `(fun _ : Unit => $(vs[0]!))
  | .sum a b, vs => do
    `($(mkIdent comb) $(← a.fn comb (vs.take a.size)) $(← b.fn comb (vs.drop a.size)))

/-- The slot type of a type built from `Fin n` and `⊕` with a literal `n`. -/
partial def Slots.ofType? (ι : Expr) : MetaM (Option Slots) := do
  let ι ← whnfR ι
  if ι.isAppOfArity ``Fin 1 then
    return (← (evalNat ι.appArg!).run).map .fin
  else if ι.isAppOfArity ``Sum 2 then
    let some a ← Slots.ofType? (ι.getArg! 0) | return none
    let some b ← Slots.ofType? (ι.getArg! 1) | return none
    return some (.sum a b)
  else return none

/-- The bijection from `dom` to `cod` sending the slot `pre[j]` of `dom` to the slot `j` of `cod`.
The list `pre` names every slot of `dom` once. The inverse laws are proved slot by slot by
`fin_cases`. -/
def slotEquiv (dom cod : Slots) (pre : List Nat) : TermElabM Term := do
  let toFun ← dom.fn ``Sum.elim (← (List.range dom.size).mapM fun i => cod.elem (pre.idxOf i))
  let invFun ← cod.fn ``Sum.elim (← pre.mapM dom.elem)
  -- `decide` would need a `DecidableEq` instance on the whole slot type, which exceeds the
  -- instance size limit from four contracted pairs on.
  `((Equiv.mk $toFun $invFun (by intro x; fin_cases x <;> rfl)
      (by intro x; fin_cases x <;> rfl) : $(← dom.type) ≃ $(← cod.type)))

/-- The entries of a literal color family `![a, b, …]`, or of `prodColors` of literal families. -/
partial def colorList? (c : Expr) : MetaM (Option (List Expr)) := do
  if c.isAppOfArity ``Tensors.prodColors 5 then
    return (· ++ ·) <$> (← colorList? (c.getArg! 3)) <*> (← colorList? (c.getArg! 4))
  let (cs, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit 0) c
  return if tail.isAppOfArity ``Matrix.vecEmpty 1 then some cs else none

/-- The literal color family `![a, b, …]`. -/
def colorsTerm (cs : List Expr) : TermElabM Term := do
  `(![$((← cs.toArray.mapM exprToSyntax)),*])

/-!

### B.2. The steps of an expression

-/

/-- A partly elaborated expression, with the name and color of each slot, its slot type, its tensor
and its species. -/
structure Node where
  /-- The index name of each slot. -/
  names : List Name
  /-- The color of each slot. -/
  colors : List Expr
  /-- The slot type. -/
  slots : Slots
  /-- The tensor. -/
  tm : Term
  /-- The species. -/
  species : Expr

/-- The tensor of `a` relabeled onto `Fin pre.length` with the colors `cs`, its slot `pre[j]`
becoming the slot `j`. -/
def Node.reindex (a : Node) (pre : List Nat) (cs : List Expr) : TermElabM Term := do
  `(Tensors.Species.reindex $(← exprToSyntax a.species)
    (Tensors.ColorEquiv.mk (c₂ := $(← colorsTerm cs)) $(← slotEquiv a.slots (.fin pre.length) pre))
    $a.tm)

/-- The expression relabeled to `Fin n`, its slots numbered in order. -/
def Node.toFin (a : Node) : TermElabM Node := do
  let n := a.names.length
  if a.slots == .fin n then return a
  return { a with slots := .fin n, tm := ← a.reindex (List.range n) a.colors }

/-- The tensor `T | i₁ i₂ …` with its slots named, lowered at each `↓μ` and raised at each `↑μ`. -/
def leaf (T : Term) (idxs : Array (TSyntax `tensorIndex)) : TermElabM Node := do
  let mut e ← instantiateMVars (← elabTerm T none)
  if e.hasSyntheticSorry then throwAbortTerm
  let mut ty ← whnfR (← instantiateMVars (← inferType e))
  if ty.isMVar then
    throwError "index notation: the type of {T} is not known; give it, as `({T} : S.Tensor ![…])`"
  unless ty.isAppOf ``Tensors.Species.Tensor do
    -- Not a tensor: read it through its `Tensorial` instance, if it has one.
    try
      e ← withoutErrToSorry do
        let e ← elabTerm (← `(Tensors.Tensorial.toTensor $(← exprToSyntax e))) none
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      ty ← whnfR (← instantiateMVars (← inferType e))
    catch ex =>
      throwError "index notation: {T} is not a tensor and has no `Tensorial` instance:\n\
        {ex.toMessageData}"
  let args := ty.getAppArgs
  let some slots ← Slots.ofType? args[args.size - 2]!
    | throwError "index notation: the slots of {T} must be `Fin n` and `⊕`"
  let some colors ← colorList? args[args.size - 1]!
    | throwError "index notation: the colors of {T} must be a literal list"
  unless colors.length = idxs.size do
    throwError "index notation: {T} has {colors.length} slots, {idxs.size} indices given"
  -- Each index with whether its slot moves to the dual color, after checking the arrow.
  let kinds ← (idxs.toList.zip colors).mapM fun (i, col) => do
    let isUp ← whnfD (← mkAppM ``Tensors.Variance.isUp #[← mkAppM ``Tensors.Color.variance #[col]])
    let check (x : Ident) (up : Bool) (arrow : String) : TermElabM (Name × Bool) := do
      unless isUp.isConstOf (if up then ``Bool.true else ``Bool.false) do
        throwError "index notation: {arrow}{x.getId} needs a visibly \
          {if up then "upper" else "lower"} index"
      pure (x.getId, true)
    match i with
    | `(tensorIndex| $x:ident) => pure (x.getId, false)
    | `(tensorIndex| ↓$x:ident) => check x true "↓"
    | `(tensorIndex| ↑$x:ident) => check x false "↑"
    | _ => throwError "index notation: unsupported index {i}"
  let mut a : Node := ⟨kinds.map (·.1), colors, slots, ← exprToSyntax e, args[args.size - 3]!⟩
  if kinds.all (!·.2) then return a
  a ← a.toFin
  let n := colors.length
  for ((_, d), i) in kinds.zipIdx do
    if d then
      let colors := a.colors.set i (← mkAppM ``Tensors.Color.dual #[a.colors[i]!])
      -- The color `col` of the slot is passed explicitly, so the form is found at the kind of
      -- `col` and every lowering at that kind uses the same instance. The proofs `c i = col` and
      -- `c' i = col.dual` are `id rfl`, since a bare `rfl` has the type `c' i = c' i`, which
      -- `rw` matches only after unfolding `![…] i`. Away from `i` the colors agree by cases.
      let sp ← exprToSyntax a.species
      let col ← exprToSyntax a.colors[i]!
      let tm ← `(Tensors.Species.toDualAt $sp (c' := $(← colorsTerm colors))
        ($(quote i) : Fin $(quote n)) $col (id rfl) (id rfl)
        (by intro x hx; fin_cases x <;> first | rfl | exact absurd rfl hx) $a.tm)
      a := { a with colors, tm }
  return a

/-- Contracts every repeated name in one `Tensor.contr`, and numbers the free slots in the order
written. -/
def contract (a : Node) : TermElabM Node := do
  let idx := a.names.zipIdx
  let mut free : List Nat := []
  let mut pairs : List (Nat × Nat) := []
  for (nm, i) in idx do
    match idx.filter (·.1 == nm) with
    | [_] => free := free ++ [i]
    | [(_, i₁), (_, i₂)] =>
      if i == i₁ then
        unless ← isDefEq a.colors[i₂]! (← mkAppM ``Tensors.Color.dual #[a.colors[i₁]!]) do
          throwError "index notation: {nm} joins the colors {a.colors[i₁]!} and \
            {a.colors[i₂]!}, which are not dual"
        pairs := pairs ++ [(i₁, i₂)]
    | _ => throwError "index notation: {nm} appears more than twice"
  if pairs.isEmpty then return ← a.toFin
  let m := free.length
  -- The pairs are labeled by `Unit` for one pair, as in `ColorEquiv.matMul`, and by
  -- `(… ⊕ Unit) ⊕ Unit` for more, as `ColorEquiv.chain` combines two contractions in sequence.
  let J := (List.range (pairs.length - 1)).foldl (fun J _ => Slots.sum J .unit) .unit
  -- The free slots go to `inl k`, the first slot of the pair `j` to `inr (inl j)` and its second
  -- slot to `inr (inr j)`.
  let σ ← slotEquiv a.slots (.sum (.fin m) (.sum J J))
    (free ++ pairs.map (·.1) ++ pairs.map (·.2))
  let pairColors ← J.fn ``Tensors.prodColors (← pairs.mapM fun (i, _) => exprToSyntax a.colors[i]!)
  let tm ← `(Tensors.Species.Tensor.contr (S := $(← exprToSyntax a.species))
    (Tensors.ColorEquiv.mk
      (c₂ := Tensors.contrColors $(← colorsTerm (free.map (a.colors[·]!))) $pairColors) $σ)
    $a.tm)
  return ⟨free.map (a.names[·]!), free.map (a.colors[·]!), .fin m, tm, a.species⟩

/-- The right side relabeled to the order of the left side's names, after checking that each name
has the same color on both sides. -/
def reorder (l r : Node) : TermElabM Term := do
  unless l.names.length == r.names.length && l.names.all (r.names.contains ·) do
    throwError "index notation: the two sides have different free indices"
  for (nm, c) in r.names.zip r.colors do
    let c' := l.colors[l.names.idxOf nm]!
    unless ← isDefEq c c' do
      throwError "index notation: {nm} has the color {c'} on the left and {c} on the right"
  if l.names == r.names then return r.tm
  r.reindex (l.names.map r.names.idxOf) l.colors

/-!

### B.3. The elaborator

-/

mutual

/-- An expression before its outer contraction. A product `A ⊗ B` is `S.tmulEquiv _ _ (A ⊗ₜ B)`,
its repeated names not yet contracted. Parentheses and each side of a sum are contracted first. -/
partial def uncontracted (stx : Syntax) : TermElabM Node := do
  match stx with
  | `(tensorIndexExpr| $T:term | $ids:tensorIndex*) => leaf T ids
  | `(tensorIndexExpr| $a:tensorIndexExpr ⊗ $b:tensorIndexExpr) => do
    let a ← uncontracted a
    let b ← uncontracted b
    let tm ← `(Tensors.Species.tmulEquiv $(← exprToSyntax a.species) _ _
      (TensorProduct.tmul _ $a.tm $b.tm))
    return ⟨a.names ++ b.names, a.colors ++ b.colors, .sum a.slots b.slots, tm, a.species⟩
  | `(tensorIndexExpr| ($a:tensorIndexExpr)) => build a
  | `(tensorIndexExpr| $a:tensorIndexExpr + $b:tensorIndexExpr) => do
    let l ← build a
    return { l with tm := ← `($l.tm + $(← reorder l (← build b))) }
  | `(tensorIndexExpr| $_:tensorIndexExpr = $_:tensorIndexExpr) =>
    throwError "index notation: an equation is allowed only at the top"
  | _ => throwError "index notation: unsupported expression {stx}"

/-- An expression, contracted. -/
partial def build (stx : Syntax) : TermElabM Node := do contract (← uncontracted stx)

end

/-- The tensor of `e` on the slots and colors of the tensor type `target`, its free indices in the
order written. It is `none` when `target` is not a tensor type with literal slots and colors. -/
def buildTo (e : Syntax) (target : Expr) : TermElabM (Option Term) := do
  let target ← whnfR (← instantiateMVars target)
  unless target.isAppOf ``Tensors.Species.Tensor do return none
  let args := target.getAppArgs
  let some slots ← Slots.ofType? args[args.size - 2]! | return none
  let c ← instantiateMVars args[args.size - 1]!
  let some cs ← colorList? c | return none
  let u ← uncontracted e
  -- A product with no contraction is already on the slots of its factors.
  let a ← if u.slots == slots && u.names.eraseDups.length == u.names.length then pure u
    else contract u
  unless cs.length == a.colors.length do
    throwError "index notation: {a.colors.length} free indices, but {cs.length} slots expected"
  for (col, i) in a.colors.zipIdx do
    unless ← isDefEq col cs[i]! do
      throwError "index notation: the free index {a.names[i]!} has the color {col}, but its slot \
        is expected to have the color {cs[i]!}"
  if a.slots == slots then return a.tm
  `(Tensors.Species.reindex $(← exprToSyntax a.species)
    (Tensors.ColorEquiv.mk (c₂ := $(← exprToSyntax c))
      $(← slotEquiv a.slots slots (List.range slots.size))) $a.tm)

/-- The term of `e` for the expected type. It is relabeled onto the slots of a tensor type, and read
back by `Tensorial.toTensor.symm` for a `Tensorial` type. -/
def buildFor (e : Syntax) (expectedType? : Option Expr) : TermElabM Term := do
  let some ty := expectedType? | return (← build e).tm
  let ty ← instantiateMVars ty
  if ty.getAppFn.isMVar || ty.isSort then return (← build e).tm
  if (← whnfR ty).isAppOf ``Tensors.Species.Tensor then
    return (← buildTo e ty).getD (← build e).tm
  -- For a `Tensorial` type, the tensor type is the codomain of `toTensor`.
  let M ← exprToSyntax ty
  let s ← saveState
  let some tensorTy ← try withoutErrToSorry do
      let f ← elabTerm (← `(fun m : $M => Tensors.Tensorial.toTensor m)) none
      synthesizeSyntheticMVarsNoPostponing
      pure (some (← inferType (← instantiateMVars f)).bindingBody!)
    catch _ => s.restore; pure none
    | return (← build e).tm
  let some tm ← buildTo e tensorTy | return (← build e).tm
  `((Tensors.Tensorial.toTensor (M := $M)).symm $tm)

/-- Elaborates index notation. An equation is allowed only at the top, possibly in parentheses. -/
@[term_elab tensorIndexSyntax] def elabTensorIndex : TermElab := fun stx expectedType? => do
  match stx with
  | `({ ($e:tensorIndexExpr) }ᵀ) => elabTerm (← `({ $e:tensorIndexExpr }ᵀ)) expectedType?
  | `({ $l:tensorIndexExpr = $r:tensorIndexExpr }ᵀ) =>
    let l ← build l
    elabTerm (← `($l.tm = $(← reorder l (← build r)))) none
  | `({ $e:tensorIndexExpr }ᵀ) => elabTerm (← buildFor e expectedType?) expectedType?
  | _ => throwUnsupportedSyntax

/-!

### B.4. Components

-/

/-- Removes `cast h a` when the two types agree at reducible transparency. -/
dsimproc_decl reduceCast (cast _ _) := fun e => do
  let_expr cast α β _ a := e | return .continue
  if ← withReducible (isDefEq α β) then return .done a else return .continue

/-- `tensor_components [l₁, …]` reduces an equation of tensors to its components at a label `φ`,
using the component lemmas `lᵢ` as well. It unfolds products, relabelings, sums, negatives, zeros,
scalar multiples and contractions of one or two pairs. For more pairs, pass
`Species.Tensor.tensorBasis_repr_contr`. It evaluates the `Function.update` at a literal slot that
`tensorBasis_repr_toDualAt` produces, and removes the casts on labels once their types agree. On a
goal that is already a component the first step is skipped. -/
syntax (name := tensorComponents) "tensor_components" " [" Lean.Parser.Tactic.simpArg,* "]" :
  tactic

macro_rules
  | `(tactic| tensor_components [$ls,*]) => `(tactic| focus
      try refine (Species.tensorBasis _ _).repr.injective (Finsupp.ext fun $(mkIdent `φ) => ?_)
      -- `Function.update_of_ne` proves `j ≠ i` for literal slots by `ne_eq` and `Fin.reduceEq`.
      simp only [map_add, map_neg, map_zero, Finsupp.add_apply, Finsupp.neg_apply,
        Finsupp.zero_apply, Species.Tensor.tensorBasis_repr_contr_one_pair,
        Species.Tensor.tensorBasis_repr_contr_two_pairs, Species.tensorBasis_repr_reindex,
        Species.tensorBasis_repr_tmulEquiv, map_smul, Finsupp.smul_apply, smul_eq_mul,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true, $ls,*]
      -- The casts of `tensorBasis_repr_reindex` agree once the relabeling and the color lists are
      -- evaluated. The option `+instances` reaches those inside instance arguments.
      try dsimp +instances only [ColorEquiv.symm, Equiv.symm_symm, Equiv.coe_fn_mk, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val, Function.comp_apply, Tensors.Notation.reduceCast])

/-!

### B.5. Regrouping contractions

-/

open Tactic

/-- The two factors `T` and `U` of a product `S.tmulEquiv c₁ c₂ (T ⊗ₜ U)`. -/
private def productFactors? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``DFunLike.coe 6 && e.appFn!.appArg!.isAppOf ``Tensors.Species.tmulEquiv then
    let x := e.appArg!.consumeMData
    if x.isAppOf ``TensorProduct.tmul then some (x.appFn!.appArg!, x.appArg!) else none
  else none

/-- The factors of a product, from left to right. -/
private partial def factors (e : Expr) : List Expr :=
  match productFactors? e with
  | some (a, b) => factors a ++ factors b
  | none => [e]

/-- The product of the first `n` factors of a left-nested product `e` of `m` factors. -/
private def leadingProduct (e : Expr) (m n : Nat) : Expr := Id.run do
  let mut e := e
  for _ in [0:m - n] do
    if let some (a, _) := productFactors? e then e := a
  return e

/-- The products `P` and `Q` of a goal `Tensor.contr σ P = Tensor.contr τ Q`. -/
private def contractedProducts : TacticM (Expr × Expr) := do
  let some (_, l, r) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "tensor_regroup: the goal is not an equation"
  let arg? (e : Expr) : Option Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``DFunLike.coe 6 &&
        e.appFn!.appArg!.isAppOf ``Tensors.Species.Tensor.contr then some e.appArg! else none
  let some p := arg? l | throwError "tensor_regroup: the left side is not a contraction"
  let some q := arg? r | throwError "tensor_regroup: the right side is not a contraction"
  return (p, q)

/-- Whether every product inside the product `e` is in its left factor. -/
private partial def isLeftNested (e : Expr) : Bool :=
  match productFactors? e with
  | some (a, b) => (productFactors? b).isNone && isLeftNested a
  | none => true

/-- Writes both sides of the goal as one contraction of a left-nested product, repeating until the
goal no longer changes, at most ten times. The three steps run separately, since together their
lemmas loop. -/
private def flattenContractions : TacticM Unit := do
  for _ in [0:10] do
    let before ← instantiateMVars (← getMainTarget)
    evalTactic (← `(tactic| try simp only [Tensors.Species.Tensor.tmulEquiv_contr_left,
      Tensors.Species.Tensor.tmulEquiv_contr_right, Tensors.Species.Tensor.contr_contr]))
    evalTactic (← `(tactic| try simp only [← Tensors.Species.tmulEquiv_assoc]))
    evalTactic (← `(tactic| try simp only [Tensors.Species.tmulEquiv_reindex_left,
      Tensors.Species.tmulEquiv_reindex_right, Tensors.Species.reindex_reindex,
      Tensors.Species.Tensor.contr_reindex, Tensors.Species.Tensor.reindex_contr]))
    if (← instantiateMVars (← getMainTarget)) == before then return
  throwError "tensor_regroup: flattening the products did not stop after ten rounds"

/-- Swaps the factors `m` and `m + 1` of the product `q`, of `n` factors, on the right side of the
goal, and absorbs the relabeling into the contraction. For two equal factors the two sides of the
swap lemma agree up to the relabeling, so it is rewritten once with `rw` rather than `simp`. -/
private def swapFactors (q : Expr) (n m : Nat) (equal : Bool) : TacticM Unit := do
  let fs := factors q
  let thm ← if m = 0 then
      `((Tensors.Species.tmulEquiv_comm _ _ $(← exprToSyntax fs[1]!)
        $(← exprToSyntax fs[0]!)).symm)
    else
      `((Tensors.Species.tmulEquiv_swapLast $(← exprToSyntax (leadingProduct q n m))
        $(← exprToSyntax fs[m]!) $(← exprToSyntax fs[m+1]!)).symm)
  if equal then
    evalTactic (← `(tactic| conv_rhs => rw [$thm:term]))
    evalTactic (← `(tactic| conv_rhs => simp only [Tensors.Species.tmulEquiv_reindex_left,
      Tensors.Species.reindex_reindex, Tensors.Species.Tensor.contr_reindex]))
  else
    evalTactic (← `(tactic| conv_rhs => simp only [$thm:term,
      Tensors.Species.tmulEquiv_reindex_left, Tensors.Species.reindex_reindex,
      Tensors.Species.Tensor.contr_reindex]))

/-- The ways to match each factor on the left with a different factor on the right, given for
each factor on the left the factors on the right equal to it. The matching in order comes first. -/
private partial def matchings : List (List Nat) → List Nat → List (List Nat)
  | [], _ => [[]]
  | c :: cs, used =>
    (c.filter (!used.contains ·)).flatMap fun j => (matchings cs (j :: used)).map (j :: ·)

/-- Orders the factors on the right side of the goal so that the factor at each position `k` is
the one that started at position `target[k]`, by swapping neighbours. `equal i j` says whether
the factors that started at `i` and `j` are equal. -/
private def arrange (target : List Nat) (equal : Nat → Nat → Bool) : TacticM Unit := do
  let n := target.length
  -- The starting positions of the factors in their current order.
  let mut labels := List.range n
  for pos in (List.range n).reverse do
    let k := labels.idxOf target[pos]!
    for m in [k:pos] do
      let (_, q) ← contractedProducts
      swapFactors q n m (equal labels[m]! labels[m+1]!)
      labels := (labels.set m labels[m+1]!).set (m+1) labels[m]!

/-- Proves `Tensor.contr σ P = Tensor.contr τ Q` for two contractions of the same factors. It writes
each side as one contraction of a product, orders the factors of the right side as on the left,
and checks by evaluation that both sides keep the same slots and contract the same pairs of slots
(`Species.Tensor.contr_eq_of_samePair`). When a factor appears more than once, each way of
matching the equal factors is tried in turn. -/
private def regroupContractions : TacticM Unit := do
  flattenContractions
  let (p, q) ← contractedProducts
  unless isLeftNested p && isLeftNested q do
    throwError "tensor_regroup: a side is not a left-nested product after flattening"
  let ps := factors p
  let qs := factors q
  unless ps.length = qs.length do
    throwError "tensor_regroup: the two sides have different numbers of factors"
  let n := ps.length
  -- Factors are compared once, without assigning metavariables of the goal.
  let same (a b : Expr) : TacticM Bool := withNewMCtxDepth (isDefEq a b)
  let candidates ← ps.mapM fun x => (List.range n).filterM fun j => same x qs[j]!
  let table ← (List.range n).toArray.mapM fun i =>
    (List.range n).toArray.mapM fun j => same qs[i]! qs[j]!
  let equal : Nat → Nat → Bool := fun i j => (table[i]!)[j]!
  let targets := matchings candidates []
  if targets.isEmpty then
    throwError "tensor_regroup: some factor on the left has no equal factor on the right"
  let s ← saveState
  let mut lastError : MessageData := m!""
  for target in targets do
    s.restore
    try
      arrange target equal
      -- The slots are a nested sum, whose `DecidableEq` instance exceeds the default size. The
      -- checks are run by `of_decide_eq_true rfl` rather than `decide`, which rejects the free
      -- color variables of the goal although the bijections of slots do not depend on them.
      evalTactic (← `(tactic| set_option synthInstance.maxSize 4096 in
        exact Tensors.Species.Tensor.contr_eq_of_samePair _ _ (of_decide_eq_true rfl)
          (of_decide_eq_true rfl) _))
      return
    catch e => lastError := e.toMessageData
  throwError "tensor_regroup: no matching of the factors gives two contractions of the same pairs \
    of slots. The last attempt failed with\n{lastError}"

/-- Brings both sides of the goal to sums of signed scalar multiples of contractions. Products,
contractions and relabelings are linear, so sums, negatives and scalars of `k` move out of them.
The scalar lemmas are given the field `k` of the species, so a group element `Λ • T` stays a
factor. -/
private def normalizeSums : TacticM Unit := do
  let some (ty, _, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "tensor_regroup: the goal is not an equation"
  let k ← exprToSyntax (← whnfR ty).getAppArgs[0]!
  evalTactic (← `(tactic| try simp only [map_add, map_neg, map_sub, map_smul,
    TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
    TensorProduct.tmul_smul (R' := $k), ← TensorProduct.smul_tmul' (R' := $k), smul_add,
    smul_neg, smul_smul, neg_neg, neg_add, sub_eq_add_neg]))

/-- The summands of a sum, from left to right. -/
private partial def summands (e : Expr) : List Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then summands e.appFn!.appArg! ++ summands e.appArg! else [e]

/-- Proves an equation of two summands with the same sign and the same scalar, by regrouping the
contractions they multiply. -/
private partial def regroupSummand : TacticM Unit := do
  let some (_, l, r) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "tensor_regroup: the goal is not an equation"
  let l := l.consumeMData
  let r := r.consumeMData
  if l.isAppOfArity ``Neg.neg 3 && r.isAppOfArity ``Neg.neg 3 then
    evalTactic (← `(tactic| refine congrArg Neg.neg ?_))
    regroupSummand
  else if l.isAppOfArity ``HSMul.hSMul 6 && r.isAppOfArity ``HSMul.hSMul 6 then
    let a := l.appFn!.appArg!
    unless ← withNewMCtxDepth (isDefEq a r.appFn!.appArg!) do
      throwError "tensor_regroup: the scalars {a} and {r.appFn!.appArg!} differ"
    evalTactic (← `(tactic| refine congrArg (HSMul.hSMul $(← exprToSyntax a)) ?_))
    regroupSummand
  else
    try evalTactic (← `(tactic| with_reducible rfl)) catch _ => regroupContractions

/-- `tensor_regroup` proves an equation of two sums of signed scalar multiples of contractions of
the same factors, grouped or ordered differently, such as
`{{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ {U | ν ρ ⊗ W | ρ τ}ᵀ | ν τ}ᵀ`. Sums,
negatives and scalars are first moved out of every product, contraction and relabeling. Each
summand on the left is then matched with a summand on the right with the same sign and scalar,
whose contraction is the same up to regrouping (`Species.Tensor.contr_eq_of_samePair`). When a
factor appears more than once, each way of matching the equal factors is tried in turn, so the
number of attempts is the product of `k!` over the factors that appear `k` times.

The scalars on the two sides must agree up to definitional equality, as `2` and `2`, and every
summand that is not the same term on both sides must be a contraction once relabelings are
absorbed. -/
elab "tensor_regroup" : tactic => do
  normalizeSums
  let some (_, l, r) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "tensor_regroup: the goal is not an equation"
  let ls := summands l
  let rs := summands r
  unless ls.length = rs.length do
    throwError "tensor_regroup: the two sides have different numbers of summands"
  if ls.length = 1 then
    regroupSummand
    return
  -- Each summand on the left is proved equal to an unused summand on the right in its own goal,
  -- and the sums then agree up to order.
  let main ← getMainGoal
  let mut used : List Nat := []
  let mut proofs : Array Term := #[]
  for a in ls do
    let mut found := false
    for j in List.range rs.length do
      if used.contains j then continue
      let s ← saveState
      let g ← mkFreshExprMVar (← mkEq a rs[j]!)
      try
        setGoals [g.mvarId!]
        regroupSummand
        unless (← getGoals).isEmpty do throwError "tensor_regroup: a summand is not closed"
        used := j :: used
        proofs := proofs.push (← exprToSyntax (← instantiateMVars g))
        found := true
        break
      catch _ => s.restore
    unless found do
      throwError "tensor_regroup: the summand{indentExpr a}\nhas no matching summand on the right"
  setGoals [main]
  -- `conv` closes the goal by `rfl` once the summands are rewritten in order.
  for h in proofs do
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| conv_lhs => rw [$h:term]))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| abel))

/-!

### B.6. Chains of lowerings and raisings

-/

/-- Whether `e` is a slotwise map `S.mapSlots F t` applied to a tensor. -/
private def isMapSlots (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``DFunLike.coe 6 && e.appFn!.appArg!.isAppOf ``Tensors.Species.mapSlots

/-- `tensor_slots` proves an equation of two chains of lowerings and raisings of the same tensor,
such as `{{T | ↓μ ↓ν}ᵀ | ↑μ ↑ν}ᵀ = T` or `{{T | ↓μ ν}ᵀ | μ ↓ν = {T | μ ↓ν}ᵀ | ↓μ ν}ᵀ`. Each chain
is one slotwise map (`Species.toDualAt_eq_mapAt`, `Species.mapSlots_mapSlots`), and the two maps
are compared slot by slot, where `Species.toDual_toDual` cancels a lowering with a raising. A side
with no lowering or raising is the slotwise identity (`Species.mapSlots_id`). The slots must be
`Fin n` with a literal `n`. -/
elab "tensor_slots" : tactic => do
  evalTactic (← `(tactic| simp only [Tensors.Species.toDualAt_eq_mapAt, Tensors.Species.mapAt,
    Tensors.Species.mapSlots_mapSlots]))
  let some (_, l, r) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "tensor_slots: the goal is not an equation"
  -- The branch is chosen from the two sides, since a failed unification with a side that is a
  -- definition, such as a named tensor, unfolds it.
  match isMapSlots l, isMapSlots r with
  | true, true => evalTactic (← `(tactic|
      refine congrArg (fun F => Tensors.Species.mapSlots _ F _) (funext ?_)))
  | true, false => evalTactic (← `(tactic|
      refine (congrArg (fun F => Tensors.Species.mapSlots _ F _) (funext ?_)).trans
        (Tensors.Species.mapSlots_id _)))
  | false, true => evalTactic (← `(tactic|
      refine (Tensors.Species.mapSlots_id _).symm.trans
        (congrArg (fun F => Tensors.Species.mapSlots _ F _) (funext ?_))))
  | false, false => throwError "tensor_slots: neither side lowers or raises an index"
  evalTactic (← `(tactic| focus
    intro x
    fin_cases x <;> refine LinearMap.ext fun v => ?_ <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, LinearMap.comp_apply,
        LinearMap.id_apply, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
        not_false_eq_true, dite_false, Representation.IntertwiningMap.coe_toLinearMap,
        Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.trans_apply,
        Tensors.Species.cast_apply, cast_cast, cast_eq, Tensors.Species.toDual_toDual] <;>
      -- On a species that is an `abbrev`, `simp` cannot rewrite under `toDual`: the types
      -- unfold and their instances do not. `rw` checks its motive at default transparency.
      (repeat rw [Tensors.Species.cast_apply]) <;> (repeat rw [cast_cast]) <;>
      (repeat rw [cast_eq]) <;> (repeat rw [Tensors.Species.toDual_toDual]) <;>
      (repeat rw [cast_cast]) <;> rfl))

end Tensors.Notation

end

/-!

## C. Examples

-/

namespace Tensors.Notation

open Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    (a c : Color K) (T U W : S.Tensor ![a, a.dual]) (T' : S.Tensor ![a.dual, a])
    (κ : K) (v : S.Tensor ![⟨κ, .up⟩]) (r : k) (Λ : G)

/-- info: T : S.Tensor ![a, a.dual] -/
#guard_msgs in
#check {T | μ ν}ᵀ

/-- The matrix product `T^μ_ν U^ν_ρ`. -/
noncomputable example : S.Tensor ![a, a.dual] := {T | μ ν ⊗ U | ν ρ}ᵀ

/-- A product given as one term, with the colors `prodColors ![a, a.dual] ![a, a.dual]`, is the
product in the notation. -/
example : {S.tmulEquiv _ _ (T ⊗ₜ U) | μ ν ν ρ = T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- An equation with a tensor `s` with no slots, `T^μ_μ = s`. The space after the bar keeps
Mathlib's absolute value `|x|` from reading it. -/
example (s : S.Tensor (![] : Fin 0 → Color K)) : {T | μ μ = s | }ᵀ ↔ {T | μ μ}ᵀ = s := Iff.rfl

/-- An equation in parentheses is the same equation. -/
example : {(T | μ ν = U | μ ν)}ᵀ ↔ {T | μ ν = U | μ ν}ᵀ := Iff.rfl

/-- An equation whose right side lists its indices in the other order, `T^μ_ν = T'_ν^μ`. -/
example : Prop := {T | μ ν = T' | ν μ}ᵀ

/-- The trace of a product of four matrices, `T^μ_ν U^ν_ρ T^ρ_σ U^σ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ}ᵀ

/-- The trace of a product of five matrices, `T^μ_ν U^ν_ρ W^ρ_σ T^σ_τ U^τ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ W | ρ σ ⊗ T | σ τ ⊗ U | τ μ}ᵀ

/-- Sums, negatives and scalar multiples, `-T^μ_ν + r U^μ_ν`. -/
example : {-T | μ ν + r • U | μ ν}ᵀ = -T + r • U := rfl

/-- A scalar multiple of a contraction, `r T^μ_ν U^ν_ρ`. -/
example : {r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ}ᵀ = r • {T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- Each side of a sum is contracted first, so `μ` is free again in the product,
`(T^λ_λ + U^λ_λ) T^μ_ν`. -/
example : {(T | μ μ + U | μ μ) ⊗ T | μ ν}ᵀ = {({T | μ μ}ᵀ + {U | μ μ}ᵀ) | ⊗ T | μ ν}ᵀ := rfl

-- The two sides of a sum or an equation must agree in the colors of each name.
/-- error: index notation: ν has the color a.dual on the left and a on the right -/
#guard_msgs in
#check {T | μ ν = T | ν μ}ᵀ

-- A term that is neither a tensor nor tensorial is rejected, with the error of the instance search.
/-- error: index notation: r is not a tensor and has no `Tensorial` instance:
failed to synthesize instance of type class
  Tensorial -/
#guard_msgs (substring := true) in
#check {r | μ}ᵀ

-- A term whose type is not known, such as a bare numeral, is rejected.
/-- error: index notation: the type of 0 is not known; give it, as `(0 : S.Tensor ![…])` -/
#guard_msgs in
#check {0 | μ ν}ᵀ

/-- An expression in parentheses is contracted first, so `μ` is free again in the product,
`(T^λ_λ) U^μ_ρ`. -/
example : {(T | μ μ) ⊗ U | μ ρ}ᵀ = {{T | μ μ}ᵀ | ⊗ U | μ ρ}ᵀ := rfl

-- A name appearing three times in one product chain is rejected.
/-- error: index notation: μ appears more than twice -/
#guard_msgs in
#check {T | μ μ ⊗ U | μ ρ}ᵀ

-- A tensor whose colors are not a literal list is rejected.
/-- error: index notation: the colors of t must be a literal list -/
#guard_msgs in
example (f : Fin 2 → Color K) (t : S.Tensor f) : S.Tensor f := {t | μ ν}ᵀ

-- A pair of slots whose colors are not dual is rejected.
/-- error: index notation: μ joins the colors a and a, which are not dual -/
#guard_msgs in
#check {T | μ ν ⊗ T | μ ρ}ᵀ

/-- Contracting `ν` and then `ρ` is contracting both at once, `(T U)^μ_ρ W^ρ_τ = T^μ_ν U^ν_ρ W^ρ_τ`,
by `tmulEquiv_contr_left` and `contr_contr`. -/
example : {{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ U | ν ρ ⊗ W | ρ τ}ᵀ := by
  rw [Tensor.tmulEquiv_contr_left, Tensor.contr_contr]
  congr 2
  ext x
  fin_cases x <;> rfl

/-- The same by `tensor_regroup`, with the other grouping on the right,
`(T U)^μ_ρ W^ρ_τ = T^μ_ν (U W)^ν_τ`. -/
example : {{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ {U | ν ρ ⊗ W | ρ τ}ᵀ | ν τ}ᵀ := by
  tensor_regroup

/-- `tensor_regroup` reorders the factors, `T^μ_ν U^ν_ρ = U^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ U | ν ρ = U | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- A factor that appears twice, `T^μ_ν T^ν_ρ = T^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ T | ν ρ = T | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- The trace is cyclic, `tr(T U T U) = tr(U T U T)`. -/
example : {T | μ ν ⊗ U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ = U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- `tensor_regroup` moves scalars out of the products, `(r T^μ_ν) U^ν_ρ = r (U^ν_ρ T^μ_ν)`. -/
example : {(r • T) | μ ν ⊗ U | ν ρ = r • {U | ν ρ ⊗ T | μ ν}ᵀ | ρ μ}ᵀ := by
  tensor_regroup

/-- Negatives, `(-T^μ_ν) U^ν_ρ = -(U^ν_ρ T^μ_ν)`. -/
example : {-T | μ ν ⊗ U | ν ρ = -{U | ν ρ ⊗ T | μ ν}ᵀ | ρ μ}ᵀ := by
  tensor_regroup

/-- Sums, matched summand by summand in any order, `T^μ_ν U^ν_ρ - W^μ_ρ = -W^μ_ρ + U^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ U | ν ρ + -W | μ ρ = -W | μ ρ + U | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- A sum inside a product is distributed, `T^μ_ν (U + W)^ν_ρ = U^ν_ρ T^μ_ν + W^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ (U | ν ρ + W | ν ρ) = U | ν ρ ⊗ T | μ ν + W | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

section Metric

variable [S.HasForm κ] [S.HasForm c.kind]

/-- Lowering and then raising an index gives the vector back, `(v_μ)^μ = v^μ`. -/
example : {{v | ↓μ}ᵀ | ↑μ}ᵀ = v := toDualAt_toDualAt _ _ _ _ _ _

/-- The same by `tensor_slots`. -/
example : {{v | ↓μ}ᵀ | ↑μ}ᵀ = v := by
  tensor_slots

/-- Lowering both indices and raising them again, `(M_μν)^μν = M^μν`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {{M | ↓μ ↓ν}ᵀ | ↑μ ↑ν}ᵀ = M := by
  tensor_slots

/-- Lowerings at two slots commute, `(M_μ^ν)_ν = (M^μ_ν)_μ`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {{M | ↓μ ν}ᵀ | μ ↓ν = {M | μ ↓ν}ᵀ | ↓μ ν}ᵀ := by
  tensor_slots

-- An arrow that does not match the variance of the slot is rejected.
/-- error: index notation: ↑μ needs a visibly lower index -/
#guard_msgs in
#check {v | ↑μ}ᵀ

/-- Lowering commutes with the group action, `(Λ v)_μ = Λ (v_μ)`, by `rw [equiv_smul]`. -/
example : {(Λ • v) | ↓μ}ᵀ = Λ • {v | ↓μ}ᵀ := by rw [equiv_smul]

/-- Lowering both indices commutes with the group action, `(Λ M)_μν = Λ (M_μν)`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {(Λ • M) | ↓μ ↓ν}ᵀ = Λ • {M | ↓μ ↓ν}ᵀ := by
  simp only [equiv_smul]

/-- A trace commutes with the group action, `(Λ T)^μ_μ = Λ (T^μ_μ)`, by
`rw [intertwiningMap_smul]`. -/
example : {(Λ • T) | μ μ}ᵀ = Λ • {T | μ μ}ᵀ := by rw [intertwiningMap_smul]

/-- `g^μν g_νρ = δ^μ_ρ`, by `contr_formTensor_formTensor`. The relabeling the notation generates
is `ColorEquiv.matMul`, checked slot by slot. -/
example : {S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ := by
  rw [← contr_formTensor_formTensor]
  congr 2
  ext x
  fin_cases x <;> rfl

end Metric

section Tensorial

variable {M : Type} [AddCommGroup M] [Module k M] [Tensorial S ![a, a.dual] M] (m : M)

/-- info: Tensorial.toTensor m : S.Tensor ![a, a.dual] -/
#guard_msgs in
#check {m | μ ν}ᵀ

/-- The contraction `m^μ_ν T^ν_ρ` of an element of a tensorial type with a tensor. -/
noncomputable example : S.Tensor ![a, a.dual] := {m | μ ν ⊗ T | ν ρ}ᵀ

/-- The contraction `m^μ_ν m^ν_ρ` inside `M ⊗ M`, through `Tensorial.prod`. -/
noncomputable example : S.Tensor ![a, a.dual] := {(m ⊗ₜ[k] m) | μ ν ν ρ}ᵀ

/-- The contraction `m^μ_ν T^ν_ρ` read back as an element of `M`. -/
noncomputable example : M := {m | μ ν ⊗ T | ν ρ}ᵀ

open TensorProduct in
/-- A product with no contraction is read back as `m ⊗ₜ m`, with no relabeling. -/
example : ({m | μ ν ⊗ m | ρ σ}ᵀ : M ⊗[k] M) = m ⊗ₜ m := by
  rw [← Tensorial.toTensor_tmul, Representation.Equiv.symm_apply_apply]

/-- A tensor on `Fin 2` relabeled onto the slots `Fin 1 ⊕ Fin 1` of a product. -/
noncomputable example : S.Tensor (prodColors ![a] ![a.dual]) := {T | μ ν}ᵀ

/-- error: index notation: the free index μ has the color a, but its slot is expected to have the
color a.dual -/
#guard_msgs in
example : S.Tensor (prodColors ![a.dual] ![a]) := {T | μ ν}ᵀ

end Tensorial

end Tensors.Notation
