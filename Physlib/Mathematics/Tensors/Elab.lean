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
per index. The heights of the indices are not written, since the colors fix them. A real Lorentz
tensor `T : Tensor S ![⟨vec, up⟩, ⟨vec, down⟩]`, with components `T^μ_ν`, is written `T | μ ν`.

An expression `{…}ᵀ` is a tensor in `Tensor S ![…]`, or a proposition if it is an equation. The
names are bound only inside the braces. Each construct is an operation of the species.

- `A ⊗ B` is `S.tmulEquiv _ _ (A ⊗ₜ B)`.
- A name written twice in a product is contracted. All pairs of the product are contracted in one
  `Tensor.contr σ`, with the reindexing `σ` generated from the names. The two indices of a pair must
  have dual colors, and the first one written is the first argument of `S.contr`.
- The free indices are numbered `0, 1, …` in the order written. The result is a tensor on `Fin m`
  with a literal color list `![…]`.
- `A + B` and `A = B` reindex `B` by `S.reindex` when its names come in another order. Each name
  must have the same color on both sides.
- `↓μ` lowers an upper index and `↑μ` raises a lower one, by `S.toDualAt`, so `{v | ↓ν}ᵀ` is
  `v_ν = v^μ g_μν`. This needs an instance `S.HasForm` at the kind of the index, and a visible
  variance, as in `⟨κ, .up⟩`.
- `τ(μ)` flips the variance of an index by `S.toDualAt` whichever way it points, so it needs no
  visible variance.
- A term `m : M` with an instance `Tensorial S c M`, such as a Lorentz vector, is read as
  `Tensorial.toTensor m`.
- Scalars, group elements and negatives are ordinary terms in front of `|`, as in `r • T | μ ν`,
  `Λ • T | μ ν` and `-T | μ ν`. A compound expression is scaled by nesting it, as in
  `r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ`. The form `-(T | μ ν)` is a parse error.

Parentheses, each side of a sum and a nested `{…}ᵀ` are contracted before they enter an enclosing
product, so the names they contract are free again outside. Thus `{(T | μ μ) ⊗ U | μ ρ}ᵀ` is
`(T^λ_λ) U^μ_ρ`. Within one product a name appears at most twice.

When the expected type is known, the result is fitted to it. On a tensor type with another index
type, such as `Fin 1 ⊕ Fin 1` for `Fin 2`, the free indices are placed on its indices in the order
written. On a type `M` with an instance `Tensorial S c M`, the result is read back by
`Tensorial.toTensor.symm`. So `({v | ↓μ}ᵀ : CoVector d)` is the covector `v_μ`, and
`({x | μ ⊗ y | ν}ᵀ : Vector d ⊗ Vector d)` is `x ⊗ₜ y`.

Every tensor needs literal indices and colors. Its index type is built from `Fin n` and `⊕` with a
literal `n`, and its colors are a literal list `![a, b, …]` or `prodColors` of such lists. General
lemmas over a variable color family are therefore stated without the notation. A tensor `s` with
no indices is written `s |` with a space after the bar, since Mathlib reads `|x|` as an absolute
value.

For an upper color `c`, the inverse forms `g^μν g_νρ = δ^μ_ρ` are written
`{S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ`, which is
`contr_formTensor_formTensor`. Examples of the notation are in
`Physlib.Mathematics.Tensors.ElabExamples`.

## ii. Key results

- `{…}ᵀ` : index notation, elaborated by `elabTensorIndex`.

## iii. Table of contents

- A. Syntax
- B. Elaboration
  - B.1. Index types
  - B.2. The steps of an expression
  - B.3. The elaborator

## iv. References

There are no known references for the material in this module.

-/

public meta section

open Lean Meta Elab Term

namespace Tensor.Notation

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
/-- A named index whose variance is flipped with the invariant form, lowered if upper and raised if
lower. -/
syntax "τ(" ident ")" : tensorIndex

/-- A tensor expression in index notation. -/
declare_syntax_cat tensorIndexExpr
/-- A tensor with a name on each index. -/
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

### B.1. Index types

-/

/-- An index type built from `Fin n`, `Unit`, `Empty` and `⊕`. Its indices are numbered `0, 1, …` in
order. -/
inductive Indices where
  /-- `Fin n`. -/
  | fin (n : Nat)
  /-- `Unit`. -/
  | unit
  /-- `Empty`. -/
  | empty
  /-- `a ⊕ b`. -/
  | sum (a b : Indices)
deriving BEq

/-- The number of indices. -/
def Indices.size : Indices → Nat
  | .fin n => n
  | .unit => 1
  | .empty => 0
  | .sum a b => a.size + b.size

/-- The index type as a term. -/
def Indices.type : Indices → TermElabM Term
  | .fin n => `(Fin $(quote n))
  | .unit => `(Unit)
  | .empty => `(Empty)
  | .sum a b => do `($(← a.type) ⊕ $(← b.type))

/-- The index type as an expression. -/
def Indices.toExpr : Indices → Expr
  | .fin n => mkApp (mkConst ``Fin) (mkNatLit n)
  | .unit => mkConst ``Unit
  | .empty => mkConst ``Empty
  | .sum a b => mkApp2 (mkConst ``Sum [.zero, .zero]) a.toExpr b.toExpr

/-- The index `i` as a term. -/
def Indices.elem : Indices → Nat → TermElabM Term
  | .fin n, i => `(($(quote i) : Fin $(quote n)))
  | .unit, _ => `(())
  | .empty, _ => throwError "index notation: internal error, `Empty` has no index"
  | .sum a b, i =>
    if i < a.size then do `(Sum.inl $(← a.elem i)) else do `(Sum.inr $(← b.elem (i - a.size)))

/-- The indices `0, 1, …` in order, as elements of the index type `toExpr`. -/
def Indices.elems : Indices → MetaM (List Expr)
  | .fin n => (List.range n).mapM fun i => do
    mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n])]
  | .unit => return [mkConst ``Unit.unit]
  | .empty => return []
  | .sum a b => do
    let inj (f : Name) := mkApp3 (mkConst f [.zero, .zero]) a.toExpr b.toExpr
    return (← a.elems).map (inj ``Sum.inl) ++ (← b.elems).map (inj ``Sum.inr)

/-- The function on an index type taking the values `vs` in index order, built from vector literals
on `Fin n`, constants on `Unit`, `Empty.elim` on `Empty` and `comb` on `⊕`. -/
def Indices.fn (comb : Name) : Indices → List Term → TermElabM Term
  | .fin _, vs => `(![$(vs.toArray),*])
  | .unit, vs => `(fun _ : Unit => $(vs[0]!))
  | .empty, _ => `(Empty.elim)
  | .sum a b, vs => do
    `($(mkIdent comb) $(← a.fn comb (vs.take a.size)) $(← b.fn comb (vs.drop a.size)))

/-- The index type of a type built from `Fin n` with a literal `n`, `Unit`, `Empty` and `⊕`. -/
partial def Indices.ofType? (ι : Expr) : MetaM (Option Indices) := do
  match_expr (← whnfR ι) with
  | Fin n => return (← (evalNat n).run).map .fin
  | Sum a b =>
    let some a ← Indices.ofType? a | return none
    let some b ← Indices.ofType? b | return none
    return some (.sum a b)
  | PUnit => return some .unit
  | Empty => return some .empty
  | _ => return none

/-- The bijection from `dom` to `cod` sending the index `pre[j]` of `dom` to the index `j` of `cod`.
The list `pre` names every index of `dom` once. Its inverse identities are proved index by index
by `fin_cases`. -/
def indexEquiv (dom cod : Indices) (pre : List Nat) : TermElabM Term := do
  let toFun ← dom.fn ``Sum.elim (← (List.range dom.size).mapM fun i => cod.elem (pre.idxOf i))
  let invFun ← cod.fn ``Sum.elim (← pre.mapM dom.elem)
  -- `decide` would need a `DecidableEq` instance on the whole index type, which exceeds the
  -- instance size limit from four contracted pairs on.
  `((Equiv.mk $toFun $invFun (by intro x; fin_cases x <;> rfl)
      (by intro x; fin_cases x <;> rfl) : $(← dom.type) ≃ $(← cod.type)))

/-- The entries of a literal color family `![a, b, …]`, or of `prodColors` of literal families. -/
partial def colorList? (c : Expr) : MetaM (Option (List Expr)) := do
  match_expr c with
  | Tensor.prodColors _ _ _ c₁ c₂ => return (· ++ ·) <$> (← colorList? c₁) <*> (← colorList? c₂)
  | _ =>
    let (cs, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit 0) c
    return if tail.isAppOfArity ``Matrix.vecEmpty 1 then some cs else none

/-- The literal color family `![a, b, …]`. -/
def colorsTerm (cs : List Expr) : TermElabM Term := do
  `(![$((← cs.toArray.mapM exprToSyntax)),*])

/-- The species `S`, the index type `ι` and the color family `c` of a tensor type
`Tensor S (ι := ι) c`. -/
def tensorTypeArgs? (ty : Expr) : Option (Expr × Expr × Expr) :=
  let_expr Tensor _ _ _ _ _ _ _ _ S ι c := ty | none
  some (S, ι, c)

/-- The index type, the color family `c` and its entries of a tensor type `Tensor S c` with literal
indices and colors. -/
def literalTensorType? (ty : Expr) : MetaM (Option (Indices × Expr × List Expr)) := do
  let some (_, ι, c) := tensorTypeArgs? (← whnfR (← instantiateMVars ty)) | return none
  let some indices ← Indices.ofType? ι | return none
  let c ← instantiateMVars c
  let some cs ← colorList? c | return none
  return (indices, c, cs)

/-!

### B.2. The steps of an expression

-/

/-- A partly elaborated expression, with the name and color of each index, its index type, its
tensor and its species. -/
structure Node where
  /-- The name of each index. -/
  names : List Name
  /-- The color of each index. -/
  colors : List Expr
  /-- The index type. -/
  indices : Indices
  /-- The tensor. -/
  tm : Term
  /-- The species. -/
  species : Expr

/-- The tensor of `a` reindexed onto `Fin pre.length` with the colors `cs`, its index `pre[j]`
becoming the index `j`. -/
def Node.reindex (a : Node) (pre : List Nat) (cs : List Expr) : TermElabM Term := do
  `(Tensor.Species.reindex $(← exprToSyntax a.species)
    (Tensor.ColorEquiv.mk (c₂ := $(← colorsTerm cs))
      $(← indexEquiv a.indices (.fin pre.length) pre))
    $a.tm)

/-- The expression reindexed to `Fin n`, its indices numbered in order. -/
def Node.toFin (a : Node) : TermElabM Node := do
  let n := a.names.length
  if a.indices == .fin n then return a
  return { a with indices := .fin n, tm := ← a.reindex (List.range n) a.colors }

/-- The expression on `Fin n` with its index `i` moved to the dual color by `S.toDualAt`. -/
def Node.toDualAt (a : Node) (i : Nat) : TermElabM Node := do
  let colors := a.colors.set i (← mkAppM ``Tensor.Color.dual #[a.colors[i]!])
  -- The color `col` of the index is passed explicitly, so the form is found at the kind of `col`
  -- and every lowering at that kind uses the same instance. The proofs `c i = col` and
  -- `c' i = col.dual` are `id rfl`, since a bare `rfl` has the type `c' i = c' i`, which `rw`
  -- matches only after unfolding `![…] i`. Away from `i` the colors agree by cases.
  let tm ← `(Tensor.Species.toDualAt $(← exprToSyntax a.species) (c' := $(← colorsTerm colors))
    ($(quote i) : Fin $(quote a.names.length)) $(← exprToSyntax a.colors[i]!) (id rfl) (id rfl)
    (by intro x hx; fin_cases x <;> first | rfl | exact absurd rfl hx) $a.tm)
  return { a with colors, tm }

/-- The term `T` and its type, a tensor type. A term that is not a tensor is read as
`Tensorial.toTensor T` through its `Tensorial` instance. -/
def tensorOf (T : Term) : TermElabM (Expr × Expr) := do
  let e ← instantiateMVars (← elabTerm T none)
  if e.hasSyntheticSorry then throwAbortTerm
  let ty ← whnfR (← instantiateMVars (← inferType e))
  if ty.isMVar then
    throwError "index notation: the type of {T} is not known; give it, as `({T} : Tensor S ![…])`"
  if ty.isAppOf ``Tensor then return (e, ty)
  try
    let e ← withoutErrToSorry do
      let e ← elabTerm (← `(Tensor.Tensorial.toTensor $(← exprToSyntax e))) none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    return (e, ← whnfR (← instantiateMVars (← inferType e)))
  catch ex =>
    throwError "index notation: {T} is not a tensor and has no `Tensorial` instance:\n\
      {ex.toMessageData}"

/-- The name of the written index `i`, of color `col`, and whether its variance is flipped, after
checking that an arrow matches the variance of `col`. -/
def indexName (i : TSyntax `tensorIndex) (col : Expr) : TermElabM (Name × Bool) := do
  let arrow (x : Ident) (up : Bool) : TermElabM (Name × Bool) := do
    let isUp ← whnfD (← mkAppM ``Tensor.Variance.isUp #[← mkAppM ``Tensor.Color.variance #[col]])
    unless isUp.isConstOf (if up then ``Bool.true else ``Bool.false) do
      throwError "index notation: {if up then "↓" else "↑"}{x.getId} needs a visibly \
        {if up then "upper" else "lower"} index"
    pure (x.getId, true)
  match i with
  | `(tensorIndex| $x:ident) => pure (x.getId, false)
  | `(tensorIndex| ↓$x:ident) => arrow x true
  | `(tensorIndex| ↑$x:ident) => arrow x false
  | `(tensorIndex| τ($x:ident)) => pure (x.getId, true)
  | _ => throwError "index notation: unsupported index {i}"

/-- The tensor `T | i₁ i₂ …` with its indices named, lowered at each `↓μ`, raised at each `↑μ`
and flipped at each `τ(μ)`. -/
def leaf (T : Term) (idxs : Array (TSyntax `tensorIndex)) : TermElabM Node := do
  let (e, ty) ← tensorOf T
  let some (S, ι, c) := tensorTypeArgs? ty
    | throwError "index notation: internal error, the type of {T} is not a tensor type"
  let some indices ← Indices.ofType? ι
    | throwError "index notation: the index type {ι} of {T} must be built from `Fin n` with a \
        literal `n`, `Unit`, `Empty` and `⊕`"
  let some colors ← colorList? c
    | throwError "index notation: the colors of {T} must be a literal list"
  unless colors.length = idxs.size do
    throwError "index notation: {T} has {colors.length} indices, but {idxs.size} names are given"
  let kinds ← (idxs.toList.zip colors).mapM fun (i, col) => indexName i col
  let a : Node := ⟨kinds.map (·.1), colors, indices, ← exprToSyntax e, S⟩
  if kinds.all (!·.2) then return a
  kinds.zipIdx.foldlM (init := ← a.toFin) fun a ((_, d), i) => if d then a.toDualAt i else pure a

/-- Contracts every repeated name in one `Tensor.contr`, and numbers the free indices in the order
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
        unless ← isDefEq a.colors[i₂]! (← mkAppM ``Tensor.Color.dual #[a.colors[i₁]!]) do
          throwError "index notation: {nm} joins the colors {a.colors[i₁]!} and \
            {a.colors[i₂]!}, which are not dual"
        pairs := pairs ++ [(i₁, i₂)]
    | _ => throwError "index notation: {nm} appears more than twice"
  if pairs.isEmpty then return ← a.toFin
  let m := free.length
  -- The pairs are labeled by `Unit` for one pair, as in `ColorEquiv.matMul`, and by
  -- `(… ⊕ Unit) ⊕ Unit` for more, as `ColorEquiv.chain` combines two contractions in sequence.
  let J := (List.range (pairs.length - 1)).foldl (fun J _ => Indices.sum J .unit) .unit
  -- The free indices go to `inl k`, the first index of the pair `j` to `inr (inl j)` and its second
  -- index to `inr (inr j)`.
  let σ ← indexEquiv a.indices (.sum (.fin m) (.sum J J))
    (free ++ pairs.map (·.1) ++ pairs.map (·.2))
  let pairColors ← J.fn ``Tensor.prodColors (← pairs.mapM fun (i, _) => exprToSyntax a.colors[i]!)
  let tm ← `(Tensor.contr (S := $(← exprToSyntax a.species))
    (Tensor.ColorEquiv.mk
      (c₂ := Tensor.contrColors $(← colorsTerm (free.map (a.colors[·]!))) $pairColors) $σ)
    $a.tm)
  return ⟨free.map (a.names[·]!), free.map (a.colors[·]!), .fin m, tm, a.species⟩

/-- The right side reindexed to the order of the left side's names, after checking that each name
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
    let tm ← `(Tensor.Species.tmulEquiv $(← exprToSyntax a.species) _ _
      (TensorProduct.tmul _ $a.tm $b.tm))
    return ⟨a.names ++ b.names, a.colors ++ b.colors, .sum a.indices b.indices, tm, a.species⟩
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

/-- The tensor of `e` on the indices and colors of the tensor type `target`, its free indices in the
order written. It is `none` when `target` is not a tensor type with literal indices and colors. -/
def buildTo (e : Syntax) (target : Expr) : TermElabM (Option Term) := do
  let some (indices, c, cs) ← literalTensorType? target | return none
  let u ← uncontracted e
  -- A product with no contraction is already on the indices of its factors.
  let a ← if u.indices == indices && u.names.eraseDups.length == u.names.length then pure u
    else contract u
  unless cs.length == a.colors.length do
    throwError "index notation: {a.colors.length} free indices, but {cs.length} indices expected"
  for (col, i) in a.colors.zipIdx do
    unless ← isDefEq col cs[i]! do
      throwError "index notation: the free index {a.names[i]!} has the color {col}, but the \
        expected index has the color {cs[i]!}"
  if a.indices == indices then return a.tm
  `(Tensor.Species.reindex $(← exprToSyntax a.species)
    (Tensor.ColorEquiv.mk (c₂ := $(← exprToSyntax c))
      $(← indexEquiv a.indices indices (List.range indices.size))) $a.tm)

/-- The term of `e` for the expected type. It is reindexed onto the indices of a tensor type, and
read back by `Tensorial.toTensor.symm` for a `Tensorial` type. -/
def buildFor (e : Syntax) (expectedType? : Option Expr) : TermElabM Term := do
  let some ty := expectedType? | return (← build e).tm
  let ty ← instantiateMVars ty
  if ty.getAppFn.isMVar || ty.isSort then return (← build e).tm
  if (← whnfR ty).isAppOf ``Tensor then
    match ← buildTo e ty with
    | some tm => return tm
    | none => return (← build e).tm
  -- For a `Tensorial` type, the tensor type is the codomain of `toTensor`.
  let M ← exprToSyntax ty
  let s ← saveState
  let some tensorTy ← try withoutErrToSorry do
      let f ← elabTerm (← `(fun m : $M => Tensor.Tensorial.toTensor m)) none
      synthesizeSyntheticMVarsNoPostponing
      pure (some (← inferType (← instantiateMVars f)).bindingBody!)
    catch _ => s.restore; pure none
    | return (← build e).tm
  let some tm ← buildTo e tensorTy | return (← build e).tm
  `((Tensor.Tensorial.toTensor (M := $M)).symm $tm)

/-- Elaborates index notation. An equation is allowed only at the top, possibly in parentheses. -/
@[term_elab tensorIndexSyntax] def elabTensorIndex : TermElab := fun stx expectedType? => do
  match stx with
  | `({ ($e:tensorIndexExpr) }ᵀ) => elabTerm (← `({ $e:tensorIndexExpr }ᵀ)) expectedType?
  | `({ $l:tensorIndexExpr = $r:tensorIndexExpr }ᵀ) =>
    let l ← build l
    elabTerm (← `($l.tm = $(← reorder l (← build r)))) none
  | `({ $e:tensorIndexExpr }ᵀ) => elabTerm (← buildFor e expectedType?) expectedType?
  | _ => throwUnsupportedSyntax

end Tensor.Notation

end
