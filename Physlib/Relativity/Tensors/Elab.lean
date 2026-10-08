/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Dual
public import Physlib.Relativity.Tensors.Tensorial
/-!

# Elaboration of tensor expressions

- Syntax in Lean allows us to represent tensor expressions in a way close to what we expect to
  see on pen-and-paper.
- The elaborator turns this syntax into a tensor tree.

## Examples

- Suppose `T` and `T'` are tensors with color `![c1, c2]`.
- `{T | μ ν}ᵀ` is `tensorNode T`.
- We can also write e.g. `{T | μ ν}ᵀ.tensor` to get the tensor itself.
- `{- T | μ ν}ᵀ` is `neg (tensorNode T)`.
- `{T | 0 ν}ᵀ` is `eval 0 0 (tensorNode T)`.
- `{T | [μ] ν}ᵀ` is `eval 0 μ (tensorNode T)`.
- `{T | μ ν + T' | μ ν}ᵀ` is `addNode (tensorNode T) (perm _ (tensorNode T'))`, where
  here `_` will be the identity permutation so does nothing.
- `{T | μ ν = T' | μ ν}ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T')).tensor`.
- If `a ∈ k` then `{a •ₜ T | μ ν}ᵀ` is `smulNode a (tensorNode T)`.
- If `g ∈ S.G` then `{g •ₐ T | μ ν}ᵀ` is `actionNode g (tensorNode T)`.
- Suppose `T2` is a tensor with color `![c3]`.
  Then `{T | μ ν ⊗ T2 | σ}ᵀ` is `prodNode (tensorNode T) (tensorNode T2)`.
- If `T3` is a tensor with color `![S.τ c1, S.τ c2]`, then
  `{T | μ ν ⊗ T3 | μ σ}ᵀ` is `contr 0 1 _ (prodNode (tensorNode T) (tensorNode T3))`.
  `{T | μ ν ⊗ T3 | μ ν }ᵀ` is
  `contr 0 0 _ (contr 0 1 _ (prodNode (tensorNode T) (tensorNode T3)))`.
- If `T4` is a tensor with color `![c2, c1]` then
  `{T | μ ν + T4 | ν μ }ᵀ`is `addNode (tensorNode T) (perm _ (tensorNode T4))` where `_`
  is the permutation of the two indices of `T4`.
  `{T | μ ν = T4 | ν μ }ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T4)).tensor` is the
  permutation of the two indices of `T4`.

## Comments

- In all of these expressions `μ`, `ν` etc are free. It does not matter what they are called,
  Lean will elaborate them in the same way. In other words, `{T | μ ν ⊗ T3 | μ ν }ᵀ` is exactly
  the same to Lean as `{T | α β ⊗ T3 | α β }ᵀ`.
- Note that compared to ordinary index notation, we do not rise or lower the indices.
  This is for two reasons: 1) It is difficult to make this general for all tensor species,
  2) It is a redundancy in ordinary index notation, since the tensor `T` itself already tells you
  this information.

-/

@[expose] public meta section
open Lean Meta Elab Tactic Term

namespace TensorSpecies
namespace Tensor

/-!

## Indices

-/

/-- A syntax category for indices of tensor expressions. -/
declare_syntax_cat indexExpr

/-- A basic index is a ident. -/
syntax ident : indexExpr

/-- An index can be a num, which will be used to evaluate the tensor. -/
syntax num : indexExpr


/-- Notation to describe the evaluation of a tensor index. The term inside the brackets is
  the value of the index, which can be an identifier `[μ]` or an arbitrary term such as
  `[Sum.inl 0]`. -/
syntax "[" term "]" : indexExpr

/-- Notation to describe the jiggle of a tensor index. -/
syntax "τ(" ident ")" : indexExpr

/-- Bool which is true if an index is a num. -/
def indexExprIsNum (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|$_:num) => true
  | _ => false

/-- Bool which is true if an index is a jiggle `τ(i)`. -/
def indexExprIsJiggle (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|τ($_)) => true
  | _ => false

/-- Removes a `τ(⬝)` wrapper from an index, leaving any other index unchanged. Pure, so it can be
  used to compare indices up to `τ` (e.g. when counting contractions in `withoutContrEval`). -/
def indexRemoveTau (stx : TSyntax `indexExpr) : TSyntax `indexExpr := Unhygienic.run do
  match stx with
  | `(indexExpr| τ($a:ident)) => `(indexExpr| $a:ident)
  | _ => return stx

/-- Bool which is true if an index is evaluated bracket `[μ]`. -/
def indexExprIsBracketEval(stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|[$_]) => true
  | _ => false

/-- If an index is a num - the underlying natural number. -/
def indexToNum (stx : Syntax) : TermElabM Nat :=
  match stx with
  | `(indexExpr|$a:num) =>
    match a.raw.isNatLit? with
    | some n => return n
    | none => throwError "Expected a natural number literal."
  | _ =>
    throwError "Unsupported tensor expression syntax in indexToNum: {stx}"

/-- When an index is not a num, the corresponding ident. -/
def indexToIdent (stx : Syntax) : TermElabM Ident :=
  match stx with
  | `(indexExpr|$a:ident) => return a
  | `(indexExpr| τ($a:ident)) => return a
  | _ =>
    throwError "Unsupported expression syntax in indexToIdent: {stx}"

/-- For an evaluated bracket index `[t]`, the term `t` giving the value of the index. -/
def indexToBracketTerm (stx : Syntax) : TermElabM Term :=
  match stx with
  | `(indexExpr| [$a:term]) => return a
  | _ =>
    throwError "Unsupported expression syntax in indexToBracketTerm: {stx}"

/-- Takes a pair ``a b : ℕ × TSyntax `indexExpr``. If `a.1 < b.1` and `a.2 = b.2` then
  outputs `some (a.1, b.1)`, otherwise `none`. -/
def indexPosEq (a b : TSyntax `indexExpr × ℕ) : TermElabM (Option (ℕ × ℕ)) := do
  let a' ← indexToIdent a.1
  let b' ← indexToIdent b.1
  if a.2 < b.2 ∧ Lean.TSyntax.getId a' = Lean.TSyntax.getId b' then
    return some (a.2, b.2)
  else
    return none

/-- Bool which is true if an index is of the form τ(i) that is, to be dualed. -/
def indexToDual (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr| τ($_)) => true
  | _ => false

/-!

## Manipulation of lists of indexExpr

-/



/-- Adjusts a list `List ℕ` by subtracting from each natural number the number
  of elements before it in the list which are less than itself. This is used
  to form a list of pairs which can be used for evaluating indices. -/
def evalAdjustPos (l : List ℕ) : List ℕ :=
  let l' := List.mapAccumr
    (fun x (prev : List ℕ) =>
      let e := prev.countP (fun y => y < x)
      (x :: prev, x - e)) l.reverse []
  l'.2.reverse


/-- Returns the positions of indices which are "jiggled", i.e., of the form `τ(μ)`,
  these are the indices which are to be raised or lowered. -/
def getJigglePos (ind : List (TSyntax `indexExpr)) : TermElabM (List ℕ) := do
  let indEnum := ind.zipIdx
  let evals := indEnum.filter (fun x => indexExprIsJiggle x.1)
  let pos := (evals.map (fun x => x.2))
  return pos

/-- info: [3, 4] -/
#guard_msgs in
#eval show TermElabM _ from do
  let inds : List (TSyntax `indexExpr) := [← `(indexExpr| α), ← `(indexExpr| β),
    ← `(indexExpr| 2), ← `(indexExpr| τ(β)), ← `(indexExpr| τ(γ)), ← `(indexExpr| γ)]
  logInfo m!"{← getJigglePos inds}"


/-- For list of `indexExpr` e.g. `[α, 3, β, 2, γ]`, `getEvalPos`
  returns a list of pairs `ℕ × ℕ` related to indices which are numbers.
  The second element of each pair is the number corresponding to that index.
  The first element is the position of that number in the list of indices when
  all other numbered indices before it are removed. Thus for the example given
  `getEvalPos` outputs `[(1, 3), (2, 2)]`. -/
def getEvalPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × ℕ)) := do
  let indEnum := ind.zipIdx
  let evals := indEnum.filter (fun x => indexExprIsNum x.1)
  let evals2 ← (evals.mapM (fun x => indexToNum x.1))
  let pos := evalAdjustPos (evals.map (fun x => x.2))
  return List.zip pos evals2

/-- For list of `indexExpr` e.g. `[α, 3, β, 2, [γ]]`, `getEvalPos`
  returns a list of pairs `ℕ × Term` related to indices which are evaluated
  e.g. `[μ]`.
  The second element of each pair is the value corresponding to that index.
  The first element is the position of that number in the list of indices when
  all other numbered indices before it are removed. Thus for the example given
  `getEvalBracketPos` outputs `[(4, γ)]`. -/
def getEvalBracketPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × Term)) := do
  let indEnum := ind.zipIdx
  let evals := indEnum.filter (fun x => indexExprIsBracketEval x.1)
  let evals2 ← (evals.mapM (fun x => indexToBracketTerm x.1))
  let pos := evalAdjustPos (evals.map (fun x => x.2))
  return List.zip pos evals2

/-- For list of `indexExpr` e.g. `[α, 3, β, α, 2, γ]`, `getContrPos`
  first removes all indices which are numbers (e.g. `[α, β, α, γ]`).
  It then outputs pairs `(a, b)` in `ℕ × ℕ` of positions of this list with `a < b`
  such that the index at `a` is equal to the index at `b`. It checks whether or not
  an element is contracted more then once. -/
def getContrPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × ℕ)) := do
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x
    ∧ ¬ indexExprIsBracketEval x)
  let indEnum := indFilt.zipIdx
  let bind := List.flatMap (fun a => indEnum.map (fun b => (a, b))) indEnum
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- info: [(1, 2), (3, 4)] -/
#guard_msgs in
#eval show TermElabM _ from do
  let inds : List (TSyntax `indexExpr) := [← `(indexExpr| α), ← `(indexExpr| β),
    ← `(indexExpr| 2), ← `(indexExpr| β), ← `(indexExpr| τ(γ)), ← `(indexExpr| γ)]
  logInfo m!"{← getContrPos inds}"

/-- The list of indices after contraction or evaluation. -/
def withoutContrEval (ind : List (TSyntax `indexExpr)) : TermElabM (List (TSyntax `indexExpr)) := do
  -- Removing the evaluated indices.
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  -- Removing the contracted indices: an index is contracted when its name, ignoring any `τ`,
  -- appears more than once.
  let indFilt := indFilt.filter (fun x => (indFilt.map indexRemoveTau).count (indexRemoveTau x) ≤ 1)
  return indFilt

-- `β` is contracted (appears twice), and `τ(γ)`/`γ` contract with each other (same name up to
-- `τ`), so only the free index `α` remains.
/-- info: [α✝] -/
#guard_msgs in
#eval show TermElabM _ from do
  let inds : List (TSyntax `indexExpr) := [← `(indexExpr| α), ← `(indexExpr| β),
    ← `(indexExpr| 2), ← `(indexExpr| β), ← `(indexExpr| τ(γ)), ← `(indexExpr| γ)]
  logInfo m!"{← withoutContrEval inds}"


/-- Takes a list and puts consecutive elements into pairs.
  e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)]. -/
def toPairs (l : List ℕ) : List (ℕ × ℕ) :=
  match l with
  | x1 :: x2 :: xs => (x1, x2) :: toPairs xs
  | [] => []
  | [x] => [(x, 0)]

/-- Adjusts a list `List (ℕ × ℕ)` by subtracting from each natural number the number
  of elements before it in the list which are less than itself. This is used
  to form a list of pairs which can be used for contracting indices. -/
def contrListAdjust (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (l.mapAccumr
    (fun (x : ℕ × ℕ) (prev : List ℕ) =>
      (x.1 :: x.2 :: prev,
        (x.1 - prev.countP (fun y => y < x.1), x.2 - prev.countP (fun y => y < x.2))))
    []).2

/-!

## Permutations of indices

-/

/-- Given two lists of indices, all of which are identifiers, returns the `List (ℕ)` whose
  `i`th entry is the position in `l2` of the `i`th index in `l1`. -/
def getPermutation (l1 l2 : List (TSyntax `indexExpr)) : TermElabM (List ℕ) := do
  /- Turn every index into an indent. -/
  let l1' ← l1.mapM (fun x => indexToIdent x)
  let l2' ← l2.mapM (fun x => indexToIdent x)
  /- For `l2 = [γ, α, δ, β]`, `l2enum` is `[(γ, 0), (α, 1), (δ, 2), (β, 3)]`. -/
  let l2enum := l2'.zipIdx
  /- For `l1 = [α, β, γ, δ]`, `l1''` is `[(α, 1), (β, 3), (γ, 0), (δ, 2)]`. -/
  let l1'' := l1'.filterMap
    (fun x => l2enum.find? (fun y => Lean.TSyntax.getId y.1 = Lean.TSyntax.getId x))
  return l1''.map fun x => x.2

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToTerm (str : String) : TermElabM Term := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => throwError "Could not create type from string (stringToTerm). "
  | Except.ok stx =>
    match stx with
    | `(term| $e) => return e

/-!

## Syntax for tensor expressions.

-/

/-- A syntax category for tensor expressions. -/
declare_syntax_cat tensorExpr

/-- The syntax for a tensor node. -/
syntax term "|" (ppSpace indexExpr)* : tensorExpr

/-- Equality. -/
syntax:40 tensorExpr "=" tensorExpr:41 : tensorExpr

/-- The syntax for tensor prod two tensor nodes. -/
syntax:70 tensorExpr "⊗" tensorExpr:71 : tensorExpr

/-- The syntax for tensor addition. -/
syntax tensorExpr "+" tensorExpr : tensorExpr

/-- Allowing brackets to be used in a tensor expression. -/
syntax "(" tensorExpr ")" : tensorExpr

/-- Scalar multiplication for tensors. -/
syntax term "•ₜ" tensorExpr : tensorExpr

/-- group action for tensors. -/
syntax term "•ₐ" tensorExpr : tensorExpr

/-- Negation of a tensor tree. -/
syntax "-" tensorExpr : tensorExpr

/-!

## Syntax of tensor expressions to indices.

-/

/-- For syntax of the form `T` where `T` is `Tensor S c` this returns
  the value of `TensorSpecies.numIndices T`. That is, the exact number of indices
  associated with that tensor. -/
def getNumIndicesExact (stx : Syntax) : TermElabM ℕ := do
  match stx with
  | `($t:term) =>
    let a ← elabTerm (← `(Tensorial.numIndices $t)) (some (mkConst ``Nat))
    let a' ← whnf a
    match a' with
    | Expr.lit (Literal.natVal n) =>
      return n
    |_ => throwError s!"Could not extract number of indices from tensor
      {stx} (getNoIndicesExact). "

/-- For syntax of the form `T | α β 2 β `, `getAllIndices` returns a list `[α, β, 2, β]`
  of all `indexExpr`. -/
def getAllIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      let indices ← args.toList.mapM fun arg => do
        match arg with
        | `(indexExpr|$t:indexExpr) => pure t
      return indices
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesNode: {stx}"

-- Tests

/-- info: [α✝, β✝, 2, β✝] -/
#guard_msgs in
#eval show TermElabM _ from do
  logInfo m!"{← getAllIndices (← `(tensorExpr| T | α β 2 β))}"

/-- info: [α✝, β✝, 2, β✝, τ(γ✝)] -/
#guard_msgs in
#eval show TermElabM _ from do
  logInfo m!"{← getAllIndices (← `(tensorExpr| T | α β 2 β τ(γ)))}"

/-!

## Modifying terms to tensor trees

-/
open TensorSpecies

/-- A Tensor expression operator is a map which takes in a pair
  consisting of a list of indices and a term and outputs a list of indices and a term,
  after applying a certain operation.-/
abbrev TensorExpressionOperator :=
  List (TSyntax `indexExpr) × Term → TermElabM (List (TSyntax `indexExpr) × Term)

/-- The creation of a tensor from a syntax tree. -/
def TensorExpressionOperator.create (stx : Syntax) :
    TermElabM (List (TSyntax `indexExpr) × Term) := do
  match stx with
  -- The raw underlying expression.
  | `(tensorExpr| $T:term | $[$args]*) =>
  let indices ← getAllIndices stx
  let rawIndex ← getNumIndicesExact T
  if indices.length ≠ rawIndex then
    throwError "The expected number of indices {rawIndex} does not match the tensor {T}."
  else
    return (indices, Syntax.mkApp (mkIdent ``Tensorial.toTensor) #[T])
  | _ => throwError "Unsupported tensor expression syntax in TensorExpressionOperator.create: {stx}"

/-- The tensor expression operator which rises or lowers the indices of a tensor based on
  indices with `τ`-syntax. -/
def TensorExpressionOperator.jiggle : TensorExpressionOperator := fun (ind, T) => do
  let pos ← getJigglePos ind
  let T' := pos.foldl (fun T' x => Syntax.mkApp (mkIdent ``Tensor.toDualMapAtIndex)
    #[Syntax.mkNumLit (toString x), T']) T
  let ind' := ind.map indexRemoveTau
  return (ind', T')

/-- The tensor expression operator which evaluates indices. -/
def TensorExpressionOperator.eval : TensorExpressionOperator := fun (ind, T) => do
  -- First evaluate the indices which are numbers, e.g. `2` in `T | α β 2 β`.
  let l ← getEvalPos ind
  let T' := l.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``Tensor.evalT)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x2), T']) T
  let ind' : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  -- Then evaluate the indices which are evaluated brackets, e.g. `[μ]` in `T | α β [μ] β`.
  let lBracket ← getEvalBracketPos ind'
  let T'' := lBracket.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``Tensor.evalT)
    #[Syntax.mkNumLit (toString x1), x2, T']) T'
  let ind'' : List (TSyntax `indexExpr) := ind'.filter (fun x => ¬ indexExprIsBracketEval x)
  return (ind'', T'')

/-- The tensor expression operator which contracts indices. -/
def TensorExpressionOperator.contr : TensorExpressionOperator := fun (ind, T) => do
  let l ← getContrPos ind
  let n := ind.length
  let proofTerm := Syntax.mkApp (mkIdent ``Tensor.contrT_decide) #[mkIdent ``rfl]
  let T' := ((contrListAdjust l).reverse.foldl (fun (m, T') (x0, x1) =>
    (m + 2, Syntax.mkApp (mkIdent ``Tensor.contrT)
    #[Syntax.mkNumLit (toString (n - m)), Syntax.mkNumLit (toString x0),
    Syntax.mkNumLit (toString x1), proofTerm, T'])) ((2, T) : ℕ × Term)).2
  let indFilt := ind.filter (fun x => (ind.map indexRemoveTau).count (indexRemoveTau x) ≤ 1)
  return (indFilt, T')

/-- The tensor expression operator which takes the product of two tensors. -/
def TensorExpressionOperator.prod : List (TSyntax `indexExpr) × Term →
    List (TSyntax `indexExpr) × Term →
    TermElabM (List (TSyntax `indexExpr) × Term) := fun (ind1, T1) (ind2, T2) => do
  let ind := ind1 ++ ind2
  let T := Syntax.mkApp (mkIdent ``Tensor.prodT) #[T1, T2]
  return (ind, T)

/-- The tensor expression operator which negates a tensor. -/
def TensorExpressionOperator.neg : TensorExpressionOperator := fun (ind, T) => do
  let T' := Syntax.mkApp (mkIdent ``Neg.neg) #[T]
  return (ind, T')

/-- The tensor expression operator which multiplies a tensor by a scalar. -/
def TensorExpressionOperator.smul (c : Term) : TensorExpressionOperator := fun (ind, T) => do
  let T' := Syntax.mkApp (mkIdent ``HSMul.hSMul) #[c, T]
  return (ind, T')

/-- The tensor expression operator which acts on a tensor by a group element. -/
def TensorExpressionOperator.action (c : Term) : TensorExpressionOperator := fun (ind, T) => do
  let T' := Syntax.mkApp (mkIdent ``HSMul.hSMul) #[c, T]
  return (ind, T')

/-- Whether `T1` and `T2` elaborate to tensors of definitionally equal colour (equal type).
  Used to decide whether an identity reindexing between them may be dropped: the bare,
  un-`permT`'d term is well typed exactly when the two colours agree by `rfl`. The check
  elaborates speculatively and restores the elaborator state afterwards. -/
def colorsDefEq (T1 T2 : Term) : TermElabM Bool := do
  let s ← saveState
  try
    let ty1 ← inferType (← elabTerm T1 none)
    let ty2 ← inferType (← elabTerm T2 none)
    let result ← Meta.isDefEq ty1 ty2
    s.restore
    return result
  catch _ =>
    s.restore
    return false

/-- Wraps `T` in the reindexing `permT ![lPerm] IsReindexing.auto`. -/
def permWrap (lPerm : List ℕ) (T : Term) : TermElabM Term := do
  let permString := "![" ++ String.intercalate ", " (lPerm.map toString) ++ "]"
  let P ← stringToTerm permString
  return Syntax.mkApp (mkIdent ``Tensor.permT) #[P, mkIdent ``IsReindexing.auto, T]

/-- The tensor expression operator which adds two tensors. -/
def TensorExpressionOperator.add : List (TSyntax `indexExpr) × Term →
    List (TSyntax `indexExpr) × Term →
    TermElabM (List (TSyntax `indexExpr) × Term) := fun (ind1, T1) (ind2, T2) => do
  let lPerm ← getPermutation ind1 ind2
  let T2' ← permWrap lPerm T2
  let addSyntax : Term :=
    if lPerm = List.range lPerm.length ∧ (← colorsDefEq T1 T2) then
        Syntax.mkApp (mkIdent ``HAdd.hAdd) #[T1, T2]
    else
      Syntax.mkApp (mkIdent ``HAdd.hAdd) #[T1, T2']
  return (ind1, addSyntax)

/-- The tensor expression operator which equates two tensors. -/
def TensorExpressionOperator.equal : List (TSyntax `indexExpr) × Term →
    List (TSyntax `indexExpr) × Term →
    TermElabM (List (TSyntax `indexExpr) × Term) := fun (ind1, T1) (ind2, T2) => do
  let lPerm ← getPermutation ind1 ind2
  let T2' ← permWrap lPerm T2
  let equalSyntax : Term :=
    if lPerm = List.range lPerm.length ∧ (← colorsDefEq T1 T2) then
        Syntax.mkApp (mkIdent ``Eq) #[T1, T2]
    else
      Syntax.mkApp (mkIdent ``Eq) #[T1, T2']
  return (ind1, equalSyntax)

/-!

## Syntax to tensor tree

-/

/-- Takes a syntax corresponding to a tensor expression and turns it into a
  term corresponding to a tensor tree. -/
partial def syntaxFull (stx : Syntax) : TermElabM (List (TSyntax `indexExpr) × Term) := do
  match stx with
  -- The raw underlying expression.
  | `(tensorExpr| $_:term | $[$args]*) =>
      let (ind, T) ← TensorExpressionOperator.create stx
      let (ind, T) ← TensorExpressionOperator.jiggle (ind, T)
      let (ind, T) ← TensorExpressionOperator.eval (ind, T)
      let (ind, T) ← TensorExpressionOperator.contr (ind, T)
      return (ind, T)
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let (ind, T) ← TensorExpressionOperator.prod (← syntaxFull a) (← syntaxFull b)
      let (ind, T) ← TensorExpressionOperator.contr (ind, T)
      return (ind, T)
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← syntaxFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return ← TensorExpressionOperator.neg (← syntaxFull a)
  | `(tensorExpr| $c:term •ₜ $a:tensorExpr) => do
      return ← TensorExpressionOperator.smul c (← syntaxFull a)
  | `(tensorExpr| $c:term •ₐ $a:tensorExpr) => do
      return ← TensorExpressionOperator.action c (← syntaxFull a)
  | `(tensorExpr| $a + $b) => do
      return ← TensorExpressionOperator.add (← syntaxFull a) (← syntaxFull b)
  | `(tensorExpr| $a:tensorExpr = $b:tensorExpr) => do
      return ← TensorExpressionOperator.equal (← syntaxFull a) (← syntaxFull b)
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

/-!

## Elaboration

-/

/-- Removes redundant `Tensorial.toTensor` coercions from an elaborated tensor expression:
  every subterm `Tensorial.toTensor t` whose `Tensorial` instance is the canonical instance
  on `S.Tensor c` (`Tensorial.self`) is replaced by `t` itself, since there the coercion is
  the identity. Coercions coming from genuine tensorial instances (e.g. on Lorentz vectors)
  carry real information and are left untouched. -/
def stripToTensorSelf (e : Expr) : Expr :=
  e.replace fun s => do
    guard (s.isAppOf ``DFunLike.coe)
    guard (s.getAppNumArgs ≥ 2)
    let f := s.appFn!.appArg!
    guard (f.isAppOf ``Tensorial.toTensor)
    guard (f.appArg!.isAppOf ``Tensorial.self)
    return s.appArg!

/-- Takes a syntax corresponding to a tensor expression and turns it into an
  expression corresponding to a tensor tree. The redundant `Tensorial.toTensor` coercions
  inserted for bare `S.Tensor` terms are removed via `stripToTensorSelf`. -/
def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  let T' ← syntaxFull stx
  let tensorExpr ← elabTerm T'.2 none
  return stripToTensorSelf (← instantiateMVars tensorExpr)

/-- The tensor tree corresponding to a tensor expression. -/
syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

/-!

## Test cases

We pin the elaboration of the `{ … }ᵀ` notation for each construct it supports: bare tensor
nodes, a genuine `Tensorial` instance, negation, evaluation, scalar multiplication, the group
action, products, contractions, addition and equality. Together these check that the elaborator
inserts neither a redundant `Tensorial.toTensor` wrapper on a bare `S.Tensor` term nor an
identity `permT` when the two sides already align, while keeping the `toTensor` coercion of a
genuine `Tensorial` instance and a genuine `permT` for a real reindexing.

-/
section Tests
variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
    {c : Fin 2 → C} {t t' : S.Tensor c} (a : k) (g : G) (y : basisIdx (c 0))
    {c1 c2 c3 : C} {u : S.Tensor ![c1, c2]} {u' : S.Tensor ![c2, c1]}
    {w : S.Tensor ![c3]} {td : S.Tensor ![S.τ c1, S.τ c2]}
    {M : Type} [AddCommMonoid M] [Module k M] [Tensorial S c M] (m : M)

-- A bare `S.Tensor` carries no redundant `Tensorial.toTensor` wrapper.
/-- info: t : S.Tensor c -/
#guard_msgs in
#check {t | α β}ᵀ

-- A genuine `Tensorial` instance (here the abstract `m : M`) keeps its `toTensor` coercion.
/-- info: Tensorial.toTensor m : S.Tensor c -/
#guard_msgs in
#check {m | α β}ᵀ

-- Negation of a tensor expression.
/-- info: -t : S.Tensor c -/
#guard_msgs in
#check {-(t | α β)}ᵀ

-- Evaluation of an index at a basis value `[y]`.
/-- info: (evalT 0 y) t : S.Tensor (c ∘ Fin.succAbove 0) -/
#guard_msgs in
#check {t | [y] β}ᵀ

-- Scalar multiplication `•ₜ`.
/-- info: a • t : S.Tensor c -/
#guard_msgs in
#check {a •ₜ t | α β}ᵀ

-- Group action `•ₐ`.
/-- info: g • t : S.Tensor c -/
#guard_msgs in
#check {g •ₐ t | α β}ᵀ

-- Tensor product of two tensors with no shared indices.
/-- info: (prodT u) w : S.Tensor (Fin.append ![c1, c2] ![c3]) -/
#guard_msgs in
#check {u | α β ⊗ w | γ}ᵀ

-- Contraction of both index pairs of a product.
/--
info: (contrT 0 0 1 ⋯) ((contrT 2 1 3 ⋯) ((prodT u) td)) :
  S.Tensor ((Fin.append ![c1, c2] ![S.τ c1, S.τ c2] ∘ Fin.succSuccAbove 1 3) ∘
  Fin.succSuccAbove 0 1)
-/
#guard_msgs (whitespace := lax) in
#check {u | α β ⊗ td | α β}ᵀ

-- Addition with aligned indices: no redundant identity `permT` (nor `toTensor`).
/-- info: t + t' : S.Tensor c -/
#guard_msgs in
#check ({t | α β + t' | α β}ᵀ)

-- Equality with aligned indices: no redundant identity `permT`.
/-- info: t = t' : Prop -/
#guard_msgs in
#check ({t | α β = t' | α β}ᵀ : Prop)

-- Equality with reordered indices: a genuine `permT` reindexing is inserted.
/-- info: u = (permT ![1, 0] ⋯) u' : Prop -/
#guard_msgs in
#check ({u | α β = u' | β α}ᵀ : Prop)

variable {V3 : Fin 3 → Type} [∀ c, AddCommGroup (V3 c)] [∀ c, Module k (V3 c)]
    {basisIdx3 : Fin 3 → Type} [∀ c, Fintype (basisIdx3 c)]
    [∀ c, DecidableEq (basisIdx3 c)]
    {rep3 : (c : Fin 3) → Representation k G (V3 c)}
    {b3 : (c : Fin 3) → Module.Basis (basisIdx3 c) k (V3 c)}
    {S3 : TensorSpecies k (Fin 3) G V3 basisIdx3 rep3 b3}
    {v3 : S3.Tensor ![0, 1, 2]} {v3' : S3.Tensor ![1, 2, 0]}

-- A non-involutive reordering uses the map from target slots to source slots.
/-- info: v3 = (permT ![2, 0, 1] ⋯) v3' : Prop -/
#guard_msgs in
#check ({v3 | α β γ = v3' | β γ α}ᵀ : Prop)

/-- info: v3 + (permT ![2, 0, 1] ⋯) v3' : S3.Tensor ![0, 1, 2] -/
#guard_msgs in
#check ({v3 | α β γ + v3' | β γ α}ᵀ)

variable {k : Type} [RCLike k] {C : Type} [DecidableEq C]  {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b} [S.WithMetric]
    {c : Fin 2 → C} {t t' : S.Tensor c} (a : k) (g : G) (y : basisIdx (c 0))
    {c1 c2 c3 : C} {u : S.Tensor ![c1, c2]} {u' : S.Tensor ![c2, c1]}
    {w : S.Tensor ![c3]} {td : S.Tensor ![S.τ c1, S.τ c2]}
    {M : Type} [AddCommMonoid M] [Module k M] [Tensorial S c M] (m : M)

/-- info: (toDualMapAtIndex 0) u :
  S.Tensor (Function.update ![c1, c2] 0 (S.τ (![c1, c2] 0))) -/
#guard_msgs (whitespace := lax) in
#check {u | τ(α) β}ᵀ

/-- info: (contrT 2 1 3 ⋯)
  ((prodT u) ((toDualMapAtIndex 1) u)) :
    S.Tensor (Fin.append ![c1, c2]
      (Function.update ![c1, c2] 1 (S.τ (![c1, c2] 1))) ∘ Fin.succSuccAbove 1 3) -/
#guard_msgs (whitespace := lax) in
#check {u | γ β ⊗ u | α τ(β)}ᵀ

end Tests

end Tensor

end TensorSpecies
