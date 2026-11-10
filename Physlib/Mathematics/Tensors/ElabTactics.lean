/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Elab
/-!

# Tactics for index notation

Tactics that prove equations of tensors written in the index notation `{…}ᵀ`.

## i. Overview

Three tactics prove equations written in index notation. `tensor_components` works on the
components, `tensor_regroup` on the contractions and `tensor_slots` on the lowerings and raisings.
Examples are in `Physlib.Mathematics.Tensors.ElabExamples`.

## ii. Key results

- `tensor_components` : reduces an equation of tensors to an equation of their components.
- `tensor_regroup` : proves an equation of two sums of contractions of the same factors, grouped
  or ordered differently, with the same signs and scalars, up to deltas, inverse pairs of forms,
  swaps of symmetric and antisymmetric forms, and lowerings written as contractions. With
  `using e₁, …`, it first rewrites a sub-product of either side by each identity `eᵢ`.
- `tensor_slots` : proves an equation of two chains of lowerings and raisings of the same tensor.

## iii. Table of contents

- A. Components
- B. Reading and rewriting the goal
- C. Matching the factors of two contractions
- D. Deltas and forms
- E. Sums, signs and scalars
- F. Chains of lowerings and raisings
- G. Rewriting a sub-product by an identity

## iv. References

-/

public meta section

open Lean Meta Elab Term

namespace Tensors.Notation

/-!

## A. Components

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
      try dsimp +instances only [ColorEquiv.toEquiv_symm, Equiv.symm_symm, Equiv.coe_fn_mk,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, Function.comp_apply,
        Tensors.Notation.reduceCast])

/-!

## B. Reading and rewriting the goal

-/

open Tactic

/-- The type and the two sides of the goal of the tactic `tac`, an equation. -/
private def goalEq (tac : String := "tensor_regroup") : TacticM (Expr × Expr × Expr) := do
  let some (ty, l, r) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "{tac}: the goal is not an equation"
  return (ty, l.consumeMData, r.consumeMData)

/-- The argument `x` of `F x`, for a bundled map `F` whose head is the constant `f`, such as
`Tensor.contr σ` for `f = Tensor.contr`. -/
private def bundledArg? (f : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``DFunLike.coe 6 && e.appFn!.appArg!.isAppOf f then some e.appArg! else none

/-- Writes each side `x` of the goal on which `p` fails as `F x`, by the term `h : F x = x`. -/
private def wrapSides (tac : String) (p : Expr → Bool) (h : Term) : TacticM Unit := do
  let (_, l, r) ← goalEq tac
  unless p l do evalTactic (← `(tactic| refine (Eq.symm $h).trans ?_))
  unless p r do evalTactic (← `(tactic| refine Eq.trans ?_ $h))

/-- Whether `a` and `b` are definitionally equal, without assigning metavariables of the goal. -/
private def isDefEqGoal (a b : Expr) : MetaM Bool := withNewMCtxDepth (isDefEq a b)

/-- Whether the factors `a` and `b` are equal up to instances, as in `rw`, so that a named tensor
is never unfolded into the contraction that defines it. -/
private def isEqFactor (a b : Expr) : MetaM Bool :=
  withNewMCtxDepth (withTransparency .instances (isDefEq a b))

/-- Runs `f x` for each `x` of `xs` in turn, each from the current state, and returns the result of
the first that succeeds. When every one fails it throws the last error, and `err` when `xs` is
empty. -/
private def firstSuccess {α β : Type} (xs : List α) (err : MessageData) (f : α → TacticM β) :
    TacticM β := do
  let s ← saveState
  let mut err := err
  for x in xs do
    try return ← f x
    catch e => s.restore; err := e.toMessageData
  throwError err

/-- The number of trailing arguments of `e` that are the tensors it is built from: the argument of
a bundled map, the two factors of `T ⊗ₜ U`, the two summands of a sum, and the tensor of a negative
or of a scalar multiple. -/
private def tensorArgs (e : Expr) : Nat :=
  if e.isAppOf ``TensorProduct.tmul || e.isAppOfArity ``HAdd.hAdd 6 then 2
  else if e.isAppOfArity ``DFunLike.coe 6 || e.isAppOfArity ``Neg.neg 3 ||
    e.isAppOfArity ``HSMul.hSMul 6 then 1
  else 0

/-- The tensors that `e` is built from, from left to right, through the arguments of
`tensorArgs`. -/
private partial def tensorLeaves (e : Expr) : List Expr :=
  let e := e.consumeMData
  let args := e.getAppArgs
  match tensorArgs e with
  | 0 => [e]
  | n => (args.toList.drop (args.size - n)).flatMap tensorLeaves

/-- The expression `e` with its leaf `k` of `tensorLeaves e` replaced by `v` if it is `x`, and `k`
less the number of leaves of `e`. -/
private partial def replaceLeaf (x v e : Expr) (k : Int) : Expr × Int :=
  let e := e.consumeMData
  let n := tensorArgs e
  if k < 0 then (e, k)
  else if n == 0 then (if k == 0 && e == x then v else e, k - 1)
  else
    let args := e.getAppArgs
    let (args, k) := (List.range n).foldl (init := (args, k)) fun (args, k) i =>
      let j := args.size - n + i
      let (a, k) := replaceLeaf x v args[j]! k
      (args.set! j a, k)
    (mkAppN e.getAppFn args, k)

/-- Rewrites the subterm `x` of the goal by the term `thm : x' = y`, where `x'` is `x` up to
unfolding instances, as in `rw`: on the left side only if `lhs = some true`, on the right side only
if `lhs = some false`, and only at the leaf `k` of the tensor leaves of the two sides
(`tensorLeaves`) if `k` is given. Unlike `rw`, it finds `x` by syntactic equality and does not check
the type of the whole goal, which on large products is slow. -/
private def rewriteSubterm (x : Expr) (thm : Term) (lhs : Option Bool := none)
    (k : Option Nat := none) : TacticM Unit := do
  let (_, l, r) ← goalEq
  -- As in `rw`, the arguments of `thm` left open, such as `rfl`, are elaborated after `x` fixes
  -- the implicit arguments.
  let h ← Tactic.elabTerm thm none (mayPostpone := true)
  let some (_, x', _) := (← instantiateMVars (← inferType h)).eq?
    | throwError "tensor_regroup: internal error, {thm} is not an equation"
  unless ← withTransparency .instances (isDefEq x x') do
    throwError "tensor_regroup: {thm} does not rewrite{indentExpr x}"
  Term.synthesizeSyntheticMVarsNoPostponing
  let motive ← withLocalDeclD `x (← inferType x) fun v => do
    let (l, r) := match k with
      | none =>
        let replace (e : Expr) := e.replace fun e => if e == x then some v else none
        (if lhs != some false then replace l else l, if lhs != some true then replace r else r)
      | some k =>
        let (l', k) := if lhs != some false then replaceLeaf x v l k else (l, k)
        (l', if lhs != some true then (replaceLeaf x v r k).1 else r)
    mkLambdaFVars #[v] (← mkEq l r)
  let pf ← mkCongrArg motive (← instantiateMVars h)
  let some (_, _, target) := (← inferType pf).eq? | throwError "tensor_regroup: internal error"
  replaceMainGoal [← (← getMainGoal).replaceTargetEq target.headBeta pf]

/-!

## C. Matching the factors of two contractions

-/

/-- The two factors `T` and `U` of a product `S.tmulEquiv c₁ c₂ (T ⊗ₜ U)`. -/
private def productFactors? (e : Expr) : Option (Expr × Expr) := do
  let x := (← bundledArg? ``Tensors.Species.tmulEquiv e).consumeMData
  if x.isAppOf ``TensorProduct.tmul then some (x.appFn!.appArg!, x.appArg!) else none

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

/-- Whether every product inside the product `e` is in its left factor. -/
private partial def isLeftNested (e : Expr) : Bool :=
  match productFactors? e with
  | some (a, b) => (productFactors? b).isNone && isLeftNested a
  | none => true

/-- The products `P` and `Q` of a goal `Tensor.contr σ P = Tensor.contr τ Q`. -/
private def contractedProducts : TacticM (Expr × Expr) := do
  let (_, l, r) ← goalEq
  let some p := bundledArg? ``Tensors.Species.Tensor.contr l
    | throwError "tensor_regroup: the left side is not a contraction"
  let some q := bundledArg? ``Tensors.Species.Tensor.contr r
    | throwError "tensor_regroup: the right side is not a contraction"
  return (p, q)

/-- Writes both sides of the goal as one contraction of a left-nested product, repeating until the
goal no longer changes, at most ten times. A side that is not a contraction is read as one with no
pairs (`Species.Tensor.contr_noPairs`). The three steps run separately, since together their lemmas
loop. -/
private def flattenContractions : TacticM Unit := do
  wrapSides "tensor_regroup" (bundledArg? ``Tensors.Species.Tensor.contr · |>.isSome)
    (← `(Tensors.Species.Tensor.contr_noPairs _))
  for _ in [0:10] do
    let before ← instantiateMVars (← getMainTarget)
    evalTactic (← `(tactic| try simp only [Tensors.Species.Tensor.tmulEquiv_contr_left,
      Tensors.Species.Tensor.tmulEquiv_contr_right, Tensors.Species.Tensor.contr_contr]))
    evalTactic (← `(tactic| try simp only [← Tensors.Species.tmulEquiv_assoc]))
    evalTactic (← `(tactic| try simp only [Tensors.Species.tmulEquiv_reindex_left,
      Tensors.Species.tmulEquiv_reindex_right, Tensors.Species.reindex_reindex,
      Tensors.Species.Tensor.contr_reindex, Tensors.Species.Tensor.reindex_contr]))
    -- The two sides may become equal, and `simp` then closes the goal.
    if (← getGoals).isEmpty then return
    if (← instantiateMVars (← getMainTarget)) == before then return
  throwError "tensor_regroup: flattening the products did not stop after ten rounds"

/-- Swaps the factors `m` and `m + 1` of the product `q`, of `n` factors, on the right side of the
goal, by `Species.tmulEquiv_comm` or `Species.tmulEquiv_swapLast`, and absorbs the relabeling into
the contraction. -/
private def swapFactors (q : Expr) (n m : Nat) : TacticM Unit := do
  let fs := factors q
  let thm ← if m = 0 then
      `((Tensors.Species.tmulEquiv_comm _ _ $(← exprToSyntax fs[1]!)
        $(← exprToSyntax fs[0]!)).symm)
    else
      `((Tensors.Species.tmulEquiv_swapLast $(← exprToSyntax (leadingProduct q n m))
        $(← exprToSyntax fs[m]!) $(← exprToSyntax fs[m+1]!)).symm)
  rewriteSubterm (leadingProduct q n (m + 2)) thm (some false)
  evalTactic (← `(tactic| conv_rhs => simp only [Tensors.Species.tmulEquiv_reindex_left,
    Tensors.Species.reindex_reindex, Tensors.Species.Tensor.contr_reindex]))

/-- The ways to match each factor on the left with a different factor on the right, given for
each factor on the left the factors on the right equal to it. The matching in order comes first. -/
private partial def matchings : List (List Nat) → List Nat → List (List Nat)
  | [], _ => [[]]
  | c :: cs, used =>
    (c.filter (!used.contains ·)).flatMap fun j => (matchings cs (j :: used)).map (j :: ·)

/-- Orders the factors on the right side of the goal so that the factor at each position `k` is
the one that started at position `target[k]`, by swapping neighbours. -/
private def arrange (target : List Nat) : TacticM Unit := do
  let n := target.length
  -- The starting positions of the factors in their current order.
  let mut labels := List.range n
  for pos in (List.range n).reverse do
    for m in [labels.idxOf target[pos]!:pos] do
      swapFactors (← contractedProducts).2 n m
      labels := (labels.set m labels[m+1]!).set (m+1) labels[m]!

/-- The largest number of matchings of equal factors that `matchFactors` tries, so that a false goal
fails within the default heartbeats. -/
private def maxMatchings : Nat := 12

/-- Proves `Tensor.contr σ P = Tensor.contr τ Q` for two flattened contractions of the same
factors. It orders the factors of the right side as on the left, and checks by evaluation that both
sides keep the same slots and contract the same pairs of slots
(`Species.Tensor.contr_eq_of_samePair`). When a factor appears more than once, each way of
matching the equal factors is tried in turn, at most `maxMatchings` of them. -/
private def matchFactors : TacticM Unit := do
  let (p, q) ← contractedProducts
  unless isLeftNested p && isLeftNested q do
    throwError "tensor_regroup: a side is not a left-nested product after flattening"
  let ps := factors p
  let qs := factors q
  unless ps.length = qs.length do
    throwError "tensor_regroup: the two sides have different numbers of factors"
  let candidates ← ps.mapM fun x => (List.range qs.length).filterM fun j => isEqFactor x qs[j]!
  if let some (x, _) := (ps.zip candidates).find? (·.2.isEmpty) then
    throwError "tensor_regroup: the factor{indentExpr x}\nhas no equal factor on the right"
  let targets := matchings candidates []
  if targets.isEmpty then
    throwError "tensor_regroup: a factor appears more often on the left than on the right"
  let tried := if targets.length ≤ maxMatchings then m!"each way" else
    m!"the first {maxMatchings} of the {targets.length} ways"
  firstSuccess (targets.take maxMatchings) m!"" fun target => do
    arrange target
    -- The slots are a nested sum, whose `DecidableEq` instance exceeds the default size. The
    -- checks are run by `of_decide_eq_true rfl` rather than `decide`, which rejects the free
    -- color variables of the goal although the bijections of slots do not depend on them.
    try evalTactic (← `(tactic| set_option synthInstance.maxSize 4096 in
      exact Tensors.Species.Tensor.contr_eq_of_samePair _ _ (of_decide_eq_true rfl)
        (of_decide_eq_true rfl) _))
    catch _ => throwError "tensor_regroup: the two sides contract different pairs of slots, for \
      {tried} of matching their equal factors"

/-!

## D. Deltas and forms

-/

/-- The factors among `xs` that are left over once each factor of `ys` takes an equal factor of
`xs`. -/
private def leftover (xs ys : List Expr) : MetaM (List Expr) := do
  let mut rest := xs
  for y in ys do
    if let some i ← (List.range rest.length).findM? fun i => isEqFactor rest[i]! y then
      rest := rest.eraseIdx i
  return rest

/-- The color `a` of a delta `S.deltaTensor a`. -/
private def deltaColor? (x : Expr) : Option Expr :=
  let x := x.consumeMData
  if x.isAppOf ``Tensors.Species.deltaTensor then some x.appArg! else none

/-- The species `S` and the color `c` of a form `S.formTensor c`. -/
private def formArgs? (x : Expr) : Option (Expr × Expr) :=
  let x := x.consumeMData
  if x.isAppOf ``Tensors.Species.formTensor then
    let args := x.getAppArgs
    some (args[args.size - 3]!, args[args.size - 2]!)
  else none

/-- Inserts a delta of color `a` at the slot `slot` of the product of the left side of the goal,
if `lhs`, or of the right side, by `T^…μ… = T^…ν… δ_ν^μ` (`Species.Tensor.contr_deltaTensor`). -/
private def insertDelta (lhs : Bool) (a : Expr) (slots : Slots) (slot : Nat) : TacticM Unit := do
  let (p, q) ← contractedProducts
  let P := if lhs then p else q
  let thm ← `((Tensors.Species.Tensor.contr_deltaTensor
    ($(← slots.elem slot) : $(← slots.type)) $(← exprToSyntax a) rfl $(← exprToSyntax P)).symm)
  rewriteSubterm P thm (some lhs)

mutual

/-- Inserts a delta of color `a` on the left side, if `lhs`, or on the right side, at each slot of
the product of color `a` in turn, and proves the goal by `regroupContractions`. With `skipForms`,
the slots of forms are left out when another factor has a slot: inserting the delta anywhere along a
chain of contracted forms gives the same factors, so trying each of their slots only repeats the
search. -/
private partial def insertDeltaAnywhere (lhs : Bool) (a : Expr) (skipForms : Bool := false) :
    TacticM Unit := do
  let (p, q) ← contractedProducts
  let P := if lhs then p else q
  let some (slots, _, colors) ← literalTensorType? (← inferType P)
    | throwError "tensor_regroup: the slots or colors of a product are not literal"
  -- Whether each slot belongs to a form, from the number of slots of each factor in turn.
  let inForm ← (factors P).flatMapM fun f => do
    let n := ((← literalTensorType? (← inferType f)).map (·.2.2.length)).getD 0
    return List.replicate n (skipForms && (formArgs? f).isSome)
  -- shortcut: misses a chain of forms that reaches no other factor, as `T^μ_ν g^αβ` against
  -- `T^μ_ν g^αγ g_γδ g^δβ`; trying the slots of forms after the others would cover it.
  let inForm := if inForm.all id then inForm.map fun _ => false else inForm
  let slotsOfColor ← colors.zipIdx.filterM fun (col, i) =>
    return !inForm.getD i false && (← isDefEqGoal col a)
  firstSuccess (slotsOfColor.map (·.2)) m!"tensor_regroup: no slot has the color {a} of a delta"
    fun slot => do
      insertDelta lhs a slots slot
      regroupContractions

/-- Matches pairs of forms `g` and `g⁻¹`, the factors `gs` left over on one side, with the factors
`ds` left over on the left side, if `lhs`, or on the right side. A delta `ds = [δ]` is written as
the contraction of two forms, `g^μν g_νρ = δ^μ_ρ` (`Species.contr_formTensor_formTensor`), trying
the color of each form whose dual form is also left over. With `ds = []`, a delta is inserted
first. Each pair cancelled this way, as a lowering `g_μν` against a raising form `g^νρ`, leaves the
other pairs to the next round of `regroupContractions`. -/
private partial def matchFormPair (lhs : Bool) (ds gs : List Expr) : TacticM Unit := do
  let fs := gs.filterMap formArgs?
  unless 2 ≤ gs.length && gs.length % 2 == 0 && fs.length == gs.length do
    throwError "tensor_regroup: the factors left over are not pairs of forms"
  -- Only the colors whose dual form is also left over can cancel, each tried once.
  let fs ← fs.eraseDups.filterM fun (_, c) => do
    let cd ← mkAppM ``Tensors.Color.dual #[c]
    fs.anyM fun (_, c') => isDefEqGoal c' cd
  match ds with
  | [d] =>
    unless (deltaColor? d).isSome do throwError "tensor_regroup: {d} is not a delta"
    firstSuccess fs m!"tensor_regroup: no two forms left over are inverse" fun (S, c) => do
      let thm ← `((Tensors.Species.contr_formTensor_formTensor (S := $(← exprToSyntax S))
        $(← exprToSyntax c)).symm)
      rewriteSubterm d thm (some lhs)
      regroupContractions
  | [] => firstSuccess fs m!"tensor_regroup: no two forms left over are inverse" fun (_, c) => do
      insertDeltaAnywhere lhs (← mkAppM ``Tensors.Color.dual #[c]) (skipForms := true)
  | _ => throwError "tensor_regroup: more than one factor is left over against forms"

/-- Proves `Tensor.contr σ P = Tensor.contr τ Q` for two contractions of the same factors, up to
deltas and inverse pairs of forms. Each side is flattened to one contraction of a left-nested
product. Two forms on one side with a delta or nothing left over on the other are matched by
`matchFormPair`. A delta on one side with no counterpart on the other is inserted on the other side
at each slot of its color in turn, since contracting with a delta is a relabeling. The factors are
then matched by `matchFactors`. -/
private partial def regroupContractions : TacticM Unit := do
  flattenContractions
  if (← getGoals).isEmpty then return
  let (p, q) ← contractedProducts
  let extraL ← leftover (factors p) (factors q)
  let extraR ← leftover (factors q) (factors p)
  -- The error reported in place of the count of factors when forms are left over on one side.
  let mut formErr : Option MessageData := none
  for (lhs, ds, gs) in [(true, extraL, extraR), (false, extraR, extraL)] do
    try matchFormPair lhs ds gs; return catch _ =>
    if 2 ≤ gs.length && gs.all (formArgs? · |>.isSome) then
      formErr := m!"tensor_regroup: the forms left over on one side do not cancel in inverse pairs \
        against the other side{indentD (MessageData.joinSep (gs.map toMessageData) "\n")}"
  -- A delta left over on the right is inserted on the left, and conversely.
  match extraL.mapM deltaColor?, extraR.mapM deltaColor? with
  | some _, some (a :: _) => insertDeltaAnywhere true a
  | some (a :: _), some [] => insertDeltaAnywhere false a
  | _, _ => try matchFactors catch e => throwError (formErr.getD e.toMessageData)

end

/-!

## E. Sums, signs and scalars

-/

/-- Brings both sides of the goal to sums of signed scalar multiples of contractions. Products,
contractions and relabelings are linear, so sums, negatives and scalars of `k` move out of them.
The scalar lemmas are given the field `k` of the species, so a group element `Λ • T` stays a
factor. -/
private def normalizeSums : TacticM Unit := do
  let (ty, _, _) ← goalEq
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

/-- Rewrites the form `F = S.formTensor c` at the tensor leaf `k` of the goal by its swap,
`g^μν = -g^νμ` for an antisymmetric form (`Species.formTensor_antisymm`), if `antisym`, and
`g^μν = g^νμ` for a symmetric one (`Species.formTensor_symm`). -/
private def flipForm (antisym : Bool) (F : Expr) (k : Nat) : TacticM Unit := do
  let some (S, c) := formArgs? F | throwError "tensor_regroup: internal error, {F} is not a form"
  let (S, c) := (← exprToSyntax S, ← exprToSyntax c)
  let thm ← if antisym then
      `(neg_eq_iff_eq_neg.mp (Tensors.Species.formTensor_antisymm (S := $S) $c).symm)
    else `((Tensors.Species.formTensor_symm (S := $S) $c).symm)
  rewriteSubterm F thm (k := some k)

mutual

/-- Proves an equation of two summands with the same sign and the same scalar, by regrouping the
contractions they multiply. When exactly one side is negated, one antisymmetric form on either
side is swapped first, as in `ε^αβ = -ε^βα`. When the regrouping fails, one symmetric form is
swapped, as in `η^μν = η^νμ`. At most one form is swapped. -/
private partial def regroupSummand (flipped : Bool := false) : TacticM Unit := do
  let (_, l, r) ← goalEq
  let negL := l.isAppOfArity ``Neg.neg 3
  let negR := r.isAppOfArity ``Neg.neg 3
  if negL && negR then
    evalTactic (← `(tactic| refine congrArg Neg.neg ?_))
    regroupSummand flipped
  else if negL != negR && !flipped then
    flipOneForm true
  else if l.isAppOfArity ``HSMul.hSMul 6 && r.isAppOfArity ``HSMul.hSMul 6 then
    let a := l.appFn!.appArg!
    unless ← isDefEqGoal a r.appFn!.appArg! do
      throwError "tensor_regroup: the scalars {a} and {r.appFn!.appArg!} differ"
    evalTactic (← `(tactic| refine congrArg (HSMul.hSMul $(← exprToSyntax a)) ?_))
    regroupSummand flipped
  else
    try evalTactic (← `(tactic| with_reducible rfl)) catch _ =>
    let s ← saveState
    try regroupContractions catch e =>
      if flipped then throw e
      -- The two sides may differ by the swap of a symmetric form.
      s.restore
      try flipOneForm false catch _ => s.restore; throw e

/-- Tries each form among the tensor leaves of the goal for `flipForm antisym`, then moves a new
sign out and regroups. A form of the other symmetry fails at `flipForm`. -/
private partial def flipOneForm (antisym : Bool) : TacticM Unit := do
  let (_, l, r) ← goalEq
  let leaves := tensorLeaves l ++ tensorLeaves r
  let s ← saveState
  let mut lastError : MessageData := m!"tensor_regroup: no form to swap"
  for F in (leaves.filter (formArgs? · |>.isSome)).eraseDups do
    for k in (List.range leaves.length).filter (leaves[·]! == F) do
      s.restore
      try flipForm antisym F k catch _ => break
      try
        normalizeSums
        regroupSummand true
        return
      catch e => lastError := e.toMessageData
  s.restore
  throwError lastError

end

/-- A proof of `e = e'` for a sum `e`, where `e'` replaces the summands of `e` from left to right
by the right sides of the proofs `hs`. The proofs left over are returned. -/
private partial def sumCongr (e : Expr) (hs : List Expr) : MetaM (Expr × List Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (p, hs) ← sumCongr e.appFn!.appArg! hs
    let (q, hs) ← sumCongr e.appArg! hs
    return (← mkCongr (← mkCongrArg e.appFn!.appFn! p) q, hs)
  match hs with
  | h :: hs => return (h, hs)
  | [] => throwError "tensor_regroup: internal error, too few summand proofs"

/-- The position among `rs`, outside `used`, of a summand equal to `a` of type `ty` by
`regroupSummand`, with the proof of the equation. -/
private def matchSummand (ty a : Expr) (rs : List Expr) (used : List Nat) :
    TacticM (Nat × Expr) := do
  let js := (List.range rs.length).filter (!used.contains ·)
  try
    firstSuccess js m!"" fun j => do
      -- The type of the tensors is taken from the goal, where it is `S.Tensor c`.
      let g ← mkFreshExprMVar (mkApp3 (.const ``Eq [← getLevel ty]) ty a rs[j]!)
      setGoals [g.mvarId!]
      regroupSummand
      unless (← getGoals).isEmpty do throwError "tensor_regroup: a summand is not closed"
      return (j, ← instantiateMVars g)
  catch _ =>
    throwError "tensor_regroup: the summand{indentExpr a}\nhas no matching summand on the right"

/-- The body of `tensor_regroup`: moves sums, negatives and scalars out, then proves the equation
summand by summand. -/
private def regroup : TacticM Unit := do
  normalizeSums
  -- Moving the scalars out may already close the goal.
  if (← getGoals).isEmpty then return
  let (ty, l, r) ← goalEq
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
  let mut proofs : Array Expr := #[]
  for a in ls do
    let (j, pf) ← matchSummand ty a rs used
    used := j :: used
    proofs := proofs.push pf
  -- The summands are replaced by congruence, not by `rw`: a summand can occur inside another one,
  -- as `T` inside its relabeling.
  let (pf, _) ← sumCongr l proofs.toList
  let some (_, _, l') := (← inferType pf).eq? | throwError "tensor_regroup: internal error"
  let rest ← mkFreshExprMVar (← mkEq l' r)
  main.assign (← mkEqTrans pf rest)
  setGoals [rest.mvarId!]
  evalTactic (← `(tactic| first | with_reducible rfl | abel))

/-- Whether `e` contains a lowering or raising `S.toDualAt`. -/
private def hasLowering (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Tensors.Species.toDualAt)).isSome

/-- The body of `tensor_regroup`: `regroup`, and again after writing lowerings and raisings as
contractions with the form (`Species.toDualAt_eq_contr`) when it fails and the goal has one. When
both fail, the first error is reported if it is about the summands or scalars, and the second
otherwise. -/
private def regroupWithLowerings : TacticM Unit := do
  unless hasLowering (← instantiateMVars (← getMainTarget)) do regroup; return
  let s ← saveState
  try regroup catch e =>
    -- Lowerings and raisings are contractions with the form (`Species.toDualAt_eq_contr`). They
    -- are expanded only when needed, since every expanded form is one more factor to match.
    s.restore
    evalTactic (← `(tactic| simp only [Tensors.Species.toDualAt_eq_contr]))
    try regroup catch e' =>
      -- The expansion changes the factors, not the summands or scalars, so an error about those
      -- reads better before it.
      let msg ← e.toMessageData.toString
      throw <| if msg.contains "summand" || msg.contains "scalars" then e else e'

/-!

## F. Chains of lowerings and raisings

-/

/-- `tensor_slots` proves an equation of two chains of lowerings and raisings of the same tensor,
such as `{{T | ↓μ ↓ν}ᵀ | ↑μ ↑ν}ᵀ = T` or `{{T | ↓μ ν}ᵀ | μ ↓ν = {T | μ ↓ν}ᵀ | ↓μ ν}ᵀ`. Each chain
is one slotwise map (`Species.toDualAt_eq_mapAt`, `Species.mapSlots_mapSlots`), and the two maps
are compared slot by slot, where `Species.toDual_toDual` cancels a lowering with a raising. A side
with no lowering or raising is the slotwise identity (`Species.mapSlots_id`). The slots must be
`Fin n` with a literal `n`. -/
elab "tensor_slots" : tactic => do
  evalTactic (← `(tactic| try simp only [Tensors.Species.toDualAt_eq_mapAt, Tensors.Species.mapAt,
    Tensors.Species.mapSlots_mapSlots]))
  let isMapSlots (e : Expr) := (bundledArg? ``Tensors.Species.mapSlots e).isSome
  let (_, l, r) ← goalEq "tensor_slots"
  unless isMapSlots l || isMapSlots r do
    throwError "tensor_slots: neither side lowers or raises an index"
  -- Each side is checked before it is unified, since a failed unification with a side that is a
  -- definition, such as a named tensor, unfolds it.
  wrapSides "tensor_slots" isMapSlots (← `(Tensors.Species.mapSlots_id_apply _))
  evalTactic (← `(tactic| focus
    refine congrArg (fun F => Tensors.Species.mapSlots _ F _) (funext ?_)
    intro x
    fin_cases x <;> refine LinearMap.ext fun v => ?_ <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, LinearMap.comp_apply,
        LinearMap.id_apply, Tensors.Species.slotMapsAt_apply_self,
        Tensors.Species.slotMapsAt_apply_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Representation.IntertwiningMap.coe_toLinearMap,
        Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.trans_apply,
        Tensors.Species.cast_apply, cast_cast, cast_eq, Tensors.Species.toDual_toDual]))

/-!

## G. Rewriting a sub-product by an identity

-/

/-- A contraction `Tensor.contr τ P` of a left-nested product `P`, read slot by slot. The slots of
`P` are numbered in order, the slots of each factor after those of the factors before it. -/
private structure ReadContraction where
  /-- The factors of `P`, from left to right. -/
  factors : List Expr
  /-- The slot of `P` at which each factor starts. -/
  offsets : List Nat
  /-- The slot of `P` of each free index, in order. -/
  free : List Nat
  /-- The two slots of `P` of each pair, the first argument of `S.contr` first. -/
  pairs : List (Nat × Nat)

/-- The elements of a slot type built from `Fin n` with a literal `n`, `Unit`, `Empty` and `⊕`, in
slot order. -/
private partial def slotElems (ι : Expr) : MetaM (List Expr) := do
  let ι ← whnfR ι
  if ι.isAppOfArity ``Fin 1 then
    let some n ← (evalNat ι.appArg!).run
      | throwError "tensor_regroup: the slot type {ι} is not literal"
    (List.range n).mapM fun i => do
      mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ι.appArg!])]
  else if let .const ``PUnit [u] := ι then return [mkConst ``PUnit.unit [u]]
  else if ι.isConstOf ``Empty then return []
  else if ι.isAppOfArity ``Sum 2 then
    let (a, b) := (ι.getArg! 0, ι.getArg! 1)
    return (← (← slotElems a).mapM fun x => mkAppOptM ``Sum.inl #[a, b, x]) ++
      (← (← slotElems b).mapM fun x => mkAppOptM ``Sum.inr #[a, b, x])
  else throwError "tensor_regroup: the slot type {ι} is not built from `Fin n` and `⊕`"

/-- The number of the slot `x` of the slot type `slots`, after evaluating `x`. -/
private partial def slotNumber : Slots → Expr → MetaM Nat
  | .fin _, x => do
    let some i ← (evalNat (← whnfD (← mkAppM ``Fin.val #[x]))).run
      | throwError "tensor_regroup: internal error, the slot {x} does not evaluate"
    return i
  | .unit, _ => return 0
  | .sum a b, x => do
    let x ← whnfD x
    if x.isAppOfArity ``Sum.inl 3 then slotNumber a x.appArg!
    else if x.isAppOfArity ``Sum.inr 3 then return a.size + (← slotNumber b x.appArg!)
    else throwError "tensor_regroup: internal error, the slot {x} does not evaluate"

/-- Reads a contraction `Tensor.contr τ P` of a left-nested product `P`, evaluating `τ` at each
free index and at each slot of each pair. -/
private def readContraction (e : Expr) : MetaM ReadContraction := do
  let some P := bundledArg? ``Tensors.Species.Tensor.contr e
    | throwError "tensor_regroup: the side{indentExpr e}\nis not a contraction"
  let τ := e.consumeMData.appFn!.appArg!.appArg!
  let some (slots, _, _) ← literalTensorType? (← inferType P)
    | throwError "tensor_regroup: the slots or colors of a product are not literal"
  let fs := factors P
  let sizes ← fs.mapM fun f => do
    let some (s, _, _) ← literalTensorType? (← inferType f)
      | throwError "tensor_regroup: the slots or colors of{indentExpr f}\nare not literal"
    return s.size
  -- `τ : ColorEquiv c (contrColors c' a)`, with `c' : κ → Color K` and `a : J → Color K`.
  let args := (← whnfR (← inferType τ)).getAppArgs
  let cargs := args[args.size - 1]!.getAppArgs
  let (κ, J) := (cargs[1]!, cargs[2]!)
  let JJ ← mkAppM ``Sum #[J, J]
  let at_ (y : Expr) : MetaM Nat := do
    slotNumber slots (← mkAppM ``Equiv.invFun #[← mkAppM ``Tensors.ColorEquiv.toEquiv #[τ], y])
  let free ← (← slotElems κ).mapM fun x => do at_ (← mkAppOptM ``Sum.inl #[κ, JJ, x])
  let pairs ← (← slotElems J).mapM fun j => do
    let half (left : Bool) := do
      at_ (← mkAppOptM ``Sum.inr #[κ, JJ, ← mkAppOptM (if left then ``Sum.inl else ``Sum.inr)
        #[J, J, j]])
    return (← half true, ← half false)
  return ⟨fs, sizes.scanl (· + ·) 0, free, pairs⟩

/-- The ways of sending the slots of `A` to slots of `G`, factor by factor, each factor of `A` to an
equal factor of `G`, so that every pair of `A` is sent to a pair of `G`. Each way is the list of
images of the slots of `A`, together with the factors of `G` that are hit. -/
private def embeddings (A G : ReadContraction) : MetaM (List (List Nat × List Nat)) := do
  let candidates ← A.factors.mapM fun x =>
    (List.range G.factors.length).filterM fun j => isEqFactor x G.factors[j]!
  let isPair (p q : Nat) := G.pairs.contains (p, q) || G.pairs.contains (q, p)
  return (matchings candidates []).filterMap fun target =>
    let φ := (target.zipIdx).flatMap fun (j, i) =>
      (List.range (A.offsets[i+1]! - A.offsets[i]!)).map (G.offsets[j]! + ·)
    if A.pairs.all fun (p, q) => isPair φ[p]! φ[q]! then some (φ, target) else none

/-- The function `x ↦ {x | … ⊗ g | … ⊗ …}ᵀ`, for `x` of the type of `A`, with its free indices
in the order of `L`, the contraction read as `G`. The factors `g` of `G` not hit by `target` follow
`x`, and every slot of `G` is named after its free index `fₖ` or its pair `pⱼ`. The slots of `x`
are named as the free indices of `A` are sent by `φ`. -/
private def regroupedFun (L A : Expr) (Aread G : ReadContraction) (φ target : List Nat) :
    TermElabM Expr := do
  let name (s : Nat) : TSyntax `tensorIndex := Unhygienic.run do
    let n := match G.free.idxOf? s with
      | some k => s!"f{k}"
      | none => s!"p{(G.pairs.findIdx? fun (p, q) => p == s || q == s).getD 0}"
    let i := mkIdent (Name.mkSimple n)
    `(tensorIndex| $i:ident)
  let leaf (T : Expr) (ss : List Nat) : TermElabM (TSyntax `tensorIndexExpr) := do
    let t ← exprToSyntax T
    `(tensorIndexExpr| $t:term | $((ss.map name).toArray)*)
  let rest ← ((List.range G.factors.length).filter (!target.contains ·)).mapM fun j =>
    leaf G.factors[j]! ((List.range (G.offsets[j+1]! - G.offsets[j]!)).map (G.offsets[j]! + ·))
  withLocalDeclD `x (← inferType A) fun x => do
    let rhs ← rest.foldlM (init := ← leaf x (Aread.free.map (φ[·]!))) fun a b =>
      `(tensorIndexExpr| $a ⊗ $b)
    -- The equation `{L | f₀ f₁ … = …}ᵀ` relabels its right side to the order of `L`.
    let eq ← Term.elabType (← `({ $(← leaf L G.free) = $rhs }ᵀ))
    Term.synthesizeSyntheticMVarsNoPostponing
    let some (_, _, M) := (← instantiateMVars eq).eq?
      | throwError "tensor_regroup: internal error, not an equation"
    mkLambdaFVars #[x] M

/-- Proves the goal `ty` by `tac`, aside from the main goal. -/
private def proveAside (ty : Expr) (tac : TacticM Unit) : TacticM Expr := do
  let g ← mkFreshExprMVar ty
  let gs ← getGoals
  setGoals [g.mvarId!]
  try
    tac
    unless (← getGoals).isEmpty do throwError "tensor_regroup: internal error, a goal is left"
  finally setGoals gs
  instantiateMVars g

/-- The side `A`, flattened to one contraction of a left-nested product, with lowerings and
raisings first written as contractions with the form if `expand`. -/
private def flattenTerm (A : Expr) (expand : Bool) : TacticM Expr := do
  let g ← mkFreshExprMVar (← mkEq A (← mkAppOptM ``Zero.zero #[← inferType A, none]))
  let gs ← getGoals
  setGoals [g.mvarId!]
  try
    if expand then evalTactic (← `(tactic| try simp only [Tensors.Species.toDualAt_eq_contr]))
    flattenContractions
    return (← goalEq).2.1
  finally setGoals gs

/-- The body of `tensor_regroup using e₁, …, eₙ`. For `e₁ : A = B`, the left side of the goal is
regrouped by `regroupWithLowerings` into a product `M A` of `A` with the factors not in `A`, which
`congrArg M e₁` rewrites to `M B`, and the remaining identities are used in the same way. Each way
of finding the factors of `A` among the factors of the goal is tried in turn, first as written and
then with lowerings and raisings written as contractions with the form, first on the left side of
the goal and then on the right. -/
private partial def regroupUsing : List Term → TacticM Unit
  | [] => regroupWithLowerings
  | e :: es => withMainContext do
    let h ← instantiateMVars (← Tactic.elabTerm e none)
    let some (_, A, B) := (← instantiateMVars (← inferType h)).eq?
      | throwError "tensor_regroup: {e} is not an equation"
    let mut err := m!"tensor_regroup: no factors of either side are contracted as in the left \
      side of {e}"
    let expands := if hasLowering (← instantiateMVars (← getMainTarget)) || hasLowering A then
      [false, true] else [false]
    -- The right side is searched by first turning the goal around.
    for flip in [false, true] do
      for expand in expands do
        let s ← saveState
        -- A side that is not a contraction has no factors to search.
        let read? ← try
            if flip then replaceMainGoal [← (← getMainGoal).applySymm]
            if expand then
              evalTactic (← `(tactic| try simp only [Tensors.Species.toDualAt_eq_contr]))
            flattenContractions
            let (_, L, _) ← goalEq
            pure (some (L, ← readContraction L, ← readContraction (← flattenTerm A expand)))
          catch _ => pure none
        if let some (L, G, Aread) := read? then
          for (φ, target) in (← embeddings Aread G).take maxMatchings do
            let s' ← saveState
            try
              -- `L = M A` by regrouping, and `M A = M B` by `congrArg M h`.
              let M ← regroupedFun L A Aread G φ target
              let h₁ ← proveAside (← mkEq L (M.beta #[A])) regroupWithLowerings
              let pf ← mkEqTrans h₁ (← mkCongrArg M h)
              let (_, _, R) ← goalEq
              let rest ← mkFreshExprSyntheticOpaqueMVar (← mkEq (M.beta #[B]) R)
              (← getMainGoal).assign (← mkEqTrans pf rest)
              replaceMainGoal [rest.mvarId!]
              regroupUsing es
              return
            catch ex => s'.restore; err := ex.toMessageData
        s.restore
    throwError err

/-- `tensor_regroup` proves an equation of two sums of signed scalar multiples of contractions of
the same factors, grouped or ordered differently, such as
`{{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ {U | ν ρ ⊗ W | ρ τ}ᵀ | ν τ}ᵀ`. Sums,
negatives and scalars are first moved out of every product, contraction and relabeling. Each
summand on the left is then matched with a summand on the right with the same sign and scalar,
whose contraction is the same up to regrouping (`Species.Tensor.contr_eq_of_samePair`). When a
factor appears more than once, each way of matching the equal factors is tried in turn, so the
number of attempts is the product of `k!` over the factors that appear `k` times, and at most 12
are tried.

Beyond regrouping, it uses these identities:
- a delta on one side with no counterpart on the other is inserted on the other side at a slot of
  its color, `T^…μ… = T^…ν… δ_ν^μ` (`Species.Tensor.contr_deltaTensor`), or, against two forms on
  the other side, written as their contraction, `g^μν g_νρ = δ^μ_ρ`
  (`Species.contr_formTensor_formTensor`), and pairs of such forms against nothing, as a lowering
  `T_…ν… = T^…μ… g_μν` contracted with `g^νρ`, are matched one pair at a time by inserting a delta
  first;
- when the signs of two summands differ, one antisymmetric form is swapped, `ε^αβ = -ε^βα`
  (`Species.formTensor_antisymm`), and when the regrouping fails, one symmetric form is swapped,
  `η^μν = η^νμ` (`Species.formTensor_symm`);
- when no matching is found, lowerings and raisings are expanded into contractions with the form
  (`Species.toDualAt_eq_contr`) and the matching is tried again.

A side that is not a contraction, such as a single tensor, is read as a contraction with no pairs
(`Species.Tensor.contr_noPairs`). The scalars on the two sides must agree up to definitional
equality, as `2` and `2`.

`tensor_regroup using e₁, …, eₙ` first rewrites by the equations `eᵢ : Aᵢ = Bᵢ`, in turn. For each,
the factors of `Aᵢ` are found among the factors of the left side of the goal, or else of the right
side, contracted along the same pairs, and that side is regrouped as `Aᵢ` times the other factors
and rewritten to `Bᵢ`. -/
syntax (name := tensorRegroup) "tensor_regroup" (" using " term,+)? : tactic

elab_rules : tactic
  | `(tactic| tensor_regroup) => regroupWithLowerings
  | `(tactic| tensor_regroup using $es,*) => regroupUsing es.getElems.toList

end Tensors.Notation

end
