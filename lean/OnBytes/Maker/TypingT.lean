-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingT.lean: from what a reader has read of a stretch of rounds to the typed parts
that a compiled verifier takes for these rounds, where one prover's message may send the roots of
several trees (OnBytes/Maker/Trees.lean). Definitions alone; the laws are in
OnBytes/Maker/TypingTLaws.lean.

A proof string has, for a stretch of rounds, the roots sent, the plain part of each message, and a
function that gives an opening (symbol, salt, path) at a position of the rounds' oracles, or
nothing. A reader of a file gives untyped data: for each round the items read and the nonce, and
for each opened tree a table "leaf, then column, salt, path". This file types the first from the
second. It uses Run/ParseThin.lean's look-up `atTT` as it stands.

Six of its definitions say again what the library holds for rounds with a list of trees: `treeIn`
and `leafIn` are `treeT` and `placeT` (OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean); `symIn`, `symT'` and
`plainsT` are `symT`, `symSL` and `plainsSL` at `toRDs` (OnBytes/TypedOracleCompiler/Run/PlanQSMore.lean); `rootsT`
is `rootsD` (OnBytes/TypedOracleCompiler/Run/ChainF.lean). OnBytes/Maker/TypingTWire.lean and TypingLine.lean
tie four of them (`treeIn_eq`, `leafIn_eq`, `plainsT_line`, `rootsT_line`); no
statement ties `symIn` to `symT` or `symT'` to `symSL`. `placeT'` differs from `placeSL` by matter:
it gives a tree's count within the stretch, not the format's number of the tree.

What the file contains.
  `treeIn`, `leafIn`, `symIn`: of a position of one round: the number of its tree among the round's
    trees; the number of its leaf; a list of words as a symbol there, if it has the tree's width.
  `treeAt`, `leafAt`: of a position of the stretch: the number of its tree within the stretch, the
    trees counted through the rounds and a round's trees in their order, as `posAtST` counts them;
    the number of its leaf.
  `placeT'`: the two as a pair. `symT'`: a list of words as a symbol at a position of the stretch.
  `plainsT`: the plain parts: each round's items without its roots, with the nonce read.
  `rootsT`: the roots of all rounds in the order sent, as digests.
  `opensT C ds base tabs`: the openings. The tables `tabs` are keyed by a tree's number over a whole
    file; `base` is the number there of the stretch's first tree. At a position: its tree and leaf,
    two look-ups (the tree's table, then the leaf) and the typing of the column, nothing else.

What is not claimed. No law is stated here. Nothing is tested here: no hash is computed, no path is
walked, and a table may hold anything. These functions are part of a step that only reformats; what
they return is an input of a verifier.


-/
import OnBytes.Maker.Trees
import Run.ParseThin

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ

/-! ## A position of one round -/

/-- The number of a position's tree among the round's trees. -/
def treeIn : (ts : List Fmt.Shape) → PosT ts → ℕ
  | _ :: _, .inl _ => 0
  | _ :: ts, .inr p => treeIn ts p + 1

/-- The number of its leaf in that tree. -/
def leafIn : (ts : List Fmt.Shape) → PosT ts → ℕ
  | _ :: _, .inl x => x.val
  | _ :: ts, .inr p => leafIn ts p

/-- A list of words as a symbol at a position: a column of its tree's width, or nothing. -/
def symIn : (ts : List Fmt.Shape) → (p : PosT ts) → List UInt64 → Option (SymT ts p)
  | s :: _, .inl _, l =>
    if h : l.length = s.W then some (fun i : Fin s.W => l[i.val]'(by rw [h]; exact i.isLt))
    else none
  | _ :: ts, .inr p, l => symIn ts p l

/-! ## A position of the stretch -/

/-- The number of a position's tree within the stretch. -/
def treeAt (C : CK) : (ds : List RDT) → OPos (uLT C ds) → ℕ
  | d :: _, .inl p => treeIn d.trees p
  | d :: ds, .inr q => d.trees.length + treeAt C ds q

/-- The number of its leaf in that tree. -/
def leafAt (C : CK) : (ds : List RDT) → OPos (uLT C ds) → ℕ
  | d :: _, .inl p => leafIn d.trees p
  | _ :: ds, .inr q => leafAt C ds q

/-- (the tree's number within the stretch, the leaf) -/
def placeT' (C : CK) (ds : List RDT) (p : OPos (uLT C ds)) : ℕ × ℕ :=
  (treeAt C ds p, leafAt C ds p)

/-- A list of words as a symbol at a position of the stretch. -/
def symT' (C : CK) :
    (ds : List RDT) → (p : OPos (uLT C ds)) → List UInt64 → Option (OSym (uLT C ds) p)
  | d :: _, .inl p, l => symIn d.trees p l
  | _ :: ds, .inr q, l => symT' C ds q l

/-! ## The typed parts -/

/-- The plain parts of the rounds, from what was read round by round; nothing if the numbers of
rounds differ or a round's items are not of the kinds that its data names. -/
def plainsT (C : CK) : (ds : List RDT) → List Fmt.RoundOut → Option (Plains (uLT C ds))
  | [], [] => some ()
  | d :: ds, o :: os =>
    match PlainOf.ofGots d.items o.vals, plainsT C ds os with
    | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
    | _, _ => none
  | _, _ => none

/-- The roots of all rounds, in the order sent. -/
def rootsT (os : List Fmt.RoundOut) : List (Dig 256) :=
  (os.flatMap fun r => Fmt.rootsOf r.vals).map bytesToDig

/-- The openings, from the tables of all trees of a file; `base` is the number over the file of the
stretch's first tree. -/
def opensT (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (p : OPos (uLT C ds)) : Option (Opening 256 (OSym (uLT C ds) p)) :=
  atTT (symT' C ds p) tabs (base + (placeT' C ds p).1) (placeT' C ds p).2

end OnBytes.Maker
