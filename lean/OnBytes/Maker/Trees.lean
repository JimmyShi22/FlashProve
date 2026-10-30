-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Trees.lean: the rounds of a chain as typed rounds, where one prover's message may send
the roots of several trees, and a round may open stored tables. Definitions, and the equations by
which they unfold.

OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean and OnBytes/TypedOracleCompiler/Run/PlanQS.lean make typed rounds of a chain's data
with a list of trees a round. This file adds one thing to a round's data: the stored tables that are
opened behind it. Everything else IS that text, by definition: a chain's typed rounds here are its
typed rounds there, at the data without the stored tables (`toRDs`). The names of this file stand
for the names of that text, so that whatever is shown there of a chain's rounds holds of these.

What the file contains.
  `RDT`: a round's data: that text's (`RD`: the plan's entry, the kind, the items, the shapes of the
    trees whose roots the round sends, the trees that are opened at its draws, by numbers whose
    meaning the user of this file fixes), and the stored tables that are opened behind it. `toRDs`.
  `PosT`, `SymT`, `zeroT`, `colT`, `posAtT`, `decPosT`: the positions of a round with several trees,
    each tree with its own depth and its own width of a column.
  `roundT`, `SLT`, `SOfT`, `uLT`: the rounds as skeletons; `SOfT` has Run/PlanQS.lean's round in
    front (`s0`).
  `drawnT`, `passT`, `rhoT`, `rvT`: what was drawn; the tests of the proofs of work; the verifier's
    messages of a transcript; the rounds of a view.
  `treeShT`, `posAtST`, `colAtST`: the shape, a position, a column of the chain's tree number n, the
    trees counted through the rounds, a round's trees in their order.
  `decSLT`, `decOST`: equality of positions is decidable.
  `treeShT_cons`, `posAtST_cons`, `colAtST_cons`: how the last three unfold at a first round.

What is not claimed. No wiring, no hash, no file.


-/
import Run.PlanQX
import OnBytes.TypedOracleCompiler.Run.PlanQS

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ
open _root_.Run.Twin (RS)

/-- A round's data, with a list of trees and the stored tables. -/
structure RDT extends TypedOracleCompiler.Run.PQ.RD where
  /-- the stored tables that are opened behind it -/
  stored : List Fmt.Stored

/-- A chain's data without the stored tables. -/
abbrev toRDs (ds : List RDT) : List TypedOracleCompiler.Run.PQ.RD := ds.map (·.toRD)

/-! ## The positions of a round with several trees -/

abbrev PosT : List Fmt.Shape → Type := TypedOracleCompiler.Run.PQ.PosT
abbrev SymT : (ts : List Fmt.Shape) → PosT ts → Type := TypedOracleCompiler.Run.PQ.SymT
abbrev zeroT : (ts : List Fmt.Shape) → (p : PosT ts) → SymT ts p := TypedOracleCompiler.Run.PQ.zeroT
abbrev colT : (ts : List Fmt.Shape) → (p : PosT ts) → SymT ts p → List UInt64 := TypedOracleCompiler.Run.PQ.colT
abbrev posAtT : (ts : List Fmt.Shape) → ℕ → ℕ → Option (PosT ts) := TypedOracleCompiler.Run.PQ.posAtT
abbrev decPosT : (ts : List Fmt.Shape) → DecidableEq (PosT ts) := TypedOracleCompiler.Run.PQ.decPosT

/-! ## Rounds as skeletons -/

abbrev roundT (C : CK) (d : RDT) : RS := TypedOracleCompiler.Run.PQ.roundS C d.toRD

abbrev SLT (C : CK) (ds : List RDT) : List RS := TypedOracleCompiler.Run.PQ.SL C (toRDs ds)

/-- A chain's rounds behind the round in front. -/
abbrev SOfT (C : CK) (ds : List RDT) : List RS := s0 C :: SLT C ds

/-- The shape of the rounds after the round in front. -/
abbrev uLT (C : CK) (ds : List RDT) : Shape := TypedOracleCompiler.Run.PQ.uL C (toRDs ds)

/-! ## What a view is made of -/

abbrev drawnT (C : CK) (ds : List RDT) : Rho (uLT C ds) → List Fmt.Drawn :=
  TypedOracleCompiler.Run.PQ.drawnSL C (toRDs ds)

abbrev passT (C : CK) (ds : List RDT) : Rho (uLT C ds) → Bool := TypedOracleCompiler.Run.PQ.passSL C (toRDs ds)

abbrev rhoT (C : CK) (ds : List RDT) : Iop.Tr (uLT C ds) → Rho (uLT C ds) :=
  TypedOracleCompiler.Run.PQ.rhoSL C (toRDs ds)

abbrev rvT (C : CK) (ds : List RDT) : Iop.Tr (uLT C ds) → List RV := TypedOracleCompiler.Run.PQ.rvSL C (toRDs ds)

/-- The shape of the chain's tree number n. -/
abbrev treeShT (ds : List RDT) : ℕ → Option Fmt.Shape := TypedOracleCompiler.Run.PQ.treeSh (toRDs ds)

/-- The position at (the chain's tree number n, leaf x). -/
abbrev posAtST (C : CK) (ds : List RDT) : ℕ → ℕ → Option (OPos (uLT C ds)) :=
  TypedOracleCompiler.Run.PQ.posAtS C (toRDs ds)

/-- The column there. -/
abbrev colAtST (C : CK) (ds : List RDT) : Iop.Tr (uLT C ds) → ℕ → ℕ → Option (List UInt64) :=
  TypedOracleCompiler.Run.PQ.colAtS C (toRDs ds)

instance decSLT (C : CK) (ds : List RDT) : DecidableEq (OPos (uLT C ds)) :=
  TypedOracleCompiler.Run.PQ.decSL C (toRDs ds)

instance decOST (C : CK) (ds : List RDT) : DecidableEq (OPos (Twin.up (SOfT C ds))) :=
  TypedOracleCompiler.Run.PQ.decOS C (toRDs ds)

/-! ## How they unfold at a first round -/

theorem treeShT_cons (d : RDT) (ds : List RDT) (n : ℕ) : treeShT (d :: ds) n =
    if n < d.trees.length then d.trees[n]? else treeShT ds (n - d.trees.length) := rfl

theorem posAtST_cons (C : CK) (d : RDT) (ds : List RDT) (n x : ℕ) : posAtST C (d :: ds) n x =
    if n < d.trees.length then (posAtT d.trees n x).map .inl
    else (posAtST C ds (n - d.trees.length) x).map .inr := rfl

theorem colAtST_cons (C : CK) (d : RDT) (ds : List RDT) (τ : Iop.Tr (uLT C (d :: ds))) (n x : ℕ) :
    colAtST C (d :: ds) τ n x =
      if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (τ.1.1 p)
      else colAtST C ds τ.2.2 (n - d.trees.length) x := rfl

end OnBytes.Maker
