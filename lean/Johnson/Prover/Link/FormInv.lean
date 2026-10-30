-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormInv.lean: THE FORM's HALF OF THE ONE INVARIANT OF THE INDUCTION OVER THE
STAGES OF THE PROXIMITY TEST (the whole: Johnson/Prover/Link/BodyInv.lean). Definitions alone: two
structures of premises; no theorem is stated. No shown or sampled value stands in them: what the
description's own tests read of the verifier's state, the book and the plan's declared tree.

  FormInv    in front of a stage's fold, where the state passes a claim on (pass = .claim row L)
  LastForm   at the last stage, in front of the base case

What is not here. No statement; nothing here says that a state meets either. Nothing on soundness;
nothing on what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxDense
import Johnson.Prover.Link.FormFold
import Johnson.Prover.Link.BasePart
import Johnson.Prover.Link.ReadSeat
import Johnson.Desc.Means.Order
import Johnson.Desc.K12.Law.ChainOf
import Johnson.Desc.ChainEndLaw
import OnBytes.Slice.BaseLast
import OnBytes.Slice.BlkFoldVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open OnBytes.Slice.ProxRun (DenseForm)

/-- **The form's half, in front of a fold.** col: the written column of the tree that holds the
group's rows. tN, tr: the place in the book, and the tree, that holds the group's members and the
message id. Of col (ℕ → List UInt64) the field `width` alone speaks: the length of each `col x`.
`keptL` reads `L.kept.getD i false`: an entry that `L.kept` lacks counts as false. -/
structure FormInv (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t : T12)
    (col : ℕ → List UInt64) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : ℕ × ℕ)
    (id tN : ℕ) (tr : Tree) : Prop where
  /-- what the fold's part asks of the state: nine clauses (FormFold.lean) -/
  front : FoldFront p j cur t row L c n id
  /-- the claim has no kept row -/
  kept0 : row.kept = #[]
  /-- the layout keeps no member -/
  keptL : ∀ i, i < L.members.size → L.kept.getD i false = false
  /-- the layout's two numbers are the stage's -/
  layK : L.k = (sgOf cur).h + (sgOf cur).g
  layH : L.h = (sgOf cur).h
  /-- the claim's form is dense: each tensor in order, its slice inside its vector (DenseForm,
  OnBytes/Slice/BlkProxDense.lean) -/
  dense : DenseForm row.c
  /-- the statement is in order (Johnson/Desc/Means/Order.lean) -/
  order : Means.InOrder t.st
  /-- statement and book in step -/
  step : t.st.oracles.size = t.book.place.size
  /-- the roots received: those in front of the test, and one a switch so far -/
  roots : t.roots = p.nums.free + j
  /-- the members and the message id are, in this order, all the parts of one tree, opened at no
  list (ReadSeat.lean) -/
  seat : ReadSeat t.st t.book L.members.toList id tN tr
  /-- the tree is as long as the stage's main code -/
  log : tr.shape.logN = cur.C.a
  /-- the tree that the plan's round "CS" declares is the book's, in number, length and width -/
  decl : ∀ dS dC, ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC] →
    ∃ o, dC.opens = [o] ∧ o.1.tree = tr.number ∧ o.1.a = cur.C.a ∧
      o.1.W = tr.shape.mainWidth + tr.shape.maskWidth
  /-- the written column has the tree's width -/
  width : ∀ x, (col x).length = tr.shape.mainWidth + tr.shape.maskWidth

/-- **The form's half at the last stage**: base_at's premises on the state and the stage
(BodyBase.lean). -/
structure LastForm (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (cl : BaseClaim) (m star a : ℕ) : Prop where
  front : BaseFront p j cur t row L c cl m star a
  st : (sgOf cur).st = cur
  h0 : (sgOf cur).h = 0
  g0 : (sgOf cur).g = 0
  pow : (sgOf cur).C.l = 2 ^ ceilLog2 (sgOf cur).C.l
  dSize : row.d.size = (sgOf cur).Z.l
  fix : FixLaw row.c [zeroE]

end Johnson.Prover.Link
