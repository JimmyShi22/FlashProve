-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuiet.lean: the step without a round that stands behind the sending of the
reads, at a layers' link and at the head's link, as a block of the format in which a file's protocol
is written (Johnson/Desc/Block.lean), at the record that the first chain carries
(Johnson/Desc/First/State.lean).

This file holds definitions only; no theorem is stated.

What the step does. The smallness test is told which weighted sums of the reads it is to speak of
(the list of tables), and the list is closed: from here on the test's own record lies in the carried
record. At a layers' link the list is what the link's own rounds returned. At the head's link it is
made here, of what was heard (tables). Then two tests on public numbers and the guard of order.

Written after the program's text of this step at the two kinds of link; and, for tables, after
Head.tablesOf (OnBytes/Model/HeadTables.lean), line for line: that routine is written in the
verifier's monad, but it reads and writes nothing of its state: it can only refuse. The plain
functions of these texts that cannot refuse are called here by name; the five that can stand in the
description's own text (Johnson/Desc/Own/HeadTabs.lean).

Main names (namespace VerifiableInference.Desc.K8.ReadsQuiet):
  closed tl funs L st: the list is closed and the three tests are asked, by import of
    Johnson/Desc/First/K8/Order.lean (Order.close, Order.front): one text of what the three kinds of
    link have in common, in this library's own words. The refusals' names are that file's.
  tables h L hp cov x: the head's tables, in the order of the vector of reads, with ten named
    clauses.
  planned tl: the block's test on the plan.
  PG, layers P; PH, head P: **the two blocks**, each of a place's public parameters.

The guard of order (Order.orderOk, the last test of Order.front) is asked here, as the program asks
it in this step. It is meant to move to the tests on the plan, with
the field "before" of the smallness test's own block; no such test stands yet. Where this block
stands behind the sending's own block in one fold, that block lays no copy of the guard: one text,
asked once.

What these two functions read. close: the test's record alone. front: of that record funClosed, shp,
NM, gtTree, ix.U; of the link's state link, check, moments, arrayOf; of the statement the messages'
mark "sampled".

Order.front's first test ("the smallness test: the list of tables is open") cannot fail here: close
itself lays that mark. It stands because the program asks it. So does "tables: the lookup's plane 1
is not there": the one test beneath it (lm from 5 to kT + 5) is the test beneath plane 0's, which
stands in front.

The covered positions at the head's link are read off the carried record (S.covered: of the
request's words and the heard reply), not handed in: no letter of the instance reaches the block.

The block's test on the plan (planned): that the plan's list of tables is open, and one shape a
matrix: they read the place's parameters alone. decide asks them again, because close and front
do.

Every refusal's words say what is wrong, not what is asked.

Of the verifier on bytes no function that returns a Bool, an Option or an Except is called by name
in this file. That the list is open is read off the record's field funClosed.

What is not claimed. That a test written here is the program's: of close and front
Johnson/Desc/First/K8/OrderAgrees.lean says it, at every argument, but for the refusals' names; of
the five makers Johnson/Desc/Own/HeadTabsAgree.lean; of the rest no theorem ties them. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.State
import Johnson.Desc.First.K8.Order
import Johnson.Desc.Own.HeadTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc (Block Place need named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Order.close Order.front)

/-- A refusal laid under this text's own name. -/
def under {α : Type} (name : String) : Except String α → Except String α
  | .ok a => .ok a
  | .error _ => .error name

/-- **The list of tables is closed.** tl: the plan's record of the smallness test at this link;
funs: the list; L: the link's state; st: the chain's statement. -/
def closed (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (st : Statement) :
    Except String HTailF2 := do
  let tl' ← Order.close tl funs
  Order.front tl' L st
  pure tl'

/-- **The head's tables**, in the order of the vector of reads. -/
def tables (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) :
    Except String Tables := do
  need "tables: the plan's list of tables is closed already" (!hp.tl.funClosed)
  let mats := hp.tl.mats
  let iHF := 0
  let iHD := h.NHf
  let iHR := iHD + 1
  let iBH := iHR + 1
  let iXL := iBH + 1
  let La := 2 ^ h.la
  let ZV ← named "tables: the squares' point has fewer than la coordinates"
    (Own.tailOf x.wpl.r h.la)
  let lowN ← named "tables: the norm's point has fewer than ls coordinates"
    (Own.cutTail (zjOf L x.g1 x.qN) h.ls)
  let YN := longPoint lowN.2 x.tN.r
  need "tables: the long point has not la = ls + lt coordinates"
    (YN.size == h.la && h.la == h.ls + h.lt)
  let (phiC, _, rhoCv) := costWeights cov (ztOf h L x.g1 x.qH)
  -- weight 1 on each of a block's S2 features, phiC on the positions
  let phiZ := (Array.range La).map fun i => phiC.getD (i % h.T) zeroE
  let qFC ← named "tables: no call has a segment CNF" (Own.callWith L "CNF")
  let qROW ← named "tables: no call has a segment ROW" (Own.callWith L "ROW")
  let mb := 2 ^ h.lmbH
  let b0 ← named "tables: the lookup's plane 0 is not there" (Own.planeWeights x.g1 h.lmbH 0)
  let b1 ← named "tables: the lookup's plane 1 is not there" (Own.planeWeights x.g1 h.lmbH 1)
  let asks : List (Nat × Nat × Nat × Array E × String) := [
    (iHF, h.NHf, La, longPhi x.Zl h.ls h.lt, "hf@Z"),
    (iHF, h.NHf, La, phiZ, "hf@phiZ"),
    (iXL, 1, La, longPhi ZV h.ls h.lt, "xbL@Z_V"),
    (iXL, 1, La, longPhi YN h.ls h.lt, "xbL@Y_N"),
    (iHD, 1, h.T, eqTab (ztOf h L x.g1 qFC), "hd@zt_FC"),
    (iHD, 1, h.T, eqTab x.tH.r, "hd@r_H"),
    (iHR, 1, h.T, eqTab (ztOf h L x.g1 qROW), "hr@zt_ROW"),
    (iHR, 1, h.T, eqTab x.PV, "hr@P_V"),
    (iHR, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
    (iHR, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
    (iHR, 1, h.T, phiC, "hr@phiC"),
    (iHR, 1, h.T, rhoCv, "hr@rhoC"),
    (iBH, 1, mb, b0, "bH-bits-0"),
    (iBH, 1, mb, b1, "bH-bits-1"),
    (iBH, 1, mb, Forest.phiP h.lmbH, "bH-pin")]
  let t ← named "tables: a table is empty"
    (asks.foldlM (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {})
  need "tables: they do not fill the vector of reads" (t.p == hp.nU.getD 2 0)
  pure t

/-- **The test on the plan**: the plan's list of tables is open; one shape a matrix. -/
def planned (tl : HTailF2) : Bool := !tl.funClosed && tl.shp.size == tl.NM

/-- A layers' link's place: its public parameters. -/
structure PG where
  place : Place
  /-- the plan's record of the smallness test at this link -/
  tl : HTailF2

/-- **The step at a layers' link.** -/
def layers (P : PG) : Block S Unit :=
  { name := "the reads' list is closed (a layers' link)", place := P.place, planOk := planned P.tl
    rounds := [], oracles := [], before := [], claims := [], after := []
    decide := fun s _ _ =>
      match s.here with
      | .lay a => do
        let own ←
          (a.own.elim (.error "reads: the own rounds' record is not laid") .ok : Except String _)
        let tl ← closed P.tl own.funs a.L s.st
        pure { s with here := .lay { a with tl := tl } }
      | _ => .error "reads: no layers' link is open" }

/-- The head's link's place: its public parameters. -/
structure PH where
  place : Place
  /-- the head's public numbers, its layout and its sub-proof's plan -/
  h : Shape
  L : HL
  hp : HPlanH2

/-- **The step at the head's link.** -/
def head (P : PH) : Block S Unit :=
  { name := "the reads' list is made and closed (the head's link)", place := P.place
    planOk := planned P.hp.tl
    rounds := [], oracles := [], before := [], claims := [], after := []
    decide := fun s _ _ =>
      match s.here with
      | .head a => do
        need "reads: the head's link is not opened" a.opened
        let cov ← under "reads: the covered positions cannot be said" (s.covered P.h.T P.h.V)
        let x ← (a.x.elim (.error "reads: what the head heard is not laid") .ok : Except String _)
        let t ← tables P.h P.L P.hp cov x
        let tl ← closed P.hp.tl t.funs a.L s.st
        pure { s with here := .head { a with t := some t, tl := tl } }
      | _ => .error "reads: the head's link is not open" }

end VerifiableInference.Desc.K8.ReadsQuiet
