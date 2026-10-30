-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotInst.lean: the honest side of the kind "lookup" (K3): the lot's
honest side at the proof file's own instance: `theLot` (Honest/K3/LotFilled.lean) with its third
letter, the reader of the instance, given as a term: `reqAt` (Honest/K3/WitReq.lean), which makes
the covered positions and the checked tokens of the instance's request by the library's own
functions. Definitions with code and three small theorems by rfl.

Terms. Honest/K3/GLOSSARY.md ("lot", "half", "instance", "seat").

What is defined and shown.
  `theLotInst`: `theLot` at req := `reqAt Z`, at every public part Z; its letters are the trace's
    reader and the index's alone.
  `theLotInstSpec`: the same at the specification's summands: in the place of `theLotInst`, never
    beside it.
  `theLotInstFit`, `theLotInstSpecFit`: the two with a half only where the tests at the seat accept
    (`fitHalves`, Honest/K3/SeatFits.lean).
  `theLotInst_is`, `theLotInstSpec_is`: at each public part the halves are those of `theLot` (of
    `theLotSpec`) at that public part's reader of the instance.
  `theLotInst_name`: its name is the lot's.
Only one of the four, and none of `theLot`, `theLotSpec`, `theLotFit`, `theLotSpecFit` beside it,
may stand in a list of lots' honest sides at a time: all bear the one lot's name. The frame lays the
halves of all lots of the list one behind the other (`firstOf`, Honest/Frame.lean), these lots lay
theirs at the sites' places, and the frame's `readyTests` refuses where two halves stand at one
place (`twice`).

Users. Honest/K3/LotInstFast.lean, among others, imports this file.

Limits. Where the library's maker of the covered positions rejects a request, `reqAt` yields empty
arrays: the test on the instance (`reqFitsB Z.p.X (reqAt Z x)`, or `reqMadeB` and `sizesOneB`:
WitReq.lean) rejects there. It is no test at the lot's seat: a lot's halves are made of the public
part, not of an instance: whoever gives the instance asks it. The theorems that are stated of this
filling's keys, bits and rounds take that test, or what an acceptance by it gives, as a hypothesis.
Nothing is evaluated in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block)

variable {X S Cl : Type} {W₀ Rc Tr : Type}

/-- **The lot's honest side at the proof file's own instance.** Here cells is the trace's reader,
and weights the index's. -/
def theLotInst (cells : Tr → Cells) (weights : W₀ → Weights) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotAt fun Z => fastFill (sourcesAt cells weights (reqAt Z) Z)

/-- The same at the specification's summands: in the place of `theLotInst`, never beside it. -/
def theLotInstSpec (cells : Tr → Cells) (weights : W₀ → Weights) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotAt fun Z => specFill (sourcesAt cells weights (reqAt Z) Z)

/-- **A half only where the tests at the seat accept.** Here bsOf gives, of the public part, the
first chain's list of sub-protocols, and made gives, of the public part, `madeB` at the files of
which it is made. In the place of `theLotInst`, never beside it. -/
def theLotInstFit (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (cells : Tr → Cells)
    (weights : W₀ → Weights) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  fitHalves bsOf made (theLotInst cells weights)

/-- The same at the specification's summands. -/
def theLotInstSpecFit (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (cells : Tr → Cells)
    (weights : W₀ → Weights) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  fitHalves bsOf made (theLotInstSpec cells weights)

/-- At each public part the halves are those of `theLot` at that public part's reader of
the instance. -/
theorem theLotInst_is (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInst (Rc := Rc) (X := X) cells weights).halves Z G =
      (theLot (Rc := Rc) (X := X) cells weights (reqAt Z)).halves Z G := rfl

/-- The same of the specification's summands. -/
theorem theLotInstSpec_is (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInstSpec (Rc := Rc) (X := X) cells weights).halves Z G =
      (theLotSpec (Rc := Rc) (X := X) cells weights (reqAt Z)).halves Z G := rfl

/-- Its name is the lot's, at every public part. -/
theorem theLotInst_name (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) :
    (theLotInst (Rc := Rc) (X := X) cells weights).name = (K3Lot.lot Z).name := rfl

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.theLotInst_is
#print axioms ProofFile.Honest.K3.theLotInstSpec_is
#print axioms ProofFile.Honest.K3.theLotInst_name
