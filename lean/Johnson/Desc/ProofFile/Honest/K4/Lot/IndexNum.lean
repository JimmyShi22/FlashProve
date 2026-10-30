-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Lot/IndexNum.lean: FIVE DEFINITIONS WITH CODE. No statement.

What is here. WHERE, IN THE WITNESS, THE ONE ENTRY OF THE INDEX MASKS' MESSAGE LIES OF WHICH THE
TIE `K4IndexTieAt` (Law/WoTies.lean) SPEAKS AT THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4) OF GROUP g: the message's number (`k4IndexNum Zp`), the mask row (`k4IndexRow Zp
g`) and the place in it (`k4IndexPlace Zp g`); with the two numbers that these are made of: the
message's number of mask rows (`k4IndexRows`) and how many entries of its ledger are taken in front
of the member (`k4IndexTakes`: the segments in front of segment 2 g that leave a pending row). All
five read the public part Zp and the group's number alone. They are the number and the fence of
K4's lot for that entry (Lot/IndexLotG.lean), which is the form of a lemma on the lot of the
message's sender; they lie in a file of their own, with two import lines, so that light files can
read them.

Kin. The library has what `k4IndexTakes` is worth in its own scope: `rowsBefore_at`
(Johnson/Road/K4/Riders/BuiltFvs.lean): at an opening, for g below 12, the segments in front of
segment 2 g that leave a row are g. It is not called here: a definition claims nothing.

Not shown here. NOTHING IS SHOWN HERE: definitions claim nothing. THE NUMERALS 4 AND (1, 0) ARE
WRITTEN: the index masks' message is meant to be oracle message number 4 of the first chain's
statement and to sit at tenant 0 of tree 1; the library has both under its hypothesis on the public
files (`P5J.AtMg.indexNo_at`, Johnson/P5J/PlanSitsCore.lean; `P5J.index_at_head`,
Johnson/P5J/ReadsTestsAtHead.lean); at other public files these definitions may name another
message, in silence. WHERE THE LIST OF SHAPES HAS NO SHAPE AT 4, OR THAT SHAPE HAS NO MASK ROW,
`k4IndexRows` IS 0, IN SILENCE: then the row is the number of takes itself and the place is 0
(Lean's «% 0» and «/ 0»): AT SUCH FILES THE THREE NUMBERS WOULD MISNAME THE ENTRY's ADDRESS, AND
NOTHING IN THIS FILE FENCES IT. Where it is fenced: at a state, not as a statement on
`k4IndexRows`, and in steps that no statement joins: the library's `LedgerAt`
(Johnson/Desc/K13/Law/LedgerWithin.lean) holds «0 < the mask rows of the shape that the STATE's
message has» as its third clause; `indexLedger_border` (Law/W/IndexFactsThr.lean) has `LedgerAt` at
message 4 where a thread of the first chain stands at a border, CONDITIONAL on the library's
hypothesis on the public files and on more (the border's place has a segment and a piece from 2 on;
the border's number; the table's item pinI is open there; the takes are at most the free entries);
`indexRows_of_facts` (the same file) has that `k4IndexRows Zp` is the LISTED shape's number; that
the state's message has the listed shape is the library's `shape_is`
(Johnson/Desc/First/RecordPlan.lean), from the facts' field h₁. The four files of these writers
that name `k4IndexRows` hold no statement «0 < k4IndexRows Zp». That the verifier's ledger hands
out just this entry, and that the reader of the pile of pending rows reads it there:
Law/W/IndexOfOwn.lean, under the library's hypothesis, where the honest side's thread stands.
(Law/WoTies.lean, Lot/IndexLotG.lean, Law/W/IndexOfOwn.lean and Law/W/IndexFactsThr.lean are no
part of the library yet.) HOW LIGHT: following import lines, and stopping unopened at every module
under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name
begins Cb.Bridge, its imports reach 10 modules under Johnson/Goal/ and 3 under Johnson/Bridge/, and
none of the others; what lies behind these is not counted. The 10 come with the library's numbering
of the witness's messages (`P5J.At.arr`, Johnson/P5J/LettersAt.lean, beneath
Johnson/P5J/FoldAt.lean): `k4IndexNum` alone needs it; what the other four definitions read
(Johnson/Top/H0/Fill/D1At.lean, Johnson/Desc/K12/Door/MsgShapes.lean,
Johnson/Top/H0/Walk/FrameEntriesDefs.lean) reaches none of these. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.P5J.FoldAt
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.First (FillP1.fvsAt)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

/-- The number of mask rows of the listed shape at number 4; 0 where there is none. -/
def k4IndexRows (Zp : ProofFile.Pub) : ℕ :=
  (((msgsOfChain Zp.made.proof.1)[4]?).map (·.maskRows)).getD 0

/-- The segments in front of segment 2 g that leave a pending row. -/
def k4IndexTakes (Zp : ProofFile.Pub) (g : ℕ) : ℕ := rowsBefore (FillP1.fvsAt Zp) (2 * g)

/-- The mask row of the entry; the number of takes itself where `k4IndexRows` is 0. -/
def k4IndexRow (Zp : ProofFile.Pub) (g : ℕ) : ℕ := k4IndexTakes Zp g % k4IndexRows Zp

/-- The place in that row; 0 where `k4IndexRows` is 0. -/
def k4IndexPlace (Zp : ProofFile.Pub) (g : ℕ) : ℕ := k4IndexTakes Zp g / k4IndexRows Zp

/-- The number in the witness of the message at tenant 0 of tree 1. -/
def k4IndexNum (Zp : ProofFile.Pub) : ℕ := P5J.At.arr Zp 1 0

end ProofFile.Honest.K4.Lot
#print axioms ProofFile.Honest.K4.Lot.k4IndexRows
#print axioms ProofFile.Honest.K4.Lot.k4IndexTakes
#print axioms ProofFile.Honest.K4.Lot.k4IndexRow
#print axioms ProofFile.Honest.K4.Lot.k4IndexPlace
#print axioms ProofFile.Honest.K4.Lot.k4IndexNum
