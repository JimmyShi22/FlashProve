-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/MaskNum.lean: FOUR DEFINITIONS WITH CODE. No statement. The
names at which the laws speak are abbreviations of them: `maskMsgOf` and `maskPosOf`
(Law/W/MaskRowWritten.lean), `maskSeatAt` and `maskNumAt` (Law/W/MaskRowAtSeg.lean).

What is here. `k4MaskNum Zp m`: the number, in the witness, of the message at the seat that the plan
gives segment m's first oracle message with mask rows; with the three definitions that it is made
of. All four read the public part Zp and the segment's number alone. Why they lie here, outside the
files of laws: a definition of the honest prover's messages has to import the number, and the laws'
imports reach seventy modules under Johnson/Goal/; this file's reach ten.

Not shown here. NOTHING IS SHOWN HERE: definitions claim nothing. That the mask row of a segment
lies in the message of that number: `maskRow_laid` (Law/W/MaskRowAtSeg.lean) has it for the segments
of the feed-forward layers' own rounds (sub-protocol K4), under the library's hypothesis on the
public files, at the name `maskNumAt`. WHERE NO MESSAGE OF THE SEGMENT HAS MASK ROWS THE SEARCH's
DEFAULT 0 STANDS IN, IN SILENCE. IT IMPORTS NO FILE OF OURS: two files of the library. A program's
walk over import lines, which stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 10 modules under Johnson/Goal/ and at 3 under
Johnson/Bridge/, and met none under ThirdParty/ or Johnson/D/ and none that begins Cb.Bridge: what
lies behind the 13 is not counted. The 10 come with the library's own numbering of the witness's
messages (`P5J.At.arr`, Johnson/P5J/LettersAt.lean). Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.P5J.Rad3Seat3At
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open VerifiableInference.Desc.First.Look (Sent messagesAt keptAt)

/-- The number, among link i's oracle messages, of the first with mask rows; 0 where there is
none. -/
def k4MaskMsg (D : Sent) (i : ℕ) : ℕ :=
  ((messagesAt D i).findIdx? fun y => y.shape.maskRows != 0).getD 0

/-- Its place in the list of the oracle messages that stand sent at link i: behind the kept ones. -/
def k4MaskPos (D : Sent) (i : ℕ) : ℕ := (keptAt D i).length + k4MaskMsg D i

/-- The seat that the plan gives segment m's first message with mask rows. Where no message of the
segment has mask rows the search's default 0 stands in: then this is what the plan's function
answers at the number of the kept messages. -/
def k4MaskSeat (Zp : ProofFile.Pub) (m : ℕ) : ℕ × ℕ :=
  P5J.At.seat3At Zp m false (k4MaskPos (P5J.At.sentAt Zp) m)

/-- The number in the witness of the message at that seat. -/
def k4MaskNum (Zp : ProofFile.Pub) (m : ℕ) : ℕ :=
  P5J.At.arr Zp (k4MaskSeat Zp m).1 (k4MaskSeat Zp m).2

end ProofFile.Honest.K4.Lot
