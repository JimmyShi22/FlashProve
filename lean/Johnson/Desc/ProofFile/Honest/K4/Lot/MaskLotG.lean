-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/MaskLotG.lean: ONE DEFINITION WITH CODE. No statement.

What is here. `k4MaskLotG … Zp g`: the lot of the member of the feed-forward layers' own rounds
(sub-protocol K4) of group g for its segment's mask row, a term of `MsgLot`
(Honest/Thread/ScriptLots.lean, of other writers). IT TAKES THE GROUP's NUMBER ALONE: the message's
number (`k4MaskNum Zp (2 * g)`, Lot/MaskNum.lean), the first place, and the public data at which the
coins are asked (`k4PubG Zp g`, Lot/PubG.lean) come of one g. `k4PubG`'s Qp has the group g and asks
the book at group g's own place (`k4PubG_fields`, `k4PubG_place`, Law/W/PubGOf.lean). WHY NO LETTER
FOR THE PUBLIC DATA STANDS BESIDE g: a lot that takes both as letters, tied by nothing, has at one
Qp and two groups one text and two message numbers, and where the book lends the row it answers with
one value in both.
 The text is `k4MaskTextG`
(Lot/MaskTxtG.lean), whose look-up in the list can fail, from the place on that is the number of
scalars that the prover sends in the lookup (`Forest.elems`); the field fx, after how many
challenges the text changes no more, is 0: it reads none. Where `k4PubG` returns nothing the lot
answers nowhere.

Not shown here. NOTHING IS SHOWN HERE: a definition claims nothing. WHERE THE LOT ANSWERS NOTHING, A
LAYING BY LOTS LAYS ANOTHER LOT's ANSWER OR ZERO: whether it answers has to be a public fact:
`k4MaskLotG_isSome` (Law/W/MaskLotGPub.lean). THE LOT IS NOT LAID: it is the text, number and fence
of a lemma on the lot of the message's sender. THE NUMBER STANDS ON A SEARCH WITH THE DEFAULT 0
(`k4MaskMsg`, Lot/MaskNum.lean): where no message of the segment has mask rows it answers all the
same, in silence. NOR IS g FENCED: at g ≥ 12 the number is what the search's default gives, and may
be another message's: said here without a theorem; no theorem of this folder shows it (near it:
`maskNums_written_no`, Law/W/MaskNumsApart.lean: at the written values the numbers at 25 and 27 are
one). K4's OTHER ASK OF A MESSAGE,
one entry of the index masks' message, has a lot of its own (Lot/IndexLotG.lean). Lean compiles it
as a definition with code; it has been run at nothing. That any list of lots holds it. NO LAW STANDS
AT A LIST THAT HOLDS IT: at a list that lacks the lot of the message's sender the laying lays 0 at
the message's other entries (Law/W/MaskLotGPub.lean's head). A program's walk from import to import,
which reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 10 modules under Johnson/Goal/ and at 3 under
Johnson/Bridge/: floors; the 10 come with the number and with `k4PubG`. Nothing on soundness, on
completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskTxtG
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskNum
import Johnson.Desc.ProofFile.Honest.K4.Lot.PubG
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open ProofFile.Honest.FirstThread (MsgLot)

/-- **K4's LOT OF GROUP g FOR ITS SEGMENT's MASK ROW, of the public part and g alone.** This is a
definition; it claims nothing. -/
def k4MaskLotG {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (X : Type) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ) :
    MsgLot Bk (Local W₀ Rc Xi Tr) :=
  ⟨k4MaskNum Zp (2 * g), 0, fun k w hd mask row place =>
    (k4PubG Zp g).bind fun Qp =>
      k4MaskTextG X cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo) k w hd mask row
        place⟩

end ProofFile.Honest.K4.Lot
