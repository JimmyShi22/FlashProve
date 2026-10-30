-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/IndexLotG.lean: one definition with code. NOTHING IS SHOWN
HERE.

What is here. THE LOT OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) OF
GROUP g FOR ITS ONE ENTRY OF THE INDEX MASKS' MESSAGE. IT IS NOT LAID: it is the text, number and
fence of a lemma on the lot of the message's sender. THE LOT TAKES THE GROUP's NUMBER ALONE: the
member's public data are made of the public part and g (`k4PubG`, Lot/PubG.lean). WHY NO LETTER FOR
THE PUBLIC DATA STANDS BESIDE g: by the text's own form that letter alone says which row's coins
are read: a lot that took both as letters, tied by nothing, would at one letter and two groups
answer alike at both groups' entries.

  `k4IndexLotG`   the lot, as a term of the structure `MsgLot` (Honest/Thread/ScriptLots.lean):
      number `k4IndexNum`, no challenge read, the text `k4IndexTextG` (Lot/IndexTxtG.lean) at
      `k4IndexRow` and `k4IndexPlace` (Lot/IndexNum.lean); «none» everywhere where `k4PubG` returns
      nothing.

WHERE THE TEXT SAYS «none» A LAYING OF THE SCRIPT BY LOTS (`Script.ofLots`) LAYS ANOTHER LOT's
ANSWER OR 0: a default stands there: in the laying, not in this text. Whether the text answers is a
function of public data: Law/W/IndexLotGIs.lean (`k4IndexTextG_isSome`, `k4IndexLotG_isSome`).

Not shown here. All: a definition claims nothing. ALL TWELVE GROUPS' LOTS BEAR ONE NUMBER n: they
part in row and place alone; that the twelve entries differ is said in Law/W/IndexApart.lean
(`k4IndexEntry_inj`, under the library's hypothesis on the public files), not here. What the text
reads of a run's coins: Lot/IndexTxtG.lean's head. Lean compiles it as a definition with code; it
has been run at nothing. It imports Lot/PubG.lean, whose head tells at how many modules under
Johnson/Goal/ and Johnson/Bridge/ a walk over its import lines stops. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Lot.PubG
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexTxtG
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open ProofFile.Honest.FirstThread (MsgLot)

/-- **K4's LOT OF GROUP g FOR ITS ENTRY OF THE INDEX MASKS' MESSAGE: IT TAKES g ALONE.** This is a
definition; it claims nothing. -/
def k4IndexLotG {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (X : Type) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Zp : ProofFile.Pub) (g : ℕ) :
    MsgLot Bk (Local W₀ Rc Xi Tr) :=
  ⟨k4IndexNum Zp, 0, fun k w hd mask r p =>
    (k4PubG Zp g).bind fun Qp =>
      k4IndexTextG X cells weights tokens look Qp (k4IndexRow Zp g) (k4IndexPlace Zp g) k w hd mask
        r p⟩

end ProofFile.Honest.K4.Lot
