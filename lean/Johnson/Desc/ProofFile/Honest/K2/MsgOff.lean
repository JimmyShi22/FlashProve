-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/MsgOff.lean: the kind "the code switch" (K2): A MESSAGE's TEXT OFF
ITS PAD: `switchMsgTxt` (ScriptLots.lean of this folder), made to answer nothing at the pad's places
(`padB`, Johnson/Desc/SeatAt.lean). One definition; no theorem; a definition claims nothing.

  `switchMsgOff`

Why so. The witness's table (`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean) reads a message's entries
off the pad from the Script's message, and at the pad's places from the Script's pad. In that
definition's own words: "WHOEVER READS A MESSAGE OFF A WITNESS READS IT THROUGH THIS: `w.msg n` at a
pad's place and `w.pad j t` outside the pad's places are pinned by nothing." The plan gives an
original and all its kept copies one number in the witness, and a pad to each seat. A kept copy's
pad places are laid off the later switch's own coins, the original's off its first sender's. So a
premise that ties the Script's message at that number to a copy's WHOLE text would ask, at the pad's
places, for entries off other coins than the first sender's tie asks for there: that the two part in
value at some coins is argued, not shown. Off the pad the two can agree. This text is for such a
premise.

Limits. A definition. That a copy's entries off the pad are the first sender's is said nowhere here.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (padB)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **Message number n, entry by entry, off its pad**: nothing at `padB`'s places; elsewhere what
`switchMsgTxt` answers. -/
def switchMsgOff (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (n : Nat) :
    Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → Nat → Nat → Option Cb.Gl.E :=
  fun k w h mask r j =>
    if padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j then none
    else switchMsgTxt ch D readers closing p n k w h mask r j

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchMsgOff
