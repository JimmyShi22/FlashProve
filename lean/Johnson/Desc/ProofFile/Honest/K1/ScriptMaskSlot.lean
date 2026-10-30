-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptMaskSlot.lean: THE SHARED "SENDING" (the kind K1) IN THE
FRAME FOR THE HONEST SIDE: WHAT THE KIND's WHOLE-MESSAGE TEXT msgTxt (Honest/K1/ScriptLots.lean)
ANSWERS AT AN ENTRY OF A MESSAGE's MASK ROWS, BY THE FORMAT's OWN NUMBER OF THE ENTRY: mask_slot
(Honest/K1/MaskLaw.lean) carried to the text. One statement and its proof; no definition.

  msgTxt_mask_slot   at a message whose table does not ride, at the entry number nu below rows *
                length: msgTxt at (true, nu % rows, nu / rows) is lentCut's value mapped to its
                value of the extension field number maskStart + nu

Limits. What is WRITTEN where: no sentence on what a mask row or an entry is for. It holds at all
entries of the mask rows, a pad's own places among them. "ce" GIVES 0 BEYOND THE PART's COUNT: THAT
THE NUMBER maskStart + nu LIES BELOW THE COUNT IS mask_in (Honest/K1/MaskLaw.lean: at n below the
messages' number, under the same two premises): WHOEVER SPENDS THE EQUATION CALLS IT, AND TAKES THE
PUBLIC TEST sendFits BY NAME. THAT NO VALUE OF THE CUT STANDS AT TWO PLACES IS NOT SAID HERE: within
one message the map from the entry's number is injective by its form; across messages, and against
tails, pads and main rows, nothing is said. Where the book does not cover the part's
count both sides are "none". That a ledger's slot number is nu, and that the message's number in
the witness is a given one, is not said here. An equation at each run. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {W Wl X : Type}

/-- **mask_slot, at the text.** Beyond the part's count "ce" gives 0: mask_in bars that at n below
the messages' number. -/
theorem msgTxt_mask_slot (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n ν : Nat)
    (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) (hr : J.ride n = none)
    (hν : ν < (shapeAt J.P n).maskRows *
      (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell) :
    msgTxt ch wit J own₀ n k w h true (ν % (shapeAt J.P n).maskRows)
        (ν / (shapeAt J.P n).maskRows) =
      (lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride)).map fun c =>
        ce c (maskStart J.P J.ride n + ν) := by
  unfold msgTxt
  congr 1
  funext c
  unfold scriptMsg rowsMsg rowsLaid
  simp only [if_true]
  exact mask_slot J.P J.ride _ c n ν hr hν

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.msgTxt_mask_slot
