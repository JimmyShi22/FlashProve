-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyAtSegment.lean: the kind "the code switch" (K2): THE ROWS
THAT `segmentGroupRows` (Honest/K2/Closing.lean) LAYS ANEW AT ANOTHER SWITCH FOR A MESSAGE OF A SWITCH's
OWN SENDING ARE THE ROWS THAT THE SENDER LAID: `segmentRows_row` (Honest/K2/Law/RowsOfSegment.lean)
joined with `copy_carried` (Honest/K2/Law/CopyOne.lean). One statement with its proof; no
definition.

  `copy_at_segment`   R.rows[n]? = some (V n), at each message n of the sender's sending but the
                      last

ITS PREMISES, BY KIND. RETURNS: both switches are handed their stretches; the sender's laying
returns V; `segmentGroupRows` returns R. PUBLIC, ON THE SEGMENT: its sizes are the sender's; its first
sending is the sender's `switchSent`. PUBLIC, ON THE BOOK: THE BOOK's TIE of `copy_carried`, at the
entry number base + n of what the other switch carries. ON THE DATA: hd: the main rows of message n
are one at both sides: at ONE letter W for what the fold in front left: that the other switch
reckons the sender's own W is not said here.

Limits. All Limits of CopyOne.lean stand. None of the premises is paid here. Not the last message,
the next fold's mask. Nothing on the later sendings of a segment, nor on the first segment, whose
sender is no switch. An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyOne
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsOfSegment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {Bk : ProverCoinCounts}

/-- **THE JOIN, AT ONE MESSAGE.** p₀: the sender. p: the switch that lays anew. S: the segment into
which p₀ leads. W: what the fold in front of p₀ left: one letter at both sides. -/
theorem copy_at_segment (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {S : SegmentPub} {W : Left} {prevKept : List OnBytes.OracleShape}
    {own own₀ : Nat → Nat → Nat → Cb.Gl.E} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable S (some W) prevKept own (Stretch.carried p.carries c.2.2) base
      withFresh = .ok R)
    (hS : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W own₀) c₀.1 = .ok V)
    {n : Nat} (hn : n < (switchSent p₀.sizes p₀.others).size - 1)
    (hd : mainRows p₀.sizes W own n = mainRows p₀.sizes W own₀ n) (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[base + n]? =
      some e)
    (t1 : e.owner = ⟨p₀.place, 0⟩)
    (t2 : e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) n)
    (t3 : e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n)) :
    R.rows[n]? = some (V n) := by
  obtain ⟨r, hr, hg⟩ := segmentRows_row hR (by rw [hSent]; exact hn)
  have hc := copy_carried ch p₀ p k c₀ h₀ c h hV (by omega) (base + n) e he t1 t2 t3
  rw [foldAt_switchFresh p₀.sizes p₀.others p₀.foldVars (by omega)] at hc
  have hdat : dataAtOf S (some W) own n = mainRows p₀.sizes W own₀ n := by
    show mainRows S.sizes W own n = _
    rw [hS, hd]
  rw [hS, hSent, hdat, hc] at hg
  rw [hr, Except.ok.inj hg]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copy_at_segment
