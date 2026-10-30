-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeyAtWalk.lean: the kind "the code switch" (K2): THE ROWS OF A
SWITCH's OWN SENDING, WHOLE, AT THE LETTERS OF A LATER SWITCH's OWN WALK: y': what the later
switch's closing (`closingFrom`, Honest/K2/Closing.lean) returns over the segments in front of the
sender p₀. Whatever `segmentGroupRows` returns at y''s two halves and y''s number for the segment into
which p₀ leads holds, message by message, the rows that p₀ laid; and as its fold's mask what p₀ laid
as its last message. One statement with its proof: a join; no definition.

  `key_at_walk`   R.rows[n]? = some (V n) in front of the last message; R.fresh = some (V q) at it

WHY THESE LETTERS. `copy_at_closing` (Honest/K2/Law/CopyAtClosing.lean) says that there are such
rows R; a caller that holds a return of `segmentGroupRows` of its own must know that it is the same call.
Here R is the caller's: any return at (y'.1.map (·.1)), ((y'.1.map (·.2)).getD []), y'.2. THE STEP:
y' is what the sender's own closing returned: two returns of one call (`closingFrom_grows`,
Honest/K2/Law/ClosingSame.lean).

ITS PREMISES, BY KIND. RETURNS: both switches are handed their stretches; the sender's closing
returns W₀; the later walk returns y'; the sender's laying returns V; `segmentGroupRows` returns R. THE
TWO TESTS ON THE BOOK SAY YES (hs, hf), with hfind. PUBLIC, ON THE SEGMENT: its sizes, first sending
and fold's row variables are the sender's. ON THE DATA AND THE CHALLENGES: ho, hg. AT EACH MESSAGE:
hF, on our own list `front`; in front of the last: hd, on the data; at the last: it has no main row.

By: `lotClosingAt_inv`, `closingFrom_next` (CopyAtClosing.lean) · `givesAll_carried`
(Honest/K2/Law/CarriedSame.lean) · `tie_of_tests` (Honest/K2/Law/CopyOfTests.lean) ·
`copy_at_segment`, `copyMask_at_segment` (Honest/K2/Law/CopyAtSegment.lean, CopyMaskAtSegment.lean).

Limits. ROWS AGAINST ROWS: THE END NAMES THE SENDER's ROWS V, NOT A WITNESS's WORDS: no law here or
beneath says what V holds of such words: so it opens no law that asks the entries of R against
words. THAT p COMES LATER THAN p₀ IS MEANT, NOT ASKED: no premise holds the two links against each
other. All Limits of these files stand. None of the premises is paid here. Nothing on the later
sendings of a segment, nor on the first segment. THE TESTS ARE EVALUATED AT NO REAL BOOK HERE. An
equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyOfTests
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyMaskAtSegment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {Bk : ProverCoinCounts}

/-- **THE KEY, AT THE WALK's OWN LETTERS.** p₀: the sender. p: the later switch. own': the own data
at which the caller's `segmentGroupRows` lays the segment: a letter. -/
theorem key_at_walk (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) {ps : List SwitchPlace} (hf : carriedFits Bk ps p = true)
    (hfind : (ps.find? fun q => (⟨q.place, 0⟩ : Addr) == ⟨p₀.place, 0⟩) = some p₀)
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ : Left}
    (hW₀ : lotClosingAt lay segs p₀ D Rd heard₀ (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) = lotOwn segs p D Rd heard (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn segs p D Rd heard) heard
      (Stretch.carried p.carries c.2.2) (segs.take p₀.link) 0 0 none = .ok y')
    {Sg : SegmentPub} (hSz : Sg.sizes = p₀.sizes)
    (hSent : Sg.sent.headD #[] = (switchSent p₀.sizes p₀.others)) (hFv : Sg.foldVars = p₀.foldVars)
    {own₀ own' : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W₀ own₀) c₀.1 = .ok V)
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) own'
      (Stretch.carried p.carries c.2.2) y'.2 true = .ok R) :
    (∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
      mainRows p₀.sizes W₀ own' n = mainRows p₀.sizes W₀ own₀ n →
      ∀ ct : Due, p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + n]? =
          some (⟨p₀.place, 0⟩, n, ct) →
        R.rows[n]? = some (V n)) ∧
    ∀ q, q + 1 = (switchSent p₀.sizes p₀.others).size →
      ((switchSent p₀.sizes p₀.others).getD q default).shape.mainRows = 0 →
      ∀ ct : Due, p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + q]? =
          some (⟨p₀.place, 0⟩, q, ct) →
        R.fresh = some (V q) := by
  obtain ⟨x₀, kept, hx₀, e₀⟩ := lotClosingAt_inv hW₀
  have e1 := closingFrom_grows freshTable
    (givesAll_carried ch p₀ p k c₀ h₀ c h (carriedSame_gives hs)) (segs.take p₀.link) 0 0 none ho
    hg x₀ hx₀
  have exy : x₀ = y' := Except.ok.inj (e1.symm.trans hy')
  subst exy
  have eb := closingFrom_next freshTable _ heard₀ _ (segs.take p₀.link) 0 0 none x₀ hx₀
  rw [e₀, eb] at hR
  have hR' : segmentGroupRows freshTable Sg (some W₀) kept own' (Stretch.carried p.carries c.2.2)
      (0 + ((segs.take p₀.link).map (·.messages)).sum) true = .ok R := hR
  refine ⟨fun n hn hd ct hF => ?_, fun q hq hm ct hF => ?_⟩
  · obtain ⟨e, he, t1, t2, t3⟩ := tie_of_tests hf hfind hF
    exact copy_at_segment ch p₀ p k c₀ h₀ c h hR' hSz hSent hV hn hd e he t1 t2 t3
  · obtain ⟨e, he, t1, t2, t3⟩ := tie_of_tests hf hfind hF
    exact copyMask_at_segment ch p₀ p k c₀ h₀ c h hR' hSz hSent hFv hV hq hm e he t1 t2 t3

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.key_at_walk
