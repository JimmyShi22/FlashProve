-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyOfTests.lean: the kind "the code switch" (K2):
`copy_at_closing` (Honest/K2/Law/CopyAtClosing.lean) WITH BOTH ITS PREMISES ON THE BOOK PAID BY THE
YES OF THE KIND's TWO PUBLIC TESTS ON THE BOOK's CARRYING ENTRIES (`carriedFits`, `carriedSame`,
Honest/K2/Law/CarriedAsks.lean). Statements with their proofs; no definition.

  `tie_of_tests`    THE BOOK's TIE of `copy_carried`, out of the first test's yes
  `copy_of_tests`   THE END: R.rows[n]? = some (V n)

WHAT COMES IN FOR THE TWO PREMISES ON THE BOOK, ALL PUBLIC: hs: `carriedSame Bk p₀ p` says yes · hf:
`carriedFits Bk ps p` says yes · hfind: p₀ is the first place of the list ps whose part stands at
its address · at each message n: hF: the member of p's own list `front` whose number is n behind all
messages of the segments in front of p₀ names p₀'s part and message n.

Limits. The Limits of CopyAtClosing.lean and CarriedAsks.lean stand. THE TESTS ARE EVALUATED AT NO
REAL BOOK HERE: that they say yes is a premise. hfind and hF are facts on our own public lists: not
paid here. The premises on returns, on the places and segments, on the data and on the challenges
stay as they are. An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {Bk : ProverCoinCounts}

/-- **THE BOOK's TIE, OUT OF THE FIRST TEST's YES.** -/
theorem tie_of_tests {ps : List SwitchPlace} {p₀ p : SwitchPlace}
    (hf : carriedFits Bk ps p = true)
    (hfind : (ps.find? fun q => (⟨q.place, 0⟩ : Addr) == ⟨p₀.place, 0⟩) = some p₀)
    {i n : Nat} {ct : Due} (hF : p.front[i]? = some (⟨p₀.place, 0⟩, n, ct)) :
    ∃ e : Ahead,
      ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
      e.owner = ⟨p₀.place, 0⟩ ∧
      e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
        (switchFresh p₀.sizes p₀.others p₀.foldVars) n ∧
      e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
        (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n) :=
  carriedFits_run hf hF (switchRunAt_of hfind n)

/-- **THE END.** V: the rows that the sender laid. -/
theorem copy_of_tests (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) {ps : List SwitchPlace} (hf : carriedFits Bk ps p = true)
    (hfind : (ps.find? fun q => (⟨q.place, 0⟩ : Addr) == ⟨p₀.place, 0⟩) = some p₀)
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ W : Left}
    (hW₀ : lotClosingAt lay segs p₀ D Rd heard₀ (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (hW : lotClosingAt lay segs p D Rd heard (Stretch.carried p.carries c.2.2) = .ok W)
    (hl : p₀.link ≤ p.link)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) = lotOwn segs p D Rd heard (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {S : SegmentPub} {rest : List SegmentPub} (hS : (segs.take p.link).drop p₀.link = S :: rest)
    (hSz : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    {own₀ : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W₀ own₀) c₀.1 = .ok V) :
    ∃ R kept, segmentGroupRows freshTable S (some W₀) kept
        (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length))
        (Stretch.carried p.carries c.2.2) (0 + ((segs.take p₀.link).map (·.messages)).sum) true =
          .ok R ∧
      ∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
        mainRows p₀.sizes W₀ (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length)) n =
          mainRows p₀.sizes W₀ own₀ n →
        ∀ ct : Due, p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + n]? =
            some (⟨p₀.place, 0⟩, n, ct) →
          R.rows[n]? = some (V n) := by
  obtain ⟨R, kept, hR, hall⟩ := copy_at_closing ch p₀ p k c₀ h₀ c h (carriedSame_gives hs) hW₀ hW hl
    ho hg hS hSz hSent hV
  refine ⟨R, kept, hR, fun n hn hd ct hF => ?_⟩
  obtain ⟨e, he, t1, t2, t3⟩ := tie_of_tests hf hfind hF
  exact hall n hn hd e he t1 t2 t3

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.tie_of_tests
#print axioms ProofFile.Honest.K2.Law.copy_of_tests
