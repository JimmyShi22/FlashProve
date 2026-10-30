-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtMg.lean: the proofs of `FormsAtLink`, `MergedAtMg` and `WoAtMg`
(Johnson/Desc/K11/Exchange/AtMgStatement.lean), to the letter. Lemmas; none of the library's goals.

How. At the merge's run the readers of a link are the run's own reader: the library's equation
`forms_link_merge` (Johnson/Top/H0/MergeLaw/MergedAtLink.lean); the table's sentence reads a reader
at that one answer alone. Which run stands under (9, "merged") at the head's sort: `runsAt_of`,
`runs_head` (Johnson/Desc/Sound/MgAt/Runs.lean). The readers at a segment: `readersAt_some`
(Johnson/Desc/First/Batch/ReadersAt.lean). The two fields of the composed meaning: by definition
(`mgAll_forms`, `mgAll_wo`, Johnson/Desc/Sound/MgAll.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtMgStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc.First.MergeLaw (mergeStates forms_link_merge)
open VerifiableInference.Desc.K9 (Readers readersOfLink holesAt readersAt_some readerOf)
open VerifiableInference.Desc.Sound (formsQ formsQA runsAt runsAt_of runs_head seatTab)

/-- **From the run's own reader to a link's readers.** -/
theorem formsAtLink : FormsAtLink := by
  intro X mH m l own piece run name r s rd hrun hst hr h
  obtain ⟨a, R, h1, h2, h3, h4⟩ := h
  refine ⟨a, R, h1, ?_, h3, h4⟩
  rw [forms_link_merge X mH m l piece run name hrun r hst hr s]
  exact h2

/-- **The field forms of the composed meaning at (9, "merged").** -/
theorem mergedAtMg : MergedAtMg := by
  intro Xi P Tok rows cols nR X D Mg m l name r z b y w hsub hlk hst hr h
  show (∀ p ∈ D.runs m 9 "merged",
      if D.ah p.1 p.2 = true then
        formsQA (D.N.sent m) (D.N.group m) (D.Rd m) p.1 p.2 b (seatTab D.cs D.arr D.ms w)
      else formsQ (D.Rd m) (D.N.group m) p.1 p.2 b (seatTab D.cs D.arr D.ms w)) ∧
      ("merged" = "weights" → D.wt m (z, b) y w)
  refine ⟨fun p hp => ?_, fun e => absurd e (by decide)⟩
  have e : D.runs m 9 "merged" = [(8, "the merge")] := by
    show runsAt D.links m 9 "merged" = _
    rw [runsAt_of D.links m .head hsub]
    exact runs_head.2.2.2.2.2.2.2
  rw [e] at hp
  rw [List.mem_singleton.1 hp]
  have hah : D.ah 8 "the merge" = false := by
    show ("the merge" == "K8.equations") = false
    decide
  rw [if_neg (by rw [hah]; simp)]
  have hRd : D.Rd m =
      readersOfLink (holesAt X (VerifiableInference.OnPublicFiles.headLink X) m l) l :=
    readersAt_some D.lk X _ m l hlk
  rw [hRd]
  exact formsAtLink X _ m l _ 8 "the merge" name r b _ (by decide) hst hr h

/-- **The field wo of the composed meaning.** -/
theorem woAtMg : WoAtMg := by
  intro Xi P Tok rows cols nR X D Mg m z b y w h
  exact h

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.formsAtLink
#print axioms Johnson.Desc.First.ForkMerge.Exchange.mergedAtMg
#print axioms Johnson.Desc.First.ForkMerge.Exchange.woAtMg
