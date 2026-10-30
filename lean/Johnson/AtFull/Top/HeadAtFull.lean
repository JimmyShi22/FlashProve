-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Top/HeadAtFull.lean: THE HEAD's EXAMPLE, AS A STATEMENT WITH TWO PREMISES
THAT ARE NOT PAID IN THIS FILE: at the stored full-size files VerifierAndGoals.storedPublicFiles: if the key file's seat
returns (`theKeyLaid`) and the proof file's seat returns (`theProofLaid`), then the test `protocolDataWellFormed`
accepts there, the named condition `P5J.rowsRead` holds there, and the head has a member
(`P5J.AtMgA`). Calls alone: nothing is evaluated here. A law file; no running text imports it.

THE GROUND. IT STANDS OVER THE PROOF FILE's FOURTEEN ENTRY TESTS (`LPFD.lawsAsk`) and would not
compile over thirteen: `P5J.owed_of_live`, which it calls, spends the fourteenth row's law.
With fourteen tests the proof file's seat returns only where the fourteenth test
`rowsMadeB` accepts: so the arms' test and the written rows' closed test are no premises here: they
are owed inside the second premise (Johnson/AtFull/Top/RowFourteen.lean has that test's accept from
them, with no use of protocolDataWellFormed).

Statements.
  `theLive_zFull_of_two`: the two returns ⊢ protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true.
  `headMember_zFull_of_two`: the two returns ⊢ that, and P5J.rowsRead storedPublicFiles, and ∃ Zp Np cF x,
    P5J.AtMgA secondHashFunction storedPublicFiles (dpZ storedPublicFiles) (theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x.
How: the scope and the files' reading at storedPublicFiles are theorems (`VerifierAndGoals.filesRead.full`) ·
`FlashProve.theLive_of_two` (Johnson/AtFull/Top/LiveOfTwo.lean) · `P5J.owed_of_live`
(Johnson/Goal/Skeleton/OwedOfLive.lean) · `P5J.head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean). `P5J.head_of_live`
(Johnson/P5J/HeadOfLive.lean) is these last two at every Z in scope; it is not imported, to keep the
imports few.

Limits. NEITHER PREMISE IS SHOWN IN THIS FILE: no example of the head is shown in this file; two, at
storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits
say what they are worth. That both
seats return at storedPublicFiles, and that protocolDataWellFormed accepts there, was seen by a run of Lean's evaluator, at the
term, over fourteen entry tests: EVALUATED, NOT PROVED IN THIS FILE. An accept of protocolDataWellFormed is no sign
that the verifier accepts any proof: whether the three runs behind it accept one is not said here.
At the second hash function. The full size alone. Nothing on soundness.
-/
import Johnson.AtFull.Top.LiveOfTwo
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open VerifierAndGoals FlashProve
open VerifierAndGoals.AtTheName (dpZ)

/-- **The two returns give that protocolDataWellFormed accepts at the stored full-size files.** -/
theorem theLive_zFull_of_two
    {K : OnBytes.Maker.WholeD × (OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
      _root_.Run.PQ.View → Bool)}
    {P : OnBytes.Maker.WholeD × (LPFD.Full.XF × OnBytes.Flat.RecFull → _root_.Run.PQ.View →
      _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)}
    (keyLaid : theKeyLaid (asDescriptionFiles storedPublicFiles) = .ok K)
    (proofLaid : theProofLaid (asDescriptionFiles storedPublicFiles) = .ok P) : protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true :=
  theLive_of_two storedPublicFiles VerifierAndGoals.filesRead.full.1 keyLaid proofLaid

/-- **The head has a member at the stored full-size files, from the two returns alone.** -/
theorem headMember_zFull_of_two
    {K : OnBytes.Maker.WholeD × (OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
      _root_.Run.PQ.View → Bool)}
    {P : OnBytes.Maker.WholeD × (LPFD.Full.XF × OnBytes.Flat.RecFull → _root_.Run.PQ.View →
      _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)}
    (keyLaid : theKeyLaid (asDescriptionFiles storedPublicFiles) = .ok K)
    (proofLaid : theProofLaid (asDescriptionFiles storedPublicFiles) = .ok P) :
    protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧ P5J.rowsRead storedPublicFiles ∧
      ∃ Zp Np cF x,
        P5J.AtMgA OnBytes.secondHashFunction storedPublicFiles (dpZ storedPublicFiles) (theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x := by
  obtain ⟨hs, pp, hr, -⟩ := VerifierAndGoals.filesRead.full
  have hl := theLive_zFull_of_two keyLaid proofLaid
  have ow := P5J.owed_of_live hl
  exact ⟨hl, ow.rows, P5J.head_exists_at_name storedPublicFiles hs hr hl ow⟩

end AtFull.Top

#print axioms AtFull.Top.theLive_zFull_of_two
#print axioms AtFull.Top.headMember_zFull_of_two
