-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupSimulatorAtTheTerm.lean: AT THE TERM. The kind "lookup" (K3): THE LOOKUPS' HAND-IN
FOR THEIR LOT OF ROWS WITH SIMULATORS, AT THE ONLINE PROVER (E2E/TheHonestProver.lean): at the lot
`lookupSimulatorLotAtTheTerm files` (LookupLotAtTheTerm.lean), at what the online maker returns: its
own description, book, public part and ground. Three theorems: joins. "Honest/" stands for
Johnson/Desc/ProofFile/Honest/.

  `lookupSimulatorHandInAtTheTerm`: at every set of public files that is in scope, is read and
  passes the library's test `protocolDataWellFormed`, at every return of `onlineMaker files`:
      (a) forgetting the lot's simulators gives the sixth of the lots of `onlineFilling files`;
      (b) `LookupHandIn` (Honest/K3/Term/LookupSimulatorHandIn.lean) at the return's description and
          book, at the lot's rows at the return's public part and ground. That is: the rows are
          fifty; no two are at one place; at the place of every sub-protocol of the kind K3 in the
          description's first chain there is one; and at every row:
          its place is of the kind K3, and is a sub-protocol's of the first chain  (`seat₁` of
          `file_owed_rows`, Honest/Thread/Rows.lean) · `Good` at the side of the row as laid, at the
          `pre` of its place, at the first chain's face and numbers, at the return's book and order
          of places, at the row's own On and bud  (`hand₁`) · bud at every number, challenges and
          positions  (so `BudDebts.bud₁`) · On from every thread and every `Said`  (`on₁`) · no part
          of it has a stop, public or private · no simulator of it reads anything but its own coins
          · no part of it reads anything of what has been shown before it.
  The threads, what is said and the falls are letters: nothing is asked of them.
  THIS THEOREM ALONE IS NOT WHAT IS TO BE COUNTED: OF A RUN (b) SAYS NOTHING WITHOUT the field fresh
  at the parts that own the coins which the lookups' parts spend. That debt is other authors'; it is
  no premise and no conclusion here.
  THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

READ THE HEAD OF Honest/K3/Term/LookupSimulatorAtTheHead.lean. In short: exact (a field of `Good`)
is THE SPENDER'S HALF ALONE: it says nothing of a run until the field fresh is paid at the parts
that own the coins which a lookup's parts spend (a part of the kind K1 at link 0, of the kind K2 at
links 1 to 24), and nothing here pays that. fresh is TRUE AND EMPTY at a lookup. On and bud
are "true". `Good` is at A and B "false": its fields plays and acc are met for nothing. Of `Owed`
(Honest/Owed.lean) there is handed in here: what the rule takes for its field `good` at the lookups'
rows; and, of its field `owed`, On and bud at the lookups' rows. That the walk's state is there
before a called part is not shown here.

By what. `P5J.head_of_live` (Johnson/P5J/HeadOfLive.lean). `lookupSimulatorHandInAtAnyFilling`
(AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean). `lookupSimulatorLotIsTheSixthLotAtTheTerm`
(LookupLotAtTheTerm.lean).

Not empty: `lookupSimulatorHandInIsNotEmptyAtTheTerm`: at every set of public files that is in
scope, is read and passes `protocolDataWellFormed` the online maker returns (`maker_returns`,
AtFullSide/K12/MakerReturnsAtLive.lean), so the sentence above speaks of a return. A witness, with
no premise: `lookupSimulatorHandInSpeaksOfTheFullSizeFiles`: the full-size public files
(`VerifierAndGoals.storedPublicFiles`) meet all three (`VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean;
`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean).

Beside it. That of the returned prover's own sides those at a place of the kind K3 are these rows'
sides, as lists, and so that no OTHER lot of `onlineFilling files` lays a side there:
`lookupHalvesAtTheTerm` (LookupHalvesAtTheTerm.lean [not in this library]). Not shown anywhere: the
one premise of `lookupKindHandsIn` (Honest/K3/Term/LookupKindHandsIn.lean), which is on lists with
simulators and parameters: it is the choice of whoever lays these lists as one term; nobody has.

What may be said of this sentence is not this file's to say.

Limits. One part at a time; at jobs right or wrong: nothing on what is sent. Nothing on any property
of the protocol.
-/
import E2E.Lookup.LookupLotAtTheTerm
import AtFullSide.Honest.K3.LookupSimulatorAtAnyFilling
import Johnson.P5J.HeadOfLive
import AtFullSide.K12.MakerReturnsAtLive
import AtFullSide.Top.LiveAtFull
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtFullSide.Honest.K3

/-- **THE LOOKUPS' HAND-IN AT THE ONLINE PROVER.** What it says and does not say: the head. -/
theorem lookupSimulatorHandInAtTheTerm (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned)
    (threads : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells → Thread returned.B returned.F.S₁ returned.F.Cl
      (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit Inst)
    (saids : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells → Nat → Coins returned.B →
      Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit → Prop)
    (falls : List (Fall returned.F.S₁)) :
    (onlineFilling files).lots[5]? = some (lookupSimulatorLotAtTheTerm files).toHLot ∧
      LookupHandIn returned.F returned.B
        ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G) threads saids falls := by
  obtain ⟨publicPart, places, firstChain, lookPlace, head⟩ := P5J.head_of_live files scope read live
  exact ⟨lookupSimulatorLotIsTheSixthLotAtTheTerm files,
    lookupSimulatorHandInAtAnyFilling head made (lookupFillingAtTheTerm files) threads saids falls⟩

/-- **IT IS NOT EMPTY**: where the files are in scope, are read and pass the library's test, the
online maker returns. -/
theorem lookupSimulatorHandInIsNotEmptyAtTheTerm (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned, onlineMaker files = .ok returned :=
  AtFullSide.K12.maker_returns files scope read live

/-- **A WITNESS**: the full-size public files are in scope, are read and pass the library's test; so
at them the online maker returns, and the hand-in speaks of that return. No premise. -/
theorem lookupSimulatorHandInSpeaksOfTheFullSizeFiles :
    ∃ returned, onlineMaker VerifierAndGoals.storedPublicFiles = .ok returned :=
  let ⟨scope, _, read, _⟩ := VerifierAndGoals.filesRead.full
  lookupSimulatorHandInIsNotEmptyAtTheTerm VerifierAndGoals.storedPublicFiles scope read AtFullSide.Top.theLive_zFull

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupSimulatorHandInAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupSimulatorHandInIsNotEmptyAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupSimulatorHandInSpeaksOfTheFullSizeFiles
