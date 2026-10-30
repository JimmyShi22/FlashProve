-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/Term/LookupKindPaysAtTheTerm.lean: **THE KIND "LOOKUP" (K3) PAYS AT THE HONEST ONLINE
PROVER** (`onlineMaker files`, E2E/TheHonestProver.lean), in the sense of `KindPays`
(Honest/Law/ReadyOfSides.lean): at every return of the maker, under the head (`P5J.AtMgA`) alone; so at
every set of public files in the goals' scope at which the verifier's test on the public files says yes;
and these premises can be met together. No definition, five theorems: calls alone; nothing is evaluated
here.

What is shown.
  **`lookupKindPaysAtTheTerm`**   the head, made ⊢
                          `KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K3`
  `lookupKindPaysAtTheTermAtTheHeadsChain`   the same at the head's own letters for the first chain:
                          `(P5J.F0T secondHashFunction publicPart places firstChain).first.blocksInOrder`
  `lookupKindPaysAtLiveFilesInScope`   `VerifierAndGoals.InScope files`, `protocolDataWellFormed (asDescriptionFiles files)`, made ⊢ the first
  `lookupKindPaysAtTheTermIsMet`   scope, live ⊢ THERE IS a return of the maker; there the kind pays; and
                          at each link below 25 and both sorts the search in returned.H.first at the
                          library's address, of the kind K3, finds a site's seat by name, at the place of
                          a member of returned.F's first chain: the end is not idle
  `lookupKindPaysAtTheTermIsMetAtTheStoredFiles`   NO PREMISE: the same at `VerifierAndGoals.storedPublicFiles`: so scope and
                          live can be met

How. `lookupKindPaysAtTheTermWhereTheBookFits`, `lookupSideStandsAtEveryAddressAtTheTerm`
(E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean); `bookFitsEveryLookupUnderTheHead` (LookupLevelsUnderTheHead.lean
beside this file); `P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) with `P5J.owed_of_live`
(Johnson/Goal/Skeleton/OwedOfLive.lean) and `LPFPol.read_of_scope` (Johnson/LPFPol/LiveAtPolicy.lean);
`makerReturns` (AtFullSide/Honest/HonestProverLaws.lean); `headMember_zFull`
(AtFullSide/Top/HeadMemberAtFull.lean), `VerifierAndGoals.filesRead`.

Why here. The book's payer and `makerReturns` lie in this side library.

Another road. `kindPays_online`, `kindPays_online_of_base` (Honest/Law/KindPaysOnline.lean) are the general road from a kind's
payment at the wide filling to the honest online prover's. This file does not take it: a lookup's seated row read through is
again a seated row, and `lookupSidePays` is general in the reader.

Hypotheses that remain. In the first two: the head, made. In the third: scope, live, made. In the fourth:
scope, live. In the fifth: none.

Limits. "The kind pays" says that `chainSteps` (Honest/Frame.lean) returns at the lookups' members: it is one
of the things that `ready` asks: nothing on whether a part plays, a round is reached or a verifier accepts.
The two later chains: E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean. At the description `returned.F`: that it is the
one at which the prover's family is laid is T1's proposition `ReturnIsTheDescription` (E2E/TheHonestProver.lean):
shown, at files in scope that are live, by `returnIsTheDescription_in_scope` (AtFullSide/K1/HeadAtReturn.lean): not called here;
LookupKindPaysAtTheLaidProver.lean [not in this library] beside this file calls it. The stored
example's weights are synthetic (the head of AtFullSide/Top/HeadMemberAtFull.lean says so).
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
The full size and the format's second hash
function alone.
All limits of the files called hold here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LookupLevelsUnderTheHead
import AtFullSide.Honest.HonestProverLaws
import AtFullSide.Top.HeadMemberAtFull
import E2E.Lookup.LookupKindPaysAtTheTermWhereTheBookFits
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

/- Lean compares the named files by their name: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files}

section
variable {D : WholeD} {r : LPFD.Full.RunPF} {publicPart : ProofFile.Pub} {places : H2U.Places4}
  {firstChain : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE KIND "LOOKUP" PAYS AT THE HONEST ONLINE PROVER.** Conditional: the head; made. -/
theorem lookupKindPaysAtTheTerm (h : AtMgA OnBytes.secondHashFunction files D r publicPart places firstChain x)
    (made : onlineMaker files = .ok returned) :
    KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first KindName.K3 :=
  _root_.AtPublicFiles.Lookup.lookupKindPaysAtTheTermWhereTheBookFits h made
    (bookFitsEveryLookupUnderTheHead h made)

/-- The same at the head's own letters for the first chain. -/
theorem lookupKindPaysAtTheTermAtTheHeadsChain
    (h : AtMgA OnBytes.secondHashFunction files D r publicPart places firstChain x)
    (made : onlineMaker files = .ok returned) :
    KindPays returned.B 0 (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).first.blocksInOrder
      returned.H.first KindName.K3 := by
  rw [← (atPure_at_laid h.laid made).2]
  exact lookupKindPaysAtTheTerm h made

end

/-- **At every set of public files in scope at which the verifier's test on them says yes.**
Conditional: scope; live; made. -/
theorem lookupKindPaysAtLiveFilesInScope (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineMaker files = .ok returned) :
    KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first KindName.K3 := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨_, _, _, _, h⟩ := P5J.head_exists_at_name files scope read live (P5J.owed_of_live live)
  exact lookupKindPaysAtTheTerm h made

/-- **THE PREMISES CAN BE MET TOGETHER, AND THE END IS NOT IDLE.** Conditional: scope; live. -/
theorem lookupKindPaysAtTheTermIsMet (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned : OnlineReturn files, onlineMaker files = .ok returned ∧
      KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first KindName.K3 ∧
      ∀ l, l < 25 → ∀ d : Bool, ∃ s ∈ lookSites returned.Z, s.at_.place = IM.k3Place l d ∧
        s.at_.place.kind = KindName.K3 ∧
        returned.H.first.find? (fun q => q.place == s.at_.place) =
          some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
            ((lookupFillingThrough matrixInput.weights id (tableCoins files) returned.Z).jobs
              s).asked
            ((lookupFillingThrough matrixInput.weights id (tableCoins files) returned.Z).wit s)
            s.at_) ∧
        ∃ b ∈ returned.F.first.blocksInOrder, b.place = s.at_.place := by
  obtain ⟨returned, made⟩ := makerReturns files scope live
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨_, _, _, _, h⟩ := P5J.head_exists_at_name files scope read live (P5J.owed_of_live live)
  obtain ⟨eZ, eF⟩ := atPure_at_laid h.laid made
  refine ⟨returned, made, lookupKindPaysAtTheTerm h made, fun l hl d => ?_⟩
  obtain ⟨s, hs, -, -, e1, e2, hf, b, hb, e3⟩ :=
    _root_.AtPublicFiles.Lookup.lookupSideStandsAtEveryAddressAtTheTerm h made l hl d
  rw [eZ, eF]
  exact ⟨s, hs, e1, e2, hf, b, hb, e3⟩

/-- **At the stored full-size files: no premise.** -/
theorem lookupKindPaysAtTheTermIsMetAtTheStoredFiles :
    ∃ returned : OnlineReturn VerifierAndGoals.storedPublicFiles, onlineMaker VerifierAndGoals.storedPublicFiles = .ok returned ∧
      KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first KindName.K3 ∧
      ∀ l, l < 25 → ∀ d : Bool, ∃ s ∈ lookSites returned.Z, s.at_.place = IM.k3Place l d ∧
        s.at_.place.kind = KindName.K3 ∧
        returned.H.first.find? (fun q => q.place == s.at_.place) =
          some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
            ((lookupFillingThrough matrixInput.weights id (tableCoins VerifierAndGoals.storedPublicFiles)
              returned.Z).jobs s).asked
            ((lookupFillingThrough matrixInput.weights id (tableCoins VerifierAndGoals.storedPublicFiles)
              returned.Z).wit s) s.at_) ∧
        ∃ b ∈ returned.F.first.blocksInOrder, b.place = s.at_.place :=
  lookupKindPaysAtTheTermIsMet VerifierAndGoals.storedPublicFiles VerifierAndGoals.filesRead.full.1
    AtFullSide.Top.headMember_zFull.1

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysAtTheTerm
#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysAtTheTermAtTheHeadsChain
#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysAtLiveFilesInScope
#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysAtTheTermIsMet
#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysAtTheTermIsMetAtTheStoredFiles
