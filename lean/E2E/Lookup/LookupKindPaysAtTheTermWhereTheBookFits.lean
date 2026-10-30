-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean: the kind "lookup" (K3) AT THE HONEST ONLINE PROVER's OWN MAKER
(`onlineMaker files`, E2E/TheHonestProver.lean): at every return of it: the sides of the first chain whose
place bears the kind K3 are the lookups' seated rows; the search at a site's place finds the site's seat,
by name; the kind pays (`KindPays`, Honest/Law/ReadyOfSides.lean) in the first chain where the book fits
every lookup, and idly in the two later chains. No definition, six theorems: calls alone; nothing is
evaluated.

What is shown, `made : onlineMaker files = .ok returned` being a premise of each.
  `lookupSidesAtTheTermAreSeats`   `SidesOfKindLookupAreSeats returned.Z returned.H.first`
  `lookupSeatIsFoundAtTheTerm`     at a site s of returned.Z the search at the site's place in
                                   returned.H.first finds `proverSideOfLookupInChainAtOneOwner` at the summands and the reader of
                                   `lookupFillingThrough matrixInput.weights id (tableCoins files)` at s
  `lookupKindPaysAtTheTermWhereTheBookFits`   the head, `BookFitsEveryLookup returned.B returned.Z` ⊢
                                   `KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K3`
  `lookupSideStandsAtEveryAddressAtTheTerm`   THE LAW ABOVE IS NOT IDLE: the head ⊢ at each link below 25
                                   and both sorts there is a site at the library's address `IM.k3Place`,
                                   of the kind K3; the search there finds the site's seat, by name; a
                                   member of the head's first chain stands there
  `lookupKindPaysAtTheTermInTheSharedChain`, `lookupKindPaysAtTheTermInTheSecondChain`   `KindPays` at
                                   the kind K3 in these chains: IDLY, BY NATURE: no member of them is at a
                                   place of the kind

How. `onlineFilling files` is, by its text, the wide filling at `matrixInput` read through
`tableCoins files`: each statement is one call of Honest/K3/Term/LookupSidesReadThrough.lean or of
Honest/K3/Term/LookupKindPays.lean.

Another road. `kindPays_online`, `kindPays_online_of_base` (Honest/Law/KindPaysOnline.lean) are the general road from a kind's
payment at the wide filling to the honest online prover's. This file does not take it: a lookup's seated row read through is
again a seated row, and `lookupSidePays` is general in the reader.

Hypotheses that remain. made: that the maker returns (T1's `MakerReturns`). The head (`P5J.AtMgA`), in the
third and the fourth. `BookFitsEveryLookup`, in the third: its payer lies in the side library:
AtFullSide/Honest/K3/Term/LookupKindPaysAtTheTerm.lean has the statement without it.

Limits. "The kind pays" says that `chainSteps` (Honest/Frame.lean) returns at the lookups' members: it is one
of the things that `ready` asks: nothing on whether a part plays, a round is reached or a verifier accepts.
At the description `returned.F`: that it is the one at which the prover's family is laid is T1's proposition
`ReturnIsTheDescription` (E2E/TheHonestProver.lean): shown, at files in scope that are live, by
`returnIsTheDescription_in_scope` (AtFullSide/K1/HeadAtReturn.lean): not called here.
The full size and the format's second hash function alone. All limits of the files called hold here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSidesReadThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files}

/-- **At the honest online prover every side of the kind "lookup" is a lookup's seated row.** -/
theorem lookupSidesAtTheTermAreSeats (made : onlineMaker files = .ok returned) :
    SidesOfKindLookupAreSeats returned.Z returned.H.first :=
  lookupSidesOfWideFillingReadThroughAreSeats made

/-- **The search at a site's place finds the site's seat, by name.** -/
theorem lookupSeatIsFoundAtTheTerm (made : onlineMaker files = .ok returned) (s : Site)
    (hs : s ∈ lookSites returned.Z) :
    returned.H.first.find? (fun q => q.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
        ((lookupFillingThrough matrixInput.weights id (tableCoins files) returned.Z).jobs s).asked
        ((lookupFillingThrough matrixInput.weights id (tableCoins files) returned.Z).wit s) s.at_) :=
  lookupSeatIsFoundReadThrough made s hs

/-- In the shared chain the kind pays idly: it has no member there. -/
theorem lookupKindPaysAtTheTermInTheSharedChain (made : onlineMaker files = .ok returned) :
    KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared KindName.K3 :=
  lookupKindPaysInTheSharedChain (atPure_ok made).2.2.1 _ _

/-- In the second chain too. -/
theorem lookupKindPaysAtTheTermInTheSecondChain (made : onlineMaker files = .ok returned) :
    KindPays returned.B 2 returned.F.second.blocksInOrder returned.H.second KindName.K3 :=
  lookupKindPaysInTheSecondChain (atPure_ok made).2.2.1 _ _

variable {D : WholeD} {r : LPFD.Full.RunPF} {publicPart : ProofFile.Pub} {places : H2U.Places4}
  {firstChain : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE KIND "LOOKUP" PAYS AT THE HONEST ONLINE PROVER, WHERE THE BOOK FITS.** Conditional: the head;
made; the returned book fits every lookup. -/
theorem lookupKindPaysAtTheTermWhereTheBookFits
    (h : AtMgA OnBytes.secondHashFunction files D r publicPart places firstChain x)
    (made : onlineMaker files = .ok returned)
    (hBook : BookFitsEveryLookup returned.B returned.Z) :
    KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first KindName.K3 :=
  lookupKindPaysReadThrough h made hBook

/-- **THE LAW ABOVE IS NOT IDLE.** Conditional: the head; made. -/
theorem lookupSideStandsAtEveryAddressAtTheTerm
    (h : AtMgA OnBytes.secondHashFunction files D r publicPart places firstChain x)
    (made : onlineMaker files = .ok returned) (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ s ∈ lookSites publicPart, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place.kind = KindName.K3 ∧
      returned.H.first.find? (fun q => q.place == s.at_.place) =
        some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩
          ((lookupFillingThrough matrixInput.weights id (tableCoins files) publicPart).jobs s).asked
          ((lookupFillingThrough matrixInput.weights id (tableCoins files) publicPart).wit s)
          s.at_) ∧
      ∃ b ∈ (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).first.blocksInOrder,
        b.place = s.at_.place :=
  lookupSideStandsAtEveryAddressReadThrough h made l hl d

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupSidesAtTheTermAreSeats
#print axioms AtPublicFiles.Lookup.lookupSeatIsFoundAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheTermInTheSharedChain
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheTermInTheSecondChain
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheTermWhereTheBookFits
#print axioms AtPublicFiles.Lookup.lookupSideStandsAtEveryAddressAtTheTerm
