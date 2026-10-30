-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's `onlineFilling`
(E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through `tableCoins`; its
return has another type; the crossing to it is not this folder's.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupSiteRestAtTheBaseProver.lean: the kind "lookup" (K3):
the seven hypotheses that `SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean) gathers hold at every
site, at the first list of the prover that `onlineProverFromPublicFiles` returns at the base filling, under the library's
hypothesis at the full size (`P5J.AtMgA`, "the head"). Two theorems: calls alone.

What is shown.
  `lookupSiteRestAtTheBaseProver`: from the head (`h`), the return (`hA`) and the site (`hsite`):
    there is a sub-protocol lot with `SiteRest Zp cF A.H.first s lot J wit`, where J and wit are the
    fast summands and their reader at the sources `sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z`.
  `lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart`: the same with the head's public part Zp in
    A.Z's place, and the reader written out: `askOf (sourcesAt id (I.weights Zp) (reqAt Zp) Zp)
    (whoOf s)`.

Which sources. `sourcesAt cells weights req Z` (Honest/K3/LotFilled.lean) at: cells := id (the
trace's type is `Cells` itself); weights := `I.weights` at the public part, I a letter of the type
`WiderIn W₀`; req := `reqAt` at the public part. These are the sources of the lot
`theLotInst id (I.weights A.Z)`, which the base filling lays for the kind (`LongLots.plain`,
Honest/AtPureWiderAt.lean).

Who pays which field. inLot, lotPlace: `lot_of_site` (Honest/K3/Law/LotOfSite.lean). half:
`lookupSideAtTheBaseProver` (Honest/K3/Term/LookupSideAtAnyFilling.lean). fits: `lookupSiteFits`
(Honest/K3/Term/LookupDrawWritten.lean). ok: `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean).
shapeIs, usedIs: `lookupShapeIsTheLayersShape`, `lookupUsedSlotsAreTheLedgersCount`
(Honest/K3/Term/LookupShapeAndUsedSlots.lean).

Hypotheses that remain. `h`: `P5J.AtMgA`. `hA`: `onlineProverFromPublicFiles` returns A at the base filling, at the
head's three files. `hsite`: s is a site of `lookSites Zp`.

Limits. The full size alone. That `onlineProverFromPublicFiles` returns is a premise. The side is the row that passes no
table on. `SiteRest` is a list of hypotheses of other theorems: by itself it says nothing on what a
side plays. Nothing on the values that the reader yields.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSideAtAnyFilling
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDrawWritten
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupShapeAndUsedSlots
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.AtFull.Shape.FaceAtSites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **`SiteRest` AT EVERY SITE, AT THE BASE PROVER's FIRST LIST.** The sources are
`sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z`. Conditional on the head, the return and the site. -/
theorem lookupSiteRestAtTheBaseProver (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A) (s : Site)
    (hsite : s ∈ lookSites Zp) :
    ∃ lot, SiteRest Zp cF A.H.first s lot
      (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).jobs s).asked)
      ((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).wit s) := by
  obtain ⟨Bs, base, opened⟩ := h.laid.opened
  obtain ⟨lot, inLot, lotPlace⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ opened s hsite
  have siteOfTheReturn : s ∈ lookSites A.Z := by
    rw [(atPure_at_laid h.laid hA).1]
    exact hsite
  exact ⟨lot,
    { inLot := inLot
      lotPlace := lotPlace
      half := lookupSideAtTheBaseProver hA s siteOfTheReturn
      fits := lookupSiteFits h s hsite
      ok := Johnson.AtFull.Shape.face_ok_site Zp s hsite
      shapeIs := lookupShapeIsTheLayersShape h s hsite
      usedIs := lookupUsedSlotsAreTheLedgersCount h s hsite }⟩

/-- **The same at the head's public part, the reader written out.** The sources are
`sourcesAt id (I.weights Zp) (reqAt Zp) Zp`; the reader is what the lookup's row at the site is
handed at the lot `theLotInst id (I.weights Zp)`. Conditional on the head, the return and the site.
-/
theorem lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A) (s : Site)
    (hsite : s ∈ lookSites Zp) :
    ∃ lot, SiteRest Zp cF A.H.first s lot
      (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights Zp) (reqAt Zp) Zp)).jobs s).asked)
      (askOf (Rc := IndexCommitterCoins) (sourcesAt id (I.weights Zp) (reqAt Zp) Zp) (whoOf s)) := by
  have rest := lookupSiteRestAtTheBaseProver h hA s hsite
  rw [(atPure_at_laid h.laid hA).1] at rest
  exact rest

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupSiteRestAtTheBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart
