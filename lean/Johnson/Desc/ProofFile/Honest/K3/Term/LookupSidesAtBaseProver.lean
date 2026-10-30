-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSidesAtBaseProver.lean: the kind "lookup" (K3): the lookups'
own list of sides pays; and at the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns at the filling
`onlineProverPartsInUse I o S O` (Honest/K1/Law/WSideAtFill.lean), at any index type and any reader I of it:
every side of the first chain whose place bears the kind K3 is a lookup's seated row, so the kind pays
where the book fits; and, under the head, the search at each of the fifty addresses finds a site's seat,
at the place of a member of the first chain. No definition, seven theorems; nothing is evaluated.

NOT THE HONEST PROVER's FILLING, from the third section on: T1's `onlineFilling` (E2E/TheHonestProver.lean) is
the filling named here READ THROUGH `tableCoins`; its return has another type, so the statements at a return
of `onlineProverFromPublicFiles` at `onlineProverPartsInUse I o S O` itself cannot be called there. The like statements at that filling
read through: Honest/K3/Term/LookupSidesReadThrough.lean; at `onlineMaker`:
E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean. `lookupLotSidesAreSeats`, `lookupLotPays`,
`lookupSidesAtAnyFillingAreSeats` and `lookupAddressesAreApart` name no filling.

Terms. Honest/K3/GLOSSARY.md ("site", "seat", "row", "half"). The head: `P5J.AtMgA`, the library's one
hypothesis at the full size. The forms `BookFitsEveryLookup` and `SidesOfKindLookupAreSeats`:
Honest/K3/Term/LookupKindPays.lean. `SidePays`, `KindPays`: Honest/Law/ReadyOfSides.lean.

What is shown.
  `lookupLotSidesAreSeats`            no premise: every side of `theLotInst cells weights` at a public
                                      part is a seated row at a site of it
  `lookupLotPays`                     the head, `BookFitsEveryLookup B Zp` ⊢ every side of
                                      `theLotInst cells weights` at Zp pays, at the book B and the head's
                                      first chain: at every type of index, randomness, trace and own
                                      state, whether or not a filling lays that list
  `lookupSidesAtAnyFillingAreSeats`   hA at a filling P one of whose lots has the halves of
                                      `theLotInst cells weights` and whose other lots have no side at a
                                      place of the kind K3 ⊢ `SidesOfKindLookupAreSeats A.Z A.H.first`
  `lookupSidesAtBaseProverAreSeats`   hA at the named filling ⊢ the same
  `lookupKindPaysAtBaseProver`        the head, hA, `BookFitsEveryLookup A.B A.Z` ⊢
                                      `KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K3`
  `lookupSideStandsAtEveryAddress`    THE LAW ABOVE IS NOT IDLE: the head, hA ⊢ at each link below 25
                                      and both sorts there is a site at the library's address
                                      `IM.k3Place`, of the kind K3; the search there in A.H.first
                                      finds the site's seat, by name; and a member of the head's
                                      first chain stands at that place
  `lookupAddressesAreApart`           the head ⊢ the fifty addresses are pairwise different

How. Which sides stand in A.H.first at a place of the kind K3, and what the search finds there:
`lookupSidesAtAnyFillingAreTheLots`, `lookupSidesAtTheBaseProverAreTheLots`, `lookupSideAtTheBaseProver`
(Honest/K3/Term/LookupSideAtAnyFilling.lean). The fifty: `site_at_all_fifty`
(Honest/K3/Law/Thread/SiteAllFifty.lean), `P5J.At.places_paid`. Two sites at one place are one:
`site_of_place` (Honest/K3/Law/Thread/SitesOnce.lean).

Hypotheses that remain. hA: that `onlineProverFromPublicFiles` returns. The head, where it is named. `BookFitsEveryLookup`, in
the second and the fifth: AtFullSide/Honest/K3/Term/LookupLevelsUnderTheHead.lean pays it under the head.

Limits. Nothing is said of a filling that is read through a map of the input (`OnlineProverParts.through`). The row
`proverSideOfLookupInChainAtOneOwner` alone. Which side stands at a place: nothing on whether it plays, is accepted, or what it
sends. Where no head is asked, o and the maker's hash are two letters.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. This file does not show that the maker
returns at it. It stands over Honest/K1/Law/WSideAtFill.lean and what it imports, and over
Honest/Law/ReadyOfSides.lean and Honest/Law/ReadyOfParts.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindPays
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSideAtAnyFilling
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAllFifty
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitesOnce
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K3.Law

/-! ## 1 The lookups' own list -/

/-- **Every side of the lookups' list is a site's seat.** No premise. -/
theorem lookupLotSidesAreSeats {W₀ Rc Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (Zq : Pub) (G : Ground) :
    SidesOfKindLookupAreSeats Zq ((theLotInst (Rc := Rc) (X := X) cells weights).halves Zq G) := by
  intro g hg _
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  exact ⟨s, hs, _, _, _, rfl⟩

/-- **The lookups' list pays**, side by side, at the head's own first chain. Conditional: the head; the
book fits every lookup. -/
theorem lookupLotPays {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {B : ProverCoinCounts} (hBook : BookFitsEveryLookup B Zp)
    {W₀ Rc Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights) (G : Ground) :
    ∀ g ∈ (theLotInst (Rc := Rc) (X := X) cells weights).halves Zp G,
      SidePays B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder g := by
  intro g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  exact lookupSidePays h B hs (hBook s hs).1 (hBook s hs).2 _ _

/-! ## 2 At any filling -/

/-- **The premise on the sides, at any filling that lays the lookups' list and no other side of the
kind.** Conditional: hA; hHalves; hOthers. -/
theorem lookupSidesAtAnyFillingAreSeats {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (cells : Tr → Cells) (weights : W₀ → Weights)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X}
    (hHalves : L.halves A.Z A.G = (theLotInst (Rc := Rc) (X := X) cells weights).halves A.Z A.G)
    (hOthers : ∀ M ∈ P.lots,
      (∀ g ∈ M.halves A.Z A.G, g.place.kind ≠ KindName.K3) ∨ M.halves A.Z A.G = L.halves A.Z A.G) :
    SidesOfKindLookupAreSeats A.Z A.H.first := fun g hg hk =>
  lookupLotSidesAreSeats cells weights A.Z A.G g
    (lookupSidesAtAnyFillingAreTheLots hA cells weights hHalves hOthers g hg hk) hk

/-! ## 3 At the wide filling itself -/

section
variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The premise on the sides is met at the base prover.** Conditional: hA. -/
theorem lookupSidesAtBaseProverAreSeats
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    SidesOfKindLookupAreSeats A.Z A.H.first := fun g hg hk =>
  lookupLotSidesAreSeats id (I.weights A.Z) A.Z A.G g
    (lookupSidesAtTheBaseProverAreTheLots hA g hg hk) hk

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE KIND "LOOKUP" PAYS AT THE BASE PROVER.** Conditional: the head; hA; A's book fits every
lookup. -/
theorem lookupKindPaysAtBaseProver (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
    (hBook : BookFitsEveryLookup A.B A.Z) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K3 :=
  lookupKindPays h hA hBook (lookupSidesAtBaseProverAreSeats hA)

/-- **THE LAW ABOVE IS NOT IDLE: the search at each of the fifty addresses finds a site's seat, by
name**, at the place of a member of the head's first chain. Conditional: the head; hA. -/
theorem lookupSideStandsAtEveryAddress (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
    (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place.kind = KindName.K3 ∧
      A.H.first.find? (fun g => g.place == s.at_.place) =
        some (AtThr.seatAt id (I.weights Zp) (reqAt Zp) Zp s) ∧
      ∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, b.place = s.at_.place := by
  obtain ⟨eZ, -⟩ := atPure_at_laid h.laid hA
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := AtThr.site_at_all_fifty h l hl d
  rw [← P5J.At.places_paid h.scope h.reads h.laid] at e4
  obtain ⟨b, hb, hbp⟩ := List.mem_map.1 e4
  have hf := lookupSideAtTheBaseProver hA s (by rw [eZ]; exact hs)
  rw [eZ] at hf
  exact ⟨s, hs, e1, e2, e3, (spot_of_site Zp s hs).1, hf, b, hb, hbp⟩

/-- **The fifty addresses are apart.** Conditional: the head. -/
theorem lookupAddressesAreApart (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l l' : Nat}
    (hl : l < 25) (hl' : l' < 25) {d d' : Bool} (e : IM.k3Place l d = IM.k3Place l' d') :
    l = l' ∧ d = d' := by
  obtain ⟨s, hs, e1, e2, e3, -⟩ := AtThr.site_at_all_fifty h l hl d
  obtain ⟨t, ht, f1, f2, f3, -⟩ := AtThr.site_at_all_fifty h l' hl' d'
  obtain rfl := AtThr.site_of_place Zp s t hs ht (e3.trans (e.trans f3.symm))
  exact ⟨e1.symm.trans f1, e2.symm.trans f2⟩

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupLotSidesAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupLotPays
#print axioms ProofFile.Honest.K3.Term.lookupSidesAtAnyFillingAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupSidesAtBaseProverAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupKindPaysAtBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupSideStandsAtEveryAddress
#print axioms ProofFile.Honest.K3.Term.lookupAddressesAreApart
