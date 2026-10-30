-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSidesReadThrough.lean: the kind "lookup" (K3): at the prover
that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns at the wide filling `onlineProverPartsInUse I o S O`
(Honest/K1/Law/WSideAtFill.lean) READ THROUGH a map g of the index and a map rd of the randomness
(`OnlineProverParts.through`, Honest/ThruK13.lean): the sides of the first chain whose place bears the kind K3 are
just the lookups' seated rows at the sites of the returned public part, at the lookups' filling read
through; so the kind pays where the book fits; and, under the head, the search at each of the fifty
addresses finds a site's seat, by name. General in g, rd, the named member, I, o, S and O. No definition,
eight theorems; nothing is evaluated.

THE HONEST PROVER's FILLING IS OF THIS FORM: T1's `onlineFilling files` (E2E/TheHonestProver.lean) is
`OnlineProverParts.through id (tableCoins files) matrixInput.dummy (onlineProverPartsInUse matrixInput secondHashFunction Sz.ref
openHonest)`. E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean calls these statements there.

Terms. Honest/K3/GLOSSARY.md ("site", "seat", "row", "half"). The head: `P5J.AtMgA`, the library's one
hypothesis at the full size. `lookupFillingThrough weights g rd` (Honest/K3/Term/LookupLotReadThrough.lean):
the summands of `fastFill` at the public part's sources, its reader composed with `Local.thru g rd`.
The forms `BookFitsEveryLookup`, `SidesOfKindLookupAreSeats`: Honest/K3/Term/LookupKindPays.lean.

What is shown.
  `lookupSidesReadThroughAreSeats`   a list of sides whose sides of the kind K3 are seats stays so when
                                     each side is read through
  `lookupLotsOfTheWideFillingAreSeatsOrOfOtherKinds`   no premise: each lot of the wide filling has, at
                                     every public part and ground, no side at a place of the kind K3, or
                                     seats at sites alone
  `lookupSidesOfFillingReadThroughAreSeats`   hA at `OnlineProverParts.through g rd d' P`, the sentence above of P's
                                     lots ⊢ `SidesOfKindLookupAreSeats A.Z A.H.first`. General in P
  `lookupSidesOfWideFillingReadThroughAreSeats`   hA ⊢ the same, at the wide filling read through
  `lookupSidesOfWideFillingReadThroughAreTheLots`  hA ⊢ BY NAME: every side of A.H.first at a place of the
                                     kind K3 is a half of `rowLotAt (lookupFillingThrough I.weights g rd)`
  `lookupSeatIsFoundReadThrough`     hA, a site s of A.Z ⊢ the search at the site's place in A.H.first
                                     finds `proverSideOfLookupInChainAtOneOwner` at that filling's summands and reader at s
  `lookupKindPaysReadThrough`        the head, hA, `BookFitsEveryLookup A.B A.Z` ⊢
                                     `KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K3`
  `lookupSideStandsAtEveryAddressReadThrough`   THE LAW ABOVE IS NOT IDLE: the head, hA ⊢ at each link
                                     below 25 and both sorts there is a site at the library's address
                                     `IM.k3Place`, of the kind K3; the search there in A.H.first finds the
                                     site's seat, by name; a member of the head's first chain stands there
That the fifty addresses are apart: `lookupAddressesAreApart` (Honest/K3/Term/LookupSidesAtBaseProver.lean).

How. That the lots of a filling read through are its lots, each read through, is `OnlineProverParts.through`'s own
text (by `rfl`): no law of `OnlineProverParts.through` is stated here. A seat read through is a seat:
`lookupSeatReadThrough`; the lookups' lot read through is `rowLotAt` at the filling read through:
`lookupLotByPublicPartReadThrough`, `lookupLotIsAmongTheLotsReadThrough`
(Honest/K3/Term/LookupLotReadThrough.lean). No other lot has a side of the kind:
`noOtherLotOfTheBaseFillingHasALookupsPlace` (Honest/K3/Term/LookupSideAtAnyFilling.lean). Reading through
keeps a side's place.

Hypotheses that remain. hA: that `onlineProverFromPublicFiles` returns. The head, in the last two. `BookFitsEveryLookup`, in
the seventh: AtFullSide/Honest/K3/Term/LookupLevelsUnderTheHead.lean pays it under the head.

Limits. Which side stands at a place: nothing on whether it plays, is accepted, or what it sends. The
row `proverSideOfLookupInChainAtOneOwner` alone.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
This file does not show that the maker returns at it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSidesAtBaseProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupLotReadThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K3.Law

/-! ## 1 General in the filling -/

/-- **Seats read through are seats.** -/
theorem lookupSidesReadThroughAreSeats {V V' W W' X : Type} (see : V' → V) (reader : W' → W)
    {Zq : Pub} {sides : List (Placed V W X)} (hSides : SidesOfKindLookupAreSeats Zq sides) :
    SidesOfKindLookupAreSeats Zq (sides.map (Placed.thru see reader)) := by
  intro g hg hk
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  obtain ⟨s, hs, Wj, J, wit, rfl⟩ := hSides g₀ hg₀ hk
  exact ⟨s, hs, Wj, J, wit ∘ reader, lookupSeatReadThrough _ J wit s.at_ see reader⟩

/-- **From the lots of a filling to the prover that `onlineProverFromPublicFiles` returns at that filling read through.**
Conditional: hA; each lot of P has, at the returned public part and ground, no side at a place of the
kind K3, or seats at sites alone. -/
theorem lookupSidesOfFillingReadThroughAreSeats {W₀ W₀' Rc Rc' Tr X₀ X : Type} {o : SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} (g : W₀' → W₀) (rd : Rc' → Rc)
    (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (hLots : ∀ M ∈ P.lots, (∀ q ∈ M.halves A.Z A.G, q.place.kind ≠ KindName.K3) ∨
      SidesOfKindLookupAreSeats A.Z (M.halves A.Z A.G)) :
    SidesOfKindLookupAreSeats A.Z A.H.first := by
  refine lookupSidesAreSeatsOfLots hA fun M' hM' => ?_
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1
    (show M' ∈ P.lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd)) from hM')
  rcases hLots M hM with hn | hy
  · refine .inl fun q hq => ?_
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1
      (show q ∈ (M.halves A.Z A.G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) from hq)
    exact hn q₀ hq₀
  · exact .inr (lookupSidesReadThroughAreSeats _ _ hy)

/-! ## 2 At the wide filling -/

section
variable {W₀ W₀' Rc' : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments)

/-- **Each lot of the wide filling has no side of the kind "lookup", or seats alone.** No premise. -/
theorem lookupLotsOfTheWideFillingAreSeatsOrOfOtherKinds (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, (∀ q ∈ M.halves Zq G, q.place.kind ≠ KindName.K3) ∨
      SidesOfKindLookupAreSeats Zq (M.halves Zq G) := by
  intro M hM
  rcases noOtherLotOfTheBaseFillingHasALookupsPlace I o S O Zq G M hM with hn | he
  · exact .inl hn
  · refine .inr ?_
    have e : M.halves Zq G =
        (theLotInst (Rc := IndexCommitterCoins) (X := Unit) id (I.weights Zq)).halves Zq G := he.trans rfl
    rw [e]
    exact lookupLotSidesAreSeats id (I.weights Zq) Zq G

variable {I o S O} {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {g : W₀' → W₀} {rd : Rc' → IndexCommitterCoins}
  {d' : W₀'} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}

/-- **The premise on the sides is met at the wide filling read through.** Conditional: hA. -/
theorem lookupSidesOfWideFillingReadThroughAreSeats
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) :
    SidesOfKindLookupAreSeats A.Z A.H.first :=
  lookupSidesOfFillingReadThroughAreSeats g rd d' hA
    (lookupLotsOfTheWideFillingAreSeatsOrOfOtherKinds I o S O A.Z A.G)

/-- **By name: the sides of the kind "lookup" there are halves of the lookups' lot at the filling read
through.** Conditional: hA. -/
theorem lookupSidesOfWideFillingReadThroughAreTheLots
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) :
    ∀ q ∈ A.H.first, q.place.kind = KindName.K3 →
      q ∈ (rowLotAt (lookupFillingThrough I.weights g rd) :
        HLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit).halves A.Z A.G := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  intro q hq hk
  rw [eH] at hq
  obtain ⟨M', hM', hqM⟩ := List.mem_flatMap.1 hq
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1
    (show M' ∈ (onlineProverPartsInUse I o S O).lots.map
      (HLot.thru (Local.thru g rd) (Local.thru g rd)) from hM')
  obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1
    (show q ∈ (M.halves A.Z A.G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) from hqM)
  rcases noOtherLotOfTheBaseFillingHasALookupsPlace I o S O A.Z A.G M hM with hn | he
  · exact absurd hk (hn q₀ hq₀)
  · rw [he] at hq₀
    rw [← lookupLotByPublicPartReadThrough]
    exact List.mem_map_of_mem hq₀

/-- **The search at a site's place finds the site's seat, by name.** Conditional: hA; the site. -/
theorem lookupSeatIsFoundReadThrough
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) (s : Site)
    (hs : s ∈ lookSites A.Z) :
    A.H.first.find? (fun q => q.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((lookupFillingThrough I.weights g rd A.Z).jobs s).asked
        ((lookupFillingThrough I.weights g rd A.Z).wit s) s.at_) := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  cases hf : A.H.first.find? (fun q => q.place == s.at_.place) with
  | none =>
    have hm : (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((lookupFillingThrough I.weights g rd A.Z).jobs s).asked
        ((lookupFillingThrough I.weights g rd A.Z).wit s) s.at_ :
        Placed (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit) ∈ A.H.first := by
      rw [eH]
      exact List.mem_flatMap.2 ⟨_, lookupLotIsAmongTheLotsReadThrough I o S O g rd d',
        List.mem_map.2 ⟨s, hs, rfl⟩⟩
    exact absurd (beq_self_eq_true s.at_.place) (List.find?_eq_none.1 hf _ hm)
  | some q =>
    have hp : q.place = s.at_.place := by simpa using List.find?_some hf
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (lookupSidesOfWideFillingReadThroughAreTheLots hA q
      (List.mem_of_find?_eq_some hf) (by rw [hp]; exact (spot_of_site A.Z s hs).1))
    rw [AtThr.site_of_place A.Z t s ht hs hp]
    rfl

end

/-! ## 3 Under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ W₀' Rc' : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {g : W₀' → W₀} {rd : Rc' → IndexCommitterCoins} {d' : W₀'} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}

/-- **THE KIND "LOOKUP" PAYS AT THE WIDE FILLING READ THROUGH.** Conditional: the head; hA; A's book fits
every lookup. -/
theorem lookupKindPaysReadThrough (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    (hBook : BookFitsEveryLookup A.B A.Z) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K3 :=
  lookupKindPays h hA hBook (lookupSidesOfWideFillingReadThroughAreSeats hA)

/-- **THE LAW ABOVE IS NOT IDLE: the search at each of the fifty addresses finds a site's seat, by
name**, at the place of a member of the head's first chain. Conditional: the head; hA. -/
theorem lookupSideStandsAtEveryAddressReadThrough (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place.kind = KindName.K3 ∧
      A.H.first.find? (fun q => q.place == s.at_.place) =
        some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((lookupFillingThrough I.weights g rd Zp).jobs s).asked
          ((lookupFillingThrough I.weights g rd Zp).wit s) s.at_) ∧
      ∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, b.place = s.at_.place := by
  obtain ⟨eZ, -⟩ := atPure_at_laid h.laid hA
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := AtThr.site_at_all_fifty h l hl d
  rw [← P5J.At.places_paid h.scope h.reads h.laid] at e4
  obtain ⟨b, hb, hbp⟩ := List.mem_map.1 e4
  have hf := lookupSeatIsFoundReadThrough hA s (by rw [eZ]; exact hs)
  rw [eZ] at hf
  exact ⟨s, hs, e1, e2, e3, (spot_of_site Zp s hs).1, hf, b, hb, hbp⟩

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupSidesReadThroughAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupSidesOfFillingReadThroughAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupLotsOfTheWideFillingAreSeatsOrOfOtherKinds
#print axioms ProofFile.Honest.K3.Term.lookupSidesOfWideFillingReadThroughAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupSidesOfWideFillingReadThroughAreTheLots
#print axioms ProofFile.Honest.K3.Term.lookupSeatIsFoundReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupKindPaysReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupSideStandsAtEveryAddressReadThrough
