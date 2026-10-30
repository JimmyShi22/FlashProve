-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKindPays.lean: the kind "lookup" (K3): conditional: the
book lends every seated row of a lookup its runs at the lookup's member of the first chain, so that
`chainSteps` (Honest/Frame.lean) returns there: the kind pays, in the sense of `KindPays`
(Honest/Law/ReadyOfSides.lean). General in the book, in the summands, in the reader of the input and
in the list of sides. Two definitions, six theorems; nothing is evaluated.

NO FILLING IS NAMED HERE: every statement is general in the filling, so it can be called at the honest
prover's own (`onlineFilling`, E2E/TheHonestProver.lean): E2E/Lookup/LookupKindPaysAtTheTermWhereTheBookFits.lean does.

Terms. Honest/K3/GLOSSARY.md ("site", "seat", "row", "book, coins", "half"). A side (also: half): a
place with a list of parts (`Placed`, Honest/Frame.lean). The head: `P5J.AtMgA`, the library's one
hypothesis at the full size.

What is defined.
  `BookFitsEveryLookup B Zp`            at every site of the public part Zp the two public tests on the
                                        book accept B: `bookFits` and `placeFits`
                                        (Honest/K3/Law/RowLends.lean), at the first chain's table
  `SidesOfKindLookupAreSeats Zp sides`  every side of the list whose place bears the kind K3 is the
                                        elder row `proverSideOfLookupInChainAtOneOwner` at a site of Zp, at some summands and
                                        some reader of the input

What is shown.
  `lookupSidePays`             the head, a site, the two tests at that site ⊢ at every summands J and
                               every reader wit the seated row at the site pays (`SidePays`), at the
                               head's own first chain
  `lookupKindPaysAtList`       the head, `BookFitsEveryLookup`, `SidesOfKindLookupAreSeats` ⊢
                               `KindPays` at the kind K3, at that book and that list of sides
  `lookupSidesAreSeatsOfLots`  where `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns A at a filling P each of
                               whose lots has, at A's public part, either no side at a place of the
                               kind K3 or seated rows at sites alone: A's first list of sides has
                               `SidesOfKindLookupAreSeats`
  `lookupKindPays`             **the join**: the head, a return A of `onlineProverFromPublicFiles` at any filling, the
                               two premises at A ⊢ `KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K3`
  `lookupKindPaysInTheSharedChain`, `lookupKindPaysInTheSecondChain`   where `onlineDescription` returns F:
                               `KindPays` at the kind K3 holds in F's two later chains at every book
                               and every list of sides: IDLY, BY NATURE: the kind has no member there

How. `sidePays_of_tests` (Honest/Law/ReadyOfSides.lean) asks six things at each member at the side's
place. As many lists of oracle messages as rounds, and as many rounds as the row has:
`member_plan_site` (Honest/K3/Law/Thread/SitePays.lean) at the lot's sub-protocol that `lot_of_site`
(Honest/K3/Law/LotOfSite.lean) finds, `lookSeat_rounds`, `fit_length` (Honest/K3/Law/MemberSite.lean)
and `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean). The book's cut, no row and no spender at
a part's number that the row does not have: `place_tests`. One return of the lending:
`rowLendsFirst` (both Honest/K3/Law/RowLends.lean). The two later chains:
Honest/K3/Term/NoLookupInTheLaterChains.lean.

Hypotheses that remain. The head. `BookFitsEveryLookup`: a test with code on public data;
AtFullSide/Honest/K3/Term/LookupLevelsUnderTheHead.lean pays it under the head alone, at any filling.
`SidesOfKindLookupAreSeats`: Honest/K3/Term/LookupSidesAtBaseProver.lean pays it at the wide filling,
Honest/K3/Term/LookupSidesReadThrough.lean at that filling read through. hA: that `onlineProverFromPublicFiles` returns.

Limits. Implications. "The kind pays" says that `chainSteps` returns at the lookups' members: nothing
on whether a part plays, a round is reached or a verifier accepts. At a list with no side of the
kind K3 `KindPays` holds idly: Honest/K3/Term/LookupSidesReadThrough.lean finds a site's seat at each
of fifty addresses that are apart. At the row `proverSideOfLookupInChainAtOneOwner` alone: a row that passes its tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) is another term. The full size and the format's second hash function alone: that limit
comes with the head. It stands over Honest/Law/ReadyOfSides.lean and Honest/Law/ReadyOfParts.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.RowLends
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays
import Johnson.AtFull.Shape.FaceAtSites
import Johnson.P5J.MgAtAll
import Johnson.IMR.PlanAt
import Johnson.Desc.ProofFile.Honest.K3.Term.NoLookupInTheLaterChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain KindName FileDescription)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K3.Law

/-! ## 1 The two premises, by name -/

/-- **The book fits every lookup**: at every site of the public part the two public tests on the
book accept, at the first chain's table and the book's own numbers of coins. -/
def BookFitsEveryLookup (B : ProverCoinCounts) (Zp : Pub) : Prop :=
  ∀ s ∈ lookSites Zp, bookFits B (B.rowsOf 0) (dueAt B.first) s.at_ = true ∧
    placeFits B (B.rowsOf 0) s.at_ = true

/-- **Every side of the kind "lookup" is a seat**: a side of the list whose place bears the kind K3
is the elder row at a site of the public part, at some summands and some reader of the input. -/
def SidesOfKindLookupAreSeats {V₁ W₁ X₁ : Type} (Zp : Pub) (sides : List (Placed V₁ W₁ X₁)) : Prop :=
  ∀ g ∈ sides, g.place.kind = KindName.K3 →
    ∃ s ∈ lookSites Zp, ∃ (Wj : Type) (J : LookJobs Wj) (wit : W₁ → Wj),
      g = proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_

/-! ## 2 One side; the kind -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A lookup's seated row pays**, at the head's own first chain. Conditional: the head; the site;
the two tests on the book at that site. General in the book, the summands and the reader. -/
theorem lookupSidePays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (B : ProverCoinCounts) {s : Site}
    (hs : s ∈ lookSites Zp)
    (hBook : bookFits B (B.rowsOf 0) (dueAt B.first) s.at_ = true)
    (hPlace : placeFits B (B.rowsOf 0) s.at_ = true)
    {V₁ W₁ X₁ Wj : Type} (J : LookJobs Wj) (wit : W₁ → Wj) :
    SidePays B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hlot, hlp⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨t1, t2, t3⟩ := place_tests (V₁ := V₁) (X₁ := X₁) J wit s.at_ B (B.rowsOf 0) hPlace
  obtain ⟨c, hc, -⟩ := rowLendsFirst V₁ W₁ X₁ Wj J wit s.at_ B hBook default
  refine sidePays_of_tests B 0 _ _ fun b hb hbp => ?_
  have hbp' : b.place = s.at_.place := hbp
  have hb' : b ∈ cF.blocksInOrder := hb
  obtain ⟨hr, ho, hfit⟩ := AtThr.member_plan_site _ _ _ _ _ Zp Bs base cF _ _ O s hs lot b hlot hlp
    hb' (hbp'.trans hlp.symm) (IM.plan_flat O h.laid.planOk b hb')
  refine ⟨by rw [hr, ho, List.length_map, List.length_map], ?_, ?_, ?_, ?_, default, c, ?_⟩
  · rw [lookSeat_rounds _ J wit s.at_
      (two_le_planes_of_ok _ (Johnson.AtFull.Shape.face_ok_site Zp s hs)), hr, List.length_map,
      fit_length _ _ hfit]
  · rw [hbp']
    simpa using t1
  · rw [hbp']
    exact t2
  · rw [hbp']
    exact t3
  · rw [hbp']
    exact hc

/-- **The kind "lookup" pays, at a list of sides.** Conditional: the head; the book fits every
lookup; every side of the kind in the list is a seat. -/
theorem lookupKindPaysAtList (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {B : ProverCoinCounts}
    (hBook : BookFitsEveryLookup B Zp) {V₁ W₁ X₁ : Type} {sides : List (Placed V₁ W₁ X₁)}
    (hSides : SidesOfKindLookupAreSeats Zp sides) :
    KindPays B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder sides KindName.K3 := by
  intro g hg hk
  obtain ⟨s, hs, Wj, J, wit, rfl⟩ := hSides g hg hk
  exact lookupSidePays h B hs (hBook s hs).1 (hBook s hs).2 J wit

end

/-! ## 3 At whatever `onlineProverFromPublicFiles` returns -/

section
variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **From the filling's lots to the returned prover's first list of sides.** Conditional: hA; each
lot of the filling has, at the returned public part and ground, no side at a place of the kind K3,
or seated rows at sites alone. -/
theorem lookupSidesAreSeatsOfLots (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hLots : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place.kind ≠ KindName.K3) ∨
      SidesOfKindLookupAreSeats A.Z (M.halves A.Z A.G)) :
    SidesOfKindLookupAreSeats A.Z A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  intro g hg hk
  rw [eH] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1 hg
  rcases hLots M hM with hn | hy
  · exact absurd hk (hn g hgM)
  · exact hy g hgM hk

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **THE KIND "LOOKUP" PAYS AT WHATEVER `onlineProverFromPublicFiles` RETURNS**, general in the filling. Conditional: the
head; hA; A's book fits every lookup; every side of the kind in A's first list is a seat. -/
theorem lookupKindPays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hBook : BookFitsEveryLookup A.B A.Z) (hSides : SidesOfKindLookupAreSeats A.Z A.H.first) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K3 := by
  obtain ⟨eZ, eF⟩ := atPure_at_laid h.laid hA
  rw [eF]
  rw [eZ] at hBook hSides
  exact lookupKindPaysAtList h hBook hSides

end

/-! ## 4 The two later chains -/

section
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **In the shared chain the kind "lookup" pays idly**: it has no member there. At every book and
every list of sides. Conditional: `onlineDescription` returns F. -/
theorem lookupKindPaysInTheSharedChain (hF : onlineDescription o pol lay KL = .ok F) (B : ProverCoinCounts)
    {V W Y : Type} (sides : List (Placed V W Y)) :
    KindPays B 1 F.shared.blocksInOrder sides KindName.K3 :=
  fun _ _ hk b hb hbp => absurd (hbp ▸ hk) (noLookupInTheSharedChain hF b hb)

/-- **In the second chain too.** Conditional: `onlineDescription` returns F. -/
theorem lookupKindPaysInTheSecondChain (hF : onlineDescription o pol lay KL = .ok F) (B : ProverCoinCounts)
    {V W Y : Type} (sides : List (Placed V W Y)) :
    KindPays B 2 F.second.blocksInOrder sides KindName.K3 :=
  fun _ _ hk b hb hbp => absurd (hbp ▸ hk) (noLookupInTheSecondChain hF b hb)

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.BookFitsEveryLookup
#print axioms ProofFile.Honest.K3.Term.SidesOfKindLookupAreSeats
#print axioms ProofFile.Honest.K3.Term.lookupSidePays
#print axioms ProofFile.Honest.K3.Term.lookupKindPaysAtList
#print axioms ProofFile.Honest.K3.Term.lookupSidesAreSeatsOfLots
#print axioms ProofFile.Honest.K3.Term.lookupKindPays
#print axioms ProofFile.Honest.K3.Term.lookupKindPaysInTheSharedChain
#print axioms ProofFile.Honest.K3.Term.lookupKindPaysInTheSecondChain
