-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's `onlineFilling`
(E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through `tableCoins`; its
return has another type; the crossing of the threads to it is not this folder's; the equation on the
lookups' lot is (Honest/K3/Term/LookupLotReadThrough.lean).
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupPlaysAndIsAcceptedAtAllFifty.lean: the honest side of
the kind "lookup" (K3): `PlaysS` and `AcceptedS` (Honest/Thread/PaysS.lean) at all fifty borders of
the lookups in the proof file's first chain, at the thread of `lettersHead h A.H ...`, where A is
any return of `onlineProverFromPublicFiles` at the base filling: with no hypothesis left but the head and that return.

Terms. Honest/K3/GLOSSARY.md: filling, half (side), seat, site, border, member.

What is shown.
  `lookupPublicTestsUnderTheHead`: the three tests of `LookupPublicTests` accept at every site.
  `lookupMemberStandsAtEveryBorder`: at each of the fifty numbers `borderOf l d`, l below 25, the
    first chain has a member, at the place of the kind K3 with that link and piece: so the
    statements below speak of a member.
  `lookupPlaysAtAnyThreadAtAllFifty`: `PlaysS T Said (borderOf l d)` at every thread T that is the
    maker's, every Said, every l below 25 and both d.
  `lookupPlaysAtAllFifty`, `lookupJoinsAtEverySite`, `lookupIsAcceptedAtAllFifty`: `PlaysS`, the
    join and
    `AcceptedS` at the thread of `lettersHead h A.H ...`, at every value of its other arguments,
    every Said and every fall.

Hypotheses that remain. `h`: the head `P5J.AtMgA`. `hA`: `onlineProverFromPublicFiles` returns A at
`onlineProverPartsInUse I o S O`, at a variable index type and variables I, o, S, O.

By what. The side: `lookupSideAtTheBaseProver`. The rounds in front: `lookupBaseIsTheChainsCount`,
which rests on the closed fact `lookupBaseWritten`, evaluated by Lean's kernel. The shape and the
slots in use: `lookupShapeIsTheLayersShape`, `lookupUsedSlotsAreTheLedgersCount`. The head's step:
`lookupHeadReturnsAtLettersHead`. A site at every link and sort: `site_digits_paid`.

Limits. All statements are implications. `PlaysS` and `AcceptedS` are forms of hypothesis of the
frame's: each speaks from a stand of `ThrS`; that a run reaches such a stand is not shown here. The
acceptance says nothing on values. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSeatAtTheMaker
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBaseWritten
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupShapeAndUsedSlots
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHeadStepReturns
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf pieceOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The three tests on public data accept at every site.** Conditional on the head and the site.
-/
theorem lookupPublicTestsUnderTheHead (s : Site) (hsite : s ∈ lookSites Zp) :
    LookupPublicTests Zp cF s :=
  ⟨lookupBaseIsTheChainsCount h s hsite,
    lookupShapeIsTheLayersShape h s hsite, lookupUsedSlotsAreTheLedgersCount h s hsite⟩

include h in
/-- **At each of the fifty numbers the first chain has a member, at the lookup's place.**
Conditional on the head. -/
theorem lookupMemberStandsAtEveryBorder (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ blk, cF.blocksInOrder[borderOf l d]? = some blk ∧
      blk.place = ⟨1, some l, pieceOf l d, KindName.K3⟩ := by
  have hP : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have e : (blockPlaces cF.blocksInOrder)[borderOf l d]? = some ⟨1, some l, pieceOf l d, KindName.K3⟩ := by
    rw [hP]
    exact places_are_k3 hl d
  unfold blockPlaces at e
  rw [List.getElem?_map] at e
  obtain ⟨blk, hk, hp⟩ := Option.map_eq_some_iff.1 e
  exact ⟨blk, hk, hp⟩

variable {Bk : ProverCoinCounts} {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
  {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)

include h hA in
/-- **`PlaysS` at all fifty borders, at any thread that is the maker's, at every Said.** Conditional
on the head, the maker's return and the six equations. -/
theorem lookupPlaysAtAnyThreadAtAllFifty
    {T : Thread Bk TS ProofFile.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst} (hT : ThreadIsTheMakers T cF A.H)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) (l : Nat)
    (hl : l < 25) (d : Bool) : PlaysS T Said (borderOf l d) := by
  obtain ⟨s, hsite, rfl, rfl, -, -⟩ := site_digits_paid h l hl d
  exact lookupPlaysAtTheBaseProver h hA hT s hsite
    (lookupPublicTestsUnderTheHead h s hsite).baseIsTheChainsCount Said

variable
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

local notation "LA" => lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

include hA in
/-- **`PlaysS` at all fifty borders, at the thread of `lettersHead` at the base prover.**
Conditional on the head and the maker's return. -/
theorem lookupPlaysAtAllFifty (l : Nat) (hl : l < 25) (d : Bool) :
    PlaysS (LA).thread Said (borderOf l d) :=
  lookupPlaysAtAnyThreadAtAllFifty h hA
    (threadIsTheMakersAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said l hl d

include hA in
/-- **The join at every site, there.** Conditional on the head, the maker's return and the site. -/
theorem lookupJoinsAtEverySite (s : Site) (hsite : s ∈ lookSites Zp) :
    LookupJoinsFromThePair (LA).thread Said (borderOf s.link s.digits) s.at_
      (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).jobs s).asked)
      ((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).wit s) s.p.first
      (K3.Law.seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Zp.p.X s.link s.digits s.shape) :=
  lookupJoinsAtTheBaseProversLetters h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said s hsite
    (lookupPublicTestsUnderTheHead h s hsite)
    (lookupHeadReturnsAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said s hsite)

include hA in
/-- **`AcceptedS` at all fifty borders, there, at every letter fall.** Conditional on the head and
the maker's return. -/
theorem lookupIsAcceptedAtAllFifty (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat)
    (hl : l < 25) (d : Bool) : AcceptedS (LA).thread Said fall (borderOf l d) := by
  obtain ⟨s, hsite, rfl, rfl, -, -⟩ := site_digits_paid h l hl d
  exact lookupIsAcceptedAtTheBaseProversLetters h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said s
    hsite (lookupPublicTestsUnderTheHead h s hsite)
    (lookupHeadReturnsAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said s hsite) fall

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupPublicTestsUnderTheHead
#print axioms ProofFile.Honest.K3.Term.lookupMemberStandsAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtAnyThreadAtAllFifty
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtAllFifty
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtEverySite
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtAllFifty
