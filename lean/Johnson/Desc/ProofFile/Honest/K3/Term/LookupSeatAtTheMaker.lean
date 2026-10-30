-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's `onlineFilling`
(E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through `tableCoins`; its
return has another type; the crossing of the threads to it is not this folder's; the equation on the
lookups' lot is (Honest/K3/Term/LookupLotReadThrough.lean).
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupSeatAtTheMaker.lean: the honest side of the kind
"lookup" (K3): `PlaysS`, the join and `AcceptedS` (Honest/K3/Term/LookupPlaysAndIsAccepted.lean) at
the prover that `onlineProverFromPublicFiles` returns at the base filling `onlineProverPartsInUse I o S O`, with the side at a
lookup's place paid by `lookupSideAtTheBaseProver` (Honest/K3/Term/LookupSideAtAnyFilling.lean).

Terms. Honest/K3/GLOSSARY.md: filling, half (side), seat, site, border.

What is shown.
  `lookupPlaysAtTheBaseProver`, `lookupJoinsAtTheBaseProver`, `lookupIsAcceptedAtTheBaseProver`:
    under the head, at any thread that is the maker's: the three, with the side paid.
  `lookupPlaysAtTheBaseProversLetters`, `lookupJoinsAtTheBaseProversLetters`,
  `lookupIsAcceptedAtTheBaseProversLetters`: the same at the thread of `lettersHead h A.H ...`, at
    every value of its other arguments, with the six equations and the promise in front paid too.
  `lookupIsAcceptedAtFortyNineBorders`: there, on the calls and off link 24, without
    `LookupHeadReturns`.

Hypotheses that remain.
  `h`: the head `P5J.AtMgA`. `hA`: `onlineProverFromPublicFiles` returns A at the filling. `hsite`: s is a site of the
    public part.
  `baseIsTheChainsCount` (for all three), `shapeIsTheLayouts`, `usedIsThePlans` (for the join and
    the acceptance): tests with code on public data (`LookupPublicTests`).
  `LookupHeadReturns`: at the digits of link 24 alone.

Limits. All statements are implications. That `onlineProverFromPublicFiles` returns at the filling, and that the three
tests accept, is not shown here. The filling read through another reader (`OnlineProverParts.through`) is not
named here. The acceptance says nothing on values.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPlaysAndIsAccepted
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSideAtAnyFilling
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

/-! ## The three at the base prover, under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ : Type} {I : WiderIn W₀}
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)

include h hA in
/-- A site of the head's public part is a site of the maker's. -/
theorem siteOfTheMakersPublicPart {s : Site} (hsite : s ∈ lookSites Zp) : s ∈ lookSites A.Z := by
  rw [(atPure_at_laid h.laid hA).1]
  exact hsite

section
variable {T : Thread Bk TS ProofFile.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    Unit ProofFile.Inst}

include h hA in
/-- **`PlaysS` at the base prover, at every one of the lookups' borders and every Said.**
Conditional on the head, the maker's return, the six equations, the site and the first test. -/
theorem lookupPlaysAtTheBaseProver (hT : ThreadIsTheMakers T cF A.H) (s : Site)
    (hsite : s ∈ lookSites Zp) (hBase : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    PlaysS T Said (borderOf s.link s.digits) :=
  lookupPlaysAtEveryBorder h hT s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hBase Said

variable {Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}

include h hA in
/-- **The join at the base prover.** Conditional on the head, the maker's return, the six equations,
the site, the three tests and the two hypotheses on the thread. -/
theorem lookupJoinsAtTheBaseProver (hT : ThreadIsTheMakers T cF A.H) (s : Site)
    (hsite : s ∈ lookSites Zp) (hTests : LookupPublicTests Zp cF s)
    (hFront : LookupPromiseInFront T Said (borderOf s.link s.digits) s)
    (hHead : LookupHeadReturns T Said (borderOf s.link s.digits) Zp s) :
    LookupJoinsFromThePair T Said (borderOf s.link s.digits) s.at_
      (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).jobs s).asked)
      ((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).wit s) s.p.first
      (K3.Law.seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Zp.p.X s.link s.digits s.shape) :=
  lookupJoinsAtEveryBorder h hT s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hTests hFront hHead

include h hA in
/-- **`AcceptedS` at the base prover, at every letter fall.** Conditional on the same. -/
theorem lookupIsAcceptedAtTheBaseProver (hT : ThreadIsTheMakers T cF A.H) (s : Site)
    (hsite : s ∈ lookSites Zp) (hTests : LookupPublicTests Zp cF s)
    (hFront : LookupPromiseInFront T Said (borderOf s.link s.digits) s)
    (hHead : LookupHeadReturns T Said (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS T Said fall (borderOf s.link s.digits) :=
  lookupIsAcceptedAtEveryBorder h hT s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hTests hFront hHead fall

end

variable
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

local notation "LA" => lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

include hA in
/-- **`PlaysS` at the thread of `lettersHead` at the base prover**, at every value of the other
letters and every Said. Conditional on the head, the maker's return, the site and the first test. -/
theorem lookupPlaysAtTheBaseProversLetters (s : Site) (hsite : s ∈ lookSites Zp)
    (hBase : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base) :
    PlaysS (LA).thread Said (borderOf s.link s.digits) :=
  lookupPlaysAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hBase Said

include hA in
/-- **The join there.** Conditional on the head, the maker's return, the site, the three tests and
`LookupHeadReturns`. -/
theorem lookupJoinsAtTheBaseProversLetters (s : Site) (hsite : s ∈ lookSites Zp)
    (hTests : LookupPublicTests Zp cF s)
    (hHead : LookupHeadReturns (LA).thread Said (borderOf s.link s.digits) Zp s) :
    LookupJoinsFromThePair (LA).thread Said (borderOf s.link s.digits) s.at_
      (((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).jobs s).asked)
      ((fastFill (Rc := IndexCommitterCoins) (sourcesAt id (I.weights A.Z) (reqAt A.Z) A.Z)).wit s) s.p.first
      (K3.Law.seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Zp.p.X s.link s.digits s.shape) :=
  lookupJoinsAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hTests Said hHead

include hA in
/-- **`AcceptedS` there, at every letter fall.** Conditional on the same. -/
theorem lookupIsAcceptedAtTheBaseProversLetters (s : Site) (hsite : s ∈ lookSites Zp)
    (hTests : LookupPublicTests Zp cF s)
    (hHead : LookupHeadReturns (LA).thread Said (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (LA).thread Said fall (borderOf s.link s.digits) :=
  lookupIsAcceptedAtLettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s hsite _ _
    (lookupSideAtTheBaseProver hA s (siteOfTheMakersPublicPart h hA hsite)) hTests Said hHead fall

include hA in
/-- **`AcceptedS` there at forty-nine of the fifty borders**: on the calls and off link 24, where
`LookupHeadReturns` asks nothing. Conditional on `h`, the maker's return, the site and the three
tests. -/
theorem lookupIsAcceptedAtFortyNineBorders (s : Site) (hsite : s ∈ lookSites Zp)
    (hn : s.digits = false ∨ s.link ≠ 24) (hTests : LookupPublicTests Zp cF s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (LA).thread Said fall (borderOf s.link s.digits) :=
  lookupIsAcceptedAtTheBaseProversLetters h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said s hsite
    hTests (lookupHeadReturnsButAtOne h _ s hsite hn) fall

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.siteOfTheMakersPublicPart
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtTheBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtTheBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtTheBaseProver
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtTheBaseProversLetters
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtTheBaseProversLetters
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtTheBaseProversLetters
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtFortyNineBorders
