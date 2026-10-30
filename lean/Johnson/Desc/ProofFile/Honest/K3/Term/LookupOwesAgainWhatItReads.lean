-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk and the thread's other letters are variables.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupOwesAgainWhatItReads.lean: the honest side of the kind
"lookup" (K3), at the first chain's letters at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean). CONDITIONAL. The shares of the debt `ExchangeS`
(Honest/Thread/PaysS.lean) in which our tops end excuse an owed item that is open in front and is of
one of four sorts: a pin of a sending, the index's pin, the stored table's pin, a constraint at one
of the four parts `P5J.parts4`. This file carries the items of these four sorts past a lookup's
step, and so turns the shares into `ExchangeS` whole at every number of the kind K3 in the written
list of places. One definition; seven theorems.

  `SamePublicPart`
      the relation "the public part is the same": nothing is asked of the states or the strings
  `headPartGoesBackOverTheSamePublicPart`     one premise: the head
      the head's part of a constraint goes back over that relation, but at the part lookCallsHeard
  `constraintReadsThePublicPartAlone`         one premise: the head
      at the honest letters a constraint says at every state and all strings what it says at one,
      at every link and part but (the head's link, lookCallsHeard)
  `constraintRidesPastEveryMember`            one premise: the head
      `RidesPastAt` at such a constraint, at every number b, of whatever kind: "keeps" is not read.
      AN ELDER LAW OF THE LIBRARY says the same at the four parts of `P5J.parts4`:
      `OnBytes.HonestTrace.ridesPastAt_constr` (Johnson/Goal/HonestTrace/ConstrAtThread.lean), not
      imported here. This one adds the part lookDigits and, off the head's link, lookCallsHeard.
      The theorems below spend it at the four parts alone
  `lookupBorderHoldsTheSitesPlace`            one premise: the head
      at a listed site's border stands the site's place, and it is the library's written place
  `lookupKeepsTheStatement`                   two premises: the head; keepsGivesTheLookupClause
      "keeps" at a listed site's border leaves the statement as it was
  `lookupExcusedItemsRidePast`                the same two premises
      `RidesPastAtS` at a listed site's border, at every item of the four excused sorts
  `lookupExchangeAtEveryBorder`               four premises: the head; sharesAtWhatTheRowOpens;
      formRidersAndKeepsBehind; keepsGivesTheLookupClause
      `ExchangeS` at every number of the kind K3

The premises, and whose each is.
  atHead                     the library's hypothesis `P5J.AtMgA` at the format's second hash function.
  sharesAtWhatTheRowOpens    the end of `lookupExchangeSharesFromWitnessFacts`
                             (Honest/K3/Term/LookupExchangeFromWitnessFacts.lean) at
                             Rd := ridersOf cs. That theorem is conditional itself. This file does
                             not import that file.
  formRidersAndKeepsBehind   `BehindS` at every listed site's border. Not shown here.
  keepsGivesTheLookupClause  the letter Kp at a listed site's place gives the lookups' own clause
                             `k3KeepsAt` (Honest/K3/Law/Thread/K3KeepsAt.lean). It bounds the letter
                             Kp from above; `BehindS` bounds it from below (the step has to give
                             "keeps"). At Kp := `k3KeepsAt Zp` this premise is an identity. That
                             `BehindS` holds at that letter is not shown here.

How the proof goes. At `lettersAt` (Honest/Thread/FirstAt.lean) the decoder of the stored table is
the constant "the input's cells". So the library's `constrQAt` (Johnson/P5J/MeansQ.lean) reads the
state through the request's reader, which reads the public part alone (`P5J.req_public_at`), and at
the head's link through the head's part, which reads that reader and, at lookCallsHeard alone, the
heard token (`headPartK6_goesBack`). The library's laws on `constrQAt` go back over every relation
that keeps these. "The public part is the same" reads the same both ways, so they are called with
the state behind in the place of the state in front. The pins: the frame's `ridesPastAt_pin` and
`ridesPastAt_pinI` (Honest/Thread/PinRides.lean) under `lookupKeepsTheStatement`, which takes the
field st of the library's `SameBut` from `lookupClauseGivesSameBut`
(Honest/K3/Term/LookupBehindAndRidesPast.lean). The stored table's pin: the frame's
`ridesPastAt_pinW` (Honest/Thread/HeadPinW.lean). The top: an owed item that is not open in front
closes the share's guard. An owed item that is open in front is of an excused sort, and the frame's
`exchangeAtS_again` (Honest/Thread/SharesS.lean) carries it; or it is of none, and that closes the
guard. The rows' own lists are not read: what the fifty rows owe is listed and counted nowhere in
this file.

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the top's four premises can hold together is not shown. The full size alone. Nothing
on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.P5J.ConstrBackAt
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.Sound (MsgT GoesBack mgAll mgBase mgAll_constr constrQAt_back
  constrQAt_back_any)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS TPart parts4)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_keeps ridesPastAt_pin ridesPastAt_pinI
  ridesPastAt_pinW)
open ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Law.Exchange (k3_number)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "TableItem" => VerifiableInference.Desc.First.Item

/-- **The public part is the same.** Nothing is asked of the two states or of the two strings. A
definition: a relation for the library's `GoesBack`. -/
def SamePublicPart : ProofFile.InstPub × TS → Strs → ProofFile.InstPub × TS → Strs → Prop :=
  fun inFront _ behind _ => inFront.1 = behind.1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" => lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-! ## 1 A constraint at the honest letters -/

/-- The head's part of a constraint, but at the part lookCallsHeard, goes back over "the public part
is the same". Conditional on the head. -/
theorem headPartGoesBackOverTheSamePublicPart (part : TPart)
    (notTheHeardReply : part ≠ .lookCallsHeard) :
    ∀ index, GoesBack SamePublicPart (atHead.𝔇.headPart part index) := fun index =>
  VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _ SamePublicPart
    (fun inFront _ behind _ related => P5J.req_public_at atHead inFront behind related) part
    (fun isTheHeardReply => absurd isTheHeardReply notTheHeardReply) index

/-- **AT THE HONEST LETTERS A CONSTRAINT READS THE PUBLIC PART ALONE**: what it says of a witness at
one state and one pair of strings it says at every state and all strings, at every link and part but
(the head's link, lookCallsHeard). Conditional on the head. -/
theorem constraintReadsThePublicPartAlone (input : Local W₀ Rc ProofFile.Inst Tr) (link : Nat)
    (part : TPart)
    (notTheHeardReplyAtTheHead : ¬ (link = headLink (P5J.At.X Zp) ∧ part = .lookCallsHeard))
    (publicPart : ProofFile.InstPub) (stateInFront stateBehind : TS)
    (stringsInFront stringsBehind : Strs) (witness : WtF)
    (saidInFront : ((LH).mg input).constr link part (publicPart, stateInFront) stringsInFront
      witness) :
    ((LH).mg input).constr link part (publicPart, stateBehind) stringsBehind witness := by
  have goesBack : GoesBack SamePublicPart
      ((mgAll { atHead.𝔇 with decT := fun _ _ => some (Q.cells input), cr1 := carryX }
        mgBase).constr link part) := by
    rw [mgAll_constr]
    by_cases isTheDigitsPart : part = .lookDigits
    · subst isTheDigitsPart
      intro inFront y behind y' v related said
      unfold P5J.constrQAt at said ⊢
      rw [if_pos rfl] at said ⊢
      exact P5J.digits_back_at atHead SamePublicPart link inFront y behind y' v related said
    · by_cases atTheHeadsLink : link = headLink (P5J.At.X Zp)
      · exact constrQAt_back_any _ _ _ _ _ link part isTheDigitsPart SamePublicPart
          (fun inFront _ behind _ related => P5J.req_public_at atHead inFront behind related)
          (fun _ _ _ _ _ => rfl)
          (headPartGoesBackOverTheSamePublicPart atHead part fun isTheHeardReply =>
            notTheHeardReplyAtTheHead ⟨atTheHeadsLink, isTheHeardReply⟩)
      · exact constrQAt_back _ _ _ _ _ link part isTheDigitsPart atTheHeadsLink SamePublicPart
          (fun inFront _ behind _ related => P5J.req_public_at atHead inFront behind related)
          (fun _ _ _ _ _ => rfl)
  exact goesBack (publicPart, stateBehind) stringsBehind (publicPart, stateInFront) stringsInFront
    witness rfl saidInFront

/-- **SUCH A CONSTRAINT RIDES PAST EVERY MEMBER**, of whatever kind: nothing is asked of "keeps".
Conditional on the head. -/
theorem constraintRidesPastEveryMember (b link : Nat) (part : TPart)
    (notTheHeardReplyAtTheHead : ¬ (link = headLink (P5J.At.X Zp) ∧ part = .lookCallsHeard)) :
    RidesPastAt (LH).thread b (VerifiableInference.Desc.First.Item.constr link part) :=
  fun _ _ mid _ _ _ witness _ _ saidInFront =>
    constraintReadsThePublicPartAlone atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      mid.st.input link part notTheHeardReplyAtTheHead _ _ _ _ _ witness saidInFront

/-! ## 2 "keeps" at a lookup's border -/

include atHead in
/-- At a listed site's border stands the site's place, and it is the library's written place; the
link is below 25. Conditional on the head. -/
theorem lookupBorderHoldsTheSitesPlace (site : Site) (siteIsListed : site ∈ lookSites Zp) :
    site.link < 25 ∧ P5J.At.ps[borderOf site.link site.digits]? = some site.at_.place ∧
      site.at_.place = IM.k3Place site.link site.digits := by
  obtain ⟨Bs, base, O⟩ := atHead.laid.opened
  obtain ⟨lot, lotIsTheLookups, lotStandsAtTheSite⟩ :=
    ProofFile.Honest.K3.Law.lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O site siteIsListed
  obtain ⟨linkBelow, placeIsWritten, -⟩ :=
    site_border atHead site siteIsListed lot lotIsTheLookups lotStandsAtTheSite
  obtain ⟨other, otherIsListed, sameLink, sameSort, otherPlace, -⟩ :=
    site_at_all_fifty atHead site.link linkBelow site.digits
  refine ⟨linkBelow, placeIsWritten, ?_⟩
  rw [← otherPlace, site_place Zp site siteIsListed, site_place Zp other otherIsListed, sameLink,
    sameSort]

/-- **"keeps" AT A LOOKUP's BORDER LEAVES THE STATEMENT AS IT WAS.** Conditional on the head and on
keepsGivesTheLookupClause at the site. -/
theorem lookupKeepsTheStatement (site : Site) (siteIsListed : site ∈ lookSites Zp)
    (keepsGivesTheLookupClause : ∀ t t', Kp site.at_.place t t' →
      k3KeepsAt Zp site.at_.place t t') :
    ∀ t t', (LH).thread.keeps (borderOf site.link site.digits) t t' → t'.st = t.st := by
  intro t t' kept
  obtain ⟨linkBelow, placeIsWritten, placeIs⟩ :=
    lookupBorderHoldsTheSitesPlace atHead site siteIsListed
  have clause := keepsGivesTheLookupClause t t'
    ((head_keeps atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w placeIsWritten t t').1 kept)
  rw [placeIs] at clause
  exact (lookupClauseGivesSameBut atHead linkBelow site.digits clause).st

/-! ## 3 The excused items ride past -/

/-- **EVERY ITEM OF THE FOUR EXCUSED SORTS RIDES PAST A LOOKUP**: a pin of a sending, the index's
pin, the stored table's pin, a constraint at one of the four parts. Conditional on the head and on
keepsGivesTheLookupClause at the site (spent at the first two sorts alone). -/
theorem lookupExcusedItemsRidePast (site : Site) (siteIsListed : site ∈ lookSites Zp)
    (keepsGivesTheLookupClause : ∀ t t', Kp site.at_.place t t' →
      k3KeepsAt Zp site.at_.place t t')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (j : TableItem)
    (ofAnExcusedSort : (∃ m t, j = .pin m t) ∨ j = .pinI ∨ j = .pinW ∨
      ∃ m q, q ∈ parts4 ∧ j = .constr m q) :
    RidesPastAtS (LH).thread Said (borderOf site.link site.digits) j := by
  rcases ofAnExcusedSort with ⟨m, t, rfl⟩ | rfl | rfl | ⟨m, q, oneOfTheFour, rfl⟩
  · exact ridesPastAtS_of _ _ (ridesPastAt_pin atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t
      (lookupKeepsTheStatement atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w site siteIsListed
        keepsGivesTheLookupClause))
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (lookupKeepsTheStatement atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w site siteIsListed
        keepsGivesTheLookupClause))
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _)
  · refine ridesPastAtS_of _ _ (constraintRidesPastEveryMember atHead H Q test carryX item n₁ n₂ b₀
      Vd Rd Kp w _ m q fun both => ?_)
    rw [both.2] at oneOfTheFour
    revert oneOfTheFour
    decide

/-! ## 4 The debt whole -/

/-- **`ExchangeS` AT EVERY NUMBER OF THE KIND K3 IN THE WRITTEN LIST OF PLACES.** Conditional on the
head and on three premises: sharesAtWhatTheRowOpens, formRidersAndKeepsBehind,
keepsGivesTheLookupClause. None of the three is shown in this file. The full size alone. -/
theorem lookupExchangeAtEveryBorder
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (sharesAtWhatTheRowOpens : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 →
      ∀ j : TableItem, j ∈ ((LH).thread.row b).owes →
      (j ∈ (LH).thread.opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ .constr m q) →
      ExchangeAtS (LH).thread Said b j)
    (formRidersAndKeepsBehind : ∀ s ∈ lookSites Zp,
      BehindS (LH).thread Said (borderOf s.link s.digits))
    (keepsGivesTheLookupClause : ∀ s ∈ lookSites Zp, ∀ t t', Kp s.at_.place t t' →
      k3KeepsAt Zp s.at_.place t t') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 → ExchangeS (LH).thread Said b := by
  intro b p placeIsWritten isALookup
  obtain ⟨l, linkBelow, d, rfl⟩ := k3_number placeIsWritten isALookup
  obtain ⟨s, siteIsListed, rfl, rfl, -, -⟩ := site_at_all_fifty atHead l linkBelow d
  refine (exchangeS_iff (LH).thread Said).2 fun (j : TableItem) owed => ?_
  by_cases openInFront : j ∈ (LH).thread.opened (borderOf s.link s.digits)
  · by_cases ofAnExcusedSort : (∃ m t, j = .pin m t) ∨ j = .pinI ∨ j = .pinW ∨
        ∃ m q, q ∈ parts4 ∧ j = .constr m q
    · exact exchangeAtS_again (LH).thread Said openInFront
        (formRidersAndKeepsBehind s siteIsListed)
        (lookupExcusedItemsRidePast atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s siteIsListed
          (keepsGivesTheLookupClause s siteIsListed) Said j ofAnExcusedSort)
    · exact sharesAtWhatTheRowOpens _ p placeIsWritten isALookup j owed fun _ =>
        ⟨fun m t isAPin => ofAnExcusedSort (Or.inl ⟨m, t, isAPin⟩),
          fun isTheIndexPin => ofAnExcusedSort (Or.inr (Or.inl isTheIndexPin)),
          fun isTheTablePin => ofAnExcusedSort (Or.inr (Or.inr (Or.inl isTheTablePin))),
          fun m q oneOfTheFour isAConstraint =>
            ofAnExcusedSort (Or.inr (Or.inr (Or.inr ⟨m, q, oneOfTheFour, isAConstraint⟩)))⟩
  · exact sharesAtWhatTheRowOpens _ p placeIsWritten isALookup j owed fun isOpen =>
      absurd isOpen openInFront

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.headPartGoesBackOverTheSamePublicPart
#print axioms ProofFile.Honest.K3.Term.constraintReadsThePublicPartAlone
#print axioms ProofFile.Honest.K3.Term.constraintRidesPastEveryMember
#print axioms ProofFile.Honest.K3.Term.lookupBorderHoldsTheSitesPlace
#print axioms ProofFile.Honest.K3.Term.lookupKeepsTheStatement
#print axioms ProofFile.Honest.K3.Term.lookupExcusedItemsRidePast
#print axioms ProofFile.Honest.K3.Term.lookupExchangeAtEveryBorder
