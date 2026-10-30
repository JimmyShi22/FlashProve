-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BOOK OF ANY RETURN OF THE MAKER; THE SCRIPT A LETTER.
Johnson/Desc/ProofFile/Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean: the honest side of the kind
"lookup" (K3): ALL THAT THE FIFTY LOOKUPS ASK OF WHOEVER WRITES THE `Script` (Honest/Thread/First.lean),
as one structure, `LookupsAskOfTheScript`; and, from it, the named premises that the lookups' own
theorems spend. It overtakes every earlier sheet of this house's asks.

Why. A lookup sends no oracle message. What it reads of the witness was sent by other kinds: the
opening (K1) and the switches (K2) send each link's messages of moment 0, with the link's mask row;
the job "digits" sends the arrays BZ and ZZ; the stored table is the index's. On the honest side the
witness is `Script.wit Q k input heard`. So the lookups' debts at the witness come down to sentences on
Q's fields `msg` and `cells`. THESE SEVEN FIELDS ARE ALL OF THEM. Nothing is asked of `pad`, `table`,
`fixed`, `tok`; of `fixedMsg` only what the sentences on `msg` imply.

THE NUMBER OF CHALLENGES stands at its value everywhere: `challengesHeardAtTheLookup` cF link digits:
as many as the first chain's rounds in front of that lookup. Each sentence speaks of lists of at
least that many challenges: the fewest lists that the lookups' theorems can still do with. So a
sender's sentence that holds from the sender's own border on gives ours: every sender of a link
stands in front of the link's lookups (not shown here). WHY THE NUMBER GOES BY THE LINK: at one number
for all 25 links, small enough for an early lookup to spend, the later links' sentences would speak
of lists that are shorter than their senders' borders, where no sender's sentence speaks: they would
have no payer.

THE FIELDS: what each asks · of whom · where it asks nothing · which theorem of ours spends it.
  1 `cellsAreLaid`            at each link: the form `LaysFilling` (Honest/K5/Law/LaysFilling.lean): the
       messages of moment 0 hold what the frame's filling `firstData` lays in their main rows; seat
       and heard, the filling's two public letters, are the payer's to choose · OF K1's authors
       (link 0) and K2's (links 1 to 24) and whoever lays Q · nothing where the filling lays nothing,
       of mask rows, of inputs outside valid · SPENT by `packedCellsOfTheInputFromLaysFilling`
       (Term/PackedTraceCellsFromLaysFilling.lean)
  2 `readersReadTheTrace`     no sentence on Q: the letter readers, which 1, 3 and 6 name, reads as cells
       the input's own trace · OF whoever lays readers · SPENT with 1 and 3
  3 `digitsAreLaid`           at each link: `ScriptLaysTheFillingAtTheLink`
       (Term/DigitArraysFromTheDigitsFilling.lean) at the digits' filling and the seats of "BZ" · OF the
       authors of the job "digits" (K1's later sendings) and whoever lays Q · nothing where that
       filling lays nothing, of mask rows · SPENT by `digitArraysAtTheSiteFromOneSentence`
       (Term/DigitArraysAtEverySiteFromOneSentence.lean)
  4 `storedCellsAreTheIndex`  `ScriptCellsAreTheIndexWeights` (Term/ScriptHoldsTheHonestValues.lean): on
       Q's field cells · OF whoever lays that field · at every row and column: where the letters'
       reader is 0 outside a shape the index's entry must be 0 · SPENT as it stands, at the layers'
       links and the head's (Term/LookupWitnessFactsAtTheHonestTrace.lean)
  5 `openingsTextIsLaid`      `OwnMsgs` (Honest/Thread/ScriptLots.lean) at K1's own whole-message text of the
       opening's message number 0, under the number `maskRowMessageNumber` Zp 0 · OF K1's authors
       and whoever lays Q · nothing where that text answers nothing · SPENT by
       `scriptLaysOwnersCoinsAtEveryLink` (Term/MaskRowOwnerAtTheWrittenBook.lean)
  6 `switchesTextsAreLaid`    the like at K2's own whole-message text of message number 3 (odd link) or 2
       (even link) of each switch that leads into a link below 25 · OF K2's authors and whoever
       lays Q · SPENT by the same
  7 `switchTextsAnswer`       no sentence on Q: `SwitchTextsAnswer`: K2's three conditions under which 6's
       texts answer at all: the closing's public test, that the frame hands a switch's part its
       coins at the book, the lot's public test at every valid input · OF K2's authors · SPENT by the
       same. Without it 6 could hold emptily.

  `challengesHeardAtTheLookup`                    the number
  `challengesHeardAtTheLookupIsTheThreads`        it is front + roundsTo bs at the border, at the thread
  `challengesHeardAtTheCallsAreHeardAtBothLookups`   the calls' number is at most the digits'
  `LookupsAskOfTheScript`                         THE STRUCTURE
  `digitArraysFromWhatTheLookupsAsk`              from 2 and 3: `ScriptHoldsTheDigitArrays` at a site
  `storedCellsFromWhatTheLookupsAsk`              from 4: the same at every number of challenges
  `maskRowsFromWhatTheLookupsAsk`                 from 5, 6, 7: the named premise on the mask row at each
                                                  of the 25 links, at the written owner and start

Limits. A DEFINITION AND CALLS. NO `Script` IS SHOWN TO MEET THE STRUCTURE: that its seven fields can
hold together is shown nowhere; 1 and 5 | 6 speak of the same messages (main rows there, the mask row
here) and 1 and 3 of different ones. The step from `maskRowsFromWhatTheLookupsAsk` to
`ScriptLaysEveryLinksMaskRow` stands in the side library
(AtFullSide/Honest/K3/Term/MaskRowAtEveryLinkFromOwnersTexts.lean), under one more premise, that the
public files are one of the two named sets. What the lookups ask of the INPUT (that it holds the
honest trace), of the BOOK, of the PROVER's list and of the thread's other letters is not here. The
trace's type is `Cells`. The elder row. The full size and the earlier hash alone. A sentence that names
a run's coins may not stand in front of a law over coins unless it is named there: 5 and 6 do.
Nothing is claimed on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowOwnerAtTheWrittenBook
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskEntriesAtTheWitness
import Johnson.Desc.ProofFile.Honest.K3.Term.DigitArraysAtEverySiteFromOneSentence
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (seatsOf pairOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.First.Look (digAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K1 (digitsFill firstFold placeJob PlaceIn)
open ProofFile.Honest.K2 (switchPlaces)
open ProofFile.Honest.K5 (LaysFilling)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **How many challenges have been heard in front of a lookup**: the rounds of the first chain's
sub-protocols in front of the lookup of that link and sort. Public. At the first chain's thread
(`Letters.thread`, Honest/Thread/First.lean, at `lettersAt`) it is front + `roundsTo` bs at the lookup's
border: there front is 0 and bs is cF.blocksInOrder. -/
def challengesHeardAtTheLookup (cF : Chain TS ProofFile.Cl) (link : Nat) (digits : Bool) : Nat :=
  roundsTo cF.blocksInOrder (borderOf link digits)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}

/-- **ALL THAT THE LOOKUPS ASK OF THE SCRIPT's WRITER.** atHead: the library's hypothesis at the full
size. makerReturns: A is a return of the maker, at any filling: the book is A.B. Q: THE SCRIPT, A
LETTER. valid: the inputs that are spoken of. weights: the index's reader. readers: the frame's
readers of an input. openingsLens, openingsOwnState, openingsFirstNumber, openingsData: the letters of
K1's text at the opening's job. switchesData, layout, segments: the letters of K2's text.
challengesRead: by the link: how many challenges the sender's text of that link's mask row's message
is handed. Each field's docstring says what it asks and of whom; the file's head says where it asks
nothing and who spends it. A definition: the form of a hypothesis; nothing shows that it is met. -/
structure LookupsAskOfTheScript (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {W₀ Rc X₀ X : Type} {filling : ProofFile.Honest.OnlineProverParts W₀ Rc Cells X₀ X}
    {A : ProofFile.Honest.OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL filling = .ok A)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (valid : Local W₀ Rc ProofFile.Inst Cells → Prop) (weights : W₀ → Weights)
    (readers : Local W₀ Rc ProofFile.Inst Cells → Readers)
    {OpeningsInstance OpeningsOwnState : Type}
    (openingsLens : Local W₀ Rc ProofFile.Inst Cells → PlaceIn OpeningsInstance)
    (openingsOwnState : OpeningsOwnState) (openingsFirstNumber : Nat)
    (openingsData : RowDataOf OpeningsInstance) (switchesData : RowDataOf ProofFile.Inst)
    (layout : OnBytes.Params.ReqLayout) (segments : List K2.SegmentPub)
    (challengesRead : Nat → Nat) : Prop where
  /-- ON `Q.msg`, of the senders of each link's messages of moment 0: their main rows hold what the
  frame's filling lays. The payer chooses the filling's two public letters -/
  cellsAreLaid : ∀ link, link < 25 → ∃ (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat),
    LaysFilling atHead Q valid (challengesHeardAtTheLookup cF link false) readers seat heard link
  /-- ON THE LETTER readers: as cells it reads the input's own trace -/
  readersReadTheTrace : ∀ input, (readers input).cells = input.trace
  /-- ON `Q.msg`, of the sender of each link's arrays BZ and ZZ: its main rows hold what the digits'
  filling lays, at the ground that `blankBy` makes of the plan -/
  digitsAreLaid : ∀ ground, ProofFile.blankBy ProofFile.pureRoad.links Zp = some ground → ∀ link, link < 25 →
    ScriptLaysTheFillingAtTheLink Zp Q valid (challengesHeardAtTheLookup cF link true) readers
      (digitsFill Zp ground (matsOwn ground.W)) (pairOf (seatsOf Zp ground "BZ")) link
  /-- ON `Q.cells`: the stored table's entries are the index's -/
  storedCellsAreTheIndex : ScriptCellsAreTheIndexWeights Q atHead.𝔇.l3 valid 0
    fun input => (weights input.w₀).entry
  /-- ON `Q.msg`, of K1's authors: the message that holds link 0's mask row is what the opening's own
  text of its message number 0 answers -/
  openingsTextIsLaid : OwnMsgs Q valid (challengesHeardAtTheLookup cF 0 false)
    (maskRowMessageNumber Zp 0) (challengesRead 0)
    (K1.msgTxt 0 openingsLens
      (placeJob (firstPar A.G.first (gpOf A.Z)) openingsFirstNumber (firstFold A.G.first)
        openingsData) openingsOwnState 0)
  /-- ON `Q.msg`, of K2's authors: the message that holds a later link's mask row is what the own text
  of the switch into that link answers, at the message that `maskRowMessageInSwitch` names -/
  switchesTextsAreLaid : ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
    OwnMsgs Q valid (challengesHeardAtTheLookup cF place.link false)
      (maskRowMessageNumber Zp place.link) (challengesRead place.link)
      (K2.switchMsgTxt 0 switchesData readers (K2.lotClosingAt layout segments) place
        (maskRowMessageInSwitch place.link))
  /-- ON PUBLIC DATA, THE BOOK AND THE VALID INPUTS, of K2's authors: these texts answer -/
  switchTextsAnswer : SwitchTextsAnswer A.B switchesData layout segments valid
    (switchPlaces A.Z A.G)

/-! ## The number, at the thread and between a link's two lookups -/

/-- **At the first chain's thread under the head the number is front + `roundsTo` bs at the lookup's
border**: the form in which the lookups' theorems ask "enough challenges are heard". By the texts of
`lettersHead`, `lettersAt` and `Letters.thread`: front is 0, bs is cF.blocksInOrder. -/
theorem challengesHeardAtTheLookupIsTheThreads (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → VerifiableInference.Desc.Strs →
      ProofFile.Honest.FirstThread.WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (valid : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : VerifiableInference.Desc.Place → TS → TS → Prop) (input : Local W₀ Rc ProofFile.Inst Tr)
    (link : Nat) (digits : Bool) :
    (ProofFile.Honest.FirstThread.lettersHead atHead H Q test carryX item n₁ n₂ b₀ valid rides keeps
        input).thread.front +
      roundsTo (ProofFile.Honest.FirstThread.lettersHead atHead H Q test carryX item n₁ n₂ b₀ valid rides
        keeps input).thread.bs (borderOf link digits) =
      challengesHeardAtTheLookup cF link digits :=
  Nat.zero_add _

/-- What has been heard in front of a link's lookup on the calls has been heard in front of either
of its lookups. -/
theorem challengesHeardAtTheCallsAreHeardAtBothLookups (cF : Chain TS ProofFile.Cl) (link : Nat)
    (digits : Bool) :
    challengesHeardAtTheLookup cF link false ≤ challengesHeardAtTheLookup cF link digits := by
  refine ProofFile.Honest.roundsTo_mono cF.blocksInOrder _ _ ?_
  unfold borderOf VerifiableInference.Desc.Sound.MgAt.ixOf
  cases digits <;> simp

/-! ## What the structure gives -/

section
variable {atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀}
  {W₀ Rc X₀ X : Type} {filling : ProofFile.Honest.OnlineProverParts W₀ Rc Cells X₀ X}
  {A : ProofFile.Honest.OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL filling = .ok A}
  {Q : Script A.B (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {weights : W₀ → Weights}
  {readers : Local W₀ Rc ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
  {openingsLens : Local W₀ Rc ProofFile.Inst Cells → PlaceIn OpeningsInstance}
  {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
  {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
  {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub} {challengesRead : Nat → Nat}

/-- **FROM FIELDS 2 AND 3: THE DIGITS' ARRAYS AT A SITE.** `ScriptHoldsTheDigitArrays`
(Term/ScriptHoldsTheHonestValues.lean) at a site on the digits, at the number of challenges heard in
front of that lookup. CONDITIONAL on the structure; the site, its sort, its sampling round, what
`digAt` answers at its link; samplingRoundIsHeardInFront: public: the round that samples the matrix
stands in front of the lookup (payers, by reading: the public test `rngFrontB`,
Honest/K3/Law/Keep/SiteRng.lean, and the site's field base). -/
theorem digitArraysFromWhatTheLookupsAsk
    (asked : LookupsAskOfTheScript atHead makerReturns Q valid weights readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments challengesRead)
    {site : Site} (siteIsALookups : site ∈ lookSites Zp) (siteIsOnTheDigits : site.digits = true)
    {round : Nat} (siteRound : site.rng = some round) {x : PlaceL} {tl : HTailF2}
    (placeAndTail : digAt Zp.p.X site.link = some (x, tl))
    (samplingRoundIsHeardInFront : round + 1 ≤ challengesHeardAtTheLookup cF site.link true) :
    ScriptHoldsTheDigitArrays Q atHead.𝔇.sent atHead.𝔇.l3 valid
      (challengesHeardAtTheLookup cF site.link true) x tl
      (fun input heard => zzOwn Zp.p.X site.link input.trace (tritsAt heard round)) := by
  obtain ⟨Bs, base, O⟩ := atHead.laid.opened
  exact digitArraysAtTheSiteFromOneSentence atHead Q siteIsALookups siteIsOnTheDigits rfl siteRound
    placeAndTail samplingRoundIsHeardInFront asked.readersReadTheTrace O.blank
    (asked.digitsAreLaid _ O.blank site.link (Law.AtThr.link_lt_head atHead site siteIsALookups))

/-- **FROM FIELD 4: THE STORED TABLE, at every number of challenges.** -/
theorem storedCellsFromWhatTheLookupsAsk
    (asked : LookupsAskOfTheScript atHead makerReturns Q valid weights readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments challengesRead)
    (challengesHeard : Nat) :
    ScriptCellsAreTheIndexWeights Q atHead.𝔇.l3 valid challengesHeard
      fun input => (weights input.w₀).entry :=
  fun k input heard isValid _ => asked.storedCellsAreTheIndex k input heard isValid (Nat.zero_le _)

/-- **FROM FIELDS 5, 6 AND 7: THE MASK ROW AT EACH OF THE 25 LINKS**: the lookups' named premise
`ScriptLaysOwnersCoinsInMaskRow` (Term/MaskRowFromScript.lean) at the written owner and start, up to
8192 entries, under the number `maskRowMessageNumber` Zp, from the challenges heard in front of the
link's lookup on the calls. -/
theorem maskRowsFromWhatTheLookupsAsk
    (asked : LookupsAskOfTheScript atHead makerReturns Q valid weights readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead) :
    ∀ link, link < 25 → ∀ count, count ≤ 8192 →
      ScriptLaysOwnersCoinsInMaskRow Q valid (challengesHeardAtTheLookup cF link false)
        (maskRowMessageNumber Zp link) (maskRowOwnerWritten link) (maskRowStartWritten link) count :=
  scriptLaysOwnersCoinsAtEveryLink atHead makerReturns
    (challengesInFront := fun link => challengesHeardAtTheLookup cF link false)
    (messageNumber := maskRowMessageNumber Zp) (challengesRead := challengesRead) openingsLens
    openingsOwnState openingsFirstNumber openingsData asked.openingsTextIsLaid switchesData readers
    layout segments asked.switchTextsAnswer asked.switchesTextsAreLaid

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.challengesHeardAtTheLookup
#print axioms ProofFile.Honest.K3.Term.LookupsAskOfTheScript
#print axioms ProofFile.Honest.K3.Term.challengesHeardAtTheLookupIsTheThreads
#print axioms ProofFile.Honest.K3.Term.challengesHeardAtTheCallsAreHeardAtBothLookups
#print axioms ProofFile.Honest.K3.Term.digitArraysFromWhatTheLookupsAsk
#print axioms ProofFile.Honest.K3.Term.storedCellsFromWhatTheLookupsAsk
#print axioms ProofFile.Honest.K3.Term.maskRowsFromWhatTheLookupsAsk
