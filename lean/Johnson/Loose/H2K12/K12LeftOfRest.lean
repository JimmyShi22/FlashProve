-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.Owed354AtMg
import Johnson.Loose.H2K12.ClosedAtMg354
import Johnson.Loose.H2K12.ClosedAtHead354
import Johnson.Loose.H2K12.ClosedMembers354
import Johnson.Loose.H2K12.Seat353OfShape
import Johnson.P5J.AtMgR
/-
Johnson/Loose/H2K12/K12LeftOfRest.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN,
sub-protocol number 354 of the table's written list: PAYMENTS ON THE NAMED LIST OF DEBTS
K12Left (H2K12/Owed354AtMg.lean, which does not turn). Of its fifteen fields ELEVEN FALL: two
by unfolding at a closed term (first, codes), nine to the head and two pins, by calls of K12's
files on the closed facts; publicLeft falls to these with one smaller debt (radius); three are
handed through (heads; clear; fold, inside reached). One Lean structure, two theorems: calls.
  K12Rest₆ h 𝔏 L   WHAT IS STILL LEFT, a field a debt: SIX: heads, reached, madePin, cutPin, radius,
                   clear. Each field's docstring says what it is, who is to pay it, and whether it
                   has run at the stored full-size files. NO FIELD IS A LAW. L: the list of the
                   oracle messages' places and the trees' shapes: a letter, which the field reached
                   ties to the composed meaning's own laying
  k12Left_of_rest  K12Rest₆ → LastTypedAt → K12Left AT THE CLOSED TERM At.foldD Zp cF L
                   (Johnson/P5J/FoldAt.lean) for the public numbers that the facts on reached states
                   read: SO NO COMPONENT OF K12Left's LETTER d IS FREE ANY MORE. LastTypedAt is
                   spent for one thing: that the sub-protocol's own test on the list of rounds
                   accepts, which the field goOn's payer asks
  k12_kind_of_rest K12Rest₆ → LastTypedAt → h.Kind 𝔏 K12
WHO PAYS WHICH FIELD OF K12Left. By unfolding at At.foldD: first, codes. By the field reached: fold.
By the head alone: pubsNone (pubsNone_at, H2K12/ClosedAtHead354.lean). By the head and madePin,
through the written sendings, codes, shape and entries (Written354, WrittenAll354,
H2K12/ClosedOfPins354.lean; "the value is laid" comes off the head): places, shapesListed, tieAll
(H2K12/ClosedAtMg354.lean); laysOnce (H2K12/ClosedMembers354.lean); fence
(H2K12/ClosedAtHead354.lean); seat353 (H2K12/Seat353OfShape.lean). By both pins: indexListed, goOn
(H2K12/ClosedAtHead354.lean) and, with radius, publicLeft (H2K12/ClosedAtMg354.lean; its clause told
by H2K12/ToldOfPins354.lean: under the cut's pin what the first chain tells is a closed list).
Handed through: heads, clear.
K12Left's DOCSTRINGS SAY LESS. What they call closed tests that ran at one
set of files are, for the nine (pubsNone, places, shapesListed, tieAll, laysOnce, fence, seat353,
indexListed, goOn), THEOREMS AT EVERY PUBLIC PART AT WHICH THE HEAD AND THE PINS HOLD. indexListed,
goOn and the index masks' tree in front (by the table's own count of trees) have run true at
the texts of these very letters, tied by examples that Lean took; seat353 "has not run" and needs no
run.
WHAT IT IS NOT. A SHORTER LIST OF DEBTS AND A JOINING: IT PAYS NO LAW. No example shows that the six
fields can be met together; where one of them is false at the files the theorems say nothing. The
field reached holds the whole structure of facts on reached states (FoldFacts.lean), unpaid, because
K12Left's field fold asks it whole: it has many clauses and seven are spent: one false clause among
the rest would empty both lists for nothing. WHERE THE LIST OF THE PROOF FILE's ENTRY TESTS
(lawsAsk, Johnson/Desc/Laid/ProofAsks.lean) DOES NOT ASK THE TWO PINS, THEY FOLLOW FROM NO ACCEPT OF
THE VERIFIER; where it asks them, both follow from the head's own field laid.asks (LPFD.asks_pins,
Johnson/Desc/Laid/ProofAsksLaw2.lean, which comes with that list; pins_of_head,
H2K12/K12RestOfHead.lean). K12Rest₆ gives K12Left and K12Left gives the kind's law: laid in a bare
premise's place each can only narrow. The full size alone.
WHERE A DOCSTRING SAYS "HAS RUN": an evaluation at the stored full-size files, at the evaluating
file's own terms; that those terms are this file's letters is by reading or by examples that Lean
took, as the docstring says. An evaluation is no proof.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.Sound
open P5J (AtMgA AtMgR F0T TS Free fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS STILL LEFT OF K12Left.** -/
structure K12Rest₆ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (L : VerifiableInference.Desc.K12.Door.Laid) : Prop where
  /-- AN EQUATION ON A LETTER: 𝔏's first two sub-protocols' letters are the first flat list's head
  and rest. To be paid by whoever lays 𝔏: true by the make of a chain's flat list at the right 𝔏. -/
  heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁
  /-- THE COMPOSED MEANING's HEAD WITH THE FACTS ON EVERY REACHED STATE (Johnson/P5J/AtMgR.lean),
  at the condition of the counted form. Three fields: listed (the composed meaning's laying of the
  list returns L: an equation on the letter L; that the laying returns has run true: 199 places,
  83 shapes), start (a closed test, not spent here) and fold: FACTS ON REACHED STATES, of which
  seven clauses are spent: bookInOrder, seatsCarried, tidy, codes, bookFits, msgShapes, pileMasks.
  To be paid by the induction along the run, which is other files' to show. Of the seven, the
  first five have run true at the state at 354 of the one honest run that was walked; pileMasks by
  report; of msgShapes no run is held here. -/
  reached : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L
  /-- A PIN: A CLOSED TEST ON THE PUBLIC PART: the made sizes, the first chain's numbers, the proof
  file's sendings and the public data's shape are the written ones. To be paid from the head's own
  field laid.asks, in scope, where the list of the proof file's entry tests (lawsAsk,
  Johnson/Desc/Laid/ProofAsks.lean) asks this test: by LPFD.asks_pins
  (Johnson/Desc/Laid/ProofAsksLaw2.lean, which comes with that list), called in
  pins_of_head (H2K12/K12RestOfHead.lean). Where the list does not ask it, nobody pays it. It has
  run true at the stored full-size files. -/
  madePin : VerifiableInference.PlanWritten.madeRow Zp = true
  /-- A PIN: A CLOSED FACT ON THE IOP AS WRITTEN IN LEAN: the cut of the first chain's flat list is
  the written one. To be paid by the same lemma with cut_of_row
  (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean), under the same condition on the list of entry
  tests. The written cut itself rests on prints of Lean's evaluator
  (Johnson/Desc/First/CutWritten.lean, by its own head). The equation has run true at the stored
  full-size files, with three negative tests that fail. -/
  cutPin : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
    VerifiableInference.PlanWritten.cutFirstFull
  /-- A CLOSED FACT ON ONE RADIUS: whatever rows the maker of the sendings' rows returns at the
  three public files, the radius at sending 75, place 0 is the written rows'. To be paid by
  rad_in_scope (Johnson/HB/LLHARD/RadiiInScope.lean) from the head and
  madePin. The member's listed radius has run: 2433820 at the stored full-size files. -/
  radius : ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R → P5T.rad? R 75 0 =
    (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2)
  /-- A CLOSED TEST on the table's numbers: K12Left's field clear, handed through: what the row at
  354 lays is none of the three components that the riders read. Nobody is named to pay it as it
  stands; the wider statement RidersClearQ (Johnson/Desc/Sound/BordersSides.lean), itself
  unpaid, gives it (clear_354_of_riders, H2K12/ClosedMembers354.lean): the narrower debt is kept. It
  has run true at a sibling of these numbers (without what the sub-protocols tell), with two
  negative tests that fail. -/
  clear : Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) fullLinks P5J.At.ps 354 = true

set_option maxHeartbeats 4000000 in
/-- **THE NAMED LIST OF DEBTS, FROM THE SHORTER ONE.** -/
theorem k12Left_of_rest {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok}
    {L : VerifiableInference.Desc.K12.Door.Laid} (K : K12Rest₆ h 𝔏 L)
    (hT : LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) :
    K12Left h 𝔏 (P5J.At.foldD Zp cF L) := by
  have hl : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok (D, r) :=
    h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have WA : WrittenAll354 Zp := writtenAll354_of_pins h.scope h.laid.pub K.madePin hl
  have W : Written354 Zp := WA.toWritten354
  have hL : P5J.At.laid? Zp = some L := K.reached.listed
  obtain ⟨pre, J, leave, _, _, _, hPub, _, _⟩ := game_at_354 (o := OnBytes.secondHashFunction) (S := Z)
    (Z := Zp) (N := Np) (c := cF) (D := D.at frS.P.T.a) (ps := P5J.At.ps) h.scope hT h.laid.pub
    h.laid.places h.laid.value h.laid.planOk (LPFD.asks_written h.laid.asks)
    (by rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data) k12AllB_full
    (places_at_mg h.toAtMg)
  exact
    { heads := K.heads
      first := rfl
      codes := rfl
      places := places_atMg W (P5J.At.foldD Zp cF L) hL
      fold := K.reached.fold
      seat353 := seat353_at_head h.toAtMg W.shape
      shapesListed := shapesListed_atMg h W (P5J.At.foldD Zp cF L) hL rfl
      tieAll := tieAll_atMg h W
      publicLeft := publicLeft_atMg₂ h W (P5J.At.foldD Zp cF L) hL
        (VerifiableInference.Desc.First.told_at_written K.cutPin).2 K.radius
      laysOnce := laysOnce_of (pseats_written W) (pseatsAll_written WA) _ _ _ _ _
      clear := K.clear
      indexListed := indexListed_at W K.cutPin L hL
      fence := fence_at h W
      pubsNone := pubsNone_at h
      goOn := goOn_at h W K.madePin K.cutPin hPub.2.1.plan L hL _ rfl }

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE SHORTER LIST.** -/
theorem k12_kind_of_rest {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok}
    {L : VerifiableInference.Desc.K12.Door.Laid} (K : K12Rest₆ h 𝔏 L) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 := fun hT =>
  k12_kind_of_left (k12Left_of_rest K hT) hT

end H2K12

#print axioms H2K12.k12Left_of_rest
#print axioms H2K12.k12_kind_of_rest
