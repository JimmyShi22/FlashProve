-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/K1SendersTies.lean: THE PUBLIC TIES BETWEEN A SEGMENT's
MESSAGES AND THEIR SENDERS OF THE KIND K1, UNDER THE HEAD: the first segment's messages and its
fold's fresh mask against the opening's sending; every segment's later sendings' messages against
the two later sendings of its link. PUBLIC DATA ALONE: written lists of shapes, codes and rides.
Five definitions: a form of six public facts; a public test; that test laid at the three sorts of
message. Lemmas; none of the library's goals.

  `K1Tie` P ride q' S sh fold
      THE FORM: the six public premises that `copyShared_at_first`, `_at_mask`, `_at_later`
      (CopySharedAtSegment.lean of this folder; this library may not hold it) take on a sender of
      the kind K1: q' is a message of P · P's codes are the segment's · its shape is sh ·
      `ShapeFits` · it has no main row or is sampled · its ride is `rideAs` at fold
  `k1TieB`
      A PUBLIC TEST: five of the six; the sixth, `ShapeFits`, comes of the sender's own test
      `K1.sendFits`
  `shapeFits_of_sendFits`
      general: `ShapeFits` at a message of any Par whose sending fits, where the ride is `rideAs`
      at fold. The like of `shapeFits_of` (Counts.lean of this folder), which stands at the
      switches' own Par
  `k1TieB_gives`
      what the test's yes gives, with `K1.sendFits`: the form
  `k1FirstTiesW`, `k1MaskTieW`, `k1LaterTiesW`
      the test accepts at the written lists: BY LEAN's KERNEL: at the first written segment
      message n of its first sending, in front of the mask, is message n of the opening's written
      plan `parGF` · the mask is the message of the same number, at fold := the segment's row
      variables · at each of the 25 written segments the messages behind the first sending are
      two: message 0 of `placeL` m false, then message 0 of `placeL` m true
  `k1FirstTiesW_can_fail`, `k1MaskTieW_can_fail`, `k1LaterTiesW_can_fail`
      CONTROLS THAT SAY NO: at the next message of the opening, at every n · at fold := none ·
      with the two later sendings swapped, at every written segment
  `first_ties_at_head`, `mask_tie_at_head`, `later_ties_at_head`
      UNDER THE HEAD AND THE OPENING: the form, at S a member of `segmentsOf` Zp Bs.G₀, at P :=
      K1.firstPar Bs.G₀.first (K1.gpOf Zp), ride := K1.rideOf (K1.firstFold Bs.G₀.first) | P :=
      K1.parL Zp Bs.G₀ m d, ride := K1.rideOf none

By. Another group of authors' (Honest/K1/Law/FitsWritten.lean): `fits_first_written`,
`fits_fifty_head`, `parL_written`; `K1.fits_shape`, `K1.pad_le_of_fits` (Honest/K1/PadLaw.lean).
Ours: `segments_at_head` (PlacesWritten.lean of this folder); `par_at_head`, `fold_at_head`
(Honest/K11/Plays/IndexKeyWritten.lean). NEAR, not called: `shapeAt_first`, `shapeAt_later`
(Honest/K1/SeatShape.lean), general in the request; `K1.fits_ride` (Honest/K1/RideOne.lean).

WHAT IT IS NOT. Of the three laws' premises it pays the public six alone: NOT the sender's cut of a
run's coins, NOT the book's entry, NOT the filling's data. THAT THE JOBS OF A FILLING's LOTS HAVE
THESE P AND ride IS NOT SAID. Seats and numbers are not treated. The opening's fifth message, the
index masks', is no message of the segment. That the hypothesis on the public files can be met is
not said.

Limits. SIX CLOSED FACTS BY EVALUATION IN LEAN's KERNEL; two more of the other authors' beneath. The
full size and the format's second hash function alone. The head and the opening are premises. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF placeL qFull)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **THE FORM**: six public facts on message q' of a sending of the kind K1, against a segment S, a
shape sh and a fold's row variables. -/
structure K1Tie (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (q' : Nat)
    (S : SegmentPub) (sh : OnBytes.OracleShape) (fold : Option Nat) : Prop where
  hq : q' < P.sent.size
  hc : P.codes = S.sizes.codes
  hs : shapeAt P q' = sh
  fits : ShapeFits P.codes (shapeAt P q') fold
  hw : (shapeAt P q').mainRows = 0 ∨ (shapeAt P q').answers ≠ 0
  hride : ride q' = rideAs (shapeAt P q') fold

/-- **A PUBLIC TEST**: five of the six. -/
def k1TieB (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (q' : Nat)
    (S : SegmentPub) (sh : OnBytes.OracleShape) (fold : Option Nat) : Bool :=
  decide (q' < P.sent.size) && decide (P.codes = S.sizes.codes) && decide (shapeAt P q' = sh) &&
    ((shapeAt P q').mainRows == 0 || (shapeAt P q').answers != 0) &&
    decide (ride q' = rideAs (shapeAt P q') fold)

/-- The sixth, of the sender's own test. General. -/
theorem shapeFits_of_sendFits {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option K1.Ride}
    (hf : K1.sendFits P ride = true) {k : Nat} (hk : k < P.sent.size) {fold : Option Nat}
    (hr : ride k = rideAs (shapeAt P k) fold) : ShapeFits P.codes (shapeAt P k) fold := by
  refine ⟨K1.fits_shape _ _ k hf hk, ?_, fun n hn => ?_⟩
  · rw [← hr]
    exact K1.pad_le_of_fits _ _ k hf hk
  · subst hn
    have h3 := hf
    simp only [K1.sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h3
    have h4 := (h3.2 k hk).2
    rw [hr] at h4
    exact h4

/-- What the test's yes gives. -/
theorem k1TieB_gives {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option K1.Ride}
    {q' : Nat} {S : SegmentPub} {sh : OnBytes.OracleShape} {fold : Option Nat}
    (hf : K1.sendFits P ride = true) (h : k1TieB P ride q' S sh fold = true) :
    K1Tie P ride q' S sh fold := by
  unfold k1TieB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, shapeFits_of_sendFits hf h.1.1.1.1 h.2, h.1.2, h.2⟩

/-- The test at the first sending's messages in front of the mask. off: 0; a control lays 1. -/
def firstTies (S : SegmentPub) (off : Nat) : List Bool :=
  (List.range ((S.sent.headD #[]).size - 1)).map fun n =>
    k1TieB parGF (K1.rideOf (K1.firstFold qFull)) (n + off) S
      ((S.sent.headD #[]).getD n default).shape none

/-- The test at the fold's fresh mask. -/
def maskTieAt (S : SegmentPub) (fold : Option Nat) : Bool :=
  k1TieB parGF (K1.rideOf (K1.firstFold qFull)) ((S.sent.headD #[]).size - 1) S
    ((S.sent.headD #[]).getD ((S.sent.headD #[]).size - 1) default).shape fold

/-- The test at the messages behind the first sending. d: which of the link's two later sendings
message number q is held against: (· == 1); a control lays (· == 0). -/
def laterTies (m : Nat) (S : SegmentPub) (d : Nat → Bool) : List Bool :=
  ((S.sent.drop 1).flatMap (·.toList)).zipIdx.map fun x =>
    k1TieB (placeL m (d x.2)) (K1.rideOf none) 0 S x.1.shape none

set_option maxRecDepth 1000000 in
/-- **At the first written segment: every message in front of the mask**, and there are some. -/
theorem k1FirstTiesW : ((segsW.take 1).all fun S =>
    !(firstTies S 0).isEmpty && (firstTies S 0).all id) = true ∧ (segsW.take 1).length = 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: at the opening's next message it says no at every one. -/
theorem k1FirstTiesW_can_fail : ((segsW.take 1).all fun S => (firstTies S 1).all (!·)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the first written segment: the fold's fresh mask.** -/
theorem k1MaskTieW : ((segsW.take 1).all fun S => maskTieAt S (some S.foldVars)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: with no fold it says no. -/
theorem k1MaskTieW_can_fail : ((segsW.take 1).all fun S => !maskTieAt S none) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At each written segment: the two messages behind the first sending.** -/
theorem k1LaterTiesW : (segsW.zipIdx.all fun x => decide (x.2 < 25) &&
    (laterTies x.2 x.1 (· == 1)).length == 2 && (laterTies x.2 x.1 (· == 1)).all id) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: with the two later sendings swapped it says no at both, at every segment. -/
theorem k1LaterTiesW_can_fail : (segsW.zipIdx.all fun x =>
    (laterTies x.2 x.1 (· == 0)).all (!·)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- A list's first member is a member of its first one. -/
theorem mem_take_one {α : Type} {l : List α} {a : α} (h : l[0]? = some a) : a ∈ l.take 1 :=
  List.mem_of_getElem? (i := 0) (by rw [List.getElem?_take_of_lt (by omega)]; exact h)

/-- **UNDER THE HEAD: the first segment's message n, in front of the mask, is the opening's message
n.** -/
theorem first_ties_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {n : Nat}
    (hn : n < (Sg.sent.headD #[]).size - 1) :
    K1Tie (VerifiableInference.Desc.K1.firstPar Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
      (K1.rideOf (K1.firstFold Bs.G₀.first)) n Sg ((Sg.sent.headD #[]).getD n default).shape
      none := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 k1FirstTiesW.1 Sg (mem_take_one hS)
  rw [Bool.and_eq_true] at k
  have kn := List.all_eq_true.1 k.2 _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  rw [ProofFile.Honest.K11.par_at_head h O, ProofFile.Honest.K11.fold_at_head h O]
  exact k1TieB_gives K1.fits_first_written kn

/-- **UNDER THE HEAD: the first segment's fold's fresh mask is the opening's message of the same
number.** -/
theorem mask_tie_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) :
    K1Tie (VerifiableInference.Desc.K1.firstPar Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
      (K1.rideOf (K1.firstFold Bs.G₀.first)) ((Sg.sent.headD #[]).size - 1) Sg
      ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape
      (some Sg.foldVars) := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 k1MaskTieW Sg (mem_take_one hS)
  rw [ProofFile.Honest.K11.par_at_head h O, ProofFile.Honest.K11.fold_at_head h O]
  exact k1TieB_gives K1.fits_first_written k

/-- **UNDER THE HEAD: behind a segment's first sending stand two messages: message 0 of its link's
"reads", then message 0 of its "digits".** -/
theorem later_ties_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) :
    ((Sg.sent.drop 1).flatMap (·.toList)).length = 2 ∧
      ∀ q y, ((Sg.sent.drop 1).flatMap (·.toList))[q]? = some y →
        K1Tie (VerifiableInference.Desc.K1.parL Zp Bs.G₀ m (q == 1)) (K1.rideOf none) 0 Sg y.shape
          none := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 k1LaterTiesW (Sg, m) (List.mem_zipIdx_iff_getElem?.2 hS)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k
  obtain ⟨⟨hm, hl⟩, ha⟩ := k
  refine ⟨?_, fun q y hy => ?_⟩
  · unfold laterTies at hl
    rw [List.length_map, List.length_zipIdx] at hl
    exact hl
  · have kn := List.all_eq_true.1 ha _
      (List.mem_map.2 ⟨(y, q), List.mem_zipIdx_iff_getElem?.2 hy, rfl⟩)
    have hf := K1.fits_fifty_head h O hm (q == 1)
    rw [K1.parL_written h O m (q == 1)] at hf ⊢
    exact k1TieB_gives hf kn

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.K1Tie
#print axioms ProofFile.Honest.K2.Law.k1TieB
#print axioms ProofFile.Honest.K2.Law.shapeFits_of_sendFits
#print axioms ProofFile.Honest.K2.Law.k1TieB_gives
#print axioms ProofFile.Honest.K2.Law.firstTies
#print axioms ProofFile.Honest.K2.Law.maskTieAt
#print axioms ProofFile.Honest.K2.Law.laterTies
#print axioms ProofFile.Honest.K2.Law.mem_take_one
#print axioms ProofFile.Honest.K2.Law.k1FirstTiesW
#print axioms ProofFile.Honest.K2.Law.k1FirstTiesW_can_fail
#print axioms ProofFile.Honest.K2.Law.k1MaskTieW
#print axioms ProofFile.Honest.K2.Law.k1MaskTieW_can_fail
#print axioms ProofFile.Honest.K2.Law.k1LaterTiesW
#print axioms ProofFile.Honest.K2.Law.k1LaterTiesW_can_fail
#print axioms ProofFile.Honest.K2.Law.first_ties_at_head
#print axioms ProofFile.Honest.K2.Law.mask_tie_at_head
#print axioms ProofFile.Honest.K2.Law.later_ties_at_head
