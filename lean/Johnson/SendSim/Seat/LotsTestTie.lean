-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotsTestTie.lean: what the executable tests of
Johnson/SendSim/Seat/LotsTest.lean give. lotsClearB accepts exactly where the premise on the book of
hand_of_lots holds. placesApartB and lotsReadsB together imply the premise of budAtLots. lotsFitB
accepts exactly where every job fits its place, which is no premise but shows where exact and fresh
have their full content. laterNoMaskB turns the premise on the book, at a segment's reads and
digits, into a plainer equivalent. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". A short version is in the head of
LotsTest.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Z is any public part and G any ground, unless IM.Open is named. The parameters
no (the number of each place's first new message) and D (the data) of the jobs are arbitrary: no
test depends on them.
  lotPars_eq         lotPars Z G is the list of the pairs (J.P, J.ride), for J in lotJobs ++ wJobs.
  lotsClearB_iff     lotsClearB Z G Bk ord accepts if and only if the book meets BookClearAny
                     (Johnson/SendSim/At/BookWide.lean) at the sender of every job of the two lists.
                     At G = Bs.G₀ that is the premise on the book of hand_of_lots (AtDescLots.lean).
  hand_of_lotsClearB   hand_of_lots with that premise replaced by the accepting test at Bs.G₀.
  lotsFitB_iff       lotsFitB Z G accepts if and only if every job of the two lists fits its place.
  reads_of_lotsReadsB   If placesApartB F and lotsReadsB F Z G accept, then at every job J, and at
                     every way to split the first chain's list of sub-protocols at a member at J's
                     place, readsWithinB accepts at the number of trees before that member. That is
                     the premise of budAtLots (AtDescLots.lean).
  budClause_of_lotsReadsB   If the two tests accept, our clause of the rule's premise on queried
                     positions (BudClause, Johnson/SendSim/Seat/Bud.lean) holds at every job. It is
                     budAtLots applied to reads_of_lotsReadsB.
  ground_of_blank    Where the maker returns, the value of ProofFile.blankBy ProofFile.pureRoad.links Z is the
                     ground Bs.G₀. So a program can compute the ground at which to run the tests.
  clear_at_later     If laterNoMaskB Z G accepts, then at every job J of lotJobs but the first (each
                     segment's reads and digits), for every book, order and owner: BookClearAny
                     holds if and only if the owner's entries are within the sending part's number
                     of coins (WithinTakes) and no address spends a coin of the owner. It follows
                     from clearAny_iff_nothing (Johnson/SendSim/At/ClearNothing.lean).
  laterNoMask_of_shape   If shapeLaterNoMaskB accepts at G.first.shape, then laterNoMaskB Z G
                     accepts, whatever the segments of G are.
  shapeLaterNoMask_full   shapeLaterNoMaskB accepts at the full-size request's shape, which the
                     library states as a value (proofSizedFull.request,
                     Johnson/Desc/Ok/PlanWritten/SizedLit.lean). Checked by evaluation in Lean's
                     kernel.
  laterCount_full, laterByLink_full   The test is not vacuous there. That shape has 50 messages that
                     are sent after their link's first prover message: it has 25 links, and each has
                     one message at moment 1, one at moment 2 and none later. Checked by evaluation
                     in Lean's kernel.
  clear_at_later_full   If G.first.shape is that value, the equivalence of clear_at_later holds at
                     each segment's reads and digits.
  clear_at_later_open   The same at the ground Bs.G₀ of the description's maker, if the maker
                     returns (IM.Open, Johnson/IMR/SeatOpen.lean) and Z.first.shape is that value.
  shapeTest_rejects, shapeTest_first_moment, noMaskB_rejects, noMaskB_accepts   Negative tests and
                     controls: shapeLaterNoMaskB rejects a made-up shape whose one message has a
                     mask row and is sent at moment 1, and accepts the same message at moment 0;
                     noMaskB rejects the small example placePadAndFree and accepts placePadInMain.

How it fits. The theorems hand_of_lots and budAtLots (AtDescLots.lean) have public premises that, at
the book that the rule's caller picks and at a given description, are met by evaluation. This file
connects the tests of LotsTest.lean by theorems to the premises that they serve, as listed above.
Under its premise on the shape, clear_at_later_full says that at the library's full-size parameter
set the premise on the book holds at a segment's reads and digits exactly where the sender's entries
are within its number of coins and no address spends a coin of it. At such a book every run that
fresh samples anew has length 0, so at a segment's reads and digits (by inspection, not proved, 50
of the 52 jobs that jobs_52_in_scope, LotCount.lean, counts in the goals' scope at the hash function
OnBytes.secondHashFunction) fresh has no content (ClearNothing.lean, How it fits, where the case of spending
entries of length 0 is by inspection, not proved). Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

The other names.
  laterPars_eq       laterPars with no table sent along is the list of the pairs (J.P, J.ride) for
                     the jobs of lotJobs but the first.
  all_lotPars        a Boolean test holds at all of lotPars if and only if it holds at every job.
  takeWhile_split    in a list without two members of one value under f, the members before b are
                     those that takeWhile keeps while the value differs from b's.
  noMask_of_test     noMaskB P gives the first premise of clearAny_iff_nothing at P.
  laterSent_noMask, noMask_parLater   from the test on the shape to noMaskB at a later moment.
  shapeOneMask       the made-up shape of the two tests on shapeLaterNoMaskB.

Limits.
No test on a book, on a description or on the fit is evaluated here. At which values the tests must
be evaluated is said in the Limits of LotsTest.lean. Of the four tests (lotsClearB, lotsFitB,
placesApartB, lotsReadsB), three are shown to accept elsewhere. Where the maker returns and the
description passes its tests on the plan, every job fits its place (fits_at_lots_plan,
RideFitsW.lean; with lotsFitB_iff, lotsFitB accepts). There no two members of the first chain are at
one place either, which is what placesApartB asks (places_nodup,
Johnson/Desc/ProofFile/Honest/Law/Cuts.lean, as AtDescLotsRule.lean applies it). At all public files
in the goals' scope at which the library's gate accepts, lotsReadsB accepts at every opening of the
maker's value, at the hash function OnBytes.secondHashFunction (reads_of_live, ReadsAtLive.lean; bud_of_live
there draws the rule's clause on queried positions from it). That lotsClearB accepts at a book made
from a proof file, with spending entries, is not shown anywhere. Each theorem holds also where the
lists are short. At a ground without segments lotJobs has the opening alone, and clear_at_later then
says nothing. At a job at whose place the chain has no member, reads_of_lotsReadsB says nothing;
where the maker returns every job has a member (seat_at_job, AtDescStands.lean).
clear_at_later_full has the premise G.first.shape = proofSizedFull.request, and clear_at_later_open
the premise Z.first.shape = proofSizedFull.request. Neither is proved here. The library derives the
second (likeFull_in_scope, Johnson/HB/LLHARD/PlanInScope.lean) when three things hold: the public
files are in the goals' scope, Z is the public part computed from them, and the test madePinnedAt
accepts at Z. At public files in the goals' scope at which the library's gate accepts, all three
hold at every opening of the maker's value at the hash function OnBytes.secondHashFunction. The gate's entry
tests accept (plan_of_live, ReadsAtLive.lean), asks_pins (Johnson/Desc/Laid/ProofAsksLaw2.lean)
gives their row madeRow at the full size's key, and pinnedAt_of_row
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) turns it into madePinnedAt. likeFull_in_scope then
gives K1.LikeFull, whose field shape is this premise. reads_of_live takes these steps inside its
proof; no lemma states the premise, and clear_at_later_open is not applied to it. That the gate
accepts is shown in the side library alone (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean).
proofSizedFull.request is a printed value. That it is what the planner makes of given files is not
proved (SizedLit.lean, Limits).
The test on the shape is evaluated at the full-size example set's shape alone, not at the stored
small example set. The small examples placePadAndFree and placePadInMain are single places made by
hand.
Where a test rejects, nothing follows, except for the two equivalences.
-/
import Johnson.SendSim.Seat.LotsTest
import Johnson.SendSim.Seat.AtDescLots
import Johnson.SendSim.At.ClearNothing
import Johnson.Desc.K1.Law.QFull

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.PlanWritten (proofSizedFull)

variable {V W X Xi Pb : Type}

/-! ## The list of public numbers is the jobs' -/

/-- laterPars, with no table sent along, is what the jobs of lotJobs but the first have. -/
theorem laterPars_eq (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    ((laterPars Z G).map fun P => (P, rideOf none)) =
      (lotJobs (X := X) no D Z G).tail.map fun J => (J.P, J.ride) := by
  unfold laterPars lotJobs
  rw [List.tail_cons, List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn]
    rfl
  · simp only [hn]
    rfl

/-- **lotPars is the list of the jobs' public numbers and tables sent along.** -/
theorem lotPars_eq (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    lotPars Z G =
      (lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G).map fun J => (J.P, J.ride) := by
  unfold lotPars
  rw [List.map_append, laterPars_eq (X := X) no D Z G]
  congr 1
  unfold wJobs
  cases linMessageW Z.first.lin <;> rfl

/-- A Boolean test holds at all of lotPars if and only if it holds at every job. -/
theorem all_lotPars (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (f : K1.Par × (Nat → Option Ride) → Bool) :
    (lotPars Z G).all f = true ↔
      ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, f (J.P, J.ride) = true := by
  rw [lotPars_eq (X := X) no D Z G, List.all_eq_true]
  constructor
  · intro h J hJ
    exact h _ (List.mem_map.2 ⟨J, hJ, rfl⟩)
  · intro h x hx
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
    exact h J hJ

/-! ## The book and the fit -/

/-- **The test on the book accepts exactly where the book meets BookClearAny at every job's
sender.** -/
theorem lotsClearB_iff (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Bk : ProverCoinCounts) (ord : List Place) :
    lotsClearB Z G Bk ord = true ↔
      ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
        BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ := by
  unfold lotsClearB
  rw [all_lotPars (X := X) no D Z G]
  constructor
  · intro h J hJ
    exact (bookClearAnyB_iff J.P J.ride).1 (h J hJ)
  · intro h J hJ
    exact (bookClearAnyB_iff J.P J.ride).2 (h J hJ)

/-- The test on the fit accepts exactly where every job fits its place. -/
theorem lotsFitB_iff (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    lotsFitB Z G = true ↔
      ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, sendFits J.P J.ride = true := by
  unfold lotsFitB
  exact all_lotPars (X := X) no D Z G _

/-- hand_of_lots with its premise on the book replaced by the accepting test. The premise H is
proved as handAtLots in AtDescLotsProof.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem hand_of_lotsClearB {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (H : Spec.handAtLots) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall F.S₁)) (h : lotsClearB Z Bs.G₀ Bk ord = true) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd F.first.blocksInOrder).On
          (r.lay T Sd F.first.blocksInOrder).bud :=
  hand_of_lots H O φ wit no D Bk ord chain ft T Sd fs ((lotsClearB_iff no D Z Bs.G₀ Bk ord).1 h)

/-- Where the maker returns, the value of ProofFile.blankBy ProofFile.pureRoad.links Z is the ground Bs.G₀. -/
theorem ground_of_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) : G = Bs.G₀ :=
  Option.some.inj (hG.symm.trans O.blank)

/-! ## The queries -/

/-- In a list without two members of one value under f, the members before b are those that
takeWhile keeps while the value differs from b's. -/
theorem takeWhile_split {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) :
    ∀ (pre : List α) (b : α) (t : List α), ((pre ++ b :: t).map f).Nodup →
      (pre ++ b :: t).takeWhile (fun x => f x != f b) = pre
  | [], b, t, _ => by
    rw [List.nil_append, List.takeWhile_cons_of_neg (by simp)]
  | x :: pre, b, t, h => by
    have h' : (f x :: (pre ++ b :: t).map f).Nodup := h
    obtain ⟨hx, hn⟩ := List.nodup_cons.1 h'
    have hne : f x ≠ f b := fun e =>
      hx (e ▸ List.mem_map.2 ⟨b, List.mem_append_right _ (List.mem_cons_self ..), rfl⟩)
    rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using hne),
      takeWhile_split f pre b t hn]

/-- **If placesApartB and lotsReadsB accept, the premise of budAtLots holds at every job of the two
lists.** -/
theorem reads_of_lotsReadsB (F : FileDescription ProofFile.Inst) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hN : placesApartB F = true) (h : lotsReadsB F Z G = true) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
      ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = J.P.place →
        readsWithinB F J.P (treesOf F.first.blocksInOrder pre) = true := by
  intro J hJ pre b t hF hb
  have h1 : readsWithinB F J.P (treesOf F.first.blocksInOrder
      (F.first.blocksInOrder.takeWhile (·.place != J.P.place))) = true :=
    (all_lotPars (X := X) no D Z G _).1 h J hJ
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup := of_decide_eq_true hN
  have h2 : F.first.blocksInOrder.takeWhile (·.place != J.P.place) = pre := by
    rw [hF] at hn ⊢
    rw [← hb]
    exact takeWhile_split (·.place) pre b t hn
  rw [h2] at h1
  exact h1

/-- If placesApartB and lotsReadsB accept, our clause of the rule's premise on queried positions
(BudClause) holds at every job. -/
theorem budClause_of_lotsReadsB (F : FileDescription ProofFile.Inst) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hN : placesApartB F = true) (h : lotsReadsB F Z G = true) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
      BudClause (V := V) (Pb := Pb) F J.P.place (jobOver J wit) :=
  budAtLots F wit _ (reads_of_lotsReadsB F no D Z G hN h)

/-! ## A segment's reads and digits -/

/-- The test gives the first premise of clearAny_iff_nothing. -/
theorem noMask_of_test {P : K1.Par} (h : noMaskB P = true) :
    ∀ k < P.sent.size, (shapeAt P k).maskRows = 0 :=
  fun k hk => beq_iff_eq.1 (List.all_eq_true.1 h k (List.mem_range.2 hk))

/-- **Where laterNoMaskB accepts, at each segment's reads and digits a book meets BookClearAny at an
owner exactly if the owner's entries are within the sending part's number of coins (WithinTakes) and
no address spends a coin of the owner.** -/
theorem clear_at_later (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (h : laterNoMaskB Z G = true) :
    ∀ J ∈ (lotJobs (X := X) no D Z G).tail, ∀ (Bk : ProverCoinCounts) (ord : List Place) (o : Addr),
      BookClearAny J.P J.ride Bk ord o ↔
        WithinTakes J.P J.ride Bk o ∧
          ∀ p, eAll (Bk.spentBy o p) = ∅ ∧ fAll (Bk.spentBy o p) = ∅ := by
  intro J hJ Bk ord o
  have hx : (J.P, J.ride) ∈ (laterPars Z G).map fun P => (P, rideOf none) := by
    rw [laterPars_eq (X := X) no D Z G]
    exact List.mem_map.2 ⟨J, hJ, rfl⟩
  obtain ⟨P, hP, e⟩ := List.mem_map.1 hx
  have e1 : P = J.P := congrArg Prod.fst e
  have e2 : rideOf none = J.ride := congrArg Prod.snd e
  refine clearAny_iff_nothing (noMask_of_test (e1 ▸ List.all_eq_true.1 h P hP)) fun k => ?_
  rw [← e2]
  rfl

/-! ## The same off the request's shape -/

/-- Where the test on the shape accepts, what a link announces at a later moment has no mask row. -/
theorem laterSent_noMask {sh : ReqShape} (h : shapeLaterNoMaskB sh = true) (l m : Nat)
    (hm : m ≠ 0) : ∀ n ∈ K1.laterSent sh l m, n.shape.maskRows = 0 := by
  intro n hn
  unfold K1.laterSent ReqFrame.notices ReqFrame.atMoment K1.frameAt at hn
  simp only [List.toList_toArray, List.mem_map, List.mem_filter, beq_iff_eq] at hn
  obtain ⟨μ, ⟨hμ, hmom⟩, rfl⟩ := hn
  cases hL : sh.link[l]? with
  | none =>
    rw [hL] at hμ
    cases hμ
  | some L =>
    rw [hL] at hμ
    have hμ' : μ ∈ L.messages := hμ
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h L (List.mem_of_getElem? hL)) μ hμ'
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h0 | h0
    · exact absurd (hmom ▸ h0) hm
    · exact h0

/-- If the test on the shape accepts at q.shape, noMaskB accepts at every later moment's public
numbers. -/
theorem noMask_parLater {q : Params.First} (h : shapeLaterNoMaskB q.shape = true)
    (gp : _root_.Desc.Plain.GPar) (l piece m : Nat) (hm : m ≠ 0) :
    noMaskB (K1.parLater q gp l piece m) = true := by
  refine List.all_eq_true.2 fun k hk => beq_iff_eq.2 ?_
  have h1 := shape_mem (K1.parLater q gp l piece m) k (List.mem_range.1 hk)
  unfold K1.shapesOf at h1
  rw [K1.parLater_sent] at h1
  obtain ⟨n, hn, e⟩ := List.mem_map.1 h1
  rw [← e]
  exact laterSent_noMask h l m hm n hn

/-- **The test on the shape gives the test at each segment's reads and digits.** -/
theorem laterNoMask_of_shape (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (h : shapeLaterNoMaskB G.first.shape = true) : laterNoMaskB Z G = true := by
  refine List.all_eq_true.2 fun P hP => ?_
  unfold laterPars at hP
  obtain ⟨⟨Y, l⟩, -, hP⟩ := List.mem_flatMap.1 hP
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn] at hP
    cases hP
  · simp only [hn, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact noMask_parLater h _ l pr 1 Nat.one_ne_zero
    · exact noMask_parLater h _ l pd 2 (by decide)

/-- The test accepts at the full-size request's shape that the library states as a value. -/
theorem shapeLaterNoMask_full : shapeLaterNoMaskB proofSizedFull.request = true := by
  decide +kernel

/-- That shape has 50 messages that are sent after their link's first prover message, so the test
above is not vacuous there. -/
theorem laterCount_full :
    (proofSizedFull.request.link.map fun L => (L.messages.filter (·.moment != 0)).length).sum =
      50 := by
  decide +kernel

/-- That shape has 25 links, and each has one message at moment 1, one at moment 2 and none
later. -/
theorem laterByLink_full :
    (proofSizedFull.request.link.length == 25 && proofSizedFull.request.link.all fun L =>
      (L.messages.filter (·.moment == 1)).length == 1 &&
        (L.messages.filter (·.moment == 2)).length == 1 &&
        L.messages.all fun m => decide (m.moment ≤ 2)) = true := by
  decide +kernel

/-- **If G.first.shape is the library's full-size value, the equivalence of clear_at_later holds at
each segment's reads and digits.** -/
theorem clear_at_later_full (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (hs : G.first.shape = proofSizedFull.request) :
    ∀ J ∈ (lotJobs (X := X) no D Z G).tail, ∀ (Bk : ProverCoinCounts) (ord : List Place) (o : Addr),
      BookClearAny J.P J.ride Bk ord o ↔
        WithinTakes J.P J.ride Bk o ∧
          ∀ p, eAll (Bk.spentBy o p) = ∅ ∧ fAll (Bk.spentBy o p) = ∅ :=
  clear_at_later no D Z G (laterNoMask_of_shape Z G (hs ▸ shapeLaterNoMask_full))

/-- The same at the ground of the description's maker, where the maker returns and the request's
shape in the public part is the library's full-size value. -/
theorem clear_at_later_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hs : Z.first.shape = proofSizedFull.request)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    ∀ J ∈ (lotJobs (X := X) no D Z Bs.G₀).tail, ∀ (Bk : ProverCoinCounts) (ord : List Place) (o : Addr),
      BookClearAny J.P J.ride Bk ord o ↔
        WithinTakes J.P J.ride Bk o ∧
          ∀ p, eAll (Bk.spentBy o p) = ∅ ∧ fAll (Bk.spentBy o p) = ∅ :=
  clear_at_later_full no D Z Bs.G₀ (O.first ▸ hs)

/-! ## Two of the tests can reject -/

/-- A made-up shape of one link with one message: one mask row, sent at the given moment. -/
def shapeOneMask (moment : Nat) : ReqShape :=
  { (default : ReqShape) with link := [⟨0, [⟨{ maskRows := 1 }, 0, moment, 0⟩]⟩] }

/-- A negative test: a mask row at moment 1 is rejected. -/
theorem shapeTest_rejects : shapeLaterNoMaskB (shapeOneMask 1) = false := by decide +kernel

/-- Its control: the same message at moment 0 is accepted. -/
theorem shapeTest_first_moment : shapeLaterNoMaskB (shapeOneMask 0) = true := by decide +kernel

/-- A negative test: a small example with a mask row is rejected. -/
theorem noMaskB_rejects : noMaskB Small.placePadAndFree = false := by decide +kernel

/-- Its control: a small example without a mask row is accepted. -/
theorem noMaskB_accepts : noMaskB Small.placePadInMain = true := by decide +kernel

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.clear_at_later_open
#print axioms OnBytes.SendSim.Seat.hand_of_lotsClearB
#print axioms OnBytes.SendSim.Seat.ground_of_blank
#print axioms OnBytes.SendSim.Seat.laterByLink_full
#print axioms OnBytes.SendSim.Seat.laterCount_full
#print axioms OnBytes.SendSim.Seat.shapeTest_rejects
#print axioms OnBytes.SendSim.Seat.shapeTest_first_moment
#print axioms OnBytes.SendSim.Seat.noMaskB_rejects
#print axioms OnBytes.SendSim.Seat.noMaskB_accepts
#print axioms OnBytes.SendSim.Seat.laterPars_eq
#print axioms OnBytes.SendSim.Seat.lotPars_eq
#print axioms OnBytes.SendSim.Seat.all_lotPars
#print axioms OnBytes.SendSim.Seat.lotsClearB_iff
#print axioms OnBytes.SendSim.Seat.lotsFitB_iff
#print axioms OnBytes.SendSim.Seat.takeWhile_split
#print axioms OnBytes.SendSim.Seat.reads_of_lotsReadsB
#print axioms OnBytes.SendSim.Seat.budClause_of_lotsReadsB
#print axioms OnBytes.SendSim.Seat.noMask_of_test
#print axioms OnBytes.SendSim.Seat.clear_at_later
#print axioms OnBytes.SendSim.Seat.laterSent_noMask
#print axioms OnBytes.SendSim.Seat.noMask_parLater
#print axioms OnBytes.SendSim.Seat.laterNoMask_of_shape
#print axioms OnBytes.SendSim.Seat.shapeLaterNoMask_full
#print axioms OnBytes.SendSim.Seat.clear_at_later_full
#print axioms OnBytes.SendSim.Seat.shapeOneMask
