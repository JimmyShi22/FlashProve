-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/FitsAtLots.lean: where the proof file's description passes its own tests on the
plan, every job of the two lots of the kind K1 fits its place, up to one test on each table that is
sent along; at each segment's reads and digits nothing is sent along, so these jobs fit.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premises are IM.Open and F.planOk = true (the description's tests on its
plan; a premise of the rule too).
  fits_at_job      For every job J of lotJobs and wJobs: if each table that J sends along fits its
                   message's shape (rideFits, Johnson/Desc/ProofFile/Honest/K1/Coins.lean), then J
                   fits its place (sendFits J.P J.ride = true).
  fits_no_ride     So every job of the two lists that sends no table along fits its place.
  later_no_ride    Every job of lotJobs but the first, that is each segment's reads and digits,
                   sends no table along.
  fits_at_later    So every job of lotJobs but the first fits its place.
  planOwn_at_job   For every job J of the two lists: every code's message length is a power of two
                   (Own.lengthsFit), and J's place passes the kind K1's own tests on the plan
                   (K1.planOkOwn: every message has an admitted shape, the trees can be laid, some
                   message is sampled, every sampled message's pads fit their row).

How it fits. Where a job does not fit its place, the fields exact and fresh of Spec.fieldsAtLots say
little (AtDescLots.lean, Limits). This file shows that this does not happen at the reads' and
digits' jobs, and reduces it at the other two (the opening's and the one at the request's own table)
to rideFits at one message each. RideFits.lean and RideFitsW.lean beside this file go on from there
to all jobs. It rests on plan_at_place and k13_m4_alone
(Johnson/Desc/ProofFile/Honest/Member/Plan.lean, Uses.lean) and on AtDescStands.lean. Meant as steps
toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy
from them. Not one of the release's goal statements.

The other names.
  sendFits_of_plan   for all public numbers P: Own.lengthsFit, K1.planOkOwn and rideFits at each
                     table that is sent along give sendFits.
  plan_at_own        each sub-protocol of K1's own lot passes its test on the plan.
  plan_of_lotJob     each job of lotJobs has a sub-protocol of that lot whose test on the plan holds
                     K1.planOkOwn at the job's numbers.
  lengths_at         Own.lengthsFit at the ground's codes: a conjunct of the opening's test.

Limits. rideFits at the two tables that are sent along is not proved here (see RideFits.lean,
RideFitsW.lean). That F.planOk holds at given public files is not shown here: the library has it,
with "the maker returns", where its gate FlashProve.protocolDataWellFormed accepts (pseat_name,
Johnson/Goal/Description/ProofSeat.lean); the side library proves that it accepts at named files
(AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean). Pointwise statements: no distribution is
named. For all other limits see AtDescLots.lean.
-/
import Johnson.SendSim.Seat.AtDescStands
import Johnson.Desc.ProofFile.Honest.Member.Plan

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {X Xi : Type}

/-- The plan's own tests, and the test on each table that is sent along, give "the job fits its
place". -/
theorem sendFits_of_plan {P : K1.Par} {ride : Nat → Option Ride}
    (hl : Own.lengthsFit P.codes = true) (hp : K1.planOkOwn P = true)
    (hr : ∀ k R, k < P.sent.size → ride k = some R → rideFits P.codes (shapeAt P k) R = true) :
    sendFits P ride = true := by
  unfold K1.planOkOwn K1.planOk at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨hs, -⟩, -⟩, hpad⟩ := hp
  unfold sendFits
  rw [hl, Bool.true_and, List.all_eq_true]
  intro k hk
  have hk' : k < P.sent.size := List.mem_range.1 hk
  have hget : shapeAt P k = P.sent[k].shape := by
    unfold shapeAt Array.getD
    split
    · rfl
    · rename_i h
      exact absurd hk' h
  have h1 : Own.sentShapeFits P.codes (shapeAt P k) = true := by
    rw [hget]
    exact Array.all_eq_true.1 hs k hk'
  have h2 : (decide ((shapeAt P k).answers = 0) ||
      (K1.Msg.of P.codes (shapeAt P k)).padFits) = true := by
    by_cases h0 : (shapeAt P k).answers = 0
    · simp [h0]
    · have hm : shapeAt P k ∈ P.tuple := by
        unfold K1.Par.tuple
        refine List.mem_filter.2 ⟨List.mem_map.2 ⟨P.sent[k], by simp, hget.symm⟩, ?_⟩
        simpa using h0
      rw [List.all_eq_true.1 hpad _ hm, Bool.or_true]
  have h3 : ((ride k).map (rideFits P.codes (shapeAt P k))).getD true = true := by
    cases hrk : ride k with
    | none => rfl
    | some R => exact hr k R hk' hrk
  rw [h1, h2, h3]
  rfl

/-- Each job of the kind's own lot has a sub-protocol of that lot whose test on the plan holds the
kind's own tests at the job's numbers. -/
theorem plan_of_lotJob (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {J : SendJob (PlaceIn Xi) X} (hJ : J ∈ lotJobs no D Z G) :
    J.P.codes = G.first.codes ∧ ∃ b₀ ∈ (ProofFile.k1Pure Z).own G,
      (b₀.planOk = true → K1.planOkOwn J.P = true) := by
  unfold lotJobs at hJ
  rcases List.mem_cons.1 hJ with rfl | hJ
  · refine ⟨rfl, _, own_first Z G, fun h => ?_⟩
    have h' : (K1.planOkOwn (K1.firstPar G.first (K1.gpOf Z)) &&
        K1.firstPlanOk G.first (K1.gpOf Z).samples) = true := h
    rw [Bool.and_eq_true] at h'
    exact h'.1
  · obtain ⟨y, hy, hJ⟩ := List.mem_flatMap.1 hJ
    obtain ⟨Y, l⟩ := y
    have hY : G.built[l]? = some Y := by
      rw [← Array.getElem?_toList]
      simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hy)
    dsimp only at hJ
    split at hJ
    · cases hJ
    · rename_i pr pd reads digits hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
      rcases hJ with rfl | rfl
      · refine ⟨rfl, _, own_reads Z G hY hn, fun h => ?_⟩
        have h' : ((K1.planOkOwn (K1.parLater G.first (K1.gpOf Z) l pr 1) && reads.isSome) &&
            (IM.k1Quiet G l Y).planOk) = true := h
        rw [Bool.and_eq_true, Bool.and_eq_true] at h'
        exact h'.1.1
      · refine ⟨rfl, _, own_digits Z G hY hn, fun h => ?_⟩
        have h' : (K1.planOkOwn (K1.parLater G.first (K1.gpOf Z) l pd 2) && digits.isSome) =
            true := h
        rw [Bool.and_eq_true] at h'
        exact h'.1

/-- Every job of the kind's own lot but the first sends no table along. -/
theorem later_no_ride (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {J : SendJob (PlaceIn Xi) X} (hJ : J ∈ (lotJobs no D Z G).tail) :
    ∀ k, J.ride k = none := by
  unfold lotJobs at hJ
  rw [List.tail_cons] at hJ
  obtain ⟨y, -, hJ⟩ := List.mem_flatMap.1 hJ
  obtain ⟨Y, l⟩ := y
  dsimp only at hJ
  split at hJ
  · cases hJ
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
    rcases hJ with rfl | rfl <;> exact fun _ => rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Where the description's maker returns and the description passes its tests on the plan, each
sub-protocol of K1's own lot passes its own test. -/
theorem plan_at_own (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {b₀ : Block First.S Unit} (hown : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) : b₀.planOk = true := by
  obtain ⟨hk, -⟩ := own_kind_link hown
  obtain ⟨m, hm, hmp⟩ := member_at_own O hown
  have hb : (b₀.retype : Block First.S ProofFile.Cl) ∈ (ProofFile.k1Pure Z).blocks Bs.G₀ :=
    List.mem_append_left _ (List.mem_map.2 ⟨b₀, hown, rfl⟩)
  exact ProofFile.Honest.AtPlace.plan_of_own b₀ (ProofFile.Honest.AtPlace.plan_at_place O hp (k1_in_seat Z) hb
          (by show b₀.place.kind ≠ _; rw [hk]; decide) hm hmp)

/-- Where the description's maker returns and the description passes its tests on the plan, every
code's message length is a power of two: a conjunct of the opening's test on the plan. -/
theorem lengths_at (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Own.lengthsFit Bs.G₀.first.codes = true := by
  have h : (K1.planOkOwn (K1.firstPar Bs.G₀.first (K1.gpOf Z)) &&
      K1.firstPlanOk Bs.G₀.first (K1.gpOf Z).samples) = true :=
    plan_at_own O hp (own_first Z Bs.G₀)
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  unfold K1.firstPlanOk at h2
  simp only [Bool.and_eq_true] at h2
  exact h2.1.1.1

/-- **Where the description's maker returns and the description passes its tests on the plan, at
every job of the two lots: the codes' lengths fit, and the place passes the kind K1's own tests on
the plan.** -/
theorem planOwn_at_job (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) :
    Own.lengthsFit J.P.codes = true ∧ K1.planOkOwn J.P = true := by
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨hc, b₀, hown, h⟩ := plan_of_lotJob no D Z Bs.G₀ hJ
    exact ⟨by rw [hc]; exact lengths_at O hp, h (plan_at_own O hp hown)⟩
  · obtain ⟨msg, hm, rfl⟩ := w_of_job no D Z Bs.G₀ hJ
    refine ⟨?_, ?_⟩
    · show Own.lengthsFit Z.first.codes = true
      rw [← O.first]
      exact lengths_at O hp
    · obtain ⟨m, hmem, hmp⟩ := ProofFile.Honest.AtPlace.stands_m4 O
      obtain ⟨x, hF, hA⟩ := ProofFile.Honest.AtPlace.k13_m4_alone O (wBlock_of_msg hm) hmem hmp
      have h1 : x.planOk = true := hF.planOk (IM.plan_flat O hp m hmem)
      rw [IM.alone_planOk hA] at h1
      have h2 : (K1.planOkOwn (K1.parW Z.first (wGp Z) 4 msg) &&
          (K13.rowsB K13.atS (K13.whereOf Z) : Block First.S Unit).planOk) = true :=
        ProofFile.Honest.AtPlace.plan_of_own _ h1
      rw [Bool.and_eq_true] at h2
      exact h2.1

/-- **Where the description's maker returns and the description passes its tests on the plan, every
job of the two lots fits its place, if each table that it sends along fits its message's shape.** -/
theorem fits_at_job (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀)
    (hr : ∀ k R, k < J.P.sent.size → J.ride k = some R →
      rideFits J.P.codes (shapeAt J.P k) R = true) :
    sendFits J.P J.ride = true :=
  sendFits_of_plan (planOwn_at_job O hp no D hJ).1 (planOwn_at_job O hp no D hJ).2 hr

/-- Where the description's maker returns and the description passes its tests on the plan, every
job of the two lots that sends no table along fits its place. -/
theorem fits_no_ride (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) (h0 : ∀ k, J.ride k = none) :
    sendFits J.P J.ride = true :=
  fits_at_job O hp no D hJ fun k R _ h => by rw [h0 k] at h; cases h

/-- **Where the description's maker returns and the description passes its tests on the plan, every
job of K1's own lot but the first, that is each segment's reads and digits, fits its place.** -/
theorem fits_at_later (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ (lotJobs no D Z Bs.G₀).tail) : sendFits J.P J.ride = true :=
  fits_no_ride O hp no D (List.mem_append_left _ (List.mem_of_mem_tail hJ))
    (later_no_ride no D Z Bs.G₀ hJ)

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendFits_of_plan
#print axioms OnBytes.SendSim.Seat.later_no_ride
#print axioms OnBytes.SendSim.Seat.planOwn_at_job
#print axioms OnBytes.SendSim.Seat.fits_at_job
#print axioms OnBytes.SendSim.Seat.fits_no_ride
#print axioms OnBytes.SendSim.Seat.fits_at_later
