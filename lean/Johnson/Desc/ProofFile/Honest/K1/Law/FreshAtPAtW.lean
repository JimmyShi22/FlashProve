-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FreshAtPAtW.lean: THE SHARED "SENDING" (the kind K1): AT W's
SENDING PART (the owner ⟨⟨1, none, 4, .K1⟩, 0⟩; number 356 of the first chain): FreshAtP
(Johnson/SendSim/At/Fresh.lean) AT THE ONE ADDRESS p := ⟨⟨3, none, 2, .K12⟩, 0⟩, AT THE SIDE THAT
THE FRAME SEATS AT W's JOB, UNDER PREMISES ON A BOOK Bk, WHICH IS A LETTER; THE ORDER IS orderOf OF
THE DESCRIPTION, BY NAME. AN INSTANCE OF ANOTHER HOUSE's LAW; NO NEW ARGUMENT. Seven theorems; no
definition.

ON THIS STATEMENT AS TEXT: "As an instance
under premises on a letter Bk it is the FORM; (d3) is PAID when your (B1) (B2) (B3) are: spentBy |
knownBy as lists at a book that a maker returns, ord := orderOf F by name, and budAt at the run's
own askedAt." "NOTHING COUNTS."

- fold_w_four_yes: A TEST THAT SAYS YES, BY LEAN's KERNEL, AT THE WRITTEN PLAN (K1.parWF) AND A
    MADE-UP BOOK THAT HOLDS FOUR ENTRIES AND NOTHING ELSE: the other house's executable tests
    foldAnyB and withinAtB accept at the owner and p. The four are written here by hand after
    another house's written lists (AtFullSide/K14/FoldsWritten.lean, RawSmallWritten.lean), which
    this file does not import. THE ORDER OF PLACES IN THE THREE TESTS IS []: AT THESE FOUR ENTRIES
    IT IS IDLE: every receiver stands at one place, so Addr.before is settled by the part's number
    at every order (off its body).
- fold_w_bent_no: A NEGATIVE TEST: with the fourth entry's receiver bent from part 1 to part 0
    foldAnyB says no.
- fold_w_short_no: A NEGATIVE TEST: with the spent entry's count 9 for 11 foldAnyB says no.
- fold_w_early_no, fold_w_early_idle: A PAIR ON THE ORDER (
    "a fifth entry of that owner (a tail coin) carried to a part at an EARLIER place: at an order
    that lists both places foldAnyB should say false; at [] it will say true: the pair shows why ord
    must be named"): the fifth entry is made up: the coin number 3893, carried to ⟨⟨2, none, 9,
    .K12⟩, 0⟩: at the order [⟨2, none, 9, .K12⟩, ⟨3, none, 2, .K12⟩]: no; at []: yes.
- w_tail_from: PUBLIC: under the head (h, O): the number maskTailNo … 1 ρ q
    (Johnson/SendSim/At/Fresh.lean) at W's plan and ride is at least 3882, at every ρ and q.
- freshAtP_w: THE FORM. PREMISES, EACH PUBLIC: h, O: the library's head; the description's maker
    succeeds, at the head's own public part Zp · hJ: the job is of wJobs
    (Johnson/SendSim/Seat/LotW.lean); Dd, the data of W's main rows, and no are letters · hσ: the
    frame's own seating (Side.seated) returns the side; wit is a letter · hW: WithinAt, the called
    law's own premise, as it stands · hSp, hc, hs: what p spends of the owner's coins is one entry
    e, of count ⟨0, 11⟩, from the number 3882 of the larger field on · hKn: every number of the
    larger field that is known at p lies below 3882. THE END: FreshAtP φ σ Bk (orderOf …) (fun _ _
    asks => budAt (jobOver J wit).P asks) p, φ general.

WHERE THE COINS LIE (RoomAtW.lean; not imported). W's plan has two messages; message 1
rides at ⟨5, 1⟩ and has 2 mask rows; its coins begin at the number 3882 of the part's 4003 coins of
the larger field; its count of mask coins is 11: 3882 to 3892.

WHICH LAW GIVES WHAT. msg_w_head (FitsAtW.lean): under the head the list wJobs has just the job at
the written message: WHERE linMessageW RETURNS NOTHING THE LIST IS EMPTY AND hJ IS MET BY NOTHING ·
seatedAt_job (Johnson/SendSim/Seat/AtDescStands.lean): the side is Seated · parW_written
(FitsAtW.lean) and the field lin of likeFull_in_scope, then Lean's kernel at the written plan: the
three numbers that are spent: two messages; the ride ⟨5, 1⟩ at message 1; maskStart = 3882 ·
FoldSpenderAny's two fields (Johnson/SendSim/At/FoldAny.lean): by the numbers · sendFreshAtPWide
(Johnson/SendSim/At/FreshWideProofs.lean): the end. hσ IS NOT IDLE: seat_at_job (AtDescStands.lean):
under O and hJ a block stands at the place.

WHY THE THREE NUMBERS ARE EVALUATED ANEW INSIDE THE PROOFS. room_w_head (RoomAtW.lean) and
ride_w_head (RideAtPlans.lean) say these numbers; they are not imported: a sealed file in the
closure of their imports (Johnson/Desc/K14/Law/SharedConst.lean) writes out a meaning at which
noColl and shown are True by definition. By a walk of ours along the lines of imports, by text, this
file's closure holds no such file. No theorem is declared here for the three numbers. Kin: another
file's rows shapesW, startsW, ridesW (Johnson/SendSim/Seat/FastAtWrittenExact.lean) have these
numbers at the written plan, in a list's form, by Lean's kernel: not called.

Limits. NOTHING SAYS THAT ANY BOOK THAT A MAKER RETURNS MEETS hW, hSp, hc, hs AND hKn TOGETHER:
fold_w_four_yes' book is made up, and holds no row. THE BOUND budAt STANDS INSIDE THE END: that a
run's own asked positions meet it is not said here. No filling known to this file's writer has a
prover's side for K1 at W's place. WHAT THE RIDING TABLE HOLDS AT ⟨5, 1⟩ (RideRows.lean;
RoomAtW.lean's rider_rows) IS NOT SPENT HERE: the called law is general in the ride. The booked
frame (Honest/Frame.lean, Honest/Side.lean) alone. THE FULL SIZE ALONE; the format's second hash function
alone. It stands over files of another house's and of ours. No property is claimed.
Terms: lean/GLOSSARY.md.
-/
import Johnson.SendSim.At.FreshWideProofs
import Johnson.SendSim.Seat.AtDescStands
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open Johnson.Prover.Send (Rows shapeAt)
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
/-- A test that says yes: at the written plan, at a made-up book of four entries. -/
theorem fold_w_four_yes :
    (foldAnyB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] }
      [] ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ &&
    withinAtB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] }
      [] ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the fourth entry's receiver bent from part 1 to part 0. -/
theorem fold_w_bent_no :
    foldAnyB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩] }
      [] ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the spent entry's count 9 for 11. -/
theorem fold_w_short_no :
    foldAnyB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 9⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] }
      [] ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test on the order: a fifth, made-up entry carries a tail coin to a part at another
place; at an order that lists that place in front of p's foldAnyB says no. -/
theorem fold_w_early_no :
    foldAnyB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"made up: a tail coin, carried to an earlier place", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3893⟩,
          ⟨0, 1⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩] }
      [⟨2, none, 9, .K12⟩, ⟨3, none, 2, .K12⟩]
      ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Its twin: at the same book, at the order [], foldAnyB says yes: the order is no idle letter. -/
theorem fold_w_early_idle :
    foldAnyB K1.parWF (rideOf (wFold K1.qFull.lin))
      { first := [], shared := [], second := [], cuts := [], ahead :=
      [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
        ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
          ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
        ⟨"made up: a tail coin, carried to an earlier place", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3893⟩,
          ⟨0, 1⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩] }
      [] ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- Under the head the numbers maskTailNo at W's message 1 lie from 3882 on. -/
theorem w_tail_from (ρ q : Nat) :
    3882 ≤ maskTailNo (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
      (rideOf (wFold Zp.first.lin)) 1 ρ q := by
  have hst : maskStart (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
      (rideOf (wFold Zp.first.lin)) 1 = 3882 := by
    rw [parW_written h O,
      (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  unfold maskTailNo
  rw [hst]
  omega

/-- "As an instance under premises on a letter Bk it is the FORM".
**FreshAtP AT W's SENDING PART, AT p := ⟨⟨3, none, 2, .K12⟩, 0⟩.** -/
theorem freshAtP_w {V W X Xi Pb : Type} (wit : W → PlaceIn Xi) (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ wJobs no Dd Zp Bs.G₀) {fs : List (Fall (F0T OnBytes.secondHashFunction Zp Np cF).S₁)}
    {σ : Side (F0T OnBytes.secondHashFunction Zp Np cF).S₁
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl V W X Pb}
    (hσ : Side.seated (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs = some σ)
    (φ : Face V W Pb) (Bk : ProverCoinCounts) {e : Ahead}
    (hW : WithinAt J.P J.ride Bk (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) ⟨σ.block.place, 0⟩
      ⟨⟨3, none, 2, .K12⟩, 0⟩)
    (hSp : Bk.spentBy ⟨σ.block.place, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = [e])
    (hc : e.count = ⟨0, 11⟩) (hs : e.start.e = 3882)
    (hKn : ∀ i ∈ eAll (Bk.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) ⟨σ.block.place, 0⟩
      ⟨⟨3, none, 2, .K12⟩, 0⟩), i < 3882) :
    FreshAtP φ σ Bk (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
      (fun _ _ asks => budAt (jobOver J wit).P asks) ⟨⟨3, none, 2, .K12⟩, 0⟩ := by
  have hS : Seated σ (jobOver J wit) :=
    seatedAt_job O wit no Dd (List.mem_append_right _ hJ) hσ
  have hJe : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀) := by
    have hJ' := hJ
    unfold wJobs at hJ'
    rw [msg_w_head h O] at hJ'
    simpa using hJ'
  subst hJe
  have hst : maskStart (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
      (rideOf (wFold Zp.first.lin)) 1 = 3882 := by
    rw [parW_written h O,
      (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  have hrd : rideOf (wFold Zp.first.lin) 1 = some ⟨5, 1⟩ := by
    rw [(K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  refine sendFreshAtPWide _ _ _ _ _ _ φ σ _ Bk _ _ hS hW (Or.inr (Or.inr ⟨⟨1, ⟨5, 1⟩, e, ?_,
    hrd, hSp, hc, hs.trans hst.symm, ?_⟩, ?_⟩))
  · show 1 < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size
    rw [parW_written h O]
    decide +kernel
  · intro ρ _ q _ hmem
    exact absurd (hKn _ hmem) (Nat.not_lt.2 (w_tail_from h O ρ q))
  · refine Finset.disjoint_left.2 fun i hi hk => ?_
    rw [hSp] at hi
    have h1 : i ∈ eOf e := by simpa [eAll] using hi
    have h2 := (Finset.mem_Ico.1 h1).1
    have h3 := hKn i hk
    omega

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.fold_w_four_yes
#print axioms ProofFile.Honest.K1.fold_w_bent_no
#print axioms ProofFile.Honest.K1.fold_w_short_no
#print axioms ProofFile.Honest.K1.fold_w_early_no
#print axioms ProofFile.Honest.K1.fold_w_early_idle
#print axioms ProofFile.Honest.K1.w_tail_from
#print axioms ProofFile.Honest.K1.freshAtP_w
