-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/WRowAt356.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis), AT THE FRAME's OWN LAYING OF THE FIRST CHAIN's THREAD
(`lettersHead`, Honest/Thread/FirstHead.lean): THE SHARE OF THE EXCHANGE AT THE ITEM "wrow", AT
NUMBER 356, FROM `WitnessHasW` (ExchangeM4.lean of this folder). `WitnessHasW` IS A PREMISE ON THE
SCRIPT's WITNESS: it is shown nowhere. Two conditional statements with their proofs: calls; no
definition. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_wrow_at_356`: **the share from the thread** (`ExchangeAt`,
Honest/Thread/Shares.lean). `k13_wrowS_at_356`: the same from the pair "the thread and what is
said", at every Said (`ExchangeAtS`, Honest/Thread/SharesS.lean).

What the premise says. Where number 356 is there, the thread stands in front of it, the reply that
the state in front holds is the one asked, the challenges fit the declared rounds, that
sub-protocol's own step is played and accepted, AND THE TABLE OF THE STATE IN FRONT HOLDS JUST ONE
ROW (s.rows = [row]; where it holds none or two the premise asks nothing): at every continuation of
the challenges: for every e below 2^kCol the word that the library's reader reads off the Script's
witness, in the main table of W's number at the layout's index of e, is the sum over the rows of
that one row's weights times the matrix of the witness's cells at the column e. The words are read
through the statement and the book of the state BEHIND the step; W's number and the layout's codes
are read off the state IN FRONT. To the letter: the definition `WitnessHasW` (ExchangeM4.lean).
Nothing is asked of a pad's place, of a row's tail, of an entry that the vector leaves free, or of a
mask row.

How. `exchange_at_letters` (ExchangeM4At.lean of this folder) at these letters; of its three
premises `PublicAtM4` from the thread is had under h (`k13_public_at_356`, PileOneAt356.lean);
`ReplyRides` at 356 from the frame's clause on the reply (`head_reply`,
Honest/Thread/FirstHead.lean) where it has begun (hb); the third is hWit. Then the list's first
member.

Limits. CONDITIONAL ON h, hb AND hWit: THEY SAY NO MORE THAN: IF `WitnessHasW` HOLDS, THE SHARE
HOLDS. That h can be met is not shown here (Honest/Thread/FirstHead.lean's head says what is had of
it). THE SHARE IS A PREMISE's FORM: it says "IF number 356 is there, the thread stands in front of
it, the challenges fit the declared rounds and the sub-protocol's step is accepted, THEN the item
holds behind". That opening clause shuts nothing out under h: no statement of this file says that
number 356 is there, but it follows from two facts beneath: the written list of places has a place
at 356 (`m4_place`, ExchangeM4At.lean), and under h the chain's places are that list (the library's
`P5J.At.places_paid`, Johnson/P5J/PlacesPaid.lean); the library's `IM.back_numbers`
(Johnson/IMR/BackSeat.lean) has even number 357 there. Whether `WitnessHasW` can hold at a Script at
which the thread stands in front of number 356 is shown by nobody. W IS LINEAR IN THE WEIGHTS: these
statements are not to stand in front of a law over coins. Whoever pays the premise goes link by
link, not by assertion: that the Script's message at W's number is the sender's text, and that the
half's matrix is the matrix of the Script's cells (`MatTie`, ExchangeAtM3.lean), bear the weight;
neither is had (of the second the library has it from a premise: MatTieOfCells.lean,
MatTieOfIndex.lean of this folder). Where the thread stands nowhere all holds for nothing. Of the
row's other items at 356: "pileOne": PileOneAt356.lean; "pinV": not this kind's; "pinW": at these
letters an idle item (its decoder is the constant "the Script's cells of the input"): a share paid
by it says nothing on what is committed. BOTH STATEMENTS REST ON CLOSED FACTS THAT LEAN's KERNEL HAS
EVALUATED BENEATH (`m4_place`, `m4_pileOne_open`, ExchangeM4At.lean; and those that
PileOneAt356.lean's head names), which no independent checker has replayed. This file's imports
reach Johnson/Goal/, by the hypothesis h (`P5J.AtMgA`). Nothing outside this file calls these
statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileOneAt356

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_reply)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- `WitnessHasW` IS A PREMISE ON THE SCRIPT's WITNESS: it is shown nowhere. **THE SHARE OF THE
EXCHANGE AT "wrow", AT NUMBER 356: FROM THE THREAD**: under h, where the thread's clause on the
reply has begun (hb), from `WitnessHasW` at the frame's own laying of the thread. -/
theorem k13_wrow_at_356 (hb : b₀ ≤ 356)
    (hWit : WitnessHasW (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 Zp
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked) :
    ExchangeAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 Item.wrow := by
  have e : ExchangeOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356
      ([Item.wrow] ++ [Item.pileOne]) :=
    exchange_at_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _
      (fun _ _ _ _ hT => k13_public_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT)
      (replyRides_of_rides (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) fun _ _ hr =>
        head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb hr) hWit
  exact ((exchangeOf_append (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356
    [Item.wrow] [Item.pileOne]).1 e).1

/-- `WitnessHasW` IS A PREMISE ON THE SCRIPT's WITNESS: it is shown nowhere. **FROM THE PAIR "THE
THREAD AND WHAT IS SAID", AT EVERY Said**, under h and the same two premises. -/
theorem k13_wrowS_at_356 (hb : b₀ ≤ 356)
    (hWit : WitnessHasW (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 Zp
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
      Item.wrow :=
  exchangeAtS_of _ Said (k13_wrow_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb hWit)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_wrow_at_356
#print axioms ProofFile.Honest.K13.k13_wrowS_at_356
