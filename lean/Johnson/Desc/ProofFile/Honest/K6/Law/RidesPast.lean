-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RidesPast.lean: THREE ITEMS THAT THE OUTPUT HEAD's OWN
SUB-PROTOCOL READS AND LEAVES (the pins of what the head's segment has sent first; the committed
table's pin; "the witness's cells are small") RIDE PAST ITS MEMBER, AND ARE IN HAND AGAIN BEHIND IT:
at the first chain's thread as it is laid at the library's hypothesis, border 341.

What the file holds. `keeps_st`: what an accepted step leaves (`K6Keeps`,
Johnson/Desc/K6/Honest/Law/Keeps.lean) leaves the statement as it was. `k6_pin_rides`: so a pin at
the threads says of the state behind what it says of the state in front: by the thread's own law on
what a pin reads (`ansJT_rows`, Honest/Thread/Ans.lean). `k6_ridesPast_pin`: the share of
`RidesPastS` (Honest/Thread/SharesS.lean) at every item pin m t. `ridesPast_small`: the share at the
item constr 24 small, at EVERY border: at the threads it reads neither the verifier's state nor what
the strings gain: the two sentences are one by unfolding; nothing of `keeps` is spent. `opened_341`:
both items are open at border 341: by the kernel, on the thread's own closed lists. `owes_341`: the
row at 341 owes seven items, these three last: by the kernel. `k6_exchange_pin`,
`k6_exchange_small`, `k6_exchange_pinW`: the three shares of `ExchangeS` at 341: the first two by
`exchangeAtS_again` (SharesS.lean), the third by the thread's own `exchangeAt_pinW`
(Honest/Thread/HeadPinW.lean). `k6_exchangeS_of_four`: so `ExchangeS` at 341 whole, from the shares
of the four items that the sub-protocol makes, each a named premise.

A NEW PREMISE, AT THE PINS ALONE: hKp': the letter Kp at the sub-protocol's place GIVES `K6Keeps`.
Honest/K6/Law/Behind.lean asks the converse (hKp: `K6Keeps` gives the letter). Whoever wants both
lays a letter that IS `K6Keeps` at that place, up to ↔.

Limits. THE FULL SIZE ALONE, and at that family of threads alone. `BehindS` at 341 is a premise of
the two shares that spend it: Honest/K6/Law/Behind.lean has it under its own premises, at its own
letters. The other four items that the row owes are other files' to pay, and stand here as four
named premises. It is shown of no step that the member accepts it, nor that the thread holds at any
stand. Modules under lean/Johnson/Goal/ are among what this file imports: it imports no module of
that folder by name; by a reader's program on names its text names nothing that is declared there: a
comparison of text, which proves no absence. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Behind
import Johnson.Desc.ProofFile.Honest.Thread.Ans
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6 k6_at341)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_keeps exchangeAt_pinW)

/-- What an accepted step leaves, leaves the statement as it was. CONDITIONAL: `K6Keeps`. -/
theorem keeps_st {s s' : TS} (K : K6Keeps s s') : s'.st = s.st := by
  have h := congrArg VerifiableInference.Desc.First.S.st K.here
  exact h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A PIN AT THE THREADS SAYS OF THE STATE BEHIND WHAT IT SAYS OF THE STATE IN FRONT**: at every
seat, whatever was handed to the chain and whatever the oracles are. CONDITIONAL: `K6Keeps`. -/
theorem k6_pin_rides {s s' : TS} (K : K6Keeps s s') (j t : Nat) (p p' : ProofFile.InstPub)
    (y y' : Strs) (v : WtF)
    (h0 : ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) j t (p, s) y
      v) :
    ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) j t (p', s') y' v :=
  ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (fun _ _ _ => by rw [keeps_st K]) h0

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **EVERY ITEM pin m t RIDES PAST THE MEMBER NUMBER 341.** CONDITIONAL: the hypothesis h; hKp':
the letter Kp at the sub-protocol's place gives `K6Keeps`. -/
theorem k6_ridesPast_pin (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s') (m t : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.pin m t) := by
  intro k s μ E s' ps v _ hK h0
  have K : K6Keeps s s' := hKp' s s'
    ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').1 hK)
  have h1 : ∀ a ∈ (P5J.At.N Zp cF).sent m t,
      ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) a.1 a.2
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k μ s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := h0
  show ∀ a ∈ (P5J.At.N Zp cF).sent m t,
      ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) a.1 a.2
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k μ s')
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v
  intro a ha
  exact k6_pin_rides K a.1 a.2 _ _ _ _ v (h1 a ha)

/-- **THE ITEM constr 24 small RIDES PAST EVERY MEMBER**: at the threads it reads neither the
verifier's state nor what the strings gain: the two sentences are one by unfolding. CONDITIONAL: the
hypothesis h: no more. -/
theorem ridesPast_small (b : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b
      (Item.constr 24 .small) :=
  fun _ _ _ _ _ _ _ _ _ h0 => h0

/-- **Both items are open at border 341.** By the kernel, on the thread's closed lists of segments
and places. CONDITIONAL: the hypothesis h, for the thread's sake alone. -/
theorem opened_341 :
    Item.pin 24 0 ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 341 ∧
      Item.constr 24 .small ∈
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 341 := by
  have e : Item.pin 24 0 ∈ fwdOpen (start P5J.At.links)
        (FirstRows.rows P5J.At.links P5J.At.ps) 341 ∧
      Item.constr 24 .small ∈ fwdOpen (start P5J.At.links)
        (FirstRows.rows P5J.At.links P5J.At.ps) 341 := by
    decide +kernel
  exact e

/-- **WHAT THE ROW AT BORDER 341 OWES: SEVEN ITEMS**: the four that the sub-protocol makes, then the
three that it reads and leaves. By the kernel, on the library's table of rows (`segRow`,
Johnson/Desc/First/Borders.lean) read forward (`FwdRow.of`, Honest/Thread/Thr.lean). CONDITIONAL:
the hypothesis h, for the thread's sake alone. -/
theorem owes_341 :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row 341).owes =
      [.formsT 24 4 "own", .formsT 24 3 "planes", .formsT 24 4 "join", .formsT 24 4 "weights",
        .pin 24 0, .pinW, .constr 24 .small] := by
  have e : (FirstRows.rows P5J.At.links P5J.At.ps 341).owes =
      [.formsT 24 4 "own", .formsT 24 3 "planes", .formsT 24 4 "join", .formsT 24 4 "weights",
        .pin 24 0, .pinW, .constr 24 .small] := by
    decide +kernel
  exact e

/-- **THE PINS OF WHAT THE HEAD's SEGMENT HAS SENT FIRST ARE IN HAND AGAIN BEHIND THE MEMBER.**
CONDITIONAL: the hypothesis h; hB: `BehindS` at 341; hKp'. -/
theorem k6_exchange_pin
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s') :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.pin 24 0) :=
  exchangeAtS_again _ Said (opened_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).1 hB
    (k6_ridesPast_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hKp' 24 0)

/-- **"THE WITNESS's CELLS ARE SMALL" IS IN HAND AGAIN BEHIND THE MEMBER.** CONDITIONAL: the
hypothesis h; hB: `BehindS` at 341. -/
theorem k6_exchange_small
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.constr 24 .small) :=
  exchangeAtS_again _ Said (opened_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).2 hB
    (ridesPast_small h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said 341)

/-- **The committed table's pin** (the item pinW): the thread's own law, laid beside a sentence
Said. CONDITIONAL: the hypothesis h. -/
theorem k6_exchange_pinW :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      Item.pinW :=
  exchangeAtS_of _ Said (exchangeAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w 341)

/-- **ALL THAT THE ROW AT 341 OWES, FROM THE FOUR ITEMS THAT THE SUB-PROTOCOL MAKES**: `ExchangeS`
at 341. CONDITIONAL: the hypothesis h; hB: `BehindS` at 341; hKp'; AND FOUR NAMED PREMISES, one for
each item that is not paid in this file: its share of `ExchangeS`. By `exchangeS_iff`
(Honest/Thread/SharesS.lean) and the list `owes_341`. -/
theorem k6_exchangeS_of_four
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s')
    (hOwn : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "own"))
    (hPlanes : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 3 "planes"))
    (hJoin : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "join"))
    (hWeights : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "weights")) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  rw [owes_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hOwn
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hPlanes
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hJoin
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hWeights
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB hKp'
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_small h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB
  cases hi

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.keeps_st
#print axioms ProofFile.Honest.K6.k6_pin_rides
#print axioms ProofFile.Honest.K6.k6_ridesPast_pin
#print axioms ProofFile.Honest.K6.ridesPast_small
#print axioms ProofFile.Honest.K6.opened_341
#print axioms ProofFile.Honest.K6.owes_341
#print axioms ProofFile.Honest.K6.k6_exchange_pin
#print axioms ProofFile.Honest.K6.k6_exchange_small
#print axioms ProofFile.Honest.K6.k6_exchange_pinW
#print axioms ProofFile.Honest.K6.k6_exchangeS_of_four
