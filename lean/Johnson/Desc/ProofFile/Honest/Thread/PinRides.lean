-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PinRides.lean: three open items of the first chain's invariant
that pass unchanged over any sub-protocol whose step leaves the statement as it was and sets no
failure mark. The items are `pin m t`, `pinI` and `unmarked` (`Item`,
Johnson/Desc/First/Borders.lean). The file holds five conditional lemmas, general in the
sub-protocol's number `b`, and no definition.

The condition `RidesPastAt T b i` (Honest/Thread/Shares.lean) says: what the open item `i` states
before sub-protocol `b` it states after it, at every state that `keeps b` allows. For the invariant
of `lettersHead` a pin states that the verifier's statement holds a sample for certain messages and
that the witness's messages have that sample's answers (`ansJT`, Honest/Thread/Ans.lean). Of the
verifier's state it reads the statement only (`ansJT_rows`). The item `unmarked` states that the
state has no failure mark.

  1  `ridesPastAt_pin`, `ridesPastAt_pinI`   if `keeps b` leaves the statement as it was, the pins
     pass
  2  `ridesPastAt_unmarked`   if `keeps b` includes "no failure mark after the step", `unmarked`
     passes
  3  `exchangeAtS_pin`, `exchangeAtS_pinI`   a pin that the sub-protocol's row has to show again
     after the step: from `BehindS` and lemma 1, by `exchangeAtS_again` (Honest/Thread/SharesS.lean)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the format's second hash function.
  * The two hypotheses on `keeps b` have to be shown for each kind from its own condition. This file
    shows them for no kind.
  * Nothing here shows that a pin holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pin m t` passes over sub-protocol `b` if `keeps b` leaves the statement as it was. -/
theorem ridesPastAt_pin {b : Nat} (m t : Nat)
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.pin m t) := by
  intro k s mm E s' ps v _ hK h0 z hz
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => by rw [hst s s' hK]) (h0 z hz)

/-- The item `pinI` passes over sub-protocol `b` if `keeps b` leaves the statement as it was. -/
theorem ridesPastAt_pinI {b : Nat}
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI := by
  intro k s mm E s' ps v _ hK h0
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => by rw [hst s s' hK]) h0

/-- The item `unmarked` passes over sub-protocol `b` if `keeps b` includes "no failure mark after
the step". -/
theorem ridesPastAt_unmarked {b : Nat}
    (hm : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.failed = none) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      Item.unmarked :=
  fun _ s _ _ s' _ _ _ hK _ => hm s s' hK

/-- The item `pin m t`, where the row of sub-protocol `b` has to show it again after the step. -/
theorem exchangeAtS_pin {b : Nat} (m t : Nat)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st)
    (hi : Item.pin m t ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b
      (Item.pin m t) :=
  exchangeAtS_again _ _ hi hB
    (ridesPastAtS_of _ _ (ridesPastAt_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t hst))

/-- The item `pinI`, where the row of sub-protocol `b` has to show it again after the step. -/
theorem exchangeAtS_pinI {b : Nat}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st)
    (hi : Item.pinI ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b Item.pinI :=
  exchangeAtS_again _ _ hi hB
    (ridesPastAtS_of _ _ (ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pin
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinI
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_unmarked
#print axioms ProofFile.Honest.FirstThread.exchangeAtS_pin
#print axioms ProofFile.Honest.FirstThread.exchangeAtS_pinI
