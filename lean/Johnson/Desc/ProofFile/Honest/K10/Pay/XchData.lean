-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchData.lean: the closing of a segment (K10): the clauses on data in the fields stand of
`TieByShared` and `TieBySwitch` (Pay/XchTieByShared.lean, Pay/XchTieBySwitch.lean), each brought down to public facts on
addresses, shapes and the count of challenges that a message's data read.

The closing's job takes a segment's own main rows by `ownBy` (Honest/K2/AtPlan.lean), at all the challenges that it has heard.
A sender took them when it sent, at the challenges heard then.

  `at_zero`        the one call of a filling at a message whose data read no challenge: the same at every list
  **`ownBy_job`**    against the shared sending: `ownBy` at a message with the address ad and the shape sh is the filling D' at ad, at
                 the first fr challenges, read as a row of its field takes it. D' : another filling that agrees with the job's at
                 ad (the shared kind's jobs take a filling of their own)
  **`ownBy_sender`** against a code switch's own messages of moment 0 (`senderOwn`, Honest/K2/Law/SenderOwn.lean)
  **`ownBy_front`**  against the code switch's closing, at a segment in front: `ownBy_prefix` (Pay/XchCongrPay.lean) at the challenges
                 heard, cut at fx

Limits. The facts on addresses, shapes and counts are premises.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchCongrPay
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (SwitchPlace ownBy asRow)
open ProofFile.Honest.K2.Law (senderOwn)

/-- At a message whose data read no challenge the call returns the same at every list. -/
theorem at_zero (D : RowData) (R : Readers) (hd hd' : List Fmt.Drawn) (a : MsgAddr) (h : D.heardAt a = 0) (r j : Nat) :
    D.at_ R hd a r j = D.at_ R hd' a r j := by
  unfold RowData.at_
  rw [h, List.take_zero, List.take_zero]

/-- **Against the shared sending.** -/
theorem ownBy_job (D D' : RowData) (R : Readers) (addrs : Nat → Nat → Option MsgAddr)
    (shapes : Nat → Nat → OnBytes.OracleShape) (front : List Fmt.Drawn) (fr seg m : Nat) {ad : MsgAddr}
    {sh : OnBytes.OracleShape} (ha : addrs seg m = some ad) (hs : shapes seg m = sh)
    (hD : ∀ hd r j, D.at_ R hd ad r j = D'.at_ R hd ad r j) (hle : D'.heardAt ad ≤ fr) (hfr : fr ≤ front.length) :
    ownBy D R addrs shapes front seg m = fun r j => asRow (sh.mainDeg == 3) (D'.at_ R (front.take fr) ad r j) := by
  funext r j
  unfold ownBy
  rw [ha]
  show asRow ((shapes seg m).mainDeg == 3) (D.at_ R front ad r j) = _
  have e0 : front = front.take fr ++ front.drop fr := (List.take_append_drop fr _).symm
  have hl : (front.take fr).length = fr := by rw [List.length_take]; omega
  rw [hs, hD]
  conv_lhs => rw [e0]
  rw [at_prefix D' R _ _ ad (by rw [hl]; exact hle)]

/-- **Against a code switch's own messages of moment 0.** -/
theorem ownBy_sender (D : RowData) (R : Readers) (addrs : Nat → Nat → Option MsgAddr)
    (shapes : Nat → Nat → OnBytes.OracleShape) (front : List Fmt.Drawn) (p : SwitchPlace) (seg m : Nat)
    (ha : addrs seg m = some (p.ownAddr m)) (hs : shapes seg m = (p.others.getD m default).shape)
    (h0 : D.heardAt (p.ownAddr m) = 0) :
    ownBy D R addrs shapes front seg m = senderOwn D R p m := by
  funext r j
  unfold ownBy
  rw [ha]
  show asRow ((shapes seg m).mainDeg == 3) (D.at_ R front (p.ownAddr m) r j) =
    asRow ((p.others.getD m default).shape.mainDeg == 3) (D.at_ R [] (p.ownAddr m) r j)
  rw [hs, at_zero D R front [] _ h0]

/-- **Against the code switch's closing, at a segment in front.** -/
theorem ownBy_front (D : RowData) (R : Readers) (addrs addrs' : Nat → Nat → Option MsgAddr)
    (shapes shapes' : Nat → Nat → OnBytes.OracleShape) (front : List Fmt.Drawn) (fx seg : Nat)
    (ha : addrs = addrs') (hs : shapes seg = shapes' seg)
    (hle : ∀ m a, addrs' seg m = some a → D.heardAt a ≤ fx) (hfx : fx ≤ front.length) :
    ownBy D R addrs shapes front seg = ownBy D R addrs' shapes' (front.take fx) seg := by
  subst ha
  have e0 : front = front.take fx ++ front.drop fx := (List.take_append_drop fx _).symm
  have hl : (front.take fx).length = fx := by rw [List.length_take]; omega
  conv_lhs => rw [e0]
  exact ownBy_prefix D R addrs shapes shapes' _ _ seg hs fun m a h => by rw [hl]; exact hle m a h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.at_zero
#print axioms ProofFile.Honest.K10.ownBy_job
#print axioms ProofFile.Honest.K10.ownBy_sender
#print axioms ProofFile.Honest.K10.ownBy_front
