-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/MaskInOrderOfTaking.lean: THE SHARED SENDING (the kind K1) LAYS ITS MASK COINS IN THE ORDER IN WHICH A LEDGER
HANDS THE MASK ENTRIES OUT. General in the place; then against the count of the key file's book.

  1  word_at_taken   the mask table's entry at the number that a ledger hands out at take ν (OnBytes.takenNo) is the
     entry of mask row ν % m at place ν / m
  2  takenRowE, senderLaysOwn_taken   THE SENDER's AUTHORS' SENTENCE (SenderLaysOwn, Honest/Law/Rule/TiesOwn.lean) at the
     ledger's numbers: at take ν stands the part's own coin number maskStart + ν: for a message whose table
     does not ride, at every take below the mask rows' entries
  3  mainE_held, table_held   AGAINST THE BOOK's MAKER's COUNT: where the book's sending is made of the place's codes
     and notices, the book's "first coin of the mask table of message j" (AtPublicFiles.KeyBook.tableAt) IS maskStart
  4  senderLays_taken   the frame's form SenderLays at a book whose count at the sender's address is the part's

By: sender_own, sender_in (Honest/K1/SenderOwn.lean) · taken_row_place (Johnson/Road/K4/Rec/MaskEntry.lean) ·
starts_held, sending_at (E2E/KeyBookHeld.lean) · startR_congr (E2E/KeyBookHeldK1.lean) · senderLays_of_own
(Honest/Law/Rule/TiesOwn.lean).

It closes two of SenderOwn.lean's own limits: "that a ledger's slot number in the verifier's statement is the format's
number is not said" (1) and "nothing holds maskStart against the book's maker's count" (3).

Limits. What is WRITTEN where: no sentence on what a mask row or a coin is for. It speaks of the rows that the SENDER
lays (maskWordE): that the entry which a spender reads (the witness's word, or a Script's message at its mask rows) is
that entry is a further tie, owed by whoever spends it. At messages where no table rides alone. The mask does not read the data. Coins of the extension field alone. This file proves nothing about
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.SenderOwn
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOwn
import Johnson.Road.K4.Rec.MaskEntry
import Johnson.Prover.Send.Held
import E2E.KeyBookHeldK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt Rows)
open AtPublicFiles.KeyBook (MsgCoins Fill msgCoins sendingOf fillOf tableAt startAt ridesOf starts_held
  sending_at startR_congr)
open AtPublicFiles.RowCode (RowsDue mainDue maskDue)

/-! ## 1 The ledger's number -/

/-- **The mask table's entry at the number of take ν is the entry of row ν % m at place ν / m.** -/
theorem word_at_taken (R : Rows) (s : OracleShape) (hm : 0 < s.maskRows) (ν : Nat) :
    R.word s .mask (takenNo s.maskRows ν) = R.mask (ν % s.maskRows) (ν / s.maskRows) := by
  obtain ⟨e1, e2⟩ := OnBytes.Road.K4.Rec.taken_row_place hm ν
  show (if takenNo s.maskRows ν % 2 ^ Fmt.Places.logUp s.maskRows < s.maskRows then
    R.mask (takenNo s.maskRows ν % 2 ^ Fmt.Places.logUp s.maskRows)
      (takenNo s.maskRows ν / 2 ^ Fmt.Places.logUp s.maskRows) else 0) = _
  rw [e1, e2, if_pos (Nat.mod_lt _ hm)]

/-! ## 2 The sender's authors' sentence at the ledger's numbers -/

/-- The mask table's entry at a number i of the table, as rowsR lays it of the part's own coins, in the program's
elements. -/
def maskWordE (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
    (k : Nat) (cs : Cs (dueR P ride)) (i : Nat) : E :=
  E.ofTriple (ofE ((rowsR P ride data cs k).word (shapeAt P k) .mask i))

/-- **AT TAKE ν STANDS THE PART's OWN COIN NUMBER maskStart + ν.** -/
theorem senderLaysOwn_taken (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (k : Nat) (hk : k < P.sent.size)
    (hr : ride k = none) :
    SenderLaysOwn (fun cs ν => maskWordE P ride data k cs (takenNo (shapeAt P k).maskRows ν))
      (maskStart P ride k)
      (· < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell) := by
  intro cs ν hν
  have hm : 0 < (shapeAt P k).maskRows := by
    rcases Nat.eq_zero_or_pos (shapeAt P k).maskRows with h0 | h0
    · have hν' := hν
      simp only [h0, Nat.zero_mul] at hν'
      exact absurd hν' (Nat.not_lt_zero _)
    · exact h0
  rw [← sender_own P ride data k hk hr cs ν hν]
  show maskWordE P ride data k cs (takenNo (shapeAt P k).maskRows ν) = maskRowE P ride data k cs ν
  unfold maskWordE maskRowE
  rw [word_at_taken _ _ hm]

/-! ## 3 Against the book's maker's count -/

/-- Where msgCoins returns a count, its field mainE is the sender's count of the main rows' coins over the
extension field. -/
theorem mainE_held (codes : Codes) (n : OracleNotice) (fill : Fill) (m : MsgCoins)
    (h : msgCoins codes n fill = some m) (r : Option Ride) :
    m.mainE = if n.shape.mainDeg == 3 then (stepsOf codes n.shape r).main else 0 := by
  unfold msgCoins at h
  split at h
  · rename_i a b ha hb
    obtain rfl := Option.some.inj h
    have hA : (a.map RowsDue.tails).sum =
          n.shape.mainRows * (codes.base.getD n.shape.code default).r ∧
        (a.map fun d => d.rows * d.code.ell).sum =
          n.shape.mainRows * (codes.base.getD n.shape.code default).ell := by
      unfold mainDue at ha
      split at ha
      · rename_i h0
        obtain rfl := Option.some.inj ha
        simp [h0]
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ha
        have : codes.base.getD n.shape.code default = c := by
          unfold AtPublicFiles.RowCode.mainOf at hc
          rw [Array.getD_eq_getD_getElem?, hc]
          rfl
        simp [RowsDue.tails, this]
    have hp : (if n.shape.maskRows == 0 then
          (if n.shape.mainDeg == 3 then 1 else 3) * n.shape.answers
        else 0) = (if n.shape.maskRows == 0 && n.shape.answers != 0 then
          (if n.shape.mainDeg == 3 then 1 else 3) * n.shape.answers else 0) := by
      by_cases h1 : n.shape.maskRows = 0 <;> by_cases h2 : n.shape.answers = 0 <;> simp [h1, h2]
    simp only [stepsOf, Steps.main, hA.1, hA.2, hp]
  · cases h

/-- **THE BOOK's "FIRST COIN OF THE MASK TABLE OF MESSAGE j" IS THE SENDER's maskStart.** hl: the book's sending is made
of the place's codes and notices. hr: at each message in front the job's ride and the book's are both none or
have one count. -/
theorem table_held (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (l : AtPublicFiles.KeyBook.Sending)
    (hl : sendingOf P.codes k P.sent.toList = some l) (j : Nat) (hj : j < P.sent.size)
    (hr : ∀ i, i < j → (ride i).map (·.count) = (ridesOf P k i).map (·.count)) :
    tableAt l j = maskStart P ride j := by
  have hj' : j < P.sent.toList.length := by simpa using hj
  obtain ⟨m, e1, e2⟩ := (sending_at P.codes k _ l hl).2 j hj'
  have hn : P.sent.toList[j] = P.sent.getD j default := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj')]
    simp
  unfold tableAt maskStart
  rw [starts_held P k l hl j (Nat.le_of_lt hj), ← startR_congr P ride (ridesOf P k) j hr,
    List.getD_eq_getElem?_getD, e1, Option.getD_some,
    mainE_held P.codes _ _ m e2 (ride j), hn]
  rfl

/-! ## 4 The frame's form -/

/-- **THE FRAME's FORM**, at a book whose count at the sender's address is the part's own: at take ν of the ledger
of message number k the sent message's mask table holds the sender's coin number maskStart + ν. own: the part's
own coins, of a run's. -/
theorem senderLays_taken {Bk : ProverCoinCounts} {W : Type} (ch : Nat) (o : Addr) (P : K1.Par)
    (ride : Nat → Option Ride) (data : W → List Fmt.Drawn → Nat → Nat → Nat → Option (GF ⊕ GE))
    (k : Nat) (hk : k < P.sent.size) (hr : ride k = none) (own : Coins Bk → Cs (dueR P ride))
    (ho : OwnIs Bk ch o (dueR P ride) own) (takes : Nat)
    (ht : takes ≤ (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    SenderLays (W := W) Bk ch o (maskStart P ride k)
      (fun c w h ν => maskWordE P ride (data w h) k (own c) (takenNo (shapeAt P k).maskRows ν))
      (· < takes) := by
  intro c w h ν hν
  have hν' : ν < (shapeAt P k).maskRows *
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell := Nat.lt_of_lt_of_le hν ht
  exact senderLays_of_own (W := W) (senderLaysOwn_taken P ride (data w h) k hk hr) ho
    (fun ν hν => sender_in P ride k hk hr ν hν) c w h ν hν'

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.word_at_taken
#print axioms ProofFile.Honest.K1.senderLaysOwn_taken
#print axioms ProofFile.Honest.K1.mainE_held
#print axioms ProofFile.Honest.K1.table_held
#print axioms ProofFile.Honest.K1.senderLays_taken
