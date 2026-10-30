-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real plan is shown at which the premise on the plan holds.
Johnson/Desc/First/Look/K3CopiesOne.lean: THE COPIES' LAW AT THE WITNESS: ONE WITNESS, TWO SEATS,
ONE NUMBER. The meaning's row asks the lookups' four clauses at lists behind a FAMILY of readings
msgF, under two premises of which either is free and both are not (by reading alone): SymsAre
(Johnson/Goal/Meaning/ReadingsOneLook.lean: the family's member k has the symbols of link k's tuple)
and ReadsOne (Johnson/Goal/Meaning/HidFamily.lean: a borrower's reading and the owner's agree).
Here: at the family that reads ALL sub-proofs in the witness's messages by number (there ReadsOne is
free: reads_one_reading, Johnson/Goal/Meaning/ReadsOneReading.lean), SymsAre HOLDS AT THE WITNESS's
OWN TUPLE msgsOf (Johnson/Desc/Sound/MsgSig.lean), under the public test linkTieB and ONE premise on
the plan. Statements and proofs: an unfolding. No error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two readings of one witness.
USER: K3CopiesRead.lean (symsAre_witness, OneNumber); 18 more files name OneNumber.
LETTERS: X, D, rad, num, idx, tls, k as in ReadingsOneLook.lean; seatT, arr as in the lookups' laws;
  wn: which of the witness's messages bears a number of num's.

Why it is no law on committed words. The witness has ONE component for all copies of a message
outside the pads' places (Wit.msg; Wit.tab): a member's typed message reads w.msg (arr j t) at its
seat (j, t). So a kept copy at the borrower and the original at the owner read one table wherever
arr gives one number at the two seats. That the two seats' committed WORDS decode to one message is
the pins' and the promise's: not spent, not shown.

Main names:
  `msgAllOf wn w`: the witness's messages as one reading by numbers.
  `readAt_msgsOf`: what the witness's tuple holds at a seat of a main row that lies in its table:
    Wit.tab at the member's shape, number and seat.
  `OneNumber`: THE PREMISE ON THE PLAN: at every symbol of link k's matrices, within the sizes: the
    place is no pad's place at the member's shape, and arr at the member's seat is wn of the number.
  `symsAre_witness`: THE END: SymsAre at (fun _ => msgAllOf wn w) and msgsOf ... seatT arr w.
  `symsAre_att`, `symsAre_lay`: the same at attMs and at the own part of layMs: hm to the letter.

Limits. OneNumber is shown at no plan: it is a test on public data (the plan's seats, arr, the
layout): it can be evaluated. Main rows alone: the symbols lie in main rows.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Goal.Meaning.ReadingsOneLook
import Johnson.Desc.First.Look.K3AttGoodIn
import Johnson.Desc.First.Look.K3LayGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Wit padB)
open VerifiableInference.Desc.Sound (MsgT msgsOf)
open VerifiableInference.Desc.First.Look (Sent Seat sigListCalls szOf readAt finOf_some ownPart)
open _root_.Meaning (Msgs SymsAre linkTieB fLay labAt msgsOfTuple seat_of_tie)

section
variable {Cells Tok : Type}

/-- The witness's messages as one reading by numbers. -/
def msgAllOf (wn : ℕ → ℕ) (w : Wit Cells Tok MsgT) : Msgs := fun n mask r p => w.msg (wn n) mask r p

/-- **What the witness's tuple holds at a seat of a main row.** -/
theorem readAt_msgsOf (cs : Codes) (l : List (OracleShape × ℕ)) (seatT : Fin l.length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (s : Seat) (hm : s.mask = false)
    (h : s.Fits cs l) :
    ∃ hk : s.msg < l.length, readAt cs l (msgsOf cs l seatT arr w) s =
      some (w.tab cs (l.get ⟨s.msg, hk⟩).1 (arr (seatT ⟨s.msg, hk⟩).1 (seatT ⟨s.msg, hk⟩).2)
        (seatT ⟨s.msg, hk⟩).1 (seatT ⟨s.msg, hk⟩).2 false s.row s.place) := by
  obtain ⟨hk, h⟩ := h
  refine ⟨hk, ?_⟩
  have hne : ¬ s.mask = true := by
    rw [hm]
    exact Bool.false_ne_true
  rw [if_neg hne] at h
  unfold readAt
  rw [dif_pos hk, if_neg hne, finOf_some h.1, finOf_some h.2]
  rfl

variable (X : Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ)
  (tls : ℕ → HTailF2) (k : ℕ) (seatT : Fin (sigListCalls D rad k).length → ℕ × ℕ)
  (arr : ℕ → ℕ → ℕ) (wn : ℕ → ℕ)

/-- **The premise on the plan.** -/
def OneNumber : Prop :=
  ∀ μ i c : ℕ, μ < (szOf (tls k)).NM → i < Alg.symRows ((szOf (tls k)).m μ) →
    c < (szOf (tls k)).k μ →
    ∀ hk : idx (fLay D.layout num (labAt X k μ) i c).1 < (sigListCalls D rad k).length,
      padB D.codes ((sigListCalls D rad k).get ⟨idx (fLay D.layout num (labAt X k μ) i c).1, hk⟩).1
        false (fLay D.layout num (labAt X k μ) i c).2.1
        (fLay D.layout num (labAt X k μ) i c).2.2 = false ∧
      arr (seatT ⟨idx (fLay D.layout num (labAt X k μ) i c).1, hk⟩).1
        (seatT ⟨idx (fLay D.layout num (labAt X k μ) i c).1, hk⟩).2 =
        wn (fLay D.layout num (labAt X k μ) i c).1

variable {X D rad num idx tls k seatT arr wn}

/-- **THE FAMILY's MEMBER HAS THE SYMBOLS OF THE WITNESS's OWN TUPLE.** -/
theorem symsAre_witness (T : linkTieB X D rad num idx k (tls k) = true)
    (O : OneNumber X D rad num idx tls k seatT arr wn) (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun _ => msgAllOf wn w) k
      (msgsOf D.codes (sigListCalls D rad k) seatT arr w) := by
  unfold SymsAre
  funext μ i' c
  obtain ⟨hk, e⟩ := readAt_msgsOf D.codes (sigListCalls D rad k) seatT arr w
    ⟨idx (fLay D.layout num (labAt X k μ.val) i'.val c.val).1, false,
      (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.1,
      (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.2⟩ rfl
    (seat_of_tie T μ.isLt i'.isLt c.isLt).2
  obtain ⟨o1, o2⟩ := O μ.val i'.val c.val μ.isLt i'.isLt c.isLt hk
  show msgAllOf wn w (fLay D.layout num (labAt X k μ.val) i'.val c.val).1 false
      (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.1
      (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.2 =
    (readAt D.codes (sigListCalls D rad k) (msgsOf D.codes (sigListCalls D rad k) seatT arr w)
      ⟨idx (fLay D.layout num (labAt X k μ.val) i'.val c.val).1, false,
        (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.1,
        (fLay D.layout num (labAt X k μ.val) i'.val c.val).2.2⟩).getD 0
  rw [e, Option.getD_some]
  unfold Wit.tab msgAllOf
  rw [if_neg (by rw [o1]; exact Bool.false_ne_true), o2]

end

section
variable {Cells Tok : Type} {X : Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
  {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {tls : ℕ → HTailF2} {x : Desc.First.Look.Place}
  {seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ} {arr : ℕ → ℕ → ℕ} {wn : ℕ → ℕ}

/-- **hm at an attention link**: at the tuple of which AttFront speaks. -/
theorem symsAre_att (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O : OneNumber X D rad num idx tls x.link seatT arr wn) (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun _ => msgAllOf wn w) x.link (attMs x D rad seatT arr w) :=
  symsAre_witness T O w

/-- **hm at a layers' link**: at the own part of the tuple of which LayFront speaks. -/
theorem symsAre_lay {oW : Cb.OMsg Cb.Gl.E} (msgW : Wit Cells Tok MsgT → oW.Msg)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O : OneNumber X D rad num idx tls x.link seatT arr wn) (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun _ => msgAllOf wn w) x.link
      (ownPart (layMs x D rad oW seatT arr msgW w)) :=
  symsAre_witness T O w

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.readAt_msgsOf
#print axioms VerifiableInference.OnPublicFiles.symsAre_witness
#print axioms VerifiableInference.OnPublicFiles.symsAre_att
#print axioms VerifiableInference.OnPublicFiles.symsAre_lay
