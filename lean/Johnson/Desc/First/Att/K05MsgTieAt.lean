-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05MsgTieAt.lean: kind K5: THE JOINING: "the two readers of a message are
one" (OneReader, Johnson/Desc/First/Att/K05MsgTieOf.lean) AT THE WITNESS OF THE RULE OF COMPOSITION:
the tuple is the typed messages of a list's members (msgsOf, Johnson/Desc/Sound/MsgSig.lean), the
reader by seat is the table of joints' own (seatTab, Johnson/Desc/Sound/BordersFill.lean): by
seatTab_main and seatTab_mask (Johnson/Desc/Sound/SeatTabMsgs.lean), called as they
lie.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

Main names:
  `MemAt ms l seat k`: that file's two premises at member k: the table's list of members ms has a
    first member at k's seat, and it has k's shape.
  `oneReader_at`: OneReader Ks … (msgsOf cs l seat arr w) (seatTab cs arr ms w), from MemAt at the
    members Ks.
  `msgTie_at`: **MsgTie at the witness**: from MemAt at the members in which a read address has its
    seat, and SeatOk at these seats.
Limits. A rule over letters: cs, l, seat, arr, ms are whoever calls it's. MemAt is a fact on the
table's list of members: shown of no list.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieOf
import Johnson.Desc.Sound.SeatTabMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (Mem seatOf seatTab msgsOf seatTab_main seatTab_mask MsgT)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt)

/-- The two premises of seatTab_main and seatTab_mask at member k. -/
def MemAt (ms : List Mem) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (k : Fin l.length) : Prop :=
  ∃ y : Mem, (ms.find? fun y => Decidable.decide (seatOf y = seat k)) = some y ∧
    (y.1.l.get y.2).1 = (l.get k).1

section
variable {Cells Tok : Type}

/-- **The two readers are one, at the witness.** -/
theorem oneReader_at (Ks : ℕ → Prop) (cs : Codes) (arr : ℕ → ℕ → ℕ) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (ms : List Mem) (w : Wit Cells Tok MsgT)
    (h : ∀ k : Fin l.length, Ks k.val → MemAt ms l seat k) :
    OneReader Ks cs l seat (msgsOf cs l seat arr w) (seatTab cs arr ms w) := by
  refine ⟨fun k hk r c => ?_, fun k hk r c => ?_⟩
  · obtain ⟨y, hy, hsh⟩ := h k hk
    exact seatTab_main cs arr l seat ms w k y hy hsh (r, c)
  · obtain ⟨y, hy, hsh⟩ := h k hk
    exact seatTab_mask cs arr l seat ms w k y hy hsh (r, c)

/-- **The one tie on the witness, at the witness.** -/
theorem msgTieOf_at (Rd : Addr → Prop) (cs : Codes) (l : List (OracleShape × ℕ))
    (sf : Addr → Option VerifiableInference.Desc.First.Look.Seat) (kept : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (arr : ℕ → ℕ → ℕ)
    (seat : Fin l.length → ℕ × ℕ) (ms : List Mem) (w : Wit Cells Tok MsgT)
    (hm : ∀ k : Fin l.length, ReadMsgOf Rd sf k.val → MemAt ms l seat k)
    (hz : ∀ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a → sf a = some z →
      ∃ o, SeatOk cs l seat f kept own st book z o) :
    MsgTieOf Rd cs l sf kept f own st book (seatTab cs arr ms w) (msgsOf cs l seat arr w) :=
  msgTieOf_of Rd cs l sf kept f own st book _ _ seat (oneReader_at _ cs arr l seat ms w hm) hz

/-- The same at the list, the seats and the kept messages of link i's lookup on the calls. -/
theorem msgTie_at (Rd : Addr → Prop) (D : Sent) (rad : OracleShape → Nat) (i : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad i).length → ℕ × ℕ) (ms : List Mem) (w : Wit Cells Tok MsgT)
    (hm : ∀ k : Fin (sigListCalls D rad i).length, ReadMsg Rd D i k.val →
      MemAt ms (sigListCalls D rad i) seat k)
    (hz : ∀ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a →
      seatCalls D i a = some z →
      ∃ o, SeatOk D.codes (sigListCalls D rad i) seat f (keptAt D i).length own st book z o) :
    MsgTie Rd D rad i f own st book (seatTab D.codes arr ms w)
      (msgsOf D.codes (sigListCalls D rad i) seat arr w) :=
  msgTie_of Rd D rad i f own st book _ _ seat
    (oneReader_at _ D.codes arr _ seat ms w hm) hz

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.oneReader_at
#print axioms VerifiableInference.Desc.First.Att.P.msgTieOf_at
#print axioms VerifiableInference.Desc.First.Att.P.msgTie_at
