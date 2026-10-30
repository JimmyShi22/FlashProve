-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OneReaderClamp.lean: "THE TWO READERS OF A MESSAGE
ARE ONE" (`OneReader`, Johnson/Desc/First/Att/K05MsgTieOf.lean) AT THE LINK LAW's OWN READER OF THE
WITNESS `rdC` (ClampPin.lean beside this file). Theorems. A law file; no running text imports it.
  `oneReader_rdC`   at the members Ks of a list l with seats seat: where each such member has, in
the table's list of members ms, a member that sits at its seat and has its shape (MemAt): OneReader
Ks cs l seat (msgsOf cs l seat arr w) (rdC cs arr ms w). How: oneReader_at has it at
the reader seatTab; OneReader reads a reader at rows and places INSIDE the member's ranges alone;
there rdC is seatTab (rdC_inside).
  `leftAsks_ones`   so the two fields oneCells and oneMask of LeftAsks (LeftThree.lean) at rdW :=
                    rdC D.codes arr ms, from MemAt at the members that hold the read cells, and at
                    the mask row's.

Limits. MemAt IS A PREMISE ON THE TABLE's LIST OF MEMBERS AND THE PLAN's SEATS: shown of no list
here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.LeftThree
import Johnson.Desc.First.Link.Law.ClampPin
import Johnson.Desc.First.Att.K05MsgTieAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf MemAt oneReader_at)

section
variable {Cells Tok : Type}

/-- **The two readers are one, at the link law's own reader.** -/
theorem oneReader_rdC (Ks : ℕ → Prop) (cs : Codes) (arr : ℕ → ℕ → ℕ) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (ms : List Mem) (w : Desc.Wit Cells Tok MsgT)
    (h : ∀ k : Fin l.length, Ks k.val → MemAt ms l seat k) :
    OneReader Ks cs l seat (msgsOf cs l seat arr w) (rdC cs arr ms w) := by
  have O := oneReader_at Ks cs arr l seat ms w h
  refine ⟨fun k hk r c => ?_, fun k hk r c => ?_⟩
  · obtain ⟨y, hy, hsh⟩ := h k hk
    rw [O.main k hk r c]
    refine (rdC_inside cs arr ms w (seat k) y hy false r.val c.val ?_).symm
    rw [hsh]
    exact ⟨r.isLt, c.isLt⟩
  · obtain ⟨y, hy, hsh⟩ := h k hk
    rw [O.mask k hk r c]
    refine (rdC_inside cs arr ms w (seat k) y hy true r.val c.val ?_).symm
    rw [hsh]
    exact ⟨r.isLt, c.isLt⟩

/-- So the two fields oneCells and oneMask of `LeftAsks`, at the link law's own reader. -/
theorem leftAsks_ones (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (ms : List Mem) (w : Desc.Wit Cells Tok MsgT)
    (hc : ∀ k : Fin (digList x D rad).length,
      ReadMsgOf (cellAddr tlD) (seatOf D x.link) k.val → MemAt ms (digList x D rad) seatT k)
    (hm : ∀ k : Fin (digList x D rad).length,
      ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link) k.val →
        MemAt ms (digList x D rad) seatT k) :
    OneReader (ReadMsgOf (cellAddr tlD) (seatOf D x.link)) D.codes (digList x D rad) seatT
        (msgsOf D.codes (digList x D rad) seatT arr w) (rdC D.codes arr ms w) ∧
      OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link)) D.codes (digList x D rad)
        seatT (msgsOf D.codes (digList x D rad) seatT arr w) (rdC D.codes arr ms w) :=
  ⟨oneReader_rdC _ D.codes arr _ seatT ms w hc, oneReader_rdC _ D.codes arr _ seatT ms w hm⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.leftAsks_ones
#print axioms VerifiableInference.Desc.LinkJoin.oneReader_rdC
