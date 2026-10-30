-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05MsgTieOf.lean: kind K5: THE ONE TIE ON THE WITNESS (MsgTie,
Johnson/Desc/First/Att/K05AddrTieOf.lean) FROM "the two readers of a message are one" and facts on
the record: general in the tuple m, the witness's reader rd and the plan's letter seat.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

Main names:
  `OneReader Ks cs l seat m rd`: at every entry of a member k of the list l WITH Ks k, and of no
    other, the tuple m holds what rd gives at the seat of k: main rows and mask rows. `ReadMsg Rd D
    i`: the members in which an address of Rd has its seat. (At m := the typed messages of a witness
    and rd := the table's accessor by seat these are seatTab_main and seatTab_mask,
    Johnson/Desc/Sound/SeatTabMsgs.lean, under that file's two premises.)
  `SeatOk …  z`: FOUR FACTS AT A SEAT z: (fits) it lies in its message's table (Seat.Fits,
    Johnson/Desc/First/Look/K3CallerBase.lean: public) · (oracle) the live request has the oracle o
    of message number z.msg · (place) THE RECORD's BOOK PLACES o AT THE PLAN's SEAT OF THAT MESSAGE,
    AND THAT SEAT LIES IN own · (row) z.row is a row of o's table by the record's statement.
  `msgTie_of`: **MsgTie Rd …** from OneReader at ReadMsg Rd D i and SeatOk at every seat that
    seatCalls gives an address of Rd.
Limits. A rule over letters. (place) and (row) are sentences on the record: who says them at a
border of the table of joints is not settled here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AddrTieOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.Sound (GQ MsgQ tabQ)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt readAt jMain jMask finOf
  finOf_some)

/-- **The two readers of a message are one**, member by member: AT THE MEMBERS Ks, AND AT NO OTHER.
-/
structure OneReader (Ks : ℕ → Prop) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (m : (Johnson.Pack.sigOf cs l).Msg) (rd : ℕ × ℕ → MsgQ) :
    Prop where
  main : ∀ (k : Fin l.length), Ks k.val → ∀ (r : Fin (l.get k).1.mainRows)
    (c : Fin (Johnson.Pack.pMain cs (l.get k).1).ell),
    m k (jMain cs (l.get k).1 r c) = rd (seat k) false r.val c.val
  mask : ∀ (k : Fin l.length), Ks k.val → ∀ (r : Fin (l.get k).1.maskRows)
    (c : Fin (Johnson.Pack.pMask cs (l.get k).1).ell),
    m k (jMask cs (l.get k).1 r c) = rd (seat k) true r.val c.val

/-- The members in which an address of Rd has its seat. -/
def ReadMsgOf (Rd : Addr → Prop) (sf : Addr → Option VerifiableInference.Desc.First.Look.Seat)
    (k : ℕ) : Prop :=
  ∃ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a ∧ sf a = some z ∧ z.msg = k

/-- These at the seats of link i's lookup on the calls. -/
def ReadMsg (Rd : Addr → Prop) (D : Sent) (i k : ℕ) : Prop := ReadMsgOf Rd (seatCalls D i) k

/-- Four facts at a seat. -/
structure SeatOk (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (f : ReqFrame) (kept : ℕ) (own : List (ℕ × ℕ)) (st : OnBytes.Statement)
    (book : OnBytes.TreeBook) (z : VerifiableInference.Desc.First.Look.Seat) (o : ℕ) : Prop where
  fits : z.Fits cs l
  oracle : oracleOfMsg f kept z.msg = some o
  place : ∀ hk : z.msg < l.length, seatAt own book o = some (seat ⟨z.msg, hk⟩)
  row : z.row < 2 ^ st.rowBits o (tableOfSeat z)

/-- **The one tie on the witness, from "the two readers are one" and four facts a seat.** -/
theorem msgTieOf_of (Rd : Addr → Prop) (cs : Codes) (l : List (OracleShape × ℕ))
    (sf : Addr → Option VerifiableInference.Desc.First.Look.Seat) (kept : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd : ℕ × ℕ → MsgQ)
    (m : (Johnson.Pack.sigOf cs l).Msg) (seat : Fin l.length → ℕ × ℕ)
    (h1 : OneReader (ReadMsgOf Rd sf) cs l seat m rd)
    (hz : ∀ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a → sf a = some z →
      ∃ o, SeatOk cs l seat f kept own st book z o) :
    MsgTieOf Rd cs l sf kept f own st book rd m := by
  intro a z ha hs
  obtain ⟨o, K⟩ := hz a z ha hs
  refine ⟨o, K.oracle, ?_⟩
  obtain ⟨hk, hfit⟩ := K.fits
  obtain ⟨t1, t2⟩ := tableIndex_parts (st.rowBits o (tableOfSeat z)) (z.row, z.place) K.row
  unfold tabQ
  rw [K.place hk]
  show _ = rd (seat ⟨z.msg, hk⟩) (tableOfSeat z == .mask) _ _
  rw [t1, t2]
  unfold readAt
  rw [dif_pos hk]
  by_cases hm : z.mask = true
  · rw [if_pos hm] at hfit ⊢
    rw [finOf_some hfit.1, finOf_some hfit.2]
    have ht : tableOfSeat z = .mask := by
      unfold tableOfSeat
      rw [if_pos hm]
    rw [ht]
    exact h1.mask ⟨z.msg, hk⟩ ⟨a, z, ha, hs, rfl⟩ ⟨z.row, hfit.1⟩ ⟨z.place, hfit.2⟩
  · rw [if_neg hm] at hfit ⊢
    rw [finOf_some hfit.1, finOf_some hfit.2]
    have ht : tableOfSeat z = .main := by
      unfold tableOfSeat
      rw [if_neg hm]
    rw [ht]
    exact h1.main ⟨z.msg, hk⟩ ⟨a, z, ha, hs, rfl⟩ ⟨z.row, hfit.1⟩ ⟨z.place, hfit.2⟩

/-- The same at the list, the seats and the kept messages of link i's lookup on the calls. -/
theorem msgTie_of (Rd : Addr → Prop) (D : Sent) (rad : OracleShape → Nat) (i : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd : ℕ × ℕ → MsgQ)
    (m : (Johnson.Pack.sigOf D.codes (sigListCalls D rad i)).Msg)
    (seat : Fin (sigListCalls D rad i).length → ℕ × ℕ)
    (h1 : OneReader (ReadMsg Rd D i) D.codes (sigListCalls D rad i) seat m rd)
    (hz : ∀ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a →
      seatCalls D i a = some z →
      ∃ o, SeatOk D.codes (sigListCalls D rad i) seat f (keptAt D i).length own st book z o) :
    MsgTie Rd D rad i f own st book rd m :=
  msgTieOf_of Rd D.codes (sigListCalls D rad i) (seatCalls D i) (keptAt D i).length f own st book rd m
    seat h1 hz

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.msgTieOf_of
#print axioms VerifiableInference.Desc.First.Att.P.msgTie_of
