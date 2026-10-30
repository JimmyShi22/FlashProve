-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05ReadMsgs.lean: kind K5: THE MEMBERS OF THE CALLER's LIST IN WHICH A READ
ADDRESS HAS ITS SEAT, AS A LIST WITH CODE, OFF PUBLIC DATA: so that the two premises hcov and hcovM
of addrTie_at (Johnson/Desc/First/Att/K05AddrTieAt.lean) and of what stands on it are paid outright,
at lists of pairs that are made here.

Why. seatsOnB and shapesOnB (Johnson/Desc/First/Att/K05DoorB.lean) test the members that their lists
of pairs name, and no other: their weight lies in "the pairs name every member that is read".

Main names:
  `msgOfArray D i t`: the member that holds array number t of link i's list: seatCalls' own number,
    which does not hang on the cell. `seat_msg`: so it is.
  `readMsgs D x tl`: the members of the symbol arrays of the list's matrices, then the member that
    holds the mask row. `readMsg_in`: **every member in which an address of ReadAddr tl fs has its
    seat is in that list**, whatever fs.
  `psOf l seat ks`, `qsOf l ks`: the pairs (number, seat) and (number, shape) at the numbers ks.
  `hcov_of`, `hcovM_of`: **hcov and hcovM at ps := psOf … (readMsgs D x tl), qs := qsOf … (readMsgs
    D x tl).**
Limits. That a symbol array HAS a member (msgOfArray answers) is not said here: where it does not,
no address of it has a seat.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieOf
import Johnson.Desc.First.Att.K05MasksAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt bornAt messagesAt szOf)

/-- The member that holds array number t of link i's list. -/
def msgOfArray (D : Sent) (i t : ℕ) : Option ℕ :=
  ((D.arrayOf.getD i #[])[t]?).bind fun bn =>
    (OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
      if bn.1 == i then some ((keptAt D i).length + a.message)
      else (bornAt D i).idxOf? (bn.1, a.message)

/-- seatCalls' number of the member does not hang on the cell. -/
theorem seat_msg {D : Sent} {i t r c : ℕ} {z : VerifiableInference.Desc.First.Look.Seat}
    (hz : seatCalls D i (.cell t r c) = some z) : msgOfArray D i t = some z.msg := by
  unfold seatCalls at hz
  obtain ⟨bn, hbn, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨rp, _, hz⟩ := Option.bind_eq_some_iff.1 hz
  unfold msgOfArray
  rw [hbn]
  show ((OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
      if bn.1 == i then some ((keptAt D i).length + a.message)
      else (bornAt D i).idxOf? (bn.1, a.message)) = _
  rw [ha]
  show (if bn.1 == i then some ((keptAt D i).length + a.message)
      else (bornAt D i).idxOf? (bn.1, a.message)) = _
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hz ⊢
    obtain rfl := Option.some.inj hz
    rfl
  · rw [if_neg hb] at hz ⊢
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hz
    exact hk

/-- The members that are read. -/
def readMsgs (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) : List ℕ :=
  ((List.range (szOf tl).NM).filterMap fun μ => msgOfArray D x.link (tl.gtTree.getD μ 0)) ++
    (maskMsg D x.link).toList

/-- **Every member in which a read address has its seat is in the list.** -/
theorem readMsg_in {D : Sent} {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    {fs : List Aff} {k : ℕ} (h : ReadMsg (ReadAddr tl fs) D x.link k) : k ∈ readMsgs D x tl := by
  obtain ⟨a, z, ha, hz, rfl⟩ := h
  unfold readMsgs
  rcases ha with ⟨μ, i', c, rfl⟩ | ⟨f, _, y, _, rfl⟩
  · exact List.mem_append_left _
      (List.mem_filterMap.2 ⟨μ.val, List.mem_range.2 μ.2, seat_msg hz⟩)
  · refine List.mem_append_right _ ?_
    have hm : maskMsg D x.link = some z.msg := by
      unfold seatCalls at hz
      obtain ⟨mi, h1, rfl⟩ := Option.map_eq_some_iff.1 hz
      unfold maskMsg
      rw [h1]
      rfl
    rw [hm]
    exact List.mem_singleton.2 rfl

/-- The pairs (number, seat) at the numbers ks. -/
def psOf (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (ks : List ℕ) :
    List (ℕ × (ℕ × ℕ)) :=
  ks.filterMap fun k => if h : k < l.length then some (k, seat ⟨k, h⟩) else none

/-- The pairs (number, shape) at the numbers ks. -/
def qsOf (l : List (OracleShape × ℕ)) (ks : List ℕ) : List (ℕ × OracleShape) :=
  ks.filterMap fun k => (l[k]?).map fun o => (k, o.1)

theorem ps_mem (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {ks : List ℕ}
    (k : Fin l.length) (h : k.val ∈ ks) : (k.val, seat k) ∈ psOf l seat ks :=
  List.mem_filterMap.2 ⟨k.val, h, by rw [dif_pos k.2]⟩

theorem qs_mem (l : List (OracleShape × ℕ)) {ks : List ℕ} (k : Fin l.length) (h : k.val ∈ ks) :
    (k.val, (l.get k).1) ∈ qsOf l ks :=
  List.mem_filterMap.2 ⟨k.val, h, by rw [List.getElem?_eq_getElem k.2]; rfl⟩

/-- **hcov, paid.** -/
theorem hcov_of (D : Sent) (rad : OracleShape → Nat) (x : VerifiableInference.Desc.First.Look.Place)
    (tl : HTailF2) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (fs : List Aff)
    (k : Fin (sigListCalls D rad x.link).length) (h : ReadMsg (ReadAddr tl fs) D x.link k.val) :
    (k.val, seat k) ∈ psOf (sigListCalls D rad x.link) seat (readMsgs D x tl) ∧
      (k.val, ((sigListCalls D rad x.link).get k).1) ∈
        qsOf (sigListCalls D rad x.link) (readMsgs D x tl) :=
  ⟨ps_mem _ seat k (readMsg_in h), qs_mem _ k (readMsg_in h)⟩

/-- **hcovM, paid.** -/
theorem hcovM_of (D : Sent) (rad : OracleShape → Nat)
    (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (k : ℕ)
    (hk : k < (sigListCalls D rad x.link).length) (hm : maskMsg D x.link = some k) :
    (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈
      qsOf (sigListCalls D rad x.link) (readMsgs D x tl) :=
  qs_mem _ ⟨k, hk⟩ (by
    unfold readMsgs
    rw [hm]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seat_msg
#print axioms VerifiableInference.Desc.First.Att.P.readMsg_in
#print axioms VerifiableInference.Desc.First.Att.P.hcov_of
#print axioms VerifiableInference.Desc.First.Att.P.hcovM_of
