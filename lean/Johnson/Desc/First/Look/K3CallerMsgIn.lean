--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3CallerMsgIn.lean: ONE NUMBER IN A LINK's LIST OF ORACLE MESSAGES, ONE
MESSAGE: msgIn (Johnson/Desc/First/Look/K3CallerAttReads.lean: in which message of the signature's
list an array's message stands) is one to one; and what a seat of seatCalls
(Johnson/Desc/First/Look/K3CallerAtt.lean) is made of, written out. Statements and proofs, on public
data alone. NO SOUNDNESS AND NO ACCEPTANCE IS CLAIMED.

Why. "No two symbols share a seat" (the clause apart of SymsSit,
Johnson/Desc/First/Att/K05MsgOnto.lean) is asked by whoever wants a tuple of messages with
prescribed cells. A seat is a message's number, a row and a place. This file has the number.

Main names.
  idxOf_get   what Array.idxOf? finds lies in the array, at the index found.
  msgIn_inj   msgIn D k b m = some n and msgIn D k b' m' = some n give b = b' and m = m'. Three
    cases: both messages are link k's own (behind the kept ones: the kept ones' number cancels);
    both are kept (the list "born" holds one pair at one index); one of each: a kept one's number is
    below the length of "born", an own one's is at least the number of the kept ones, and the two
    lengths are one (kept_born, Johnson/Desc/First/Att/K05KeptBorn.lean).
  seatCalls_parts   a cell's seat: the list names an array; the layout has it; a block holds the
    element; the seat's message is msgIn of the array's link and message; its row and place are the
    block's. The converse of OnBytes.Road.K4.Rec.seatCalls_cell (Johnson/Road/K4/Rec/Arrays.lean).

Limits. Nothing on rows and places (Johnson/Desc/First/Look/K3CallerLaidApart.lean). Nothing on mask
entries' seats. That "born" holds no pair twice is neither said nor needed.
Not claimed: anything on completeness.

-/
import Johnson.Desc.First.Look.K3CallerAttReads
import Johnson.Desc.First.Att.K05KeptBorn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

/-- What idxOf? finds lies in the array, at the index found. -/
theorem idxOf_get {α : Type} [BEq α] [LawfulBEq α] {xs : Array α} {a : α} {i : ℕ}
    (h : xs.idxOf? a = some i) : i < xs.size ∧ xs[i]? = some a := by
  obtain ⟨l⟩ := xs
  rw [List.idxOf?_toArray] at h
  obtain ⟨hl, e, -⟩ := List.idxOf?_eq_some_iff.1 h
  refine ⟨by simpa using hl, ?_⟩
  rw [List.getElem?_toArray, List.getElem?_eq_getElem hl, e]

/-- **One number in link k's list, one (link, message).** -/
theorem msgIn_inj {D : Sent} {k b b' m m' n : ℕ} (h : msgIn D k b m = some n)
    (h' : msgIn D k b' m' = some n) : b = b' ∧ m = m' := by
  have kb := VerifiableInference.Desc.First.Att.P.kept_born D k
  unfold msgIn at h h'
  by_cases e : (b == k) = true
  · rw [if_pos e] at h
    have h1 := Option.some.inj h
    by_cases e' : (b' == k) = true
    · rw [if_pos e'] at h'
      have h2 := Option.some.inj h'
      exact ⟨(beq_iff_eq.1 e).trans (beq_iff_eq.1 e').symm, by omega⟩
    · rw [if_neg e'] at h'
      have lt := (idxOf_get h').1
      omega
  · rw [if_neg e] at h
    by_cases e' : (b' == k) = true
    · rw [if_pos e'] at h'
      have h2 := Option.some.inj h'
      have lt := (idxOf_get h).1
      omega
    · rw [if_neg e'] at h'
      have p : (b, m) = (b', m') :=
        Option.some.inj ((idxOf_get h).2.symm.trans (idxOf_get h').2)
      exact ⟨congrArg Prod.fst p, congrArg Prod.snd p⟩

/-- **What a cell's seat is made of.** -/
theorem seatCalls_parts {D : Sent} {k t r c : ℕ} {s : Seat}
    (h : seatCalls D k (.cell t r c) = some s) :
    ∃ bn a rp, (D.arrayOf.getD k #[])[t]? = some bn ∧
      OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧ laidPlace a.blocks r c = some rp ∧
      msgIn D k bn.1 a.message = some s.msg ∧ s.mask = false ∧ s.row = rp.1 ∧
      s.place = rp.2 := by
  unfold seatCalls at h
  obtain ⟨bn, hbn, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨rp, hrp, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨bn, a, rp, hbn, ha, hrp, ?_⟩
  unfold msgIn
  by_cases hb : (bn.1 == k) = true
  · rw [if_pos hb] at h ⊢
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [if_neg hb] at h ⊢
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨hn, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.idxOf_get
#print axioms VerifiableInference.Desc.First.Look.msgIn_inj
#print axioms VerifiableInference.Desc.First.Look.seatCalls_parts
