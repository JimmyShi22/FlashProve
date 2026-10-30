-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05DoorB.lean: kind K5: THREE BOOLS WITH CODE ON THE CARRIED RECORD, for
public items that come through the table of joints' door (Johnson/Desc/First/Borders.lean:
Pub.more): what the tie between the kind's law's tuple of messages and the witness's
tables (Johnson/Desc/First/Att/K05MsgTieOf.lean: SeatOk; Johnson/Desc/First/Att/K05SeatsOne.lean:
FrameIs) asks of the record. No Mathlib: so that a run can evaluate them at a walk's borders.

Main names:
  `oracleOfMsg f kept k`: message number k of a caller's list (the kept messages, then the link's
    own), as a number in the statement, by the live request f.
  `liveReqB born s`: OFFERED for an item "K5.liveReq": a link is open; its own copy of the live
    request stands at the link's number; a link is under way in it; its group's list "born" at that
    link is born (the plan's).
  `seatsAtB kept seats own s`: the law's letter for "the record's book places message number k of
    the open link's live request at the plan's seat number k, and that seat lies in own".
  `shapesAtB kept shapes s`: OFFERED: the statement's oracle of message number k has the plan's
    shape number k.
  `seatsOnB kept pairs own s`, `shapesOnB kept pairs s`: the last two AT THE MEMBERS THAT A LIST OF
    PAIRS (number, seat | shape) NAMES, AND AT NO OTHER: what the laws spend. `seatsOn_of_at`,
    `shapesOn_of_at`: a yes at the whole list gives them.
  `liveReqB_at`, `seatsAtB_at`, `shapesAtB_at`, `seatsOnB_at`, `shapesOnB_at`: what a yes gives.
  CONTROLS, THROUGH LEAN: `liveReqB_one`, `seatsAtB_one`, `shapesAtB_one`, `seatsOnB_one`,
  `shapesOnB_one`: two letters with a yes at one
    record agree (wherever both lists have an entry): so at a bent letter the Bool says no.
seatsAtB, shapesAtB, seatsOnB AND shapesOnB TEST EACH ENTRY THAT THE LETTER HAS, NOT THAT THE
LETTER IS WHOLE: at the empty list, or a list cut short, they say yes at every record with an open
link: a row of the door that is filled with a short list passes for nothing. (In
Johnson/Desc/First/Att/K05DoorLaws.lean the letters are whole by their make.)
Limits. None is evaluated at a record here. Who makes each true, and who keeps it, is not said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- Message number k of the caller's list, as a number in the statement. -/
def oracleOfMsg (f : ReqFrame) (kept k : Nat) : Option Nat :=
  if k < kept then f.keptBefore[k]? else f.own[k - kept]?

/-- OFFERED: the open link's own copy of the live request stands in that link. -/
def liveReqB (born : Array (Nat × Nat)) (s : First.S) : Bool :=
  s.link?.any fun L =>
    L.check.frame.link == L.link && L.check.frame.next == .laterOrClose &&
      (L.check.frame.groups.getD L.check.frame.link {}).born == born

/-- The book places the live request's messages at the plan's seats, which lie in own. -/
def seatsAtB (kept : Nat) (seats own : List (Nat × Nat)) (s : First.S) : Bool :=
  s.link?.any fun L =>
    seats.zipIdx.all fun x =>
      (oracleOfMsg L.check.frame kept x.2).any fun o =>
        s.book.place[o]? == some x.1 && own.contains x.1

/-- OFFERED: the statement's oracles of the live request's messages have the plan's shapes. -/
def shapesAtB (kept : Nat) (shapes : List OracleShape) (s : First.S) : Bool :=
  s.link?.any fun L =>
    shapes.zipIdx.all fun x =>
      (oracleOfMsg L.check.frame kept x.2).any fun o =>
        (s.st.oracles[o]?).any fun y => y.shape == x.1

/-- seatsAtB AT THE MEMBERS THAT A LIST OF PAIRS (number, seat) NAMES, AND AT NO OTHER. -/
def seatsOnB (kept : Nat) (pairs : List (Nat × (Nat × Nat))) (own : List (Nat × Nat))
    (s : First.S) : Bool :=
  s.link?.any fun L =>
    pairs.all fun x =>
      (oracleOfMsg L.check.frame kept x.1).any fun o =>
        s.book.place[o]? == some x.2 && own.contains x.2

/-- shapesAtB at the members that a list of pairs (number, shape) names, and at no other. -/
def shapesOnB (kept : Nat) (pairs : List (Nat × OracleShape)) (s : First.S) : Bool :=
  s.link?.any fun L =>
    pairs.all fun x =>
      (oracleOfMsg L.check.frame kept x.1).any fun o =>
        (s.st.oracles[o]?).any fun y => y.shape == x.2

section
variable {s : First.S} {L : LinkCtx}

theorem liveReqB_at {born : Array (Nat × Nat)} (h : liveReqB born s = true) (hL : s.link? = some L) :
    L.check.frame.link = L.link ∧ L.check.frame.next = .laterOrClose ∧
      (L.check.frame.groups.getD L.check.frame.link {}).born = born := by
  unfold liveReqB at h
  rw [hL] at h
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem seatsAtB_at {kept : Nat} {seats own : List (Nat × Nat)} (h : seatsAtB kept seats own s = true)
    (hL : s.link? = some L) {k : Nat} {x : Nat × Nat} (hx : seats[k]? = some x) :
    ∃ o, oracleOfMsg L.check.frame kept k = some o ∧ s.book.place[o]? = some x ∧
      own.contains x = true := by
  unfold seatsAtB at h
  rw [hL] at h
  simp only [Option.any_some] at h
  have h1 := List.all_eq_true.1 h (x, k) (List.mem_zipIdx_iff_getElem?.2 hx)
  cases ho : oracleOfMsg L.check.frame kept k with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨o, rfl, h1.1, h1.2⟩

theorem shapesAtB_at {kept : Nat} {shapes : List OracleShape} (h : shapesAtB kept shapes s = true)
    (hL : s.link? = some L) {k : Nat} {x : OracleShape} (hx : shapes[k]? = some x) :
    ∃ o y, oracleOfMsg L.check.frame kept k = some o ∧ s.st.oracles[o]? = some y ∧ y.shape = x := by
  unfold shapesAtB at h
  rw [hL] at h
  simp only [Option.any_some] at h
  have h1 := List.all_eq_true.1 h (x, k) (List.mem_zipIdx_iff_getElem?.2 hx)
  cases ho : oracleOfMsg L.check.frame kept k with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some] at h1
    cases hy : s.st.oracles[o]? with
    | none =>
      rw [hy] at h1
      cases h1
    | some y =>
      rw [hy] at h1
      simp only [Option.any_some, beq_iff_eq] at h1
      exact ⟨o, y, rfl, hy, h1⟩

theorem seatsOnB_at {kept : Nat} {pairs : List (Nat × (Nat × Nat))} {own : List (Nat × Nat)}
    (h : seatsOnB kept pairs own s = true) (hL : s.link? = some L) {k : Nat} {x : Nat × Nat}
    (hx : (k, x) ∈ pairs) :
    ∃ o, oracleOfMsg L.check.frame kept k = some o ∧ s.book.place[o]? = some x ∧
      own.contains x = true := by
  unfold seatsOnB at h
  rw [hL] at h
  simp only [Option.any_some] at h
  have h1 := List.all_eq_true.1 h (k, x) hx
  cases ho : oracleOfMsg L.check.frame kept k with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨o, rfl, h1.1, h1.2⟩

theorem shapesOnB_at {kept : Nat} {pairs : List (Nat × OracleShape)}
    (h : shapesOnB kept pairs s = true) (hL : s.link? = some L) {k : Nat} {x : OracleShape}
    (hx : (k, x) ∈ pairs) :
    ∃ o y, oracleOfMsg L.check.frame kept k = some o ∧ s.st.oracles[o]? = some y ∧ y.shape = x := by
  unfold shapesOnB at h
  rw [hL] at h
  simp only [Option.any_some] at h
  have h1 := List.all_eq_true.1 h (k, x) hx
  cases ho : oracleOfMsg L.check.frame kept k with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some] at h1
    cases hy : s.st.oracles[o]? with
    | none =>
      rw [hy] at h1
      cases h1
    | some y =>
      rw [hy] at h1
      simp only [Option.any_some, beq_iff_eq] at h1
      exact ⟨o, y, rfl, hy, h1⟩

/-- A yes at the whole list gives a yes at every list of pairs out of it. -/
theorem seatsOn_of_at {kept : Nat} {seats own : List (Nat × Nat)}
    {pairs : List (Nat × (Nat × Nat))} (h : seatsAtB kept seats own s = true)
    (hL : s.link? = some L) (hp : ∀ p ∈ pairs, seats[p.1]? = some p.2) :
    seatsOnB kept pairs own s = true := by
  unfold seatsOnB
  rw [hL]
  simp only [Option.any_some]
  refine List.all_eq_true.2 fun p hpm => ?_
  obtain ⟨o, e1, e2, e3⟩ := seatsAtB_at h hL (hp p hpm)
  rw [e1]
  show (s.book.place[o]? == some p.2 && own.contains p.2) = true
  rw [e2, e3]
  simp

theorem shapesOn_of_at {kept : Nat} {shapes : List OracleShape} {pairs : List (Nat × OracleShape)}
    (h : shapesAtB kept shapes s = true) (hL : s.link? = some L)
    (hp : ∀ p ∈ pairs, shapes[p.1]? = some p.2) : shapesOnB kept pairs s = true := by
  unfold shapesOnB
  rw [hL]
  simp only [Option.any_some]
  refine List.all_eq_true.2 fun p hpm => ?_
  obtain ⟨o, y, e1, e2, e3⟩ := shapesAtB_at h hL (hp p hpm)
  rw [e1]
  show ((s.st.oracles[o]?).any fun y => y.shape == p.2) = true
  rw [e2]
  show (y.shape == p.2) = true
  rw [e3]
  simp

/-! ## Controls -/

theorem link_of_liveReqB {born : Array (Nat × Nat)} (h : liveReqB born s = true) :
    ∃ L, s.link? = some L := by
  unfold liveReqB at h
  cases hL : s.link? with
  | none =>
    rw [hL] at h
    cases h
  | some L => exact ⟨L, rfl⟩

/-- A CONTROL: at one record the Bool says yes at one list "born" alone. -/
theorem liveReqB_one {b b' : Array (Nat × Nat)} (h : liveReqB b s = true)
    (h' : liveReqB b' s = true) : b = b' := by
  obtain ⟨L, hL⟩ := link_of_liveReqB h
  exact (liveReqB_at h hL).2.2.symm.trans (liveReqB_at h' hL).2.2

/-- A CONTROL: two lists of seats with a yes at one record agree wherever both have an entry. -/
theorem seatsAtB_one {kept : Nat} {a a' own own' : List (Nat × Nat)}
    (h : seatsAtB kept a own s = true) (h' : seatsAtB kept a' own' s = true)
    (hL : s.link? = some L) {k : Nat} {x x' : Nat × Nat} (hx : a[k]? = some x)
    (hx' : a'[k]? = some x') : x = x' := by
  obtain ⟨o, e1, e2, _⟩ := seatsAtB_at h hL hx
  obtain ⟨o', e1', e2', _⟩ := seatsAtB_at h' hL hx'
  obtain rfl : o = o' := Option.some.inj (e1.symm.trans e1')
  exact Option.some.inj (e2.symm.trans e2')

/-- A CONTROL: the like for two lists of shapes. -/
theorem shapesAtB_one {kept : Nat} {a a' : List OracleShape} (h : shapesAtB kept a s = true)
    (h' : shapesAtB kept a' s = true) (hL : s.link? = some L) {k : Nat} {x x' : OracleShape}
    (hx : a[k]? = some x) (hx' : a'[k]? = some x') : x = x' := by
  obtain ⟨o, y, e1, e2, e3⟩ := shapesAtB_at h hL hx
  obtain ⟨o', y', e1', e2', e3'⟩ := shapesAtB_at h' hL hx'
  obtain rfl : o = o' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : y = y' := Option.some.inj (e2.symm.trans e2')
  exact e3.symm.trans e3'

/-- A CONTROL: two lists of pairs with a yes at one record give a member that both name one seat. -/
theorem seatsOnB_one {kept : Nat} {a a' : List (Nat × (Nat × Nat))} {own own' : List (Nat × Nat)}
    (h : seatsOnB kept a own s = true) (h' : seatsOnB kept a' own' s = true)
    (hL : s.link? = some L) {k : Nat} {x x' : Nat × Nat} (hx : (k, x) ∈ a) (hx' : (k, x') ∈ a') :
    x = x' := by
  obtain ⟨o, e1, e2, _⟩ := seatsOnB_at h hL hx
  obtain ⟨o', e1', e2', _⟩ := seatsOnB_at h' hL hx'
  obtain rfl : o = o' := Option.some.inj (e1.symm.trans e1')
  exact Option.some.inj (e2.symm.trans e2')

/-- A CONTROL: the like for two lists of pairs (number, shape). -/
theorem shapesOnB_one {kept : Nat} {a a' : List (Nat × OracleShape)}
    (h : shapesOnB kept a s = true) (h' : shapesOnB kept a' s = true) (hL : s.link? = some L)
    {k : Nat} {x x' : OracleShape} (hx : (k, x) ∈ a) (hx' : (k, x') ∈ a') : x = x' := by
  obtain ⟨o, y, e1, e2, e3⟩ := shapesOnB_at h hL hx
  obtain ⟨o', y', e1', e2', e3'⟩ := shapesOnB_at h' hL hx'
  obtain rfl : o = o' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : y = y' := Option.some.inj (e2.symm.trans e2')
  exact e3.symm.trans e3'

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.liveReqB_at
#print axioms VerifiableInference.Desc.First.Att.P.seatsAtB_at
#print axioms VerifiableInference.Desc.First.Att.P.shapesAtB_at
#print axioms VerifiableInference.Desc.First.Att.P.seatsOnB_at
#print axioms VerifiableInference.Desc.First.Att.P.shapesOnB_at
#print axioms VerifiableInference.Desc.First.Att.P.seatsOn_of_at
#print axioms VerifiableInference.Desc.First.Att.P.shapesOn_of_at
#print axioms VerifiableInference.Desc.First.Att.P.liveReqB_one
#print axioms VerifiableInference.Desc.First.Att.P.seatsAtB_one
#print axioms VerifiableInference.Desc.First.Att.P.shapesAtB_one
#print axioms VerifiableInference.Desc.First.Att.P.seatsOnB_one
#print axioms VerifiableInference.Desc.First.Att.P.shapesOnB_one
