-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05OwnersSent.lean: kind K5: THE KIND's TWO BOOLS ON THE SEATS AND THE SHAPES
OF THE MESSAGES THAT ARE READ (seatsOnB, shapesOnB) FROM THREE ITEMS' BOOLS THAT ARE OPEN AT THE
SAME BORDER: "frame.sentIs" (sentIsB, Johnson/Desc/First/FillSent.lean: the
open link's frame holds the plan's numbers), "K12.seatsCarried" and "K12.msgShapes":
seatsOn_of_carried and shapesOn_of_msgShapes (Johnson/Desc/First/Att/K05OwnersGive.lean) with "which
numbers the frame holds" paid.

IS IT EMPTY HERE? At the empty list of pairs both conclusions hold where a link is open. NO MEMBER
IS SHOWN.

Main names:
  `oNoP d m kept k`: the plan's term for the number in the statement of member k of the caller's
    list of segment m: a kept message's number below kept; an own message's from there on.
  `oracle_of_sentIs`: a yes of sentIsB d m at a state with the open link L: oracleOfMsg
    L.check.frame kept k = oNoP d m kept k.
  `seatsOn_of_sentIs`, `shapesOn_of_sentIs`: the kind's two Bools. WHAT IS LEFT, PAIR BY PAIR: the
    plan's term answers a number o (public) · the plan's list has my seat, which lies in own | my
    shape at o (public) · o IS BELOW THE BOOK's NUMBER OF PLACES | THE STATEMENT's NUMBER OF
    MESSAGES: "it is sent already": a fact on the verifier's state that none of the three Bools
    says.
  `sizes_of_bookAt`: THE PROMISE's OWN CLAUSE bookAt SAYS IT: both sizes are the plan's number
    N.msgsAt at the place.
  `seatsPlanB`, `shapesPlanB`: two tests on public data (they have run nowhere). `seatsOn_of_items`,
    `shapesOn_of_items`: **the kind's two Bools from sentIsB, the owner's Bool, bookAt and the
    public test at n := N.msgsAt p.**
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05OwnersGive
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB five_of_sentIs)
open VerifiableInference.Desc.First (Numbers bookAt)

/-- The plan's term for the number in the statement of member k of the caller's list of segment m.
-/
def oNoP (d : SentData) (m kept k : Nat) : Option Nat :=
  if k < kept then (d.kept m)[k]? else (d.own m)[k - kept]?

/-- The frame's number is the plan's. -/
theorem oracle_of_sentIs {d : SentData} {m : Nat} {s : First.S} {L : LinkCtx} (hL : s.link? = some L)
    (h : sentIsB d m s = true) (kept k : Nat) : oracleOfMsg L.check.frame kept k = oNoP d m kept k := by
  obtain ⟨_, _, _, h4, h5⟩ := five_of_sentIs hL h
  unfold oracleOfMsg oNoP
  rw [h4, h5]

/-- **The kind's Bool on the seats.** -/
theorem seatsOn_of_sentIs {d : SentData} {m : Nat} {Ld : Laid} {s : First.S} {L : LinkCtx} {kept : Nat}
    {pairs : List (Nat × (Nat × Nat))} {own : List (Nat × Nat)} (hs : sentIsB d m s = true)
    (h : seatsCarriedB Ld s.book = true) (hL : s.link? = some L)
    (hp : ∀ p ∈ pairs, ∃ o, oNoP d m kept p.1 = some o ∧ o < s.book.place.size ∧
      Ld.places[o]? = some p.2 ∧ own.contains p.2 = true) :
    seatsOnB kept pairs own s = true :=
  seatsOn_of_carried h hL fun p hpm => by
    obtain ⟨o, e1, e2⟩ := hp p hpm
    exact ⟨o, (oracle_of_sentIs hL hs kept p.1).trans e1, e2⟩

/-- **The kind's Bool on the shapes.** -/
theorem shapesOn_of_sentIs {d : SentData} {m : Nat} {M : List OracleShape} {s : First.S} {L : LinkCtx}
    {kept : Nat} {pairs : List (Nat × OracleShape)} (hs : sentIsB d m s = true)
    (h : msgShapesB M s.st = true) (hL : s.link? = some L)
    (hp : ∀ p ∈ pairs, ∃ o, oNoP d m kept p.1 = some o ∧ o < s.st.oracles.size ∧ M[o]? = some p.2) :
    shapesOnB kept pairs s = true :=
  shapesOn_of_msgShapes h hL fun p hpm => by
    obtain ⟨o, e1, e2⟩ := hp p hpm
    exact ⟨o, (oracle_of_sentIs hL hs kept p.1).trans e1, e2⟩

/-- "It is sent already", on public data: the promise's own clause bookAt
(Johnson/Desc/First/Borders.lean) pins the book's number of places and the statement's number of
messages at the plan's number at the place. -/
theorem sizes_of_bookAt {N : Numbers} {p : Option VerifiableInference.Desc.Place} {s : First.S}
    (h : bookAt N p s = true) : s.book.place.size = N.msgsAt p ∧ s.st.oracles.size = N.msgsAt p := by
  unfold bookAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2.trans h.2, h.2⟩

/-- A test on public data: each pair's member has a number in the plan's term, below n; the plan's
list has the pair's seat there; the seat lies in own. -/
def seatsPlanB (d : SentData) (m kept : Nat) (Ld : Laid) (pairs : List (Nat × (Nat × Nat)))
    (own : List (Nat × Nat)) (n : Nat) : Bool :=
  pairs.all fun p =>
    (oNoP d m kept p.1).any fun o =>
      decide (o < n) && decide (Ld.places[o]? = some p.2) && own.contains p.2

/-- A test on public data: each pair's member has a number in the plan's term, below n; the plan's
list has the pair's shape there. -/
def shapesPlanB (d : SentData) (m kept : Nat) (M : List OracleShape) (pairs : List (Nat × OracleShape))
    (n : Nat) : Bool :=
  pairs.all fun p =>
    (oNoP d m kept p.1).any fun o => decide (o < n) && decide (M[o]? = some p.2)

/-- **The kind's Bool on the seats, from three Bools on the state and one on public data.** -/
theorem seatsOn_of_items {d : SentData} {m : Nat} {Ld : Laid} {s : First.S} {L : LinkCtx} {kept : Nat}
    {pairs : List (Nat × (Nat × Nat))} {own : List (Nat × Nat)} {N : Numbers}
    {p : Option VerifiableInference.Desc.Place} (hs : sentIsB d m s = true)
    (h : seatsCarriedB Ld s.book = true) (hb : bookAt N p s = true) (hL : s.link? = some L)
    (hp : seatsPlanB d m kept Ld pairs own (N.msgsAt p) = true) : seatsOnB kept pairs own s = true :=
  seatsOn_of_sentIs hs h hL fun q hq => by
    have h0 := List.all_eq_true.1 hp q hq
    obtain ⟨o, e1, e2⟩ := (Option.any_eq_true _ _).1 h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e2
    exact ⟨o, e1, by rw [(sizes_of_bookAt hb).1]; exact e2.1.1, e2.1.2, e2.2⟩

/-- **The kind's Bool on the shapes, from three Bools on the state and one on public data.** -/
theorem shapesOn_of_items {d : SentData} {m : Nat} {M : List OracleShape} {s : First.S} {L : LinkCtx}
    {kept : Nat} {pairs : List (Nat × OracleShape)} {N : Numbers}
    {p : Option VerifiableInference.Desc.Place} (hs : sentIsB d m s = true)
    (h : msgShapesB M s.st = true) (hb : bookAt N p s = true) (hL : s.link? = some L)
    (hp : shapesPlanB d m kept M pairs (N.msgsAt p) = true) : shapesOnB kept pairs s = true :=
  shapesOn_of_sentIs hs h hL fun q hq => by
    have h0 := List.all_eq_true.1 hp q hq
    obtain ⟨o, e1, e2⟩ := (Option.any_eq_true _ _).1 h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e2
    exact ⟨o, e1, by rw [(sizes_of_bookAt hb).2]; exact e2.1, e2.2⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatsOn_of_items
#print axioms VerifiableInference.Desc.First.Att.P.shapesOn_of_items
#print axioms VerifiableInference.Desc.First.Att.P.oracle_of_sentIs
#print axioms VerifiableInference.Desc.First.Att.P.seatsOn_of_sentIs
#print axioms VerifiableInference.Desc.First.Att.P.shapesOn_of_sentIs
