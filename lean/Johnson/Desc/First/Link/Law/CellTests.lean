-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CellTests.lean: THE TWO TESTS ON THE STATE THAT
`cellOkR_at` (CellOkAt.lean beside this file) ASKS (seatsAtB, shapesAtB:
                    Johnson/Desc/First/Att/K05DoorB.lean, at no kept message), OUT OF THREE TESTS
                    THAT THE TABLE's PROMISE AND THE FOLD's FACTS HOLD (bookAt · atFirstSeats ·
                    atFirstShapes), THE LIVE REQUEST's LIST OF ITS OWN MESSAGES' NUMBERS, AND TWO
                    TESTS ON PUBLIC DATA. Definitions with code and theorems. A law file; no running
                    text imports it.
  `seatsPubB nos N p Ld own seats`   ON PUBLIC DATA: for each k: message number nos[k] is sent at
                    the place p; the plan's list of places has seats[k] at it; that seat lies in
                    own.
  `shapesPubB nos N p M shapes`   ON PUBLIC DATA: for each k: message number nos[k] is sent at the
                    place p; the plan's list of shapes has shapes[k] at it.
  `seatsAtB_of`, `shapesAtB_of`   the two tests on the state.
  `cellOkR_of_facts`   so CellOkR at a part that the lens atS reads, with no test on the state but
the three. How: after another file's pattern at the mask row
(Johnson/Desc/First/Look/K3MaskOkTools.lean: book_place, bookAt_sizes, CALLED) and the door's
msgShape_at (Johnson/Desc/K12/Door/MsgShapes.lean).

Limits. AN IMPLICATION ON ONE STATE. The two public tests are evaluated at no plan here. That the
live request's own list is nos is a premise (frameIs_paid has it at
d.ownAt). The premises are not shown to be satisfiable. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.CellOkAt
import Johnson.Desc.First.Look.K3MaskOkTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S Numbers bookAt)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs seatsAtB shapesAtB oracleOfMsg)

/-- On public data: the plan's list of places has the list's seats at the own messages' numbers. -/
def seatsPubB (nos : Array ℕ) (N : Numbers) (p : Option Desc.Place) (Ld : Desc.K12.Door.Laid)
    (own seats : List (ℕ × ℕ)) : Bool :=
  seats.zipIdx.all fun x =>
    (nos[x.2]?).any fun o => bookedB N p o && Ld.places[o]? == some x.1 && own.contains x.1

/-- On public data: the plan's list of shapes has the list's shapes at the own messages' numbers. -/
def shapesPubB (nos : Array ℕ) (N : Numbers) (p : Option Desc.Place) (M shapes : List OracleShape) :
    Bool :=
  shapes.zipIdx.all fun x => (nos[x.2]?).any fun o => bookedB N p o && M[o]? == some x.1

section
variable {s : S} {L : LinkCtx} {nos : Array ℕ} {N : Numbers} {p : Option Desc.Place}

theorem oracle_own (hown : L.check.frame.own = nos) (k : ℕ) :
    oracleOfMsg L.check.frame 0 k = nos[k]? := by
  unfold oracleOfMsg
  rw [if_neg (Nat.not_lt_zero _), hown, Nat.sub_zero]

/-- **The book places the own messages at the list's seats.** -/
theorem seatsAtB_of {Ld : Desc.K12.Door.Laid} {own seats : List (ℕ × ℕ)} (hL : s.link? = some L)
    (hown : L.check.frame.own = nos) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hT : seatsPubB nos N p Ld own seats = true) : seatsAtB 0 seats own s = true := by
  unfold seatsAtB
  rw [hL]
  simp only [Option.any_some]
  refine List.all_eq_true.2 fun x hx => ?_
  have h1 := List.all_eq_true.1 hT x hx
  rw [oracle_own hown]
  cases ho : nos[x.2]? with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1 ⊢
    exact ⟨book_place hbook hseats (of_decide_eq_true h1.1.1) h1.1.2, h1.2⟩

/-- **The statement's oracles of the own messages have the list's shapes.** -/
theorem shapesAtB_of {M shapes : List OracleShape} (hL : s.link? = some L)
    (hown : L.check.frame.own = nos) (hbook : bookAt N p s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hT : shapesPubB nos N p M shapes = true) : shapesAtB 0 shapes s = true := by
  unfold shapesAtB
  rw [hL]
  simp only [Option.any_some]
  refine List.all_eq_true.2 fun x hx => ?_
  have h1 := List.all_eq_true.1 hT x hx
  rw [oracle_own hown]
  cases ho : nos[x.2]? with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    have hoS : o < s.st.oracles.size := by
      rw [(bookAt_sizes hbook).2]
      exact of_decide_eq_true h1.1
    have hsh := Desc.K12.Door.msgShape_at hshapes o hoS
    rw [h1.2] at hsh
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hsh
    simp only [Option.any_some, hy, beq_iff_eq]
    exact e

end

/-- **CellOkR at a part that the lens reads, with no test on the state but the three.** -/
theorem cellOkR_of_facts (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (own : List (ℕ × ℕ)) {s : S} {a : K9.Part}
    (ha : atS.get? s = some a) (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : s.st.codes = D.codes) {nos : Array ℕ} {N : Numbers} {p : Option Desc.Place}
    {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (hown : a.L.check.frame.own = nos)
    (hbook : bookAt N p s = true) (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hT1 : seatsPubB nos N p Ld own (List.ofFn seatT) = true)
    (hT2 : shapesPubB nos N p M ((digList x D rad).map (·.1)) = true)
    (hseat : ∀ ad, cellAddr tl ad → (seatOf D x.link ad).isSome = true)
    (hfit : ∀ ad z, cellAddr tl ad → seatOf D x.link ad = some z →
      z.Fits D.codes (digList x D rad))
    (hP : LaidPub x tl D rad) : CellOkR x tl D rad seatT own a :=
  cellOkR_atS x tl D rad seatT own ha hfr hlay harr hcs
    (seatsAtB_of (part_reads s a ha).1 hown hbook hseats hT1)
    (shapesAtB_of (part_reads s a ha).1 hown hbook hshapes hT2) hseat hfit hP

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatsAtB_of
#print axioms VerifiableInference.Desc.LinkJoin.shapesAtB_of
#print axioms VerifiableInference.Desc.LinkJoin.cellOkR_of_facts
