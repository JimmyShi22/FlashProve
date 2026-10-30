-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FillStart.lean: WHAT THE PROMISE AT THE CHAIN's FIRST BORDER READS OF THE
FILLING, AS A LAYER WITH CODE, AND THAT A LAWFUL FIRST RECORD HAS IT BY ITS MAKE. Small; no Mathlib.
A file BESIDE the table of joints: it turns nothing of it.

Why. At the first border the promise (`onAt_start`, Johnson/Desc/First/BordersStart.lean) asks of
the filling: "in order"; the public items that are open at the start (`unheard`, `noneSent`, and
what a filling of the door lays open there); the book's numbers at the front. The tie between the
chain's first statement and the request must draw all of these from the first record's make.
`unheard` lies in the table's own layer (FillKeeper.lean). Here: the three equations that "in order"
owes, and `noneSent`.

What is said. `eqsB codes shape layout s`: the statement's codes, and the request's shape and the
rows' layout in the chain's own state of the calls, are the three given. `noneSentB s`: the
statement holds no oracle message, and the frame no message "at the start". `pubStart1`,
`fillStart`: the layer: `inOrder` is CONJOINED with `eqsB` (whoever else speaks to that field is
kept); `noneSent` is `noneSentB`; every other item and field as it was. `startP_is`: a start that
passes the start's tests IS the first record. AT THE FIRST RECORD WITH ANY REQUEST's WORDS LAID:
`eqsB_first`, `noneSentB_first`, `unheardB_first`: each test says yes; `bookAt_first`: the book's
clause holds wherever the two numbers at that place are 0. `withTold_front`: at `Numbers.withTold`
the two numbers at a list's first place are 0.

Limits. (1) `noneSent` is another kind's item (K1's): its own layer lays the same two clauses and
one more: WHEN THAT LAYER IS COMPOSED THIS ONE YIELDS THE ITEM. (2) "In order" has a further
conjunct of that kind (a test on groups, rows and samples): not here. (3) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.First.BordersStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- The three equations that "in order" owes. -/
def eqsB (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) (s : S) : Bool :=
  decide (s.st.codes = codes) && decide (s.check.frame.shape = shape) &&
    decide (s.check.rows.layout = layout)

/-- No oracle message has been sent; the frame holds none "at the start". -/
def noneSentB (s : S) : Bool := s.st.oracles.isEmpty && s.check.frame.atStart.isEmpty

/-- **The layer's half with code.** -/
def pubStart1 {P : Type} (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .noneSent => noneSentB a.2
    | q => f q a

/-- **The layer.** -/
def fillStart {P W : Type} (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout)
    (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    inOrder := fun a => Mg.inOrder a && eqsB codes shape layout a.2
    pub := pubStart1 Mg.pub }

section
variable {P W : Type} (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout)
  (Mg : Meaning P W)

theorem fillStart_pub : (fillStart codes shape layout Mg).pub = pubStart1 Mg.pub := rfl

theorem fillStart_inOrder (a : P × S) : (fillStart codes shape layout Mg).inOrder a =
    (Mg.inOrder a && eqsB codes shape layout a.2) := rfl

theorem fillStart_noneSent (a : P × S) :
    (fillStart codes shape layout Mg).pub .noneSent a = noneSentB a.2 := rfl

/-- Every other item is handed on. -/
theorem fillStart_else (q : Pub) (h : q ≠ .noneSent) (a : P × S) :
    (fillStart codes shape layout Mg).pub q a = Mg.pub q a := by
  cases q <;> first | rfl | exact absurd rfl h

end

/-- A start that passes the start's tests IS the first record. -/
theorem startP_is {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {s : S} (h : S.startP Pp codes shape layout = some s) :
    s = S.firstRecord codes shape layout := by
  unfold S.startP at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

section
variable (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout)
  (req : Array UInt32)

theorem eqsB_first :
    eqsB codes shape layout ((S.firstRecord codes shape layout).withReq req) = true := by
  simp [eqsB, S.firstRecord, S.withReq]

theorem noneSentB_first : noneSentB ((S.firstRecord codes shape layout).withReq req) = true := rfl

theorem unheardB_first : unheardB ((S.firstRecord codes shape layout).withReq req) = true := rfl

/-- The book's clause at the first record, wherever the two numbers are 0. -/
theorem bookAt_first (N : Numbers) (p : Option Place) (hT : N.treesAt p = 0) (hM : N.msgsAt p = 0) :
    bookAt N p ((S.firstRecord codes shape layout).withReq req) = true := by
  unfold bookAt
  rw [hT, hM]
  rfl

end

/-- At the filling off what the blocks tell, the two numbers at a list's first place are 0. -/
theorem withTold_front (N : Numbers) (p : Place) (l : List Place) (told : List (List Oracle)) :
    (N.withTold (p :: l) told).treesAt (some p) = 0 ∧
      (N.withTold (p :: l) told).msgsAt (some p) = 0 := by
  simp [Numbers.withTold, borderOf, treesTold, msgsTold]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fillStart_else
#print axioms VerifiableInference.Desc.First.startP_is
#print axioms VerifiableInference.Desc.First.eqsB_first
#print axioms VerifiableInference.Desc.First.bookAt_first
#print axioms VerifiableInference.Desc.First.withTold_front
