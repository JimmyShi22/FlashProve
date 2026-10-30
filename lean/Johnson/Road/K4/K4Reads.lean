-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4Reads.lean: A SECOND STRUCTURE BESIDE `K4Means` (K4Means.lean): SEVEN LINES ON
SEVEN OF THE OWNERS' LETTERS: "a letter that may read the verifier's state reads of it what an
accept of K4's sub-protocol leaves". Definitions alone. A LIGHT FILE: over K4Means.lean and the
frame of K4's yes. Why a structure of its own: `K4Means` holds equations of the meaning's
fields; these are sentences on the DATA at which the fields stand (`K4Data`): no field of the
meaning says them, no test on the public parameters can, and K4's files cannot prove them of a
letter: they are owed by whoever fills the letters.

  `LayRest s s'`: THE FENCE, WRITTEN OUT: s stands in a feed-forward segment, and `Rest s s'`
    (Johnson/Desc/First/K4/ReadsAtS.lean): of the verifier's state st · book · roots · failed ·
    check · out · req are the same; so are the readers link? · tl? · look? · lookHeard?; s' stands
    in a feed-forward segment too, with the same L · fo · tl · lookHeard. THE SEGMENT's LEDGER F,
    own AND THE STATE's rowsOwed MAY DIFFER AT WILL.
  `SameStr Fr base x y`: of the strings: the committed table is the same; so is every entry of a
    tree below base.
  **`K4Reads D Z Fr base`**: EACH LINE IS ASKED INSIDE THE FENCE, NEVER AT ALL PAIRS OF STATES
    (outside a feed-forward segment `Rest` lets the open part differ at will). rw: the pile's reader
    of the witness is one at s and s' · decT: so is the committed table's decoder · req: and the
    relation's reader of the request · head: the head's part goes back from (s', y) to (s, x) · smp:
    the samples' reader is one · base: what lies beneath all layers of "in order" rides · stMask:
    the stated function's mask is one.

  **`K4Kept Mg rest Z`**: beside it, ON THE MEANING: one line, general in the name: the test of a
    name at the table's door that is of the sort rest says one thing at s and s' inside the fence.
    (Why: which names of other kinds are open across K4's sub-protocol hangs on
    the composed filling; a closed list of names in K4's theorems would turn with it.)

Limits. SENTENCES: NOTHING IS PROVED HERE. MARKED STATES ARE INSIDE THE FENCE (the table's door
asks "the committed table decodes" at them too). A letter that reads the segment's ledger, own or
rowsOwed cannot meet its line. No promise stands in the fence: the lines are asked at more pairs
than K4's laws spend them at: so that the file names neither the meaning nor a law of K4's road. NOT
EVERY LETTER THAT READS THE STATE HAS A LINE HERE: the segments' readers Rd read the segment's
ledger too: what is wanted of them stands, at the lookup's run "objects", in
Riders/ObjectsAtMeans.lean's structure of premises. WHO PAYS: `k4Reads_at` (K4ReadsOf.lean), general
in the data: rw, stMask, smp and req under an equation each on a letter, decT where the committed
table's decoder reads no state; base and head stay lines there (head: K4HeadBlind.lean): head may
fail if the head's part reads a tree from base on (an open question). K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Desc.First.K4.ReadsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.Sound (Frame strsOf MsgT)

/-- The fence: s stands in a feed-forward segment, and s' is s but for what an accept of K4's lays.
-/
def LayRest (s s' : S) : Prop := (∃ a : LayOwn, s.here = .lay a) ∧ Rest s s'

/-- Of the strings: the committed table, and every tree below base. -/
def SameStr (Fr : Frame) (base : ℕ) (x y : Fr.E.Str) : Prop :=
  y.1 = x.1 ∧ ∀ (j l : ℕ) (q : PosL Fr.all), posL Fr.all j l = some q → j < base → y.2 q = x.2 q

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}

/-- **THE STRUCTURE: what the owners' letters read of the verifier's state, across an accept of
K4's.**
-/
structure K4Reads (D : K4Data Xi P Tok rows cols nR kC X) (Z : P) (Fr : Frame) (base : ℕ) :
    Prop where
  rw : ∀ s s', LayRest s s' → D.rw13 (Z, s') = D.rw13 (Z, s)
  decT : ∀ s s', LayRest s s' → ∀ c, D.decT c (Z, s') = D.decT c (Z, s)
  req : ∀ s s', LayRest s s' → D.H.req (Z, s) = D.H.req (Z, s')
  head : ∀ s s' (x y : Fr.E.Str), LayRest s s' → SameStr Fr base x y → ∀ p i w,
    D.headPart p i (Z, s') (strsOf Fr y) w → D.headPart p i (Z, s) (strsOf Fr x) w
  smp : ∀ s s', LayRest s s' → ∀ sd i, D.smp (Z, s') sd i = D.smp (Z, s) sd i
  base : ∀ s s', LayRest s s' → D.base (Z, s) = true → D.base (Z, s') = true
  stMask : ∀ s s', LayRest s s' → ∀ B j, (D.St.at1 s' B).mask j = (D.St.at1 s B).mask j

/-- **ONE LINE FOR EVERY NAME AT THE DOOR, OF WHICHEVER KIND**: a name of the sort rest has a
test
that says one thing at s and s' inside the fence. A new name that is open across K4's sub-protocol
costs
its owner this one line, and turns no theorem of K4's. -/
structure K4Kept (Mg : VerifiableInference.Desc.First.Meaning P (Wit (CellsK rows cols) Tok MsgT))
    (rest : Option ℕ → String → Bool) (Z : P) : Prop where
  kept : ∀ seg name, rest seg name = true → ∀ s s', LayRest s s' →
    Mg.pub (.more seg name) (Z, s') = Mg.pub (.more seg name) (Z, s)

end OnBytes.Road.K4
