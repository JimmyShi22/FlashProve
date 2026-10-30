-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/Steps.lean: the layers' own rounds (K4) as steps of a chain's decision. CODE
ALONE: no theorem.

K4 has two halves (OnBytes/Desc/First/K4/Plain.lean). HEAR reads the stretch's rounds. CLAIMS reads
no round: it makes two lists of linear forms from what was heard, and these are added to the
sub-proof's one equation behind the batching draw. Here each half becomes a step of the one type
(state, this stretch's rounds, the opened columns not yet taken; the new state and how many columns
were taken, or a refusal).

`hearStep`. It refuses unless:
  1. nothing is owed in front: the round closed last counts no batched rows, or their number has
     been compared;
  2. THE TABLE FITS: the plan's entries and the view's rounds of the stretch are, row by row, what
     K4's own table of rounds says (`rounds P hp g`, OnBytes/Desc/First/K4/Rounds.lean): the name;
     how many elements are sent; how many are drawn, and how many of these are never 0; HOW MANY
     ROWS THE ROUND BATCHES; and there are as many entries and rounds as rows;
  3. every round is plain: elements of the extension field alone are sent and drawn, and the entry
     says so (the strict reading of a round: OnBytes/Desc/First/FlStep.lean);
  4. `hearFl` returns (its own tests: the page's table under «Hear»), and has used the stretch up.
Behind it nothing is owed.

WHO COMPARES A BATCHING ROUND's COUNT OF ROWS. Test 2 does, for every round, against a number that
the table works out of the layout's public numbers. So the count is compared HERE, IN CODE, whatever
close the function beneath calls; that `Fl.batch` compares it once more is not what the step
leans on. `rowsTabled` therefore answers the strict reading's question «how are this entry's rows
answered for» by: none, or compared inside.

`shapeStep`: the lookup's shape is the layout's (`shapeFits`). HEAR asks it again at its head; it
stands as a step of its own because the skeleton has a quiet step there. `frontStep`, `backStep`:
the two lists of forms, each added to the one equation in its order (`addForms`). `backStep` also
asks `freeSlotOk`, the test behind all claims. By the table of kinds that test belongs to the page
that writes the one equation (K9); it is called here, so that the step asks
no less than the skeleton's.

`claimsCounted`, `tablesHeld`: two tests of the layers' top routine that stand behind all claims, in
the quiet step that holds the smallness test's own tests ("7.quiet": K8's): as many claims were
added as the plan counts; the tables that the smallness test holds are those that HEAR returned.
Plain functions on data, to be called from that step.

`Seat S` says where in a state S lie the things that the steps read and write: the sub-proof's
ledger; what the lookup returned; what HEAR returned; what is owed; THE REQUEST's TOKENS. A step
refuses if what it reads is not there. The tokens are the one thing that K4 reads of the instance
(in the first group, for the claim on the embedding): they come OFF THE STATE, where the start has
laid them, not out of the place's parameters: the field tokv of the public record P is overwritten
and never read (read from the text, not shown here: a file's description hangs on the public
files alone).

Limits. Definitions alone. P, hp, g and the plan's entries es are the table's maker's. `take P hp g`
is the number of rounds. Never run.
-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.FlStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.Desc.First.Kit (Step RowsHow ofFlWith quiet)

/-- Where in a state lie the things that K4's steps read and write. -/
structure Seat (S : Type) where
  /-- the sub-proof's ledger -/
  fork : S → Fork
  setFork : S → Fork → S
  /-- what the lookup on the calls returned -/
  look : S → Option Forest.Heard
  /-- what HEAR returned -/
  own : S → Option Own
  setOwn : S → Own → S
  /-- what is owed: some n: the round closed last counts n batched rows, not yet compared -/
  owed : S → Option Nat
  setOwed : S → Option Nat → S
  /-- the request's tokens: what K4 reads of the instance (in the first group: the embedding) -/
  tokv : S → Array Nat

/-- As many entries and rounds as rows of the table, and each row fits. -/
def fitsAll : List Rd → List Fmt.Entry → List Fmt.RoundView → Bool
  | [], [], [] => true
  | d :: ds, e :: es, r :: rs => d.fits e r && fitsAll ds es rs
  | _, _, _ => false

/-- How many rounds HEAR takes. -/
def take (P : Pub) (hp : HPlan2) (g : Nat) : Nat := (rounds P hp g).length

/-- How an entry's rows are answered for, where the table has been held against it: it counts none,
or its count has been compared with the table's. -/
def rowsTabled (e : Fmt.Entry) : RowsHow := if e.rows == 0 then .no else .inside

variable {S : Type} (L : Seat S)

/-- HEAR. es: the plan's entries of the stretch. -/
def hearStep (P : Pub) (hp : HPlan2) (g : Nat) (es : List Fmt.Entry) : Step S := fun s rs cols =>
  if fitsAll (rounds P hp g) es rs then
    ofFlWith rowsTabled es L.fork L.owed
      (fun s => (L.look s).map fun fo => hearFl { P with tokv := L.tokv s } hp g fo)
      (fun s o F d => L.setOwed (L.setOwn (L.setFork s F) o) d) s rs cols
  else none

/-- The lookup's shape is the layout's. -/
def shapeStep (P : Pub) : Step S :=
  quiet fun s => (L.look s).bind fun fo => if shapeFits P fo then some s else none

/-- CLAIMS, groups 1 to 12, added to the one equation. -/
def frontStep (P : Pub) (g : Nat) : Step S :=
  quiet fun s => do
    let o ← L.own s
    let (fs, G) ← formsFront P g o (L.fork s)
    let G ← addForms fs G
    pure (L.setFork s G)

/-- CLAIMS, groups 14 and 15, added to the one equation; and the test behind all claims. -/
def backStep (hp : HPlan2) : Step S :=
  quiet fun s => do
    let o ← L.own s
    let (fs, G) ← formsBack o (L.fork s)
    let G ← addForms fs G
    if freeSlotOk hp.used o.wo.sFv G then pure (L.setFork s G) else none

/-! ## Two tests behind all claims, for the step that holds the smallness test's own tests -/

/-- As many claims have been added to the one equation as the plan counts
(OnBytes/Model/Layer.lean:633). No mere book-keeping: in one control (the claim on the embedding
dropped) this test alone refused. -/
def claimsCounted (hp : HPlan2) (F : Fork) : Bool := F.nClaim == hp.nLin

/-- The tables that the smallness test holds are those that HEAR returned (Layer.lean:634). -/
def tablesHeld (o : Own) (tl : HTailF2) : Bool := tl.funsHeld o.funs

end OnBytes.Desc.First.K4
