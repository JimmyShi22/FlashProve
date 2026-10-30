-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Block.lean: K4, the layers' own rounds, as a block of the interactive oracle
proof (Johnson/Desc/Block.lean). CODE ALONE: no theorem.

ROUNDS. K4's own table (`rounds P hp g`: OnBytes/Desc/First/K4/Rounds.lean), each row as a whole
entry of the plan (`entryOf`): the name; 24 bytes for each element sent; how many elements are
drawn, and how many of these are never 0; how many rows the round batches. All other words of an
entry are at their defaults: no proof of work, no root, no sample answer, no position, no matrix
entry. `Block.step` holds a view against these rounds (`roundsFit`), and the tests on the plan hold
them against the made plan's entries, whole.
READS. No round opens anything, and no round sends a root: `oracles` is empty at each round. K4's
claims name entries of the reads' array, which is committed behind the stretch, and of the mask row;
K9 and K10 read these.
FIXED BEFORE THE DRAW. `before` is a parameter of the place (`Par.before`): the oracle messages on
which K4's tests lean, by their numbers of sending. By the format's page
(docs/format/11-2-feed-forward-segment.md:55-63, :69): all that the segment commits at its moment 0,
in front of the lookup; and, from group 1 on, the message of the segment before that holds its
outgoing stream. ALL OF MOMENT 0, UNSIFTED: which of these arrays a form of K4's names is not
said here. What is sent behind the stretch (the reads; the digits) must not stand in it.
The committed weights are a stored table, no message of the chain.
THE INSTANCE. K4 reads the request's tokens, in the first group alone. They come off the state
(`Seat.tokv`), not out of `Par`.
THE TESTS ON THE PLAN ALONE. The plan is one that K4 is written for (`covers`).
DECIDES. Six refusals, each under its name: something is owed in front · the view's rounds do not
fit K4's table · a round is not plain (the strict reading of a round:
OnBytes/Desc/First/FlStep.lean) · what the lookup returned is not there · HEAR refuses (`hearFl`:
its own tests stand on the page's table under «Hear»; they bear one name here, because the
plain functions refuse without a word) · the stretch is not used up. Behind it nothing is owed. THE
SECOND AND THE THIRD ARE ALSO ASKED BY `roundsFit`: they stay in decide; k4_fit
(Johnson/AtFull/Shape/K4Fit.lean; digests dropped) says, for all views, that roundsFit implies them.

THE DEBT OF ROWS. Block.lean does not ask it, and no kind drops its own guard. In front:
`decide`'s first test. Of K4's own entries: the count of each is the table's, out of the layout's
public numbers; the tests on the plan compare it with the made plan's; every round that counts rows
is one of the four that batch, and the last round counts none.
CLAIMS. Two named runs, "front" (the format's groups 1 to 12) and "back" (14 and 15). The smallness
test's claims stand between them: THE ORDER IS PROTOCOL, and the link states it. Neither run reads
the number of claims gathered so far. GROUP 1 IS THE LOOKUP's OWN. `Par.k3Runs` says who states it.
false: "front" makes these claims and marks them as paid, as `verify-on-bytes`'s routine
does. true: K3's block states them as a run of its own; "front" then begins at group 2, AND THE
LINK's ORDER MUST LAY K3's RUN RIGHT IN FRONT OF "front", where it also marks them as paid.
BEHIND THE BATCHING. One named run, "free-slot": every slot but the merge's has a coefficient in the
one equation as it stands behind the adding.
SENDS. Not written in this file (Johnson/Desc/ProofFile/Honest/K4/Part.lean).

Limits. THAT `entryOf` MAKES THE PLAN's OWN ENTRIES, WHOLE, IS SHOWN BY NO THEOREM HERE, AND THIS
TEXT HAS NOT RUN. The type of
a claim is `verify-on-bytes`'s `Aff`.
-/
import Johnson.Desc.Block
import OnBytes.Desc.First.K4.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open VerifiableInference.Desc (Block Kind Place named)

/-- A row of K4's table as a whole entry of the plan. -/
def entryOf (d : Rd) : Fmt.Entry :=
  { name := d.name.name, msg := 24 * d.sent, drawE := d.drawn, drawNZ := d.notZero, rows := d.rows }

/-- The plan's entries of K4's stretch, as K4's table makes them. -/
def entries (P : Pub) (hp : HPlan2) (g : Nat) : List Fmt.Entry := (rounds P hp g).map entryOf

/-- A place's public parameters. -/
structure Par where
  /-- the place's name, for a refusal's words -/
  name : String
  /-- the link's number in the first chain; the block's number inside the link -/
  link : Nat
  piece : Nat
  /-- the oracle messages that must have been sent before the first draw: chain, number -/
  before : List (Nat × Nat)
  /-- whether the lookup's block (K3) states its own claims (the format's group 1) as a run of its
  own: then "front" drops them -/
  k3Runs : Bool := false
  /-- the layers' public record (its field tokv is never read: the tokens come off the state), the
  sub-proof's plan, the group of layers -/
  P : Pub
  hp : HPlan2
  g : Nat

/-- A test under its name: Johnson/Desc/Block.lean's `need` (K4/Claims.lean has another of that name
in this namespace). -/
abbrev test (name : String) (b : Bool) : Except String Unit := VerifiableInference.Desc.need name b

variable {S : Type} (L : Seat S)

/-- DECIDES. -/
def hearAt (p : Par) (s : S) (rs : List Fmt.RoundView) : Except String S := do
  test "K4.something-is-owed-in-front" (L.owed s).isNone
  -- the next two: also asked by roundsFit
  test "K4.the-table-of-rounds" (fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs)
  test "K4.the-strict-reading" (Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs)
  let fo ← named "K4.what-the-lookup-returned-is-not-there" (L.look s)
  match hearFl { p.P with tokv := L.tokv s } p.hp p.g fo (L.fork s)
      (paired rs (entries p.P p.hp p.g)) with
  | some (o, F, []) => pure (L.setOwed (L.setOwn (L.setFork s F) o) none)
  | some _ => throw "K4.the-stretch-is-not-used-up"
  | none => throw "K4.hear"

/-- CLAIMS as a named run: the forms as a list, and the state with the ledger behind them. -/
def runOf (name : String) (f : Own → Fork → Option (Array Aff × Fork)) (s : S) :
    Except String (List Aff × S) := do
  let o ← named "K4.what-was-heard-is-not-there" (L.own s)
  let x ← named name (f o (L.fork s))
  pure (x.1.toList, L.setFork s x.2)

/-- BEHIND THE BATCHING. -/
def freeSlot (hp : HPlan2) (s : S) : Except String S := do
  let o ← named "K4.what-was-heard-is-not-there" (L.own s)
  test "K4.free-slot" (freeSlotOk hp.used o.wo.sFv (L.fork s))
  pure s

/-- **K4.** -/
def block : Kind Par S Aff := fun p =>
  { name := p.name
    place := ⟨1, some p.link, p.piece, .K4⟩
    planOk := covers p.P
    rounds := (entries p.P p.hp p.g).map fun e => { entry := e }
    oracles := (entries p.P p.hp p.g).map fun _ => []
    before := p.before
    decide := fun s rs _ => hearAt L p s rs
    claims := [("front", fun _ s => runOf L "K4.claims-front"
                  ((if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g) s),
               ("back", fun _ s => runOf L "K4.claims-back" formsBack s)]
    after := [("free-slot", freeSlot L p.hp)] }

end OnBytes.Desc.First.K4
