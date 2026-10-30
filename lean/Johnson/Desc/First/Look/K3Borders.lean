-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Borders.lean: THE TABLE OF JOINTS: THE TWO BORDERS OF THE KIND "LOOKUP"
(K3), THE LOWER STOREY: WHAT IS PROMISED, as two functions to Bool that a run evaluates. Definitions
alone; without Mathlib; over the carried record's own readers (`fork?`, `rowsOwed`, `lookHeard?`,
`tl?`), no raw field. The relations at the two borders are not stated here.


IN FRONT OF K3's PLACE, PROMISED (`k3OnIn`): the place has a shape; a ledger is open, its three
arrays of the ledger's size, its count at the place's first slot, THE LOOKUP'S SLOTS INSIDE ITS ROOM
AND FREE; no rows are owed; nothing is heard yet at this seat. THE LEDGER'S SIZES AND THE FREE MARKS
ARE LOAD-BEARING, AND THE KIND TESTS NONE OF THEM: from a ledger
whose arrays are shorter than its size a hidden value reads as the public 0, and no row binds a mask
entry. Read, not shown here: no run reaches such a ledger (whoever opens one makes it sized). SO
IT IS THIS JOINT'S PROMISE; WHO OWES IT: the block that opens the ledger.

BEHIND K3's PLACE, AND AT EVERY BORDER FROM THERE UP TO THE FRONT OF THE LINK'S BATCHING (there the
row ends), PROMISED (`k3OnOut`): something is heard at this seat, AND ITS SHAPE IS THE PLACE'S,
every field; the shape has a call for each of its NC; zx has dT coordinates, zy rK, and there is a
key point a call (what `block_point` proves); call c's key point has as many coordinates as the
call's keys have bits; a ledger is open, of the right sizes, its count at least behind the lookup's
slots; THE SLOTS OF THE SUMCHECK OVER THE LEAVES ARE INSIDE THE ROOM AND STILL FREE: the hearing
takes them and does not fill them; the run of claims "planes" fills them at the link's batching, and
the ledger's own function refuses a slot that is filled already; AND THAT STRETCH LIES INSIDE THE
LOOKUP'S OWN SLOTS (without it two lookups'
stretches could not be told apart by the places' first slots); THE TWO POINTS AT WHICH THE PLANES
ARE READ HAVE kT + cK + 5 COORDINATES EACH (the callers' tables of weights on
the planes' rows have their 2 ^ lm entries only then: `Forest.phiB` cuts a shorter point in
silence).

WHAT HAS RUN: no run of these two functions is held in this library. Of the stretch's two
comparisons the lower one has been seen to fail at no record (said here without a theorem). One
conjunct stays out: "two formulas return at this ledger" (no relation here needs it).

Limits: nothing of the kind is proved. A deferred mark (`failed`) is not in these rows: one wrapper
for all borders (`onAt`, Johnson/Desc/First/Borders.lean). Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff Fork Call)
open OnBytes.Model.Forest (Shape Heard)

/-- Two calls are the same: read by the whole constructor: a field more or fewer breaks it at Lean.
(No instance is laid here: another file of the fold's harness derives one.) -/
def sameCall : Call → Call → Bool
  | ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ =>
    a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7 &&
      a8 == b8 && a9 == b9 && a10 == b10

/-- Two shapes are the same: every field, by the whole constructor. -/
def sameShapeAll : Shape → Shape → Bool
  | ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ =>
    a1.size == b1.size && (a1.toList.zip b1.toList).all (fun x => sameCall x.1 x.2) &&
      a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7 && a8 == b8 &&
      a9 == b9 && a10 == b10 && a11 == b11

/-! ## 1 In front -/

/-- The ledger's three arrays have the ledger's size. -/
def sizedB (G : Fork) : Bool := G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns

/-- The n slots from first on lie inside the ledger's room and are free. -/
def freeB (G : Fork) (first n : Nat) : Bool :=
  decide (first + n ≤ G.ns) && (List.range n).all fun j => !G.gotF.getD (first + j) true

/-- What was heard at the seat: the lookup on the digits, or the one on the calls. -/
def heardAt (digits : Bool) (s : First.S) : Option Heard :=
  if digits then s.tl?.bind (·.heard) else s.lookHeard?

/-- **IN FRONT: PROMISED.** -/
def k3OnIn (p : First.Look.P) (s : First.S) : Bool :=
  match p.shape with
  | some h =>
    (heardAt p.digits s).isNone && First.Tape.RowsOwed.noneWaits s.rowsOwed &&
      s.fork?.any fun G =>
        G.next == p.first && sizedB G && freeB G p.first (Model.Forest.elems h)
  | none => false

/-! ## 2 Behind, up to the front of the batching -/

/-- **BEHIND: PROMISED.** -/
def k3OnOut (p : First.Look.P) (s : First.S) : Bool :=
  match p.shape, heardAt p.digits s, s.fork? with
  | some h, some g, some G =>
    sameShapeAll g.shape h && h.calls.size == h.NC &&
      g.zx.size == h.dT && g.zy.size == h.rK && g.zk.size == h.NC &&
      ((List.range h.calls.size).all fun c =>
        (g.zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0) &&
      decide (p.first + Model.Forest.elems h ≤ G.next) && sizedB G &&
      freeB G g.leaves.first (1 + 2 * h.d + 5) &&
      decide (p.first ≤ g.leaves.first) &&
      decide (g.leaves.first + (1 + 2 * h.d + 5) ≤ p.first + Model.Forest.elems h) &&
      (g.zb 0).size == h.kT + h.cK + 5 && (g.zb 1).size == h.kT + h.cK + 5
  | _, _, _ => false

end VerifiableInference.Desc.K3
