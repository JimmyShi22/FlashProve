-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/Via/Via.lean: the kind "lookup" (K3) at a proof file's link: the block of
Johnson/Desc/First/Look/K3Lookup.lean with the hearing exchanged for the hearing on a view's rounds.
Definitions alone; it imports no proof.

Main names:
  `hearVia`: `hearV` (Johnson/Desc/First/Look/Via/Rounds.lean) at the face of the place's shape, led
    back to the verifier program's record by `toHeardG` and `toHeard`. It reads no entry of the
    plan.
  `fitsVia`: a test on the plan alone: the plan's entries are, but for the work bits, those that the
    hearing goes by (`entriesFit`), and each passes the tests of the strict reading of a round that
    read the entry alone (`staticT`, Johnson/Desc/First/Look/Via/Static.lean).
  `decideVia`: K3Lookup.lean's `decide`, line for line, the refusals' names too, with `hearVia` in
    `hear`'s place.
  `blockVia`: K3Lookup.lean's `block`, field by field and written out, so that it does not name
    K3.block: planOk asks `fitsVia` besides; decide is `decideVia`; name, place, rounds, oracles,
    before, the runs "objects" and "guests", and after are K3.block's.

The namespace is VerifiableInference.Desc.K3.Law, so that these names can be loaded beside other
definitions of the same short names in VerifiableInference.Desc.K3.

Limits. No theorem stands here: that `decideVia` says yes only where K3.block's decide does is a
matter for files that import this one. If K3Lookup.lean's `decide` or `block` turns, this text does
not follow by itself. The limits of Rounds.lean's head hold of `hearVia`. Where the place's shape
has fewer than two calls `hearVia` says no (its test 1 < h.NC), as K3Lookup.lean's own `hear` does.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.First.Look.Via.Static

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.Law
open OnBytes
open OnBytes.Model (Fork Aff)
open First.Look (P Guest)

/-- **In the place of K3Lookup.lean's `hear`**: hearV at the shape's face, led back to the program's
record. It reads no entry of the plan. -/
def hearVia (p : P) (F : Fork) (rs : List Fmt.RoundView) : Option (Model.Forest.Heard × Fork) :=
  match p.shape with
  | some h =>
    if 1 < h.NC then
      (hearV (faceOf h) F rs).bind fun x =>
        (toHeard h (toHeardG x.1)).map fun g => (g, x.2)
    else none
  | none => none

/-- **The two public premises of the laws, as one test on the plan**: the plan's entries are, but
for the work bits, those that the hearing goes by; and each passes the strict reading's tests that
read the entry alone. -/
def fitsVia (p : P) : Bool :=
  match p.shape with
  | some h => entriesFit (faceOf h) (p.entries.getD []) && (p.entries.getD []).all staticT
  | none => false

/-- K3Lookup.lean's own decide, line for line, with the hearing alone exchanged. -/
def decideVia {S Cl : Type} (seat : Seat S Cl) (p : P) (s : S) (rs : List Fmt.RoundView) :
    Except String S := do
  let F ← named "K3: no sub-proof is open" (seat.fork s)
  need "K3: nothing is heard yet" (seat.heard s).isNone
  need "K3: rows are owed in front" (seat.owed s).noneWaits
  need "K3: the ledger's count of slots" (F.next == p.first)
  let x ← named "K3: the hearing" (hearVia p F rs)
  pure (seat.put s x.1 x.2)

/-- **K3Lookup.lean's own block with the hearing exchanged**, written out. -/
def blockVia {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) :
    KindWithGuestIdentities P (Guest S Cl) S Cl := fun p guests =>
  { name := p.name
    place := ⟨1, some p.link, piece, .K3⟩
    planOk := planOk p laid guests && fitsVia p
    rounds := p.rounds
    oracles := p.rounds.map fun _ => []
    before := before
    decide := fun s rs _ => decideVia seat p s rs
    claims :=
      [("objects", fun _ s => do
        let F ← named "K3 objects: no sub-proof is open" (seat.fork s)
        let g ← named "K3 objects: nothing was heard" (seat.heard s)
        pure (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects))),
       ("guests", fun _ s =>
        named "K3 guests: a guest refuses"
          ((guests.mapM fun (g : Guest S Cl) => g.form s).map fun l => (l, s)))]
    after := [] }

end VerifiableInference.Desc.K3.Law
