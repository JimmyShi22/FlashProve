-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySFollows.lean: the carry of a reading of written rounds (`Maps`,
OnBytes/Flat/CarrySMaps.lean) steps and skips as the list of the written rounds' weights says
(`Held.Follows`, OnBytes/Flat/CountsHeld.lean), and its written error counts are that file's.

CarrySMaps.lean has, for a reading M that is as asked, written counts `M.err ε` that bear the typed
counts ε (`Maps.fits`). CountsHeld.lean has the same for any `CarryS` that follows a list of weights
(`Held.fits_cnts`, at `Held.cnts`), and holds these counts below the planner's numbers. Here the two
vocabularies are joined, by recursion on the reading. Definitions and proofs.

Main names:
  `Maps.marks`: true where a written round is read as the next typed round, false where it is
    skipped.
  `Maps.follows`: `M.OK` gives `Held.Follows M.carry (Held.wsOf (ds.map toRD) M.marks)`.
  `Maps.err_eq_cnts`: `M.err ε` is `Held.cnts` at that list. `Maps.fits_cnts`: so the carry fits ε
    at these counts.
  `Maps.marks_app`: the marks of two readings in a row.
Limits: nothing on how large the counts are: that is `Held.cnts_below_held` and what it asks.
Nothing on soundness.
-/
import OnBytes.Flat.CarrySMaps
import OnBytes.Flat.CountsHeld

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice

namespace Maps

/-- True where a written round is read as the next typed round, false where it is skipped. -/
def marks : {ds : List RDT} → {s' : Shape} → Maps ds s' → List Bool
  | _, _, .nil => []
  | _, _, .step _ rest => true :: rest.marks
  | _, _, .skip _ rest => false :: rest.marks

theorem marks_app : ∀ {ds es : List RDT} {s' t' : Shape} (M : Maps ds s') (N : Maps es t'),
    (M.app N).marks = M.marks ++ N.marks
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .step _ rest, N => congrArg (true :: ·) (marks_app rest N)
  | _, _, _, _, .skip _ rest, N => congrArg (false :: ·) (marks_app rest N)

/-- **The carry steps and skips as the list of the written rounds' weights says.** -/
theorem follows : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s'), M.OK →
    Held.Follows M.carry (Held.wsOf (ds.map toRD) M.marks)
  | _, _, .nil, _ => trivial
  | _, _, .step (d := d) M rest, h =>
      ⟨fun _ c' => chalTo_fib (toRD d) M.g h.1.inj h.1.log c', fun _ _ => follows rest h.2⟩
  | _, _, .skip _ rest, h => fun _ _ => follows rest h

/-- The written counts are those of OnBytes/Flat/CountsHeld.lean. -/
theorem err_eq_cnts : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (ε : Err s'),
    M.err ε = Held.cnts (uLT (ckP .two) ds) (Held.wsOf (ds.map toRD) M.marks) s' ε
  | _, _, .nil, _ => rfl
  | _, _, .step (d := d) _ rest, (e, ε) =>
      congrArg (Prod.mk (e * (bsRound .two d.entry d.kind).w)) (err_eq_cnts rest ε)
  | _, _, .skip _ rest, ε => congrArg (Prod.mk 0) (err_eq_cnts rest ε)

/-- So the carry fits every typed count at these written counts. -/
theorem fits_cnts {ds : List RDT} {s' : Shape} (M : Maps ds s') (h : M.OK) (ε : Err s') :
    M.carry.Fits ε (Held.cnts (uLT (ckP .two) ds) (Held.wsOf (ds.map toRD) M.marks) s' ε) :=
  Held.fits_cnts M.carry _ ε (M.follows h)

end Maps

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.follows
#print axioms OnBytes.Flat.Maps.err_eq_cnts
#print axioms OnBytes.Flat.Maps.fits_cnts
