-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeardShape.lean: the kind "lookup" (K3): WHAT THE BLOCK's YES LEAVES AS
THE HEARD SHAPE IS THE PLAN's OWN RECORD, at every record that Verify.publicOf returns, at the
lookup on the calls of every link. Statements and proofs: each puts two theorems together.
NO SOUNDNESS IS CLAIMED.

Why. A kind that hears behind the lookup takes what the lookup heard. Its texts run ranges by the
HEARD shape's numbers and hold them against the layout's. The layers' own kind tests seven numbers
and lists of the two shapes against each other (OnBytes/Desc/First/K4/Hear.lean: shapeFits), and not
the number of calls. Here all of the shape is shown to be the plan's, from the lookup's own yes.

Main names:
  `heard_shape`: where the block at the calls' seat, at parameters p, says yes: the heard record's
    shape is what p.shape returns.
  `heard_shape_lay`, `heard_shape_att`, `heard_shape_head`: at the place x that lookAt makes at a
    layers', an attention, the head's link: the heard shape is x.fs; at a layers' link that is
    X.y.fo.
  `heard_calls_lay`: so the heard shape has as many calls as the layout's: the premise hNC of
    Johnson/Desc/First/Look/PlanesPartsReturns.lean [not in this library].

Limits. One direction: from a yes of the block's decide and publicOf's equation. That the record
which a later kind is handed IS the one that the seat's `heard` returns behind that yes is the
description's own wiring, not shown here.
OBJECT: VerifiableInference.Desc.K3.block at K3.seatCalls (Johnson/Desc/First/Look/K3Lookup.lean): its
decide.
USER: none in this library yet. Meant for whoever holds a later kind's ranges, run by the heard
shape, against the layout's.
LETTERS: p := P.ofPlace set false x at the x that lookAt X i false returns; claim, piece, laid,
before, guests, set: free.
COMPILED IN TWO BUILDS, over two versions each of Johnson/Desc/Block.lean,
Johnson/Desc/First/State.lean, K3Lookup.lean and LookKind.lean. heard_shape's proof has two roads, tried
in turn: over the first build P.shape unfolds to the program's Forest.shape; over the second it goes
by the kind's own shapeOwn, and P.shape_older (Johnson/Desc/First/Look/LookKindAgrees.lean, which
lies beneath this file there) says the same of it. The driver's text and K3Own.lean do not lie
beneath this file. Over another version of the four it is to be compiled anew.
Compiled with the whole library.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3PointAtSeats
import Johnson.Desc.First.Look.K3CallerAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

section
variable {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
  (before : List (Nat × Nat)) (guests : List (Guest First.S Cl))
  {s s' : First.S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}

/-- **The heard shape is the parameters' own.** -/
theorem heard_shape (p : P)
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧ p.shape = some g.shape := by
  obtain ⟨g, hg, ⟨h0, e1, e2, e3⟩, -⟩ :=
    Desc.K3.block_point_calls claim piece laid before p guests H
  refine ⟨g, hg, ?_⟩
  first
    | (unfold P.shape
       rw [e1]
       dsimp only
       rw [e2, e3]
       rfl)
    | (rw [P.shape_older, e1]
       dsimp only
       rw [e2, e3]
       rfl)

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}
  (set : Params.Setting)

theorem heard_shape_lay (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X i false = some x) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) = 0)
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before (P.ofPlace set false x)
      guests).decide s rs cols = .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧ g.shape = X.y.fo := by
  obtain ⟨g, hg, e1⟩ := heard_shape claim piece laid before guests _ H
  obtain ⟨_, _, _, e2, _⟩ := lookAt_lay e hn h0
  rw [lay_shape set h e hn h0] at e1
  exact ⟨g, hg, by rw [← Option.some.inj e1, e2]⟩

/-- **The heard shape has as many calls as the layout's.** -/
theorem heard_calls_lay (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X i false = some x) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) = 0)
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before (P.ofPlace set false x)
      guests).decide s rs cols = .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧ g.shape.NC = X.y.fo.NC := by
  obtain ⟨g, hg, e1⟩ := heard_shape_lay claim piece laid before guests set h e hn h0 H
  exact ⟨g, hg, by rw [e1]⟩

theorem heard_shape_att (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X i false = some x) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before (P.ofPlace set false x)
      guests).decide s rs cols = .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧ g.shape = x.fs := by
  obtain ⟨g, hg, e1⟩ := heard_shape claim piece laid before guests _ H
  rw [att_shape set h e hn h0] at e1
  exact ⟨g, hg, (Option.some.inj e1).symm⟩

theorem heard_shape_head (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x)
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before (P.ofPlace set false x)
      guests).decide s rs cols = .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧ g.shape = x.fs := by
  obtain ⟨g, hg, e1⟩ := heard_shape claim piece laid before guests _ H
  rw [head_shape set h e] at e1
  exact ⟨g, hg, (Option.some.inj e1).symm⟩

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.heard_shape
#print axioms VerifiableInference.Desc.First.Look.heard_shape_lay
#print axioms VerifiableInference.Desc.First.Look.heard_calls_lay
#print axioms VerifiableInference.Desc.First.Look.heard_shape_att
#print axioms VerifiableInference.Desc.First.Look.heard_shape_head
