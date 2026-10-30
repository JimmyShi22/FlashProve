-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3FillCode.lean (CUT IN TWO: the door's name «frame.liveIs» has
a thin half of its own): the kind "lookup" (K3): ITS LAYER OF THE FILLING OF THE TABLE OF JOINTS'
MEANING: THE HALF WITH CODE: pubK3 d f: what K3's public items say of the verifier's state, as
Bools, over whatever function f says the other items. Definitions alone. NO MATHLIB beneath it: so
the layers' halves can be composed and run without a Meaning.

Main names.
  K3Data: the layer's data: the public parameters X, and of the plan's data the request's shape, the
    rows' layout and, link by link, the table of arrays.
  k3SortAt X m pc: which of segment m's two lookups stands at piece pc (by K3.pieceAt): some true:
    on the digits; some false: on the calls; none: neither.
  lookInC, lookOutC, linkFreshC, liveIsC: the four Bools. EACH IS, BY rfl
    (Johnson/Desc/First/Look/K3Fill.lean), THE BOOL OF THE LOOKUPS' LAWS: k3LookInAt, k3OnOutAt
    (K3BoolsAt.lean), linkFreshB (K3CallsKeeps.lean), liveIsB (K3LiveIs.lean), whose files stand
    above Mathlib: so their texts are written out here once more.
  k3Item d q: is the item one of this layer's? k3LiveItem q: is it the door's name «frame.liveIs» of
    a segment?
  pubK3 d f: THE HALF WITH CODE: lookIn m pc, lookOut m pc by the sort of the piece · linkFresh m ·
    left m, leftOn m := true (what they say is pubP's) · every other item is handed on to f.
  pubK3Live d f: THE THIN HALF: the door's item (some m, "frame.liveIs") := liveIsC; every other
    item is handed on to f.
OBJECT. No block's text: Bools on the public parameters and the verifier's state.
USER. fillK3 (K3Fill.lean); the table's files' composed half.
LETTERS. d, f.

Compiled with the whole library.
Limits. Definitions: nothing is proved. At this term nothing has run.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.K3Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (Pub)

/-- **The layer's data.** -/
structure K3Data where
  /-- the public parameters -/
  X : Verify.Public
  /-- the request's shape, by the plan -/
  shape : Params.ReqShape
  /-- the rows' layout, by the plan -/
  layout : Params.ReqLayout
  /-- link by link, for each array of the sub-proof's list: the link that sent it, its name -/
  arrayOf : Array (Array (Nat × String))

/-- Which of segment m's two lookups stands at piece pc. -/
def k3SortAt (X : Verify.Public) (m pc : Nat) : Option Bool :=
  if pc == Desc.K3.pieceAt X m true then some true
  else if pc == Desc.K3.pieceAt X m false then some false
  else none

/-- The lookup's condition in front of its block. -/
def lookInC (d : K3Data) (m : Nat) (dg : Bool) (s : First.S) : Bool :=
  (placeAt d.X m dg).any fun p =>
    Desc.K3.k3OnIn p s && s.link?.any fun L => L.link == p.link && L.arrayOf == d.arrayOf.getD m #[]

/-- And behind it, up to the batching. -/
def lookOutC (d : K3Data) (m : Nat) (dg : Bool) (s : First.S) : Bool :=
  (placeAt d.X m dg).any fun p => Desc.K3.k3OnOut p s

/-- Nothing is heard at the digits' seat, and the open link's table of arrays is the plan's. -/
def linkFreshC (d : K3Data) (m : Nat) (s : First.S) : Bool :=
  (s.tl?.bind (·.heard)).isNone && s.link?.any fun L => L.arrayOf == d.arrayOf.getD m #[]

/-- The live request's shape and its rows' layout are the plan's. -/
def liveIsC (d : K3Data) (s : First.S) : Bool :=
  decide (s.live.frame.shape = d.shape) && decide (s.live.rows.layout = d.layout)

/-- Is the item one of this layer's? -/
def k3Item (d : K3Data) : Pub → Bool
  | .lookIn m pc => (k3SortAt d.X m pc).isSome
  | .lookOut m pc => (k3SortAt d.X m pc).isSome
  | .linkFresh _ => true
  | .left _ => true
  | .leftOn _ => true
  | _ => false

/-- **THE LAYER's HALF WITH CODE**: over whatever says the other items. -/
def pubK3 {P : Type} (d : K3Data) (f : Pub → P × First.S → Bool) : Pub → P × First.S → Bool :=
  fun q a =>
    match q with
    | .lookIn m pc =>
      match k3SortAt d.X m pc with
      | some dg => lookInC d m dg a.2
      | none => f (.lookIn m pc) a
    | .lookOut m pc =>
      match k3SortAt d.X m pc with
      | some dg => lookOutC d m dg a.2
      | none => f (.lookOut m pc) a
    | .linkFresh m => linkFreshC d m a.2
    | .left _ => true
    | .leftOn _ => true
    | q => f q a

/-- Is the item the door's name "frame.liveIs" of a segment? -/
def k3LiveItem : Pub → Bool
  | .more (some _) name => name == "frame.liveIs"
  | _ => false

/-- **THE THIN HALF WITH CODE FOR THAT ONE NAME**: over whatever says the other items. -/
def pubK3Live {P : Type} (d : K3Data) (f : Pub → P × First.S → Bool) : Pub → P × First.S → Bool :=
  fun q a =>
    match q with
    | .more (some m) name =>
      if name == "frame.liveIs" then liveIsC d a.2 else f (.more (some m) name) a
    | q => f q a

end VerifiableInference.Desc.First.Look
