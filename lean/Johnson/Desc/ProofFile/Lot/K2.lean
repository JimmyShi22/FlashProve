-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K2.lean: THE CODE SWITCH's BLOCKS' MAKERS ALONE: FOR A DESCRIPTION OF THE
KINDS' OWN BLOCKS ALONE: a lot (letters := false; still := []; controls := []) whose own := the
switch alone at the links · H:2 · F:1, reached through no definition that
names socksOf | quietAround | stepsBlock | standIn. THIS FILE IMPORTS LotCore.lean AND Places.lean
(the records Pub · Ground · Lot; Spot · spotsOf), THE KIND's PLAIN TEXT (Kind · Finish · Head) AND
THE PLACES' NUMBERS OUT OF THE PLAN (K2OfPlan.lean): NO STRUCK | PLANTED |
LADDERED COPY, NO CONTROL.
  purePlaces      the places of the kind
  pureSpots       the same, each with its numbers
  pureLetters     the head's link's letters off the public records
  pureMute      a place at which the block cannot be made SPEAKS: planOk := false and a named
  refusal
  pureAt q      the kind's block at one place: «F:1»: finishPlace · «H:2»: the switch andThen
  headOpened · at a link: the switch, then what q gives (some none: the switch alone)
  lot       the switch ALONE at the links: FOR A FOLD THAT TAKES THE LINKS' FRAME FROM ITS OWN LOT
THE LOT's STEPS: ‹link›.0.call (3 | 23), the switch alone · H.1.call · H.1.quiet · F.0.front ·
F.0.call · F.0.quiet.
letters := false: no block of the kind reads a token of the request off the harness: the covered
positions are read off the carried record (S.covered); W · first · built are public.
-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.Places
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Desc.ProofFile.Lot.K2OfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot Lot spotsOf)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2

/-- The places of the kind, without their numbers. -/
def purePlaces (Z : Pub) : List Spot := ((spotsOf Z.cuts).getD []).filter fun sp =>
    sp.place.kind == .K2

/-- The places of the kind, each with its numbers. -/
def pureSpots (Z : Pub) (G : Ground) : List (Spot × P2) :=
    ((spotsOf Z.cuts).map (p2All Z G)).getD []

/-- The head's link's letters, off the public records. -/
def pureLetters (G : Ground) (l : Nat) : Option HeadPar :=
  (G.built[l]?).map fun X =>
    ⟨⟨X.name, X.kind, X.Fp, X.Tp, X.fv, X.NCL, X.arrayOf⟩, l, G.W.hS.V, G.W.hS.T, G.W.H, G.W.owner,
        (Verify.borderOf G.W.y).kxb⟩

/-- A place of the kind at which the block cannot be made speaks. -/
def pureMute (sp : Spot) (why : String) : Block S Unit :=
  { name := sp.name, place := sp.place, planOk := false, rounds := [], oracles := [], before := []
    decide := fun _ _ _ => .error why
    claims := []
    after := [] }

/-- The kind's block at one place. q: what follows the switch at a link (none: nothing can be made
there; some none: the switch alone). -/
def pureAt (q : Ground → Nat → Option (Option (Block S Unit))) (G : Ground) (x : Spot × P2) : Option
    (Block S Unit) :=
  let sp := x.1
  let under (b : Block S Unit) : Block S Unit := { b with name := sp.name, place := sp.place }
  match x.2.stands with
  | .finish => some (under (finishPlace x.2))
  | .head => (sp.place.link.bind (pureLetters G)).map fun P =>
      under ((codeSwitchKind x.2 : Block S Unit).andThen sp.name (headOpened sp.name sp.place P))
  | .link =>
    (sp.place.link.bind (q G)).map fun o =>
      match o with
      | some z => under ((codeSwitchKind x.2 : Block S Unit).andThen sp.name z)
      | none => under (codeSwitchKind x.2)

/-- All places of the kind. -/
def pureTable (q : Ground → Nat → Option (Option (Block S Unit))) (Z : Pub) (G : Ground) : List
    (Block S Unit) :=
  let made := pureSpots Z G
  (purePlaces Z).map fun sp =>
    match made.find? fun x => x.1.name == sp.name with
    | none => pureMute sp "N0: the place's numbers cannot be made of the plan's public records"
    | some x => (pureAt q G x).getD (pureMute sp "N0: the place's letters cannot be made")

def lot (Z : Pub) : Lot :=
  { name := "the code switch"
    letters := false
    own := pureTable (fun _ _ => some none) Z
    still := []
    controls := [] }

end P1K2
