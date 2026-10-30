-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieTwo.lean (over Johnson/IMR/HandsFence.lean): THE TABLE OF JOINTS' PROMISE BEHIND A
SUB-PROTOCOL WHOSE ROW OPENS CLASSES OF ROWS AND PINS, FROM «HandsR» AND WHAT THE STRINGS' SIDE
GIVES. A rule over letters, free of the kind; typed for the code switch's tie t2. NO BLOCK IMPORTS
THIS FILE.
NEAREST KIN: onAt_step_held (Johnson/Desc/First/PromiseRides.lean): the promise rides
past a sub-protocol whose row is QUIET (it closes and opens no class of rows and no pin). A
switch's row is not quiet: here every clause is asked at the open set BEHIND.
  pubAt · EQ Mg links ps z   the open public items at a border · the two tests of the promise that
                             Hands' four do not hold: «in order» and the public items' test
                             (pubHeld), at the public part z, as the letter E of Hands
  xk_of_on       the promise at border k at an unmarked state gives X k at E := EQ
  on_of_handsR   HandsR Fk … (EQ Mg links ps z) ft k B · Fk k s · an accept of B from s to s' · s
                 unmarked · the promise in front · behind: «the stored table decodes» · and, where
                 s' is unmarked: the state holds the OOD sample of every tenant whose pin is open
                 behind · each such tenant's tree shows all leaves and has no collision · what the
                 open public items say beside their tests: THE PROMISE BEHIND (onAt at border k +
                 1)
LIMITS. A rule: its premises are the whole work. No soundness is claimed.
-/
import Johnson.IMR.HandsFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.First (S ModelPart Numbers Item Pub Meaning onAt pubHeld pubSets
  samplesHeld sampledIn)
open ProofFile (Cl)
open IM (HandsR XK BK Yes xk_parts openAt)

variable {P W : Type}

/-- The public items that are open at border k. -/
def pubAt (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : Nat) : List Pub :=
  ((pubSets Mg.more links ps)[k]?).getD []

/-- «In order» and the public items' test, at the public part z. -/
def EQ (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (z : P) (k : Nat) (s : S) : Bool :=
  Mg.inOrder (z, s) && pubHeld Mg (openAt links ps k) (pubAt Mg links ps k) (z, s)

theorem xk_of_on {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {k : Nat} {s : S} {y : Strs}
    (ha : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, s) y)
    (hu : s.failed = none) : XK N links ps (EQ Mg links ps z) k s = true := by
  rcases ha.2 with hm | ⟨hB, _⟩
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at hB
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hB
    unfold XK BK EQ
    rw [h1, h2, h3, h4, h5, h6]
    rfl

theorem on_of_handsR {Fk : Nat → S → Prop} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {z : P} {ft k : Nat} {B : Block S Cl}
    (H : HandsR Fk N links ps (EQ Mg links ps z) ft k B) {s s' : S} {y y' : Strs}
    (hf : Fk k s) (hy : Yes ft B s s') (hu : s.failed = none)
    (ha : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, s) y)
    (hDec : Mg.decodes (z, s') y')
    (hHeld : s'.failed = none → samplesHeld N Mg (openAt links ps (k + 1)) (z, s') = true)
    (hSN : s'.failed = none → ∀ x ∈ sampledIn N (openAt links ps (k + 1)),
      Mg.shown x.1 x.2 y' ∧ Mg.noColl x.1 x.2 (z, s') y')
    (hPP : s'.failed = none → ∀ q ∈ pubAt Mg links ps (k + 1), Mg.pubP q (z, s')) :
    onAt N Mg links ps[k + 1]? (openAt links ps (k + 1)) (pubAt Mg links ps (k + 1)) (z, s') y' :=
        by
  refine ⟨hDec, ?_⟩
  by_cases hb : s'.failed = none
  · right
    have hx := H.step hf hy hu hb (xk_of_on ha hu)
    obtain ⟨c1, c2, c3, c4, c5⟩ := xk_parts hx
    unfold EQ at c5
    rw [Bool.and_eq_true] at c5
    refine ⟨?_, hHeld hb, hSN hb, hPP hb⟩
    rw [c1, c2, c3, c5.1, c5.2, c4]
    rfl
  · left
    exact hb

end P1K2

#print axioms P1K2.xk_of_on
#print axioms P1K2.on_of_handsR
