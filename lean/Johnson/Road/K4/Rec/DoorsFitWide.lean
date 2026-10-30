-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/DoorsFitWide.lean: THE BRIDGE's TEST ON THE TWO LISTS OF EXTRA PUBLIC TESTS,
`doorsFitB` (Johnson/Desc/Sound/PlusDoorA.lean), EVALUATED BY LEAN's KERNEL at the border in front
of and at the border behind K4's sub-protocol, at each of its twelve places of the written list of
25 segments: at the composed meaning's own list `moreAll` (Johnson/Desc/Sound/MoreAll.lean), the
wider meaning's list `moreWideAll` (Johnson/Desc/Sound/MgWide.lean) and the class `classA` of the
names that have left (Johnson/Desc/First/PubWide.lean); with negative tests; and as a theorem at
the two terms.

  `k4DoorsFit M₀ M cA links ps`: `doorsFitB` at both borders, at every place of K4's.
  `doors_of_fit`: its law, general in the two lists and the class. Premises: H (in the caller's
    hand) · the accept.
  **`k4_doorsFit_wide`**: BY THE KERNEL: it accepts; the places are twelve.
  `k4_doorsFit_noClass`: A NEGATIVE TEST: with the empty class the test rejects in front of K4's
    sub-protocol at each of the twelve.
  `k4_doorsFit_swapped`: A NEGATIVE TEST: so it does with the two lists swapped.
  **`doorsFit_mgWide`**: at a place of K4's: the test accepts at both borders at the fields more of
    `mgAll Dm mgBase` and of the wider meaning over it (`moreW Dm mgBase`), at every Dm.
Limits. One of the bridge's premises, at K4's twenty-four borders alone. The bridge's other
premises (the facts at the reached states among them) are not touched. THE LIST OF SEGMENTS IS
WRITTEN (`linksFull`), not read off the public parameters. The base is `mgBase`. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.PlanTests
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Pub More flatPlacesOf classA)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (linksFull moreAll moreWideAll MgData mgAll mgBase moreW
  moreW_base mgAll_more_base mgMore_is doorsFitB)

/-- The test on the two lists at both borders of K4's sub-protocol, at every place of K4's. -/
def k4DoorsFit (M₀ M : More) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k _ => doorsFitB M₀ M cA links ps k && doorsFitB M₀ M cA links ps (k + 1)

/-- What an accept gives at a place of K4's. -/
theorem doors_of_fit {M₀ M : More} {cA : Pub → Bool} {links : List ModelPart} {ps : List Place}
    {k m : ℕ} {pl : Place} (H : AtK4 links ps k m pl)
    (h : k4DoorsFit M₀ M cA links ps = true) :
    doorsFitB M₀ M cA links ps k = true ∧ doorsFitB M₀ M cA links ps (k + 1) = true := by
  have h1 := atK4s_at
    (t := fun k _ => doorsFitB M₀ M cA links ps k && doorsFitB M₀ M cA links ps (k + 1)) H h
  rw [Bool.and_eq_true] at h1
  exact h1

set_option maxRecDepth 1000000 in
theorem k4_doorsFit_wide :
    (k4DoorsFit moreAll moreWideAll classA linksFull (flatPlacesOf linksFull true) &&
      ((flatPlacesOf linksFull true).countP (isK4At linksFull) == 12)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with the empty class the test rejects at every place of K4's. -/
theorem k4_doorsFit_noClass :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k _ =>
      !doorsFitB moreAll moreWideAll (fun _ => false) linksFull (flatPlacesOf linksFull true)
        k) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with the two lists swapped the test rejects at every place of K4's. -/
theorem k4_doorsFit_swapped :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k _ =>
      !doorsFitB moreWideAll moreAll classA linksFull (flatPlacesOf linksFull true) k) = true := by
  decide +kernel

/-- **The bridge's test on the two lists, at the two terms.** -/
theorem doorsFit_mgWide {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi P Tok rows cols nR X) {k m : ℕ} {pl : Place}
    (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) :
    doorsFitB (mgAll Dm mgBase).more (moreW Dm mgBase) classA linksFull
        (flatPlacesOf linksFull true) k = true ∧
      doorsFitB (mgAll Dm mgBase).more (moreW Dm mgBase) classA linksFull
        (flatPlacesOf linksFull true) (k + 1) = true := by
  rw [mgAll_more_base, mgMore_is, moreW_base]
  have h := k4_doorsFit_wide
  rw [Bool.and_eq_true] at h
  exact doors_of_fit H h.1

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.doors_of_fit
#print axioms OnBytes.Road.K4.Rec.k4_doorsFit_wide
#print axioms OnBytes.Road.K4.Rec.k4_doorsFit_noClass
#print axioms OnBytes.Road.K4.Rec.k4_doorsFit_swapped
#print axioms OnBytes.Road.K4.Rec.doorsFit_mgWide
