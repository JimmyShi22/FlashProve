-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PubWide.lean: the composed public tests (`pubAll`,
Johnson/Desc/First/PubAll.lean) with the tests of the names that have left the table laid over
them again. Definitions with code and theorems. No Mathlib.
Why. Thirteen names have left the table's list of extra public tests
(Johnson/Desc/First/SmallDoor.lean). Ties that were typed while these names still stood there
speak of a WIDER meaning. A bridge (Johnson/Desc/Sound/PlusDoorA.lean) carries such a tie to the
narrower meaning; it wants the wider tests as ONE function that agrees with the narrower one
outside the names that left. This file gives that function once, for all authors.
  `classA q`: the public item q is one of the names that left.
  `pubWide d12 dP D base`: over `pubAll D base`: the pending claim's and the approximate range
    proof's four names, the proximity test's four, the weights' name, "frame.liveIs", the last
    sub-protocols' three: each by its own authors' function.
  `pubK3Live_else`, `pubWeights_else`, `pubK12_else`: each of these functions hands on what is not
    its own.
  `pubWide_hand`: **outside `classA` the wider function IS the narrower one.**
  `pubWide_bookInOrder` ... `pubWide_room`: at each of the thirteen names it is its authors' own
    test.
Limits: definitions and unfoldings. No soundness is claimed.

-/
import Johnson.Desc.First.PubAll
import Johnson.Desc.First.SmallDoor
import Johnson.Desc.First.FillWeights
import Johnson.Desc.K12.Door.FillK12
import Johnson.Top.H0.Fill.FillP1Plus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.K12.Door (K12Data pubK12 k12Item atFirstBook atFirstSeats
  atFirstShapes atFirstFits)
open VerifiableInference.Desc.K13 (pubK13PlusC k13PlusItemC pubK13PlusC_else pileMasksC pileWithinC
  oneRowC)
open VerifiableInference.Desc.First.Look (pubK3Live k3LiveItem liveIsC)
open VerifiableInference.Desc.First.FillP1 (PlusData pubPlus plusItem pubPlus_else)

/-- The public item is one of the names that left the table's list of extra public tests. -/
def classA : Pub → Bool
  | .more sg name => leavesName (sg, name)
  | _ => false

/-- **The composed public tests, with the tests of the names that left laid over them again.** -/
def pubWide {P : Type} (d12 : K12Data) (dP : PlusData) (D : PubData) (base : Pub → P × S → Bool) :
    Pub → P × S → Bool :=
  pubK13PlusC (pubK3Live D.d3 (pubWeights (pubK12 d12 (pubPlus dP (pubAll D base)))))

theorem ne_of_notA (sg : Option Nat) (name lit : String) (hl : leavesName (sg, lit) = true)
    (h : classA (.more sg name) = false) : (name == lit) = false := by
  cases e : name == lit with
  | false => rfl
  | true =>
    have e' : name = lit := by simpa using e
    subst e'
    have h' : leavesName (sg, name) = false := h
    rw [hl] at h'
    cases h'

section
variable {P : Type} (f : Pub → P × S → Bool) (q : Pub) (a : P × S)

theorem pubK3Live_else (d : Look.K3Data) (h : k3LiveItem q = false) :
    pubK3Live d f q a = f q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => rfl
    | some m =>
      have e : (name == "frame.liveIs") = false := h
      show (if (name == "frame.liveIs") = true then liveIsC d a.2
        else f (.more (some m) name) a) = _
      rw [e]
      rfl
  | _ => rfl

theorem pubWeights_else (h : weightsItem q = false) : pubWeights f q a = f q a := by
  unfold pubWeights
  split
  · rename_i name
    simp only [weightsItem] at h
    rw [if_neg (by simp [h])]
  · rfl

theorem pubK12_else (d : K12Data) (h : k12Item q = false) : pubK12 d f q a = f q a := by
  unfold pubK12
  split
  · rename_i name
    simp only [k12Item, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.1.1.1]), if_neg (by simp [h.1.1.2]), if_neg (by simp [h.1.2]),
      if_neg (by simp [h.2])]
  · rfl

end

section
variable {P : Type} (d12 : K12Data) (dP : PlusData) (D : PubData) (base : Pub → P × S → Bool)

/-- **Outside the names that left, the wider function is the narrower one.** -/
theorem pubWide_hand (q : Pub) (h : classA q = false) (a : P × S) :
    pubWide d12 dP D base q a = pubAll D base q a := by
  have h1 : k13PlusItemC q = false := by
    cases q with
    | more sg name =>
      cases sg with
      | some m => rfl
      | none =>
        show (true && (name == "K13.pileMasks" || name == "K13.pileWithin" ||
          name == "K13.oneRow")) = false
        rw [ne_of_notA none name "K13.pileMasks" rfl h, ne_of_notA none name "K13.pileWithin" rfl h,
          ne_of_notA none name "K13.oneRow" rfl h]
        rfl
    | _ => rfl
  have h2 : k3LiveItem q = false := by
    cases q with
    | more sg name =>
      cases sg with
      | none => rfl
      | some m => exact ne_of_notA (some m) name "frame.liveIs" rfl h
    | _ => rfl
  have h3 : weightsItem q = false := by
    cases q with
    | more sg name =>
      cases sg with
      | some m => rfl
      | none => exact ne_of_notA none name "K13.weightsOk" rfl h
    | _ => rfl
  have h4 : k12Item q = false := by
    cases q with
    | more sg name =>
      cases sg with
      | some m => rfl
      | none =>
        show (name == "K12.bookInOrder" || name == "K12.seatsCarried" || name == "K12.msgShapes" ||
          name == "K12.bookFits") = false
        rw [ne_of_notA none name "K12.bookInOrder" rfl h,
          ne_of_notA none name "K12.seatsCarried" rfl h,
          ne_of_notA none name "K12.msgShapes" rfl h, ne_of_notA none name "K12.bookFits" rfl h]
        rfl
    | _ => rfl
  have h5 : plusItem q = false := by
    cases q with
    | more sg name =>
      cases sg with
      | none => rfl
      | some m =>
        show (name == "K8.lay7" || name == "K8.onThird" || name == "K8.funsThird" ||
          name == "pile.room") = false
        rw [ne_of_notA (some m) name "K8.lay7" rfl h, ne_of_notA (some m) name "K8.onThird" rfl h,
          ne_of_notA (some m) name "K8.funsThird" rfl h,
          ne_of_notA (some m) name "pile.room" rfl h]
        rfl
    | _ => rfl
  unfold pubWide
  rw [pubK13PlusC_else _ q h1 a, pubK3Live_else _ q a D.d3 h2, pubWeights_else _ q a h3,
    pubK12_else _ q a d12 h4, pubPlus_else dP _ q h5 a]

theorem pubWide_bookInOrder (a : P × S) :
    pubWide d12 dP D base (.more none "K12.bookInOrder") a = atFirstBook d12.ft a.2 := rfl

theorem pubWide_seatsCarried (a : P × S) :
    pubWide d12 dP D base (.more none "K12.seatsCarried") a = atFirstSeats d12.L a.2 := rfl

theorem pubWide_msgShapes (a : P × S) :
    pubWide d12 dP D base (.more none "K12.msgShapes") a = atFirstShapes d12.M a.2 := rfl

theorem pubWide_bookFits (a : P × S) :
    pubWide d12 dP D base (.more none "K12.bookFits") a = atFirstFits a.2 := rfl

theorem pubWide_weightsOk (a : P × S) :
    pubWide d12 dP D base (.more none "K13.weightsOk") a = weightsB a.2 := rfl

theorem pubWide_pileMasks (a : P × S) :
    pubWide d12 dP D base (.more none "K13.pileMasks") a = pileMasksC a.2 := rfl

theorem pubWide_pileWithin (a : P × S) :
    pubWide d12 dP D base (.more none "K13.pileWithin") a = pileWithinC a.2 := rfl

theorem pubWide_oneRow (a : P × S) :
    pubWide d12 dP D base (.more none "K13.oneRow") a = oneRowC a.2 := rfl

theorem pubWide_liveIs (m : Nat) (a : P × S) :
    pubWide d12 dP D base (.more (some m) "frame.liveIs") a = liveIsC D.d3 a.2 := rfl

theorem pubWide_lay7 (m : Nat) (a : P × S) :
    pubWide d12 dP D base (.more (some m) "K8.lay7") a =
      (dP.tl m).any fun tlP => K8.Ready.lay7B tlP a.2 := rfl

theorem pubWide_onThird (m : Nat) (a : P × S) :
    pubWide d12 dP D base (.more (some m) "K8.onThird") a = K8.Ready.onThirdB a.2 := rfl

theorem pubWide_funsThird (m : Nat) (a : P × S) :
    pubWide d12 dP D base (.more (some m) "K8.funsThird") a = K8.Ready.funsThirdB a.2 := rfl

theorem pubWide_room (m : Nat) (a : P × S) :
    pubWide d12 dP D base (.more (some m) "pile.room") a =
      Johnson.Desc.First.Walk.Tied.roomIsB dP.free0 dP.fvs m a.2 := rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.pubWide_lay7
#print axioms VerifiableInference.Desc.First.pubWide_onThird
#print axioms VerifiableInference.Desc.First.pubWide_funsThird
#print axioms VerifiableInference.Desc.First.pubWide_room
#print axioms VerifiableInference.Desc.First.pubWide_hand
#print axioms VerifiableInference.Desc.First.pubWide_bookInOrder
#print axioms VerifiableInference.Desc.First.pubWide_seatsCarried
#print axioms VerifiableInference.Desc.First.pubWide_msgShapes
#print axioms VerifiableInference.Desc.First.pubWide_bookFits
#print axioms VerifiableInference.Desc.First.pubWide_weightsOk
#print axioms VerifiableInference.Desc.First.pubWide_pileMasks
#print axioms VerifiableInference.Desc.First.pubWide_pileWithin
#print axioms VerifiableInference.Desc.First.pubWide_oneRow
#print axioms VerifiableInference.Desc.First.pubWide_liveIs
