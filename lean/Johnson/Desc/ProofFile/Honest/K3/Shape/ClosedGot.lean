-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ClosedGot.lean: THE LEDGER's MARKS BEHIND A LOOKUP's HEARING,
ON THE CODE, IN CLOSED FORM: what `runOps` and `lookUpd` (Honest/K3/Shape/Ops.lean) do to the
shape's list got (for each slot: is it filled?), as an equation of lists; and a second text for
lookUpd that lays the marks by that closed form and is equal to lookUpd at every face and every
shape. Three definitions, seven theorems. General; nothing is evaluated.

Why. A step `.sum o e` lays got := fillB (fillB L.got (L.next + o) e) L.next o: two fills, each
"take ++ replicate ++ drop" over the whole list; a lookup has many such steps, one upon the other.
Whoever makes the list behind the lookup whole walks every one of these layers at every slot. TIMED
TRIALS, OUTSIDE THE LIBRARY, NOT SHOWN HERE (Lean's kernel alone, "lean -j1
--tstack=131072"; the stored full-size example; a ledger of 4,190 slots; the run on shapes over the
eight members 15 to 22, which hold two lookups; each figure the resident peak of a process of its
own). Three processes of one job, over a working copy of the library: asked only whether the run
returns 17.9 GiB; the marks compared with a written list besides, which makes them whole, 29.2 GiB;
the value less look and lookHeard compared with a written one (lessB,
Johnson/AtFull/Shape/JoinPieces.lean) 31.3 GiB. Two further jobs, over another working copy of the
library: that last line 31.3
GiB; the same line with lookUpdL at the ledger's seat of both lookups
(Johnson/AtFull/Shape/LookLight.lean), over this file's code, 18.0 GiB. Why that wins more than the
marks cost was not looked into.

What is shown.
  `marks_ext`: two lists of marks of one length with the same mark at every place are one list.
  `fill_next`: a fill and the next fill right behind it are one fill. `fill_front`: a fill and then
    the fill right in front of it are one fill. Each under room.
  `spans l a n`: the stretches that the steps l fill, where the open stretch begins at a and is n
    long so far: a `.sum` lengthens the open stretch; a `.left` closes it and opens an empty one
    behind its own slots; an `.owe` does nothing. `fillAll g xs`: the stretches filled in turn.
  **`runOps_got`**: L.got = fillB g a n → L.next = a + n → a + n + (the steps' lengths' sum) ≤
    g.length → (runOps l L).got = fillAll g (spans l a n).
  **`lookUpd_got`**: L.next + (the lookup's steps' lengths' sum) ≤ L.got.length → (lookUpd f L).got
    = fillAll L.got (spans (lookOps f) L.next 0).
  `setGot_self`: a shape with its own marks laid anew is itself.
  `lookUpdL f L`: where that room is there: lookUpd f L with the marks laid by the closed form;
    where it is not: lookUpd f L. **`lookUpdL_eq`**: lookUpdL f L = lookUpd f L. No hypothesis.

Hypotheses that remain. Room: the stretch lies inside the list. It is asked for more than is needed.
fill_front fails without any: at g = [false], a = 0, o = 2, e = 1 the left side is [true, true], the
right [true, true, true] (by hand); by a reader's argument, and by that reader's program over small
cases, a + o ≤ g.length would do for it, and fill_next holds with no premise at all: neither is
shown here; the one caller has the room. So lookUpdL's test is enough for the closed form and is not
shown to be needed. lookUpdL asks the room by a test with code, so lookUpdL_eq has no hypothesis.

Terms. Honest/K3/GLOSSARY.md: see there ledger, slot, hearing, face and shape (of the ledger: LedSh,
Johnson/Desc/First/Shape/Parts.lean). A mark is an entry of the shape's list got. A stretch, here:
slots that touch and are filled by steps that touch. ClosedMarks.lean [not in this library], beside
this file, has the marks outside all of a lookup's slots, pointwise; this file has the whole list.

Users. Johnson/AtFull/Shape/LookLight.lean imports this file.

Taken as they stand: fillB_get, fillB_length (Honest/K3/Shape/Window.lean), fillB_zero
(Honest/K3/Shape/Atoms.lean), Op.len (Honest/K3/Shape/Closed.lean).

Limits. Equations of lists and of ledgers' shapes. HOW MANY STRETCHES spans (lookOps f) a 0 HAS IS
NOT SHOWN: by its text one more than the list has steps `.left`; lookOps f has one, next to last, so
two: read off the texts, no theorem. That the lengths' sum is the face's number of slots is
lookOps_len's (Closed.lean), under f.ok; it is not spent here. Nothing says that a hearing returns,
or that any ledger has room. What either text costs whoever evaluates it is not said by any theorem.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Window
import Johnson.Desc.ProofFile.Honest.K3.Shape.Atoms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open VerifiableInference.Desc.First.Shape (LedSh fillB)

local notation "KFace" => VerifiableInference.Desc.K3.Face

/-! ## 1 Fills that touch -/

/-- Two lists of marks of one length with the same mark at every place are one list. -/
theorem marks_ext {a b : List Bool} (hl : a.length = b.length)
    (h : ∀ j : Nat, a[j]?.getD false = b[j]?.getD false) : a = b := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have e := h i
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at e
  exact e

/-- **A fill, and the next fill right behind it, are one fill.** Conditional on room. -/
theorem fill_next (g : List Bool) (a n m : Nat) (h : a + n + m ≤ g.length) :
    fillB (fillB g a n) (a + n) m = fillB g a (n + m) := by
  have l1 : (fillB g a n).length = g.length := fillB_length g a n (by omega)
  refine marks_ext ?_ fun j => ?_
  · rw [fillB_length _ _ _ (by rw [l1]; omega), l1, fillB_length _ _ _ (by omega)]
  · rw [fillB_get _ _ _ _ (by rw [l1]; omega), fillB_get g a n j (by omega),
      fillB_get g a (n + m) j (by omega)]
    by_cases c1 : a + n ≤ j ∧ j < a + n + m
    · rw [if_pos c1, if_pos (by omega)]
    · rw [if_neg c1]
      by_cases c2 : a ≤ j ∧ j < a + n
      · rw [if_pos c2, if_pos (by omega)]
      · rw [if_neg c2, if_neg (by omega)]

/-- **A fill, and then the fill right in front of it, are one fill.** Conditional on room. -/
theorem fill_front (g : List Bool) (a o e : Nat) (h : a + o + e ≤ g.length) :
    fillB (fillB g (a + o) e) a o = fillB g a (o + e) := by
  have l1 : (fillB g (a + o) e).length = g.length := fillB_length g (a + o) e (by omega)
  refine marks_ext ?_ fun j => ?_
  · rw [fillB_length _ _ _ (by rw [l1]; omega), l1, fillB_length _ _ _ (by omega)]
  · rw [fillB_get _ _ _ _ (by rw [l1]; omega), fillB_get g (a + o) e j (by omega),
      fillB_get g a (o + e) j (by omega)]
    by_cases c1 : a ≤ j ∧ j < a + o
    · rw [if_pos c1, if_pos (by omega)]
    · rw [if_neg c1]
      by_cases c2 : a + o ≤ j ∧ j < a + o + e
      · rw [if_pos c2, if_pos (by omega)]
      · rw [if_neg c2, if_neg (by omega)]

/-! ## 2 A list of steps -/

/-- The stretches that a list of steps fills. a: where the open stretch begins; n: how long it is so
far. Each stretch as (its first slot, its length); any of them may be empty. -/
def spans : List Op → Nat → Nat → List (Nat × Nat)
  | [], a, n => [(a, n)]
  | .sum o e :: l, a, n => spans l a (n + (o + e))
  | .left o :: l, a, n => (a, n) :: spans l (a + n + o) 0
  | .owe :: l, a, n => spans l a n

/-- The stretches filled, one after the other. -/
def fillAll (g : List Bool) : List (Nat × Nat) → List Bool
  | [] => g
  | x :: r => fillAll (fillB g x.1 x.2) r

/-- **What a list of steps does to the marks.** g: the marks in front of the open stretch's first
fill. Conditional on L's marks being g with the open stretch filled, on L's count of slots standing
right behind that stretch, and on room for all the steps. -/
theorem runOps_got : ∀ (l : List Op) (L : LedSh) (g : List Bool) (a n : Nat),
    L.got = fillB g a n → L.next = a + n → a + n + (l.map Op.len).sum ≤ g.length →
    (runOps l L).got = fillAll g (spans l a n)
  | [], _, _, _, _, hg, _, _ => hg
  | .sum o e :: l, L, g, a, n, hg, hn, hr => by
    have hr' : a + n + ((o + e) + (l.map Op.len).sum) ≤ g.length := hr
    have lg : (fillB g a n).length = g.length := fillB_length g a n (by omega)
    have e1 : ((Op.sum o e).on L).got = fillB g a (n + (o + e)) := by
      show fillB (fillB L.got (L.next + o) e) L.next o = _
      rw [fill_front L.got L.next o e (by rw [hg, lg, hn]; omega), hg, hn,
        fill_next g a n (o + e) (by omega)]
    have e2 : ((Op.sum o e).on L).next = a + (n + (o + e)) := by
      show L.next + o + e = _
      rw [hn]
      omega
    exact runOps_got l _ g a (n + (o + e)) e1 e2 (by omega)
  | .left o :: l, L, g, a, n, hg, hn, hr => by
    have hr' : a + n + (o + (l.map Op.len).sum) ≤ g.length := hr
    have lg : (fillB g a n).length = g.length := fillB_length g a n (by omega)
    show (runOps l ((Op.left o).on L)).got = fillAll (fillB g a n) (spans l (a + n + o) 0)
    refine runOps_got l _ (fillB g a n) (a + n + o) 0 ?_ ?_ ?_
    · show L.got = _
      rw [fillB_zero]
      exact hg
    · show L.next + o = a + n + o + 0
      rw [hn]
      rfl
    · rw [lg]
      omega
  | .owe :: l, L, g, a, n, hg, hn, hr => by
    have hr' : a + n + (0 + (l.map Op.len).sum) ≤ g.length := hr
    exact runOps_got l (Op.owe.on L) g a n hg hn (by omega)

/-! ## 3 The lookup -/

/-- **The marks behind a lookup's hearing, on the code.** Conditional on room for the lookup's
steps. -/
theorem lookUpd_got (f : KFace) (L : LedSh)
    (h : L.next + ((lookOps f).map Op.len).sum ≤ L.got.length) :
    (lookUpd f L).got = fillAll L.got (spans (lookOps f) L.next 0) :=
  runOps_got (lookOps f) L L.got L.next 0 (fillB_zero _ _).symm rfl (by omega)

/-- A shape with its own marks laid anew is itself. -/
theorem setGot_self (M : LedSh) : M.setGot M.got = M := rfl

/-- **A second text for lookUpd**: where the lookup's steps have room, the marks by their closed
form and every other component lookUpd's own; where they have not, lookUpd. -/
def lookUpdL (f : KFace) (L : LedSh) : LedSh :=
  if L.next + ((lookOps f).map Op.len).sum ≤ L.got.length then
    (lookUpd f L).setGot (fillAll L.got (spans (lookOps f) L.next 0))
  else lookUpd f L

/-- **It is lookUpd**, at every face and every shape of a ledger. No hypothesis. -/
theorem lookUpdL_eq (f : KFace) (L : LedSh) : lookUpdL f L = lookUpd f L := by
  unfold lookUpdL
  split
  · rename_i h
    rw [← lookUpd_got f L h]
    exact setGot_self _
  · rfl

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.marks_ext
#print axioms ProofFile.Honest.K3.Shape.fill_next
#print axioms ProofFile.Honest.K3.Shape.fill_front
#print axioms ProofFile.Honest.K3.Shape.spans
#print axioms ProofFile.Honest.K3.Shape.fillAll
#print axioms ProofFile.Honest.K3.Shape.runOps_got
#print axioms ProofFile.Honest.K3.Shape.lookUpd_got
#print axioms ProofFile.Honest.K3.Shape.setGot_self
#print axioms ProofFile.Honest.K3.Shape.lookUpdL
#print axioms ProofFile.Honest.K3.Shape.lookUpdL_eq
