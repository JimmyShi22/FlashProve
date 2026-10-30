-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillK4.lean: K4's LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: two
public items AT THE LAYERS' SEGMENTS, each with its test on the record, laid into a `Meaning` over
whatever is there; at a segment of another sort both are handed on. Small; no Mathlib. A file BESIDE
the table of joints (Johnson/Desc/First/Borders.lean): it turns nothing of it. After the pattern of
Johnson/Desc/First/FillKeeper.lean.

What is said. `lookLayB`: the item look m: the record stands in a layers' link that holds what the
lookup on the calls returned (fo); every slot that the form in which its key side ends (cEnd) names
lies below the ledger's number of slots and is filled; AND THE LINK's TWO FIELDS fo AND lookHeard
ARE EQUAL, WHOLE. `callerInLayB n`: the item callerIn m: the record stands in a layers' link in
which the own rounds have not been heard (own = none), and the ledger's next free slot is n (n: the
plan's number for the segment). `pubK4`: THE LAYER's HALF WITH CODE: at a segment that links says is
a layers' these two; every other item, and these two at every other segment, handed on to a function
that it is given. `fillK4`: the layer. `fillK4_pub` (by the make), `_look`, `_callerIn`: what it
lays, at every `Meaning`. `fillK4_else`: what it leaves. `look_agrees`, `look_filled`,
`callerIn_next`, `callerIn_own`: WHAT THE TWO TESTS GIVE, as sentences, for whoever spends the
items: of them K4's road takes `look_agrees` and `look_filled`.

The equality of two records of the lookup is decided by instances that are derived here (no file
beneath this one derives them). Their NAMES stand in this file's own namespace; the instances are in
sight of every file that imports this one.

Limits. (1) links and nextOf are letters: the sorts of the segments; the plan's next free slot in
front of K4's block, by segment; where nextOf answers nothing callerIn is false. nextOf IS NOT FREE:
nextOf m is meant as the lookup's first slot + `Forest.elems` of the layout's shape: under the item
left m no other number can be met: at another number look · left · callerIn are true together at no
record, and the promise in front of K4's block holds of marked statements alone: in silence. (2)
NOTHING SAYS HERE WHO MAKES THE TWO: by the table's rows the lookup's block on the calls does: that
its yes makes these tests true is owed by nobody yet. (3) BY A RUN, NO THEOREM (copies of the tests,
tied to this text by program): at one honest proof of each of two sizes both tests are true at the
border in front of K4's block at every layers' segment, at n := `Forest.elems` of the layout's shape
(one number for all segments), and false at five controls; callerIn is true at that
border alone; look is true at every later border of the segment too: wider than the table's row for
it; and it asks that the lookup IS heard, where the table's words are "where it is heard". (4)
K04_law, the law of K4's block itself, IS NOT PROVED. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillK4
open OnBytes OnBytes.Model

deriving instance DecidableEq for OnBytes.Model.Ent
deriving instance DecidableEq for OnBytes.Model.Aff
deriving instance DecidableEq for OnBytes.Psc.Weight
deriving instance DecidableEq for OnBytes.Model.Psc
deriving instance DecidableEq for OnBytes.Model.Call
deriving instance DecidableEq for OnBytes.Model.Forest.Shape
deriving instance DecidableEq for OnBytes.Model.Forest.Heard

/-- Every slot that the form names lies below the ledger's number of slots and is filled. -/
def filledB (F : Fork) (f : Aff) : Bool :=
  f.slots.toList.all fun x => decide (x.1 < F.ns) && F.gotF.getD x.1 false

/-- look m at a layers' segment. -/
def lookLayB (s : S) : Bool :=
  match s.here with
  | .lay a =>
    (match a.fo with
      | some g => filledB a.F g.cEnd
      | none => false) && decide (a.fo = a.lookHeard)
  | _ => false

/-- callerIn m at a layers' segment. n: the plan's next free slot in front of K4's block. -/
def callerInLayB (n : Nat) (s : S) : Bool :=
  match s.here with
  | .lay a => a.own.isNone && a.F.next == n
  | _ => false

/-- Is segment m a layers' segment? -/
def isLay (links : List ModelPart) (m : Nat) : Bool := links[m]? == some .layers

/-- Is the item one of this layer's? -/
def k4Item (links : List ModelPart) : Pub → Bool
  | .look m => isLay links m
  | .callerIn m => isLay links m
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubK4 {P : Type} (links : List ModelPart) (nextOf : Nat → Option Nat) (f : Pub → P × S → Bool) :
    Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .look m => if isLay links m then lookLayB a.2 else f (.look m) a
    | .callerIn m =>
      if isLay links m then (nextOf m).any fun n => callerInLayB n a.2 else f (.callerIn m) a
    | q => f q a

/-- **K4's layer.** -/
def fillK4 {P W : Type} (links : List ModelPart) (nextOf : Nat → Option Nat) (Mg : Meaning P W) :
    Meaning P W :=
  { Mg with pub := pubK4 links nextOf Mg.pub }

section
variable {P W : Type} (links : List ModelPart) (nextOf : Nat → Option Nat) (Mg : Meaning P W)

/-- The layer's `pub` is its half with code, by the make. -/
theorem fillK4_pub : (fillK4 links nextOf Mg).pub = pubK4 links nextOf Mg.pub := rfl

theorem fillK4_look {m : Nat} (h : isLay links m = true) (a : P × S) :
    (fillK4 links nextOf Mg).pub (.look m) a = lookLayB a.2 := by
  show (if isLay links m then lookLayB a.2 else Mg.pub (.look m) a) = _
  rw [if_pos h]

theorem fillK4_callerIn {m : Nat} (h : isLay links m = true) (a : P × S) :
    (fillK4 links nextOf Mg).pub (.callerIn m) a = (nextOf m).any fun n => callerInLayB n a.2 := by
  show (if isLay links m then _ else Mg.pub (.callerIn m) a) = _
  rw [if_pos h]

/-- Every other item, and the two at a segment of another sort, are handed on. -/
theorem fillK4_else (q : Pub) (h : k4Item links q = false) (a : P × S) :
    (fillK4 links nextOf Mg).pub q a = Mg.pub q a := by
  cases q with
  | look m =>
    show (if isLay links m then lookLayB a.2 else Mg.pub (.look m) a) = _
    rw [if_neg (by simpa [k4Item] using h)]
  | callerIn m =>
    show (if isLay links m then _ else Mg.pub (.callerIn m) a) = _
    rw [if_neg (by simpa [k4Item] using h)]
  | _ => rfl

end

/-- **What look's test gives: the link's two fields are equal.** -/
theorem look_agrees {s : S} (h : lookLayB s = true) {a : LayOwn} (ha : s.here = .lay a) :
    a.fo = a.lookHeard := by
  unfold lookLayB at h
  rw [ha] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- What look's test gives: what the lookup returned is there, and its end form's slots are filled.
-/
theorem look_filled {s : S} (h : lookLayB s = true) {a : LayOwn} (ha : s.here = .lay a) :
    ∃ g, a.fo = some g ∧ ∀ x ∈ g.cEnd.slots.toList, x.1 < a.F.ns ∧ a.F.gotF.getD x.1 false = true :=
    by
  unfold lookLayB at h
  rw [ha] at h
  simp only [Bool.and_eq_true] at h
  cases hg : a.fo with
  | none => simp [hg] at h
  | some g =>
    refine ⟨g, rfl, fun x hx => ?_⟩
    have h1 := h.1
    simp only [hg, filledB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1 x hx

/-- **What callerIn's test gives: the ledger's next free slot is n.** -/
theorem callerIn_next {n : Nat} {s : S} (h : callerInLayB n s = true) {a : LayOwn}
    (ha : s.here = .lay a) : a.F.next = n := by
  unfold callerInLayB at h
  rw [ha] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- What callerIn's test gives: the own rounds have not been heard. -/
theorem callerIn_own {n : Nat} {s : S} (h : callerInLayB n s = true) {a : LayOwn}
    (ha : s.here = .lay a) : a.own = none := by
  unfold callerInLayB at h
  rw [ha] at h
  simp only [Bool.and_eq_true] at h
  exact Option.isNone_iff_eq_none.mp h.1

end VerifiableInference.Desc.First.FillK4

#print axioms VerifiableInference.Desc.First.FillK4.fillK4_else
#print axioms VerifiableInference.Desc.First.FillK4.look_agrees
#print axioms VerifiableInference.Desc.First.FillK4.callerIn_next
