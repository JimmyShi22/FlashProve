-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillBare.lean: A LAYER OF THE TABLE OF JOINTS' FILLING WITH TWO NAMES THROUGH THE
DOOR: (some m, "K4.rowsBare"): none of the rows that the lookup on the calls keeps names an entry of
an array · (some m, "K4.lookLeft"): ALL ELSE THAT K4's FILES WANT, IN FRONT OF K4's SUB-PROTOCOL,
OF THE FORMS AND OF THE UNFINISHED SUMCHECK THAT THE LOOKUP ON THE CALLS HAS LEFT IN THE VERIFIER's
STATE, AS ONE TEST WITH CODE.
Definitions (the test, its rows in the promise's table, the layer)
and small statements with their proofs. No Mathlib.

WHAT THE TEST SAYS (`lookLeftB`), at a feed-forward segment in which something is heard, g, at the
  segment's ledger F: (1) `namedB` of every kept row, of the form in which the key side ends, of the
      slot of the bits' shown value and of the leaves' sumcheck's start form: the form names NO
      ENTRY of an array, and slots alone that lie below the ledger's number of slots and are filled;
  (2) `readyB`: the leaves' sumcheck is begun, its row is not made yet, it has a variable, and as
      many points as variables;
  (3) its window lies below the ledger's next free slot;
  (4) `winFreeB`: each slot of its window is there and free.

WHO ASKS IT, AND WHY. K4's files, at three places. (a) The item formsT m 2 "objects" (the lookup's
kept rows) is open across K4's sub-protocol and must go back over K4's accept; its sentence reads
each entry that a row names through the stated function of the arrays of the second sending, WHICH
READS, AT A FEED-FORWARD SEGMENT, WHAT K4 HAS HEARD: so it rides only where the rows name no entry.
(b) K4's own two runs of claims must RETURN behind K4's accept (the public item formsInT m 3 "own"
asks them at the verifier's state): the run "front" ends the leaves' sumcheck: it wants (2), (3),
(4). (c) That item asks that every form of these runs name only what is there: they take over the
lookup's forms: (1). An honest lookup leaves all that; no item of the promise in front of K4's
sub-protocol says it: the item left m says (1) of the one form cEnd alone.

  `bare_of` · `parts_of`: what the test gives, in plain words of the verifier's state.
  `leftMore`: THE ROWS, OF BOTH NAMES: made by the lookup's sub-protocol on the calls (piece 2) of a
    feed-forward segment · asked and dropped by the caller's sub-protocol (piece 3): span one: no
    keeper.
  `pubLeft`, `fillBare`: the layer. `fillBare_bare`, `fillBare_at`, `fillBare_else`,
    `fillBare_more`.

Limits. (1) NOTHING SAYS HERE WHO MAKES IT: by the rows the lookup's sub-protocol does: that its
accept makes the test true is owed by that sub-protocol's files. (2) THE TEST HAS NOT RUN. (3)
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillBare
open OnBytes OnBytes.Model

/-- The form names no entry, and slots alone that are there and filled. -/
def namedB (F : Fork) (f : Aff) : Bool :=
  f.ents.isEmpty && f.slots.toList.all fun x => decide (x.1 < F.ns) && F.gotF.getD x.1 false

/-- The sumcheck is begun, its row not made, it has a variable, and as many points as variables. -/
def readyB (p : Psc) : Bool :=
  !p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size

/-- Each slot of the sumcheck's window is there and free. -/
def winFreeB (p : Psc) (F : Fork) : Bool :=
  (List.range p.walk.1.length).all fun i =>
    decide (p.first + i < F.ns) && !F.gotF.getD (p.first + i) false

/-- The test at what was heard and the ledger. -/
def leftAtB (g : Forest.Heard) (F : Fork) : Bool :=
  g.rows.toList.all (namedB F) && namedB F g.cEnd && namedB F (Aff.slot g.sBit) &&
    namedB F g.leaves.start && readyB g.leaves &&
    decide (g.leaves.first + g.leaves.walk.1.length ≤ F.next) && winFreeB g.leaves F

/-- "K4.rowsBare". -/
def rowsBareB (s : S) : Bool :=
  match s.here with
  | .lay a => a.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty
  | _ => false

/-- "K4.lookLeft". -/
def lookLeftB (s : S) : Bool :=
  match s.here with
  | .lay a => a.lookHeard.any fun g => leftAtB g a.F
  | _ => false

/-- What the test gives: its seven parts. -/
theorem parts_of {s : S} (h : lookLeftB s = true) {a : LayOwn} (ha : s.here = .lay a)
    {g : Forest.Heard} (hg : a.lookHeard = some g) :
    (∀ f ∈ g.rows.toList, namedB a.F f = true) ∧ namedB a.F g.cEnd = true ∧
      namedB a.F (Aff.slot g.sBit) = true ∧ namedB a.F g.leaves.start = true ∧
      readyB g.leaves = true ∧ g.leaves.first + g.leaves.walk.1.length ≤ a.F.next ∧
      winFreeB g.leaves a.F = true := by
  unfold lookLeftB at h
  rw [ha] at h
  simp only [hg, Option.any_some, leftAtB, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A form that passes has no entry. -/
theorem ents_of_named {F : Fork} {f : Aff} (h : namedB F f = true) : f.ents.toList = [] := by
  unfold namedB at h
  have e := (Eq.mp (Bool.and_eq_true _ _) h).1
  simpa [Array.isEmpty_iff] using e

/-- What the first test gives: no kept row names an entry. -/
theorem bare_of {s : S} (h : rowsBareB s = true) {a : LayOwn} (ha : s.here = .lay a)
    {g : Forest.Heard} (hg : a.lookHeard = some g) : ∀ f ∈ g.rows.toList, f.ents.toList = [] := by
  unfold rowsBareB at h
  rw [ha] at h
  simp only [hg, Option.any_some, List.all_eq_true] at h
  intro f hf
  have e := h f hf
  simpa [Array.isEmpty_iff] using e

def bareName (m : Nat) : MoreName := (some m, "K4.rowsBare")
def leftName (m : Nat) : MoreName := (some m, "K4.lookLeft")

/-- **The door's filling.** -/
def leftMore : More where
  rows links p :=
    match p.link with
    | some m =>
      if links[m]? == some .layers then
        if p.piece == 2 then { makes := [bareName m, leftName m] }
        else if p.piece == 3 then
          { asks := [bareName m, leftName m], drops := [bareName m, leftName m] }
        else {}
      else {}
    | none => {}

/-- Is the item this layer's? -/
def leftItem (links : List ModelPart) : Pub → Bool
  | .more (some m) name =>
    links[m]? == some .layers && (name == "K4.rowsBare" || name == "K4.lookLeft")
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubLeft {P : Type} (links : List ModelPart) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more (some m) name =>
      if links[m]? == some .layers && name == "K4.rowsBare" then rowsBareB a.2
      else if links[m]? == some .layers && name == "K4.lookLeft" then lookLeftB a.2
      else f (.more (some m) name) a
    | q => f q a

/-- **The layer.** -/
def fillBare {P W : Type} (links : List ModelPart) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubLeft links Mg.pub, more := Mg.more.merge leftMore }

section
variable {P W : Type} (links : List ModelPart) (Mg : Meaning P W)

theorem fillBare_bare {m : Nat} (hm : links[m]? = some .layers) (a : P × S) :
    (fillBare links Mg).pub (moreItem (bareName m)) a = rowsBareB a.2 := by
  show pubLeft links Mg.pub (.more (some m) "K4.rowsBare") a = _
  unfold pubLeft
  simp only [hm]
  rfl

theorem fillBare_at {m : Nat} (hm : links[m]? = some .layers) (a : P × S) :
    (fillBare links Mg).pub (moreItem (leftName m)) a = lookLeftB a.2 := by
  show pubLeft links Mg.pub (.more (some m) "K4.lookLeft") a = _
  unfold pubLeft
  simp only [hm]
  rfl

theorem fillBare_else (q : Pub) (a : P × S) (h : leftItem links q = false) :
    (fillBare links Mg).pub q a = Mg.pub q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => rfl
    | some m =>
      have e : (links[m]? == some .layers && (name == "K4.rowsBare" || name == "K4.lookLeft")) =
          false := h
      show pubLeft links Mg.pub (.more (some m) name) a = _
      unfold pubLeft
      cases h1 : (links[m]? == some .layers) with
      | false =>
        have h1' : links[m]? ≠ some .layers := by simpa using h1
        simp [h1']
      | true =>
        rw [h1, Bool.true_and, Bool.or_eq_false_iff] at e
        simp [e.1, e.2]
  | _ => rfl

theorem fillBare_more : (fillBare links Mg).more = Mg.more.merge leftMore := rfl

end

end VerifiableInference.Desc.First.FillBare
