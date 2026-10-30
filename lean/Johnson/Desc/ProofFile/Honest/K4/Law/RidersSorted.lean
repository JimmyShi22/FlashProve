-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RidersSorted.lean: A TEST ON TWO WRITTEN LISTS, DECIDED BY
LEAN's KERNEL, AND WHAT ITS YES GIVES.

What is here. Which items ride past the member of the feed-forward layers' own rounds (sub-protocol
K4): the items that are open in front of it and that its forward row neither shuts nor owes. The
threads' debt `RidesPastS` (Honest/Thread/PaysS.lean) is asked at just these. At the full size's
two written lists they are of five sorts: `unmarked`; `pile`; a class of rows of the member's own
segment; the lookup's run of claims "objects" of that segment; a part of a segment's relation, one
of the four of the library's `P5J.parts4`.

  `onePassAtBorder`   general in the lists and in the test: a test on (open set, place) that says
     yes along `opens` (Honest/Thread/FirstRows.lean: one pass) says yes at every border's own open
     set `fwdOpen`. After `asks_open` (Honest/Thread/FirstFits.lean), which is this at one test.
  `isRiderSort`, `IsRider`, `isRider_of_sort`   the five sorts, as a test and as a sentence.
  `ridersAreSortedAt`   the test at one place: at piece 3 of a layers' segment every rider is of a
     given sort; at every other place: yes.
  `ridersAreSorted_full`   **the test says yes at the full size's two lists.** One evaluation by
     the kernel.
  five controls   with one sort struck from the test (at the rows and at the parts: one member of
     the sort), it says no there: so each sort does ride somewhere, and the test can say no.
  `riders_are_sorted`   **at a thread of the first chain whose lists pass the test: every rider at
     K4's member is of one of the five sorts.**

Not shown here. Lists alone: nothing on what an item says, on any run, thread or witness. THE FULL
SIZE's TWO WRITTEN LISTS ALONE (`P5J.At.links`, `P5J.At.ps`, Johnson/P5J/LettersAt.lean) in the six
closed statements, whose proofs are evaluations by the kernel that no independent checker has
replayed. The sentence `IsRider` is wider than the list: it admits every class of rows of the
segment and every segment's four parts, also those that do not ride at a given member. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.P5J.LettersAt
import Johnson.P5J.MeansQ
import Johnson.Road.K4.K4AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item start)
open ProofFile.Honest.FirstRows (opens rowAt rows fwdOpen_cons)
open ProofFile.Honest.FirstThread (Letters)
open OnBytes.Road.K4 (AtK4)
open P5J (parts4)

/-! ## 1 A test in one pass speaks at every border -/

/-- **A test on (open set, place) that says yes along `opens` says yes at every border's own open
set.** General in the lists, the start and the test. -/
theorem onePassAtBorder (links : List ModelPart) (t : List Item → Place → Bool) :
    ∀ (ps : List Place) (O : List Item),
      (((opens links ps O).zip ps).all fun x => t x.1 x.2) = true →
      ∀ b p, ps[b]? = some p → t (fwdOpen O (rows links ps) b) p = true
  | [], _, _, _, _, hp => by simp at hp
  | q :: ps, O, h, b, p, hp => by
    have h' : (t O q &&
        ((opens links ps (fwdStep O (rowAt links q))).zip ps).all fun x => t x.1 x.2) = true := h
    rw [Bool.and_eq_true] at h'
    cases b with
    | zero =>
      have e : q = p := by simpa using hp
      rw [← e]
      exact h'.1
    | succ b =>
      rw [fwdOpen_cons]
      exact onePassAtBorder links t ps _ h'.2 b p (by simpa using hp)

/-! ## 2 The five sorts -/

/-- The five sorts, as a test. m: the member's segment. This defines a test; the definition claims
nothing. -/
def isRiderSort (m : Nat) : Item → Bool
  | .unmarked => true
  | .pile => true
  | .row l _ => l == m
  | .formsT l k r => l == m && k == 2 && r == "objects"
  | .constr _ q => parts4.contains q
  | _ => false

/-- The five sorts, as a sentence. This defines a proposition; the definition claims nothing. -/
def IsRider (m : Nat) (i : Item) : Prop :=
  i = .unmarked ∨ i = .pile ∨ (∃ c, i = .row m c) ∨ i = .formsT m 2 "objects" ∨
    ∃ l q, q ∈ parts4 ∧ i = .constr l q

/-- The test's yes gives the sentence. -/
theorem isRider_of_sort {m : Nat} {i : Item} (h : isRiderSort m i = true) : IsRider m i := by
  unfold IsRider
  cases i with
  | unmarked => exact Or.inl rfl
  | pile => exact Or.inr (Or.inl rfl)
  | row l c =>
    have e : l = m := by simpa [isRiderSort] using h
    subst e
    exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  | formsT l k r =>
    have e : (l = m ∧ k = 2) ∧ r = "objects" := by simpa [isRiderSort] using h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | constr l q =>
    have e : q ∈ parts4 := by simpa [isRiderSort] using h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨l, q, e, rfl⟩)))
  | _ => simp [isRiderSort] at h

/-! ## 3 The test at a place, and at the full size's lists -/

/-- **The test at one place.** sort: a test on (segment, item). O: the open set in front. At piece 3
of a layers' segment: every item of O that the forward row neither shuts nor owes passes sort at
that segment. At every other place: yes. This defines a test; the definition claims nothing. -/
def ridersAreSortedAt (sort : Nat → Item → Bool) (links : List ModelPart) (O : List Item) (p : Place) :
    Bool :=
  if (p.link.bind fun m => links[m]?) = some ModelPart.layers ∧ p.piece = 3 then
    (O.filter fun i =>
      !(rowAt links p).shuts.contains i && !(rowAt links p).owes.contains i).all
      (sort (p.link.getD 0))
  else true

/-- At piece 3 of the layers' segment m the test is its first arm. -/
theorem ridersAreSortedAt_layers {sort : Nat → Item → Bool} {links : List ModelPart} {O : List Item}
    {p : Place} {m : Nat} (hl : p.link = some m) (hs : links[m]? = some ModelPart.layers)
    (hp : p.piece = 3) :
    ridersAreSortedAt sort links O p =
      (O.filter fun i =>
        !(rowAt links p).shuts.contains i && !(rowAt links p).owes.contains i).all (sort m) := by
  have c : (p.link.bind fun m => links[m]?) = some ModelPart.layers ∧ p.piece = 3 :=
    ⟨by rw [hl]; exact hs, hp⟩
  unfold ridersAreSortedAt
  rw [if_pos c]
  simp only [hl, Option.getD_some]

/-- **AT THE FULL SIZE's TWO LISTS EVERY RIDER AT K4's MEMBERS IS OF ONE OF THE FIVE SORTS.** -/
theorem ridersAreSorted_full :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt isRiderSort P5J.At.links x.1 x.2) = true := by
  decide +kernel

/-- Control: without `unmarked` the test says no. -/
theorem ridersAreSorted_control_unmarked :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt (fun m i => isRiderSort m i && i != Item.unmarked) P5J.At.links x.1 x.2) =
      false := by
  decide +kernel

/-- Control: without `pile` the test says no. -/
theorem ridersAreSorted_control_pile :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt (fun m i => isRiderSort m i && i != Item.pile) P5J.At.links x.1 x.2) =
      false := by
  decide +kernel

/-- Control: without the first moment's sample rows the test says no. -/
theorem ridersAreSorted_control_row :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt (fun m i => isRiderSort m i && i != Item.row m (.sample 0)) P5J.At.links
        x.1 x.2) = false := by
  decide +kernel

/-- Control: without the run "objects" the test says no. -/
theorem ridersAreSorted_control_objects :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt (fun m i => isRiderSort m i && i != Item.formsT m 2 "objects")
        P5J.At.links x.1 x.2) = false := by
  decide +kernel

/-- Control: without one part of the last segment's relation the test says no. -/
theorem ridersAreSorted_control_constr :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ridersAreSortedAt (fun m i => isRiderSort m i && i != Item.constr 24 .small) P5J.At.links
        x.1 x.2) = false := by
  decide +kernel

/-! ## 4 At a thread of the first chain -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)

/-- **EVERY RIDER AT K4's MEMBER IS OF ONE OF THE FIVE SORTS.** CONDITIONAL: on hTest (the test at
the thread's two lists) and A (the member's number, segment and place stand in these lists). -/
theorem riders_are_sorted
    (hTest : (((opens L.links L.ps (start L.links)).zip L.ps).all fun x =>
      ridersAreSortedAt isRiderSort L.links x.1 x.2) = true)
    {b m : Nat} {pl : Place} (A : AtK4 L.links L.ps b m pl) {i : Item}
    (hi : i ∈ L.thread.opened b) (hs : i ∉ (L.thread.row b).shuts)
    (ho : i ∉ (L.thread.row b).owes) : IsRider m i := by
  have h1 := onePassAtBorder L.links (ridersAreSortedAt isRiderSort L.links) L.ps (start L.links)
    hTest b pl A.here
  rw [ridersAreSortedAt_layers A.link A.sub A.piece] at h1
  have hr : rows L.links L.ps b = rowAt L.links pl := by
    simp only [rows, A.here, Option.map_some, Option.getD_some]
  have hs' : i ∉ (rowAt L.links pl).shuts := by
    rw [← hr]
    exact hs
  have ho' : i ∉ (rowAt L.links pl).owes := by
    rw [← hr]
    exact ho
  have hi' : i ∈ fwdOpen (start L.links) (rows L.links L.ps) b := hi
  exact isRider_of_sort (List.all_eq_true.1 h1 i (List.mem_filter.2 ⟨hi', by simp [hs', ho']⟩))

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.onePassAtBorder
#print axioms ProofFile.Honest.K4.isRider_of_sort
#print axioms ProofFile.Honest.K4.ridersAreSortedAt_layers
#print axioms ProofFile.Honest.K4.ridersAreSorted_full
#print axioms ProofFile.Honest.K4.ridersAreSorted_control_unmarked
#print axioms ProofFile.Honest.K4.ridersAreSorted_control_pile
#print axioms ProofFile.Honest.K4.ridersAreSorted_control_row
#print axioms ProofFile.Honest.K4.ridersAreSorted_control_objects
#print axioms ProofFile.Honest.K4.ridersAreSorted_control_constr
#print axioms ProofFile.Honest.K4.riders_are_sorted
