-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EqNumbersOf.lean: WHAT THE LAW ON THE ONE EQUATION's BLOCK ASKS OF THE
PLAN's NUMBERS FOLLOWS FROM THE TABLE's OWN TEST ON THESE NUMBERS (`rowsAtFit`,
Johnson/Desc/First/Borders.lean) AND A FACT ON THE TABLE AND THE WRITTEN LIST OF PLACES ALONE. So no
new test on the numbers is wanted: IT OVERTAKES EqNumbersFit.lean (not in this library), whose Bool falls. Definitions,
theorems, four evaluations.

What is said.
  `clsOf`, `listedOf O m`: the classes of rows of segment m that are open in O and lie in the
    group's list. `rowsDue_listed`: the count of rows that are due is the sum of the plan's counts
    over these. `listAt`, `listFit links ps`: a Bool on the table and the list: in front of each one
    equation the open listed classes of its segment are «carried» and «position», in this order
    (none in the first segment), and every segment of which a class of rows is open is one of the
    list's. `eachOnce_nodup`. `numbers_of_fit`: **from `rowsAtFit N links.length` and `listFit links
    ps`, at a place of a one equation of a segment m of the list: `N.rowsAt m .equation = (rowsDue N
    O m, 1)`, and no other open segment has m's group**: the premises `hat` and `inj` of
    EqHands.lean's `eq_rows`, to the letter. `listFit_full`: the kernel's yes at the full list;
    `listAsks_full`: the test asks something at 25 numbers; `listFit_bent`, a negative test: with
    the places of the second segment's one equation and of the closing behind it changed over
    (numbers 25 and 26): no. `listFit_unseen`: what the test does not see: two hearing places
    changed over: yes.

Limits. `rowsAtFit`'s yes at the numbers that are made of a plan is the table's files'. That the
written list is the list of a description's places is another file's. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EqHands
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (ModelPart Item RowClass Numbers flatPlacesOf start openSets rowSegs
  rowsDue rowsAtFit eachOnce)

/-- The item is a class of rows of segment m that lies in the group's list. -/
def clsOf (m : ℕ) : Item → Option RowClass
  | .row m' c => if m' == m && c.inList then some c else none
  | _ => none

theorem clsOf_row (m m' : ℕ) (c : RowClass) :
    clsOf m (.row m' c) = if m' == m && c.inList then some c else none := rfl

/-- The classes of rows of segment m that are open and lie in the group's list. -/
def listedOf (O : List Item) (m : ℕ) : List RowClass := O.filterMap (clsOf m)

theorem rowsDue_acc (N : Numbers) (m : ℕ) (f : ℕ → Item → ℕ)
    (hs : ∀ k i c, clsOf m i = some c → f k i = k + (N.rowsAt m c).2)
    (hn : ∀ k i, clsOf m i = none → f k i = k) : ∀ (O : List Item) (k : ℕ),
    O.foldl f k = k + ((listedOf O m).map fun c => (N.rowsAt m c).2).sum
  | [], k => rfl
  | i :: O, k => by
    rw [List.foldl_cons, rowsDue_acc N m f hs hn O]
    unfold listedOf
    cases hc : clsOf m i with
    | none => rw [List.filterMap_cons_none hc, hn k i hc]
    | some c =>
      rw [List.filterMap_cons_some hc, hs k i c hc, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The count of rows that are due is the sum of the plan's counts over the open listed classes. -/
theorem rowsDue_listed (N : Numbers) (O : List Item) (m : ℕ) :
    rowsDue N O m = ((listedOf O m).map fun c => (N.rowsAt m c).2).sum := by
  unfold rowsDue
  rw [rowsDue_acc N m _ (fun k i c hc => ?_) (fun k i hc => ?_) O 0, Nat.zero_add]
  · cases i with
    | row m' c' =>
      rw [clsOf_row] at hc
      by_cases h : (m' == m && c'.inList) = true
      · rw [if_pos h] at hc
        obtain rfl : c' = c := Option.some.inj hc
        show (if (m' == m && c'.inList) = true then k + (N.rowsAt m c').2 else k) = _
        rw [if_pos h]
      · rw [if_neg h] at hc
        exact nomatch hc
    | _ => exact nomatch hc
  · cases i with
    | row m' c' =>
      rw [clsOf_row] at hc
      by_cases h : (m' == m && c'.inList) = true
      · rw [if_pos h] at hc
        exact nomatch hc
      · show (if (m' == m && c'.inList) = true then k + (N.rowsAt m c').2 else k) = _
        rw [if_neg h]
    | _ => rfl

/-- **The test at number k of the list**: the table and the list alone. -/
def listAt (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      let O := (openSets links ps (start links))[k]?.getD []
      if p.piece == hearN links m + 3 then
        decide (listedOf O m = if m == 0 then [] else [.carried, .position]) &&
          (rowSegs O).all fun m' => decide (m' ≤ links.length)
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def listFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (listAt links ps)

theorem eachOnce_nodup : ∀ l : List (ℕ × ℕ), eachOnce l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    unfold eachOnce at h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact List.nodup_cons.2 ⟨by simpa using h1, eachOnce_nodup l h2⟩

/-- **THE TWO PREMISES ON THE PLAN's NUMBERS, FROM THE TABLE's OWN TEST.** -/
theorem numbers_of_fit (N : Numbers) (links : List ModelPart) (ps : List Place)
    (hN : rowsAtFit N links.length = true) (h : listFit links ps = true) (k m : ℕ) (p : Place)
    (hp : ps[k]? = some p) (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (hm : m < links.length) :
    N.rowsAt m .equation = (rowsDue N ((openSets links ps (start links))[k]?.getD []) m, 1) ∧
      ∀ m' ∈ rowSegs ((openSets links ps (start links))[k]?.getD []), m' ≠ m →
        N.groupAt m' ≠ N.groupAt m := by
  unfold listFit at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold listAt at h0
  rw [hp] at h0
  simp only [hl, hpc, beq_self_eq_true, if_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h0
  obtain ⟨hlist, hseg⟩ := h0
  unfold rowsAtFit at hN
  obtain ⟨hg, hall⟩ := Bool.and_eq_true_iff.1 hN
  have hr := List.all_eq_true.1 hall m (List.mem_range.2 (by omega))
  obtain ⟨hr4, e3⟩ := Bool.and_eq_true_iff.1 hr
  obtain ⟨hr3, e2⟩ := Bool.and_eq_true_iff.1 hr4
  obtain ⟨_, e1⟩ := Bool.and_eq_true_iff.1 hr3
  have e1' : (N.rowsAt m .equation).1 = (N.rowsAt m .carried).2 + (N.rowsAt m .position).2 := by
    simpa using e1
  have e2' : (N.rowsAt m .equation).2 = 1 := by
    have hne : (m == links.length) = false := by simpa using Nat.ne_of_lt hm
    rw [hne] at e2
    simpa using e2
  refine ⟨?_, fun m' hm' hd he => ?_⟩
  · rw [rowsDue_listed, hlist]
    refine Prod.ext ?_ e2'
    by_cases h0 : m = 0
    · subst h0
      have e3' : (N.rowsAt 0 .carried).2 + (N.rowsAt 0 .position).2 = 0 := by simpa using e3
      show (N.rowsAt 0 .equation).1 = _
      rw [e1', e3']
      rfl
    · have hz : (m == 0) = false := by simpa using h0
      show (N.rowsAt m .equation).1 = _
      rw [e1', hz]
      simp
  · have hinj := List.inj_on_of_nodup_map (eachOnce_nodup _ hg)
    exact hd (hinj (List.mem_range.2 (Nat.lt_succ_of_le (hseg m' hm')))
      (List.mem_range.2 (by omega)) (by rw [he]))

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE FULL SIZE.** -/
theorem listFit_full : listFit fullList (flatPlacesOf fullList true) = true := by decide +kernel

/-- The place at number k is a one equation's. -/
def listAsks (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m => p.piece == hearN links m + 3
    | none => false
  | none => false

set_option maxRecDepth 1000000 in
/-- **THE TEST ASKS SOMETHING AT 25 NUMBERS OF THE FULL LIST.** -/
theorem listAsks_full : ((List.range (flatPlacesOf fullList true).length).filter
    (listAsks fullList (flatPlacesOf fullList true))).length = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: THE SECOND SEGMENT's ONE EQUATION AND THE CLOSING BEHIND IT CHANGED
OVER.** -/
theorem listFit_bent : listFit fullList (swapAt (flatPlacesOf fullList true) 25) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- WHAT THE TEST DOES NOT SEE: two hearing places of the second segment changed over (numbers 16
and 17): yes. (A negative test that does not fail.) -/
theorem listFit_unseen : listFit fullList (swapAt (flatPlacesOf fullList true) 16) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsDue_listed
#print axioms VerifiableInference.Desc.LinkJoin.numbers_of_fit
#print axioms VerifiableInference.Desc.LinkJoin.listFit_full
#print axioms VerifiableInference.Desc.LinkJoin.listAsks_full
#print axioms VerifiableInference.Desc.LinkJoin.listFit_bent
#print axioms VerifiableInference.Desc.LinkJoin.listFit_unseen
