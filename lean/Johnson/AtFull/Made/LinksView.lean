-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Made/LinksView.lean: THE PLANNER's PUBLIC TESTS ON THE SEGMENTS' ENTRIES READ FOUR
PLAIN FIELDS OF AN ENTRY AND NOTHING ELSE: `tableRows`, `numbersHeld`, `indexMaskRoom`,
`linksLaid`, `linksFit` (OnBytes/Model/StagesLinks.lean) at a list of entries are the same tests
at the entries made anew from a view of four fields. An entry: the structure `LinkH`, one for each
segment of the first chain. One abbreviation, three definitions and fourteen theorems.
Why. An entry holds a routine and three large plans. A test that Lean's kernel is to decide at
written values must stand at a term without them. One view serves `linksFit` where the chains are
made and the three tests of `buildLinksH` that are handed the entries.
  `LinkView`: fv (the sub-proof leaves a row on the committed table), gid (its public identifier),
    ns (the scalars that it sends), arrayOf (for each array of its list: the segment that commits
    to it and its name there). `viewOf X`. `ofView v`: an entry with these four fields, the
    placeholder routine, every other field at its default. `narrow X := ofView (viewOf X)`.
  `onTable_narrow`, `gids_narrow`, `tableRows_narrow`, `numbersHeld_narrow`,
    `indexMaskRoom_narrow`, `linksLaid_narrow`, `linksFit_narrow`: EQUATIONS: a refusal carries
    over too, with its name.
  `narrow_of_views`: entries whose views are the list vs are, narrowed, vs's entries.
    `tests_at_view`: THE END: under `links.toList.map viewOf = vs` the three tests at links are
    the tests at `(vs.map ofView).toArray`.
  `narrow_blind`: the view does not feel the planned state. `narrow_feels_ns`, `_fv`, `_gid`,
    `_arrayOf`: it feels each of its four fields.
How: THE MANNER AND THE TOOLS ARE ANOTHER AUTHOR's
(Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean: `blank` keeps all fields but the routine; its
lemma on loops `loop_mapL` is called; its proofs are followed line by line with `narrow` for
`blank`). No test is typed anew: the library's own definitions stand on both sides.
A snare for a caller: where `open OnBytes` stands, the bare name `viewOf` is ambiguous with the
library's `OnBytes.viewOf`: write `Johnson.AtFull.Made.viewOf`.
Limits. NO VALUE OF A VIEW IS GIVEN HERE: that the planner's entries have any written views is a
debt of whoever calls `tests_at_view`. `headLast`, `linksCount`, `declareLinks` read more of an
entry (its kind, its list of arrays, its plan): they are not touched: so `buildLinksH` whole does
not stand at a view. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.Law.PlainIsPlanned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params
open ProofFile.Law (loop_mapL)

/-- fv, gid, ns, arrayOf. -/
abbrev LinkView := Bool × Nat × Nat × Array (Nat × String)

/-- What the tests read of an entry. -/
def viewOf (X : LinkH) : LinkView := (X.fv, X.gid, X.ns, X.arrayOf)

/-- An entry of a view: the placeholder routine; every other field at its default. -/
def ofView (v : LinkView) : LinkH :=
  { fv := v.1, gid := v.2.1, ns := v.2.2.1, arrayOf := v.2.2.2, run := ProofFile.Plain.notToBeRun }

/-- An entry, cut to its view. -/
def narrow (X : LinkH) : LinkH := ofView (viewOf X)

theorem onTable_narrow (links : Array LinkH) : onTable (links.map narrow) = onTable links := by
  unfold onTable
  rw [Array.toList_map, List.filter_map, List.length_map]
  rfl

theorem gids_narrow (nm : Array LinkH) :
    (nm.map narrow).toList.map (·.gid) = nm.toList.map (·.gid) := by
  rw [Array.toList_map, List.map_map]
  rfl

theorem tableRows_narrow (links : Array LinkH) (NGr : Nat) :
    tableRows (links.map narrow) NGr = tableRows links NGr := by
  unfold tableRows
  rw [onTable_narrow]

theorem numbersHeld_narrow (links : Array LinkH) (p : Params.First) :
    numbersHeld (links.map narrow) p = numbersHeld links p := by
  unfold numbersHeld
  rw [Array.size_map, onTable_narrow, gids_narrow]

theorem indexMaskRoom_narrow (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (kCol : Nat) :
    indexMaskRoom (links.map narrow) codes shape kCol = indexMaskRoom links codes shape kCol := by
  unfold indexMaskRoom
  rw [onTable_narrow]

theorem linksLaid_narrow (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) :
    linksLaid (links.map narrow) codes shape layout = linksLaid links codes shape layout := by
  unfold linksLaid
  rw [Array.toList_map, List.zipIdx_map]
  cases codes.mask[shape.maskCode]? with
  | none => rfl
  | some zk =>
    try dsimp only
    refine loop_mapL (Prod.map narrow id) ?_
    rintro ⟨X, l⟩ r
    rfl

theorem linksFit_narrow (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) (kCol : Nat) :
    linksFit (links.map narrow) codes shape layout kCol =
      linksFit links codes shape layout kCol := by
  unfold linksFit
  rw [indexMaskRoom_narrow, linksLaid_narrow]

/-- Entries whose views are vs are, narrowed, vs's entries. -/
theorem narrow_of_views {links : Array LinkH} {vs : List LinkView}
    (hv : links.toList.map viewOf = vs) : links.map narrow = (vs.map ofView).toArray := by
  subst hv
  apply Array.toList_inj.1
  rw [Array.toList_map, List.map_map]
  rfl

/-- **THE TESTS AT THE ENTRIES ARE THE TESTS AT THE VIEWS' ENTRIES.** -/
theorem tests_at_view {links : Array LinkH} {vs : List LinkView}
    (hv : links.toList.map viewOf = vs) (NGr : Nat) (p : Params.First) (codes : Codes)
    (shape : Params.ReqShape) (layout : Params.ReqLayout) (kCol : Nat) :
    tableRows links NGr = tableRows (vs.map ofView).toArray NGr ∧
      numbersHeld links p = numbersHeld (vs.map ofView).toArray p ∧
      linksFit links codes shape layout kCol =
        linksFit (vs.map ofView).toArray codes shape layout kCol := by
  rw [← narrow_of_views hv]
  exact ⟨(tableRows_narrow links NGr).symm, (numbersHeld_narrow links p).symm,
    (linksFit_narrow links codes shape layout kCol).symm⟩

/-- The view does not feel the planned state. -/
theorem narrow_blind (X : LinkH) (F : Fork) : narrow { X with Fp := F } = narrow X := rfl

/-- **It feels the number of scalars.** -/
theorem narrow_feels_ns (X : LinkH) : (narrow { X with ns := X.ns + 1 }).ns ≠ (narrow X).ns :=
  Nat.succ_ne_self X.ns

/-- It feels the flag. -/
theorem narrow_feels_fv (X : LinkH) : (narrow { X with fv := !X.fv }).fv ≠ (narrow X).fv := by
  show (!X.fv) ≠ X.fv
  cases X.fv <;> decide

/-- It feels the identifier. -/
theorem narrow_feels_gid (X : LinkH) : (narrow { X with gid := X.gid + 1 }).gid ≠ (narrow X).gid :=
  Nat.succ_ne_self X.gid

/-- It feels the list of the arrays' names. -/
theorem narrow_feels_arrayOf (X : LinkH) (a : Nat × String) :
    (narrow { X with arrayOf := X.arrayOf.push a }).arrayOf.size ≠ (narrow X).arrayOf.size := by
  show (X.arrayOf.push a).size ≠ X.arrayOf.size
  rw [Array.size_push]
  exact Nat.succ_ne_self _

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.onTable_narrow
#print axioms Johnson.AtFull.Made.gids_narrow
#print axioms Johnson.AtFull.Made.tableRows_narrow
#print axioms Johnson.AtFull.Made.numbersHeld_narrow
#print axioms Johnson.AtFull.Made.indexMaskRoom_narrow
#print axioms Johnson.AtFull.Made.linksLaid_narrow
#print axioms Johnson.AtFull.Made.linksFit_narrow
#print axioms Johnson.AtFull.Made.narrow_of_views
#print axioms Johnson.AtFull.Made.tests_at_view
#print axioms Johnson.AtFull.Made.narrow_blind
#print axioms Johnson.AtFull.Made.narrow_feels_ns
#print axioms Johnson.AtFull.Made.narrow_feels_fv
#print axioms Johnson.AtFull.Made.narrow_feels_gid
#print axioms Johnson.AtFull.Made.narrow_feels_arrayOf
