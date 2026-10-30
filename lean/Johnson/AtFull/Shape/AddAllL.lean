-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/AddAllL.lean: "FORMS' SHAPES LAID ONE BEHIND ANOTHER" (`addAllSh`,
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanes.lean) ONCE MORE, GATHERED FIRST AND JOINED ONCE:
`addAllL`; AND THE TWO ARE EQUAL AT ALL ARGUMENTS: `addAllSh_L`. No premise. Two definitions (one of
them a reader for the tests), one theorem, four small tests. It imports ClaimPlanes.lean alone.

Purpose. addAllSh walks a list of columns and appends each column's shape BEHIND all that stands so
far: "f.append (q c)", that is "l ++ x" with l growing: left-nested. For Lean's kernel each such
append walks l anew: in timed trials on toy lines an append of one member at the end, 1,000 times
over, cost it some 44 s and 3 GB (seen by trial; not shown here). The lookup's run "planes" lays its
three forms so, one entry a column. addAllL asks all columns first (List.mapM) and joins their lists
by flatMap: each list is walked once. Whoever has to evaluate a text that calls addAllSh may rewrite
by addAllSh_L first.

Main names.
* `addAllL l q init`: nothing where q refuses at a member of l; else the shape whose entries are
  init's and then the members' own, in l's order; its slots likewise.
* **`addAllSh_L`**: addAllSh l q init = addAllL l q init. By induction on l, init general.

Limits. An equality of two functions. Nothing is said on what either costs; nothing is evaluated
here but four toy tests. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClaimPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.AddAllL
open VerifiableInference.Desc.First.Shape (AffSh)
open ProofFile.Honest.K3.Shape (addAllSh)

/-- addAllSh, gathered first and joined once. -/
def addAllL (l : List Nat) (q : Nat → Option AffSh) (init : AffSh) : Option AffSh :=
  (l.mapM q).map fun fs =>
    AffSh.mk (init.ents ++ fs.flatMap (·.ents)) (init.slots ++ fs.flatMap (·.slots))

/-- **THE LAW: addAllSh IS addAllL**, at all lists, readers and first shapes. -/
theorem addAllSh_L (q : Nat → Option AffSh) : ∀ (l : List Nat) (init : AffSh),
    addAllSh l q init = addAllL l q init
  | [], init => by
    unfold addAllSh addAllL
    simp [AffSh.mk, AffSh.ents, AffSh.slots]
  | c :: l, init => by
    have ih := addAllSh_L q l
    unfold addAllSh addAllL at ih ⊢
    rw [List.foldlM_cons, List.mapM_cons]
    cases hq : q c with
    | none => rfl
    | some x =>
      show l.foldlM (fun f c => (q c).map f.append) (init.append x) = _
      rw [ih (init.append x)]
      cases l.mapM q with
      | none => rfl
      | some fs =>
        simp [AffSh.mk, AffSh.ents, AffSh.slots, AffSh.append, List.append_assoc]

/-- A reader for the tests: column c has the entry (0, 0, c) and the slot c; it refuses at 7. -/
def readerForTests (c : Nat) : Option AffSh :=
  if c == 7 then none else some (AffSh.mk [(0, 0, c)] [c])

/-- No column: the first shape. -/
example : addAllL [] readerForTests (AffSh.mk [(9, 9, 9)] [9]) =
    some (AffSh.mk [(9, 9, 9)] [9]) := by decide

/-- Three columns behind a first shape that is not empty: in order. -/
example : addAllL [1, 2, 3] readerForTests (AffSh.mk [(9, 9, 9)] [9]) =
    some (AffSh.mk [(9, 9, 9), (0, 0, 1), (0, 0, 2), (0, 0, 3)] [9, 1, 2, 3]) := by decide

/-- The library's own text at the same arguments gives the same. -/
example : addAllSh [1, 2, 3] readerForTests (AffSh.mk [(9, 9, 9)] [9]) =
    some (AffSh.mk [(9, 9, 9), (0, 0, 1), (0, 0, 2), (0, 0, 3)] [9, 1, 2, 3]) := by decide

/-- A reader that refuses in the middle: both give nothing. -/
example : addAllL [1, 7, 3] readerForTests (AffSh.mk [] []) = none ∧
    addAllSh [1, 7, 3] readerForTests (AffSh.mk [] []) = none := by decide

end Johnson.AtFull.Shape.AddAllL

#print axioms Johnson.AtFull.Shape.AddAllL.addAllL
#print axioms Johnson.AtFull.Shape.AddAllL.addAllSh_L
#print axioms Johnson.AtFull.Shape.AddAllL.readerForTests
