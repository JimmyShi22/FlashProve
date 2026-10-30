-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FiveTest.lean: FIVE OF THE SEVEN THINGS A TREE THAT THE CODE SWITCH's
READING ASKS (the tree is in the book · its depth lies within the positions' range · its number,
depth and width are the plan's entry's), ALONG TWO LISTS, FROM A TEST WITH CODE ON A LAID LIST,
where the book carries that laid list's seats and numbers its trees in order. No state of the walk,
no plan: a book, a laid list and lists of numbers. Two definitions and a toy; statements with their
proofs.

  `AllFive ft logN B0 ts rd` as many trees as entries; tree t and entry r, pair by pair: B0 has a
                    tree at t · its depth is at most logN · its number less ft is r.1 · its depth is
                    r.2.1 · its two widths' sum is r.2.2
  `treesFiveB Ld logN ts rd` the same as a test on the laid list Ld's shapes, with t itself for the
                    tree's number
  `place_written` where the book carries Ld's seats (`seatsCarriedB`), a placed message's place is
                    Ld's
  `trees_written` so the rising list of the trees of a list of messages is that of any list with the
                    same members, read off Ld
  `allFive_of` THE TOP: the seats carried · tree j bears the number j · every t of ts is below the
                    number of trees · the test's yes ⊢ `AllFive 0 logN B ts rd`
  `toyLaid`, `fiveB_can_fail` a control at a toy: at a laid list of one shape the test says no to a
                    wrong depth and to lists of two lengths, and yes to the right entry

By, all the library's: `seatsCarriedB`, `Laid` (Johnson/Desc/K12/Door/DoorBools.lean) · `place_at`
(Johnson/P1K8R/ShareOfNums.lean), `tree_shape_of_seats` (Johnson/ToldDescR/BookAtW.lean) ·
`listOfT_eq`, `eq_of_incr` (OnBytes/Chain/Draws.lean), `listOf_mem`, `listOf_incr`
(Fmt/Rules6Laws.lean).

Limits. Nothing on the two other things a tree (`leafOk`; "a tree of one list has not been opened").
That a book carries a laid list's seats is a premise. The control is a toy; it closes by the plain
tactic `decide`: the one device here. This file's imports are heavy. Nothing on any property.



-/
import Johnson.P1K8R.ShareOfNums
import Johnson.ToldDescR.BookAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB)

/-- **Five things a tree, along two lists.** -/
def AllFive (ft logN : Nat) (B0 : TreeBook) : List Nat → List (Nat × Nat × Nat) → Prop
  | [], [] => True
  | t :: ts, r :: rd =>
    (∃ tree, B0.trees[t]? = some tree ∧ tree.shape.logN ≤ logN ∧ tree.number - ft = r.1 ∧
      tree.shape.logN = r.2.1 ∧ tree.shape.mainWidth + tree.shape.maskWidth = r.2.2) ∧
      AllFive ft logN B0 ts rd
  | _, _ => False

/-- The same as a test on a laid list's shapes. -/
def treesFiveB (Ld : Laid) (logN : Nat) : List Nat → List (Nat × Nat × Nat) → Bool
  | [], [] => true
  | t :: ts, r :: rd =>
    (match Ld.shapes[t]? with
      | some sh => decide (sh.logN ≤ logN) && t == r.1 && sh.logN == r.2.1 &&
          sh.mainWidth + sh.maskWidth == r.2.2
      | none => false) && treesFiveB Ld logN ts rd
  | _, _ => false

/-- A placed message's place is the laid list's. -/
theorem place_written {Ld : Laid} {B : TreeBook} (hSe : seatsCarriedB Ld B = true) {o : Nat}
    (lt : o < B.place.size) : B.place.getD o (0, 0) = Ld.places.getD o (0, 0) := by
  have h1 : B.place[o]? = some B.place[o] := Array.getElem?_eq_getElem lt
  have h2 := P1K8T.place_at hSe h1
  rw [Array.getD_eq_getD_getElem?, h1, List.getD_eq_getElem?_getD, h2]

/-- **The rising list of the messages' trees, read off the laid list.** -/
theorem trees_written {Ld : Laid} {B : TreeBook} (hSe : seatsCarriedB Ld B = true)
    {ids idsW : List Nat} (hm : ∀ o, o ∈ ids ↔ o ∈ idsW) (hlt : ∀ o ∈ idsW, o < B.place.size) :
    listOfT (ids.map fun o => (B.place.getD o (0, 0)).1) =
      listOfT (idsW.map fun o => (Ld.places.getD o (0, 0)).1) := by
  rw [listOfT_eq, listOfT_eq]
  refine eq_of_incr _ _ (Fmt.listOf_incr _) (Fmt.listOf_incr _) fun z => ?_
  rw [Fmt.listOf_mem, Fmt.listOf_mem]
  simp only [List.mem_map]
  constructor
  · rintro ⟨o, ho, e⟩
    have hw := (hm o).1 ho
    exact ⟨o, hw, by rw [← place_written hSe (hlt o hw)]; exact e⟩
  · rintro ⟨o, hw, e⟩
    exact ⟨o, (hm o).2 hw, by rw [place_written hSe (hlt o hw)]; exact e⟩

/-- **From the test's yes.** -/
theorem allFive_of {Ld : Laid} {B : TreeBook} (hSe : seatsCarriedB Ld B = true)
    (hN : ∀ (j : Nat) (t : Tree), B.trees[j]? = some t → t.number = 0 + j) (logN : Nat) :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)), (∀ t ∈ ts, t < B.trees.size) →
      treesFiveB Ld logN ts rd = true → AllFive 0 logN B ts rd
  | [], [], _, _ => trivial
  | t :: ts, r :: rd, hlt, h => by
    simp only [treesFiveB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have lt : t < B.trees.size := hlt t List.mem_cons_self
    have hT : B.trees[t]? = some B.trees[t] := Array.getElem?_eq_getElem lt
    rw [ToldDesc.tree_shape_of_seats hSe hT] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h1
    refine ⟨⟨_, hT, a, ?_, c, d⟩,
      allFive_of hSe hN logN ts rd (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) h2⟩
    rw [hN t _ hT]
    omega
  | [], _ :: _, _, h => by simp [treesFiveB] at h
  | _ :: _, [], _, h => by simp [treesFiveB] at h

/-- The toy's laid list: one tree of depth 3 and width 2 + 1. -/
def toyLaid : Laid := { shapes := [{ logN := 3, mainSymbols := #[2], maskSymbols := #[1] }] }

/-- A control at a toy. -/
theorem fiveB_can_fail :
    treesFiveB toyLaid 4 [0] [(0, 3, 3)] = true ∧ treesFiveB toyLaid 4 [0] [(0, 2, 3)] = false ∧
      treesFiveB toyLaid 4 [0] [] = false := by
  decide

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.place_written
#print axioms VerifiableInference.Desc.K2.Honest.Returns.trees_written
#print axioms VerifiableInference.Desc.K2.Honest.Returns.allFive_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fiveB_can_fail
