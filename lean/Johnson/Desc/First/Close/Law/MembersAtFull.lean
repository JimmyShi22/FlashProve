-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MembersAtFull.lean (kind K10): THE PUBLIC LIST OF A LINK's GROUP's
MEMBERS (`membersPub`, MembersPublic.lean) IS THE PLAN's NUMBERING (`noK10`, NoOfLink.lean) OF THE
WRITTEN LIST's MEMBERS, IN THEIR ORDER, AT LINKS 1 TO 23: at the written values by an evaluation in
Lean's kernel; and in the form of the premise hT3 of ShapesReached.lean, where the first chain's cut
is the written one. Theorems.
Why. K10's law has ONE letter for a member's number in the statement. Some files' payers hold it as
a term on the state (the n-th entry of the group's own list), others' as a term off the plan.
`members_public` makes the first a public list; here that list is the second.
  `seatsPlanW`: the written plan's seats, all 199, in the order of sending. `membersPub_free`:
    `membersPub` reads the table's numbers through msgsAt alone, which `withTold` lays: so the
    numbers beneath drop out.
  `t3B_full`: **the two lists are one at l = 1 .. 23**, at the written tellings `toldCut`
    (Johnson/Desc/First/CutWritten.lean). THE NEGATIVE LINES: `t3B_zero`: at l = 0 they differ
    (`membersPub`'s text counts the index masks' message); `t3B_told`: at l = 1, with the first
    telling dropped, they differ.
  `t3_full`: the equation, at any numbers beneath. `t3_at_cut`: **the same at `toldOf bs`, where
    `cutOf bs = cutFirstFull`: hT3's own text at no := `noK10 seatsPlanW ..`.**
Limits. Links 0 and 24 are not here. hc (the cut is the written one) is a premise: an accept of the
verifier's entry test on the cut gives it: a law that is that test's files' to show. THE WRITTEN CUT
RESTS ON PRINTS OF LEAN's EVALUATOR (CutWritten.lean's own limit). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.MembersPublic
import Johnson.Desc.First.Close.Law.NoOfLink
import Johnson.Desc.First.Close.Law.Drawn.Def
import Johnson.Desc.First.CutWritten
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open Johnson.G (linksFullLit)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The written plan's seats, in the order of sending. -/
abbrev seatsPlanW : List (ℕ × ℕ) := P5T.psFull.map fun p => (p.j, p.t)

/-- `membersPub` reads the numbers through msgsAt alone, which `withTold` lays. -/
theorem membersPub_free (N₀ N₁ : Numbers) (ps : List Place) (told : List (List Oracle))
    (sh : Params.ReqShape) (l : ℕ) :
    membersPub (N₀.withTold ps told) sh l = membersPub (N₁.withTold ps told) sh l := rfl

set_option maxRecDepth 1000000 in
/-- **(W) The two lists are one at l = 1 .. 23.** -/
theorem t3B_full :
    ((List.range 23).all fun j =>
      decide (membersPub (P5T.N0Full.withTold IM.placesW toldCut) shapeFull (j + 1) =
        (membersOf (linksFullLit.getD (j + 1) [])).map
          (noK10 seatsPlanW (linksFullLit.getD (j + 1) []) P5T.psFull (j + 1)))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** At l = 0 they differ. -/
theorem t3B_zero :
    decide (membersPub (P5T.N0Full.withTold IM.placesW toldCut) shapeFull 0 =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** At l = 1, with the first telling dropped, they differ. -/
theorem t3B_told :
    decide (membersPub (P5T.N0Full.withTold IM.placesW (toldCut.drop 1)) shapeFull 1 =
      (membersOf (linksFullLit.getD 1 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 1 []) P5T.psFull 1)) = false := by decide +kernel

/-- **THE EQUATION AT THE WRITTEN TELLINGS**, at any numbers beneath. -/
theorem t3_full (N₀ : Numbers) (l : ℕ) (h1 : 1 ≤ l) (h24 : l < 24) :
    membersPub (N₀.withTold IM.placesW toldCut) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map
        (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l) := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  rw [membersPub_free N₀ P5T.N0Full]
  exact of_decide_eq_true (List.all_eq_true.1 t3B_full j (List.mem_range.2 (by omega)))

/-- **hT3's OWN TEXT**, where the first chain's cut is the written one. -/
theorem t3_at_cut {St Cl : Type} {bs : List (Block St Cl)}
    (hc : VerifiableInference.PlanWritten.cutOf bs = VerifiableInference.PlanWritten.cutFirstFull)
    (N₀ : Numbers) (l : ℕ) (h1 : 1 ≤ l) (h24 : l < 24) :
    membersPub (N₀.withTold IM.placesW (toldOf bs)) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map
        (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l) := by
  rw [(told_at_written hc).2]
  exact t3_full N₀ l h1 h24

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.membersPub_free
#print axioms VerifiableInference.Desc.First.Close.t3B_full
#print axioms VerifiableInference.Desc.First.Close.t3B_zero
#print axioms VerifiableInference.Desc.First.Close.t3B_told
#print axioms VerifiableInference.Desc.First.Close.t3_full
#print axioms VerifiableInference.Desc.First.Close.t3_at_cut
