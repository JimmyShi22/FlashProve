-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/AlikeFull.lean (kind K10): THE TWO TESTS OF SeatsOfLink.lean AT THE
WRITTEN VALUES OF THE FULL SIZE, AT ALL 26 WRITTEN LISTS: BY EVALUATIONS IN LEAN's KERNEL; and the
two sentences there. Definitions with code, and theorems.
  `radW k i`: the written radius of the i-th sampled oracle message of the first chain's k-th
    sending (`Johnson.G.radsFull`, Johnson/HB/LLHARD/RadiiWritten.lean); 0 where
    there is none: the form in which `rad_in_scope` (RadiiInScope.lean) gives the radii of the rows
    of the sendings (`Johnson.G.sendRowsOf`, G/LinkSig.lean). `mlFull`: the members' plain lists by
    the make (`P5T.memberListsR`) at 82 sendings, these radii and the written seats `P5T.psFull`.
  `alikeB_full`, `hitB_full`: **both tests say yes at every l < 26**, at own := `P5T.N0Full.group
    l`, lo := the l-th of `Johnson.G.linksFullLit`, the seats `seatsOfLink P5T.psFull l`.
  `hitB_full_zero`, `alikeB_full_naive`: NEGATIVE LINES: with all radii 0 no link passes the second
    test; with the group's own list for the seats link 0 fails the first.
  `alike_full`, `hit_full`: **so, at every l < 26: every member of `msOf mlFull` at a tenant of the
    group is alike to a place of the written list at `seatK10`; and every place is alike to a
    member.**
Limits. AT WRITTEN VALUES. That the composed meaning's members at a public part in scope are `msOf
mlFull` is not said here: it wants the plan's seats, the number of sendings and the radii off the
rows of the sendings (`sendRowsOf`) to be the written ones. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.HB.LLHARD.RadiiWritten
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.Sound (msOf seatOf Alike)

/-- **The written radii**, by (sending, place); 0 where there is none. -/
def radW (k i : ℕ) : ℕ := (((Johnson.G.radsFull[k]?).bind (·[i]?)).map (·.2)).getD 0

/-- **The members' plain lists at the written values.** -/
def mlFull : MemberLists := P5T.memberListsR 82 radW P5T.psFull

set_option maxRecDepth 1000000 in
/-- **(W) Every member at a tenant of the group is alike to a place of the written list.** -/
theorem alikeB_full :
    ((List.range 26).all fun l => alikeB mlFull (P5T.N0Full.group l)
      (Johnson.G.linksFullLit.getD l []) (seatsOfLink P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(W) Every place of the written list is alike to a member.** -/
theorem hitB_full :
    ((List.range 26).all fun l => hitB mlFull (Johnson.G.linksFullLit.getD l [])
      (seatsOfLink P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With all radii 0 no link passes the second test. -/
theorem hitB_full_zero :
    ((List.range 26).any fun l => hitB (P5T.memberListsR 82 (fun _ _ => 0) P5T.psFull)
      (Johnson.G.linksFullLit.getD l []) (seatsOfLink P5T.psFull l)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With the group's own list for the seats link 0 fails the first test. -/
theorem alikeB_full_naive :
    alikeB mlFull (P5T.N0Full.group 0) (Johnson.G.linksFullLit.getD 0 []) (P5T.N0Full.group 0) =
      false := by decide +kernel

/-- **THE FIRST SENTENCE AT THE WRITTEN VALUES.** -/
theorem alike_full (l : ℕ) (hl : l < 26) :
    ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group l →
      ∃ i : Fin (Johnson.G.linksFullLit.getD l []).length,
        Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
          seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l⟩, i⟩ :=
  alike_of_B (List.all_eq_true.1 alikeB_full l (List.mem_range.2 hl))

/-- **THE SECOND.** -/
theorem hit_full (l : ℕ) (hl : l < 26) :
    ∀ i : Fin (Johnson.G.linksFullLit.getD l []).length, ∃ x ∈ msOf mlFull,
      Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
        seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l⟩, i⟩ :=
  hit_of_B (List.all_eq_true.1 hitB_full l (List.mem_range.2 hl))

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.alikeB_full
#print axioms VerifiableInference.Desc.First.Close.hitB_full
#print axioms VerifiableInference.Desc.First.Close.hitB_full_zero
#print axioms VerifiableInference.Desc.First.Close.alikeB_full_naive
#print axioms VerifiableInference.Desc.First.Close.alike_full
#print axioms VerifiableInference.Desc.First.Close.hit_full
