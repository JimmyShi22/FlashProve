-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/PlusAt.lean: kind K5: THE COMPOSED TESTS OF THE PUBLIC ITEMS
(pubAll, Johnson/Desc/First/PubAll.lean: a tower of eleven parts over a function base) WITH THE
WIDER TESTS (pubPlus, Johnson/Desc/First/Att/Door/Plus.lean) LAID AT ITS FOOT. No part of the tower
claims the five names: so it hands them down.

Main names:
  `pubAll_cong`: the tower's answer at an item hangs on base at that item alone.
  `pubAll_plus_else`: at an item that is none of the five the wider tower answers as the narrower.
  `pubAll_plus_seats`, `pubAll_plus_shapes`, `pubAll_plus_live`: at three names it answers the
    owners' own tests. `pubAll_plus_bare`, `pubAll_plus_left`: at the fourth: bareAttB; at the
    fifth: leftAttB.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.Door.Plus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (K3Data liveIsC)
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes)

section
variable {P : Type} (D : PubData)

theorem pubKeeper_cong' {f f' : Pub → P × S → Bool} {q : Pub} {a : P × S} (h : f q a = f' q a) :
    pubKeeper D.nsOf f q a = pubKeeper D.nsOf f' q a := by
  cases q <;> first | rfl | exact h

/-- **The tower's answer at an item hangs on base at that item alone.** -/
theorem pubAll_cong {b b' : Pub → P × S → Bool} {q : Pub} {a : P × S} (h : b q a = b' q a) :
    pubAll D b q a = pubAll D b' q a :=
  pubForms_cong D _ _ _ _ (pubK13C_cong D _ _ _ _ (pubK3_cong D _ _ _ _ (pubK6K7_cong D _ _ _ _ (pubK4_cong D _ _ _ _
    (pubP1_cong D _ _ _ _ (pubK5_cong D _ _ _ _ (pubSent_cong D _ _ _ _ (pubSent1_cong D _ _ _ _
      (pubLeft_cong D _ _ _ _ (pubKeeper_cong' D h))))))))))

variable (L : Laid) (M : List OracleShape) (d3 : K3Data) (b : Pub → P × S → Bool)

theorem pubAll_plus_else {q : Pub} (h : ∀ n s, q = .more n s → isWide (n, s) = false) (a : P × S) :
    pubAll D (pubPlus L M d3 b) q a = pubAll D b q a := by
  refine pubAll_cong D ?_
  cases q with
  | more n s => exact pubPlus_more_else L M d3 b (h n s rfl) a
  | _ => rfl

theorem pubAll_plus_seats (a : P × S) :
    pubAll D (pubPlus L M d3 b) (.more none "K12.seatsCarried") a = atFirstSeats L a.2 := rfl

theorem pubAll_plus_shapes (a : P × S) :
    pubAll D (pubPlus L M d3 b) (.more none "K12.msgShapes") a = atFirstShapes M a.2 := rfl

theorem pubAll_plus_live (m : Nat) (a : P × S) :
    pubAll D (pubPlus L M d3 b) (.more (some m) "frame.liveIs") a = liveIsC d3 a.2 := by
  rw [pubAll_else D _ (.more (some m) "frame.liveIs") rfl rfl rfl rfl rfl rfl (by simp [k5Item]) (by simp [FillSent.sentItem])
    (by simp [FillSent.sent1Item]) (by simp [FillBare.leftItem]) rfl a]
  rfl

theorem pubAll_plus_bare (m : Nat) (a : P × S) :
    pubAll D (pubPlus L M d3 b) (.more (some m) "K5.rowsBare") a = bareAttB a.2 := by
  rw [pubAll_else D _ (.more (some m) "K5.rowsBare") rfl rfl rfl rfl rfl rfl (by simp [k5Item]) (by simp [FillSent.sentItem])
    (by simp [FillSent.sent1Item]) (by simp [FillBare.leftItem]) rfl a]
  rfl

theorem pubAll_plus_left (m : Nat) (a : P × S) :
    pubAll D (pubPlus L M d3 b) (.more (some m) "K5.lookLeft") a = leftAttB a.2 := by
  rw [pubAll_else D _ (.more (some m) "K5.lookLeft") rfl rfl rfl rfl rfl rfl (by simp [k5Item]) (by simp [FillSent.sentItem])
    (by simp [FillSent.sent1Item]) (by simp [FillBare.leftItem]) rfl a]
  rfl

end

end H2K5.Door

#print axioms H2K5.Door.pubAll_cong
#print axioms H2K5.Door.pubAll_plus_else
#print axioms H2K5.Door.pubAll_plus_seats
#print axioms H2K5.Door.pubAll_plus_shapes
#print axioms H2K5.Door.pubAll_plus_live
#print axioms H2K5.Door.pubAll_plus_bare
#print axioms H2K5.Door.pubAll_plus_left
