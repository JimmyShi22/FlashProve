-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchLeaves.lean: the bound `cTrees` on the leaves of one execution of Batch, by components.

In Batch a round has up to two trees: one over the shared component of the prover message, built
once, and one over a slot's component, built for each of the Ns slots (Iop/BatchWireOf.lean).
`Compile.Batch.cTrees` counts both in every round; it enters the hash terms of the index-privacy
error ζ (`xTree`, Compile/Batch/Counts.lean; index privacy: ZKCP/Gen.lean). Bounding both trees of a
round by a tree over all positions of the round overcounts by a factor of up to Ns + 1. This file
defines the two sums of which `cTrees` consists at the wire record over challenge samplers:
  `lvJ`, `lv0`          The leaves of the trees of one slot, and of the shared trees, summed over
                        the rounds (a component without positions counts one leaf). That cTrees = Ns
                        · lvJ + lv0 is proved, for the wire record over challenge samplers, in
                        Top/BatchBoundsGenDr.lean (`cTrees_ofDraws`).
  `lvJ_slot`, `lv0_slot`, `lvJ_shared`, `lv0_shared`:
      rounds in which only the slots send: `lvJ` is the ordinary count (Blocks/Leaves.lean), `lv0`
      the number of rounds; rounds in which only the shared component is sent: the other way round.

(Terms: lean/GLOSSARY.md.)
-/
import Compile.Batch.Counts
import Iop.BatchWireOf
import Blocks.Leaves
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Top.BatchLeaves
open Iop Blocks Compile Compile.Batch

/-- The leaves of the trees of one slot. -/
def lvJ : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => 2 ^ Nat.clog 2 (a.cardJ pt) + lvJ s A pts

/-- The leaves of the shared trees. -/
def lv0 : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => 2 ^ Nat.clog 2 (a.card0 pt) + lv0 s A pts

theorem lvJ_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
      lvJ (s ++ t) (RoundSplits.app A B) (pointApp a b) = lvJ s A a + lvJ t B b
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (x, A), B, (pt, a), b => by
      show 2 ^ Nat.clog 2 (x.cardJ pt) + lvJ _ (RoundSplits.app A B) (pointApp a b) =
        2 ^ Nat.clog 2 (x.cardJ pt) + lvJ _ A a + lvJ _ B b
      rw [lvJ_app A B a b, Nat.add_assoc]

theorem lv0_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
      lv0 (s ++ t) (RoundSplits.app A B) (pointApp a b) = lv0 s A a + lv0 t B b
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (x, A), B, (pt, a), b => by
      show 2 ^ Nat.clog 2 (x.card0 pt) + lv0 _ (RoundSplits.app A B) (pointApp a b) =
        2 ^ Nat.clog 2 (x.card0 pt) + lv0 _ A a + lv0 _ B b
      rw [lv0_app A B a b, Nat.add_assoc]

/-! ## One round -/

theorem cardJ_ofSlot (k : Kind) (r : Round) (pt : r.IsPoint) :
    (RAnn.ofSlot k r).cardJ pt = @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)

theorem card0_ofSlot (k : Kind) (r : Round) (pt : r.IsPoint) : (RAnn.ofSlot k r).card0 pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun p => Bool.noConfusion p.2⟩

theorem card0_ofShared (k : Kind) (r : Round) (pt : r.IsPoint) :
    (RAnn.ofShared k r).card0 pt = @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)

theorem cardJ_ofShared (k : Kind) (r : Round) (pt : r.IsPoint) :
    (RAnn.ofShared k r).cardJ pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun p => Bool.noConfusion p.2⟩

theorem two_clog_zero : 2 ^ Nat.clog 2 0 = 1 := rfl

/-! ## The same rule in every round -/

theorem lvJ_slot (k : Kind) :
    ∀ (s : Shape) (pts : s.IsPoint), lvJ s (RoundSplits.const (RAnn.ofSlot k) s) pts = leaves s pts
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show 2 ^ Nat.clog 2 ((RAnn.ofSlot k r).cardJ pt) + lvJ s (RoundSplits.const (RAnn.ofSlot k) s) pts =
        2 ^ depthR pt + leaves s pts
      rw [cardJ_ofSlot, lvJ_slot k s pts]
      rfl

theorem lv0_slot (k : Kind) :
    ∀ (s : Shape) (pts : s.IsPoint), lv0 s (RoundSplits.const (RAnn.ofSlot k) s) pts = s.length
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show 2 ^ Nat.clog 2 ((RAnn.ofSlot k r).card0 pt) + lv0 s (RoundSplits.const (RAnn.ofSlot k) s) pts =
        s.length + 1
      rw [card0_ofSlot, lv0_slot k s pts, two_clog_zero, Nat.add_comm]

theorem lv0_shared (k : Kind) :
    ∀ (s : Shape) (pts : s.IsPoint), lv0 s (RoundSplits.const (RAnn.ofShared k) s) pts = leaves s pts
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show 2 ^ Nat.clog 2 ((RAnn.ofShared k r).card0 pt) +
          lv0 s (RoundSplits.const (RAnn.ofShared k) s) pts =
        2 ^ depthR pt + leaves s pts
      rw [card0_ofShared, lv0_shared k s pts]
      rfl

theorem lvJ_shared (k : Kind) :
    ∀ (s : Shape) (pts : s.IsPoint), lvJ s (RoundSplits.const (RAnn.ofShared k) s) pts = s.length
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show 2 ^ Nat.clog 2 ((RAnn.ofShared k r).cardJ pt) +
          lvJ s (RoundSplits.const (RAnn.ofShared k) s) pts = s.length + 1
      rw [cardJ_ofShared, lvJ_shared k s pts, two_clog_zero, Nat.add_comm]

end Top.BatchLeaves
