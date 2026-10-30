-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchCountsPlans.lean: how the depths and numbers of positions that `CountsB`
(Top/BatchBoundsGen.lean) bounds change when rounds are merged or split (Iop/BatchJoin.lean,
Iop/BatchSplit.lean).

The explicit bounds are built from counts: rounds, the largest depth of a tree, leaves of all trees
(`depths`, `leaves`: Blocks/Leaves.lean; `lvJ`, `lv0`: Top/BatchLeaves.lean).
At a merge of two challenges, (J2), the round that is removed has no position, so its depth and
numbers of positions are 0 (`depthR_noPos`, `cardJ_noPos`, `card0_noPos`).
At a split of a round into a first part and a remainder, the tree of a part is at most as deep as
its round's (`depthR_fst_le`, `depthR_snd_le`). Under `ACut.OK` the remainder has no more positions
in each component than its round (`cardJ_snd_le`, `card0_snd_le`). At a split the largest depth does
not grow (`depths_splitK_le`).

A prover message of Batch has a shared and a slot's component (`RAnn`, Iop/Batch.lean). (Terms:
lean/GLOSSARY.md.)

Notation: first part, remainder: the two parts into which a split cuts the prover message of a round
(`RCut`, Iop/Split.lean); `ACut`: the annotation of a split (Iop/BatchSplit.lean); `CountsB`: what
the record of counts must bound.

Limits: Nothing for a merge by (J1), the merge of two prover messages: a tree over the positions of
two messages may have more leaves than the two trees together (1 and 4 positions: 8 leaves against
5). The counts still give one padding leaf to a component without positions; whether such a tree is
built depends on the wire record (`has0`, `hasJ`: Iop/BatchWire.lean).
-/
import Top.BatchBoundsGen
import Iop.JoinData
import Iop.SplitData
import Iop.BatchSplitProofs
import Iop.BatchJoinProofs
import Iop.JoinKit

set_option autoImplicit false

namespace Top
open Iop Blocks Top.BatchLeaves
open scoped ENNReal

/-! ## 1. A merge by (J2) -/

theorem depthR_noPos {r : Round} (pt : r.IsPoint) (np : r.Pos → Empty) : depthR pt = 0 := by
  have h : @Fintype.card r.Pos pt.finPos = 0 :=
    @Fintype.card_eq_zero_iff _ pt.finPos |>.2 ⟨fun p => (np p).elim⟩
  show Nat.clog 2 (@Fintype.card r.Pos pt.finPos) = 0
  rw [h]
  rfl

theorem cardJ_noPos {r : Round} (a : RAnn r) (pt : r.IsPoint) (np : r.Pos → Empty) :
    a.cardJ pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun p => (np p.1).elim⟩

theorem card0_noPos {r : Round} (a : RAnn r) (pt : r.IsPoint) (np : r.Pos → Empty) :
    a.card0 pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun p => (np p.1).elim⟩



/-! ## 2. A split -/

section OneCut
variable {r : Round} (c : RCut r)

theorem depthR_fst_le (pt : r.IsPoint) (p1 : c.fst.IsPoint) : depthR p1 ≤ depthR pt :=
  Nat.clog_mono_right 2
    (@Fintype.card_le_of_injective _ _ p1.finPos pt.finPos (fun p : c.PosA => c.pos (.inl p))
      fun _ _ e => Sum.inl.inj (c.pos.injective e))

theorem depthR_snd_le (pt : r.IsPoint) (p2 : c.snd.IsPoint) : depthR p2 ≤ depthR pt :=
  Nat.clog_mono_right 2
    (@Fintype.card_le_of_injective _ _ p2.finPos pt.finPos (fun p : c.PosB => c.pos (.inr p))
      fun _ _ e => Sum.inr.inj (c.pos.injective e))

variable {c} {a : RAnn r} {b : ACut c a}

theorem cardJ_snd_le (hb : b.OK) (pt : r.IsPoint) (p2 : c.snd.IsPoint) :
    b.ann2.cardJ p2 ≤ a.cardJ pt := by
  letI := pt.finPos
  letI := p2.finPos
  exact Fintype.card_le_of_injective
    (fun p : {p : c.PosB // b.B.own p = true} =>
      (⟨c.pos (.inr p.1), (hb.ownB p.1).symm.trans p.2⟩ : {p : r.Pos // a.own p = true}))
    fun _ _ e => Subtype.ext (Sum.inr.inj (c.pos.injective (congrArg Subtype.val e)))

theorem card0_snd_le (hb : b.OK) (pt : r.IsPoint) (p2 : c.snd.IsPoint) :
    b.ann2.card0 p2 ≤ a.card0 pt := by
  letI := pt.finPos
  letI := p2.finPos
  exact Fintype.card_le_of_injective
    (fun p : {p : c.PosB // b.B.own p = false} =>
      (⟨c.pos (.inr p.1), (hb.ownB p.1).symm.trans p.2⟩ : {p : r.Pos // a.own p = false}))
    fun _ _ e => Subtype.ext (Sum.inr.inj (c.pos.injective (congrArg Subtype.val e)))

end OneCut

theorem depths_splitK_le {s : Shape} (P : SPlan s) :
    ∀ (K : P.Kits) (pts : s.IsPoint), depths P.shape (pts.splitK P K) ≤ depths s pts := by
  induction P with
  | nil => intro _ _; exact Nat.le_refl _
  | keep r P ih =>
      rintro K ⟨pt, pts⟩
      exact max_le_max (le_refl _) (ih K pts)
  | cut c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨pt, pts⟩
      exact max_le ((depthR_fst_le c pt K1.pt).trans (le_max_left _ _))
        ((ih K (K2.pt, pts)).trans (max_le_max (depthR_snd_le c pt K2.pt) (le_refl _)))



end Top
