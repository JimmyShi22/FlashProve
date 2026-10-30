-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkChain.lean: the program's yes on a link's chain, followed from block to block.

The program is the Lean verifier in OnBytes/. If its decision on a link's chain is a yes, then one
block, `linkVerify` (OnBytes/Iop/Link.lean), has run through on the view and no named test has
failed (a named test, `Blk.check`, does not stop a run; its failure is noted in the context). A yes
asks more, that the run uses up the view, which is not used here. OnBytes/Slice/BlkTop.lean takes
such a run apart into the runs of the link's steps, the batching, two folds, two code switches and
the base case. This file follows a property along these runs. What is known between two blocks is a
predicate on the context and on the claim that the program holds there, a joint. For each block one
statement says: if the joint in front of the block holds and the block runs through, then the next
joint holds where the run ends. From these six statements and a yes of the decision follows what the
last of them concludes.

The joints are variables here. So this file unfolds no definition of the program, and a joint can be
made stronger without a change to it.

Main definitions.
 `GroupJoint`, `SingleJoint`   the types of a joint.
 `HeadRuns`, `FoldRuns`, `CsRuns`, `LastRuns`   a run of a block leads from joint to joint.
Main theorem.
 `blk_chain`   the six statements, joined.

Not claimed. That any of the six statements holds for joints of interest.
-/
import OnBytes.Slice.BlkTop

set_option autoImplicit false

namespace OnBytes.Slice
open Params (LinkShape IoppStage IoppChoice)

/-! ## A run of a block leads from joint to joint -/

/-- A joint before a fold or the base case: the number of answers to a sample; the context; the
claim on the group, the group's layout, and the mask that has come for the next step. -/
abbrev GroupJoint : Type := Nat → Ctx → GroupRow → GroupLayout → Option Nat → Prop

/-- A joint after a fold: the number of answers to a sample; the context; the claim on the folded
rows. -/
abbrev SingleJoint : Type := Nat → Ctx → SingleRows → Prop

/-- The link's steps and the batching lead from the context c0 to the joint J. -/
def HeadRuns (S : LinkShape) (first further : TableKey) (st1 : IoppStage) (c0 : Ctx)
    (J : GroupJoint) : Prop :=
  ∀ (x : LinkRun) (c1 : Ctx) (answers : Nat) (ca : Ctx) (St : Statement) (cb : Ctx)
    (row : GroupRow) (L : GroupLayout) (cd ce : Ctx) (G : Group) (cf : Ctx),
    (linkStepsVerify S first further).Yields c0 x c1 → Blk.samples.Yields c1 answers ca →
    Blk.statement.Yields ca St cb → ioppOk St.codes S.test answers = true →
    (batVerify x.group).Yields cb (row, L) cd →
    (Blk.note "BAT: target" row.target).Yields cd () ce → (Blk.group x.group).Yields ce G cf →
    (G.code == st1.code && G.maskCode == st1.maskCode && L.k == st1.k && L.h == st1.h) = true →
    J answers cf row L x.mask

/-- A fold at the stage cur leads from the joint J to the joint J'. -/
def FoldRuns (cur : IoppStage) (J : GroupJoint) (J' : SingleJoint) : Prop :=
  ∀ (answers : Nat) (c : Ctx) (row : GroupRow) (L : GroupLayout) (mask : Option Nat)
    (rows : SingleRows) (c' : Ctx), J answers c row L mask →
    (foldVerify (ioppFoldShape cur L) row mask).Yields c rows c' → J' answers c' rows

/-- A code switch to the stage next, with the new group before it, leads from the joint J to the
joint J'. From c1 to c2 and from c4 to c8 the program only keeps intermediate values
(`Blk.SameButNotes`). -/
def CsRuns (ride : Bool) (next : IoppStage) (rest : List IoppStage) (J : SingleJoint)
    (J' : GroupJoint) : Prop :=
  ∀ (answers : Nat) (c1 : Ctx) (rows : SingleRows) (c2 : Ctx) (to : Nat) (c3 : Ctx) (s : Switched)
    (row' : GroupRow) (L' : GroupLayout) (c4 c8 : Ctx) (mask : Option Nat),
    J answers c1 rows → Blk.SameButNotes c1 c2 →
    (Blk.newGroup next.code next.maskCode).Yields c2 to c3 →
    (csVerify rows (switchTargetStage next.code next.maskCode next.k next.h answers) to
      (stageOthers ride next rest)).Yields c3 (s, row', L') c4 →
    Blk.SameButNotes c4 c8 →
    ((ride = true ∧ s.others[0]? = mask ∧ mask.isSome = true) ∨ (ride = false ∧ mask = none)) →
    J' answers c8 row' L' mask

/-- The last stage: from the joint J, a run of the last stage after which no named test has
failed gives the goal. -/
def LastRuns (ride : Bool) (cur : IoppStage) (J : GroupJoint) (Goal : Prop) : Prop :=
  ∀ (answers : Nat) (c : Ctx) (row : GroupRow) (L : GroupLayout) (mask : Option Nat) (c' : Ctx),
    J answers c row L mask → (ioppStagesVerify answers ride cur [] row L mask).Yields c () c' →
    c'.failed = none → Goal

/-! ## The chain -/

/-- The program's yes, followed from block to block, for a proximity test of three stages. -/
theorem blk_chain (S : LinkShape) (first further : TableKey) (st1 st2 st3 : IoppStage)
    (htest : S.test = [st1, st2, st3]) (s : Start) (v : Fmt.View) (J0 J2 J4 : GroupJoint)
    (J1 J3 : SingleJoint) (Goal : Prop)
    (hHead : HeadRuns S first further st1 (startCtx s v) J0) (hF1 : FoldRuns st1 J0 J1)
    (hC1 : CsRuns S.choice.masksRide st2 [st3] J1 J2) (hF2 : FoldRuns st2 J2 J3)
    (hC2 : CsRuns S.choice.masksRide st3 [] J3 J4)
    (hLast : LastRuns S.choice.masksRide st3 J4 Goal)
    (h : (linkVerify S first further).decides s v = true) : Goal := by
  have tr : ∀ {a b c : Ctx}, Blk.SameButNotes a b → Blk.SameButNotes b c → Blk.SameButNotes a c :=
    fun h1 h2 =>
      ⟨h2.ch.trans h1.ch, h2.st.trans h1.st, h2.book.trans h1.book, h2.failed.trans h1.failed⟩
  obtain ⟨cEnd, hrun, hfail⟩ := decides_yields _ s v h
  obtain ⟨x, c1, c2, hsteps, htst, hall⟩ := linkVerify_inv S first further _ _ hrun
  rw [htest] at htst
  obtain ⟨answers, ca, St, cb, row, L, cd, ce, G, cf, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    ioppVerify_inv _ _ _ _ _ _ _ htst
  have j0 : J0 answers cf row L x.mask :=
    hHead x c1 answers ca St cb row L cd ce G cf hsteps k1 k2 (by rw [htest]; exact k3) k4 k5 k6 k7
  -- the first stage
  obtain ⟨rows1, a1, a2, to1, a3, s1, row1, L1, a4, a5, a6, a7, a8, mask1, f1, n1, g1, w1, n2, n3,
    n4, n5, hm1, r1⟩ := ioppStages_step_inv _ _ _ _ _ _ _ _ _ _ k8
  have j1 : J1 answers a1 rows1 := hF1 answers cf row L x.mask rows1 a1 j0 f1
  have j2 : J2 answers a8 row1 L1 mask1 :=
    hC1 answers a1 rows1 a2 to1 a3 s1 row1 L1 a4 a8 mask1 j1 (Blk.yields_note _ _ _ _ n1) g1 w1
      (tr (tr (tr (Blk.yields_note _ _ _ _ n2)
        (Blk.yields_noteBy _ _ _ _ n3)) (Blk.yields_note _ _ _ _ n4)) (Blk.yields_note _ _ _ _ n5))
      hm1
  -- the second stage
  obtain ⟨rows2, b1, b2, to2, b3, s2, row2, L2, b4, b5, b6, b7, b8, mask2, f2, o1, g2, w2, o2, o3,
    o4, o5, hm2, r2⟩ := ioppStages_step_inv _ _ _ _ _ _ _ _ _ _ r1
  have j3 : J3 answers b1 rows2 := hF2 answers a8 row1 L1 mask1 rows2 b1 j2 f2
  have j4 : J4 answers b8 row2 L2 mask2 :=
    hC2 answers b1 rows2 b2 to2 b3 s2 row2 L2 b4 b8 mask2 j3 (Blk.yields_note _ _ _ _ o1) g2 w2
      (tr (tr (tr (Blk.yields_note _ _ _ _ o2)
        (Blk.yields_noteBy _ _ _ _ o3)) (Blk.yields_note _ _ _ _ o4)) (Blk.yields_note _ _ _ _ o5))
      hm2
  -- the last stage
  rw [requireAllTested_inv _ _ hall] at hfail
  exact hLast answers b8 row2 L2 mask2 c2 j4 r2 hfail

end OnBytes.Slice

#print axioms OnBytes.Slice.blk_chain
