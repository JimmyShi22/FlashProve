-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PlanReads.lean: what the plan of the output head's sub-proof (Head.planH2,
OnBytes/Model/HeadPlan.lean) reads of the head's layout and of the owner's plan: nineteen numbers of
the first, four small things of the second; and that it reads no more. Two definitions with code
and a general law: nothing is evaluated. No sub-protocol imports this file.
  headReads L       the nineteen numbers: sizes of two arrays of calls and of the counts, six
                    numbers of the lookup's shape, the planes' columns, the sizes of hf, hd and hr,
                    three numbers of filled features
  ownerReads O      the label of the owner's matrix number O.iXO · at the owner's last array that
                    another sub-proof reads: rows, columns, ec, a and p · a sum of two sizes · the
                    owner's own entry for the stream
  planH2_congr      two layouts with the same headReads and two owners with the same ownerReads
                    give the same planH2, return or refusal, at all other arguments
Why. The layout holds arrays of hundreds of thousands of entries and two tables of 65,536 words; the
owner is a whole plan of a group of layers. With this law planH2 can be evaluated at small stand-ins
(PlanAtFull.lean beside).
Limits. It says nothing on whether planH2 returns. No soundness is claimed. On hiding nothing.

-/
import OnBytes.Model.HeadPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head

/-- What planH2 reads of the head's layout. -/
def headReads (L : HL) : List Nat :=
  [L.fs.calls.size, L.calls.size, L.fs.pub.size, L.fs.NT, L.fs.dT, L.fs.rK, L.fs.kT, L.fs.cK,
    L.fs.NC, L.kb, L.m, L.k, L.mD, L.kD, L.mR, L.kR, L.filled, L.fillD, L.fillR]

/-- What planH2 reads of the owner's plan. -/
def ownerReads (O : Owner) :
    Option Nat × Option (Nat × Nat × Nat × Nat × Option ShP) × Nat × Except String PlaceF :=
  ((O.tl.mats[O.iXO]?).map (·.aId),
    O.tl.ix.TX.back?.map fun last =>
      ((O.Fp.trees.getD last {}).R, (O.Fp.trees.getD last {}).K, (O.Tp.nt.getD last {}).ec,
        (O.Tp.nt.getD last {}).a, (O.Tp.nt.getD last {}).p),
    O.tl.pkMat.size + O.tl.ix.TX.size, O.tl.ownEntry "stream")

/-- The comparison with the owner's plan reads the last three of the four. -/
theorem ownerHeld_congr {O O' : Owner} (h : ownerReads O = ownerReads O') (NGr : Nat)
    (tl : HTailF2) (Fp : Fork) (Tp : Tail2) :
    ownerHeld O NGr tl Fp Tp = ownerHeld O' NGr tl Fp Tp := by
  unfold ownerReads at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  unfold ownerHeld
  rw [h3, h4]
  cases e : O.tl.ix.TX.back? with
  | none =>
    cases e' : O'.tl.ix.TX.back? with
    | none => rfl
    | some b => rw [e, e'] at h2; cases h2
  | some a =>
    cases e' : O'.tl.ix.TX.back? with
    | none => rw [e, e'] at h2; cases h2
    | some b =>
      rw [e, e'] at h2
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨r1, r2, r3, r4, r5⟩ := h2
      simp only [t2SameShape, r1, r2, r3, r4, r5, bind, Except.bind, pure, Except.pure]

/-- **planH2 reads no more.** -/
theorem planH2_congr (g : Settings) (h : Shape) (b : Border) (NGr lkW : Nat) {L L' : HL}
    {O O' : Owner} (hL : headReads L = headReads L') (hO : ownerReads O = ownerReads O') :
    planH2 g h L b O NGr lkW = planH2 g h L' b O' NGr lkW := by
  have hO1 : (O.tl.mats[O.iXO]?).map (·.aId) = (O'.tl.mats[O'.iXO]?).map (·.aId) :=
    congrArg Prod.fst hO
  unfold headReads at hL
  simp only [List.cons.injEq, and_true] at hL
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ :=
    hL
  have m1 : ∀ gid sid, matsH h L b gid sid = matsH h L' b gid sid := by
    intro gid sid
    unfold matsH
    rw [a10, a11, a12, a13, a14, a15, a16]
  have m2 : ∀ tl, slotsH h L tl lkW = slotsH h L' tl lkW := by
    intro tl
    unfold slotsH Forest.elems Forest.Shape.v Forest.Shape.d
    rw [a5, a6, a7, a8]
  have m3 : readsLength h L b = readsLength h L' b := by
    unfold readsLength
    rw [a17, a18, a19, a10]
  have m4 : readsH h L b = readsH h L' b := by
    unfold readsH
    rw [a11, a13, a15]
  have m5 : ∀ tl r, claimsH h L tl r = claimsH h L' tl r := by
    intro tl r
    unfold claimsH Forest.lins Forest.Shape.v Forest.Shape.d
    rw [a5, a6, a7, a8]
  have m6 : Forest.planeCols L.fs h.lmbH = Forest.planeCols L'.fs h.lmbH := by
    unfold Forest.planeCols
    rw [a7, a9]
  have m7 := fun tl Fp Tp => ownerHeld_congr hO NGr tl Fp Tp
  unfold planH2
  simp only [a1, a2, a3, a4, a10, m1, m2, m3, m4, m5, m6, m7]
  cases e : O.tl.mats[O.iXO]? with
  | none =>
    cases e' : O'.tl.mats[O'.iXO]? with
    | none => rfl
    | some M' => rw [e, e'] at hO1; cases hO1
  | some M =>
    cases e' : O'.tl.mats[O'.iXO]? with
    | none => rw [e, e'] at hO1; cases hO1
    | some M' =>
      rw [e, e'] at hO1
      have k : M.aId = M'.aId := Option.some.inj hO1
      simp only [k, bind, Except.bind, pure, Except.pure]

end AtFull.Head

#print axioms AtFull.Head.ownerHeld_congr
#print axioms AtFull.Head.planH2_congr
