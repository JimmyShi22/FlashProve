-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorAtRun.lean

What it proves. The door at the proximity test on G_u as a conclusion, at a run of the frame's
walking prover (runC) at the proof file's own description under the head P5J.AtMg. At every book and
every prover whose key is the instance's: where ready and runC return and a part of the side at the
test on G_u is called, the stand that midSharedAtW returns is there, and at its input and at a front
that has seen the eight's rounds as the stand has seen them, doorUF (DoorsByShape.lean) with the
reader colsLoc (DoorReturns.lean) at the prover's own stored columns is off its fall-back: its state
is what the seat's way in makes of the state that the description's own fold over the eight returns,
from the description's own start, at the shared view's rounds and columns.

Names.
  door_at_run   the theorem.

By what. called_at_run (CalledAtRun.lean); door_of_cols (DoorAtWalk.lean); foldBlocks_more
(DoorReturns.lean); flatOf_carried (Johnson/Desc/K14/Honest/FlatForm.lean); facts_at_head
(NearAtHead.lean); the head's field laid.planOk.

Limits.
- It is of the walk (runC). midSharedAtW (ProofFile/Honest/MidW.lean) is made of ready, of the start
  as runC lays it and of walk over the Steps in front of the part: m is the state that this walk
  holds. The frame's run (play) reaches stands at which the verifier would long have refused; there
  doorUF falls back as before, and nothing is said here.
- Nothing on whether ready or runC returns, or whether the part is called: at no prover and no book
  is that shown here.
- hα is a premise on the prover: the key that its shared parts are given is the instance's.
- hR, S and h9 are on the filling and the book: where the part's rounds are, and that the blocks in
  front of its block are the shared chain's front block and the eight.
- It moves no count. It gives no SaysAt (AsksWhole.lean); at a called part the state is not the
  fall-back, so there SaysAt is a sentence on the prover's values. The test on G_u alone.
- What MarksBehind.lean stands over are files of this library.
  Also beneath this file: K12/LiveField.lean and, of the frame's authors (ProofFile/Honest/): Blind,
  Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW, WalkHeard, WalkLive, WalkOpened,
  Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledAtRun
import Johnson.Desc.ProofFile.Honest.K12.DoorAtWalk
import Johnson.Desc.ProofFile.Honest.K12.DoorAtFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (Seat.enter)
open Desc.K14 (St blocks first)
open Desc.K14.Honest (flatOf_carried)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The door at the test on G_u as a conclusion, at a run of the proof file's own description
under the head.** F := P5J.F0T o Zp Np cF. At every book and every prover whose key is the
instance's (hα): where ready and runC return and a part of the side at the test on G_u is called
(i: how many rounds of the test come before the part), the stand that midSharedAtW returns is there,
and at its input and at a front that has seen the eight's rounds as the stand has, doorUF with the
reader colsLoc at the prover's own stored columns is off its fall-back: its state is what the seat's
way in makes of the state d8 that the description's own fold over the eight returns, from the
description's own start, at the shared view's rounds and columns.
Public: the head h, hb. On the prover: hα. On the filling and the book: hR, S, h9 (the blocks in
front of the side's are the nine). On the run: hrun, hc.
No premise on the form of the rounds, on the key's sizes or values or on the stored columns' widths.
It is of the walk (runC), not of play (run); nothing on whether runC returns or calls the part. No
SaysAt follows. The test on G_u alone. -/
theorem door_at_run {W₀ Rc Tr X₀ Y V Pb X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre t : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (d8 : St) (rest : List Fmt.RoundView)
      (more : List OpenedColumn),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length + i ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      ∀ fr : Front X, fr.seen.rounds =
          m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length →
        Seat.enter (·.gU) (·.firstMask) d8 =
          .ok (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
            (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
            m.st.input fr) := by
  obtain ⟨m, s, cols, more, rest, hm, hin, hrounds, hlen, hcols, hfold, hfill⟩ :=
    called_at_run h.laid.planOk hR σ u pre t i S hrun hc
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  subst epre
  have eR : [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  have hlen : m.seen.length =
      (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds)).length +
        i := hlen
  have hfold' : foldBlocks 0 ([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl))
      (first (K1.qAt Zp Np).codes x.pub.key)
      (m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
        (·.rounds)).length) cols = .ok (s, [], []) := hfold
  have hfill : ProofFile.Honest.fillCols (ProofFile.Honest.readsOf 1 0 (P.storedWords w₀ rc)
            (ProofFile.Honest.treeOwn (r.run.played.2.1.take
                    (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
                      (·.rounds)).length))
            (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds))
            ((m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
              (·.rounds)).length).map (·.drawn))) [] = .ok cols := hfill
  rw [eR] at hlen hfold' hfill
  obtain ⟨g1, g2⟩ := door_of_cols (V := Common W₀ Rc TableKey) (X := X) Zp.p.chains (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb (facts_at_head h).2.2 _
    (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))) 1 (P.storedWords w₀ rc) _ x.pub.key _ cols s hfold' hfill
  have gE := Desc.K14.Honest.peel_front Zp.p.chains 0 _ _ _ _ _
    (Desc.K14.Honest.fold_like 0 _ _ (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5
      (.cons l6 (.cons l7 (.cons l8 .nil))))))))) _ _ _ _ hfold')
  have hview := foldBlocks_more 0 _ _ _ _ _ gE
    (m.seen.drop ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length ++ rest) more
  rw [← List.append_assoc, List.take_append_drop, ← hrounds, ← hcols] at hview
  refine ⟨m, s, _, more, hm, hlen, hview, fun fr hfr => ?_⟩
  refine g2 (fun w => w.key) (fun w => P.storedWords w.w₀ w.rc) m.st.input fr ?_ ?_ hfr
  · rw [hin]
    exact hα x
  · rw [hin]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.door_at_run
