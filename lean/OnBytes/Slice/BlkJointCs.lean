-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJointCs.lean: a run of the program's code switch leads from joint to joint.

OnBytes/Slice/BlkJoints.lean writes down what is known between two blocks of the program's run on a
link's chain. This file proves the statement of OnBytes/Slice/BlkChain.lean on a code switch for the
joint after a fold (`SingleAt`) and any joint after the switch, from what a run of the switch has
done (OnBytes/Slice/BlkCsRun.lean: `CsRan`) and keeps (OnBytes/Slice/BlkCsKeeps.lean). It does the
part that concerns the run: the values that are kept on the way, the new group, the two rounds that
the switch takes of the view, and what every joint says of the run after the switch.

Main theorems.
 `RunAt.notes`       keeping a value changes nothing that a joint says of the run.
 `stageOthers_plain` what rides (is sent along) in a switch's message has no sample.
 `csRuns_of`         the statement on a code switch, if what the run has done gives the joint after
                     it.

Not claimed. That what the run has done gives the joint after it (the claim, the form, which oracle
messages are the parts of the new tree): it is a hypothesis. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsKeeps
import OnBytes.Slice.BlkJoints

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- Keeping a value changes nothing that a joint says of the run. -/
theorem RunAt.notes {V : Fmt.View} {K : Codes} {roots : Nat} {rest : List Fmt.RoundView} {answers : Nat}
    {c c' : Ctx} (h : RunAt V K roots rest answers c) (hn : Blk.SameButNotes c c') :
    RunAt V K roots rest answers c' := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, h.answers⟩
  · rw [hn.ch]; exact h.onView.dry
  · rw [hn.ch]; exact h.onView.first
  · rw [hn.ch]; exact h.onView.opened
  · rw [hn.ch]; exact h.pending
  · rw [hn.st]; exact h.codes
  · rw [hn.ch]; exact h.roots

/-- What rides in a switch's message beside the new tables has no sample. -/
theorem stageOthers_plain (ride : Bool) (next : IoppStage) (rest : List IoppStage) :
    ∀ n ∈ stageOthers ride next rest, n.shape.answers = 0 := by
  intro n hn
  unfold stageOthers at hn
  split at hn
  · simp at hn
  · split at hn
    · simp at hn
      rw [hn]
      rfl
    · simp at hn
      rw [hn]
      rfl

/-- A run of the program's code switch leads from the joint after a fold to a joint J', if what
the run has done gives J'. Tie must not depend on the values that are kept nor on the groups; J' not
on the values that are kept. -/
theorem csRuns_of (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (ride : Bool) (next : IoppStage)
    (later : List IoppStage) (dS dC : PQ.RD) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE)) (Tie : Ctx → SingleRows → Prop)
    (J' : GroupJoint)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hJ' : ∀ (a : Nat) (c c' : Ctx) (row : GroupRow) (L : GroupLayout) (m : Option Nat),
      Blk.SameButNotes c c' → J' a c row L m → J' a c' row L m)
    (hgive : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken) (mask : Option Nat),
      RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → stmS s rows = q → Tie c rows →
      c.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } →
      CsRan rows (switchTargetStage next.code next.maskCode next.k next.h 1) gp
        (stageOthers ride next later) c c' sw row' L' theta D →
      RunAt V K (roots + D.lay.shapes.size) rest 1 c' →
      ((ride = true ∧ sw.others[0]? = mask ∧ mask.isSome = true) ∨ (ride = false ∧ mask = none)) →
      J' 1 c' row' L' mask) :
    CsRuns ride next later
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie) J' := by
  intro answers c1 rows c2 gp c3 sw row' L' c4 c8 mask hJ n12 hnew hcs n48 hmask
  obtain rfl : answers = 1 := hJ.run.answers
  have r2 := hJ.run.notes n12
  obtain ⟨hto, e3⟩ := newGroup_inv _ _ _ _ _ hnew
  have r3 : RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c3 := by
    rw [e3]
    exact ⟨⟨r2.onView.dry, r2.onView.first, r2.onView.opened⟩, r2.pending, r2.codes, r2.roots, rfl⟩
  have t3 : Tie c3 rows := by
    refine hTie c1 c3 rows ?_ ?_ ?_ ?_ hJ.tie
    · rw [e3]; exact n12.ch
    · rw [e3]; exact n12.book
    · rw [e3]; show c2.st.oracles = _; rw [n12.st]
    · rw [e3]; show c2.st.codes = _; rw [n12.st]
  have g3 : c3.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } := by
    rw [e3, hto]
    exact withGroup_group _ _ _
  obtain ⟨theta, D, hran⟩ := csVerify_inv rows _ gp _ sw row' L' c3 c4 r3.onView.dry rfl rfl
    (stageOthers_plain ride next later) hcs
  have hrest : D.rest = rest := by
    have e : D.rS :: D.rC :: D.rest = PQ.rvSL (ckP .two) [dS, dC] τC ++ rest :=
      hran.pending.symm.trans r3.pending
    injection e with _ e2
    injection e2 with _ e3
  have r4 : RunAt V K (roots + D.lay.shapes.size) rest 1 c4 :=
    ⟨hran.onView V r3.onView, hran.pending'.trans hrest, hran.codes.trans r3.codes,
      by rw [hran.roots_eq, r3.roots], rfl⟩
  exact hJ' 1 c4 c8 row' L' mask n48
    (hgive c3 c4 rows gp sw row' L' theta D mask r3 hJ.claim t3 g3 hran r4 hmask)

end OnBytes.Slice

#print axioms OnBytes.Slice.RunAt.notes
#print axioms OnBytes.Slice.stageOthers_plain
#print axioms OnBytes.Slice.csRuns_of
