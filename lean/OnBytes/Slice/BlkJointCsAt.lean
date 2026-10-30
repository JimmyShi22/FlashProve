-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJointCsAt.lean: a run of the program's code switch leads from the joint after a
fold to the joint before the next fold.

OnBytes/Slice/BlkJointCs.lean does the part of a code switch that concerns the run. This file adds
what the run has computed: the claim (OnBytes/Slice/BlkCsClaim.lean), the new group's layout
(OnBytes/Slice/BlkCsLay.lean) and the number of the mask that rode (was sent along) in the switch's
message.

Main definition.
 `FoldedOk`   what is public of the three folded rows before a switch: their codes, that no member
              is kept, the sizes of the two mask vectors, the number of variables of the form's
              tensors, none of which has a written-out factor.
Main theorems.
 `stageOthers_size`   if masks ride, one oracle message rides in a switch's message.
 `csRan_mask`         it has the number after the new oracle message's.
 `csRan_group`        the group before the switch is the one that the statement had at the start.
 `csRuns_group`       the statement of OnBytes/Slice/BlkChain.lean on a code switch, from `SingleAt`
                      at a claim q to `GroupAt` at `csNextW` of q.

Not claimed. What `csRuns_group` asks, as hypotheses with names, is not shown here. `hOk`: the tie
after the fold gives `FoldedOk`. `hread`: the symbols that the run has read are the long symbols of
the word y. `hTie'`: the tie before the next fold. And public facts on sizes. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsClaim
import OnBytes.Slice.BlkJointCs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-- What is public of the three folded rows before a switch from the stage s to the stage s'.
K: the statement's codes. nc, nz: the numbers of the new stage's codes. -/
structure FoldedOk (s s' : Sg) (K : Codes) (nc nz : ℕ) (old : SingleRows) : Prop where
  /-- the four codes are the two stages'; two mask rows; no kept member -/
  prog : CsProg s s' K old nc nz
  /-- no form on a kept member -/
  kept : old.kept = #[]
  /-- the vector on the carried mask row has the mask code's message length -/
  d0 : (old.d.getD 0 #[]).size = s.Z.l
  /-- the vector on the fresh mask row likewise -/
  d1 : (old.d.getD 1 #[]).size = s.Z.l
  /-- each tensor of the form has the variables of the main code's message -/
  vars : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l
  /-- no tensor of the form has a written-out factor -/
  plain : PlainForm old.c

/-- If masks ride, one oracle message rides in a switch's message. -/
theorem stageOthers_size (next : IoppStage) (later : List IoppStage) :
    (stageOthers true next later).size = 1 := by
  unfold stageOthers
  cases later.isEmpty <;> rfl

section
variable {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {c c' : Ctx} {out : Switched}
  {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The mask that rode in the switch's message has the number after the new oracle message's. -/
theorem csRan_mask {next : IoppStage} {later : List IoppStage}
    (h : CsRan old T gp (stageOthers true next later) c c' out row lay theta D)
    (mask : Option Nat) (hm : out.others[0]? = mask) : mask = some (c.st.oracles.size + 1) := by
  rw [← hm, h.riders, stageOthers_size]
  simp

/-- The group before the switch (`D.G`) is the group that the statement had under the number gp at
the start of the run. -/
theorem csRan_group {others : Array OracleNotice} {G : Group}
    (h : CsRan old T gp others c c' out row lay theta D) (hg : c.st.groups[gp]? = some G) :
    D.G = G :=
  Option.some.inj (h.group0.symm.trans hg)

end

/-- A run of the program's code switch leads from the joint after a fold to the joint before the
next fold. s, s': the two stages. y: the three folded words. The hypotheses: see the file's head. -/
theorem csRuns_group (V : Fmt.View) (K : Codes) (roots : Nat) {s s' : Sg} (hf : CsFit s s')
    (next : IoppStage) (later : List IoppStage) (hK' : StageCodes s' next K) (hk1 : 1 ≤ s'.h + s'.g)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE)) (y : s.cMid.Word)
    (Tie : Ctx → SingleRows → Prop) (Tie' : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hTn : ∀ (c c' : Ctx) (row : GroupRow) (L : GroupLayout) (o : Nat), Blk.SameButNotes c c' →
      Tie' c row L o → Tie' c' row L o)
    (hOk : ∀ (c : Ctx) (rows : SingleRows), Tie c rows →
      FoldedOk s s' K next.code next.maskCode rows)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hone : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next later)) = some lay → lay.shapes.size = 1)
    (hread : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → Tie c rows →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next later) c c' sw row' L' theta D →
      ∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
        symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α)
    (hTie' : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → Tie c rows →
      c.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next later) c c' sw row' L' theta D →
      Tie' c' row' L' (c.st.oracles.size + 1)) :
    CsRuns true next later
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie)
      (GroupAt V K (roots + 1) s' (csNextW hf dS dC q y τC) rest Tie') := by
  refine csRuns_of V K roots s true next later dS dC τC rest q Tie _ hTie ?_ ?_
  · intro a c c' row L m hn hJ
    obtain ⟨o, ho, ht⟩ := hJ.mask
    exact ⟨hJ.run.notes hn, hJ.claim, hJ.plain, o, ho, hTn c c' row L o hn ht⟩
  · intro c c' rows gp sw row' L' theta D mask hrun hq ht hg hran hrun' hmask
    rw [hK'.k, hK'.h] at hran
    have hG := csRan_group hran hg
    have ok := hOk c rows ht
    have hcl := csRan_claim hf dS dC hr τC rest hran hrun.pending
      (by rw [hrun.codes]; exact ok.prog) ok.kept hG ok.d0 ok.d1 ok.vars
      (by rw [hrun.codes]; exact hbits) y (hread c c' rows gp sw row' L' theta D hrun ht hran)
    have hlay := hran.lay_eq (by rw [hG]) (by rw [hG])
    have hk : L'.k = s'.h + s'.g := by
      rw [hlay]
      show max (max (s'.h + s'.g) s'.h) 1 = s'.h + s'.g
      omega
    have hh : L'.h = s'.h := by rw [hlay]
    have h1 : D.lay.shapes.size = 1 := hone D.lay (by rw [← hrun.codes]; exact hran.trees)
    rw [h1] at hrun'
    refine ⟨hrun', ?_,
      hran.plain ok.kept ok.prog.masks ok.prog.noKept (by rw [hG]) (by rw [hG]) ok.plain,
      c.st.oracles.size + 1, ?_, hTie' c c' rows gp sw row' L' theta D hrun ht hg hran⟩
    · rw [stmG_eq, ← hk, ← hh, hcl, hq]
    · rcases hmask with ⟨_, hm, _⟩ | ⟨hf', _⟩
      · exact csRan_mask hran mask hm
      · cases hf'

end OnBytes.Slice

#print axioms OnBytes.Slice.stageOthers_size
#print axioms OnBytes.Slice.csRan_mask
#print axioms OnBytes.Slice.csRan_group
#print axioms OnBytes.Slice.csRuns_group
