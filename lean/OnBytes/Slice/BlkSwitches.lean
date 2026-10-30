-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSwitches.lean: the two code switches of the program's run on a link's chain lead
from joint to joint, with the ties written out.

OnBytes/Slice/BlkJointCsAt.lean and BlkJointCsLast.lean prove the statement of
OnBytes/Slice/BlkChain.lean on a code switch for ties that are variables, under hypotheses on these
variables. This file takes the ties of OnBytes/Slice/BlkTies.lean and meets these
hypotheses: the reading of the old rows (OnBytes/Slice/BlkCsReadAt.lean) and the tie before the next
fold (OnBytes/Slice/BlkCsTie.lean). What is left to ask is public, but for `hshow` (see below).

Main definition.
 `OneTree`   how the oracle messages of one prover's message are placed: all in one tree, in their
             order.
Main theorems.
 `csRuns_first`    the switch after the fold of the link's group, which has two members.
 `csRuns_second`   the switch into the last stage, after the fold of a group with one member.

Not claimed. The public facts on sizes, codes and widths that are hypotheses here. That the view
shows the written tree's columns under the tree's number (`hshow`).
-/
import OnBytes.Slice.BlkCsReadAt
import OnBytes.Slice.BlkCsTie
import OnBytes.Slice.BlkJointCsLast

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-- The oracle messages sent are placed in one tree, in their order, under the codes K: a tree of
2^logN leaves whose column has each message's symbols in turn. This is said of what the program's
`layTrees` returns: where it returns nothing, the statement is true and empty. -/
def OneTree (K : Codes) (sent : Array OracleNotice) (logN : Nat) : Prop :=
  ∀ lay, layTrees K sent = some lay → ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = logN ∧
    (∀ i, i < sent.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
    sh.mainSymbols = ((sent.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray ∧
    sh.maskSymbols = ((sent.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray

/-- The switch after the fold of the link's group leads from joint to joint, under the hypotheses
that the statement lists. The group has two members of equal shape sh and no mask rows; fr: the
fresh mask's shape; f1: the first row of the second member's block. d, m: the written round that
sent their tree, and its message. n: the tree's number. -/
theorem csRuns_first (V : Fmt.View) (K : Codes) (roots : Nat) (S : Sz) {s s' : Sg}
    (hf : CsFit s s') (hs0 : s.h = 0) (next n3 : IoppStage) (later : List IoppStage)
    (hK' : StageCodes s' next K) (hk1 : 1 ≤ s'.h + s'.g) (dS dC : PQ.RD)
    (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView)
    (q : GE × (s.cMid.J → GE)) (n : Nat) (sh fr : OracleShape) (pt : Fin (s.h + s.g) → GE)
    (d : PQ.RD) (m : (wRound d).Msg) (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hone : OneTree K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
      #[foldMaskNotice (ioppFoldShape next {})]) s'.C.a) :
    CsRuns true next (n3 :: later)
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest)
        (SingleTie s s' K next.code next.maskCode n [sh, sh, fr] #[some 0, some f1] #[none, none]
          pt))
      (GroupAt V K (roots + 1) s' (csNextW hf dS dC q (wordMid s (col1 S d m.1) pt) τC) rest
        (GroupTie s' roots [(switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape,
          (foldMaskNotice (ioppFoldShape next {})).shape] #[some 0] #[some 0])) := by
  refine csRuns_group V K roots hf next (n3 :: later) hK' hk1 dS dC hr τC rest q _ _ _
    (fun c c' rows _ hb ho _ ht => ht.congr hb ho) (fun c c' row L o hn ht => ht.notes hn)
    (fun c rows ht => ht.ok) hbits ?_ ?_ ?_
  · intro lay hlay
    obtain ⟨shT, l1, _⟩ := hone lay hlay
    rw [l1]
    rfl
  · intro c c' rows gp sw row' L' theta D hrun ht hran
    exact hread_group V K roots S hs0 dS dC hr τC rest _ _ n sh fr pt d m hshow hW mem hmems hE
      hm0 f1 hst hf1 hk hR h3 hz hfm hfz _ _ c c' rows gp sw row' L' theta D hrun ht hran
  · intro c c' rows gp sw row' L' theta D hrun ht hg hran
    obtain ⟨shT, l1, l2, l3, l4, l5⟩ := hone D.lay (by rw [← hrun.codes]; exact hran.trees)
    exact CsRan.groupTie s' (foldMaskNotice (ioppFoldShape next {})) hran (csRan_group hran hg) shT
      l1 l3 l4 l5 l2 roots (by rw [hrun.onView.first, hrun.roots, Nat.zero_add])

/-- The switch into the last stage, after the fold of a group with one member of the shape sh,
leads from joint to joint, under the hypotheses that the statement lists. sh': the fresh mask's
shape. d, m: the written round that sent their tree, and its message. n: the tree's number. -/
theorem csRuns_second (V : Fmt.View) (K : Codes) (roots : Nat) {s s' : Sg} (hf : CsFit s s')
    (next : IoppStage) (hK' : StageCodes s' next K) (h0 : s'.h = 0) (g0 : s'.g = 0)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE)) (n : Nat) (sh sh' : OracleShape)
    (pt : Fin (s.h + s.g) → GE) (d : PQ.RD) (m : (wRound d).Msg)
    (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hlay : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next [])) = some lay →
      ∃ shT : TreeShape, lay.shapes = #[shT] ∧ shT.logN = s'.C.a ∧
        (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
        shT.mainSymbols = #[3, 3] ∧ shT.maskSymbols = #[3, 3]) :
    CsRuns true next []
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest)
        (SingleTie s s' K next.code next.maskCode n [sh, sh'] #[some 0] #[some 0] pt))
      (LastAt V K (roots + 1) s' next (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC) rest
        roots) :=
  csRuns_last V K roots hf next hK' h0 g0 dS dC hr τC rest q _ _
    (fun _ _ _ _ hb ho _ ht => ht.congr hb ho) (fun _ _ ht => ht.ok) hbits hlay
    (fun c c' rows gp sw row' L' theta D hrun ht hran =>
      hread_stage V K roots dS dC hr τC rest _ _ n sh sh' pt d m hshow hW m1 m2 m3 f1 f3 _ _ c c'
        rows gp sw row' L' theta D hrun ht hran)

end OnBytes.Slice

#print axioms OnBytes.Slice.csRuns_first
#print axioms OnBytes.Slice.csRuns_second
