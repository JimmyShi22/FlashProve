-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyBlkSwitch.lean: a code switch between two stages in the middle of the program's
run on a link's chain leads from joint to joint, with the ties written out.

OnBytes/Slice/BlkSwitches.lean has the switch after the fold of the link's group and the switch
into the last stage. A chain of more than three stages has a third kind: the switch after the fold
of a group with one member, into a stage that is folded again. Its old side is that of
`csRuns_second`, its new side that of `csRuns_first`.

Main theorem.
 `csRuns_middle`   the switch after the fold of a group with one member, into a stage that is not
                   the last.

Not claimed. The public facts on sizes, codes and widths that are hypotheses here. That the view
shows the written tree's columns under the tree's number (`hshow`).

-/
import OnBytes.Slice.BlkSwitches

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-- The switch after the fold of a group with one member of the shape sh, into a stage after which
more stages come, leads from joint to joint, under the hypotheses that the statement lists. sh': the
fresh mask's shape. d, m: the written round that sent their tree, and its message. n: the tree's
number. -/
theorem csRuns_middle (V : Fmt.View) (K : Codes) (roots : Nat) {s s' : Sg} (hf : CsFit s s')
    (next n3 : IoppStage) (later : List IoppStage) (hK' : StageCodes s' next K)
    (hk1 : 1 ≤ s'.h + s'.g) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (n : Nat) (sh sh' : OracleShape) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD)
    (m : (wRound d).Msg) (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hone : OneTree K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
      #[foldMaskNotice (ioppFoldShape next {})]) s'.C.a) :
    CsRuns true next (n3 :: later)
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest)
        (SingleTie s s' K next.code next.maskCode n [sh, sh'] #[some 0] #[some 0] pt))
      (GroupAt V K (roots + 1) s' (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC) rest
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
    exact hread_stage V K roots dS dC hr τC rest _ _ n sh sh' pt d m hshow hW m1 m2 m3 f1 f3 _ _ c
      c' rows gp sw row' L' theta D hrun ht hran
  · intro c c' rows gp sw row' L' theta D hrun ht hg hran
    obtain ⟨shT, l1, l2, l3, l4, l5⟩ := hone D.lay (by rw [← hrun.codes]; exact hran.trees)
    exact CsRan.groupTie s' (foldMaskNotice (ioppFoldShape next {})) hran (csRan_group hran hg) shT
      l1 l3 l4 l5 l2 roots (by rw [hrun.onView.first, hrun.roots, Nat.zero_add])

end OnBytes.Slice
