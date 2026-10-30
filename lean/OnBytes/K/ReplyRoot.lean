-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyRoot.lean: the token that the prover names for the reply is the caller's reply, at
the very state from which the head's routine was called. For proofs only; the program does
not import this file.

OnBytes/TieK/HeadRoot.lean lays the road from what the exit code 0 says of the proof file to the run
of the head's routine as a record of values D, each of which stands with the equation or the run
that gives it from the one before (`Root F further D`). Among them: the state D.chk of the chain's
calls with which the head's routine was called, and the reply D.res.reply that the links' block
returned, which is the first plain scalar of D.chk.
  `root_reply_own`: under `Root F further D`: the first plain scalar of D.chk is
    `Model.ofNat D.so.y`, the caller's reply; so the number that `Head.replyToken` makes of D.chk's
    plain scalars is D.so.y; and `Head.winOf` at that number, at the window at which the statement's
    positions were made, returns the field `hWin` of these positions.
  `root_win`: the head's routine has passed its first test, so its own window is the one at which
    the statement's positions were made; so from whatever states `Head.hear` returns on D.chk's
    plain scalars, the field `win` of what it returns is the field `hWin`. That there are
    such states: OnBytes/K/HeadSplitRoot.lean [not in this library].
With `covered_of` (OnBytes/K/TokensCovered.lean) that list, at the positions r to e - 1, is
`outputOf`. No hypothesis of the kind "keeps" is left: the two of OnBytes/K/ReplyRun.lean are met by
OnBytes/K/ReplyKeeps.lean.
Where e is the window's size, the token at the last covered position is the caller's reply. Where e
is below it, the reply must be 0 and stands at no covered position: there the sentence on the reply
says only that the prover's plain scalar is the field's 0.
What is not claimed: that the routine has called `hear` on these scalars and has gone on at what it
returned: OnBytes/K/HeadSplitRoot.lean [not in this library] has that. What the routine does with that list. `head_root`
gives some D, not the only one.


-/
import OnBytes.K.ReplyKeeps
import OnBytes.K.ReplyMore
import OnBytes.K.HeadSplit
import OnBytes.TieK.HeadRoot

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model
open OnBytes.Cut (mapL)

/-- At the state from which the head's routine was called. In words: the head of this file. -/
theorem root_reply_own {F : Files} {further : Params.TableName} {D : TieK.RootData}
    (R : TieK.Root F further D) :
    D.chk.plain[0]? = some (Model.ofNat D.so.y) ∧ tokenOf D.chk.plain = D.so.y ∧
      Head.winOf D.cov D.p.X.T (tokenOf D.chk.plain) = D.cov.hWin := by
  have hrun : D.block D.start = .ok (D.real, D.cEnd) := (Blk.yields_iff _ _ _ _).1 R.ran.run
  have hl : D.linksBlock D.start = .ok (D.res, D.cL) := (Blk.yields_iff _ _ _ _).1 R.links_ran
  haveI hk : L5.Keeps D.linksBlock := by
    have h0 := L5.keeps_links R.made.links_made D.p.built.links D.first D.wsLay
    rw [R.made.list] at h0
    exact h0
  obtain ⟨r, c1, got, g1, _, g2, g3⟩ := firstBlock_reply (keepsDry_of D.linksBlock)
    (fun r => keepsFailed_of (firstTail D.first r)) hrun rfl R.ran.clean
  have e : (r, c1) = (D.res, D.cL) := Except.ok.inj (g1.symm.trans hl)
  have e1 : r = D.res := congrArg Prod.fst e
  have h0 : D.chk.plain[0]? = some got := by
    rw [← R.reply_is, ← e1]
    exact g2
  have eg : got = Model.ofNat D.so.y := by simpa using g3
  have hs := reply_small R.made.own
  exact ⟨by rw [h0, eg], token_of_reply h0 g3 hs, win_of_reply R.made.covered h0 g3 hs⟩

/-- Under `Root F further D`: the head's routine's own window is the one at which the statement's
positions were made; `winOf` at that window and at the number made of D.chk's plain scalars is the
field `hWin`; so from whatever states `hear` returns on these scalars, the field `win` of what it
returns is `hWin`. -/
theorem root_win {F : Files} {further : Params.TableName} {D : TieK.RootData}
    (R : TieK.Root F further D) :
    D.p.X.hS.T = D.p.X.T ∧
      Head.winOf D.cov D.p.X.hS.T (tokenOf D.chk.plain) = D.cov.hWin ∧
      ∀ F1 c1 x F2 c2, Head.hear D.p.X.hS D.p.X.HLy D.p.X.H D.cov D.chk.plain F1 c1 =
          .ok ((x, F2), c2) → x.win = D.cov.hWin := by
  have hrun := (Blk.yields_iff _ _ _ _).1 R.head_at.run
  rw [R.made.routine] at hrun
  obtain ⟨_, _, _, _, hv, _⟩ := mapL (g := some) (x := Head.runForkHidH2 D.p.X.hS D.p.X.HLy
    (Verify.borderOf D.p.X.y) D.p.X.H D.p.X.owner D.cov D.p.X.layers.wsLay) hrun
  have eT : D.p.X.hS.T = D.p.X.T := sized_same R.made.covered (head_split hv).1
  have eW : Head.winOf D.cov D.p.X.hS.T (tokenOf D.chk.plain) = D.cov.hWin := by
    rw [eT]
    exact (root_reply_own R).2.2
  exact ⟨eT, eW, fun _ _ _ _ _ hq' => (hear_win hq').trans eW⟩

end OnBytes.K
