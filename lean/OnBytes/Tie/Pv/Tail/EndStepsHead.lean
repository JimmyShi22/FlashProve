-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndStepsHead.lean: the routines of the head's sub-proof keep every relation that
holds across each basic step (`Steps`, OnBytes/Tie/Pv/Tail/EndSteps.lean).

Theorems with their proofs, each by a walk through a routine's text. The statements and proofs are
those of OnBytes/Tie/Pv/Tail/EndWalkHead.lean, with the class replaced.

Main names: `stp_` and a routine's name.

Limits: those of OnBytes/Tie/Pv/Tail/EndSteps.lean. `Head.hear` sets the number of slots and is not
here.


-/
import OnBytes.Model.Head
import OnBytes.Tie.Pv.Tail.EndStepsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.StepsW
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-! ## OnBytes/Model/HeadHeard.lean -/

open OnBytes.Model.Head in
/-- `Head.noteH` keeps R. -/
instance stp_Model_Head_noteH [Steps R] (what : String) (value : E) :
    Stp R (OnBytes.Model.Head.noteH what value) := by
  unfold OnBytes.Model.Head.noteH
  stp

open OnBytes.Model.Head in
/-- `Head.replyToken` keeps R. -/
instance stp_Model_Head_replyToken [Steps R] (plain : Array E) (V : Nat) :
    Stp R (OnBytes.Model.Head.replyToken plain V) := by
  unfold OnBytes.Model.Head.replyToken
  stp

open OnBytes.Model.Head in
/-- `Head.mergedPoint` keeps R. -/
instance stp_Model_Head_mergedPoint [Steps R] (h : Shape) (g1 : Forest.Heard) :
    Stp R (OnBytes.Model.Head.mergedPoint h g1) := by
  unfold OnBytes.Model.Head.mergedPoint
  stp

open OnBytes.Model.Head in
/-- `Head.hearSquares` keeps R. -/
instance stp_Model_Head_hearSquares [Steps R] (h : Shape) (PV : Array E) :
    Stp R (OnBytes.Model.Head.hearSquares h PV) := by
  unfold OnBytes.Model.Head.hearSquares
  stp

open OnBytes.Model.Head in
/-- `Head.shownRun` keeps R. -/
instance stp_Model_Head_shownRun [Steps R] (first n : Nat) :
    Stp R (OnBytes.Model.Head.shownRun first n) := by
  unfold OnBytes.Model.Head.shownRun
  stp

open OnBytes.Model.Head in
/-- `Head.hearProducts` keeps R. -/
instance stp_Model_Head_hearProducts [Steps R] (h : Shape) (PV : Array E) :
    Stp R (OnBytes.Model.Head.hearProducts h PV) := by
  unfold OnBytes.Model.Head.hearProducts
  stp

open OnBytes.Model.Head in
/-- `Head.hearStream` keeps R. -/
instance stp_Model_Head_hearStream [Steps R] (h : Shape) (zt : Array E) :
    Stp R (OnBytes.Model.Head.hearStream h zt) := by
  unfold OnBytes.Model.Head.hearStream
  stp

open OnBytes.Model.Head in
/-- `Head.channelRounds` keeps R. -/
instance stp_Model_Head_channelRounds [Steps R] :
    ∀ (n : Nat) (r : Array E) (p : Psc), Stp R (OnBytes.Model.Head.channelRounds n r p)
  | 0, r, p => by
    unfold OnBytes.Model.Head.channelRounds
    stp
  | n + 1, r, p => by
    have := stp_Model_Head_channelRounds n
    unfold OnBytes.Model.Head.channelRounds
    stp

open OnBytes.Model.Head in
/-- `Head.hearLogits` keeps R. -/
instance stp_Model_Head_hearLogits [Steps R] (h : Shape) (lam : Nat) (zt : Array E) :
    Stp R (OnBytes.Model.Head.hearLogits h lam zt) := by
  unfold OnBytes.Model.Head.hearLogits
  stp

/-! ## OnBytes/Model/HeadTables.lean -/

open OnBytes.Model.Head in
/-- `Head.tablesOf` keeps R. -/
instance stp_Model_Head_tablesOf [Steps R] (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered)
    (x : Heard) :
    Stp R (OnBytes.Model.Head.tablesOf h L hp cov x) := by
  unfold OnBytes.Model.Head.tablesOf
  stp

open OnBytes.Model.Head in
/-- `Head.tabAt` keeps R. -/
instance stp_Model_Head_tabAt [Steps R] (Rn : OnBytes.Model.Head.Run) (n : String) :
    Stp R (OnBytes.Model.Head.tabAt Rn n) := by
  unfold OnBytes.Model.Head.tabAt
  stp

open OnBytes.Model.Head in
/-- `Head.U3at` keeps R. -/
instance stp_Model_Head_U3at [Steps R] (Rn : OnBytes.Model.Head.Run) (t i : Nat) :
    Stp R (OnBytes.Model.Head.U3at Rn t i) := by
  unfold OnBytes.Model.Head.U3at
  stp

/-! ## OnBytes/Model/HeadForms.lean -/

open OnBytes.Model.Head in
/-- `Head.segOf` keeps R. -/
instance stp_Model_Head_segOf [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Stp R (OnBytes.Model.Head.segOf Rn sn) := by
  unfold OnBytes.Model.Head.segOf
  stp

open OnBytes.Model.Head in
/-- `Head.ewOf` keeps R. -/
instance stp_Model_Head_ewOf [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Stp R (OnBytes.Model.Head.ewOf Rn sn) := by
  unfold OnBytes.Model.Head.ewOf
  stp

open OnBytes.Model.Head in
/-- `Head.ewh` keeps R. -/
instance stp_Model_Head_ewh [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Stp R (OnBytes.Model.Head.ewh Rn sn) := by
  unfold OnBytes.Model.Head.ewh
  stp

open OnBytes.Model.Head in
/-- `Head.Sl` keeps R. -/
instance stp_Model_Head_Sl [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) (OFF nl J : Nat) :
    Stp R (OnBytes.Model.Head.Sl Rn sn OFF nl J) := by
  unfold OnBytes.Model.Head.Sl
  stp

open OnBytes.Model.Head in
/-- `Head.xbA` keeps R. -/
instance stp_Model_Head_xbA [Steps R] (Rn : OnBytes.Model.Head.Run) (t kh : Nat) :
    Stp R (OnBytes.Model.Head.xbA Rn t kh) := by
  unfold OnBytes.Model.Head.xbA
  stp

open OnBytes.Model.Head in
/-- `Head.sh2` keeps R. -/
instance stp_Model_Head_sh2 [Steps R] (Rn : OnBytes.Model.Head.Run) (t j : Nat) :
    Stp R (OnBytes.Model.Head.sh2 Rn t j) := by
  unfold OnBytes.Model.Head.sh2
  stp

open OnBytes.Model.Head in
/-- `Head.rowAt` keeps R. -/
instance stp_Model_Head_rowAt [Steps R] (Rn : OnBytes.Model.Head.Run) (P : String) :
    Stp R (OnBytes.Model.Head.rowAt Rn P) := by
  unfold OnBytes.Model.Head.rowAt
  stp

open OnBytes.Model.Head in
/-- `Head.row5At` keeps R. -/
instance stp_Model_Head_row5At [Steps R] (Rn : OnBytes.Model.Head.Run) (P : String) :
    Stp R (OnBytes.Model.Head.row5At Rn P) := by
  unfold OnBytes.Model.Head.row5At
  stp

open OnBytes.Model.Head in
/-- `Head.gapAt` keeps R. -/
instance stp_Model_Head_gapAt [Steps R] (Rn : OnBytes.Model.Head.Run) (P : String) (i : Nat)
    (wsum : E) :
    Stp R (OnBytes.Model.Head.gapAt Rn P i wsum) := by
  unfold OnBytes.Model.Head.gapAt
  stp

open OnBytes.Model.Head in
/-- `Head.ztSeg` keeps R. -/
instance stp_Model_Head_ztSeg [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Stp R (OnBytes.Model.Head.ztSeg Rn sn) := by
  unfold OnBytes.Model.Head.ztSeg
  stp

open OnBytes.Model.Head in
/-- `Head.middleDigit` keeps R. -/
instance stp_Model_Head_middleDigit [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E) :
    Stp R (OnBytes.Model.Head.middleDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.middleDigit
  stp

open OnBytes.Model.Head in
/-- `Head.lowDigit` keeps R. -/
instance stp_Model_Head_lowDigit [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E) :
    Stp R (OnBytes.Model.Head.lowDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.lowDigit
  stp

open OnBytes.Model.Head in
/-- `Head.LINE` keeps R. -/
instance stp_Model_Head_LINE [Steps R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Stp R (OnBytes.Model.Head.LINE Rn sn) := by
  unfold OnBytes.Model.Head.LINE
  stp

open OnBytes.Model.Head in
/-- `Head.keyForm` keeps R. -/
instance stp_Model_Head_keyForm [Steps R] (Rn : OnBytes.Model.Head.Run) (q : Nat)
    (laid : Array Nat) :
    Stp R (OnBytes.Model.Head.keyForm Rn q laid) := by
  unfold OnBytes.Model.Head.keyForm
  stp

/-! ## OnBytes/Model/Head.lean -/

open OnBytes.Model.Head in
/-- `Head.weightsClaim` keeps R. -/
instance stp_Model_Head_weightsClaim [Steps R] (Rn : OnBytes.Model.Head.Run) (wsLay : WsLay) :
    Stp R (OnBytes.Model.Head.weightsClaim Rn wsLay) := by
  unfold OnBytes.Model.Head.weightsClaim
  stp

open OnBytes.Model.Head in
/-- `Head.claimSquares` keeps R. -/
instance stp_Model_Head_claimSquares [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimSquares Rn) := by
  unfold OnBytes.Model.Head.claimSquares
  stp

open OnBytes.Model.Head in
/-- `Head.claimLedger5` keeps R. -/
instance stp_Model_Head_claimLedger5 [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimLedger5 Rn) := by
  unfold OnBytes.Model.Head.claimLedger5
  stp

open OnBytes.Model.Head in
/-- `Head.claimLedger4` keeps R. -/
instance stp_Model_Head_claimLedger4 [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimLedger4 Rn) := by
  unfold OnBytes.Model.Head.claimLedger4
  stp

open OnBytes.Model.Head in
/-- `Head.claimLedger` keeps R. -/
instance stp_Model_Head_claimLedger [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimLedger Rn) := by
  unfold OnBytes.Model.Head.claimLedger
  stp

open OnBytes.Model.Head in
/-- `Head.claimStream` keeps R. -/
instance stp_Model_Head_claimStream [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimStream Rn) := by
  unfold OnBytes.Model.Head.claimStream
  stp

open OnBytes.Model.Head in
/-- `Head.claimJoin` keeps R. -/
instance stp_Model_Head_claimJoin [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimJoin Rn) := by
  unfold OnBytes.Model.Head.claimJoin
  stp

open OnBytes.Model.Head in
/-- `Head.claimPolicy` keeps R. -/
instance stp_Model_Head_claimPolicy [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimPolicy Rn) := by
  unfold OnBytes.Model.Head.claimPolicy
  stp

open OnBytes.Model.Head in
/-- `Head.claimPlanes` keeps R. -/
instance stp_Model_Head_claimPlanes [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimPlanes Rn) := by
  unfold OnBytes.Model.Head.claimPlanes
  stp

open OnBytes.Model.Head in
/-- `Head.claimLogits` keeps R. -/
instance stp_Model_Head_claimLogits [Steps R] (Rn : OnBytes.Model.Head.Run) :
    Stp R (OnBytes.Model.Head.claimLogits Rn) := by
  unfold OnBytes.Model.Head.claimLogits
  stp

open OnBytes.Model.Head in
/-- `Head.noteConstant` keeps R. -/
instance stp_Model_Head_noteConstant [Steps R] (group : String) :
    Stp R (OnBytes.Model.Head.noteConstant group) := by
  unfold OnBytes.Model.Head.noteConstant
  stp

end OnBytes.Tie.Pv.Tail.StepsW

#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_Model_Head_claimJoin
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_Model_Head_weightsClaim
