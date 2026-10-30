-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalkHead.lean: the routines of the head's sub-proof (OnBytes/Model/Head.lean
and the files that it imports), of the token sumcheck and of the merge (OnBytes/Model/Tsc.lean,
OnBytes/Model/Merge.lean) keep whatever the basic steps keep.

Theorems with their proofs, one for each routine, each by a walk through the routine's text (`walk`,
OnBytes/Tie/Pv/Tail/EndWalk.lean). R: any relation with `Prim R`. «x keeps R»: wherever the routine
x returns, R holds from the state before to the state after (`Pres R x`, `PresL R x`).

Main names: `pres_` and the routine's name; `pres_range`, `pres_map`, `pres_mapMArr`: a loop over a
range of numbers, a function applied to what a routine returns, a routine for each member of an
array with the values gathered; `walk2`: the walk with these three.

Limits: those of OnBytes/Tie/Pv/Tail/EndWalk.lean.


-/
import OnBytes.Model.Head
import OnBytes.Tie.Pv.Tail.EndWalkTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-! ## Three more laws, and the walk with them -/

/-- A loop over a range of numbers. -/
theorem pres_range [Prim R] {β : Type} (f : Nat → β → SubM (ForInStep β))
    (hf : ∀ a b, Pres R (f a b)) (r : Std.Legacy.Range) (b : β) : Pres R (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact pres_loop f hf _ b

/-- A function applied to what a routine returns. -/
theorem pres_map [Prim R] {α β : Type} (g : α → β) {x : SubM α} (hx : Pres R x) :
    Pres R (g <$> x) := by
  rw [map_eq_pure_bind]
  exact pres_bind hx fun _ => pres_pure _

/-- A routine for each member of an array, with the values gathered. -/
theorem pres_mapMArr [Prim R] {α β : Type} (f : α → SubM β) (hf : ∀ a, Pres R (f a))
    (as : Array α) : Pres R (as.mapM f) := by
  rw [Array.mapM_eq_foldlM]
  exact pres_foldlMArr _ (fun _ a => pres_map _ (hf a)) as _

/-- One step of a walk through a routine's text, with the laws above. -/
macro "walk2_step" : tactic => `(tactic| first
  | walk_step | refine pres_range _ ?_ _ _ | refine pres_map _ ?_ | refine pres_mapMArr _ ?_ _)

/-- A walk through a routine's text, with the laws above. -/
macro "walk2" : tactic => `(tactic| repeat' walk2_step)

/-! ## OnBytes/Model/Tsc.lean -/

open OnBytes.Model in
/-- `tscLoop` keeps R. -/
instance pres_Model_tscLoop [Prim R] :
    ∀ (zs : List E) (r : Array E) (p : Psc), Pres R (OnBytes.Model.tscLoop zs r p)
  | [], r, p => by
    unfold OnBytes.Model.tscLoop
    walk2
  | z :: zs, r, p => by
    have := pres_Model_tscLoop zs
    unfold OnBytes.Model.tscLoop
    walk2

open OnBytes.Model in
/-- `tscRounds` keeps R. -/
instance pres_Model_tscRounds [Prim R] (P : Array E) (lt : Nat) :
    Pres R (OnBytes.Model.tscRounds P lt) := by
  unfold OnBytes.Model.tscRounds
  walk2

open OnBytes.Model in
/-- `tscIn` keeps R. -/
instance pres_Model_tscIn [Prim R] (P : Array E) (lt shown degreeInY : Nat) :
    Pres R (OnBytes.Model.tscIn P lt shown degreeInY) := by
  unfold OnBytes.Model.tscIn
  walk2

/-! ## OnBytes/Model/Merge.lean -/

open OnBytes.Model in
/-- `wsForkRounds` keeps R. -/
instance pres_Model_wsForkRounds [Prim R] :
    ∀ (n : Nat) (rm : Array E) (p : Psc), Pres R (OnBytes.Model.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold OnBytes.Model.wsForkRounds
    walk2
  | n + 1, rm, p => by
    have := pres_Model_wsForkRounds n
    unfold OnBytes.Model.wsForkRounds
    walk2

open OnBytes.Model in
/-- `wsForkMerge` keeps R. -/
instance pres_Model_wsForkMerge [Prim R] (lk : Nat) (sv : Array Nat) :
    Pres R (OnBytes.Model.wsForkMerge lk sv) := by
  unfold OnBytes.Model.wsForkMerge
  walk2

open OnBytes.Model in
/-- `wsForkLin` keeps R. -/
instance pres_Model_wsForkLin [Prim R] (o : WsMerged) :
    Pres R (OnBytes.Model.wsForkLin o) := by
  unfold OnBytes.Model.wsForkLin
  walk2

open OnBytes.Model in
/-- `wsForkEnd` keeps R. -/
instance pres_Model_wsForkEnd [Prim R] (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Pres R (OnBytes.Model.wsForkEnd lay cl sv) := by
  unfold OnBytes.Model.wsForkEnd
  walk2

/-! ## OnBytes/Model/HeadHeard.lean -/

open OnBytes.Model.Head in
/-- `Head.noteH` keeps R. -/
instance pres_Model_Head_noteH [Prim R] (what : String) (value : E) :
    Pres R (OnBytes.Model.Head.noteH what value) := by
  unfold OnBytes.Model.Head.noteH
  walk2

open OnBytes.Model.Head in
/-- `Head.replyToken` keeps R. -/
instance pres_Model_Head_replyToken [Prim R] (plain : Array E) (V : Nat) :
    Pres R (OnBytes.Model.Head.replyToken plain V) := by
  unfold OnBytes.Model.Head.replyToken
  walk2

open OnBytes.Model.Head in
/-- `Head.mergedPoint` keeps R. -/
instance pres_Model_Head_mergedPoint [Prim R] (h : Shape) (g1 : Forest.Heard) :
    Pres R (OnBytes.Model.Head.mergedPoint h g1) := by
  unfold OnBytes.Model.Head.mergedPoint
  walk2

open OnBytes.Model.Head in
/-- `Head.hearSquares` keeps R. -/
instance pres_Model_Head_hearSquares [Prim R] (h : Shape) (PV : Array E) :
    Pres R (OnBytes.Model.Head.hearSquares h PV) := by
  unfold OnBytes.Model.Head.hearSquares
  walk2

open OnBytes.Model.Head in
/-- `Head.shownRun` keeps R. -/
instance pres_Model_Head_shownRun [Prim R] (first n : Nat) :
    Pres R (OnBytes.Model.Head.shownRun first n) := by
  unfold OnBytes.Model.Head.shownRun
  walk2

open OnBytes.Model.Head in
/-- `Head.hearProducts` keeps R. -/
instance pres_Model_Head_hearProducts [Prim R] (h : Shape) (PV : Array E) :
    Pres R (OnBytes.Model.Head.hearProducts h PV) := by
  unfold OnBytes.Model.Head.hearProducts
  walk2

open OnBytes.Model.Head in
/-- `Head.hearStream` keeps R. -/
instance pres_Model_Head_hearStream [Prim R] (h : Shape) (zt : Array E) :
    Pres R (OnBytes.Model.Head.hearStream h zt) := by
  unfold OnBytes.Model.Head.hearStream
  walk2

open OnBytes.Model.Head in
/-- `Head.channelRounds` keeps R. -/
instance pres_Model_Head_channelRounds [Prim R] :
    ∀ (n : Nat) (r : Array E) (p : Psc), Pres R (OnBytes.Model.Head.channelRounds n r p)
  | 0, r, p => by
    unfold OnBytes.Model.Head.channelRounds
    walk2
  | n + 1, r, p => by
    have := pres_Model_Head_channelRounds n
    unfold OnBytes.Model.Head.channelRounds
    walk2

open OnBytes.Model.Head in
/-- `Head.hearLogits` keeps R. -/
instance pres_Model_Head_hearLogits [Prim R] (h : Shape) (lam : Nat) (zt : Array E) :
    Pres R (OnBytes.Model.Head.hearLogits h lam zt) := by
  unfold OnBytes.Model.Head.hearLogits
  walk2

open OnBytes.Model.Head in
/-- `Head.hear` keeps R. -/
instance pres_Model_Head_hear [PrimS R] (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered)
    (plain : Array E) :
    Pres R (OnBytes.Model.Head.hear h L hp cov plain) := by
  unfold OnBytes.Model.Head.hear
  walk2

/-! ## OnBytes/Model/HeadTables.lean -/

open OnBytes.Model.Head in
/-- `Head.tablesOf` keeps R. -/
instance pres_Model_Head_tablesOf [Prim R] (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered)
    (x : Heard) :
    Pres R (OnBytes.Model.Head.tablesOf h L hp cov x) := by
  unfold OnBytes.Model.Head.tablesOf
  walk2

open OnBytes.Model.Head in
/-- `Head.tabAt` keeps R. -/
instance pres_Model_Head_tabAt [Prim R] (Rn : OnBytes.Model.Head.Run) (n : String) :
    Pres R (OnBytes.Model.Head.tabAt Rn n) := by
  unfold OnBytes.Model.Head.tabAt
  walk2

open OnBytes.Model.Head in
/-- `Head.U3at` keeps R. -/
instance pres_Model_Head_U3at [Prim R] (Rn : OnBytes.Model.Head.Run) (t i : Nat) :
    Pres R (OnBytes.Model.Head.U3at Rn t i) := by
  unfold OnBytes.Model.Head.U3at
  walk2

/-! ## OnBytes/Model/HeadForms.lean -/

open OnBytes.Model.Head in
/-- `Head.segOf` keeps R. -/
instance pres_Model_Head_segOf [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Pres R (OnBytes.Model.Head.segOf Rn sn) := by
  unfold OnBytes.Model.Head.segOf
  walk2

open OnBytes.Model.Head in
/-- `Head.ewOf` keeps R. -/
instance pres_Model_Head_ewOf [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Pres R (OnBytes.Model.Head.ewOf Rn sn) := by
  unfold OnBytes.Model.Head.ewOf
  walk2

open OnBytes.Model.Head in
/-- `Head.ewh` keeps R. -/
instance pres_Model_Head_ewh [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Pres R (OnBytes.Model.Head.ewh Rn sn) := by
  unfold OnBytes.Model.Head.ewh
  walk2

open OnBytes.Model.Head in
/-- `Head.Sl` keeps R. -/
instance pres_Model_Head_Sl [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) (OFF nl J : Nat) :
    Pres R (OnBytes.Model.Head.Sl Rn sn OFF nl J) := by
  unfold OnBytes.Model.Head.Sl
  walk2

open OnBytes.Model.Head in
/-- `Head.xbA` keeps R. -/
instance pres_Model_Head_xbA [Prim R] (Rn : OnBytes.Model.Head.Run) (t kh : Nat) :
    Pres R (OnBytes.Model.Head.xbA Rn t kh) := by
  unfold OnBytes.Model.Head.xbA
  walk2

open OnBytes.Model.Head in
/-- `Head.sh2` keeps R. -/
instance pres_Model_Head_sh2 [Prim R] (Rn : OnBytes.Model.Head.Run) (t j : Nat) :
    Pres R (OnBytes.Model.Head.sh2 Rn t j) := by
  unfold OnBytes.Model.Head.sh2
  walk2

open OnBytes.Model.Head in
/-- `Head.rowAt` keeps R. -/
instance pres_Model_Head_rowAt [Prim R] (Rn : OnBytes.Model.Head.Run) (P : String) :
    Pres R (OnBytes.Model.Head.rowAt Rn P) := by
  unfold OnBytes.Model.Head.rowAt
  walk2

open OnBytes.Model.Head in
/-- `Head.row5At` keeps R. -/
instance pres_Model_Head_row5At [Prim R] (Rn : OnBytes.Model.Head.Run) (P : String) :
    Pres R (OnBytes.Model.Head.row5At Rn P) := by
  unfold OnBytes.Model.Head.row5At
  walk2

open OnBytes.Model.Head in
/-- `Head.gapAt` keeps R. -/
instance pres_Model_Head_gapAt [Prim R] (Rn : OnBytes.Model.Head.Run) (P : String) (i : Nat)
    (wsum : E) :
    Pres R (OnBytes.Model.Head.gapAt Rn P i wsum) := by
  unfold OnBytes.Model.Head.gapAt
  walk2

open OnBytes.Model.Head in
/-- `Head.ztSeg` keeps R. -/
instance pres_Model_Head_ztSeg [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Pres R (OnBytes.Model.Head.ztSeg Rn sn) := by
  unfold OnBytes.Model.Head.ztSeg
  walk2

open OnBytes.Model.Head in
/-- `Head.middleDigit` keeps R. -/
instance pres_Model_Head_middleDigit [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E) :
    Pres R (OnBytes.Model.Head.middleDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.middleDigit
  walk2

open OnBytes.Model.Head in
/-- `Head.lowDigit` keeps R. -/
instance pres_Model_Head_lowDigit [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E) :
    Pres R (OnBytes.Model.Head.lowDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.lowDigit
  walk2

open OnBytes.Model.Head in
/-- `Head.LINE` keeps R. -/
instance pres_Model_Head_LINE [Prim R] (Rn : OnBytes.Model.Head.Run) (sn : String) :
    Pres R (OnBytes.Model.Head.LINE Rn sn) := by
  unfold OnBytes.Model.Head.LINE
  walk2

open OnBytes.Model.Head in
/-- `Head.keyForm` keeps R. -/
instance pres_Model_Head_keyForm [Prim R] (Rn : OnBytes.Model.Head.Run) (q : Nat)
    (laid : Array Nat) :
    Pres R (OnBytes.Model.Head.keyForm Rn q laid) := by
  unfold OnBytes.Model.Head.keyForm
  walk2

/-! ## OnBytes/Model/Head.lean -/

open OnBytes.Model.Head in
/-- `Head.weightsClaim` keeps R. -/
instance pres_Model_Head_weightsClaim [Prim R] (Rn : OnBytes.Model.Head.Run) (wsLay : WsLay) :
    Pres R (OnBytes.Model.Head.weightsClaim Rn wsLay) := by
  unfold OnBytes.Model.Head.weightsClaim
  walk2

open OnBytes.Model.Head in
/-- `Head.claimSquares` keeps R. -/
instance pres_Model_Head_claimSquares [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimSquares Rn) := by
  unfold OnBytes.Model.Head.claimSquares
  walk2

open OnBytes.Model.Head in
/-- `Head.claimLedger5` keeps R. -/
instance pres_Model_Head_claimLedger5 [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimLedger5 Rn) := by
  unfold OnBytes.Model.Head.claimLedger5
  walk2

open OnBytes.Model.Head in
/-- `Head.claimLedger4` keeps R. -/
instance pres_Model_Head_claimLedger4 [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimLedger4 Rn) := by
  unfold OnBytes.Model.Head.claimLedger4
  walk2

open OnBytes.Model.Head in
/-- `Head.claimLedger` keeps R. -/
instance pres_Model_Head_claimLedger [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimLedger Rn) := by
  unfold OnBytes.Model.Head.claimLedger
  walk2

open OnBytes.Model.Head in
/-- `Head.claimStream` keeps R. -/
instance pres_Model_Head_claimStream [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimStream Rn) := by
  unfold OnBytes.Model.Head.claimStream
  walk2

open OnBytes.Model.Head in
/-- `Head.claimJoin` keeps R. -/
instance pres_Model_Head_claimJoin [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimJoin Rn) := by
  unfold OnBytes.Model.Head.claimJoin
  walk2

open OnBytes.Model.Head in
/-- `Head.claimPolicy` keeps R. -/
instance pres_Model_Head_claimPolicy [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimPolicy Rn) := by
  unfold OnBytes.Model.Head.claimPolicy
  walk2

open OnBytes.Model.Head in
/-- `Head.claimPlanes` keeps R. -/
instance pres_Model_Head_claimPlanes [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimPlanes Rn) := by
  unfold OnBytes.Model.Head.claimPlanes
  walk2

open OnBytes.Model.Head in
/-- `Head.claimLogits` keeps R. -/
instance pres_Model_Head_claimLogits [Prim R] (Rn : OnBytes.Model.Head.Run) :
    Pres R (OnBytes.Model.Head.claimLogits Rn) := by
  unfold OnBytes.Model.Head.claimLogits
  walk2

open OnBytes.Model.Head in
/-- `Head.noteConstant` keeps R. -/
instance pres_Model_Head_noteConstant [Prim R] (group : String) :
    Pres R (OnBytes.Model.Head.noteConstant group) := by
  unfold OnBytes.Model.Head.noteConstant
  walk2

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_range
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_mapMArr
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_wsForkEnd
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Head_hear
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Head_claimLogits
