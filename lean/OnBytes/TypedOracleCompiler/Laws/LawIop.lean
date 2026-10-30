-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawIop.lean: the class `Same (Alike G d)` for 44 routines of OnBytes/Iop/ that
name neither the book of trees nor a source nor a digest.

The class (OnBytes/TypedOracleCompiler/Laws/LawKit.lean, LawAlike.lean) says: one text, from contexts that are
alike, fails alike or gives equal values and leaves contexts that are alike. The form of each proof
is the same: the routine is unfolded once and walked by the tactic; a routine that calls itself is
walked by induction on the argument that falls.

Not claimed. Nothing on two texts with different arguments (OnBytes/TypedOracleCompiler/Laws/LawDry.lean), nor on
the routines that name the book (OnBytes/TypedOracleCompiler/Laws/LawTail.lean). These 44 are not all such routines.
Lkp's and Wf's are walked by the command in OnBytes/TypedOracleCompiler/Laws/LawKey.lean. No file of this folder has
a law for groupTarget, linkStepsVerify, linkTestVerify, linkVerify (OnBytes/Iop/Link.lean) or for
reqLaterMoments, reqLinks, reqVerify (OnBytes/Iop/Req.lean). linkVerify is the block of an entry
file's chain: so this folder says nothing of an entry file.

-/
import OnBytes.TypedOracleCompiler.Laws.LawSend
import OnBytes.Iop.ReqRows
import OnBytes.Iop.Lin

namespace OnBytes.TwoLaws

open OnBytes

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

/-! ## BAT (OnBytes/Iop/Bat.lean) -/

instance same_batVerify (g : Nat) : Same (Alike G d) (batVerify g) := by unfold batVerify; walk

/-! ## FOLD (OnBytes/Iop/Fold.lean) -/

instance same_singleRowsRead (s : SingleRows) (p : Positions) :
    Same (Alike G d) (singleRowsRead s p) := by
  unfold singleRowsRead; walk
instance same_foldStartVerify (F : FoldShape) (m : Option Nat) :
    Same (Alike G d) (foldStartVerify F m) := by
  unfold foldStartVerify; walk
instance same_foldEpsilon (s : FoldStart) : Same (Alike G d) (foldEpsilon s) := by
  unfold foldEpsilon; walk
instance same_foldRounds (n : Nat) (claim : E) : Same (Alike G d) (foldRounds n claim) := by
  induction n generalizing claim with
  | zero => unfold foldRounds; walk
  | succ n ih => unfold foldRounds; walk
instance same_foldRoundsVerify (F : FoldShape) (row : GroupRow) (s : FoldStart) :
    Same (Alike G d) (foldRoundsVerify F row s) := by
  unfold foldRoundsVerify; walk
instance same_foldVerify (F : FoldShape) (row : GroupRow) (m : Option Nat) :
    Same (Alike G d) (foldVerify F row m) := by
  unfold foldVerify; walk

/-! ## The code switch (OnBytes/Iop/Cs.lean) -/

instance same_switchAdmit (old : SingleRows) (T : SwitchTarget) (to : Nat) (out : Switched)
    (y : Array E) : Same (Alike G d) (switchAdmit old T to out y) := by
  unfold switchAdmit; walk
instance same_switchVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) (th : Bool) :
    Same (Alike G d) (switchVerify old T to others th) := by
  unfold switchVerify; walk
instance same_csSigmaVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Same (Alike G d) (csSigmaVerify old T to others) := by
  unfold csSigmaVerify; walk
instance same_csVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Same (Alike G d) (csVerify old T to others) := by
  unfold csVerify; walk

/-! ## The proximity test (OnBytes/Iop/Prox.lean) -/

instance same_recvVectors (l : List Nat) : Same (Alike G d) (recvVectors l) := by
  induction l with
  | nil => unfold recvVectors; walk
  | cons n ns ih => unfold recvVectors; walk
instance same_baseVerify (R : SingleRows) (m : Option Nat) (lc : Nat) :
    Same (Alike G d) (baseVerify R m lc) := by
  unfold baseVerify; walk
instance same_ioppStagesVerify (answers : Nat) (ride : Bool) (cur : Params.IoppStage)
    (rest : List Params.IoppStage) (row : GroupRow) (L : GroupLayout) (m : Option Nat) :
    Same (Alike G d) (ioppStagesVerify answers ride cur rest row L m) := by
  induction rest generalizing cur row L m with
  | nil => unfold ioppStagesVerify; walk
  | cons next rest ih => unfold ioppStagesVerify; walk
instance same_ioppVerify (g : Nat) (st : List Params.IoppStage) (ch : Params.IoppChoice) (m : Option Nat) :
    Same (Alike G d) (ioppVerify g st ch m) := by
  unfold ioppVerify; walk

/-! ## The frame of a request's chain (OnBytes/Iop/Req.lean, ReqRows.lean) -/

instance same_frameStart (s : Params.ReqShape) : Same (Alike G d) (ReqFrame.start s) := by
  unfold ReqFrame.start; walk
instance same_joinOwn (f : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) :
    Same (Alike G d) (f.joinOwn sent ids) := by
  unfold ReqFrame.joinOwn; walk
instance same_beginLink (f : ReqFrame) : Same (Alike G d) f.beginLink := by
  unfold ReqFrame.beginLink; walk
instance same_frameFirst (f : ReqFrame) : Same (Alike G d) f.first := by unfold ReqFrame.first; walk
instance same_frameLater (f : ReqFrame) : Same (Alike G d) f.later := by unfold ReqFrame.later; walk
instance same_frameClose (f : ReqFrame) : Same (Alike G d) f.close := by unfold ReqFrame.close; walk
instance same_frameFinish (f : ReqFrame) :
    Same (Alike G d) f.finish := by unfold ReqFrame.finish; walk
instance same_rowsMake (s : Params.ReqShape) (l : Params.ReqLayout) :
    Same (Alike G d) (ReqRows.make s l) := by
  unfold ReqRows.make; walk
instance same_rowsRow (R : ReqRows) (f : ReqFrame) (eq : ReqEquation) :
    Same (Alike G d) (R.row f eq) := by
  unfold ReqRows.row; walk

/-! ## The sumcheck and the batching of tensor rows (OnBytes/Iop/Psc.lean, Batt.lean) -/

instance same_hearOne (n : String) (k : Fmt.Kind) (a b : Nat) :
    Same (Alike G d) (Psc.hearOne n k a b) := by
  unfold Psc.hearOne; walk
instance same_hearMany (l : List Nat) : Same (Alike G d) (Psc.hearMany l) := by
  induction l with
  | nil => unfold Psc.hearMany; walk
  | cons n ns ih => unfold Psc.hearMany; walk
instance same_hear (x : Psc.Size) : Same (Alike G d) (Psc.hear x) := by unfold Psc.hear; walk
instance same_pscVerify (c : Psc.Claim) (S : Psc.Summand) (fr : List Slot) :
    Same (Alike G d) (Psc.verify c S fr) := by
  unfold Psc.verify; walk
instance same_takeSlots (o n : Nat) : Same (Alike G d) (takeSlots o n) := by unfold takeSlots; walk
instance same_battVerify (k : Nat) (rows : List TensorRow) (l : Nat) :
    Same (Alike G d) (Batt.verify k rows l) := by
  unfold Batt.verify; walk

/-! ## The first part of the test on the table (OnBytes/Iop/Lin.lean) -/

instance same_linFirstRows (S : Params.LinShape) (cl : LinClaim) (ids : Array Nat) :
    Same (Alike G d) (linFirstRows S cl ids) := by
  unfold linFirstRows; walk
instance same_linFirstVerify (S : Params.LinShape) (cl : LinClaim) :
    Same (Alike G d) (linFirstVerify S cl) := by
  unfold linFirstVerify; walk
instance same_memberFirstVerify (S : Params.LinShape) (i : Nat) (pend : List TensorRow) :
    Same (Alike G d) (memberFirstVerify S i pend) := by
  unfold memberFirstVerify; walk

/-! ## Under the tail's blocks (Bat, Split, Foldeq, Lin, Psc) -/

instance same_batSigmaVerify (rows : Array Row) : Same (Alike G d) (batSigmaVerify rows) := by
  unfold batSigmaVerify; walk
instance same_splitVerify (row : Row) (g1 g2 m : Nat) :
    Same (Alike G d) (splitVerify row g1 g2 m) := by
  unfold splitVerify; walk
instance same_drawPoint (r : String) (n : Nat) : Same (Alike G d) (drawPoint r n) := by
  unfold drawPoint; walk
instance same_foldeqJoined (S : Params.FoldeqShape) (key : TableKey) (e : Array E) (o g : Nat) :
    Same (Alike G d) (foldeqJoined S key e o g) := by
  unfold foldeqJoined; walk
instance same_foldeqColumnsVerify (key : TableKey) (S : Params.FoldeqShape) (e : Array E)
    (pos : Positions) (first : Nat) (u : FoldedRow) (g : Nat) :
    Same (Alike G d) (foldeqColumnsVerify key S e pos first u g) := by
  unfold foldeqColumnsVerify; walk
instance same_foldeqRequire (key : TableKey) (S : Params.FoldeqShape) :
    Same (Alike G d) (foldeqRequire key S) := by
  unfold foldeqRequire; walk
instance same_foldeqVerify (key : TableKey) (S : Params.FoldeqShape) (gamma : List E) (g : Nat)
    (others : Array OracleNotice) : Same (Alike G d) (foldeqVerify key S gamma g others) := by
  unfold foldeqVerify; walk
instance same_linSharedTestsVerify (S : Params.LinShape) (x : LinShared) :
    Same (Alike G d) (linSharedTestsVerify S x) := by
  unfold linSharedTestsVerify; walk
instance same_linSecondTestsVerify (S : Params.LinShape) (first : LinFirst) (x : LinSecond) :
    Same (Alike G d) (linSecondTestsVerify S first x) := by
  unfold linSecondTestsVerify; walk
instance same_hearDraw (n : String) (k : Nat) : Same (Alike G d) (hearDraw n k) := by
  unfold hearDraw; walk
instance same_line (a b : PointClaim) : Same (Alike G d) (line a b) := by
  unfold line; walk

end OnBytes.TwoLaws
