-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsIop.lean: the class Keeps of OnBytes/Tie/Pv/Keeps/KeepsKit.lean for the
blocks of OnBytes/Iop/ that stand under a request's frame (ReqFrame) and under the first part of the
test on the table (memberFirstVerify). Each routine is unfolded once and walked by the tactic keeps;
a routine that calls itself is walked by induction on the argument that falls.
-/
import OnBytes.Tie.Pv.Keeps.KeepsKit
import OnBytes.Iop.ReqRows
import OnBytes.Iop.Lin

namespace OnBytes.L5

open OnBytes

/-! ## SEND (OnBytes/Iop/Send.lean) -/

instance keeps_admit (o : Nat) (rows : Array Row) : Keeps (Send.admit o rows) := by
  unfold Send.admit; keeps
instance keeps_sendVerify' (ids : Array Nat) (own : Bool) : Keeps (Send.verify ids own) := by
  unfold Send.verify; keeps
instance keeps_sendVerify (n : Array OracleNotice) (own : Bool) : Keeps (sendVerify n own) := by
  unfold sendVerify; keeps

/-! ## BAT (OnBytes/Iop/Bat.lean) -/

instance keeps_batVerify (g : Nat) : Keeps (batVerify g) := by unfold batVerify; keeps

/-! ## FOLD (OnBytes/Iop/Fold.lean) -/

instance keeps_singleRowsRead (s : SingleRows) (p : Positions) : Keeps (singleRowsRead s p) := by
  unfold singleRowsRead; keeps
instance keeps_foldStartVerify (F : FoldShape) (m : Option Nat) :
    Keeps (foldStartVerify F m) := by
  unfold foldStartVerify; keeps
instance keeps_foldEpsilon (s : FoldStart) : Keeps (foldEpsilon s) := by
  unfold foldEpsilon; keeps
instance keeps_foldRounds (n : Nat) (claim : E) : Keeps (foldRounds n claim) := by
  induction n generalizing claim with
  | zero => unfold foldRounds; keeps
  | succ n ih => unfold foldRounds; keeps
instance keeps_foldRoundsVerify (F : FoldShape) (row : GroupRow) (s : FoldStart) :
    Keeps (foldRoundsVerify F row s) := by
  unfold foldRoundsVerify; keeps
instance keeps_foldVerify (F : FoldShape) (row : GroupRow) (m : Option Nat) :
    Keeps (foldVerify F row m) := by
  unfold foldVerify; keeps

/-! ## The code switch (OnBytes/Iop/Cs.lean) -/

instance keeps_switchAdmit (old : SingleRows) (T : SwitchTarget) (to : Nat) (out : Switched)
    (y : Array E) : Keeps (switchAdmit old T to out y) := by
  unfold switchAdmit; keeps
instance keeps_switchVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) (th : Bool) : Keeps (switchVerify old T to others th) := by
  unfold switchVerify; keeps
instance keeps_csSigmaVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Keeps (csSigmaVerify old T to others) := by
  unfold csSigmaVerify; keeps
instance keeps_csVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Keeps (csVerify old T to others) := by
  unfold csVerify; keeps

/-! ## The proximity test (OnBytes/Iop/Prox.lean) -/

instance keeps_recvVectors (l : List Nat) : Keeps (recvVectors l) := by
  induction l with
  | nil => unfold recvVectors; keeps
  | cons n ns ih => unfold recvVectors; keeps
instance keeps_baseVerify (R : SingleRows) (m : Option Nat) (lc : Nat) :
    Keeps (baseVerify R m lc) := by
  unfold baseVerify; keeps
instance keeps_ioppStagesVerify (answers : Nat) (ride : Bool) (cur : Params.IoppStage)
    (rest : List Params.IoppStage) (row : GroupRow) (L : GroupLayout) (m : Option Nat) :
    Keeps (ioppStagesVerify answers ride cur rest row L m) := by
  induction rest generalizing cur row L m with
  | nil => unfold ioppStagesVerify; keeps
  | cons next rest ih => unfold ioppStagesVerify; keeps
instance keeps_ioppVerify (g : Nat) (st : List Params.IoppStage) (ch : Params.IoppChoice) (m : Option Nat) :
    Keeps (ioppVerify g st ch m) := by
  unfold ioppVerify; keeps

/-! ## The frame of a request's chain (OnBytes/Iop/Req.lean, ReqRows.lean) -/

instance keeps_frameStart (s : Params.ReqShape) : Keeps (ReqFrame.start s) := by
  unfold ReqFrame.start; keeps
instance keeps_joinOwn (f : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) :
    Keeps (f.joinOwn sent ids) := by
  unfold ReqFrame.joinOwn; keeps
instance keeps_beginLink (f : ReqFrame) : Keeps f.beginLink := by
  unfold ReqFrame.beginLink; keeps
instance keeps_frameFirst (f : ReqFrame) : Keeps f.first := by unfold ReqFrame.first; keeps
instance keeps_frameLater (f : ReqFrame) : Keeps f.later := by unfold ReqFrame.later; keeps
instance keeps_frameClose (f : ReqFrame) : Keeps f.close := by unfold ReqFrame.close; keeps
instance keeps_frameFinish (f : ReqFrame) : Keeps f.finish := by unfold ReqFrame.finish; keeps
instance keeps_rowsMake (s : Params.ReqShape) (l : Params.ReqLayout) :
    Keeps (ReqRows.make s l) := by
  unfold ReqRows.make; keeps
instance keeps_rowsRow (R : ReqRows) (f : ReqFrame) (eq : ReqEquation) : Keeps (R.row f eq) := by
  unfold ReqRows.row; keeps

/-! ## The sumcheck and the batching of tensor rows (OnBytes/Iop/Psc.lean, Batt.lean) -/

instance keeps_hearOne (n : String) (k : Fmt.Kind) (a b : Nat) : Keeps (Psc.hearOne n k a b) := by
  unfold Psc.hearOne; keeps
instance keeps_hearMany (l : List Nat) : Keeps (Psc.hearMany l) := by
  induction l with
  | nil => unfold Psc.hearMany; keeps
  | cons n ns ih => unfold Psc.hearMany; keeps
instance keeps_hear (x : Psc.Size) : Keeps (Psc.hear x) := by unfold Psc.hear; keeps
instance keeps_pscVerify (c : Psc.Claim) (S : Psc.Summand) (fr : List Slot) :
    Keeps (Psc.verify c S fr) := by
  unfold Psc.verify; keeps
instance keeps_takeSlots (o n : Nat) : Keeps (takeSlots o n) := by unfold takeSlots; keeps
instance keeps_battVerify (k : Nat) (rows : List TensorRow) (l : Nat) :
    Keeps (Batt.verify k rows l) := by
  unfold Batt.verify; keeps

/-! ## The first part of the test on the table (OnBytes/Iop/Lin.lean) -/

instance keeps_linFirstRows (S : Params.LinShape) (cl : LinClaim) (ids : Array Nat) :
    Keeps (linFirstRows S cl ids) := by
  unfold linFirstRows; keeps
instance keeps_linFirstVerify (S : Params.LinShape) (cl : LinClaim) :
    Keeps (linFirstVerify S cl) := by
  unfold linFirstVerify; keeps
instance keeps_memberFirstVerify (S : Params.LinShape) (i : Nat) (pend : List TensorRow) :
    Keeps (memberFirstVerify S i pend) := by
  unfold memberFirstVerify; keeps

#print axioms keeps_admit
#print axioms keeps_sendVerify'
#print axioms keeps_sendVerify
#print axioms keeps_batVerify
#print axioms keeps_singleRowsRead
#print axioms keeps_foldStartVerify
#print axioms keeps_foldEpsilon
#print axioms keeps_foldRounds
#print axioms keeps_foldRoundsVerify
#print axioms keeps_foldVerify
#print axioms keeps_switchAdmit
#print axioms keeps_switchVerify
#print axioms keeps_csSigmaVerify
#print axioms keeps_csVerify
#print axioms keeps_recvVectors
#print axioms keeps_baseVerify
#print axioms keeps_ioppStagesVerify
#print axioms keeps_ioppVerify
#print axioms keeps_frameStart
#print axioms keeps_joinOwn
#print axioms keeps_beginLink
#print axioms keeps_frameFirst
#print axioms keeps_frameLater
#print axioms keeps_frameClose
#print axioms keeps_frameFinish
#print axioms keeps_rowsMake
#print axioms keeps_rowsRow
#print axioms keeps_hearOne
#print axioms keeps_hearMany
#print axioms keeps_hear
#print axioms keeps_pscVerify
#print axioms keeps_takeSlots
#print axioms keeps_battVerify
#print axioms keeps_linFirstRows
#print axioms keeps_linFirstVerify
#print axioms keeps_memberFirstVerify

end OnBytes.L5
