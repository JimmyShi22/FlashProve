-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksKeepsBank.lean: the checks of the model's sub-proofs, and the calls of the
request's chain, leave the two flags of a run as they are.

Each theorem has the name `OnBytes.Flat.KeepsOf` ++ f of a routine f and says `Over.K (f x₁ …)` at
all arguments; where an argument is itself a routine, the same is asked of it. Each is shown by the
walk (`keeps`, OnBytes/Flat/LinksKeepsTool.lean), which goes through f's text and finds the theorems
on the routines that f calls by their names: so a routine's theorem stands behind those of the
routines that it calls. The statements were written out by a program from the list that the command
`keeps_bank` of that file makes; Lean checks each as it stands here. The routines that call
themselves and the blocks written as functions of the context have their theorems in
OnBytes/Flat/LinksKeepsHand.lean.

Main theorems, each the last of its section: on `Layer.runForkHidG2`, `Attention.run`,
`Head.runForkHidH2`, the checks of the three kinds of sub-proof; on `ChainCheck.start`, `first`,
`finish`; on `Stages.pendingRowH` and `Stages.indexMasksH`.

Not claimed: anything on what a routine decides. For proofs only; no module of the program imports
this file.


-/
import OnBytes.Flat.LinksKeepsHand

set_option autoImplicit false

namespace OnBytes.Flat

/-! ### `OnBytes.Model.Layer.runForkHidG2`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.takeMasks (o count : Nat) :
    Over.K (OnBytes.Blk.takeMasks o count) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.draws (h : OnBytes.Model.Forest.Shape) :
    Over.K (OnBytes.Model.Forest.draws h) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.paddingLaid (g : OnBytes.Model.Forest.Heard)
    (laid : Array Nat) : Over.K (OnBytes.Model.Forest.paddingLaid g laid) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.planesAt (g : OnBytes.Model.Forest.Heard)
    (lm e : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Over.K (bit a a_1)) :
    Over.K (OnBytes.Model.Forest.planesAt g lm e bit) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.coefficientsF (tl : OnBytes.Model.HTailF2) :
    Over.K tl.coefficientsF := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.weightsF (tl : OnBytes.Model.HTailF2) :
    Over.K tl.weightsF := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.form {α : Type} (x : Option α) :
    Over.K (OnBytes.Model.Layer.form x) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.freeSlotTest (g used sFv : Nat) :
    Over.K (OnBytes.Model.Layer.freeSlotTest g used sFv) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.joinStart (v : OnBytes.Model.Layer.Env)
    (H : OnBytes.Model.Layer.Heard) (om : Array OnBytes.E) :
    Over.K (OnBytes.Model.Layer.joinStart v H om) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.note (what : String) (x : OnBytes.E) :
    Over.K (OnBytes.Model.Layer.note what x) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.noteClaims (what : String) :
    Over.K (OnBytes.Model.Layer.noteClaims what) := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.call
    (f : OnBytes.Model.ChainCheck → OnBytes.Blk OnBytes.Model.ChainCheck)
    (h : ∀ (a : OnBytes.Model.ChainCheck), Over.K (f a)) :
    Over.K (OnBytes.Model.LinkM.call f) := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.sub {α : Type} (x : OnBytes.Model.SubM α)
    (h : Over.K x) : Over.K (OnBytes.Model.LinkM.sub x) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.allTaken :
    Over.K OnBytes.Model.SubM.allTaken := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.batchBy (drawn : OnBytes.E) :
    Over.K (OnBytes.Model.SubM.batchBy drawn) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.claims :
    Over.K OnBytes.Model.SubM.claims := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.kap :
    Over.K OnBytes.Model.SubM.kap := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.lin (f : OnBytes.Model.Aff) :
    Over.K (OnBytes.Model.SubM.lin f) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.owe (what : String) :
    Over.K (OnBytes.Model.SubM.owe what) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.paid (i : Nat) :
    Over.K (OnBytes.Model.SubM.paid i) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.push (w : OnBytes.E) (a : OnBytes.Model.Aff) :
    Over.K (OnBytes.Model.SubM.push w a) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.rootTaken (t w : Nat) :
    Over.K (OnBytes.Model.SubM.rootTaken t w) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.setPlanClaims (n : Nat) :
    Over.K (OnBytes.Model.SubM.setPlanClaims n) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.settle (used : Nat) :
    Over.K (OnBytes.Model.SubM.settle used) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.shown (j : Nat) :
    Over.K (OnBytes.Model.SubM.shown j) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.slot :
    Over.K OnBytes.Model.SubM.slot := by
  keeps

theorem KeepsOf.OnBytes.Model.layerObject (o : OnBytes.Model.Level) :
    Over.K (OnBytes.Model.layerObject o) := by
  keeps

theorem KeepsOf.OnBytes.Model.levelIn (mu : Nat) (rho : Array OnBytes.E)
    (C : OnBytes.Model.Aff) (order : List Nat) :
    Over.K (OnBytes.Model.levelIn mu rho C order) := by
  keeps

theorem KeepsOf.OnBytes.Model.roundsIn (form : OnBytes.Model.RoundForm)
    (p : OnBytes.Model.Psc) (zs : List (OnBytes.E × Nat)) :
    Over.K (OnBytes.Model.roundsIn form p zs) := by
  keeps

theorem KeepsOf.OnBytes.Model.stackRounds (st : OnBytes.Model.Stack) :
    Over.K (OnBytes.Model.stackRounds st) := by
  keeps

theorem KeepsOf.OnBytes.Model.t2Lin (a : OnBytes.Model.Aff)
    (runs : Array OnBytes.Model.Run2) : Over.K (OnBytes.Model.t2Lin a runs) := by
  keeps

theorem KeepsOf.OnBytes.Model.testAs (name : String) (b : Bool) :
    Over.K (OnBytes.Model.testAs name b) := by
  keeps

theorem KeepsOf.OnBytes.Model.trBatchOpen :
    Over.K OnBytes.Model.trBatchOpen := by
  keeps

theorem KeepsOf.OnBytes.Model.trBatchRows (rows : Nat) :
    Over.K (OnBytes.Model.trBatchRows rows) := by
  keeps

theorem KeepsOf.OnBytes.Model.trPoint (r : OnBytes.Model.RoundName) (n : Nat) :
    Over.K (OnBytes.Model.trPoint r n) := by
  keeps

theorem KeepsOf.OnBytes.Model.trTrits (columns combinations : Nat) :
    Over.K (OnBytes.Model.trTrits columns combinations) := by
  keeps

theorem KeepsOf.OnBytes.Model.tscRounds (P : Array OnBytes.E) (lt : Nat) :
    Over.K (OnBytes.Model.tscRounds P lt) := by
  keeps

theorem KeepsOf.OnBytes.Model.wsForkLin (o : OnBytes.Model.WsMerged) :
    Over.K (OnBytes.Model.wsForkLin o) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.joinOwn (f : OnBytes.ReqFrame)
    (sent : List OnBytes.Params.ReqMessage) (ids : Array Nat) :
    Over.K (f.joinOwn sent ids) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.later (f : OnBytes.ReqFrame) :
    Over.K f.later := by
  keeps

theorem KeepsOf.OnBytes.ReqRows.row (R : OnBytes.ReqRows) (f : OnBytes.ReqFrame)
    (eq : OnBytes.ReqEquation) : Over.K (R.row f eq) := by
  keeps

theorem KeepsOf.OnBytes.batVerify (g : Nat) :
    Over.K (OnBytes.batVerify g) := by
  keeps

theorem KeepsOf.OnBytes.Model.ChainCheck.later (c : OnBytes.Model.ChainCheck) :
    Over.K c.later := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.joinAdded (g : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Forest.joinAdded g) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.level (s : OnBytes.Model.Forest.Descent)
    (mu : Nat) (order : List Nat) : Over.K (OnBytes.Model.Forest.level s mu order) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.objects (g : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Forest.objects g) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.planeClaims (g : OnBytes.Model.Forest.Heard)
    (lm : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (pin : Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Over.K (bit a a_1)) :
    (∀ (a : Nat), Over.K (pin a)) →
      Over.K (OnBytes.Model.Forest.planeClaims g lm bit pin) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.planesAdded (g : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Forest.planesAdded g) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.tieStep (a : OnBytes.E)
    (s : OnBytes.Model.Forest.TieStep) (j : Nat) :
    Over.K (OnBytes.Model.Forest.tieStep a s j) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.coefficients (tl : OnBytes.Model.HTailF2) :
    Over.K tl.coefficients := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.linBits9 (tl : OnBytes.Model.HTailF2) :
    Over.K tl.linBits9 := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.linJoin9 (tl : OnBytes.Model.HTailF2) :
    Over.K tl.linJoin9 := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.linRead (tl : OnBytes.Model.HTailF2)
    (Fn : OnBytes.Model.HFun) (sg laid : Nat) (sums : OnBytes.E) :
    Over.K (tl.linRead Fn sg laid sums) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.linTie (tl : OnBytes.Model.HTailF2) (mu : Nat) :
    Over.K (tl.linTie mu) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.objectsF (tl : OnBytes.Model.HTailF2)
    (funs : Array OnBytes.Model.HFun) : Over.K (tl.objectsF funs) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.selfTestF (tl : OnBytes.Model.HTailF2)
    (nU : Array Nat) : Over.K (tl.selfTestF nU) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.tileSelfTestF (tl : OnBytes.Model.HTailF2) :
    Over.K tl.tileSelfTestF := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimEmbedding (v : OnBytes.Model.Layer.Env)
    (H : OnBytes.Model.Layer.Heard) (sVE : Nat) :
    Over.K (OnBytes.Model.Layer.claimEmbedding v H sVE) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimRowBatch (y : OnBytes.Model.Layer.Lay)
    (H : OnBytes.Model.Layer.Heard) :
    Over.K (OnBytes.Model.Layer.claimRowBatch y H) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsEnds (v : OnBytes.Model.Layer.Env)
    (o : OnBytes.Model.Level) (e : Array OnBytes.E) (t rows blocks stride : Nat) (lamOf : Nat → Nat)
    (first : Nat) :
    Over.K (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsGated (P : OnBytes.Model.Layer.Pub)
    (v : OnBytes.Model.Layer.Env) (hd : OnBytes.Model.Level) (hd2 : Option OnBytes.Model.Level) :
    Over.K (OnBytes.Model.Layer.claimsGated P v hd hd2) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsNorms (P : OnBytes.Model.Layer.Pub)
    (v : OnBytes.Model.Layer.Env) (H : OnBytes.Model.Layer.Heard) :
    Over.K (OnBytes.Model.Layer.claimsNorms P v H) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsOneHot (v : OnBytes.Model.Layer.Env) :
    Over.K (OnBytes.Model.Layer.claimsOneHot v) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsTerms (v : OnBytes.Model.Layer.Env)
    (H : OnBytes.Model.Layer.Heard) : Over.K (OnBytes.Model.Layer.claimsTerms v H) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.shownRun (first n : Nat) :
    Over.K (OnBytes.Model.Layer.shownRun first n) := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.fork :
    Over.K OnBytes.Model.LinkM.fork := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.must (b : Bool) :
    Over.K (OnBytes.Model.LinkM.must b) := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.mustAs (name : String) (b : Bool) :
    Over.K (OnBytes.Model.LinkM.mustAs name b) := by
  keeps

theorem KeepsOf.OnBytes.Model.LinkM.testAs (name : String) (b : Bool) :
    Over.K (OnBytes.Model.LinkM.testAs name b) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.batchOpen :
    Over.K OnBytes.Model.SubM.batchOpen := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.batchRows (rows : Nat) :
    Over.K (OnBytes.Model.SubM.batchRows rows) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.point (r : OnBytes.Model.RoundName) (n : Nat) :
    Over.K (OnBytes.Model.SubM.point r n) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.trits (columns combinations : Nat) :
    Over.K (OnBytes.Model.SubM.trits columns combinations) := by
  keeps

theorem KeepsOf.OnBytes.Model.rootInH (trees : List Nat) :
    Over.K (OnBytes.Model.rootInH trees) := by
  keeps

theorem KeepsOf.OnBytes.Model.rowWeights (X : OnBytes.Model.HTree)
    (r : OnBytes.Model.HRow) : Over.K (OnBytes.Model.rowWeights X r) := by
  keeps

theorem KeepsOf.OnBytes.Model.t2Batch (used : Nat) :
    Over.K (OnBytes.Model.t2Batch used) := by
  keeps

theorem KeepsOf.OnBytes.Model.trBatch (rows : Nat) :
    Over.K (OnBytes.Model.trBatch rows) := by
  keeps

theorem KeepsOf.OnBytes.Model.tscIn (P : Array OnBytes.E) (lt shown degreeInY : Nat) :
    Over.K (OnBytes.Model.tscIn P lt shown degreeInY) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.close (f : OnBytes.ReqFrame) :
    Over.K f.close := by
  keeps

theorem KeepsOf.OnBytes.Model.ChainCheck.close (c : OnBytes.Model.ChainCheck)
    (equation : OnBytes.ReqEquation) : Over.K (c.close equation) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.planeLins (g : OnBytes.Model.Forest.Heard)
    (lm : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (pin : Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Over.K (bit a a_1)) :
    (∀ (a : Nat), Over.K (pin a)) →
      Over.K (OnBytes.Model.Forest.planeLins g lm bit pin) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.tie (a : OnBytes.E) :
    Over.K (OnBytes.Model.Forest.tie a) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.drawMatrixF (tl : OnBytes.Model.HTailF2) :
    Over.K tl.drawMatrixF := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.fixedBeforeTheMatrixF
    (tl : OnBytes.Model.HTailF2) : Over.K tl.fixedBeforeTheMatrixF := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.rkSelfTest (tl : OnBytes.Model.HTailF2) :
    Over.K tl.rkSelfTest := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.selfTest (tl : OnBytes.Model.HTailF2)
    (nU : Array Nat) : Over.K (tl.selfTest nU) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsLedger4 (v : OnBytes.Model.Layer.Env)
    (H : OnBytes.Model.Layer.Heard) :
    Over.K (OnBytes.Model.Layer.claimsLedger4 v H) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsLedger5 (v : OnBytes.Model.Layer.Env)
    (H : OnBytes.Model.Layer.Heard) :
    Over.K (OnBytes.Model.Layer.claimsLedger5 v H) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.claimsPlanes (v : OnBytes.Model.Layer.Env)
    (fo : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Layer.claimsPlanes v fo) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearGated (P : OnBytes.Model.Layer.Pub)
    (H : OnBytes.Model.Layer.Heard) (K : OnBytes.Model.Layer.HeardStack) :
    Over.K (OnBytes.Model.Layer.hearGated P H K) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearTerms (P : OnBytes.Model.Layer.Pub)
    (H : OnBytes.Model.Layer.Heard) : Over.K (OnBytes.Model.Layer.hearTerms P H) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.batch (rows : Nat) :
    Over.K (OnBytes.Model.SubM.batch rows) := by
  keeps

theorem KeepsOf.OnBytes.Model.doorTerms (born : Nat) (array : String)
    (X : OnBytes.Model.HTree) : Over.K (OnBytes.Model.doorTerms born array X) := by
  keeps

theorem KeepsOf.OnBytes.Model.wsForkMerge (lk : Nat) (sv : Array Nat) :
    Over.K (OnBytes.Model.wsForkMerge lk sv) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.pad (calls : Array OnBytes.Model.Call)
    (pub : Array Nat) (lid : Nat) : Over.K (OnBytes.Model.Forest.pad calls pub lid) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.transcriptF (tl : OnBytes.Model.HTailF2) :
    Over.K tl.transcriptF := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearLook (y : OnBytes.Model.Layer.Lay) (g : Nat) :
    Over.K (OnBytes.Model.Layer.hearLook y g) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearNorms (P : OnBytes.Model.Layer.Pub) (g : Nat)
    (fo : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Layer.hearNorms P g fo) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearStack (P : OnBytes.Model.Layer.Pub)
    (v : OnBytes.Model.Layer.Env) (H : OnBytes.Model.Layer.Heard) (lamS NCLp : Nat) :
    Over.K (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by
  keeps

theorem KeepsOf.OnBytes.Model.doorH (equationsLaid : Nat) :
    Over.K (OnBytes.Model.doorH equationsLaid) := by
  keeps

theorem KeepsOf.OnBytes.Model.wsForkEnd (lay : OnBytes.Model.WsLay)
    (cl : Array OnBytes.Model.WsClaim) (sv : Array Nat) :
    Over.K (OnBytes.Model.wsForkEnd lay cl sv) := by
  keeps

theorem KeepsOf.OnBytes.Model.HTailF2.transcript (tl : OnBytes.Model.HTailF2) :
    Over.K tl.transcript := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.hearOwn (P : OnBytes.Model.Layer.Pub)
    (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) (fo : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Layer.hearOwn P hp g fo) := by
  keeps

theorem KeepsOf.OnBytes.Model.Layer.runForkHidG2 (P : OnBytes.Model.Layer.Pub)
    (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) :
    Over.K (OnBytes.Model.Layer.runForkHidG2 P hp g) := by
  keeps

/-! ### `OnBytes.Attention.run`, and what its text reaches -/

theorem KeepsOf.OnBytes.Attention.PlaceM.getAs {α : Type} (name : String)
    (x : Option α) : Over.K (OnBytes.Attention.PlaceM.getAs name x) := by
  keeps

theorem KeepsOf.OnBytes.Attention.PlaceM.placed :
    Over.K OnBytes.Attention.PlaceM.placed := by
  keeps

theorem KeepsOf.OnBytes.Attention.PlaceM.total (start : Nat) :
    Over.K (OnBytes.Attention.PlaceM.total start) := by
  keeps

theorem KeepsOf.OnBytes.Attention.PlaceM.weights (len : Nat)
    (f : Unit → Array OnBytes.E) : Over.K (OnBytes.Attention.PlaceM.weights len f) := by
  keeps

theorem KeepsOf.OnBytes.Attention.Seam.batch (used : Nat) :
    Over.K (OnBytes.Attention.Seam.batch used) := by
  keeps

theorem KeepsOf.OnBytes.Attention.Seam.finish (tl : OnBytes.Model.HTailF2)
    (nU : Array Nat) : Over.K (OnBytes.Attention.Seam.finish tl nU) := by
  keeps

theorem KeepsOf.OnBytes.Attention.Seam.objects (tl : OnBytes.Model.HTailF2)
    (funs : Array OnBytes.Model.HFun) :
    Over.K (OnBytes.Attention.Seam.objects tl funs) := by
  keeps

theorem KeepsOf.OnBytes.Attention.Seam.start (s : OnBytes.Attention.Seam) (ns : Nat) :
    Over.K (s.start ns) := by
  keeps

theorem KeepsOf.OnBytes.Attention.Seam.transcript (tl : OnBytes.Model.HTailF2) :
    Over.K (OnBytes.Attention.Seam.transcript tl) := by
  keeps

theorem KeepsOf.OnBytes.Attention.add (mats : Array OnBytes.Model.TMat) (mat len : Nat)
    (phi : Array OnBytes.E) (elems : Nat) :
    Over.K (OnBytes.Attention.add mats mat len phi elems) := by
  keeps

theorem KeepsOf.OnBytes.Attention.addAs (S : OnBytes.Attention.Shape)
    (mats : Array OnBytes.Model.TMat) (phi : Unit → Array OnBytes.E) :
    Over.K (OnBytes.Attention.addAs S mats phi) := by
  keeps

theorem KeepsOf.OnBytes.Attention.addRow (S : OnBytes.Attention.Shape)
    (mats : Array OnBytes.Model.TMat) (psi : Unit → Array OnBytes.E) :
    Over.K (OnBytes.Attention.addRow S mats psi) := by
  keeps

theorem KeepsOf.OnBytes.Attention.allJoined (j : OnBytes.Attention.Joins) :
    Over.K (OnBytes.Attention.allJoined j) := by
  keeps

theorem KeepsOf.OnBytes.Attention.coinsOm (n : Nat) :
    Over.K (OnBytes.Attention.coinsOm n) := by
  keeps

theorem KeepsOf.OnBytes.Attention.countsHeld (P : OnBytes.Attention.Plan)
    (tl : OnBytes.Model.HTailF2) : Over.K (OnBytes.Attention.countsHeld P tl) := by
  keeps

theorem KeepsOf.OnBytes.Attention.keyTerm (S : OnBytes.Attention.Shape) (sKC : Nat)
    (pj : Array OnBytes.E) (w : OnBytes.E) (b : Nat) :
    Over.K (OnBytes.Attention.keyTerm S sKC pj w b) := by
  keeps

theorem KeepsOf.OnBytes.Attention.lessPieces (start : OnBytes.Model.Aff)
    (pw : Array OnBytes.Attention.PW)
    (f : OnBytes.Attention.PW → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a : OnBytes.Attention.PW), Over.K (f a)) :
    Over.K (OnBytes.Attention.lessPieces start pw f) := by
  keeps

theorem KeepsOf.OnBytes.Attention.lng (S : OnBytes.Attention.Shape)
    (zc : Array OnBytes.E) (ptk : Unit → Array OnBytes.E) :
    Over.K (OnBytes.Attention.lng S zc ptk) := by
  keeps

theorem KeepsOf.OnBytes.Attention.noFreeSlot (nMsg : Nat) :
    Over.K (OnBytes.Attention.noFreeSlot nMsg) := by
  keeps

theorem KeepsOf.OnBytes.Attention.paddingLaid (S : OnBytes.Attention.Shape)
    (g : OnBytes.Model.Forest.Heard) : Over.K (OnBytes.Attention.paddingLaid S g) := by
  keeps

theorem KeepsOf.OnBytes.Attention.productIn (S : OnBytes.Attention.Shape)
    (pwW : Array OnBytes.Attention.PW) (zgW ziW : Array OnBytes.E) (sZO : Nat) :
    Over.K (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by
  keeps

theorem KeepsOf.OnBytes.Attention.scdIn (degrees : List Nat) (degreeInY n : Nat)
    (start : OnBytes.Model.Aff) :
    Over.K (OnBytes.Attention.scdIn degrees degreeInY n start) := by
  keeps

theorem KeepsOf.OnBytes.Attention.scdRow (o : OnBytes.Attention.Scd) (s0 : OnBytes.E) :
    Over.K (OnBytes.Attention.scdRow o s0) := by
  keeps

theorem KeepsOf.OnBytes.Attention.scoreAtIndexIn (S : OnBytes.Attention.Shape)
    (tg ti : Array OnBytes.E) : Over.K (OnBytes.Attention.scoreAtIndexIn S tg ti) := by
  keeps

theorem KeepsOf.OnBytes.Attention.scores (S : OnBytes.Attention.Shape)
    (zk : Array (Array OnBytes.E)) : Over.K (OnBytes.Attention.scores S zk) := by
  keeps

theorem KeepsOf.OnBytes.Attention.valueBelowIn (S : OnBytes.Attention.Shape)
    (pwW : Array OnBytes.Attention.PW) (zgW zihi : Array OnBytes.E) (sCl : Nat) :
    Over.K (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by
  keeps

theorem KeepsOf.OnBytes.Attention.valueOnIn (S : OnBytes.Attention.Shape)
    (pwW : Array OnBytes.Attention.PW) (zgW zihi : Array OnBytes.E) (sCl1 : Nat) :
    Over.K (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by
  keeps

theorem KeepsOf.OnBytes.Attention.weighted (n : Nat) (w : Array OnBytes.E)
    (f : Nat → OnBytes.Model.SubM OnBytes.Model.Aff) (h : ∀ (a : Nat), Over.K (f a)) :
    Over.K (OnBytes.Attention.weighted n w f) := by
  keeps

theorem KeepsOf.OnBytes.Model.Forest.join (g : OnBytes.Model.Forest.Heard)
    (KF : Array OnBytes.Model.Aff) : Over.K (OnBytes.Model.Forest.join g KF) := by
  keeps

theorem KeepsOf.OnBytes.Model.uEnt (t x : Nat) :
    Over.K (OnBytes.Model.uEnt t x) := by
  keeps

theorem KeepsOf.OnBytes.Attention.addLong (S : OnBytes.Attention.Shape)
    (mats : Array OnBytes.Model.TMat) (mat : Nat) (zc : Array OnBytes.E)
    (ptk : Unit → Array OnBytes.E) (elems : Nat) :
    Over.K (OnBytes.Attention.addLong S mats mat zc ptk elems) := by
  keeps

theorem KeepsOf.OnBytes.Attention.bitsIn (S : OnBytes.Attention.Shape)
    (tk tbg tbi : Array OnBytes.E) : Over.K (OnBytes.Attention.bitsIn S tk tbg tbi) := by
  keeps

theorem KeepsOf.OnBytes.Attention.divide (S : OnBytes.Attention.Shape)
    (zk : Array (Array OnBytes.E)) : Over.K (OnBytes.Attention.divide S zk) := by
  keeps

theorem KeepsOf.OnBytes.Attention.keyAtIndexIn (S : OnBytes.Attention.Shape)
    (scF : OnBytes.Attention.Sc3) : Over.K (OnBytes.Attention.keyAtIndexIn S scF) := by
  keeps

theorem KeepsOf.OnBytes.Attention.overG (h : OnBytes.Attention.Heard)
    (zg : Array OnBytes.E) (f : Nat → OnBytes.Model.SubM OnBytes.Model.Aff) :
    (∀ (a : Nat), Over.K (f a)) →
      Over.K (OnBytes.Attention.overG h zg f) := by
  keeps

theorem KeepsOf.OnBytes.Attention.placeAll (S : OnBytes.Attention.Shape)
    (mats : Array OnBytes.Model.TMat) (nW : Nat) (g : OnBytes.Model.Forest.Heard)
    (planes : Array OnBytes.Attention.PlaneClaim) (scores : Array OnBytes.Attention.Score)
    (d : OnBytes.Attention.Divide) (x : OnBytes.Attention.Attain) :
    Over.K (OnBytes.Attention.placeAll S mats nW g planes scores d x) := by
  keeps

theorem KeepsOf.OnBytes.Attention.tables (S : OnBytes.Attention.Shape)
    (mats : Array OnBytes.Model.TMat) (nW : Nat) (g : OnBytes.Model.Forest.Heard)
    (planes : Array OnBytes.Attention.PlaneClaim) (scores : Array OnBytes.Attention.Score)
    (d : OnBytes.Attention.Divide) (x : OnBytes.Attention.Attain) :
    Over.K (OnBytes.Attention.tables S mats nW g planes scores d x) := by
  keeps

theorem KeepsOf.OnBytes.Attention.u3at (h : OnBytes.Attention.Heard) (t i : Nat) :
    Over.K (OnBytes.Attention.u3at h t i) := by
  keeps

theorem KeepsOf.OnBytes.Attention.xl (h : OnBytes.Attention.Heard) (t : Nat)
    (X : OnBytes.Model.TenAt) (lam hd : Nat) (zc : Array OnBytes.E) :
    Over.K (OnBytes.Attention.xl h t X lam hd zc) := by
  keeps

theorem KeepsOf.OnBytes.Attention.attain (S : OnBytes.Attention.Shape) :
    Over.K (OnBytes.Attention.attain S) := by
  keeps

theorem KeepsOf.OnBytes.Attention.hear (P : OnBytes.Attention.Plan) :
    Over.K (OnBytes.Attention.hear P) := by
  keeps

theorem KeepsOf.OnBytes.Attention.plane (h : OnBytes.Attention.Heard) (t x lam a : Nat)
    (z : Array OnBytes.E) (isD : Bool) :
    Over.K (OnBytes.Attention.plane h t x lam a z isD) := by
  keeps

theorem KeepsOf.OnBytes.Attention.readGroup (h : OnBytes.Attention.Heard) (t : Nat)
    (X : OnBytes.Model.TenAt) (zg zc : Array OnBytes.E) (lam : Nat) :
    Over.K (OnBytes.Attention.readGroup h t X zg zc lam) := by
  keeps

theorem KeepsOf.OnBytes.Attention.readHead (h : OnBytes.Attention.Heard) (t : Nat)
    (X : OnBytes.Model.TenAt) (zg zc : Array OnBytes.E) (lam a : Nat) :
    Over.K (OnBytes.Attention.readHead h t X zg zc lam a) := by
  keeps

theorem KeepsOf.OnBytes.Attention.shV (h : OnBytes.Attention.Heard)
    (t off nl J lam j : Nat) : Over.K (OnBytes.Attention.shV h t off nl J lam j) := by
  keeps

theorem KeepsOf.OnBytes.Attention.valueProduct (h : OnBytes.Attention.Heard)
    (sc : OnBytes.Attention.Sc3) (tS : Nat) (pt : Array OnBytes.E) (isD : Bool) (tV : Nat) :
    Over.K (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim6 (h : OnBytes.Attention.Heard) :
    Over.K (OnBytes.Attention.claim6 h) := by
  keeps

theorem KeepsOf.OnBytes.Attention.endValues (h : OnBytes.Attention.Heard)
    (k : OnBytes.Attention.Score) (tb : OnBytes.Attention.ScoreTables) (rc : Array OnBytes.E)
    (b : Nat) (w : OnBytes.Attention.PW) :
    Over.K (OnBytes.Attention.endValues h k tb rc b w) := by
  keeps

theorem KeepsOf.OnBytes.Attention.linPlanes (h : OnBytes.Attention.Heard)
    (pc : OnBytes.Attention.PlaneClaim) : Over.K (OnBytes.Attention.linPlanes h pc) := by
  keeps

theorem KeepsOf.OnBytes.Attention.readDenominator (h : OnBytes.Attention.Heard)
    (t : Nat) (zg : Array OnBytes.E) (lam a : Nat) :
    Over.K (OnBytes.Attention.readDenominator h t zg lam a) := by
  keeps

theorem KeepsOf.OnBytes.Attention.readIndexBit (h : OnBytes.Attention.Heard) (t : Nat)
    (zg : Array OnBytes.E) (lam a k : Nat) :
    Over.K (OnBytes.Attention.readIndexBit h t zg lam a k) := by
  keeps

theorem KeepsOf.OnBytes.Attention.readMaximum (h : OnBytes.Attention.Heard) (t : Nat)
    (zg : Array OnBytes.E) (lam a : Nat) :
    Over.K (OnBytes.Attention.readMaximum h t zg lam a) := by
  keeps

theorem KeepsOf.OnBytes.Attention.unitKFD (h : OnBytes.Attention.Heard) (i : Nat)
    (k : OnBytes.Attention.Score) : Over.K (OnBytes.Attention.unitKFD h i k) := by
  keeps

theorem KeepsOf.OnBytes.Attention.callKFD (h : OnBytes.Attention.Heard) (q : Nat)
    (c : OnBytes.Attention.ACall) : Over.K (OnBytes.Attention.callKFD h q c) := by
  keeps

theorem KeepsOf.OnBytes.Attention.callKR (h : OnBytes.Attention.Heard) (q : Nat) :
    Over.K (OnBytes.Attention.callKR h q) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim3 (h : OnBytes.Attention.Heard)
    (j : OnBytes.Attention.Joins) : Over.K (OnBytes.Attention.claim3 h j) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim4 (h : OnBytes.Attention.Heard)
    (j : OnBytes.Attention.Joins) : Over.K (OnBytes.Attention.claim4 h j) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim7 (h : OnBytes.Attention.Heard) :
    Over.K (OnBytes.Attention.claim7 h) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim8 (h : OnBytes.Attention.Heard) :
    Over.K (OnBytes.Attention.claim8 h) := by
  keeps

theorem KeepsOf.OnBytes.Attention.endValuesE (h : OnBytes.Attention.Heard) (b : Nat)
    (w : OnBytes.Attention.PW) : Over.K (OnBytes.Attention.endValuesE h b w) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claim5 (h : OnBytes.Attention.Heard)
    (j : OnBytes.Attention.Joins) : Over.K (OnBytes.Attention.claim5 h j) := by
  keeps

theorem KeepsOf.OnBytes.Attention.claims (P : OnBytes.Attention.Plan)
    (h : OnBytes.Attention.Heard) : Over.K (OnBytes.Attention.claims P h) := by
  keeps

theorem KeepsOf.OnBytes.Attention.run (P : OnBytes.Attention.Plan) :
    Over.K (OnBytes.Attention.run P) := by
  keeps

/-! ### `OnBytes.Model.Head.runForkHidH2`, and what its text reaches -/

theorem KeepsOf.OnBytes.Model.Head.U3at (R : OnBytes.Model.Head.Run) (t i : Nat) :
    Over.K (OnBytes.Model.Head.U3at R t i) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.getAs {α : Type} (name : String) (x : Option α) :
    Over.K (OnBytes.Model.Head.getAs name x) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.hearLogits (h : OnBytes.Model.Head.Shape)
    (lam : Nat) (zt : Array OnBytes.E) :
    Over.K (OnBytes.Model.Head.hearLogits h lam zt) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.hearSquares (h : OnBytes.Model.Head.Shape)
    (PV : Array OnBytes.E) : Over.K (OnBytes.Model.Head.hearSquares h PV) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.hearStream (h : OnBytes.Model.Head.Shape)
    (zt : Array OnBytes.E) : Over.K (OnBytes.Model.Head.hearStream h zt) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.held {α : Type} (x : Except String α) :
    Over.K (OnBytes.Model.Head.held x) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.mergedPoint (h : OnBytes.Model.Head.Shape)
    (g1 : OnBytes.Model.Forest.Heard) :
    Over.K (OnBytes.Model.Head.mergedPoint h g1) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.noteH (what : String) (value : OnBytes.E) :
    Over.K (OnBytes.Model.Head.noteH what value) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.replyToken (plain : Array OnBytes.E) (V : Nat) :
    Over.K (OnBytes.Model.Head.replyToken plain V) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.segOf (R : OnBytes.Model.Head.Run) (sn : String) :
    Over.K (OnBytes.Model.Head.segOf R sn) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.selfTests (R : OnBytes.Model.Head.Run)
    (tl : OnBytes.Model.HTailF2) (wo : OnBytes.Model.WsForkOut) :
    Over.K (OnBytes.Model.Head.selfTests R tl wo) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.sh2 (R : OnBytes.Model.Head.Run) (t j : Nat) :
    Over.K (OnBytes.Model.Head.sh2 R t j) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.shownRun (first n : Nat) :
    Over.K (OnBytes.Model.Head.shownRun first n) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.tabAt (R : OnBytes.Model.Head.Run) (n : String) :
    Over.K (OnBytes.Model.Head.tabAt R n) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.tablesOf (h : OnBytes.Model.Head.Shape)
    (L : OnBytes.Model.Head.HL) (hp : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered)
    (x : OnBytes.Model.Head.Heard) :
    Over.K (OnBytes.Model.Head.tablesOf h L hp cov x) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.xbA (R : OnBytes.Model.Head.Run) (t kh : Nat) :
    Over.K (OnBytes.Model.Head.xbA R t kh) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.ztSeg (R : OnBytes.Model.Head.Run) (sn : String) :
    Over.K (OnBytes.Model.Head.ztSeg R sn) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.slots (n : Nat) :
    Over.K (OnBytes.Model.SubM.slots n) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimLogits (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimLogits R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimPlanes (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimPlanes R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimSquares (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimSquares R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.ewOf (R : OnBytes.Model.Head.Run) (sn : String) :
    Over.K (OnBytes.Model.Head.ewOf R sn) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.ewh (R : OnBytes.Model.Head.Run) (sn : String) :
    Over.K (OnBytes.Model.Head.ewh R sn) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.gapAt (R : OnBytes.Model.Head.Run) (P : String)
    (i : Nat) (wsum : OnBytes.E) : Over.K (OnBytes.Model.Head.gapAt R P i wsum) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.hearProducts (h : OnBytes.Model.Head.Shape)
    (PV : Array OnBytes.E) : Over.K (OnBytes.Model.Head.hearProducts h PV) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.noteConstant (group : String) :
    Over.K (OnBytes.Model.Head.noteConstant group) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.row5At (R : OnBytes.Model.Head.Run) (P : String) :
    Over.K (OnBytes.Model.Head.row5At R P) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.rowAt (R : OnBytes.Model.Head.Run) (P : String) :
    Over.K (OnBytes.Model.Head.rowAt R P) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.weightsClaim (R : OnBytes.Model.Head.Run)
    (wsLay : OnBytes.Model.WsLay) :
    Over.K (OnBytes.Model.Head.weightsClaim R wsLay) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.Sl (R : OnBytes.Model.Head.Run) (sn : String)
    (OFF nl J : Nat) : Over.K (OnBytes.Model.Head.Sl R sn OFF nl J) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimLedger4 (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimLedger4 R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimLedger5 (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimLedger5 R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimPolicy (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimPolicy R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimStream (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimStream R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.hear (h : OnBytes.Model.Head.Shape)
    (L : OnBytes.Model.Head.HL) (hp : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered)
    (plain : Array OnBytes.E) : Over.K (OnBytes.Model.Head.hear h L hp cov plain) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.lowDigit (R : OnBytes.Model.Head.Run) (sn : String)
    (wR : OnBytes.E) : Over.K (OnBytes.Model.Head.lowDigit R sn wR) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.middleDigit (R : OnBytes.Model.Head.Run)
    (sn : String) (wR : OnBytes.E) :
    Over.K (OnBytes.Model.Head.middleDigit R sn wR) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.LINE (R : OnBytes.Model.Head.Run) (sn : String) :
    Over.K (OnBytes.Model.Head.LINE R sn) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimLedger (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimLedger R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.keyForm (R : OnBytes.Model.Head.Run) (q : Nat)
    (laid : Array Nat) : Over.K (OnBytes.Model.Head.keyForm R q laid) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.claimJoin (R : OnBytes.Model.Head.Run) :
    Over.K (OnBytes.Model.Head.claimJoin R) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.walk (R : OnBytes.Model.Head.Run)
    (tl : OnBytes.Model.HTailF2) (wo : OnBytes.Model.WsForkOut) :
    Over.K (OnBytes.Model.Head.walk R tl wo) := by
  keeps

theorem KeepsOf.OnBytes.Model.Head.runForkHidH2 (h : OnBytes.Model.Head.Shape)
    (L : OnBytes.Model.Head.HL) (b : OnBytes.Model.Head.Border) (hp : OnBytes.Model.Head.HPlanH2)
    (O : OnBytes.Model.Head.Owner) (cov : OnBytes.Model.Head.Covered)
    (wsLay : OnBytes.Model.WsLay) :
    Over.K (OnBytes.Model.Head.runForkHidH2 h L b hp O cov wsLay) := by
  keeps

/-! ### `OnBytes.Model.ChainCheck.start`, and what its text reaches -/

theorem KeepsOf.OnBytes.ReqFrame.start (shape : OnBytes.Params.ReqShape) :
    Over.K (OnBytes.ReqFrame.start shape) := by
  keeps

theorem KeepsOf.OnBytes.ReqRows.make (shape : OnBytes.Params.ReqShape)
    (layout : OnBytes.Params.ReqLayout) :
    Over.K (OnBytes.ReqRows.make shape layout) := by
  keeps

theorem KeepsOf.OnBytes.Model.ChainCheck.start (shape : OnBytes.Params.ReqShape)
    (layout : OnBytes.Params.ReqLayout) :
    Over.K (OnBytes.Model.ChainCheck.start shape layout) := by
  keeps

/-! ### `OnBytes.Model.ChainCheck.first`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.recvEs (count : Nat) :
    Over.K (OnBytes.Blk.recvEs count) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.beginLink (f : OnBytes.ReqFrame) :
    Over.K f.beginLink := by
  keeps

theorem KeepsOf.OnBytes.csSigmaVerify (old : OnBytes.SingleRows)
    (T : OnBytes.SwitchTarget) (to : Nat) (others : Array OnBytes.OracleNotice) :
    Over.K (OnBytes.csSigmaVerify old T to others) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.first (f : OnBytes.ReqFrame) :
    Over.K f.first := by
  keeps

theorem KeepsOf.OnBytes.Model.ChainCheck.first (c : OnBytes.Model.ChainCheck) :
    Over.K c.first := by
  keeps

/-! ### `OnBytes.Model.ChainCheck.finish`, and what its text reaches -/

theorem KeepsOf.OnBytes.ioppVerify (g : Nat) (stages : List OnBytes.Params.IoppStage)
    (choice : OnBytes.Params.IoppChoice) (firstMask : Option Nat := Option.none) :
    Over.K (OnBytes.ioppVerify g stages choice firstMask) := by
  keeps

theorem KeepsOf.OnBytes.ReqFrame.finish (f : OnBytes.ReqFrame) :
    Over.K f.finish := by
  keeps

theorem KeepsOf.OnBytes.Model.ChainCheck.finish (c : OnBytes.Model.ChainCheck) :
    Over.K c.finish := by
  keeps

/-! ### `OnBytes.Model.Stages.pendingRowH`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.takeMask (o : Nat) :
    Over.K (OnBytes.Blk.takeMask o) := by
  keeps

theorem KeepsOf.OnBytes.Model.Stages.pendingRowH (wsLay : OnBytes.Model.WsLay)
    (indexMasks : Nat) (o : OnBytes.Model.WsForkOut) (claims : Nat) (S : OnBytes.Params.LinShape) :
    Over.K (OnBytes.Model.Stages.pendingRowH wsLay indexMasks o claims S) := by
  keeps

/-! ### `OnBytes.Model.Stages.indexMasksH`, and what its text reaches -/

theorem KeepsOf.OnBytes.Model.Stages.indexMasksH
    (links : Array OnBytes.Model.Stages.LinkH) (p : OnBytes.Params.First)
    (check : OnBytes.Model.ChainCheck) :
    Over.K (OnBytes.Model.Stages.indexMasksH links p check) := by
  keeps

end OnBytes.Flat
