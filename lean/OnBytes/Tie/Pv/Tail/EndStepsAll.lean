-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndStepsAll.lean: the routines of the masked sumchecks, of the lookup, of the
attention sub-proof and of a layer group's sub-proof, and the hearing of the smallness test, keep
every relation that holds across each basic step (`Steps`, OnBytes/Tie/Pv/Tail/EndSteps.lean).

Theorems with their proofs, each by a walk through a routine's text. The statements and proofs are
those of OnBytes/Tie/Pv/Tail/EndWalkLook.lean, EndWalkTail.lean, EndWalkAtt.lean, EndWalkHead.lean
and EndWalkLayer.lean, with the class replaced.

Main names: `stp_` or `stpL_` and a routine's name.

Limits: those of OnBytes/Tie/Pv/Tail/EndSteps.lean. objectsF and the routines behind it, t2Batch and
the routines that set up a sub-proof's state are not here.


-/
import OnBytes.Model.Attention
import OnBytes.Model.Layer
import OnBytes.Tie.Pv.Tail.EndSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.StepsW
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

open OnBytes.Model in
/-- `pscBeginAt` keeps R. -/
instance stp_Model_pscBeginAt [Steps R] (target : E) :
    Stp R (OnBytes.Model.pscBeginAt target) := by
  unfold OnBytes.Model.pscBeginAt
  stp

open OnBytes.Model in
/-- `pscBegin` keeps R. -/
instance stp_Model_pscBegin [Steps R] (C : Aff) :
    Stp R (OnBytes.Model.pscBegin C) := by
  unfold OnBytes.Model.pscBegin
  stp

open OnBytes.Model in
/-- `pscRound` keeps R. -/
instance stp_Model_pscRound [Steps R] (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) :
    Stp R (OnBytes.Model.pscRound p w draw) := by
  unfold OnBytes.Model.pscRound
  stp

open OnBytes.Model in
/-- `roundIn` keeps R. -/
instance stp_Model_roundIn [Steps R] (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Stp R (OnBytes.Model.roundIn form p z degree) := by
  unfold OnBytes.Model.roundIn
  stp

open OnBytes.Model in
/-- `pscEnds` keeps R. -/
instance stp_Model_pscEnds [Steps R] (p : Psc) (degreeInY n : Nat) :
    Stp R (OnBytes.Model.pscEnds p degreeInY n) := by
  unfold OnBytes.Model.pscEnds
  stp

open OnBytes.Model in
/-- `pscRow` keeps R. -/
instance stp_Model_pscRow [Steps R] (p : Psc) (S0 : E) (kept : Aff) :
    Stp R (OnBytes.Model.pscRow p S0 kept) := by
  unfold OnBytes.Model.pscRow
  stp

/-- `levelRounds` keeps R. -/
instance stp_Model_levelRounds [Steps R] (mu : Nat) (rho : Array E) :
    ∀ (l : List Nat) (r : Array E) (p : Psc), Stp R (OnBytes.Model.levelRounds mu rho l r p)
  | [], r, p => by
    unfold OnBytes.Model.levelRounds
    stp
  | t :: l, r, p => by
    have := stp_Model_levelRounds mu rho l
    unfold OnBytes.Model.levelRounds
    stp

open OnBytes.Model in
/-- `levelIn` keeps R. -/
instance stp_Model_levelIn [Steps R] (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Stp R (OnBytes.Model.levelIn mu rho C order) := by
  unfold OnBytes.Model.levelIn
  stp

open OnBytes.Model in
/-- `layerObject` keeps R. -/
instance stp_Model_layerObject [Steps R] (o : Level) :
    Stp R (OnBytes.Model.layerObject o) := by
  unfold OnBytes.Model.layerObject
  stp

open OnBytes.Model in
/-- `uEnt` keeps R. -/
instance stp_Model_uEnt [Steps R] (t x : Nat) :
    Stp R (OnBytes.Model.uEnt t x) := by
  unfold OnBytes.Model.uEnt
  stp

open OnBytes.Model in
/-- `roundsIn` keeps R. -/
instance stp_Model_roundsIn [Steps R] (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Stp R (OnBytes.Model.roundsIn form p zs) := by
  unfold OnBytes.Model.roundsIn
  stp

open OnBytes.Model in
/-- `stackRounds` keeps R. -/
instance stp_Model_stackRounds [Steps R] (st : Stack) :
    Stp R (OnBytes.Model.stackRounds st) := by
  unfold OnBytes.Model.stackRounds
  stp

open OnBytes.Model.Forest in
/-- `Forest.draws` keeps R. -/
instance stp_Model_Forest_draws [Steps R] (h : Shape) :
    Stp R (OnBytes.Model.Forest.draws h) := by
  unfold OnBytes.Model.Forest.draws
  stp

open OnBytes.Model.Forest in
/-- `Forest.tieStep` keeps R. -/
instance stp_Model_Forest_tieStep [Steps R] (a : E) (s : TieStep) (j : Nat) :
    Stp R (OnBytes.Model.Forest.tieStep a s j) := by
  unfold OnBytes.Model.Forest.tieStep
  stp

open OnBytes.Model.Forest in
/-- `Forest.tie` keeps R. -/
instance stp_Model_Forest_tie [Steps R] (a : E) :
    Stp R (OnBytes.Model.Forest.tie a) := by
  unfold OnBytes.Model.Forest.tie
  stp

open OnBytes.Model.Forest in
/-- `Forest.level` keeps R. -/
instance stp_Model_Forest_level [Steps R] (s : Descent) (mu : Nat) (order : List Nat) :
    Stp R (OnBytes.Model.Forest.level s mu order) := by
  unfold OnBytes.Model.Forest.level
  stp

open OnBytes.Model.Forest in
/-- `Forest.pad` keeps R. -/
instance stp_Model_Forest_pad [Steps R] (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    Stp R (OnBytes.Model.Forest.pad calls pub lid) := by
  unfold OnBytes.Model.Forest.pad
  stp

open OnBytes.Model.Forest in
/-- `Forest.objects` keeps R. -/
instance stp_Model_Forest_objects [Steps R] (g : Heard) :
    Stp R (OnBytes.Model.Forest.objects g) := by
  unfold OnBytes.Model.Forest.objects
  stp

open OnBytes.Model.Forest in
/-- `Forest.planesAdded` keeps R. -/
instance stp_Model_Forest_planesAdded [Steps R] (g : Heard) :
    Stp R (OnBytes.Model.Forest.planesAdded g) := by
  unfold OnBytes.Model.Forest.planesAdded
  stp

open OnBytes.Model.Forest in
/-- `Forest.joinAdded` keeps R. -/
instance stp_Model_Forest_joinAdded [Steps R] (g : Heard) :
    Stp R (OnBytes.Model.Forest.joinAdded g) := by
  unfold OnBytes.Model.Forest.joinAdded
  stp

open OnBytes.Model.Forest in
/-- `Forest.paddingLaid` keeps R. -/
instance stp_Model_Forest_paddingLaid [Steps R] (g : Heard) (laid : Array Nat) :
    Stp R (OnBytes.Model.Forest.paddingLaid g laid) := by
  unfold OnBytes.Model.Forest.paddingLaid
  stp

open OnBytes.Model.Forest in
/-- `Forest.join` keeps R. -/
instance stp_Model_Forest_join [Steps R] (g : Heard) (KF : Array Aff) :
    Stp R (OnBytes.Model.Forest.join g KF) := by
  unfold OnBytes.Model.Forest.join
  stp

open OnBytes.Model.Forest in
/-- `Forest.planesAt` keeps R. -/
instance stp_Model_Forest_planesAt [Steps R] (g : Heard) (lm e : Nat) (bit : Nat → Nat → SubM Aff)
    [∀ x0 x1, Stp R (bit x0 x1)] :
    Stp R (OnBytes.Model.Forest.planesAt g lm e bit) := by
  unfold OnBytes.Model.Forest.planesAt
  stp

open OnBytes.Model.Forest in
/-- `Forest.planeClaims` keeps R. -/
instance stp_Model_Forest_planeClaims [Steps R] (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [∀ x0 x1, Stp R (bit x0 x1)] [∀ x0, Stp R (pin x0)] :
    Stp R (OnBytes.Model.Forest.planeClaims g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeClaims
  stp

open OnBytes.Model.Forest in
/-- `Forest.planeLins` keeps R. -/
instance stp_Model_Forest_planeLins [Steps R] (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [∀ x0 x1, Stp R (bit x0 x1)] [∀ x0, Stp R (pin x0)] :
    Stp R (OnBytes.Model.Forest.planeLins g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeLins
  stp

/-! ## The hearing of the smallness test -/

open OnBytes.Model.HTailF2 in
/-- `HTailF2.drawMatrixF` keeps R. -/
instance stp_Model_HTailF2_drawMatrixF [Steps R] (tl : HTailF2) :
    Stp R (OnBytes.Model.HTailF2.drawMatrixF tl) := by
  unfold OnBytes.Model.HTailF2.drawMatrixF
  stp

/-- `rootInH` keeps R. -/
instance stpL_Model_rootInH [Steps R] (trees : List Nat) :
    StpL R (OnBytes.Model.rootInH trees) := by
  unfold OnBytes.Model.rootInH
  stpL

/-- `HTailF2.fixedBeforeTheMatrixF` keeps R. -/
instance stpL_Model_HTailF2_fixedBeforeTheMatrixF [Steps R] (tl : HTailF2) :
    StpL R (OnBytes.Model.HTailF2.fixedBeforeTheMatrixF tl) := by
  unfold OnBytes.Model.HTailF2.fixedBeforeTheMatrixF
  stpL

/-- `HTailF2.transcriptF` keeps R. -/
instance stpL_Model_HTailF2_transcriptF [Steps R] (tl : HTailF2) :
    StpL R (OnBytes.Model.HTailF2.transcriptF tl) := by
  unfold OnBytes.Model.HTailF2.transcriptF
  stpL

/-! ## OnBytes/Model/Tsc.lean, Merge.lean -/

open OnBytes.Model in
/-- `tscLoop` keeps R. -/
instance stp_Model_tscLoop [Steps R] :
    ∀ (zs : List E) (r : Array E) (p : Psc), Stp R (OnBytes.Model.tscLoop zs r p)
  | [], r, p => by
    unfold OnBytes.Model.tscLoop
    stp
  | z :: zs, r, p => by
    have := stp_Model_tscLoop zs
    unfold OnBytes.Model.tscLoop
    stp

open OnBytes.Model in
/-- `tscRounds` keeps R. -/
instance stp_Model_tscRounds [Steps R] (P : Array E) (lt : Nat) :
    Stp R (OnBytes.Model.tscRounds P lt) := by
  unfold OnBytes.Model.tscRounds
  stp

open OnBytes.Model in
/-- `tscIn` keeps R. -/
instance stp_Model_tscIn [Steps R] (P : Array E) (lt shown degreeInY : Nat) :
    Stp R (OnBytes.Model.tscIn P lt shown degreeInY) := by
  unfold OnBytes.Model.tscIn
  stp

open OnBytes.Model in
/-- `wsForkRounds` keeps R. -/
instance stp_Model_wsForkRounds [Steps R] :
    ∀ (n : Nat) (rm : Array E) (p : Psc), Stp R (OnBytes.Model.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold OnBytes.Model.wsForkRounds
    stp
  | n + 1, rm, p => by
    have := stp_Model_wsForkRounds n
    unfold OnBytes.Model.wsForkRounds
    stp

open OnBytes.Model in
/-- `wsForkMerge` keeps R. -/
instance stp_Model_wsForkMerge [Steps R] (lk : Nat) (sv : Array Nat) :
    Stp R (OnBytes.Model.wsForkMerge lk sv) := by
  unfold OnBytes.Model.wsForkMerge
  stp

open OnBytes.Model in
/-- `wsForkLin` keeps R. -/
instance stp_Model_wsForkLin [Steps R] (o : WsMerged) :
    Stp R (OnBytes.Model.wsForkLin o) := by
  unfold OnBytes.Model.wsForkLin
  stp

open OnBytes.Model in
/-- `wsForkEnd` keeps R. -/
instance stp_Model_wsForkEnd [Steps R] (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Stp R (OnBytes.Model.wsForkEnd lay cl sv) := by
  unfold OnBytes.Model.wsForkEnd
  stp

/-! ## OnBytes/Model/AttentionSums.lean -/

open OnBytes.Attention in
/-- `Attention.sc3Rounds` keeps R. -/
instance stp_Attention_sc3Rounds [Steps R] :
    ∀ (n : Nat) (p : Psc) (r : Array E), Stp R (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r => by
    unfold OnBytes.Attention.sc3Rounds
    stp
  | n + 1, p, r => by
    have := stp_Attention_sc3Rounds n
    unfold OnBytes.Attention.sc3Rounds
    stp

open OnBytes.Attention in
/-- `Attention.sc3In` keeps R. -/
instance stp_Attention_sc3In [Steps R] (nv nb : Nat) (start : Model.Aff) :
    Stp R (OnBytes.Attention.sc3In nv nb start) := by
  unfold OnBytes.Attention.sc3In
  stp

open OnBytes.Attention in
/-- `Attention.sc3Shown` keeps R. -/
instance stp_Attention_sc3Shown [Steps R] (o : Sc3) (W : Array E) :
    ∀ (n b : Nat) (s : E), Stp R (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    unfold OnBytes.Attention.sc3Shown
    stp
  | n + 1, b, s => by
    have := stp_Attention_sc3Shown o W n
    unfold OnBytes.Attention.sc3Shown
    stp

open OnBytes.Attention in
/-- `Attention.sc3Row` keeps R. -/
instance stp_Attention_sc3Row [Steps R] (o : Sc3) (W : Array E) :
    Stp R (OnBytes.Attention.sc3Row o W) := by
  unfold OnBytes.Attention.sc3Row
  stp

open OnBytes.Attention in
/-- `Attention.scdRounds` keeps R. -/
instance stp_Attention_scdRounds [Steps R] :
    ∀ (ds : List Nat) (p : Psc) (r : Array E), Stp R (OnBytes.Attention.scdRounds ds p r)
  | [], p, r => by
    unfold OnBytes.Attention.scdRounds
    stp
  | d :: ds, p, r => by
    have := stp_Attention_scdRounds ds
    unfold OnBytes.Attention.scdRounds
    stp

open OnBytes.Attention in
/-- `Attention.scdIn` keeps R. -/
instance stp_Attention_scdIn [Steps R] (degrees : List Nat) (degreeInY n : Nat)
    (start : Model.Aff) :
    Stp R (OnBytes.Attention.scdIn degrees degreeInY n start) := by
  unfold OnBytes.Attention.scdIn
  stp

open OnBytes.Attention in
/-- `Attention.scdRow` keeps R. -/
instance stp_Attention_scdRow [Steps R] (o : Scd) (s0 : E) :
    Stp R (OnBytes.Attention.scdRow o s0) := by
  unfold OnBytes.Attention.scdRow
  stp

/-! ## OnBytes/Model/AttentionScores.lean -/

open OnBytes.Attention in
/-- `Attention.planeUnit` keeps R. -/
instance stp_Attention_planeUnit [Steps R] (S : Shape) (zk : Array (Array E))
    (u : Nat × ACall × OnBytes.Attention.Seg) :
    Stp R (OnBytes.Attention.planeUnit S zk u) := by
  unfold OnBytes.Attention.planeUnit
  stp

open OnBytes.Attention in
/-- `Attention.planeUnits` keeps R. -/
instance stp_Attention_planeUnits [Steps R] (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × OnBytes.Attention.Seg)) (planes : Array PlaneClaim),
      Stp R (OnBytes.Attention.planeUnits S zk us planes)
  | [], planes => by
    unfold OnBytes.Attention.planeUnits
    stp
  | u :: us, planes => by
    have := stp_Attention_planeUnits S zk us
    unfold OnBytes.Attention.planeUnits
    stp

open OnBytes.Attention in
/-- `Attention.scoreUnit` keeps R. -/
instance stp_Attention_scoreUnit [Steps R] (S : Shape) (zk : Array (Array E)) (claim : Nat)
    (u : Nat × ACall × OnBytes.Attention.Seg) :
    Stp R (OnBytes.Attention.scoreUnit S zk claim u) := by
  unfold OnBytes.Attention.scoreUnit
  stp

open OnBytes.Attention in
/-- `Attention.scoreUnits` keeps R. -/
instance stp_Attention_scoreUnits [Steps R] (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × OnBytes.Attention.Seg)) (planes : Array PlaneClaim)
      (stored : Array Score),
      Stp R (OnBytes.Attention.scoreUnits S zk us planes stored)
  | [], planes, stored => by
    unfold OnBytes.Attention.scoreUnits
    stp
  | u :: us, planes, stored => by
    have := stp_Attention_scoreUnits S zk us
    unfold OnBytes.Attention.scoreUnits
    stp

open OnBytes.Attention in
/-- `Attention.scores` keeps R. -/
instance stp_Attention_scores [Steps R] (S : Shape) (zk : Array (Array E)) :
    Stp R (OnBytes.Attention.scores S zk) := by
  unfold OnBytes.Attention.scores
  stp

/-! ## OnBytes/Model/AttentionDivide.lean -/

open OnBytes.Attention in
/-- `Attention.coinsOm` keeps R. -/
instance stp_Attention_coinsOm [Steps R] (n : Nat) :
    Stp R (OnBytes.Attention.coinsOm n) := by
  unfold OnBytes.Attention.coinsOm
  stp

open OnBytes.Attention in
/-- `Attention.productIn` keeps R. -/
instance stp_Attention_productIn [Steps R] (S : Shape) (pwW : Array PW) (zgW ziW : Array E)
    (sZO : Nat) :
    Stp R (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by
  unfold OnBytes.Attention.productIn
  stp

open OnBytes.Attention in
/-- `Attention.valueBelowIn` keeps R. -/
instance stp_Attention_valueBelowIn [Steps R] (S : Shape) (pwW : Array PW) (zgW zihi : Array E)
    (sCl : Nat) :
    Stp R (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by
  unfold OnBytes.Attention.valueBelowIn
  stp

open OnBytes.Attention in
/-- `Attention.valueOnIn` keeps R. -/
instance stp_Attention_valueOnIn [Steps R] (S : Shape) (pwW : Array PW) (zgW zihi : Array E)
    (sCl1 : Nat) :
    Stp R (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by
  unfold OnBytes.Attention.valueOnIn
  stp

open OnBytes.Attention in
/-- `Attention.divide` keeps R. -/
instance stp_Attention_divide [Steps R] (S : Shape) (zk : Array (Array E)) :
    Stp R (OnBytes.Attention.divide S zk) := by
  unfold OnBytes.Attention.divide
  stp

open OnBytes.Attention in
/-- `Attention.scoreAtIndexIn` keeps R. -/
instance stp_Attention_scoreAtIndexIn [Steps R] (S : Shape) (tg ti : Array E) :
    Stp R (OnBytes.Attention.scoreAtIndexIn S tg ti) := by
  unfold OnBytes.Attention.scoreAtIndexIn
  stp

open OnBytes.Attention in
/-- `Attention.keyTerm` keeps R. -/
instance stp_Attention_keyTerm [Steps R] (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) :
    Stp R (OnBytes.Attention.keyTerm S sKC pj w b) := by
  unfold OnBytes.Attention.keyTerm
  stp

open OnBytes.Attention in
/-- `Attention.keyAtIndexIn` keeps R. -/
instance stp_Attention_keyAtIndexIn [Steps R] (S : Shape) (scF : Sc3) :
    Stp R (OnBytes.Attention.keyAtIndexIn S scF) := by
  unfold OnBytes.Attention.keyAtIndexIn
  stp

open OnBytes.Attention in
/-- `Attention.bitsIn` keeps R. -/
instance stp_Attention_bitsIn [Steps R] (S : Shape) (tk tbg tbi : Array E) :
    Stp R (OnBytes.Attention.bitsIn S tk tbg tbi) := by
  unfold OnBytes.Attention.bitsIn
  stp

open OnBytes.Attention in
/-- `Attention.attain` keeps R. -/
instance stp_Attention_attain [Steps R] (S : Shape) :
    Stp R (OnBytes.Attention.attain S) := by
  unfold OnBytes.Attention.attain
  stp

/-! ## OnBytes/Model/AttentionClaimsA.lean -/

open OnBytes.Attention in
/-- `Attention.u3at` keeps R. -/
instance stp_Attention_u3at [Steps R] (h : Heard) (t i : Nat) :
    Stp R (OnBytes.Attention.u3at h t i) := by
  unfold OnBytes.Attention.u3at
  stp

open OnBytes.Attention in
/-- `Attention.weighted` keeps R. -/
instance stp_Attention_weighted [Steps R] (n : Nat) (w : Array E) (f : Nat → SubM Aff)
    [∀ x0, Stp R (f x0)] :
    Stp R (OnBytes.Attention.weighted n w f) := by
  unfold OnBytes.Attention.weighted
  stp

open OnBytes.Attention in
/-- `Attention.plane` keeps R. -/
instance stp_Attention_plane [Steps R] (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool) :
    Stp R (OnBytes.Attention.plane h t x lam a z isD) := by
  unfold OnBytes.Attention.plane
  stp

open OnBytes.Attention in
/-- `Attention.shV` keeps R. -/
instance stp_Attention_shV [Steps R] (h : Heard) (t off nl J lam j : Nat) :
    Stp R (OnBytes.Attention.shV h t off nl J lam j) := by
  unfold OnBytes.Attention.shV
  stp

open OnBytes.Attention in
/-- `Attention.xl` keeps R. -/
instance stp_Attention_xl [Steps R] (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat)
    (zc : Array E) :
    Stp R (OnBytes.Attention.xl h t X lam hd zc) := by
  unfold OnBytes.Attention.xl
  stp

open OnBytes.Attention in
/-- `Attention.overG` keeps R. -/
instance stp_Attention_overG [Steps R] (h : Heard) (zg : Array E) (f : Nat → SubM Aff)
    [∀ x0, Stp R (f x0)] :
    Stp R (OnBytes.Attention.overG h zg f) := by
  unfold OnBytes.Attention.overG
  stp

open OnBytes.Attention in
/-- `Attention.readDenominator` keeps R. -/
instance stp_Attention_readDenominator [Steps R] (h : Heard) (t : Nat) (zg : Array E)
    (lam a : Nat) :
    Stp R (OnBytes.Attention.readDenominator h t zg lam a) := by
  unfold OnBytes.Attention.readDenominator
  stp

open OnBytes.Attention in
/-- `Attention.readMaximum` keeps R. -/
instance stp_Attention_readMaximum [Steps R] (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat) :
    Stp R (OnBytes.Attention.readMaximum h t zg lam a) := by
  unfold OnBytes.Attention.readMaximum
  stp

open OnBytes.Attention in
/-- `Attention.readIndexBit` keeps R. -/
instance stp_Attention_readIndexBit [Steps R] (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) :
    Stp R (OnBytes.Attention.readIndexBit h t zg lam a k) := by
  unfold OnBytes.Attention.readIndexBit
  stp

open OnBytes.Attention in
/-- `Attention.readHead` keeps R. -/
instance stp_Attention_readHead [Steps R] (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E)
    (lam a : Nat) :
    Stp R (OnBytes.Attention.readHead h t X zg zc lam a) := by
  unfold OnBytes.Attention.readHead
  stp

open OnBytes.Attention in
/-- `Attention.readGroup` keeps R. -/
instance stp_Attention_readGroup [Steps R] (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E)
    (lam : Nat) :
    Stp R (OnBytes.Attention.readGroup h t X zg zc lam) := by
  unfold OnBytes.Attention.readGroup
  stp

open OnBytes.Attention in
/-- `Attention.lessPieces` keeps R. -/
instance stp_Attention_lessPieces [Steps R] (start : Aff) (pw : Array PW) (f : PW → SubM Aff)
    [∀ x0, Stp R (f x0)] :
    Stp R (OnBytes.Attention.lessPieces start pw f) := by
  unfold OnBytes.Attention.lessPieces
  stp

open OnBytes.Attention in
/-- `Attention.linPlanes` keeps R. -/
instance stp_Attention_linPlanes [Steps R] (h : Heard) (pc : PlaneClaim) :
    Stp R (OnBytes.Attention.linPlanes h pc) := by
  unfold OnBytes.Attention.linPlanes
  stp

open OnBytes.Attention in
/-- `Attention.callKR` keeps R. -/
instance stp_Attention_callKR [Steps R] (h : Heard) (q : Nat) :
    Stp R (OnBytes.Attention.callKR h q) := by
  unfold OnBytes.Attention.callKR
  stp

open OnBytes.Attention in
/-- `Attention.claim3` keeps R. -/
instance stp_Attention_claim3 [Steps R] (h : Heard) (j : Joins) :
    Stp R (OnBytes.Attention.claim3 h j) := by
  unfold OnBytes.Attention.claim3
  stp

open OnBytes.Attention in
/-- `Attention.endValues` keeps R. -/
instance stp_Attention_endValues [Steps R] (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array E)
    (b : Nat) (w : PW) :
    Stp R (OnBytes.Attention.endValues h k tb rc b w) := by
  unfold OnBytes.Attention.endValues
  stp

open OnBytes.Attention in
/-- `Attention.unitKFD` keeps R. -/
instance stp_Attention_unitKFD [Steps R] (h : Heard) (i : Nat) (k : Score) :
    Stp R (OnBytes.Attention.unitKFD h i k) := by
  unfold OnBytes.Attention.unitKFD
  stp

open OnBytes.Attention in
/-- `Attention.callKFD` keeps R. -/
instance stp_Attention_callKFD [Steps R] (h : Heard) (q : Nat) (c : ACall) :
    Stp R (OnBytes.Attention.callKFD h q c) := by
  unfold OnBytes.Attention.callKFD
  stp

open OnBytes.Attention in
/-- `Attention.claim4` keeps R. -/
instance stp_Attention_claim4 [Steps R] (h : Heard) (j : Joins) :
    Stp R (OnBytes.Attention.claim4 h j) := by
  unfold OnBytes.Attention.claim4
  stp

/-! ## OnBytes/Model/AttentionClaimsB.lean -/

open OnBytes.Attention in
/-- `Attention.endValuesE` keeps R. -/
instance stp_Attention_endValuesE [Steps R] (h : Heard) (b : Nat) (w : PW) :
    Stp R (OnBytes.Attention.endValuesE h b w) := by
  unfold OnBytes.Attention.endValuesE
  stp

open OnBytes.Attention in
/-- `Attention.claim5` keeps R. -/
instance stp_Attention_claim5 [Steps R] (h : Heard) (j : Joins) :
    Stp R (OnBytes.Attention.claim5 h j) := by
  unfold OnBytes.Attention.claim5
  stp

open OnBytes.Attention in
/-- `Attention.valueProduct` keeps R. -/
instance stp_Attention_valueProduct [Steps R] (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E)
    (isD : Bool) (tV : Nat) :
    Stp R (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by
  unfold OnBytes.Attention.valueProduct
  stp

open OnBytes.Attention in
/-- `Attention.claim6` keeps R. -/
instance stp_Attention_claim6 [Steps R] (h : Heard) :
    Stp R (OnBytes.Attention.claim6 h) := by
  unfold OnBytes.Attention.claim6
  stp

open OnBytes.Attention in
/-- `Attention.claim7` keeps R. -/
instance stp_Attention_claim7 [Steps R] (h : Heard) :
    Stp R (OnBytes.Attention.claim7 h) := by
  unfold OnBytes.Attention.claim7
  stp

open OnBytes.Attention in
/-- `Attention.claim8` keeps R. -/
instance stp_Attention_claim8 [Steps R] (h : Heard) :
    Stp R (OnBytes.Attention.claim8 h) := by
  unfold OnBytes.Attention.claim8
  stp

/-! ## OnBytes/Model/Attention.lean -/

open OnBytes.Attention in
/-- `Attention.allJoined` keeps R. -/
instance stp_Attention_allJoined [Steps R] (j : Joins) :
    Stp R (OnBytes.Attention.allJoined j) := by
  unfold OnBytes.Attention.allJoined
  stp

open OnBytes.Attention in
/-- `Attention.paddingLaid` keeps R. -/
instance stp_Attention_paddingLaid [Steps R] (S : Shape) (g : Forest.Heard) :
    Stp R (OnBytes.Attention.paddingLaid S g) := by
  unfold OnBytes.Attention.paddingLaid
  stp

open OnBytes.Attention in
/-- `Attention.noFreeSlot` keeps R. -/
instance stp_Attention_noFreeSlot [Steps R] (nMsg : Nat) :
    Stp R (OnBytes.Attention.noFreeSlot nMsg) := by
  unfold OnBytes.Attention.noFreeSlot
  stp

open OnBytes.Attention in
/-- `Attention.countsHeld` keeps R. -/
instance stp_Attention_countsHeld [Steps R] (P : Plan) (tl : HTailF2) :
    Stp R (OnBytes.Attention.countsHeld P tl) := by
  unfold OnBytes.Attention.countsHeld
  stp

open OnBytes.Attention in
/-- `Attention.hear` keeps R. -/
instance stp_Attention_hear [Steps R] (P : Plan) :
    Stp R (OnBytes.Attention.hear P) := by
  unfold OnBytes.Attention.hear
  stp

open OnBytes.Attention in
/-- `Attention.claims` keeps R. -/
instance stp_Attention_claims [Steps R] (P : Plan) (h : Heard) :
    Stp R (OnBytes.Attention.claims P h) := by
  unfold OnBytes.Attention.claims
  stp

/-! ## OnBytes/Model/Layer.lean -/

open OnBytes.Model.Layer in
/-- `Layer.form` keeps R. -/
instance stp_Model_Layer_form [Steps R] {α : Type} (x : Option α) :
    Stp R (OnBytes.Model.Layer.form x) := by
  unfold OnBytes.Model.Layer.form
  stp

open OnBytes.Model.Layer in
/-- `Layer.note` keeps R. -/
instance stp_Model_Layer_note [Steps R] (what : String) (x : E) :
    Stp R (OnBytes.Model.Layer.note what x) := by
  unfold OnBytes.Model.Layer.note
  stp

open OnBytes.Model.Layer in
/-- `Layer.noteClaims` keeps R. -/
instance stp_Model_Layer_noteClaims [Steps R] (what : String) :
    Stp R (OnBytes.Model.Layer.noteClaims what) := by
  unfold OnBytes.Model.Layer.noteClaims
  stp

open OnBytes.Model.Layer in
/-- `Layer.shownRun` keeps R. -/
instance stp_Model_Layer_shownRun [Steps R] (first n : Nat) :
    Stp R (OnBytes.Model.Layer.shownRun first n) := by
  unfold OnBytes.Model.Layer.shownRun
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearLook` keeps R. -/
instance stp_Model_Layer_hearLook [Steps R] (y : Lay) (g : Nat) :
    Stp R (OnBytes.Model.Layer.hearLook y g) := by
  unfold OnBytes.Model.Layer.hearLook
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearNorms` keeps R. -/
instance stp_Model_Layer_hearNorms [Steps R] (P : Pub) (g : Nat) (fo : Forest.Heard) :
    Stp R (OnBytes.Model.Layer.hearNorms P g fo) := by
  unfold OnBytes.Model.Layer.hearNorms
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearTerms` keeps R. -/
instance stp_Model_Layer_hearTerms [Steps R] (P : Pub) (H : Heard) :
    Stp R (OnBytes.Model.Layer.hearTerms P H) := by
  unfold OnBytes.Model.Layer.hearTerms
  stp

open OnBytes.Model.Layer in
/-- `Layer.joinStart` keeps R. -/
instance stp_Model_Layer_joinStart [Steps R] (v : Env) (H : Heard) (om : Array E) :
    Stp R (OnBytes.Model.Layer.joinStart v H om) := by
  unfold OnBytes.Model.Layer.joinStart
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearStack` keeps R. -/
instance stp_Model_Layer_hearStack [Steps R] (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    Stp R (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by
  unfold OnBytes.Model.Layer.hearStack
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearGated` keeps R. -/
instance stp_Model_Layer_hearGated [Steps R] (P : Pub) (H : Heard) (K : HeardStack) :
    Stp R (OnBytes.Model.Layer.hearGated P H K) := by
  unfold OnBytes.Model.Layer.hearGated
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsNorms` keeps R. -/
instance stp_Model_Layer_claimsNorms [Steps R] (P : Pub) (v : Env) (H : Heard) :
    Stp R (OnBytes.Model.Layer.claimsNorms P v H) := by
  unfold OnBytes.Model.Layer.claimsNorms
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimRowBatch` keeps R. -/
instance stp_Model_Layer_claimRowBatch [Steps R] (y : Lay) (H : Heard) :
    Stp R (OnBytes.Model.Layer.claimRowBatch y H) := by
  unfold OnBytes.Model.Layer.claimRowBatch
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsLedger5` keeps R. -/
instance stp_Model_Layer_claimsLedger5 [Steps R] (v : Env) (H : Heard) :
    Stp R (OnBytes.Model.Layer.claimsLedger5 v H) := by
  unfold OnBytes.Model.Layer.claimsLedger5
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsLedger4` keeps R. -/
instance stp_Model_Layer_claimsLedger4 [Steps R] (v : Env) (H : Heard) :
    Stp R (OnBytes.Model.Layer.claimsLedger4 v H) := by
  unfold OnBytes.Model.Layer.claimsLedger4
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsTerms` keeps R. -/
instance stp_Model_Layer_claimsTerms [Steps R] (v : Env) (H : Heard) :
    Stp R (OnBytes.Model.Layer.claimsTerms v H) := by
  unfold OnBytes.Model.Layer.claimsTerms
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsEnds` keeps R. -/
instance stp_Model_Layer_claimsEnds [Steps R] (v : Env) (o : Level) (e : Array E)
    (t rows blocks stride : Nat) (lamOf : Nat → Nat) (first : Nat) :
    Stp R (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by
  unfold OnBytes.Model.Layer.claimsEnds
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsGated` keeps R. -/
instance stp_Model_Layer_claimsGated [Steps R] (P : Pub) (v : Env) (hd : Level)
    (hd2 : Option Level) :
    Stp R (OnBytes.Model.Layer.claimsGated P v hd hd2) := by
  unfold OnBytes.Model.Layer.claimsGated
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsOneHot` keeps R. -/
instance stp_Model_Layer_claimsOneHot [Steps R] (v : Env) :
    Stp R (OnBytes.Model.Layer.claimsOneHot v) := by
  unfold OnBytes.Model.Layer.claimsOneHot
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimsPlanes` keeps R. -/
instance stp_Model_Layer_claimsPlanes [Steps R] (v : Env) (fo : Forest.Heard) :
    Stp R (OnBytes.Model.Layer.claimsPlanes v fo) := by
  unfold OnBytes.Model.Layer.claimsPlanes
  stp

open OnBytes.Model.Layer in
/-- `Layer.claimEmbedding` keeps R. -/
instance stp_Model_Layer_claimEmbedding [Steps R] (v : Env) (H : Heard) (sVE : Nat) :
    Stp R (OnBytes.Model.Layer.claimEmbedding v H sVE) := by
  unfold OnBytes.Model.Layer.claimEmbedding
  stp

open OnBytes.Model.Layer in
/-- `Layer.freeSlotTest` keeps R. -/
instance stp_Model_Layer_freeSlotTest [Steps R] (g used sFv : Nat) :
    Stp R (OnBytes.Model.Layer.freeSlotTest g used sFv) := by
  unfold OnBytes.Model.Layer.freeSlotTest
  stp

open OnBytes.Model.Layer in
/-- `Layer.hearOwn` keeps R. -/
instance stp_Model_Layer_hearOwn [Steps R] (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) :
    Stp R (OnBytes.Model.Layer.hearOwn P hp g fo) := by
  unfold OnBytes.Model.Layer.hearOwn
  stp

end OnBytes.Tie.Pv.Tail.StepsW

#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_Attention_hear
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_Attention_claims
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_Model_Layer_hearOwn
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stpL_Model_HTailF2_transcriptF
