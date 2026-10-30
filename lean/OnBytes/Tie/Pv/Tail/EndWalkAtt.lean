-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalkAtt.lean: the routines of the attention sub-proof's check
(OnBytes/Model/Attention.lean and the files that it imports) keep whatever the basic steps keep.

Theorems with their proofs, one for each routine, each by a walk through the routine's text (`walk`,
OnBytes/Tie/Pv/Tail/EndWalk.lean). R: any relation with `Prim R`. «x keeps R»: wherever the routine
x returns, R holds from the state before to the state after (`Pres R x`, `PresL R x`).

Main names: `pres_` and the routine's name.

Limits: those of OnBytes/Tie/Pv/Tail/EndWalk.lean.


-/
import OnBytes.Model.Attention
import OnBytes.Tie.Pv.Tail.EndWalkTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-! ## OnBytes/Model/AttentionSums.lean -/

open OnBytes.Attention in
/-- `Attention.sc3Rounds` keeps R. -/
instance pres_Attention_sc3Rounds [Prim R] :
    ∀ (n : Nat) (p : Psc) (r : Array E), Pres R (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r => by
    unfold OnBytes.Attention.sc3Rounds
    walk
  | n + 1, p, r => by
    have := pres_Attention_sc3Rounds n
    unfold OnBytes.Attention.sc3Rounds
    walk

open OnBytes.Attention in
/-- `Attention.sc3In` keeps R. -/
instance pres_Attention_sc3In [Prim R] (nv nb : Nat) (start : Model.Aff) :
    Pres R (OnBytes.Attention.sc3In nv nb start) := by
  unfold OnBytes.Attention.sc3In
  walk

open OnBytes.Attention in
/-- `Attention.sc3Shown` keeps R. -/
instance pres_Attention_sc3Shown [Prim R] (o : Sc3) (W : Array E) :
    ∀ (n b : Nat) (s : E), Pres R (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    unfold OnBytes.Attention.sc3Shown
    walk
  | n + 1, b, s => by
    have := pres_Attention_sc3Shown o W n
    unfold OnBytes.Attention.sc3Shown
    walk

open OnBytes.Attention in
/-- `Attention.sc3Row` keeps R. -/
instance pres_Attention_sc3Row [Prim R] (o : Sc3) (W : Array E) :
    Pres R (OnBytes.Attention.sc3Row o W) := by
  unfold OnBytes.Attention.sc3Row
  walk

open OnBytes.Attention in
/-- `Attention.scdRounds` keeps R. -/
instance pres_Attention_scdRounds [Prim R] :
    ∀ (ds : List Nat) (p : Psc) (r : Array E), Pres R (OnBytes.Attention.scdRounds ds p r)
  | [], p, r => by
    unfold OnBytes.Attention.scdRounds
    walk
  | d :: ds, p, r => by
    have := pres_Attention_scdRounds ds
    unfold OnBytes.Attention.scdRounds
    walk

open OnBytes.Attention in
/-- `Attention.scdIn` keeps R. -/
instance pres_Attention_scdIn [Prim R] (degrees : List Nat) (degreeInY n : Nat)
    (start : Model.Aff) :
    Pres R (OnBytes.Attention.scdIn degrees degreeInY n start) := by
  unfold OnBytes.Attention.scdIn
  walk

open OnBytes.Attention in
/-- `Attention.scdRow` keeps R. -/
instance pres_Attention_scdRow [Prim R] (o : Scd) (s0 : E) :
    Pres R (OnBytes.Attention.scdRow o s0) := by
  unfold OnBytes.Attention.scdRow
  walk

/-! ## OnBytes/Model/AttentionScores.lean -/

open OnBytes.Attention in
/-- `Attention.planeUnit` keeps R. -/
instance pres_Attention_planeUnit [Prim R] (S : Shape) (zk : Array (Array E))
    (u : Nat × ACall × Seg) :
    Pres R (OnBytes.Attention.planeUnit S zk u) := by
  unfold OnBytes.Attention.planeUnit
  walk

open OnBytes.Attention in
/-- `Attention.planeUnits` keeps R. -/
instance pres_Attention_planeUnits [Prim R] (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes : Array PlaneClaim),
      Pres R (OnBytes.Attention.planeUnits S zk us planes)
  | [], planes => by
    unfold OnBytes.Attention.planeUnits
    walk
  | u :: us, planes => by
    have := pres_Attention_planeUnits S zk us
    unfold OnBytes.Attention.planeUnits
    walk

open OnBytes.Attention in
/-- `Attention.scoreUnit` keeps R. -/
instance pres_Attention_scoreUnit [Prim R] (S : Shape) (zk : Array (Array E)) (claim : Nat)
    (u : Nat × ACall × Seg) :
    Pres R (OnBytes.Attention.scoreUnit S zk claim u) := by
  unfold OnBytes.Attention.scoreUnit
  walk

open OnBytes.Attention in
/-- `Attention.scoreUnits` keeps R. -/
instance pres_Attention_scoreUnits [Prim R] (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes : Array PlaneClaim) (stored : Array Score),
      Pres R (OnBytes.Attention.scoreUnits S zk us planes stored)
  | [], planes, stored => by
    unfold OnBytes.Attention.scoreUnits
    walk
  | u :: us, planes, stored => by
    have := pres_Attention_scoreUnits S zk us
    unfold OnBytes.Attention.scoreUnits
    walk

open OnBytes.Attention in
/-- `Attention.scores` keeps R. -/
instance pres_Attention_scores [Prim R] (S : Shape) (zk : Array (Array E)) :
    Pres R (OnBytes.Attention.scores S zk) := by
  unfold OnBytes.Attention.scores
  walk

/-! ## OnBytes/Model/AttentionDivide.lean -/

open OnBytes.Attention in
/-- `Attention.coinsOm` keeps R. -/
instance pres_Attention_coinsOm [Prim R] (n : Nat) :
    Pres R (OnBytes.Attention.coinsOm n) := by
  unfold OnBytes.Attention.coinsOm
  walk

open OnBytes.Attention in
/-- `Attention.productIn` keeps R. -/
instance pres_Attention_productIn [Prim R] (S : Shape) (pwW : Array PW) (zgW ziW : Array E)
    (sZO : Nat) :
    Pres R (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by
  unfold OnBytes.Attention.productIn
  walk

open OnBytes.Attention in
/-- `Attention.valueBelowIn` keeps R. -/
instance pres_Attention_valueBelowIn [Prim R] (S : Shape) (pwW : Array PW) (zgW zihi : Array E)
    (sCl : Nat) :
    Pres R (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by
  unfold OnBytes.Attention.valueBelowIn
  walk

open OnBytes.Attention in
/-- `Attention.valueOnIn` keeps R. -/
instance pres_Attention_valueOnIn [Prim R] (S : Shape) (pwW : Array PW) (zgW zihi : Array E)
    (sCl1 : Nat) :
    Pres R (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by
  unfold OnBytes.Attention.valueOnIn
  walk

open OnBytes.Attention in
/-- `Attention.divide` keeps R. -/
instance pres_Attention_divide [Prim R] (S : Shape) (zk : Array (Array E)) :
    Pres R (OnBytes.Attention.divide S zk) := by
  unfold OnBytes.Attention.divide
  walk

open OnBytes.Attention in
/-- `Attention.scoreAtIndexIn` keeps R. -/
instance pres_Attention_scoreAtIndexIn [Prim R] (S : Shape) (tg ti : Array E) :
    Pres R (OnBytes.Attention.scoreAtIndexIn S tg ti) := by
  unfold OnBytes.Attention.scoreAtIndexIn
  walk

open OnBytes.Attention in
/-- `Attention.keyTerm` keeps R. -/
instance pres_Attention_keyTerm [Prim R] (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) :
    Pres R (OnBytes.Attention.keyTerm S sKC pj w b) := by
  unfold OnBytes.Attention.keyTerm
  walk

open OnBytes.Attention in
/-- `Attention.keyAtIndexIn` keeps R. -/
instance pres_Attention_keyAtIndexIn [Prim R] (S : Shape) (scF : Sc3) :
    Pres R (OnBytes.Attention.keyAtIndexIn S scF) := by
  unfold OnBytes.Attention.keyAtIndexIn
  walk

open OnBytes.Attention in
/-- `Attention.bitsIn` keeps R. -/
instance pres_Attention_bitsIn [Prim R] (S : Shape) (tk tbg tbi : Array E) :
    Pres R (OnBytes.Attention.bitsIn S tk tbg tbi) := by
  unfold OnBytes.Attention.bitsIn
  walk

open OnBytes.Attention in
/-- `Attention.attain` keeps R. -/
instance pres_Attention_attain [Prim R] (S : Shape) :
    Pres R (OnBytes.Attention.attain S) := by
  unfold OnBytes.Attention.attain
  walk

/-! ## OnBytes/Model/AttentionClaimsA.lean -/

open OnBytes.Attention in
/-- `Attention.u3at` keeps R. -/
instance pres_Attention_u3at [Prim R] (h : Heard) (t i : Nat) :
    Pres R (OnBytes.Attention.u3at h t i) := by
  unfold OnBytes.Attention.u3at
  walk

open OnBytes.Attention in
/-- `Attention.weighted` keeps R. -/
instance pres_Attention_weighted [Prim R] (n : Nat) (w : Array E) (f : Nat → SubM Aff)
    [∀ x0, Pres R (f x0)] :
    Pres R (OnBytes.Attention.weighted n w f) := by
  unfold OnBytes.Attention.weighted
  walk

open OnBytes.Attention in
/-- `Attention.plane` keeps R. -/
instance pres_Attention_plane [Prim R] (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool) :
    Pres R (OnBytes.Attention.plane h t x lam a z isD) := by
  unfold OnBytes.Attention.plane
  walk

open OnBytes.Attention in
/-- `Attention.shV` keeps R. -/
instance pres_Attention_shV [Prim R] (h : Heard) (t off nl J lam j : Nat) :
    Pres R (OnBytes.Attention.shV h t off nl J lam j) := by
  unfold OnBytes.Attention.shV
  walk

open OnBytes.Attention in
/-- `Attention.xl` keeps R. -/
instance pres_Attention_xl [Prim R] (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat)
    (zc : Array E) :
    Pres R (OnBytes.Attention.xl h t X lam hd zc) := by
  unfold OnBytes.Attention.xl
  walk

open OnBytes.Attention in
/-- `Attention.overG` keeps R. -/
instance pres_Attention_overG [Prim R] (h : Heard) (zg : Array E) (f : Nat → SubM Aff)
    [∀ x0, Pres R (f x0)] :
    Pres R (OnBytes.Attention.overG h zg f) := by
  unfold OnBytes.Attention.overG
  walk

open OnBytes.Attention in
/-- `Attention.readDenominator` keeps R. -/
instance pres_Attention_readDenominator [Prim R] (h : Heard) (t : Nat) (zg : Array E)
    (lam a : Nat) :
    Pres R (OnBytes.Attention.readDenominator h t zg lam a) := by
  unfold OnBytes.Attention.readDenominator
  walk

open OnBytes.Attention in
/-- `Attention.readMaximum` keeps R. -/
instance pres_Attention_readMaximum [Prim R] (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat) :
    Pres R (OnBytes.Attention.readMaximum h t zg lam a) := by
  unfold OnBytes.Attention.readMaximum
  walk

open OnBytes.Attention in
/-- `Attention.readIndexBit` keeps R. -/
instance pres_Attention_readIndexBit [Prim R] (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) :
    Pres R (OnBytes.Attention.readIndexBit h t zg lam a k) := by
  unfold OnBytes.Attention.readIndexBit
  walk

open OnBytes.Attention in
/-- `Attention.readHead` keeps R. -/
instance pres_Attention_readHead [Prim R] (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E)
    (lam a : Nat) :
    Pres R (OnBytes.Attention.readHead h t X zg zc lam a) := by
  unfold OnBytes.Attention.readHead
  walk

open OnBytes.Attention in
/-- `Attention.readGroup` keeps R. -/
instance pres_Attention_readGroup [Prim R] (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E)
    (lam : Nat) :
    Pres R (OnBytes.Attention.readGroup h t X zg zc lam) := by
  unfold OnBytes.Attention.readGroup
  walk

open OnBytes.Attention in
/-- `Attention.lessPieces` keeps R. -/
instance pres_Attention_lessPieces [Prim R] (start : Aff) (pw : Array PW) (f : PW → SubM Aff)
    [∀ x0, Pres R (f x0)] :
    Pres R (OnBytes.Attention.lessPieces start pw f) := by
  unfold OnBytes.Attention.lessPieces
  walk

open OnBytes.Attention in
/-- `Attention.linPlanes` keeps R. -/
instance pres_Attention_linPlanes [Prim R] (h : Heard) (pc : PlaneClaim) :
    Pres R (OnBytes.Attention.linPlanes h pc) := by
  unfold OnBytes.Attention.linPlanes
  walk

open OnBytes.Attention in
/-- `Attention.callKR` keeps R. -/
instance pres_Attention_callKR [Prim R] (h : Heard) (q : Nat) :
    Pres R (OnBytes.Attention.callKR h q) := by
  unfold OnBytes.Attention.callKR
  walk

open OnBytes.Attention in
/-- `Attention.claim3` keeps R. -/
instance pres_Attention_claim3 [Prim R] (h : Heard) (j : Joins) :
    Pres R (OnBytes.Attention.claim3 h j) := by
  unfold OnBytes.Attention.claim3
  walk

open OnBytes.Attention in
/-- `Attention.endValues` keeps R. -/
instance pres_Attention_endValues [Prim R] (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array E)
    (b : Nat) (w : PW) :
    Pres R (OnBytes.Attention.endValues h k tb rc b w) := by
  unfold OnBytes.Attention.endValues
  walk

open OnBytes.Attention in
/-- `Attention.unitKFD` keeps R. -/
instance pres_Attention_unitKFD [Prim R] (h : Heard) (i : Nat) (k : Score) :
    Pres R (OnBytes.Attention.unitKFD h i k) := by
  unfold OnBytes.Attention.unitKFD
  walk

open OnBytes.Attention in
/-- `Attention.callKFD` keeps R. -/
instance pres_Attention_callKFD [Prim R] (h : Heard) (q : Nat) (c : ACall) :
    Pres R (OnBytes.Attention.callKFD h q c) := by
  unfold OnBytes.Attention.callKFD
  walk

open OnBytes.Attention in
/-- `Attention.claim4` keeps R. -/
instance pres_Attention_claim4 [Prim R] (h : Heard) (j : Joins) :
    Pres R (OnBytes.Attention.claim4 h j) := by
  unfold OnBytes.Attention.claim4
  walk

/-! ## OnBytes/Model/AttentionClaimsB.lean -/

open OnBytes.Attention in
/-- `Attention.endValuesE` keeps R. -/
instance pres_Attention_endValuesE [Prim R] (h : Heard) (b : Nat) (w : PW) :
    Pres R (OnBytes.Attention.endValuesE h b w) := by
  unfold OnBytes.Attention.endValuesE
  walk

open OnBytes.Attention in
/-- `Attention.claim5` keeps R. -/
instance pres_Attention_claim5 [Prim R] (h : Heard) (j : Joins) :
    Pres R (OnBytes.Attention.claim5 h j) := by
  unfold OnBytes.Attention.claim5
  walk

open OnBytes.Attention in
/-- `Attention.valueProduct` keeps R. -/
instance pres_Attention_valueProduct [Prim R] (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E)
    (isD : Bool) (tV : Nat) :
    Pres R (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by
  unfold OnBytes.Attention.valueProduct
  walk

open OnBytes.Attention in
/-- `Attention.claim6` keeps R. -/
instance pres_Attention_claim6 [Prim R] (h : Heard) :
    Pres R (OnBytes.Attention.claim6 h) := by
  unfold OnBytes.Attention.claim6
  walk

open OnBytes.Attention in
/-- `Attention.claim7` keeps R. -/
instance pres_Attention_claim7 [Prim R] (h : Heard) :
    Pres R (OnBytes.Attention.claim7 h) := by
  unfold OnBytes.Attention.claim7
  walk

open OnBytes.Attention in
/-- `Attention.claim8` keeps R. -/
instance pres_Attention_claim8 [Prim R] (h : Heard) :
    Pres R (OnBytes.Attention.claim8 h) := by
  unfold OnBytes.Attention.claim8
  walk

/-! ## OnBytes/Model/Attention.lean -/

open OnBytes.Attention.Seam in
/-- `Attention.Seam.objects` keeps R. -/
instance pres_Attention_Seam_objects [Prim R] (tl : HTailF2) (funs : Array HFun) :
    Pres R (OnBytes.Attention.Seam.objects tl funs) := by
  unfold OnBytes.Attention.Seam.objects
  walk

open OnBytes.Attention in
/-- `Attention.allJoined` keeps R. -/
instance pres_Attention_allJoined [Prim R] (j : Joins) :
    Pres R (OnBytes.Attention.allJoined j) := by
  unfold OnBytes.Attention.allJoined
  walk

open OnBytes.Attention in
/-- `Attention.paddingLaid` keeps R. -/
instance pres_Attention_paddingLaid [Prim R] (S : Shape) (g : Forest.Heard) :
    Pres R (OnBytes.Attention.paddingLaid S g) := by
  unfold OnBytes.Attention.paddingLaid
  walk

open OnBytes.Attention in
/-- `Attention.noFreeSlot` keeps R. -/
instance pres_Attention_noFreeSlot [Prim R] (nMsg : Nat) :
    Pres R (OnBytes.Attention.noFreeSlot nMsg) := by
  unfold OnBytes.Attention.noFreeSlot
  walk

open OnBytes.Attention in
/-- `Attention.countsHeld` keeps R. -/
instance pres_Attention_countsHeld [Prim R] (P : Plan) (tl : HTailF2) :
    Pres R (OnBytes.Attention.countsHeld P tl) := by
  unfold OnBytes.Attention.countsHeld
  walk

open OnBytes.Attention in
/-- `Attention.hear` keeps R. -/
instance pres_Attention_hear [Prim R] (P : Plan) :
    Pres R (OnBytes.Attention.hear P) := by
  unfold OnBytes.Attention.hear
  walk

open OnBytes.Attention in
/-- `Attention.claims` keeps R. -/
instance pres_Attention_claims [Prim R] (P : Plan) (h : Heard) :
    Pres R (OnBytes.Attention.claims P h) := by
  unfold OnBytes.Attention.claims
  walk

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Attention_hear
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Attention_claims
