-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndGoodAtt.lean: the attention sub-proof's own claims (`Attention.claims`,
OnBytes/Model/Attention.lean) are added by the steps of OnBytes/Tie/Pv/Led/LedAdds.lean, and every
form among them names entries of the vector of the tables alone.

Definitions, and theorems with their proofs, each by a walk through a routine's text (`walkQ`,
OnBytes/Tie/Pv/Tail/EndGood.lean).

Main names: the instances of `HasGood` for the records that hold forms: a masked sumcheck's state
(its start), the two kinds of attention's sumchecks (their states and their rows), a score, the
division, the maximum, what the lookup has heard (its rows, its leaves' sumcheck, its end form),
what the sub-proof has heard, the calls' key forms;
  `pq_` and a routine's name: the forms that the routine adds have entries in that array alone, and
    what it returns is good; `good_` and a function's name;
  `attention_claims_adds`: where `Attention.claims P h` returns from F to G and the record h is
    good: there is a list l of forms with `Adds F l G`, and every entry of every member of l lies in
    array h.iU3.

Limits: those of OnBytes/Tie/Pv/Tail/EndGood.lean. That the record h is good (the forms that were
stored while the messages were heard have entries in that array alone; by reading they have none) is
a premise.


-/
import OnBytes.Model.Attention
import OnBytes.Tie.Pv.Tail.EndGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Forms
open OnBytes OnBytes.Model

variable {t0 : Nat}

/-! ## The records that hold forms -/

instance : HasGood Psc := ⟨fun t r => HasGood.good t r.start⟩

/-- The record's field `start`. -/
instance good_Psc_start (r : Psc) [h : Good t0 r] : Good t0 r.start := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Sc3 := ⟨fun t r => HasGood.good t r.p ∧ HasGood.good t r.rowU⟩

/-- The record's field `p`. -/
instance good_Sc3_p (r : Attention.Sc3) [h : Good t0 r] : Good t0 r.p := ⟨h.out.1⟩

/-- The record's field `rowU`. -/
instance good_Sc3_rowU (r : Attention.Sc3) [h : Good t0 r] : Good t0 r.rowU := ⟨h.out.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Scd := ⟨fun t r => HasGood.good t r.p ∧ HasGood.good t r.rowU⟩

/-- The record's field `p`. -/
instance good_Scd_p (r : Attention.Scd) [h : Good t0 r] : Good t0 r.p := ⟨h.out.1⟩

/-- The record's field `rowU`. -/
instance good_Scd_rowU (r : Attention.Scd) [h : Good t0 r] : Good t0 r.rowU := ⟨h.out.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Score := ⟨fun t r => HasGood.good t r.sc⟩

/-- The record's field `sc`. -/
instance good_Score_sc (r : Attention.Score) [h : Good t0 r] : Good t0 r.sc := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Divide :=
  ⟨fun t r => HasGood.good t r.scE ∧ HasGood.good t r.vpm ∧ HasGood.good t r.vpd⟩

/-- The record's field `scE`. -/
instance good_Divide_scE (r : Attention.Divide) [h : Good t0 r] : Good t0 r.scE := ⟨h.out.1⟩

/-- The record's field `vpm`. -/
instance good_Divide_vpm (r : Attention.Divide) [h : Good t0 r] : Good t0 r.vpm := ⟨h.out.2.1⟩

/-- The record's field `vpd`. -/
instance good_Divide_vpd (r : Attention.Divide) [h : Good t0 r] : Good t0 r.vpd := ⟨h.out.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Attain :=
  ⟨fun t r => HasGood.good t r.scF ∧ HasGood.good t r.scd ∧ HasGood.good t r.scH⟩

/-- The record's field `scF`. -/
instance good_Attain_scF (r : Attention.Attain) [h : Good t0 r] : Good t0 r.scF := ⟨h.out.1⟩

/-- The record's field `scd`. -/
instance good_Attain_scd (r : Attention.Attain) [h : Good t0 r] : Good t0 r.scd := ⟨h.out.2.1⟩

/-- The record's field `scH`. -/
instance good_Attain_scH (r : Attention.Attain) [h : Good t0 r] : Good t0 r.scH := ⟨h.out.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Forest.Heard :=
  ⟨fun t r => HasGood.good t r.rows ∧ HasGood.good t r.leaves ∧ HasGood.good t r.cEnd⟩

/-- The record's field `rows`. -/
instance good_FHeard_rows (r : Forest.Heard) [h : Good t0 r] : Good t0 r.rows := ⟨h.out.1⟩

/-- The record's field `leaves`. -/
instance good_FHeard_leaves (r : Forest.Heard) [h : Good t0 r] : Good t0 r.leaves := ⟨h.out.2.1⟩

/-- The record's field `cEnd`. -/
instance good_FHeard_cEnd (r : Forest.Heard) [h : Good t0 r] : Good t0 r.cEnd := ⟨h.out.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Heard :=
  ⟨fun t r => HasGood.good t r.g ∧ HasGood.good t r.scores ∧ HasGood.good t r.d ∧
    HasGood.good t r.x⟩

/-- The record's field `g`. -/
instance good_Heard_g (r : Attention.Heard) [h : Good t0 r] : Good t0 r.g := ⟨h.out.1⟩

/-- The record's field `scores`. -/
instance good_Heard_scores (r : Attention.Heard) [h : Good t0 r] : Good t0 r.scores := ⟨h.out.2.1⟩

/-- The record's field `d`. -/
instance good_Heard_d (r : Attention.Heard) [h : Good t0 r] : Good t0 r.d := ⟨h.out.2.2.1⟩

/-- The record's field `x`. -/
instance good_Heard_x (r : Attention.Heard) [h : Good t0 r] : Good t0 r.x := ⟨h.out.2.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.Joins := ⟨fun t r => HasGood.good t r.kf⟩

/-- The record's field `kf`. -/
instance good_Joins_kf (r : Attention.Joins) [h : Good t0 r] : Good t0 r.kf := ⟨h.out⟩

/-- No key form is set yet. -/
instance good_Joins_empty (n : Nat) : Good t0 (Attention.Joins.empty n) :=
  ⟨(inferInstance : Good t0 (Array.replicate n (Aff.ofConst zeroE))).out⟩

/-- A key form is set. -/
instance good_Joins_set (j : Attention.Joins) (q : Nat) (v : Aff) [Good t0 j] [Good t0 v] :
    Good t0 (j.set q v) := ⟨(inferInstance : Good t0 (j.kf.setIfInBounds q v)).out⟩

/-! ## Functions that return forms -/

/-- Slots added to a form. -/
instance good_addSlots (a : Aff) (first : Nat) (form : Array E) [Good t0 a] :
    Good t0 (addSlots a first form) := by
  unfold addSlots
  have : Good t0 (form.foldl addSlot (first, a)) := by
    refine good_foldlArr _ ?_ _ _ inferInstance inferInstance
    intro b x hb _
    obtain ⟨j, u⟩ := b
    have : Good t0 u := ⟨hb.out.2⟩
    show Good t0 (j + 1, Aff.addMul u (Aff.slot j) x)
    infer_instance
  infer_instance

/-- The claim that a masked sumcheck leaves. -/
instance good_rowForm (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    Good t0 (p.rowForm S0 kept) := by
  unfold Psc.rowForm
  infer_instance

/-- The state of a masked sumcheck whose claim is made. -/
instance good_rowMade (p : Psc) [h : Good t0 p] : Good t0 { p with rowMade := true } := ⟨h.out⟩

/-- `pscRow` adds no claim; the claim that it returns is good if the sumcheck's start and the form
kept are. -/
instance pq_pscRow (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    PresQ t0 (pscRow p S0 kept) := by
  unfold pscRow
  walkQ

open OnBytes.Attention in
/-- `Attention.sc3A` returns a good value. -/
instance good_Attention_sc3A (o : Sc3) (b : Nat) :
    Good t0 (OnBytes.Attention.sc3A o b) := by
  unfold OnBytes.Attention.sc3A
  walkQ

open OnBytes.Attention in
/-- `Attention.sc3B` returns a good value. -/
instance good_Attention_sc3B (o : Sc3) (b : Nat) :
    Good t0 (OnBytes.Attention.sc3B o b) := by
  unfold OnBytes.Attention.sc3B
  walkQ

open OnBytes.Attention in
/-- `Attention.keyKR` returns a good value. -/
instance good_Attention_keyKR (pc : PlaneClaim) :
    Good t0 (OnBytes.Attention.keyKR pc) := by
  unfold OnBytes.Attention.keyKR
  walkQ

open OnBytes.Attention in
/-- `Attention.padTerm` returns a good value. -/
instance good_Attention_padTerm (c : ACall) (zk : Array E) :
    Good t0 (OnBytes.Attention.padTerm c zk) := by
  unfold OnBytes.Attention.padTerm
  walkQ

open OnBytes.Attention in
/-- `Attention.keyKFD` returns a good value. -/
instance good_Attention_keyKFD (d : ShD) (k : Score) :
    Good t0 (OnBytes.Attention.keyKFD d k) := by
  unfold OnBytes.Attention.keyKFD
  walkQ

open OnBytes.Attention in
/-- `Attention.remForm` returns a good value. -/
instance good_Attention_remForm (d : Divide) :
    Good t0 (OnBytes.Attention.remForm d) := by
  unfold OnBytes.Attention.remForm
  walkQ

open OnBytes.Attention in
/-- `Attention.indexForm` returns a good value. -/
instance good_Attention_indexForm (d : Divide) (lt : Nat) :
    Good t0 (OnBytes.Attention.indexForm d lt) := by
  unfold OnBytes.Attention.indexForm
  walkQ

open OnBytes.Attention in
/-- `Attention.keyWL` returns a good value. -/
instance good_Attention_keyWL (d : Divide) :
    Good t0 (OnBytes.Attention.keyWL d) := by
  unfold OnBytes.Attention.keyWL
  walkQ

open OnBytes.Attention in
/-- `Attention.keyIX` returns a good value. -/
instance good_Attention_keyIX (S : Shape) (d : Divide) :
    Good t0 (OnBytes.Attention.keyIX S d) := by
  unfold OnBytes.Attention.keyIX
  walkQ

open OnBytes.Attention in
/-- `Attention.keyWH` returns a good value. -/
instance good_Attention_keyWH (d : Divide) :
    Good t0 (OnBytes.Attention.keyWH d) := by
  unfold OnBytes.Attention.keyWH
  walkQ

open OnBytes.Attention in
/-- `Attention.joinR16` returns a good value. -/
instance good_Attention_joinR16 (S : Shape) (d : Divide) (j : Joins) [Good t0 j] :
    Good t0 (OnBytes.Attention.joinR16 S d j) := by
  unfold OnBytes.Attention.joinR16
  walkQ

/-! ## OnBytes/Model/Look.lean -/

open OnBytes.Model.Forest in
/-- `Forest.objects`: its forms and what it returns are good. -/
instance pq_Model_Forest_objects (g : Heard) [Good t0 g] :
    PresQ t0 (OnBytes.Model.Forest.objects g) := by
  unfold OnBytes.Model.Forest.objects
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.planesAdded`: its forms and what it returns are good. -/
instance pq_Model_Forest_planesAdded (g : Heard) [Good t0 g] :
    PresQ t0 (OnBytes.Model.Forest.planesAdded g) := by
  unfold OnBytes.Model.Forest.planesAdded
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.joinAdded`: its forms and what it returns are good. -/
instance pq_Model_Forest_joinAdded (g : Heard) [Good t0 g] :
    PresQ t0 (OnBytes.Model.Forest.joinAdded g) := by
  unfold OnBytes.Model.Forest.joinAdded
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.paddingLaid`: its forms and what it returns are good. -/
instance pq_Model_Forest_paddingLaid (g : Heard) (laid : Array Nat) [Good t0 g] [Good t0 laid] :
    PresQ t0 (OnBytes.Model.Forest.paddingLaid g laid) := by
  unfold OnBytes.Model.Forest.paddingLaid
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.join`: its forms and what it returns are good. -/
instance pq_Model_Forest_join (g : Heard) (KF : Array Aff) [Good t0 g] [Good t0 KF] :
    PresQ t0 (OnBytes.Model.Forest.join g KF) := by
  unfold OnBytes.Model.Forest.join
  refine pq_bind inferInstance fun _ _ => ?_
  refine pq_bind inferInstance fun _ _ => ?_
  refine @pq_pure _ _ _ _ ?_
  refine @good_sub _ _ _ (@good_add _ _ _ ?_ inferInstance) inferInstance
  refine good_foldl _ ?_ _ _ inferInstance inferInstance
  intro f c _ _
  dsimp only
  infer_instance

open OnBytes.Model.Forest in
/-- `Forest.planesAt`: its forms and what it returns are good. -/
instance pq_Model_Forest_planesAt (g : Heard) (lm e : Nat) (bit : Nat → Nat → SubM Aff) [Good t0 g]
    [Good t0 lm] [Good t0 e] [∀ x0 x1, PresQ t0 (bit x0 x1)] :
    PresQ t0 (OnBytes.Model.Forest.planesAt g lm e bit) := by
  unfold OnBytes.Model.Forest.planesAt
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.planeClaims`: its forms and what it returns are good. -/
instance pq_Model_Forest_planeClaims (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [Good t0 g] [Good t0 lm] [∀ x0 x1, PresQ t0 (bit x0 x1)]
    [∀ x0, PresQ t0 (pin x0)] :
    PresQ t0 (OnBytes.Model.Forest.planeClaims g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeClaims
  walkQ

open OnBytes.Model.Forest in
/-- `Forest.planeLins`: its forms and what it returns are good. -/
instance pq_Model_Forest_planeLins (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [Good t0 g] [Good t0 lm] [∀ x0 x1, PresQ t0 (bit x0 x1)]
    [∀ x0, PresQ t0 (pin x0)] :
    PresQ t0 (OnBytes.Model.Forest.planeLins g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeLins
  walkQ

/-! ## OnBytes/Model/AttentionClaimsA.lean -/

open OnBytes.Attention in
/-- `Attention.u3at`: its forms and what it returns are good. -/
instance pq_Attention_u3at (h : Heard) (t i : Nat) [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 i] :
    PresQ h.iU3 (OnBytes.Attention.u3at h t i) := by
  unfold OnBytes.Attention.u3at
  walkQ

open OnBytes.Attention in
/-- `Attention.weighted`: its forms and what it returns are good. -/
instance pq_Attention_weighted (n : Nat) (w : Array E) (f : Nat → SubM Aff) [Good t0 n] [Good t0 w]
    [∀ x0, PresQ t0 (f x0)] :
    PresQ t0 (OnBytes.Attention.weighted n w f) := by
  unfold OnBytes.Attention.weighted
  walkQ

open OnBytes.Attention in
/-- `Attention.plane`: its forms and what it returns are good. -/
instance pq_Attention_plane (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool) [Good h.iU3 h]
    [Good h.iU3 t] [Good h.iU3 x] [Good h.iU3 lam] [Good h.iU3 a] [Good h.iU3 z] [Good h.iU3 isD] :
    PresQ h.iU3 (OnBytes.Attention.plane h t x lam a z isD) := by
  unfold OnBytes.Attention.plane
  walkQ

open OnBytes.Attention in
/-- `Attention.shV`: its forms and what it returns are good. -/
instance pq_Attention_shV (h : Heard) (t off nl J lam j : Nat) [Good h.iU3 h] [Good h.iU3 t]
    [Good h.iU3 off] [Good h.iU3 nl] [Good h.iU3 J] [Good h.iU3 lam] [Good h.iU3 j] :
    PresQ h.iU3 (OnBytes.Attention.shV h t off nl J lam j) := by
  unfold OnBytes.Attention.shV
  walkQ

open OnBytes.Attention in
/-- `Attention.xl`: its forms and what it returns are good. -/
instance pq_Attention_xl (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat) (zc : Array E)
    [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 X] [Good h.iU3 lam] [Good h.iU3 hd] [Good h.iU3 zc] :
    PresQ h.iU3 (OnBytes.Attention.xl h t X lam hd zc) := by
  unfold OnBytes.Attention.xl
  walkQ

open OnBytes.Attention in
/-- `Attention.overG`: its forms and what it returns are good. -/
instance pq_Attention_overG (h : Heard) (zg : Array E) (f : Nat → SubM Aff) [Good h.iU3 h]
    [Good h.iU3 zg] [∀ x0, PresQ h.iU3 (f x0)] :
    PresQ h.iU3 (OnBytes.Attention.overG h zg f) := by
  unfold OnBytes.Attention.overG
  walkQ

open OnBytes.Attention in
/-- `Attention.readDenominator`: its forms and what it returns are good. -/
instance pq_Attention_readDenominator (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)
    [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 zg] [Good h.iU3 lam] [Good h.iU3 a] :
    PresQ h.iU3 (OnBytes.Attention.readDenominator h t zg lam a) := by
  unfold OnBytes.Attention.readDenominator
  walkQ

open OnBytes.Attention in
/-- `Attention.readMaximum`: its forms and what it returns are good. -/
instance pq_Attention_readMaximum (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat) [Good h.iU3 h]
    [Good h.iU3 t] [Good h.iU3 zg] [Good h.iU3 lam] [Good h.iU3 a] :
    PresQ h.iU3 (OnBytes.Attention.readMaximum h t zg lam a) := by
  unfold OnBytes.Attention.readMaximum
  walkQ

open OnBytes.Attention in
/-- `Attention.readIndexBit`: its forms and what it returns are good. -/
instance pq_Attention_readIndexBit (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat)
    [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 zg] [Good h.iU3 lam] [Good h.iU3 a] [Good h.iU3 k] :
    PresQ h.iU3 (OnBytes.Attention.readIndexBit h t zg lam a k) := by
  unfold OnBytes.Attention.readIndexBit
  walkQ

open OnBytes.Attention in
/-- `Attention.readHead`: its forms and what it returns are good. -/
instance pq_Attention_readHead (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam a : Nat)
    [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 X] [Good h.iU3 zg] [Good h.iU3 zc] [Good h.iU3 lam]
    [Good h.iU3 a] :
    PresQ h.iU3 (OnBytes.Attention.readHead h t X zg zc lam a) := by
  unfold OnBytes.Attention.readHead
  walkQ

open OnBytes.Attention in
/-- `Attention.readGroup`: its forms and what it returns are good. -/
instance pq_Attention_readGroup (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam : Nat)
    [Good h.iU3 h] [Good h.iU3 t] [Good h.iU3 X] [Good h.iU3 zg] [Good h.iU3 zc] [Good h.iU3 lam] :
    PresQ h.iU3 (OnBytes.Attention.readGroup h t X zg zc lam) := by
  unfold OnBytes.Attention.readGroup
  walkQ

open OnBytes.Attention in
/-- `Attention.lessPieces`: its forms and what it returns are good. -/
instance pq_Attention_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) [Good t0 start]
    [Good t0 pw] [∀ x0, PresQ t0 (f x0)] :
    PresQ t0 (OnBytes.Attention.lessPieces start pw f) := by
  unfold OnBytes.Attention.lessPieces
  walkQ

open OnBytes.Attention in
/-- `Attention.linPlanes`: its forms and what it returns are good. -/
instance pq_Attention_linPlanes (h : Heard) (pc : PlaneClaim) [Good h.iU3 h] [Good h.iU3 pc] :
    PresQ h.iU3 (OnBytes.Attention.linPlanes h pc) := by
  unfold OnBytes.Attention.linPlanes
  walkQ

open OnBytes.Attention in
/-- `Attention.callKR`: its forms and what it returns are good. -/
instance pq_Attention_callKR (h : Heard) (q : Nat) [Good h.iU3 h] [Good h.iU3 q] :
    PresQ h.iU3 (OnBytes.Attention.callKR h q) := by
  unfold OnBytes.Attention.callKR
  walkQ

open OnBytes.Attention in
/-- `Attention.claim3`: its forms and what it returns are good. -/
instance pq_Attention_claim3 (h : Heard) (j : Joins) [Good h.iU3 h] [Good h.iU3 j] :
    PresQ h.iU3 (OnBytes.Attention.claim3 h j) := by
  unfold OnBytes.Attention.claim3
  walkQ

open OnBytes.Attention in
/-- `Attention.endValues`: its forms and what it returns are good. -/
instance pq_Attention_endValues (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array E) (b : Nat)
    (w : PW) [Good h.iU3 h] [Good h.iU3 k] [Good h.iU3 tb] [Good h.iU3 rc] [Good h.iU3 b]
    [Good h.iU3 w] :
    PresQ h.iU3 (OnBytes.Attention.endValues h k tb rc b w) := by
  unfold OnBytes.Attention.endValues
  walkQ

open OnBytes.Attention in
/-- `Attention.unitKFD`: its forms and what it returns are good. -/
instance pq_Attention_unitKFD (h : Heard) (i : Nat) (k : Score) [Good h.iU3 h] [Good h.iU3 i]
    [Good h.iU3 k] :
    PresQ h.iU3 (OnBytes.Attention.unitKFD h i k) := by
  unfold OnBytes.Attention.unitKFD
  walkQ

open OnBytes.Attention in
/-- `Attention.callKFD`: its forms and what it returns are good. -/
instance pq_Attention_callKFD (h : Heard) (q : Nat) (c : ACall) [Good h.iU3 h] [Good h.iU3 q]
    [Good h.iU3 c] :
    PresQ h.iU3 (OnBytes.Attention.callKFD h q c) := by
  unfold OnBytes.Attention.callKFD
  walkQ

open OnBytes.Attention in
/-- `Attention.claim4`: its forms and what it returns are good. -/
instance pq_Attention_claim4 (h : Heard) (j : Joins) [Good h.iU3 h] [Good h.iU3 j] :
    PresQ h.iU3 (OnBytes.Attention.claim4 h j) := by
  unfold OnBytes.Attention.claim4
  walkQ

/-! ## OnBytes/Model/AttentionClaimsB.lean -/

open OnBytes.Attention in
/-- `Attention.endValuesE`: its forms and what it returns are good. -/
instance pq_Attention_endValuesE (h : Heard) (b : Nat) (w : PW) [Good h.iU3 h] [Good h.iU3 b]
    [Good h.iU3 w] :
    PresQ h.iU3 (OnBytes.Attention.endValuesE h b w) := by
  unfold OnBytes.Attention.endValuesE
  walkQ

open OnBytes.Attention in
/-- `Attention.claim5`: its forms and what it returns are good. -/
instance pq_Attention_claim5 (h : Heard) (j : Joins) [Good h.iU3 h] [Good h.iU3 j] :
    PresQ h.iU3 (OnBytes.Attention.claim5 h j) := by
  unfold OnBytes.Attention.claim5
  walkQ

open OnBytes.Attention in
/-- `Attention.valueProduct`: its forms and what it returns are good. -/
instance pq_Attention_valueProduct (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E) (isD : Bool)
    (tV : Nat) [Good h.iU3 h] [Good h.iU3 sc] [Good h.iU3 tS] [Good h.iU3 pt] [Good h.iU3 isD]
    [Good h.iU3 tV] :
    PresQ h.iU3 (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by
  unfold OnBytes.Attention.valueProduct
  walkQ

open OnBytes.Attention in
/-- `Attention.claim6`: its forms and what it returns are good. -/
instance pq_Attention_claim6 (h : Heard) [Good h.iU3 h] :
    PresQ h.iU3 (OnBytes.Attention.claim6 h) := by
  unfold OnBytes.Attention.claim6
  walkQ

open OnBytes.Attention in
/-- `Attention.claim7`: its forms and what it returns are good. -/
instance pq_Attention_claim7 (h : Heard) [Good h.iU3 h] :
    PresQ h.iU3 (OnBytes.Attention.claim7 h) := by
  unfold OnBytes.Attention.claim7
  walkQ

open OnBytes.Attention in
/-- `Attention.claim8`: its forms and what it returns are good. -/
instance pq_Attention_claim8 (h : Heard) [Good h.iU3 h] :
    PresQ h.iU3 (OnBytes.Attention.claim8 h) := by
  unfold OnBytes.Attention.claim8
  walkQ

/-! ## OnBytes/Model/Attention.lean -/

open OnBytes.Attention in
/-- `Attention.allJoined`: its forms and what it returns are good. -/
instance pq_Attention_allJoined (j : Joins) [Good t0 j] :
    PresQ t0 (OnBytes.Attention.allJoined j) := by
  unfold OnBytes.Attention.allJoined
  walkQ

open OnBytes.Attention in
/-- `Attention.paddingLaid`: its forms and what it returns are good. -/
instance pq_Attention_paddingLaid (S : Shape) (g : Forest.Heard) [Good t0 S] [Good t0 g] :
    PresQ t0 (OnBytes.Attention.paddingLaid S g) := by
  unfold OnBytes.Attention.paddingLaid
  walkQ

open OnBytes.Attention in
/-- `Attention.claims`: its forms and what it returns are good. -/
instance pq_Attention_claims (P : Plan) (h : Heard) [Good h.iU3 P] [Good h.iU3 h] :
    PresQ h.iU3 (OnBytes.Attention.claims P h) := by
  unfold OnBytes.Attention.claims
  walkQ

/-- The attention sub-proof's own claims: a walk, and every entry in the vector of the tables. -/
theorem attention_claims_adds (P : Attention.Plan) (h : Attention.Heard) (F G : Fork) (c c' : Ctx)
    (hg : Good h.iU3 h) (hr : Attention.claims P h F c = .ok (((), G), c')) :
    ∃ l, OnBytes.Road.Rows.Adds F l G ∧ ∀ a ∈ l, ∀ e ∈ a.ents.toList, e.tree = h.iU3 :=
  ((inferInstance : PresQ h.iU3 (Attention.claims P h)).out F c () G c' hr).1

end OnBytes.Tie.Pv.Tail.Forms

#print axioms OnBytes.Tie.Pv.Tail.Forms.attention_claims_adds
