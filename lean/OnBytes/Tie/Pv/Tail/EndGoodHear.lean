-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndGoodHear.lean: the forms that the attention sub-proof's check stores while it
hears the messages (`Attention.hear`, OnBytes/Model/Attention.lean) have entries in no array; so the
premise of `attention_claims_adds` (OnBytes/Tie/Pv/Tail/EndGoodAtt.lean) holds.

Definitions, and theorems with their proofs, each by a walk through a routine's text.

Main names: the instances of `HasGood` for the further records that hold forms while the messages
are heard; laws for the basic steps that take slots, fill them and read the channel; `walkH`: the
walk that also takes a record apart into its fields;
  `pq_` and a routine's name;
  `attention_hear_good`: what `Attention.hear` returns is good, for every array;
  `attention_adds`: where `Attention.hear P` has returned f and `Attention.claims P h` returns from
    F to G, for a record h made of f: there is a list l of forms with `Adds F l G`, and every entry
    of every member of l lies in array h.iU3.

Limits: those of OnBytes/Tie/Pv/Tail/EndGood.lean.


-/
import OnBytes.Tie.Pv.Tail.EndGoodAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Forms
open OnBytes OnBytes.Model

variable {t0 : Nat}

/-! ## Further records -/

/-- What is asked of a value of this type. -/
instance : HasGood Level := ⟨fun t r => HasGood.good t r.row⟩

/-- The record's field `row`. -/
instance good_Level_row (r : Level) [h : Good t0 r] : Good t0 r.row := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Forest.Tie := ⟨fun t r => HasGood.good t r.rows ∧ HasGood.good t r.cT⟩

/-- The record's field `rows`. -/
instance good_Tie_rows (r : Forest.Tie) [h : Good t0 r] : Good t0 r.rows := ⟨h.out.1⟩

/-- The record's field `cT`. -/
instance good_Tie_cT (r : Forest.Tie) [h : Good t0 r] : Good t0 r.cT := ⟨h.out.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Forest.TieStep := ⟨fun t r => HasGood.good t r.rows⟩

/-- The record's field `rows`. -/
instance good_TieStep_rows (r : Forest.TieStep) [h : Good t0 r] : Good t0 r.rows := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Forest.Descent := ⟨fun t r => HasGood.good t r.rows ∧ HasGood.good t r.form⟩

/-- The record's field `rows`. -/
instance good_Descent_rows (r : Forest.Descent) [h : Good t0 r] : Good t0 r.rows := ⟨h.out.1⟩

/-- The record's field `form`. -/
instance good_Descent_form (r : Forest.Descent) [h : Good t0 r] : Good t0 r.form := ⟨h.out.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Attention.First :=
  ⟨fun t r => HasGood.good t r.g ∧ HasGood.good t r.scores ∧ HasGood.good t r.d ∧
    HasGood.good t r.x⟩

/-- The record's field `g`. -/
instance good_First_g (r : Attention.First) [h : Good t0 r] : Good t0 r.g := ⟨h.out.1⟩

/-- The record's field `scores`. -/
instance good_First_scores (r : Attention.First) [h : Good t0 r] : Good t0 r.scores := ⟨h.out.2.1⟩

/-- The record's field `d`. -/
instance good_First_d (r : Attention.First) [h : Good t0 r] : Good t0 r.d := ⟨h.out.2.2.1⟩

/-- The record's field `x`. -/
instance good_First_x (r : Attention.First) [h : Good t0 r] : Good t0 r.x := ⟨h.out.2.2.2⟩

/-! ## Further steps -/

/-- A good form, with the class unfolded. -/
theorem inU_of_good (a : Aff) [h : Good t0 a] : InU t0 a := h.out

/-- A good array of forms, with the class unfolded. -/
theorem allU_of_good (a : Array Aff) [h : Good t0 a] : ∀ x ∈ a.toList, InU t0 x := h.out

/-- A step on the state that returns a value of a type of which nothing is asked. -/
theorem pq_take {α : Type} [HasGood α] [Unasked α] (f : Fork → Option (α × Fork))
    (hf : ∀ F a G, f F = some (a, G) → AddsIn t0 F G) : PresQ t0 (SubM.take f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨⟨a1, G1⟩, hx, e⟩ := (OnBytes.PscRun.take_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact ⟨hf F _ _ hx, Unasked.all _ _⟩⟩

/-- `SubM.takeSlots` adds no claim. -/
instance pq_takeSlots (n : Nat) : PresQ t0 (SubM.takeSlots n) :=
  pq_take _ fun F a G h => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact AddsIn.ofKeeps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SubM.hide` adds no claim. -/
instance pq_hide (j : Nat) (y f : E) : PresQ t0 (SubM.hide j y f) :=
  pq_change _ fun _ _ h => AddsIn.ofKeeps (OnBytes.Road.Rows.hide_keeps h)

/-- `SubM.owe` adds no claim. -/
instance pq_owe (what : String) : PresQ t0 (SubM.owe what) :=
  pq_take _ fun F a G h => by
    have e2 : (F.owe what).2 = G := congrArg Prod.snd (Option.some.inj h)
    rw [← e2]
    exact AddsIn.ofKeeps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SubM.read` adds no claim. -/
instance pq_read (n : Nat) : PresQ t0 (SubM.read n) := pq_liftS _

/-- `SubM.readSum` adds no claim. -/
instance pq_readSum : PresQ t0 SubM.readSum := pq_liftS _

/-- `SubM.answer` adds no claim. -/
instance pq_answer (r : RoundName) : PresQ t0 (SubM.answer r) := pq_liftS _

/-- `SubM.answerNotZero` adds no claim. -/
instance pq_answerNotZero (r : RoundName) : PresQ t0 (SubM.answerNotZero r) := pq_liftS _

/-- `SubM.point` adds no claim. -/
instance pq_point (r : RoundName) (n : Nat) : PresQ t0 (SubM.point r n) := pq_liftS _

/-- `SubM.batch` adds no claim. -/
instance pq_batch (rows : Nat) : PresQ t0 (SubM.batch rows) := pq_liftS _

/-- `SubM.empty` adds no claim. -/
instance pq_emptyR (r : RoundName) : PresQ t0 (SubM.empty r) := pq_liftS _

/-- What a layer of a product tree hands down: slots alone. -/
instance good_handDown (o : Level) : Good t0 o.handDown := by
  unfold Level.handDown
  infer_instance

/-- One step of the walk that also takes a record apart into its fields. -/
macro "walkH_step" : tactic => `(tactic| first
  | exact inferInstance | exact Good.out | exact inU_of_good _ | exact allU_of_good _
  | refine And.intro ?_ ?_ | dsimp only | simp only [HasGood.good]
  | refine @inU_of_good _ _ (good_foldl _ ?_ _ _ ?_ ?_) | walkQ_step | refine Good.mk ?_)

/-- The walk that also takes a record apart into its fields. -/
macro "walkH" : tactic => `(tactic| repeat' walkH_step)

/-- `SubM.claimsIn` adds no claim. -/
instance pq_claimsIn (n : Nat) : PresQ t0 (SubM.claimsIn n) := by
  unfold SubM.claimsIn
  walkH

/-! ## OnBytes/Model/Psc.lean -/

open OnBytes.Model in
/-- `pscBeginAt`: its forms and what it returns are good. -/
instance pq_Model_pscBeginAt (target : E) [Good t0 target] :
    PresQ t0 (OnBytes.Model.pscBeginAt target) := by
  unfold OnBytes.Model.pscBeginAt
  walkH

open OnBytes.Model in
/-- `pscBegin`: its forms and what it returns are good. -/
instance pq_Model_pscBegin (C : Aff) [Good t0 C] :
    PresQ t0 (OnBytes.Model.pscBegin C) := by
  unfold OnBytes.Model.pscBegin
  walkH

open OnBytes.Model in
/-- `pscRound`: its forms and what it returns are good. -/
instance pq_Model_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) [Good t0 p] [Good t0 w]
    [Good t0 draw] :
    PresQ t0 (OnBytes.Model.pscRound p w draw) := by
  unfold OnBytes.Model.pscRound
  walkH

open OnBytes.Model in
/-- `roundIn`: its forms and what it returns are good. -/
instance pq_Model_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) [Good t0 form]
    [Good t0 p] [Good t0 z] [Good t0 degree] :
    PresQ t0 (OnBytes.Model.roundIn form p z degree) := by
  unfold OnBytes.Model.roundIn
  walkH

open OnBytes.Model in
/-- `pscEnds`: its forms and what it returns are good. -/
instance pq_Model_pscEnds (p : Psc) (degreeInY n : Nat) [Good t0 p] [Good t0 degreeInY]
    [Good t0 n] :
    PresQ t0 (OnBytes.Model.pscEnds p degreeInY n) := by
  unfold OnBytes.Model.pscEnds
  walkH

open OnBytes.Model in
/-- `levelRounds`: its forms and what it returns are good. -/
instance pq_Model_levelRounds (mu : Nat) (rho : Array E) :
    ∀ (l : List Nat) (r : Array E) (p : Psc) [Good t0 p],
      PresQ t0 (OnBytes.Model.levelRounds mu rho l r p)
  | [], r, p, _ => by
    unfold OnBytes.Model.levelRounds
    walkH
  | t :: l, r, p, _ => by
    have := pq_Model_levelRounds mu rho l
    unfold OnBytes.Model.levelRounds
    walkH

open OnBytes.Model in
/-- `levelIn`: its forms and what it returns are good. -/
instance pq_Model_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) [Good t0 mu]
    [Good t0 rho] [Good t0 C] [Good t0 order] :
    PresQ t0 (OnBytes.Model.levelIn mu rho C order) := by
  unfold OnBytes.Model.levelIn
  walkH

/-! ## OnBytes/Model/Look.lean -/

open OnBytes.Model in
/-- `roundsIn`: its forms and what it returns are good. -/
instance pq_Model_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) [Good t0 form]
    [Good t0 p] [Good t0 zs] :
    PresQ t0 (OnBytes.Model.roundsIn form p zs) := by
  unfold OnBytes.Model.roundsIn
  walkH

open OnBytes.Model.Forest in
/-- `Forest.draws`: its forms and what it returns are good. -/
instance pq_Model_Forest_draws (h : Shape) [Good t0 h] :
    PresQ t0 (OnBytes.Model.Forest.draws h) := by
  unfold OnBytes.Model.Forest.draws
  walkH

open OnBytes.Model.Forest in
/-- `Forest.tieStep`: its forms and what it returns are good. -/
instance pq_Model_Forest_tieStep (a : E) (s : TieStep) (j : Nat) [Good t0 a] [Good t0 s]
    [Good t0 j] :
    PresQ t0 (OnBytes.Model.Forest.tieStep a s j) := by
  unfold OnBytes.Model.Forest.tieStep
  walkH

open OnBytes.Model.Forest in
/-- `Forest.tie`: its forms and what it returns are good. -/
instance pq_Model_Forest_tie (a : E) [Good t0 a] :
    PresQ t0 (OnBytes.Model.Forest.tie a) := by
  unfold OnBytes.Model.Forest.tie
  walkH

open OnBytes.Model.Forest in
/-- `Forest.level`: its forms and what it returns are good. -/
instance pq_Model_Forest_level (s : Descent) (mu : Nat) (order : List Nat) [Good t0 s] [Good t0 mu]
    [Good t0 order] :
    PresQ t0 (OnBytes.Model.Forest.level s mu order) := by
  unfold OnBytes.Model.Forest.level
  walkH

open OnBytes.Model.Forest in
/-- `Forest.pad`: its forms and what it returns are good. -/
instance pq_Model_Forest_pad (calls : Array Call) (pub : Array Nat) (lid : Nat) [Good t0 calls]
    [Good t0 pub] [Good t0 lid] :
    PresQ t0 (OnBytes.Model.Forest.pad calls pub lid) := by
  unfold OnBytes.Model.Forest.pad
  walkH

/-! ## OnBytes/Model/AttentionSums.lean -/

open OnBytes.Attention in
/-- `Attention.sc3Rounds`: its forms and what it returns are good. -/
instance pq_Attention_sc3Rounds :
    ∀ (n : Nat) (p : Psc) (r : Array E) [Good t0 p], PresQ t0 (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r, _ => by
    unfold OnBytes.Attention.sc3Rounds
    walkH
  | n + 1, p, r, _ => by
    have := pq_Attention_sc3Rounds n
    unfold OnBytes.Attention.sc3Rounds
    walkH

open OnBytes.Attention in
/-- `Attention.sc3In`: its forms and what it returns are good. -/
instance pq_Attention_sc3In (nv nb : Nat) (start : Model.Aff) [Good t0 nv] [Good t0 nb]
    [Good t0 start] :
    PresQ t0 (OnBytes.Attention.sc3In nv nb start) := by
  unfold OnBytes.Attention.sc3In
  walkH

open OnBytes.Attention in
/-- `Attention.sc3Shown`: its forms and what it returns are good. -/
instance pq_Attention_sc3Shown (o : Sc3) (W : Array E) :
    ∀ (n b : Nat) (s : E), PresQ t0 (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    unfold OnBytes.Attention.sc3Shown
    walkH
  | n + 1, b, s => by
    have := pq_Attention_sc3Shown o W n
    unfold OnBytes.Attention.sc3Shown
    walkH

open OnBytes.Attention in
/-- `Attention.sc3Row`: its forms and what it returns are good. -/
instance pq_Attention_sc3Row (o : Sc3) (W : Array E) [Good t0 o] [Good t0 W] :
    PresQ t0 (OnBytes.Attention.sc3Row o W) := by
  unfold OnBytes.Attention.sc3Row
  walkH

open OnBytes.Attention in
/-- `Attention.scdRounds`: its forms and what it returns are good. -/
instance pq_Attention_scdRounds :
    ∀ (ds : List Nat) (p : Psc) (r : Array E) [Good t0 p],
      PresQ t0 (OnBytes.Attention.scdRounds ds p r)
  | [], p, r, _ => by
    unfold OnBytes.Attention.scdRounds
    walkH
  | d :: ds, p, r, _ => by
    have := pq_Attention_scdRounds ds
    unfold OnBytes.Attention.scdRounds
    walkH

open OnBytes.Attention in
/-- `Attention.scdIn`: its forms and what it returns are good. -/
instance pq_Attention_scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Model.Aff)
    [Good t0 degrees] [Good t0 degreeInY] [Good t0 n] [Good t0 start] :
    PresQ t0 (OnBytes.Attention.scdIn degrees degreeInY n start) := by
  unfold OnBytes.Attention.scdIn
  walkH

open OnBytes.Attention in
/-- `Attention.scdRow`: its forms and what it returns are good. -/
instance pq_Attention_scdRow (o : Scd) (s0 : E) [Good t0 o] [Good t0 s0] :
    PresQ t0 (OnBytes.Attention.scdRow o s0) := by
  unfold OnBytes.Attention.scdRow
  walkH

/-! ## OnBytes/Model/AttentionScores.lean -/

open OnBytes.Attention in
/-- `Attention.planeUnit`: its forms and what it returns are good. -/
instance pq_Attention_planeUnit (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg)
    [Good t0 S] [Good t0 zk] [Good t0 u] :
    PresQ t0 (OnBytes.Attention.planeUnit S zk u) := by
  unfold OnBytes.Attention.planeUnit
  walkH

open OnBytes.Attention in
/-- `Attention.planeUnits`: its forms and what it returns are good. -/
instance pq_Attention_planeUnits (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes : Array PlaneClaim),
      PresQ t0 (OnBytes.Attention.planeUnits S zk us planes)
  | [], planes => by
    unfold OnBytes.Attention.planeUnits
    walkH
  | u :: us, planes => by
    have := pq_Attention_planeUnits S zk us
    unfold OnBytes.Attention.planeUnits
    walkH

open OnBytes.Attention in
/-- `Attention.scoreUnit`: its forms and what it returns are good. -/
instance pq_Attention_scoreUnit (S : Shape) (zk : Array (Array E)) (claim : Nat)
    (u : Nat × ACall × Seg) [Good t0 S] [Good t0 zk] [Good t0 claim] [Good t0 u] :
    PresQ t0 (OnBytes.Attention.scoreUnit S zk claim u) := by
  unfold OnBytes.Attention.scoreUnit
  walkH

open OnBytes.Attention in
/-- `Attention.scoreUnits`: its forms and what it returns are good. -/
instance pq_Attention_scoreUnits (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes : Array PlaneClaim)
      (stored : Array Score) [Good t0 stored],
      PresQ t0 (OnBytes.Attention.scoreUnits S zk us planes stored)
  | [], planes, stored, _ => by
    unfold OnBytes.Attention.scoreUnits
    walkH
  | u :: us, planes, stored, _ => by
    have := pq_Attention_scoreUnits S zk us
    unfold OnBytes.Attention.scoreUnits
    walkH

open OnBytes.Attention in
/-- `Attention.scores`: its forms and what it returns are good. -/
instance pq_Attention_scores (S : Shape) (zk : Array (Array E)) [Good t0 S] [Good t0 zk] :
    PresQ t0 (OnBytes.Attention.scores S zk) := by
  unfold OnBytes.Attention.scores
  walkH

/-! ## OnBytes/Model/AttentionDivide.lean -/

open OnBytes.Attention in
instance good_Attention_weightedSum (n : Nat) (w : Array E) (form : Nat → Aff)
    [∀ b, Good t0 (form b)] :
    Good t0 (OnBytes.Attention.weightedSum n w form) := by
  unfold OnBytes.Attention.weightedSum
  walkH

open OnBytes.Attention in
/-- `Attention.coinsOm`: its forms and what it returns are good. -/
instance pq_Attention_coinsOm (n : Nat) [Good t0 n] :
    PresQ t0 (OnBytes.Attention.coinsOm n) := by
  unfold OnBytes.Attention.coinsOm
  walkH

open OnBytes.Attention in
/-- `Attention.productIn`: its forms and what it returns are good. -/
instance pq_Attention_productIn (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat)
    [Good t0 S] [Good t0 pwW] [Good t0 zgW] [Good t0 ziW] [Good t0 sZO] :
    PresQ t0 (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by
  unfold OnBytes.Attention.productIn
  walkH

open OnBytes.Attention in
/-- `Attention.valueBelowIn`: its forms and what it returns are good. -/
instance pq_Attention_valueBelowIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat)
    [Good t0 S] [Good t0 pwW] [Good t0 zgW] [Good t0 zihi] [Good t0 sCl] :
    PresQ t0 (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by
  unfold OnBytes.Attention.valueBelowIn
  walkH

open OnBytes.Attention in
/-- `Attention.valueOnIn`: its forms and what it returns are good. -/
instance pq_Attention_valueOnIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat)
    [Good t0 S] [Good t0 pwW] [Good t0 zgW] [Good t0 zihi] [Good t0 sCl1] :
    PresQ t0 (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by
  unfold OnBytes.Attention.valueOnIn
  walkH

open OnBytes.Attention in
/-- `Attention.divide`: its forms and what it returns are good. -/
instance pq_Attention_divide (S : Shape) (zk : Array (Array E)) [Good t0 S] [Good t0 zk] :
    PresQ t0 (OnBytes.Attention.divide S zk) := by
  unfold OnBytes.Attention.divide
  walkH

open OnBytes.Attention in
/-- `Attention.scoreAtIndexIn`: its forms and what it returns are good. -/
instance pq_Attention_scoreAtIndexIn (S : Shape) (tg ti : Array E) [Good t0 S] [Good t0 tg]
    [Good t0 ti] :
    PresQ t0 (OnBytes.Attention.scoreAtIndexIn S tg ti) := by
  unfold OnBytes.Attention.scoreAtIndexIn
  walkH

open OnBytes.Attention in
/-- `Attention.keyTerm`: its forms and what it returns are good. -/
instance pq_Attention_keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) [Good t0 S]
    [Good t0 sKC] [Good t0 pj] [Good t0 w] [Good t0 b] :
    PresQ t0 (OnBytes.Attention.keyTerm S sKC pj w b) := by
  unfold OnBytes.Attention.keyTerm
  walkH

open OnBytes.Attention in
/-- `Attention.keyAtIndexIn`: its forms and what it returns are good. -/
instance pq_Attention_keyAtIndexIn (S : Shape) (scF : Sc3) [Good t0 S] [Good t0 scF] :
    PresQ t0 (OnBytes.Attention.keyAtIndexIn S scF) := by
  unfold OnBytes.Attention.keyAtIndexIn
  walkH

open OnBytes.Attention in
/-- `Attention.bitsIn`: its forms and what it returns are good. -/
instance pq_Attention_bitsIn (S : Shape) (tk tbg tbi : Array E) [Good t0 S] [Good t0 tk]
    [Good t0 tbg] [Good t0 tbi] :
    PresQ t0 (OnBytes.Attention.bitsIn S tk tbg tbi) := by
  unfold OnBytes.Attention.bitsIn
  walkH

open OnBytes.Attention in
/-- `Attention.attain`: its forms and what it returns are good. -/
instance pq_Attention_attain (S : Shape) [Good t0 S] :
    PresQ t0 (OnBytes.Attention.attain S) := by
  unfold OnBytes.Attention.attain
  walkH

/-! ## OnBytes/Model/Attention.lean -/

open OnBytes.Attention in
/-- `Attention.hear`: its forms and what it returns are good. -/
instance pq_Attention_hear (P : Plan) [Good t0 P] :
    PresQ t0 (OnBytes.Attention.hear P) := by
  unfold OnBytes.Attention.hear
  walkH

/-- What `Attention.hear` returns is good, for every array. -/
theorem attention_hear_good (P : Attention.Plan) (f : Attention.First) (F G : Fork) (c c' : Ctx)
    (hr : Attention.hear P F c = .ok ((f, G), c')) : Good t0 f :=
  ⟨((inferInstance : PresQ t0 (Attention.hear P)).out F c f G c' hr).2⟩

/-- The attention sub-proof's own claims, from the runs of the hearing and of the claims. -/
theorem attention_adds (P : Attention.Plan) (f : Attention.First) (S : Attention.Shape)
    (t : Attention.Tables) (iU3 : Nat) (F1 F2 F G : Fork) (c1 c2 c c' : Ctx)
    (hh : Attention.hear P F1 c1 = .ok ((f, F2), c2))
    (hr : Attention.claims P
      { S := S, g := f.g, planes := f.planes, scores := f.scores, d := f.d, x := f.x, t := t,
        iU3 := iU3 } F c = .ok (((), G), c')) :
    ∃ l, OnBytes.Road.Rows.Adds F l G ∧ ∀ a ∈ l, ∀ e ∈ a.ents.toList, e.tree = iU3 := by
  have hf : Good iU3 f := attention_hear_good P f F1 F2 c1 c2 hh
  exact attention_claims_adds P _ F G c c' ⟨hf.out⟩ hr

end OnBytes.Tie.Pv.Tail.Forms

#print axioms OnBytes.Tie.Pv.Tail.Forms.attention_hear_good
#print axioms OnBytes.Tie.Pv.Tail.Forms.attention_adds
