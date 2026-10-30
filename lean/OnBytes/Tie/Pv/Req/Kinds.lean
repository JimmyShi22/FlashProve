-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Req/Kinds.lean: the three kinds of sub-proof in the frame of a proof's first chain:
their routines meet the frame's premise, and what they lay behind moment 0.

OnBytes/Tie/Pv/Req/Frame.lean cuts the plan of the first chain into stretches under one premise on
the sub-proofs' routines (SubOK). Here that premise is proved of layerRounds, attentionRounds and
headRounds (OnBytes/Params/SubRounds.lean), at every moment. And the stretch behind moment 0 is cut
in two: the lookup on the calls, then the sub-proof's own rounds.

Main names:
  `adds_inj`: two lists that were added to the same rounds with the same result are one list.
  `Fixed st x L`: from every idle state x ends well only in an idle state, and adds just L.
    `fixed_att`, `fixed_lay`: from the two forms of AddsW (OnBytes/Tie/Pv/Att/PlanCalc.lean,
    OnBytes/Tie/Pv/Lay/PlanBounds.lean). `laid_fixed`: whatever such a routine has laid is L.
  `laid_bind`: what two routines in a row have laid is what each has laid.
  `keeps_attention`, `keeps_layer`, `keeps_head`: the three routines keep an idle state, at every
    moment (with `shuts_psc`, `keeps_small`, `keeps_headOwn`, `keeps_headEnd` and others).
  `KindAt sub l`: the rounds of link number l are those of one of the three kinds.
  `subOK_kinds`: where every link is of one of the three kinds and nothing is sent behind the links,
    SubOK holds.
  `laid_att0`, `laid_lay0`: behind moment 0 an attention link has what the lookup has laid and then
    the list attRounds (OnBytes/Tie/Pv/Att/PlanOwnW.lean); a link of layers the list ownRounds
    (OnBytes/Tie/Pv/Lay/PlanBounds.lean). `laid_head0`: the head's link has what the lookup has laid
    and then what planHeadOwn has laid.

Limits: the lookup's rounds and the head's own rounds are not listed. That the sub-proofs of a
configuration are of these kinds is a premise (KindAt). Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Req.Frame
import OnBytes.Tie.Pv.Att.PlanOwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Req

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Tail (Idle Shut Reads plan_bind needs_ok)
open OnBytes.Tie.Pv.Att.Plan (AddsW At att_addsW attRounds)

/-! ### Lists that are fixed by the setting -/

/-- Two lists that were added to the same rounds with the same result are one list. -/
theorem adds_inj {p q : PlanState} {F G : List PlanRound} (h : Adds p q F) (k : Adds p q G) :
    F = G := by
  unfold Adds at h k
  rw [h] at k
  have e := congrArg Array.toList k
  simpa using e

theorem at_of_idle {st : Setting} {p : PlanState} (h : Idle st p) : At st 0 p :=
  ⟨h.set, h.scope, h.bytes, h.roots, h.answers⟩

theorem idle_of_at {st : Setting} {p : PlanState} (h : At st 0 p) : Idle st p :=
  ⟨h.set, h.scope, h.bytes, h.roots, h.answers⟩

/-- From every idle state x ends well only in an idle state, and adds just the rounds L. -/
def Fixed (st : Setting) (x : Planning Unit) (L : List PlanRound) : Prop :=
  ∀ p q, Idle st p → x p = .ok ((), q) → Idle st q ∧ Adds p q L

theorem fixed_att {st : Setting} {x : Planning Unit} {L : List PlanRound}
    (h : AddsW st 0 0 x L) : Fixed st x L := fun p q hp hq =>
  ⟨idle_of_at (h p q (at_of_idle hp) hq).1, (h p q (at_of_idle hp) hq).2⟩

theorem fixed_lay {st : Setting} {x : Planning Unit} {L : List PlanRound}
    (h : Lay.AddsW st 0 0 x L) : Fixed st x L := fun p q hp hq => by
  obtain ⟨a, e⟩ := h p q ⟨hp.set, hp.scope, hp.bytes, hp.roots, hp.answers⟩ hq
  exact ⟨⟨a.set, a.scope, a.bytes, a.roots, a.answers⟩, e⟩

/-- Whatever a routine with a fixed list has laid is that list. -/
theorem laid_fixed {st : Setting} {x : Planning Unit} {L F : List PlanRound}
    (h : Fixed st x L) (k : LaidIdle st x F) : F = L := by
  obtain ⟨p, _, q, hp, hq, e⟩ := k
  exact adds_inj e (h p q hp hq).2

theorem keeps_fixed {st : Setting} {x : Planning Unit} {L : List PlanRound}
    (h : Fixed st x L) : Keeps st x := fun p _ q hp hq => ⟨(h p q hp hq).1, L, (h p q hp hq).2⟩

/-- What two routines in a row have laid is what each has laid, one list behind the other. -/
theorem laid_bind {st : Setting} {x y : Planning Unit} {F : List PlanRound} (hx : Keeps st x)
    (hy : Keeps st y) (k : LaidIdle st (x >>= fun _ => y) F) :
    ∃ F1 F2, F = F1 ++ F2 ∧ LaidIdle st x F1 ∧ LaidIdle st y F2 := by
  obtain ⟨p, _, q, hp, hq, e⟩ := k
  obtain ⟨_, m, g1, g2⟩ := plan_bind hq
  obtain ⟨a1, F1, e1⟩ := hx p _ m hp g1
  obtain ⟨_, F2, e2⟩ := hy m _ q a1 g2
  exact ⟨F1, F2, adds_inj e (e1.trans e2), ⟨p, _, m, hp, g1, e1⟩, ⟨m, _, q, a1, g2, e2⟩⟩

/-! ### The sub-proofs' routines keep an idle state -/

section Keep
variable (st : Setting)

theorem keeps_forest (z : ForestSize) : Keeps st (planForest z) :=
  keeps_of_lay st (Lay.keeps_forest st z)

theorem keeps_psc (z : PscSize) : Keeps st (planPsc z) := keeps_of_lay st (Lay.keeps_psc st 0 z)

theorem keeps_pscRounds (s' : Setting) : ∀ g : List Nat, Keeps st (planPscRounds s' g)
  | [] => keeps_pure ()
  | _ :: g =>
    (Runs.then (runs_scalars st _) fun _ =>
      Shuts.then (shuts_close st _ _ _ _) fun _ => keeps_pscRounds s' g).keeps

/-- A sumcheck shuts, whatever is open before it. -/
theorem shuts_psc (z : PscSize) : Shuts st (planPsc z) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun s' =>
    Runs.then (runs_scalars st 1) fun _ =>
      Shuts.then (shuts_close st _ _ _ _) fun _ =>
        Keeps.bind (keeps_pscRounds st s' z.degree) fun _ =>
          Keeps.ite
            (Runs.then (runs_scalars st _) fun _ =>
              Runs.then (shuts_close st _ _ _ _).runs fun _ =>
                Runs.then (runs_scalars st _) fun _ => shuts_none st _).keeps
            (keeps_pure ())

theorem shuts_zero (v : Nat) : Shuts st (planZero v) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ => shuts_close st _ _ _ _

theorem shuts_line : Shuts st planLine :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ => shuts_close st _ _ _ _

theorem shuts_tokenSum (lt shown deg more : Nat) : Shuts st (planTokenSum lt shown deg more) :=
  Runs.then (runs_scalars st 1) fun _ => shuts_psc st _

theorem shuts_rng (columns : Nat) : Shuts st (planRng columns) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ =>
    Runs.then (runs_of_reads reads_scope) fun _ =>
      Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ => shuts_close st _ _ _ _

theorem keeps_small (x : SmallSize) (which : Nat) : Keeps st (planSmall x which) :=
  Keeps.ite
    (Keeps.bind (keeps_of_reads Tail.reads_setting) fun _ =>
      Keeps.bind (keeps_of_reads reads_scope) fun _ =>
        Keeps.bind (keeps_of_reads (Tail.reads_needs _ _)) fun _ => (shuts_rng st _).keeps)
    (Keeps.bind (keeps_of_reads (Tail.reads_needs _ _)) fun _ => keeps_forest st _)

theorem keeps_attOwn (y : AttentionRounds) : Keeps st (planAttentionOwn y) :=
  keeps_fixed (fixed_att (att_addsW st y))

theorem keeps_layOwn (y : LayerRounds) : Keeps st (planLayerOwn y) :=
  keeps_fixed (fixed_lay (Lay.own_addsW st y))

theorem keeps_headOwn (y : HeadRounds) : Keeps st (planHeadOwn y) :=
  (Shuts.then (shuts_zero st _) fun _ =>
    (Runs.then (runs_scalars st _) fun _ =>
      Shuts.then (shuts_batSigma st _) fun _ =>
        Keeps.bind (shuts_psc st _).keeps fun _ =>
          Keeps.bind (shuts_line st).keeps fun _ =>
            (Runs.then (runs_scalars st _) fun _ =>
              Shuts.then (shuts_batSigma st _) fun _ =>
                Keeps.bind (shuts_tokenSum st _ _ _ _).keeps fun _ =>
                  Keeps.bind (shuts_tokenSum st _ _ _ _).keeps fun _ =>
                    (shuts_tokenSum st _ _ _ _).keeps).keeps).keeps).keeps

theorem keeps_headEnd (y : HeadRounds) : Keeps st (planHeadEnd y) :=
  Keeps.bind (shuts_batSigma st _).keeps fun _ =>
    Keeps.bind (shuts_psc st _).keeps fun _ => (shuts_batSigma st _).keeps

theorem keeps_attention (look : ForestSize) (y : AttentionRounds) (x : SmallSize) (m : Nat) :
    Keeps st (attentionRounds look y x m) :=
  have j2 : Keeps st (if (m == 2) = true then planBatSigma y.rows else pure PUnit.unit) :=
    Keeps.ite (shuts_batSigma st _).keeps (keeps_pure _)
  have j1 := Keeps.ite (c := 1 ≤ m) (Keeps.bind (keeps_small st x (m - 1)) fun _ => j2)
    (Keeps.bind (keeps_pure PUnit.unit) fun _ => j2)
  Keeps.ite (Keeps.bind (keeps_forest st look) fun _ => Keeps.bind (keeps_attOwn st y) fun _ => j1)
    (Keeps.bind (keeps_pure PUnit.unit) fun _ => j1)

theorem keeps_layer (look : ForestSize) (y : LayerRounds) (x : SmallSize) (claims m : Nat) :
    Keeps st (layerRounds look y x claims m) :=
  Keeps.ite (Keeps.bind (keeps_forest st look) fun _ => keeps_layOwn st y)
    (Keeps.bind (keeps_small st x _) fun _ =>
      Keeps.ite (shuts_batSigma st _).keeps (keeps_pure ()))

theorem keeps_head (look : ForestSize) (y : HeadRounds) (x : SmallSize) (m : Nat) :
    Keeps st (headRounds look y x m) :=
  have j2 : Keeps st (if (m == 2) = true then planHeadEnd y else pure PUnit.unit) :=
    Keeps.ite (keeps_headEnd st y) (keeps_pure _)
  have j1 := Keeps.ite (c := 1 ≤ m) (Keeps.bind (keeps_small st x (m - 1)) fun _ => j2)
    (Keeps.bind (keeps_pure PUnit.unit) fun _ => j2)
  Keeps.ite (Keeps.bind (keeps_forest st look) fun _ => Keeps.bind (keeps_headOwn st y) fun _ => j1)
    (Keeps.bind (keeps_pure PUnit.unit) fun _ => j1)

end Keep

/-! ### The premise on the sub-proofs, for the three kinds -/

/-- The rounds of link number l are those of one of the three kinds of sub-proof. -/
inductive KindAt (sub : Subproofs) (l : Nat) : Prop
  | layers (look : ForestSize) (y : LayerRounds) (x : SmallSize) (claims : Nat)
      (h : ∀ m, sub.plan l m = layerRounds look y x claims m)
  | attention (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
      (h : ∀ m, sub.plan l m = attentionRounds look y x m)
  | head (look : ForestSize) (y : HeadRounds) (x : SmallSize)
      (h : ∀ m, sub.plan l m = headRounds look y x m)

theorem shut_of_idle {st : Setting} {p : PlanState} (h : Idle st p) : Shut st p :=
  ⟨h.set, h.bytes, h.roots, h.answers⟩

/-- Where every link is of one of the three kinds and nothing is sent behind the links, the premise
of req_from and first_plan holds. -/
theorem subOK_kinds (st : Setting) (sub : Subproofs) (hk : ∀ l, KindAt sub l)
    (ha : sub.afterLinks = pure ()) : SubOK st sub where
  plan := fun l m p q hp h => by
    have k : Keeps st (sub.plan l m) := by
      cases hk l with
      | layers look y x claims e => rw [e m]; exact keeps_layer st look y x claims m
      | attention look y x e => rw [e m]; exact keeps_attention st look y x m
      | head look y x e => rw [e m]; exact keeps_head st look y x m
    exact ⟨shut_of_idle (k p _ q hp h).1, (k p _ q hp h).2⟩
  after := fun p q hp h => by
    rw [ha] at h
    exact ⟨shut_of_idle (keeps_pure (st := st) () p _ q hp h).1,
      (keeps_pure (st := st) () p _ q hp h).2⟩

/-! ### Behind moment 0: the lookup's rounds, then the sub-proof's own -/

section Zero
variable {st : Setting}

theorem laid_att0 (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
    {R : List PlanRound} (k : LaidIdle st (attentionRounds look y x 0) R) :
    ∃ F, R = F ++ attRounds st y ∧ LaidIdle st (planForest look) F := by
  obtain ⟨p, _, q, hp, hq, e⟩ := k
  have h' : (planForest look >>= fun _ => planAttentionOwn y >>= fun _ =>
      (pure () : Planning Unit) >>= fun _ => (pure () : Planning Unit)) p = .ok ((), q) := hq
  obtain ⟨_, m1, g1, k1⟩ := plan_bind h'
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain rfl : m2 = q := (Prod.mk.inj (Except.ok.inj k2)).2
  obtain ⟨a1, F, e1⟩ := keeps_forest st look p _ m1 hp g1
  obtain ⟨_, e2⟩ := fixed_att (att_addsW st y) m1 m2 a1 g2
  exact ⟨F, adds_inj e (e1.trans e2), p, _, m1, hp, g1, e1⟩

theorem laid_lay0 (look : ForestSize) (y : LayerRounds) (x : SmallSize) (claims : Nat)
    {R : List PlanRound} (k : LaidIdle st (layerRounds look y x claims 0) R) :
    ∃ F, R = F ++ Lay.ownRounds st y ∧ LaidIdle st (planForest look) F := by
  obtain ⟨p, _, q, hp, hq, e⟩ := k
  have h' : (planForest look >>= fun _ => planLayerOwn y) p = .ok ((), q) := hq
  obtain ⟨F1, F2, e', l1, l2⟩ := laid_bind (keeps_forest st look) (keeps_layOwn st y)
    ⟨p, _, q, hp, h', e⟩
  exact ⟨F1, by rw [e', laid_fixed (fixed_lay (Lay.own_addsW st y)) l2], l1⟩

theorem laid_head0 (look : ForestSize) (y : HeadRounds) (x : SmallSize)
    {R : List PlanRound} (k : LaidIdle st (headRounds look y x 0) R) :
    ∃ F G, R = F ++ G ∧ LaidIdle st (planForest look) F ∧ LaidIdle st (planHeadOwn y) G := by
  obtain ⟨p, _, q, hp, hq, e⟩ := k
  have h' : (planForest look >>= fun _ => planHeadOwn y >>= fun _ =>
      (pure () : Planning Unit) >>= fun _ => (pure () : Planning Unit)) p = .ok ((), q) := hq
  obtain ⟨_, m1, g1, k1⟩ := plan_bind h'
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain rfl : m2 = q := (Prod.mk.inj (Except.ok.inj k2)).2
  obtain ⟨a1, F, e1⟩ := keeps_forest st look p _ m1 hp g1
  obtain ⟨_, G, e2⟩ := keeps_headOwn st y m1 _ m2 a1 g2
  exact ⟨F, G, adds_inj e (e1.trans e2), ⟨p, _, m1, hp, g1, e1⟩, ⟨m1, _, m2, a1, g2, e2⟩⟩

end Zero

end OnBytes.Tie.Pv.Req

#print axioms OnBytes.Tie.Pv.Req.subOK_kinds
#print axioms OnBytes.Tie.Pv.Req.laid_att0
#print axioms OnBytes.Tie.Pv.Req.laid_lay0
#print axioms OnBytes.Tie.Pv.Req.laid_head0
