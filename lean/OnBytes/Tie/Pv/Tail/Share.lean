-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/Share.lean: the rounds that the planner lays for the smallness test's share of a
link of a request's first chain, as one list, from an idle state to an idle state.

A link of that chain has three moments. After moment 0 come the sub-proof's lookup and its own
rounds. The rest of the link belongs to the smallness test: the planner's routine for the frame
(reqMoments, OnBytes/Params/DeriveReq.lean), run from moment 1 for two moments, lays: the sending of
moment 1's oracle messages; the sub-proof's rounds after moment 1; the sending of moment 2's; the
sub-proof's rounds after moment 2. After each of the sub-proof's routines it sets the scope again.
This file says which rounds these are, for each of the three kinds of sub-proof. The statements are
about the imported reqMoments, layerRounds, attentionRounds and headRounds. Definitions, statements
and proofs.

Main names:
  `reqSend_idle`: the frame's sending, with a round of its own for the answers, leads from an idle
    state to an idle state and adds two rounds, named SEND seed and SEND answer.
  `Ends st f E`: from an idle state the routine f ends well only in an idle state, and adds some
    list of rounds and then just the rounds E.
  `layer_ends`, `attention_ends`: after moment 2 the rounds end in the round BAT-sigma that batches
    the sub-proof's rows. `head_ends`: the same of the head, in whose routine a batch of one row and
    a sumcheck come between; they are among the rounds that are not listed.
  `share`: if the sub-proof's routine adds just the round of the matrix after moment 1, and ends
    in E after moment 2: reqMoments, run from moment 1 for two moments, leads from an idle state to
    an idle state and adds: SEND seed, SEND answer, the round of the matrix, SEND seed, SEND answer,
    some list of rounds, and E.
  `layer_share`, `attention_share`, `head_share`: the three kinds.

Limits: of the four rounds of the two sendings only the names are said. The rounds of the lookup on
the digits are not listed: they are "some list". That a chain's routine calls reqMoments from an
idle state, with these arguments, is not shown here.
-/
import OnBytes.Params.DeriveReq
import OnBytes.Tie.Pv.Lay.PlanLook
import OnBytes.Tie.Pv.Att.PlanCalc
import OnBytes.Tie.Pv.Tail.CallFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan (rBat addsW_bat)

theorem reads_must {α : Type} (x : Option α) (why : String) : Reads (must x why) :=
  fun p a m h => by
  unfold must at h
  cases x with
  | none => cases h
  | some y => exact ((Prod.mk.inj (Except.ok.inj h)).2).symm

/-- The frame's sending, with a round of its own for the answers. -/
theorem reqSend_idle (st : Setting) (codes : Codes) (sent : List OracleNotice)
    (group atStart : GroupSize) (riders : Nat) (p q : PlanState) (hp : Idle st p)
    (h : reqSend codes sent group atStart riders true p = .ok ((), q)) :
    Idle st q ∧ ∃ R1 R2 : PlanRound, q.rounds = (p.rounds.push R1).push R2 ∧
      R1.entry.name = "SEND seed" ∧ R2.entry.name = "SEND answer" := by
  unfold reqSend at h
  obtain ⟨r, m, g, k⟩ := plan_bind h
  obtain rfl := reads_must _ _ _ _ _ g
  exact send_idle st _ r _ q hp k

/-- From an idle state f ends well only in an idle state, and adds some rounds and then just E. -/
def Ends (st : Setting) (f : Planning Unit) (E : List PlanRound) : Prop :=
  ∀ p q, Idle st p → f p = .ok ((), q) →
    Idle st q ∧ ∃ F : List PlanRound, q.rounds = p.rounds ++ (F ++ E).toArray

/-- The lookup on the digits keeps an idle state and only adds rounds. -/
theorem small_one (st : Setting) (x : SmallSize) : Ends st (planSmall x 1) [] := fun p q hp h => by
  have h' : (needs ((1 : Nat) == 1) >>= fun _ => planForest x.digits) p = .ok ((), q) := h
  obtain ⟨_, m, g, k⟩ := plan_bind h'
  obtain ⟨_, rfl⟩ := needs_ok g
  obtain ⟨a, F, r⟩ := OnBytes.Tie.Pv.Lay.keeps_forest st x.digits p q
    ⟨hp.set, hp.scope, hp.bytes, hp.roots, hp.answers⟩ k
  exact ⟨⟨a.set, a.scope, a.bytes, a.roots, a.answers⟩, F, by rw [r]; simp⟩

/-- The round that batches rows, behind a routine that ends in nothing. -/
theorem ends_bat {st : Setting} {f : Planning Unit} (hf : Ends st f []) (rows : Nat) :
    Ends st (f >>= fun _ => planBatSigma rows) [rBat st 0 rows] := fun p q hp h => by
  obtain ⟨_, m, g, k⟩ := plan_bind h
  obtain ⟨a, F, r⟩ := hf p m hp g
  obtain ⟨b, r2⟩ := addsW_bat st 0 rows m q ⟨a.set, a.scope, a.bytes, a.roots, a.answers⟩ k
  exact ⟨⟨b.set, b.scope, b.bytes, b.roots, b.answers⟩, F, by rw [r2, r]; simp⟩

/-- A group of layers, after moment 2. -/
theorem layer_ends (st : Setting) (look : ForestSize) (y : LayerRounds) (x : SmallSize)
    (claims : Nat) : Ends st (layerRounds look y x claims 2) [rBat st 0 claims] :=
  fun p q hp h => ends_bat (small_one st x) claims p q hp h

/-- Attention, after moment 2. -/
theorem attention_ends (st : Setting) (look : ForestSize) (y : AttentionRounds) (x : SmallSize) :
    Ends st (attentionRounds look y x 2) [rBat st 0 y.rows] := fun p q hp h => by
  have h' : ((pure () : Planning Unit) >>= fun _ => planSmall x 1 >>= fun _ =>
      planBatSigma y.rows) p = .ok ((), q) := h
  obtain ⟨_, m0, g0, k0⟩ := plan_bind h'
  obtain rfl : p = m0 := (Prod.mk.inj (Except.ok.inj g0)).2
  exact ends_bat (small_one st x) y.rows p q hp k0

/-- The output head, after moment 2. -/
theorem head_ends (st : Setting) (look : ForestSize) (y : HeadRounds) (x : SmallSize) :
    Ends st (headRounds look y x 2) [rBat st 0 y.rows] := fun p q hp h => by
  have h' : ((pure () : Planning Unit) >>= fun _ => planSmall x 1 >>= fun _ =>
      planBatSigma 1 >>= fun _ =>
      planPsc { degree := List.replicate y.lkW 3, degreeY := 1, values := 1 } >>= fun _ =>
      planBatSigma y.rows) p = .ok ((), q) := h
  obtain ⟨_, m0, g0, k0⟩ := plan_bind h'
  obtain rfl : p = m0 := (Prod.mk.inj (Except.ok.inj g0)).2
  obtain ⟨_, m1, g1, k1⟩ := plan_bind k0
  obtain ⟨a1, F1, r1⟩ := small_one st x p m1 hp g1
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain ⟨a2, r2⟩ := addsW_bat st 0 1 m1 m2 ⟨a1.set, a1.scope, a1.bytes, a1.roots, a1.answers⟩ g2
  obtain ⟨_, m3, g3, k3⟩ := plan_bind k2
  obtain ⟨a3, F3, r3⟩ := OnBytes.Tie.Pv.Lay.keeps_psc st 0 _ m2 m3
    ⟨a2.set, a2.scope, a2.bytes, a2.roots, a2.answers⟩ g3
  obtain ⟨a4, r4⟩ := addsW_bat st 0 y.rows m3 q
    ⟨a3.set, a3.scope, a3.bytes, a3.roots, a3.answers⟩ k3
  exact ⟨⟨a4.set, a4.scope, a4.bytes, a4.roots, a4.answers⟩, F1 ++ [rBat st 0 1] ++ F3,
    by rw [r4, r3, r2, r1]; simp⟩

/-- The smallness test's share of a link. -/
theorem share (st : Setting) (z : ProofSized) (sub : Subproofs) (l : Nat) (msgs : List ReqMessage)
    (x : SmallSize) (E : List PlanRound)
    (h1 : ∀ p q, Idle st p → sub.plan l 1 p = .ok ((), q) →
      Idle st q ∧ q.rounds = p.rounds.push (rngRound st x))
    (h2 : Ends st (sub.plan l 2) E) (p q : PlanState) (n : Nat) (hp : Idle st p)
    (h : Params.reqMoments z sub l msgs 2 1 p = .ok (n, q)) :
    Idle st q ∧ ∃ (S1 A1 S2 A2 : PlanRound) (F : List PlanRound),
      q.rounds = p.rounds ++ ([S1, A1, rngRound st x, S2, A2] ++ F ++ E).toArray ∧
      S1.entry.name = "SEND seed" ∧ A1.entry.name = "SEND answer" ∧
      S2.entry.name = "SEND seed" ∧ A2.entry.name = "SEND answer" := by
  unfold Params.reqMoments at h
  obtain ⟨_, m1, g1, k1⟩ := plan_bind h
  obtain ⟨a1, S1, A1, r1, n1, n1'⟩ := reqSend_idle st _ _ _ _ _ p m1 hp g1
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain ⟨a2, r2⟩ := h1 m1 m2 a1 g2
  obtain ⟨_, m3, g3, k3⟩ := plan_bind k2
  obtain ⟨a3, r3⟩ := scope_idle st m2 m3 a2.shut g3
  obtain ⟨more, m4, g4, k4⟩ := plan_bind k3
  obtain rfl : m4 = q := (Prod.mk.inj (Except.ok.inj k4)).2
  unfold Params.reqMoments at g4
  obtain ⟨_, m5, g5, k5⟩ := plan_bind g4
  obtain ⟨a5, S2, A2, r5, n5, n5'⟩ := reqSend_idle st _ _ _ _ _ m3 m5 a3 g5
  obtain ⟨_, m6, g6, k6⟩ := plan_bind k5
  obtain ⟨a6, F, r6⟩ := h2 m5 m6 a5 g6
  obtain ⟨_, m7, g7, k7⟩ := plan_bind k6
  obtain ⟨a7, r7⟩ := scope_idle st m6 m7 a6.shut g7
  obtain ⟨more2, m8, g8, k8⟩ := plan_bind k7
  obtain rfl : m8 = m4 := (Prod.mk.inj (Except.ok.inj k8)).2
  unfold Params.reqMoments at g8
  obtain rfl : m7 = m8 := (Prod.mk.inj (Except.ok.inj g8)).2
  exact ⟨a7, S1, A1, S2, A2, F, by rw [r7, r6, r5, r3, r2, r1]; simp, n1, n1', n5, n5'⟩

/-- A group of layers. -/
theorem layer_share (st : Setting) (z : ProofSized) (sub : Subproofs) (l : Nat)
    (msgs : List ReqMessage) (look : ForestSize) (y : LayerRounds) (x : SmallSize) (claims : Nat)
    (hs : ∀ m, sub.plan l m = layerRounds look y x claims m) (p q : PlanState) (n : Nat)
    (hp : Idle st p) (h : Params.reqMoments z sub l msgs 2 1 p = .ok (n, q)) :
    Idle st q ∧ ∃ (S1 A1 S2 A2 : PlanRound) (F : List PlanRound),
      q.rounds = p.rounds ++
        ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 claims]).toArray ∧
      S1.entry.name = "SEND seed" ∧ A1.entry.name = "SEND answer" ∧
      S2.entry.name = "SEND seed" ∧ A2.entry.name = "SEND answer" :=
  share st z sub l msgs x _
    (fun p q hp h => (layer_adds st look y x claims p q hp (by rw [← hs 1]; exact h)).1)
    (by rw [hs 2]; exact layer_ends st look y x claims) p q n hp h

/-- Attention. -/
theorem attention_share (st : Setting) (z : ProofSized) (sub : Subproofs) (l : Nat)
    (msgs : List ReqMessage) (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = attentionRounds look y x m) (p q : PlanState) (n : Nat)
    (hp : Idle st p) (h : Params.reqMoments z sub l msgs 2 1 p = .ok (n, q)) :
    Idle st q ∧ ∃ (S1 A1 S2 A2 : PlanRound) (F : List PlanRound),
      q.rounds = p.rounds ++
        ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 y.rows]).toArray ∧
      S1.entry.name = "SEND seed" ∧ A1.entry.name = "SEND answer" ∧
      S2.entry.name = "SEND seed" ∧ A2.entry.name = "SEND answer" :=
  share st z sub l msgs x _
    (fun p q hp h => (attention_adds st look y x p q hp (by rw [← hs 1]; exact h)).1)
    (by rw [hs 2]; exact attention_ends st look y x) p q n hp h

/-- The output head. -/
theorem head_share (st : Setting) (z : ProofSized) (sub : Subproofs) (l : Nat)
    (msgs : List ReqMessage) (look : ForestSize) (y : HeadRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = headRounds look y x m) (p q : PlanState) (n : Nat)
    (hp : Idle st p) (h : Params.reqMoments z sub l msgs 2 1 p = .ok (n, q)) :
    Idle st q ∧ ∃ (S1 A1 S2 A2 : PlanRound) (F : List PlanRound),
      q.rounds = p.rounds ++
        ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 y.rows]).toArray ∧
      S1.entry.name = "SEND seed" ∧ A1.entry.name = "SEND answer" ∧
      S2.entry.name = "SEND seed" ∧ A2.entry.name = "SEND answer" :=
  share st z sub l msgs x _
    (fun p q hp h => (head_adds st look y x p q hp (by rw [← hs 1]; exact h)).1)
    (by rw [hs 2]; exact head_ends st look y x) p q n hp h

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.share
#print axioms OnBytes.Tie.Pv.Tail.layer_share
#print axioms OnBytes.Tie.Pv.Tail.attention_share
#print axioms OnBytes.Tie.Pv.Tail.head_share
