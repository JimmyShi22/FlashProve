-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Req/Frame.lean: the rounds of the plan of a proof's first chain are the stretches of
the frame and of the sub-proofs, one behind the other, in the planner's own order.

The planner lays the first chain by firstPlan, whose frame is reqPlanFrom, a recursion on the groups
of the chain (OnBytes/Params/DeriveReq.lean). There is one group for each link, and one more, the
last, without a link. The sub-proofs' rounds come in through a record of routines (Subproofs). This
file cuts the list of rounds that these imported routines add into stretches, each tied to the
routine that has laid it. Definitions, statements and proofs.

Main names:
  `LaidIdle st x F`: F is the list of rounds that the routine x has added in a run from an idle
    state (Idle, OnBytes/Tie/Pv/Tail/Plan.lean).
  `SubOK st sub`: the one premise: from an idle state each routine of the sub-proofs ends well only
    with the setting kept and no open message, in whatever scope, and only adds rounds.
    (OnBytes/Tie/Pv/Req/Kinds.lean proves it for the three kinds of sub-proof.)
  `replyOf`, `sendOf`, `membersOf`, `switchOf`, `closedOf`, `laterOf`, `battOf`: the parts of the
    planner's routines, by name. switchOf is the sending at the head of a group and, from the second
    group on, the positions of the group before, as one routine: the sending leaves its answers
    open, and the round of the positions takes them in.
    `reqPlanFrom_cons`, `firstPlan_eq`: the imported routines are made of these parts.
  `FrameIs st z sub l gs links before R`: by recursion on the groups gs. At a group with a link: R
    is what the reply has laid, then switchOf, then the sub-proof's routine behind moment 0, then
    the later moments, then the batching, then the fold, then a list with FrameIs for the next
    group. At a group without a link: the reply's, switchOf's, and what the proximity test has laid.
  `req_from`: under SubOK, from an idle state reqPlanFrom ends well only in an idle state, and the
    rounds that it has added are a list with FrameIs.
  `FirstIs z sub L`, `first_plan`: THE STATEMENT: if firstPlan z sub is a plan P, the rounds of P
    are a list with FrameIs from group 0 on, then what the routine behind the links has laid, then
    the batching of the pending rows on the table, then the sending of W, then the seal.

Limits: LaidIdle says "in some run from an idle state", not "in the run at this place of the plan".
An idle state fixes every field of the planner's state but the rounds so far. That no routine reads
these is not proved here. So a stretch is tied to its routine's list only where that list is proved
the same in all such runs (Fixed, OnBytes/Tie/Pv/Req/Kinds.lean). The numbers of rows that the two
batchings are given are not said, so their rounds' errors and numbers of rows are not tied. Nothing
says that firstPlan ends well, that a round's bound holds of the protocol, or that the verifier on
bytes hears these rounds. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Req.Flow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Req

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Tail (Idle Shut Reads plan_bind needs_ok scope_idle)

/-- F is the list of rounds that the routine x has added in a run from an idle state. -/
def LaidIdle (st : Setting) {α : Type} (x : Planning α) (F : List PlanRound) : Prop :=
  ∃ p a q, Idle st p ∧ x p = .ok (a, q) ∧ Adds p q F

/-- What is asked of the sub-proofs' routines: from an idle state each ends well only with the
setting kept and no open message, in whatever scope, and only adds rounds. -/
structure SubOK (st : Setting) (sub : Subproofs) : Prop where
  plan : ∀ l m p q, Idle st p → sub.plan l m p = .ok ((), q) → Shut st q ∧ ∃ F, Adds p q F
  after : ∀ p q, Idle st p → sub.afterLinks p = .ok ((), q) → Shut st q ∧ ∃ F, Adds p q F

/-- The step that sets the scope again. -/
abbrev setScope : Planning Unit := modify fun p => { p with scope := .request }

section Parts
variable (z : ProofSized) (sub : Subproofs)

/-- A link's oracle messages. -/
def msgsOf (links : List ReqLink) : List ReqMessage := (links.head?.map (·.messages)).getD []

/-- The members of group number l: the target (from the second group on), the kept messages, the
link's messages of moment 0, the fresh mask of the group's fold. -/
def membersOf (l : Nat) (g : ReqGroup) (links : List ReqLink) : List OracleNotice :=
  (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
  (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
  ((msgsOf links).filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
  [foldMaskNotice (ioppFoldShape ⟨z.request.code, z.request.maskCode, g.k, g.h⟩ {})]

/-- The round of a link's plain scalars, where it has some. -/
def replyOf (links : List ReqLink) : Planning Unit :=
  if (links.head?.map (·.plain)).getD 0 != 0 then do
    planScalars ((links.head?.map (·.plain)).getD 0)
    closeNone "REPLY"
  else pure ()

/-- The sending at the head of group number l. -/
def sendOf (l : Nat) (g : ReqGroup) (links : List ReqLink) : Planning Unit :=
  reqSend z.codes
    (if l == 0 then membersOf z l g links ++ z.request.atStart else membersOf z l g links)
    (if links.head?.isSome then z.link.group else z.last.first) z.batch.own.first
    (if l == 0 then z.request.atStart.length else 0) (l == 0)

/-- The sending at the head of group number l and, from the second group on, the positions of the
group before, which take in the sending's answers. It returns the number of rows that the switch
into the group leaves on it. -/
def switchOf (l : Nat) (g : ReqGroup) (links : List ReqLink) (before : GroupSize) :
    Planning Nat :=
  sendOf z l g links >>= fun _ =>
    if 0 < l then planLoc before >>= fun t =>
      pure (1 + sumT ((keptOf g).map (·.shape.answers)) +
        t * (3 + sumT ((keptOf g).map (·.shape.mainRows))))
    else pure 0

/-- The group as it is closed. -/
def closedOf (g : ReqGroup) (gs : List ReqGroup) : GroupSize :=
  { z.link.group with
    k := g.k, h := g.h,
    slots := 2 ^ clog2 (1 + sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))) }

/-- The later moments of a link. -/
def laterOf (l : Nat) (links : List ReqLink) : Planning Nat :=
  Params.reqMoments z sub l (msgsOf links)
    (((msgsOf links).getLast?.map (·.moment + 1)).getD 0 - 1) 1

end Parts

/-- The list R is made of the stretches of the frame from group number l on, in the planner's own
order, each the list that its routine has added in a run. -/
def FrameIs (st : Setting) (z : ProofSized) (sub : Subproofs) :
    Nat → List ReqGroup → List ReqLink → GroupSize → List PlanRound → Prop
  | _, [], _, _, R => R = []
  | l, g :: gs, links, before, R =>
    ∃ Rr Rs Rest, R = Rr ++ (Rs ++ Rest) ∧
      LaidIdle st (replyOf links) Rr ∧ LaidIdle st (switchOf z l g links before) Rs ∧
      (if links.head?.isSome then
        ∃ R0 Rm Rb Rf R' n, Rest = R0 ++ (Rm ++ (Rb ++ (Rf ++ R'))) ∧
          LaidIdle st (sub.plan l 0) R0 ∧ LaidIdle st (laterOf z sub l links) Rm ∧
          LaidIdle st (planBat [closedOf z g gs] n) Rb ∧
          LaidIdle st (planFold (closedOf z g gs) 0) Rf ∧
          FrameIs st z sub (l + 1) gs (links.drop 1) (closedOf z g gs) R'
      else
        ∃ n, LaidIdle st (planIopp z.last.stages n 0 z.request.choice.masksRide) Rest)

section Proofs
variable {st : Setting} {z : ProofSized} {sub : Subproofs}

theorem keeps_reply (links : List ReqLink) : Keeps st (replyOf links) :=
  Keeps.ite ((Runs.then (runs_scalars st _) fun _ => shuts_none st _).keeps) (keeps_pure ())

/-- A sub-proof's routine and the step that sets the scope again. -/
theorem sub_then_scope (hs : SubOK st sub) (l m : Nat) (p q r : PlanState) (hp : Idle st p)
    (h1 : sub.plan l m p = .ok ((), q)) (h2 : setScope q = .ok ((), r)) :
    Idle st r ∧ ∃ F, Adds p q F ∧ Adds p r F := by
  obtain ⟨a, F, e⟩ := hs.plan l m p q hp h1
  obtain ⟨b, e2⟩ := scope_idle st q r a h2
  exact ⟨b, F, e, by unfold Adds at *; rw [e2, e]⟩

theorem keeps_moments (hs : SubOK st sub) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Keeps st (Params.reqMoments z sub l msgs fuel moment)
  | 0, _ => keeps_pure 0
  | fuel + 1, moment => fun p n q hp h => by
    unfold Params.reqMoments at h
    obtain ⟨_, m1, g1, k1⟩ := plan_bind h
    obtain ⟨a1, F1, e1⟩ := shuts_reqSend st _ _ _ _ _ p _ m1 (live_of_idle hp) g1
    obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
    obtain ⟨_, m3, g3, k3⟩ := plan_bind k2
    obtain ⟨a3, F2, _, e3⟩ := sub_then_scope hs l moment m1 m2 m3 a1 g2 g3
    obtain ⟨more, m4, g4, k4⟩ := plan_bind k3
    obtain ⟨a4, F3, e4⟩ := keeps_moments hs l msgs fuel (moment + 1) m3 more m4 a3 g4
    obtain rfl : m4 = q := (Prod.mk.inj (Except.ok.inj k4)).2
    exact ⟨a4, _, (e1.trans e3).trans e4⟩

theorem keeps_switch (l : Nat) (g : ReqGroup) (links : List ReqLink) (before : GroupSize) :
    Keeps st (switchOf z l g links before) := by
  unfold switchOf
  by_cases hl : 0 < l
  · simp only [if_pos hl]
    exact (Runs.then (runs_reqSend st _ _ _ _ _ _) fun _ =>
      Shuts.then (shuts_loc st before) fun _ => keeps_pure _).keeps
  · obtain rfl : l = 0 := by omega
    simp only [if_neg hl]
    exact (Shuts.then (shuts_reqSend st _ _ _ _ _) fun _ => keeps_pure _).keeps

/-- The planner's routine for the frame at a group, in the words of this file. -/
theorem reqPlanFrom_cons (l : Nat) (g : ReqGroup) (gs : List ReqGroup) (links : List ReqLink)
    (open_ : List Nat) (before : GroupSize) :
    reqPlanFrom z sub l (g :: gs) links open_ before =
      (replyOf links >>= fun _ => switchOf z l g links before >>= fun carried =>
        if links.head?.isSome then
          sub.plan l 0 >>= fun _ => setScope >>= fun _ => laterOf z sub l links >>= fun more =>
            planBat [closedOf z g gs] (open_.headD 0 + carried +
              sumT ((membersOf z l g links).map (·.shape.answers)) + more) >>= fun _ =>
            planFold (closedOf z g gs) 0 >>= fun _ =>
            reqPlanFrom z sub (l + 1) gs (links.drop 1) (open_.drop 1) (closedOf z g gs)
        else
          planIopp z.last.stages
            (carried + sumT ((membersOf z l g links).map (·.shape.answers))) 0
            z.request.choice.masksRide) := by
  rw [reqPlanFrom]
  unfold replyOf switchOf sendOf laterOf closedOf membersOf msgsOf
  by_cases hc : ((links.head?.map (·.plain)).getD 0 != 0) = true <;> by_cases hl : 0 < l <;>
    simp only [hc, hl, if_true, if_false, Bool.false_eq_true, bind_assoc, pure_bind] <;>
    cases links <;> rfl

/-- The frame's rounds from group number l on. -/
theorem req_from (hs : SubOK st sub) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize) (p q : PlanState), Idle st p →
      reqPlanFrom z sub l gs links open_ before p = .ok ((), q) →
      Idle st q ∧ ∃ R, Adds p q R ∧ FrameIs st z sub l gs links before R
  | [], l, links, open_, before, p, q, hp, h => by
    unfold reqPlanFrom at h
    obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
    exact ⟨hp, [], Adds.refl _, rfl⟩
  | g :: gs, l, links, open_, before, p, q, hp, h => by
    rw [reqPlanFrom_cons] at h
    obtain ⟨_, m1, g1, k1⟩ := plan_bind h
    obtain ⟨a1, Rr, e1⟩ := keeps_reply links p _ m1 hp g1
    obtain ⟨carried, m3, g3, k3⟩ := plan_bind k1
    obtain ⟨a3, Rs, e3⟩ := keeps_switch l g links before m1 carried m3 a1 g3
    by_cases hk : links.head?.isSome
    · rw [if_pos hk] at k3
      obtain ⟨_, m4, g4, k4⟩ := plan_bind k3
      obtain ⟨_, m5, g5, k5⟩ := plan_bind k4
      obtain ⟨a5, R0, e4, e5⟩ := sub_then_scope hs l 0 m3 m4 m5 a3 g4 g5
      obtain ⟨more, m6, g6, k6⟩ := plan_bind k5
      obtain ⟨a6, Rm, e6⟩ := keeps_moments hs l _ _ _ m5 more m6 a5 g6
      obtain ⟨_, m7, g7, k7⟩ := plan_bind k6
      obtain ⟨a7, Rb, e7⟩ := shuts_bat st _ _ m6 _ m7 (live_of_idle a6) g7
      obtain ⟨_, m8, g8, k8⟩ := plan_bind k7
      obtain ⟨a8, Rf, e8⟩ := shuts_fold st _ _ m7 _ m8 (live_of_idle a7) g8
      obtain ⟨a9, R', e9, f9⟩ := req_from hs gs (l + 1) _ _ _ m8 q a8 k8
      refine ⟨a9, Rr ++ (Rs ++ (R0 ++ (Rm ++ (Rb ++ (Rf ++ R'))))), ?_, ?_⟩
      · exact e1.trans (e3.trans (e5.trans (e6.trans (e7.trans (e8.trans e9)))))
      · refine ⟨Rr, Rs, _, rfl, ⟨p, _, m1, hp, g1, e1⟩, ⟨m1, _, m3, a1, g3, e3⟩, ?_⟩
        rw [if_pos hk]
        exact ⟨R0, Rm, Rb, Rf, R', _, rfl, ⟨m3, _, m4, a3, g4, e4⟩, ⟨m5, _, m6, a5, g6, e6⟩,
          ⟨m6, _, m7, a6, g7, e7⟩, ⟨m7, _, m8, a7, g8, e8⟩, f9⟩
    · rw [if_neg hk] at k3
      obtain ⟨a4, Rest, e4⟩ := shuts_iopp st _ _ _ _ m3 _ q (live_of_idle a3) k3
      refine ⟨a4, Rr ++ (Rs ++ Rest), e1.trans (e3.trans e4), ?_⟩
      refine ⟨Rr, Rs, Rest, rfl, ⟨p, _, m1, hp, g1, e1⟩, ⟨m1, _, m3, a1, g3, e3⟩, ?_⟩
      rw [if_neg hk]
      exact ⟨_, m3, _, q, a3, k3, e4⟩

/-! ### The whole first chain -/

/-- The batching of the pending rows on the table, where there are more than one. -/
def battOf (z : ProofSized) (sub : Subproofs) : Planning Unit :=
  if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol else pure ()

/-- All rounds of a proof's first chain. -/
def firstBody (z : ProofSized) (sub : Subproofs) : Planning Unit :=
  reqPlan z sub >>= fun _ => sub.afterLinks >>= fun _ => setScope >>= fun _ =>
    battOf z sub >>= fun _ => linPlanFirst z.codes z.batch >>= fun _ => planSeal

theorem firstPlan_eq (z : ProofSized) (sub : Subproofs) :
    firstPlan z sub = finishHeld z.set .request (firstBody z sub) := by
  unfold firstPlan firstBody battOf
  by_cases h : 1 < sub.pendingRows <;> simp only [h, if_true, if_false, pure_bind]

/-- A plan that is finished and held is the list of the rounds of a run from the empty plan. -/
theorem finishHeld_ok {s : Setting} {scope : Scope} {x : Planning Unit} {P : Planned}
    (h : finishHeld s scope x = .ok P) :
    ∃ q, x { set := s, scope := scope } = .ok ((), q) ∧ P.rounds = q.rounds.toList := by
  unfold finishHeld at h
  cases hf : finish s scope x with
  | error e =>
    rw [hf] at h
    cases h
  | ok p =>
    rw [hf] at h
    have h' : (if p.holds then (pure p : Except String Planned) else throw notAdmitted) =
        .ok P := h
    split at h'
    · obtain rfl : p = P := Except.ok.inj h'
      unfold finish at hf
      split at hf
      · cases hf
      · rename_i u q hx
        split at hf
        · cases hf
        · obtain rfl := Except.ok.inj hf
          exact ⟨q, hx, rfl⟩
    · cases h'

/-- The stretches of a proof's first chain, in the planner's own order. -/
structure FirstIs (z : ProofSized) (sub : Subproofs) (L : List PlanRound) : Prop where
  parts : ∃ R Ra Rb Rw Rs, L = R ++ (Ra ++ (Rb ++ (Rw ++ Rs))) ∧
    FrameIs z.set z sub 0 (reqGroups z.request).toList z.request.link z.link.group R ∧
    LaidIdle z.set sub.afterLinks Ra ∧ LaidIdle z.set (battOf z sub) Rb ∧
    LaidIdle z.set (linPlanFirst z.codes z.batch) Rw ∧ LaidIdle z.set planSeal Rs

theorem keeps_batt (z : ProofSized) (sub : Subproofs) : Keeps st (battOf z sub) :=
  Keeps.ite (shuts_batt st _ _).keeps (keeps_pure ())

/-- THE STATEMENT: the rounds of the plan of a proof's first chain. -/
theorem first_plan (z : ProofSized) (sub : Subproofs) (hs : SubOK z.set sub) (P : Planned)
    (h : firstPlan z sub = .ok P) : FirstIs z sub P.rounds := by
  rw [firstPlan_eq] at h
  obtain ⟨q, hq, e⟩ := finishHeld_ok h
  have hp : Idle z.set ({ set := z.set, scope := .request } : PlanState) :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold firstBody at hq
  obtain ⟨_, m1, g1, k1⟩ := plan_bind hq
  obtain ⟨a1, R, e1, f1⟩ := req_from hs _ _ _ _ _ _ m1 hp g1
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain ⟨a2, Ra, e2⟩ := hs.after m1 m2 a1 g2
  obtain ⟨_, m3, g3, k3⟩ := plan_bind k2
  obtain ⟨a3, e3⟩ := scope_idle z.set m2 m3 a2 g3
  obtain ⟨_, m4, g4, k4⟩ := plan_bind k3
  obtain ⟨a4, Rb, e4⟩ := keeps_batt z sub m3 _ m4 a3 g4
  obtain ⟨_, m5, g5, k5⟩ := plan_bind k4
  obtain ⟨a5, Rw, e5⟩ := shuts_linFirst z.set _ _ m4 _ m5 (live_of_idle a4) g5
  obtain ⟨_, Rs, e6⟩ := shuts_seal z.set m5 _ q (live_of_idle a5) k5
  have e3' : Adds m2 m3 [] := by unfold Adds; rw [e3]; simp
  have all := e1.trans (e2.trans (e3'.trans (e4.trans (e5.trans e6))))
  refine ⟨R, Ra, Rb, Rw, Rs, ?_, f1, ⟨m1, _, m2, a1, g2, e2⟩, ⟨m3, _, m4, a3, g4, e4⟩,
    ⟨m4, _, m5, a4, g5, e5⟩, ⟨m5, _, q, a5, k5, e6⟩⟩
  rw [e]
  unfold Adds at all
  rw [all]
  simp

end Proofs

end OnBytes.Tie.Pv.Req

#print axioms OnBytes.Tie.Pv.Req.req_from
#print axioms OnBytes.Tie.Pv.Req.first_plan
