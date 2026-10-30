-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Req/Link.lean: the places of a link of a proof's first chain, and of the chain's end,
as stretches of the plan.

OnBytes/Tie/Pv/Req/Frame.lean cuts the plan of the first chain into the stretches of the planner's
routines. This file cuts a link's stretches further, for each of the three kinds of sub-proof, with
OnBytes/Tie/Pv/Req/Kinds.lean (behind moment 0), OnBytes/Tie/Pv/Tail/Share.lean (the later moments)
and OnBytes/Tie/Pv/Req/Names.lean (the frame's own rounds, by name).

Main names:
  `headNames l links`: REPLY, where the link has plain scalars; SEND seed; SEND answer at the first
    group alone; LOC from the second group on.
  `frame_link`: a group with a link: the frame's rounds in front, with the names headNames; what the
    sub-proof's routine has laid behind moment 0; what the later moments have laid; the closing,
    with the names BAT, FOLD epsilon, k times FOLD round; a list with FrameIs for the next group.
  `frame_last`: the last group: all its rounds by name: headNames, BAT, stageNames.
  `ThreeMoments links`: the link has three moments.
  `later_att`, `later_lay`, `later_head`: the later moments: a sending; the round of the matrix; a
    sending; some rounds; the round that batches the sub-proof's rows.
  `att_places`, `lay_places`, `head_places`: THE STATEMENTS: the whole link in a row: the frame's
    rounds in front; what the lookup on the calls has laid; the sub-proof's own rounds (the lists
    attRounds, ownRounds; of the head: what planHeadOwn has laid); a sending; the round of the
    matrix; a sending; some rounds; the round that batches the rows; the closing; the next group.
  `first_tail`: behind all groups, by name: BAT-sigma, PSC epsilon and kCol times PSC round, where
    there is more than one pending row; SEND seed, SEND answer; SEAL.

Limits: those of OnBytes/Tie/Pv/Req/Frame.lean and OnBytes/Tie/Pv/Tail/Share.lean. "Some rounds":
the rounds between the second sending and the last batching are not listed: the lookup on the
digits, and in the head's link also the merge. Of the frame's own rounds only the names are said.
That a link has three moments, and of which kind it is, are premises. No table of places outside
this library is compared with these lists here. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Req.Names
import OnBytes.Tie.Pv.Tail.Share

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Req

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Tail (Idle rngRound)
open OnBytes.Tie.Pv.Att.Plan (rBat attRounds)

variable {st : Setting} {z : ProofSized} {sub : Subproofs}

/-- The names of the frame's own rounds in front of a link's sub-proof: the reply, where the link
has plain scalars; the sending; from the second group on, the positions of the group before. -/
def headNames (l : Nat) (links : List ReqLink) : List String :=
  (if ((links.head?.map (·.plain)).getD 0 != 0) = true then ["REPLY"] else []) ++
    (("SEND seed" :: (if (l == 0) = true then ["SEND answer"] else [])) ++
      (if 0 < l then ["LOC"] else []))

/-- A group with a link: the frame's rounds in front, by name; what the sub-proof's routine has laid
behind moment 0; what the later moments have laid; the closing, by name; the rest of the frame. -/
theorem frame_link {l : Nat} {g : ReqGroup} {gs : List ReqGroup} {links : List ReqLink}
    {before : GroupSize} {R : List PlanRound} (hk : links.head?.isSome = true)
    (h : FrameIs st z sub l (g :: gs) links before R) :
    ∃ Rh R0 Rm Rc R', R = Rh ++ (R0 ++ (Rm ++ (Rc ++ R'))) ∧ namesOf Rh = headNames l links ∧
      LaidIdle st (sub.plan l 0) R0 ∧ LaidIdle st (laterOf z sub l links) Rm ∧
      namesOf Rc = "BAT" :: "FOLD epsilon" :: List.replicate g.k "FOLD round" ∧
      FrameIs st z sub (l + 1) gs (links.drop 1) (closedOf z g gs) R' := by
  obtain ⟨Rr, Rs, Rest, e, lr, ls, hr⟩ := h
  rw [if_pos hk] at hr
  obtain ⟨R0, Rm, Rb, Rf, R', n, e', l0, lm, lb, lf, f⟩ := hr
  refine ⟨Rr ++ Rs, R0, Rm, Rb ++ Rf, R', ?_, ?_, l0, lm, ?_, f⟩
  · rw [e, e']
    simp
  · have a := laidIdle_says (says_reply links) lr
    have b := laidIdle_says (says_switch (z := z) l g links before) ls
    unfold headNames
    rw [← a, ← b]
    simp [namesOf]
  · have a := laidIdle_says (says_bat _ _) lb
    have b := laidIdle_says (says_fold _ _) lf
    have c : namesOf (Rb ++ Rf) = namesOf Rb ++ namesOf Rf := by simp [namesOf]
    rw [c, a, b]
    rfl

/-- The last group, which has no link: all its rounds by name. -/
theorem frame_last {l : Nat} {g : ReqGroup} {gs : List ReqGroup} {links : List ReqLink}
    {before : GroupSize} {R : List PlanRound} (hk : ¬ links.head?.isSome = true)
    (h : FrameIs st z sub l (g :: gs) links before R) :
    namesOf R = headNames l links ++ ("BAT" :: stageNames z.last.stages) := by
  obtain ⟨Rr, Rs, Rest, e, lr, ls, hr⟩ := h
  rw [if_neg hk] at hr
  obtain ⟨n, li⟩ := hr
  have a := laidIdle_says (says_reply links) lr
  have b := laidIdle_says (says_switch (z := z) l g links before) ls
  have c := laidIdle_says (says_iopp _ _ _ _) li
  unfold headNames
  rw [e, ← a, ← b, ← c]
  simp [namesOf]

/-- The link has three moments. -/
def ThreeMoments (links : List ReqLink) : Prop :=
  ((msgsOf links).getLast?.map (·.moment + 1)).getD 0 = 3

/-- The names of a sending with a round of its own for the answers. -/
abbrev sendNames : List String := ["SEND seed", "SEND answer"]

/-- The later moments of an attention link. -/
theorem later_att {l : Nat} {links : List ReqLink} {Rm : List PlanRound} (h3 : ThreeMoments links)
    (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = attentionRounds look y x m)
    (k : LaidIdle st (laterOf z sub l links) Rm) :
    ∃ Sa Sb F, Rm = Sa ++ ([rngRound st x] ++ (Sb ++ (F ++ [rBat st 0 y.rows]))) ∧
      namesOf Sa = sendNames ∧ namesOf Sb = sendNames := by
  obtain ⟨p, n, q, hp, hq, e⟩ := k
  unfold laterOf at hq
  rw [h3] at hq
  obtain ⟨_, S1, A1, S2, A2, F, r, n1, n2, n3, n4⟩ :=
    Tail.attention_share st z sub l (msgsOf links) look y x hs p q n hp hq
  refine ⟨[S1, A1], [S2, A2], F, ?_, by simp [namesOf, n1, n2], by simp [namesOf, n3, n4]⟩
  have e' : Adds p q ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 y.rows]) := r
  rw [adds_inj e e']
  simp

/-- The later moments of a link of a group of layers. -/
theorem later_lay {l : Nat} {links : List ReqLink} {Rm : List PlanRound} (h3 : ThreeMoments links)
    (look : ForestSize) (y : LayerRounds) (x : SmallSize) (claims : Nat)
    (hs : ∀ m, sub.plan l m = layerRounds look y x claims m)
    (k : LaidIdle st (laterOf z sub l links) Rm) :
    ∃ Sa Sb F, Rm = Sa ++ ([rngRound st x] ++ (Sb ++ (F ++ [rBat st 0 claims]))) ∧
      namesOf Sa = sendNames ∧ namesOf Sb = sendNames := by
  obtain ⟨p, n, q, hp, hq, e⟩ := k
  unfold laterOf at hq
  rw [h3] at hq
  obtain ⟨_, S1, A1, S2, A2, F, r, n1, n2, n3, n4⟩ :=
    Tail.layer_share st z sub l (msgsOf links) look y x claims hs p q n hp hq
  refine ⟨[S1, A1], [S2, A2], F, ?_, by simp [namesOf, n1, n2], by simp [namesOf, n3, n4]⟩
  have e' : Adds p q ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 claims]) := r
  rw [adds_inj e e']
  simp

/-- The later moments of the head's link. -/
theorem later_head {l : Nat} {links : List ReqLink} {Rm : List PlanRound}
    (h3 : ThreeMoments links) (look : ForestSize) (y : HeadRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = headRounds look y x m)
    (k : LaidIdle st (laterOf z sub l links) Rm) :
    ∃ Sa Sb F, Rm = Sa ++ ([rngRound st x] ++ (Sb ++ (F ++ [rBat st 0 y.rows]))) ∧
      namesOf Sa = sendNames ∧ namesOf Sb = sendNames := by
  obtain ⟨p, n, q, hp, hq, e⟩ := k
  unfold laterOf at hq
  rw [h3] at hq
  obtain ⟨_, S1, A1, S2, A2, F, r, n1, n2, n3, n4⟩ :=
    Tail.head_share st z sub l (msgsOf links) look y x hs p q n hp hq
  refine ⟨[S1, A1], [S2, A2], F, ?_, by simp [namesOf, n1, n2], by simp [namesOf, n3, n4]⟩
  have e' : Adds p q ([S1, A1, rngRound st x, S2, A2] ++ F ++ [rBat st 0 y.rows]) := r
  rw [adds_inj e e']
  simp

/-- THE PLACES OF AN ATTENTION LINK: the frame's rounds in front; the lookup on the calls; the own
rounds, as the list attRounds; a sending; the round of the matrix; a sending; some rounds (the
lookup on the digits); the round that batches all rows; the closing; the rest of the frame. -/
theorem att_places {l : Nat} {g : ReqGroup} {gs : List ReqGroup} {links : List ReqLink}
    {before : GroupSize} {R : List PlanRound} (hk : links.head?.isSome = true)
    (h3 : ThreeMoments links) (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = attentionRounds look y x m)
    (h : FrameIs st z sub l (g :: gs) links before R) :
    ∃ Rh Fl Sa Sb Fd Rc R', R = Rh ++ (Fl ++ (attRounds st y ++ (Sa ++ ([rngRound st x] ++
        (Sb ++ (Fd ++ ([rBat st 0 y.rows] ++ (Rc ++ R')))))))) ∧
      namesOf Rh = headNames l links ∧ LaidIdle st (planForest look) Fl ∧
      namesOf Sa = sendNames ∧ namesOf Sb = sendNames ∧
      namesOf Rc = "BAT" :: "FOLD epsilon" :: List.replicate g.k "FOLD round" ∧
      FrameIs st z sub (l + 1) gs (links.drop 1) (closedOf z g gs) R' := by
  obtain ⟨Rh, R0, Rm, Rc, R', e, nh, l0, lm, nc, f⟩ := frame_link hk h
  rw [hs 0] at l0
  obtain ⟨Fl, e0, lf⟩ := laid_att0 look y x l0
  obtain ⟨Sa, Sb, Fd, em, na, nb⟩ := later_att h3 look y x hs lm
  exact ⟨Rh, Fl, Sa, Sb, Fd, Rc, R', by rw [e, e0, em]; simp, nh, lf, na, nb, nc, f⟩

/-- THE PLACES OF A LINK OF A GROUP OF LAYERS. -/
theorem lay_places {l : Nat} {g : ReqGroup} {gs : List ReqGroup} {links : List ReqLink}
    {before : GroupSize} {R : List PlanRound} (hk : links.head?.isSome = true)
    (h3 : ThreeMoments links) (look : ForestSize) (y : LayerRounds) (x : SmallSize)
    (claims : Nat) (hs : ∀ m, sub.plan l m = layerRounds look y x claims m)
    (h : FrameIs st z sub l (g :: gs) links before R) :
    ∃ Rh Fl Sa Sb Fd Rc R', R = Rh ++ (Fl ++ (Lay.ownRounds st y ++ (Sa ++ ([rngRound st x] ++
        (Sb ++ (Fd ++ ([rBat st 0 claims] ++ (Rc ++ R')))))))) ∧
      namesOf Rh = headNames l links ∧ LaidIdle st (planForest look) Fl ∧
      namesOf Sa = sendNames ∧ namesOf Sb = sendNames ∧
      namesOf Rc = "BAT" :: "FOLD epsilon" :: List.replicate g.k "FOLD round" ∧
      FrameIs st z sub (l + 1) gs (links.drop 1) (closedOf z g gs) R' := by
  obtain ⟨Rh, R0, Rm, Rc, R', e, nh, l0, lm, nc, f⟩ := frame_link hk h
  rw [hs 0] at l0
  obtain ⟨Fl, e0, lf⟩ := laid_lay0 look y x claims l0
  obtain ⟨Sa, Sb, Fd, em, na, nb⟩ := later_lay h3 look y x claims hs lm
  exact ⟨Rh, Fl, Sa, Sb, Fd, Rc, R', by rw [e, e0, em]; simp, nh, lf, na, nb, nc, f⟩

/-- THE PLACES OF THE HEAD's LINK. Its own rounds are what planHeadOwn has laid; the rounds between
the second sending and the last batching (the lookup on the digits, the merge) are not listed. -/
theorem head_places {l : Nat} {g : ReqGroup} {gs : List ReqGroup} {links : List ReqLink}
    {before : GroupSize} {R : List PlanRound} (hk : links.head?.isSome = true)
    (h3 : ThreeMoments links) (look : ForestSize) (y : HeadRounds) (x : SmallSize)
    (hs : ∀ m, sub.plan l m = headRounds look y x m)
    (h : FrameIs st z sub l (g :: gs) links before R) :
    ∃ Rh Fl Go Sa Sb Fd Rc R', R = Rh ++ (Fl ++ (Go ++ (Sa ++ ([rngRound st x] ++
        (Sb ++ (Fd ++ ([rBat st 0 y.rows] ++ (Rc ++ R')))))))) ∧
      namesOf Rh = headNames l links ∧ LaidIdle st (planForest look) Fl ∧
      LaidIdle st (planHeadOwn y) Go ∧ namesOf Sa = sendNames ∧ namesOf Sb = sendNames ∧
      namesOf Rc = "BAT" :: "FOLD epsilon" :: List.replicate g.k "FOLD round" ∧
      FrameIs st z sub (l + 1) gs (links.drop 1) (closedOf z g gs) R' := by
  obtain ⟨Rh, R0, Rm, Rc, R', e, nh, l0, lm, nc, f⟩ := frame_link hk h
  rw [hs 0] at l0
  obtain ⟨Fl, Go, e0, lf, lg⟩ := laid_head0 look y x l0
  obtain ⟨Sa, Sb, Fd, em, na, nb⟩ := later_head h3 look y x hs lm
  exact ⟨Rh, Fl, Go, Sa, Sb, Fd, Rc, R', by rw [e, e0, em]; simp, nh, lf, lg, na, nb, nc, f⟩

/-- The end of the first chain, by name. -/
theorem first_tail {L : List PlanRound} (ha : sub.afterLinks = pure ()) (h : FirstIs z sub L) :
    ∃ R T, L = R ++ T ∧
      FrameIs z.set z sub 0 (reqGroups z.request).toList z.request.link z.link.group R ∧
      namesOf T = (if 1 < sub.pendingRows then
          "BAT-sigma" :: "PSC epsilon" :: List.replicate z.batch.shape.kCol "PSC round" else []) ++
        (sendNames ++ ["SEAL"]) := by
  obtain ⟨R, Ra, Rb, Rw, Rs, e, f, la, lb, lw, ls⟩ := h.parts
  rw [ha] at la
  have a := laidIdle_says (says_pure ()) la
  have b := laidIdle_says (says_battOf (z := z) (sub := sub)) lb
  have c : namesOf Rw = sendNames := laidIdle_says (says_linFirst _ _) lw
  have d := laidIdle_says says_seal ls
  refine ⟨R, Ra ++ (Rb ++ (Rw ++ Rs)), e, f, ?_⟩
  rw [← b, ← c, ← d]
  have a' : Ra = [] := by simpa [namesOf] using a
  rw [a']
  simp [namesOf]

end OnBytes.Tie.Pv.Req

#print axioms OnBytes.Tie.Pv.Req.frame_link
#print axioms OnBytes.Tie.Pv.Req.frame_last
#print axioms OnBytes.Tie.Pv.Req.att_places
#print axioms OnBytes.Tie.Pv.Req.lay_places
#print axioms OnBytes.Tie.Pv.Req.head_places
#print axioms OnBytes.Tie.Pv.Req.first_tail
