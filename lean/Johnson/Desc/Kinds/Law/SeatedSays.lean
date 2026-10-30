-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SeatedSays.lean.
WHAT IT DOES NOT SHOW. No soundness by itself: it carries laws to the seated block. That a
description seats that block: not here. ONE PREMISE IS A TEST WITH CODE THAT NO BLOCK ASKS TODAY
(Stored/HeadAsks.lean): moreOk W, on public numbers: seated_cond alone takes it. Of K6On three
clauses stay premises (K6Left): the ledger is well laid; a heard token is below V; what the lookup
has heard has its last claim's numbers filled. The rule's premise (no bad element is drawn),
Canonical and what the block opens stay rowStep's; the components d stand under "for all", tied to
nothing that is fixed in front of the draws, as in rowStep.
LETTERS. seated_step: under "there is": bU: pinned by blockOf W l = some bU. Read by one premise
alone: ms and l (h); ft, cols, n (the step).
OBJECT. The block as a lot seats it: Stored/HeadAddsAtS.lean's seatedClaims W l ms.
WHAT IT IS. WHAT THE SEATED BLOCK's TWO YESES GIVE THE LAWS.
  laidOk_is         the seat's test on the laid numbers IS Law/LaidSays.lean's, by rfl.
  more_says         what the five further tests say.
  seated_cond       where the seated block's test on the plan says yes, and moreOk W: all eighteen
                    premises on public numbers that the laws on this kind ask
                    (Law/K06ConditionSpends.lean: Cond.K06CondAt W): twelve by the block's own test,
                    one by the block's being there, five by moreOk.
  step_carries      a step goes over from a block to another with the same rounds whose decision
                    goes on wherever the first one's does.
  seated_step       WHERE THE SEATED BLOCK's STEP GOES ON: the step of blockOf's block goes on to
                    the same record, AND THE RECORD's OWN TEST ON THE REQUEST SAID YES.
  start_pays        that test gives the kind's part of the test on the instance (by
                    Law/StartPays.lean's okStart_of_reqOk).
  K6Left, k6On_seated   THE TWO YESES PAY THREE OF K6On's SIX CLAUSES.
  rowStep_seated, rowPromise_seated   Law/RowPins.lean's rowStep and Law/RowPromise.lean's
                    rowPromise AT THE SEATED BLOCK; and behind its step the two readers of the
                    lookup's hearing agree WHOLE, not in its points alone.

-/
import Mathlib
import Johnson.Stored.HeadAsks
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.Kinds.Law.StartPays
import Johnson.Desc.Kinds.Law.LaidSays
import Johnson.Desc.Kinds.Law.K06ConditionSpends
import Johnson.Desc.Kinds.Law.RowPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open OnBytes

/-- **The seat's test on the laid numbers is the law's.** -/
theorem laidOk_is (W : Model.Verify.Public) :
    laidOk W = (letI := sizesAt W.hS; letI := policyAt W.hS;
      (laidOf W.hS (Model.Verify.borderOf W.y)).ok) := rfl

/-- What the five further tests say. -/
theorem more_says {W : Model.Verify.Public} (h : moreOk W = true) :
    Model.Head.admitted W.hS = true ∧ (Model.Head.numbers W.hS).toOption.isSome = true ∧
      (letI := sizesOf W.hS; ∀ k : PlaceKey, lenOf k < 2 ^ 41) ∧
      (Params.settingOf W.P.frame).workOf .field .request + 66 ≤ 128 ∧
      (Params.settingOf W.P.frame).instances = 1 := by
  unfold moreOk moreTests moreTestsAt at h
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true, beq_iff_eq,
    Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨a1, a2, ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩, a4, a5⟩ := h
  refine ⟨a1, a2, fun k => ?_, a4, a5⟩
  rcases k with k | k
  · cases k
    · exact k1
    · exact k2
    · exact k3
    · exact k4
  · cases k
    · exact k5
    · exact k6
    · exact k7
    · exact k8
    · exact k9

/-- **WHERE THE SEATED BLOCK's TEST ON THE PLAN SAYS YES, AND THE FIVE FURTHER TESTS: ALL
EIGHTEEN.** -/
theorem seated_cond {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true)
    (hm : moreOk W = true) : Cond.K06CondAt W := by
  obtain ⟨hok, hl⟩ := seatedClaims_plan h hp
  obtain ⟨m1, m2, m3, m4, m5⟩ := more_says hm
  rw [laidOk_is] at hl
  obtain ⟨a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11, a12, _⟩ := laid_says _ _ hl
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS 0).policy
  letI : Request := requestOf S.blank
  letI : Token := ⟨0⟩
  have P : PlanFacts := planFacts (sT := W.hS.tabS) hok
  obtain ⟨b0, h0, _⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, hU, _⟩ := Option.map_eq_some_iff.mp h0
  exact
    { ok := hok, admitted := m1, numbers := m2, features := a1, point := a2, rows := a3
      block := a4, pad := a5, limbs := a6, blocks := Nat.dvd_of_mod_eq_zero P.hdS
      table := Nat.dvd_of_mod_eq_zero P.hJVa, keys := m3, index := ⟨a8, a9⟩
      stream := by rw [Nat.one_mul]; exact a12
      origin := ⟨a10, a11⟩, work := m4, once := m5, reads := by rw [hU]; rfl }

/-- A step goes over to a block with the same rounds whose decision goes on wherever the first one's
does. -/
theorem step_carries {S' Cl Cl' : Type} (a : Block S' Cl) (b : Block S' Cl')
    (hr : a.rounds = b.rounds) {s : S'}
    (hd : ∀ rs gs s', a.decide s rs gs = .ok s' → b.decide s rs gs = .ok s') {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {s' : S'} {n : Nat}
    (h : a.step ft s rs cols = .ok (s', n)) : b.step ft s rs cols = .ok (s', n) := by
  unfold Block.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i x1 e1
    split at h
    · cases h
    · rename_i x2 e2
      split at h
      · cases h
      · rename_i s1 e3
        unfold Block.step
        rw [← hr]
        simp only [bind, Except.bind, pure, Except.pure, e1, e2, hd _ _ _ e3]
        exact h

/-- **WHERE THE SEATED BLOCK's STEP GOES ON.** -/
theorem seated_step {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) :
    ∃ bU, blockOf W l = some bU ∧ bU.step ft s rs cols = .ok (s', n) ∧ startOk W s = true := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, hU, rfl⟩ := Option.map_eq_some_iff.mp h0
  obtain ⟨gs, hd⟩ := Came.step_decide ft _ s rs cols s' n hs
  refine ⟨blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l, ?_, ?_,
    ((tested_decide _ _ _ _ _ _ _ _).1 hd).2⟩
  · unfold blockOf
    rw [hU]
    rfl
  · have hsame : (kindWithJoin (K3.seatCalls asClaim) (seatAt W.hS iU3) l 4
        (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).decide =
        (blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l).decide := rfl
    exact step_carries
      (tested (laidOk W) (startOk W) ms (kindWithJoin (K3.seatCalls asClaim) (seatAt W.hS iU3) l 4
        (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))))
      (blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l) rfl
      (fun rs gs t e => hsame ▸ ((tested_decide _ _ _ _ _ _ _ _).1 e).1) hs

/-- **The record's own test on the request gives the kind's part of the test on the instance.** -/
theorem start_pays (W : Model.Verify.Public) (s : S) (h : startOk W s = true) :
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true :=
  StartPays.okStart_of_reqOk W.hS (workOf W) s h

/-- What is left of K6On as a premise on the record in front. -/
def K6Left (W : Model.Verify.Public) (s : S) : Prop :=
  WellLaid ((seatAt W.hS (readsOf W)).ledger s) ∧
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) ∧
    (∀ gk, s.lookHeard? = some gk → CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s))

/-- **The two yeses pay three of K6On's six clauses.** -/
theorem k6On_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) {ft : Nat}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hs : b.step ft s rs cols = .ok (s', n)) (hL : K6Left W s) : K6On W s := by
  obtain ⟨hok, hl⟩ := seatedClaims_plan h hp
  rw [laidOk_is] at hl
  obtain ⟨_, _, _, h4⟩ := seated_step h hs
  exact ⟨hL.1, hok, (laid_says _ _ hl).1, start_pays W s h4, hL.2.1, hL.2.2⟩

/-- **rowStep AT THE SEATED BLOCK.** -/
theorem rowStep_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) (ft : Nat)
    (s : S) (d : Pinned) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat)
    (hL : K6Left W s) (hnb : Sound.NoBad (ruleStep W s d) rs) (hcan : Canonical rs)
    (hs : b.step ft s rs cols = .ok (s', n)) (hout : K6Out W s' d) : K6In W s d := by
  obtain ⟨bU, hU, hsU, _⟩ := seated_step h hs
  exact Came.rowStep W l bU hU ft s d rs cols s' n (k6On_seated h hp hs hL) hnb hcan hsU hout

/-- **rowPromise AT THE SEATED BLOCK; and the two readers of the lookup's hearing agree whole.** -/
theorem rowPromise_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) (ft : Nat)
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat) (hL : K6Left W s)
    (hs : b.step ft s rs cols = .ok (s', n)) :
    K6Behind W s s' ∧ s'.look? = s'.lookHeard? := by
  obtain ⟨bU, hU, hsU, _⟩ := seated_step h hs
  refine ⟨Came.rowPromise W l bU hU ft s rs cols s' n (k6On_seated h hp hs hL) hsU, ?_⟩
  obtain ⟨gs, hd⟩ := Came.step_decide ft bU s rs cols s' n hsU
  unfold blockOf at hU
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hU
  exact Came.look_behind W.hS iU3 _ l hd

end VerifiableInference.Desc.Kinds.Head.Law
