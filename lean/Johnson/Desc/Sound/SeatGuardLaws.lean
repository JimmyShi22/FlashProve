-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardLaws.lean: the laws of the guard on one seat
(Johnson/Desc/SeatGuard.lean).

Main names:
  `guarded_under`: where the guarded block says yes, the block says the same yes, at the same record
    (`Block.Under`, HearsOnce.lean): at every place, with no premise. So every law on a block's YES
    is a law on the guarded block's yes, unturned. A law that says THAT a block says yes does not
    cross: the guard can refuse an honest file (Johnson/Desc/SeatGuard.lean, Limits (1)).
  `guarded_claims_under`, `guarded_after_under`: the like for each run.
  `guarded_yes`: at a place that `but` does not name: the guarded yes is the block's yes and "the
    seat is as it was".
  `guarded_idle`: where the block never writes the seat, the guarded decision is the block's own.
  `Chain.guarded_flat`: at (same t s = true → h s = h t): every block of
    `(c.guarded same but).blocksInOrder` stands at a place that `but` names, or leaves h: with no premise on
    any kind's text.

Silly members. `same := fun _ _ => true`: the guard is idle, and the law's premise asks a constant
h. `same := fun _ _ => false`: every guarded part refuses: the laws hold for nothing.
`but := fun _ => true`: `Chain.guarded_flat` says nothing of the blocks' decisions.
Every "there is", walked: two: `guarded_claims_under` and `guarded_after_under` name, for a run of
the guarded block, a run of the block under the same name: a member of a list, found by the map that
made the guarded list. They are spent by the two `Leaves` clauses alone; what the fold finds by
lookup is said by `guarded_lookup_claims` and `guarded_lookup_after` (SeatGuardChain.lean).

Limits. Rules. Block by block and run by run. The chain's form ("the guarded chain's yes is the
unguarded chain's yes") stands in SeatGuardChain.lean, under one premise on the batching
(`Link.BatchMono`): the batching's block is handed the guarded runs as one function, and what an
arbitrary batching does with another function is not said by its type.
Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.SeatGuard
import Johnson.Desc.Sound.LeavesBut
import Johnson.Desc.Sound.HearsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α : Type}

theorem seatSame_ok {same : S → S → Bool} {t s s' : S} (h : seatSame same t s = .ok s') :
    s' = s ∧ same t s = true := by
  unfold seatSame at h
  split at h
  · rename_i e
    exact ⟨(Except.ok.inj h).symm, e⟩
  · exact nomatch h

section
variable (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl)

/-- **Where the guarded block says yes, the block says the same yes.** -/
theorem guarded_under : (b.guarded same but).Under b := by
  intro t rs gs s' D
  have D' : (if but b.place then b.decide t rs gs
      else (b.decide t rs gs).bind (seatSame same t)) = .ok s' := D
  split at D'
  · exact D'
  · obtain ⟨s, hs, e⟩ := bindOk D'
    rw [(seatSame_ok e).1]
    exact hs

theorem guarded_yes (hp : but b.place = false) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S) :
    (b.guarded same but).decide t rs gs = .ok s' ↔
      b.decide t rs gs = .ok s' ∧ same t s' = true := by
  show (if but b.place then b.decide t rs gs
      else (b.decide t rs gs).bind (seatSame same t)) = .ok s' ↔ _
  rw [hp]
  constructor
  · intro D
    obtain ⟨s, hs, e⟩ := bindOk (x := b.decide t rs gs) D
    obtain ⟨rfl, e'⟩ := seatSame_ok e
    exact ⟨hs, e'⟩
  · rintro ⟨hs, e⟩
    show (b.decide t rs gs).bind (seatSame same t) = .ok s'
    rw [hs]
    show seatSame same t s' = .ok s'
    unfold seatSame
    rw [e]; rfl

/-- Each guarded run of claims says the run's own yes. -/
theorem guarded_claims_under : ∀ c ∈ (b.guarded same but).claims, ∃ c₀ ∈ b.claims, c₀.1 = c.1 ∧
    ∀ n t y, c.2 n t = .ok y → c₀.2 n t = .ok y ∧ same t y.2 = true := by
  intro c hc
  obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
  refine ⟨c₀, h₀, rfl, fun n t y hy => ?_⟩
  obtain ⟨y₀, hy₀, e⟩ := bindOk (x := c₀.2 n t) hy
  obtain ⟨s, hs, rfl⟩ := mapOk (x := seatSame same t y₀.2) e
  exact ⟨hy₀, (seatSame_ok hs).2⟩

/-- Each guarded run behind the batching says the run's own yes. -/
theorem guarded_after_under : ∀ c ∈ (b.guarded same but).after, ∃ c₀ ∈ b.after, c₀.1 = c.1 ∧
    ∀ t s', c.2 t = .ok s' → c₀.2 t = .ok s' ∧ same t s' = true := by
  intro c hc
  obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
  refine ⟨c₀, h₀, rfl, fun t s' hy => ?_⟩
  obtain ⟨s, hs, e⟩ := bindOk (x := c₀.2 t) hy
  obtain ⟨rfl, e'⟩ := seatSame_ok e
  exact ⟨hs, e'⟩

/-- Idle where the block never writes the seat. -/
theorem guarded_idle (hb : ∀ t rs gs s, b.decide t rs gs = .ok s → same t s = true) :
    (b.guarded same but).decide = b.decide := by
  funext t rs gs
  show (if but b.place then b.decide t rs gs
      else (b.decide t rs gs).bind (seatSame same t)) = b.decide t rs gs
  split
  · rfl
  · cases hd : b.decide t rs gs with
    | error e => rfl
    | ok s =>
      show seatSame same t s = .ok s
      unfold seatSame
      rw [hb t rs gs s hd]; rfl

variable {same} {h : S → α} (hs : ∀ t s, same t s = true → h s = h t)
include hs

theorem guarded_or : but (b.guarded same but).place = true ∨ (b.guarded same but).Leaves h := by
  show but b.place = true ∨ _
  cases e : but b.place with
  | true => exact Or.inl rfl
  | false => exact Or.inr fun t rs gs s' D => hs t s' ((guarded_yes same but b e t rs gs s').1 D).2

theorem guarded_claims_leave :
    ∀ c ∈ (b.guarded same but).claims, ∀ n t y, c.2 n t = .ok y → h y.2 = h t := by
  intro c hc n t y hy
  obtain ⟨_, _, _, k⟩ := guarded_claims_under same but b c hc
  exact hs t y.2 (k n t y hy).2

theorem guarded_after_leaves :
    ∀ c ∈ (b.guarded same but).after, ∀ t s', c.2 t = .ok s' → h s' = h t := by
  intro c hc t s' hy
  obtain ⟨_, _, _, k⟩ := guarded_after_under same but b c hc
  exact hs t s' (k t s' hy).2

theorem Link.guarded_leavesBut (L : Link S Cl) : (L.guarded same but).LeavesBut h but where
  lay := fun t s' K => by
    obtain ⟨s, _, e⟩ := bindOk (x := L.lay t) K
    obtain ⟨rfl, e'⟩ := seatSame_ok e
    exact hs t _ e'
  hear := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_or but b₀ hs
  claims := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_claims_leave but b₀ hs
  after := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_after_leaves but b₀ hs
  batch := fun f _ => guarded_or but (L.batch f) hs
  close := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_or but b₀ hs
  clear := fun t s' K => by
    obtain ⟨s, _, e⟩ := bindOk (x := L.clear t) K
    obtain ⟨rfl, e'⟩ := seatSame_ok e
    exact hs t _ e'

theorem Chain.guarded_leavesBut (c : Chain S Cl) : (c.guarded same but).LeavesBut h but where
  first := guarded_or but c.first hs
  front := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_or but b₀ hs
  links := fun L hL => by
    obtain ⟨L₀, _, rfl⟩ := List.mem_map.1 hL
    exact Link.guarded_leavesBut but hs L₀
  back := fun b hb => by
    obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact guarded_or but b₀ hs
  last := guarded_or but c.last hs

/-- **The law of the guard**: every block of the guarded chain's flat list stands at a place that
`but` names, or leaves h: whatever the kinds' texts are. -/
theorem Chain.guarded_flat (c : Chain S Cl) :
    ∀ b ∈ (c.guarded same but).blocksInOrder, but b.place = true ∨ b.Leaves h :=
  (Chain.guarded_leavesBut but hs c).flat

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.guarded_under
#print axioms VerifiableInference.Desc.guarded_yes
#print axioms VerifiableInference.Desc.guarded_claims_under
#print axioms VerifiableInference.Desc.guarded_after_under
#print axioms VerifiableInference.Desc.guarded_idle
#print axioms VerifiableInference.Desc.Chain.guarded_leavesBut
#print axioms VerifiableInference.Desc.Chain.guarded_flat
