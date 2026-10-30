-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/StillOfLeaves.lean: FORM (A)'s LEMMAS GIVE THE GUARD's DEBT FOR THE DAY WHEN IT IS STRUCK: from "this part leaves the reading h" (Block.Leaves, FoldHeard.lean; the clauses of Link.LeavesBut | Chain.LeavesBut,
LeavesBut.lean) to "this part is still" (Block.Still | Link.Still | Chain.Still, SeatGuardChain.lean), at the guard's test sameBy h t s := (h s == h t), where == on h's values is lawful.

  sameBy h (SeatGuard.lean): the guard's test that belongs to a reading h. sameBy_leaves: its yes is the equation (the premise of Chain.guarded_flat). runsLeave_of_bare: a block without runs owes nothing for them.
  still_of_leaves: a block: its decision leaves h (asked only where but does not name its place), its runs of both sorts leave h.
  **Chain.still_of_leavesBut**: c.LeavesBut h but, with "or" read as "where but does not name the place" ⇒ c.Still (sameBy h) but. THE BATCHING: LeavesBut's own fenced clause (at every function that leaves h) is spent AT THE LINK's OWN
    FUNCTION, which leaves h by leavesClaimsInBy; that the batching has no runs of its own that write is asked beside it.
  **Chain.strike**: so c.LeavesBut h but (and the runs' clauses outside the links) ⇒ (c.guarded (sameBy h) but).blocksInOrder = c.blocksInOrder.

Every "there is", walked: no statement has one.
Limits. Rules: shown of no chain of the protocol; a member: SeatGuardStillToy.lean [not in this library; so here read: not proved in this library]. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α : Type}

/-- The runs of a block leave h. -/
def Block.RunsLeave (h : S → α) (b : Block S Cl) : Prop :=
  (∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → h y.2 = h s) ∧ (∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → h s' = h s)

/-- A block without runs: for nothing. So, where the tests on the plan hold, every block outside "hear" (Block.hasNoClaimsAndNothingAfter stands in Chain.blocksInOrder's and in "laid"'s tests). -/
theorem runsLeave_of_bare (h : S → α) {b : Block S Cl} (hb : b.hasNoClaimsAndNothingAfter = true) : b.RunsLeave h := by
  unfold Block.hasNoClaimsAndNothingAfter at hb
  have hc : b.claims = [] := List.isEmpty_iff.1 (Bool.and_eq_true_iff.1 hb).1
  have ha : b.after = [] := List.isEmpty_iff.1 (Bool.and_eq_true_iff.1 hb).2
  exact ⟨fun c m => (by rw [hc] at m; exact nomatch m), fun c m => (by rw [ha] at m; exact nomatch m)⟩

/-- What a chain owes beside Chain.LeavesBut: the runs of the blocks that stand outside "hear": they are run by nobody where the tests on the plan hold ("hasNoClaimsAndNothingAfter"), but they are fields, and the guard lays its test over them. -/
structure Chain.RunsLeave (h : S → α) (c : Chain S Cl) : Prop where
  first : c.first.RunsLeave h
  front : ∀ b ∈ c.front, b.RunsLeave h
  batch : ∀ L ∈ c.links, (L.batch (claimsInBy L.each L.hear L.order)).RunsLeave h
  close : ∀ L ∈ c.links, ∀ b ∈ L.close, b.RunsLeave h
  back : ∀ b ∈ c.back, b.RunsLeave h
  last : c.last.RunsLeave h

variable [BEq α] [LawfulBEq α]

theorem sameBy_leaves (h : S → α) : ∀ t s, sameBy h t s = true → h s = h t := fun _ _ e => eq_of_beq e

theorem sameBy_of (h : S → α) {t s : S} (e : h s = h t) : sameBy h t s = true := by
  unfold sameBy; rw [e]; exact beq_self_eq_true _

theorem still_of_leaves {h : S → α} {but : Place → Bool} {b : Block S Cl}
    (hd : but b.place = true ∨ b.Leaves h) (hr : b.RunsLeave h) : b.Still (sameBy h) but :=
  ⟨fun hp t rs gs s e => by
      rcases hd with k | k
      · rw [hp] at k; exact nomatch k
      · exact sameBy_of h (k t rs gs s e),
    fun c m n t y e => sameBy_of h (hr.1 c m n t y e), fun c m t s e => sameBy_of h (hr.2 c m t s e)⟩

theorem Link.still_of_leavesBut {h : S → α} {but : Place → Bool} {L : Link S Cl} (H : L.LeavesBut h but)
    (hb : (L.batch (claimsInBy L.each L.hear L.order)).RunsLeave h) (hc : ∀ b ∈ L.close, b.RunsLeave h) :
    L.Still (sameBy h) but where
  lay := fun t s e => sameBy_of h (H.lay t s e)
  hear := fun b m => still_of_leaves (H.hear b m) ⟨H.claims b m, H.after b m⟩
  batch := still_of_leaves
    (H.batch _ fun s y K => leavesClaimsInBy h L.each L.hear L.order H.claims s y K) hb
  close := fun b m => still_of_leaves (H.close b m) (hc b m)
  clear := fun t s e => sameBy_of h (H.clear t s e)

theorem Chain.still_of_leavesBut {h : S → α} {but : Place → Bool} {c : Chain S Cl} (H : c.LeavesBut h but)
    (R : c.RunsLeave h) : c.Still (sameBy h) but where
  first := still_of_leaves H.first R.first
  front := fun b m => still_of_leaves (H.front b m) (R.front b m)
  links := fun L m => Link.still_of_leavesBut (H.links L m) (R.batch L m) (R.close L m)
  back := fun b m => still_of_leaves (H.back b m) (R.back b m)
  last := still_of_leaves H.last R.last

/-- **THE GUARD IS STRUCK**: where every part leaves h (form (A)'s lemmas), the guarded chain's flat list is the chain's. -/
theorem Chain.strike {h : S → α} {but : Place → Bool} {c : Chain S Cl} (H : c.LeavesBut h but) (R : c.RunsLeave h) :
    (c.guarded (sameBy h) but).blocksInOrder = c.blocksInOrder :=
  (Chain.still_of_leavesBut H R).guarded_flat_eq

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.runsLeave_of_bare
#print axioms VerifiableInference.Desc.still_of_leaves
#print axioms VerifiableInference.Desc.Link.still_of_leavesBut
#print axioms VerifiableInference.Desc.Chain.still_of_leavesBut
#print axioms VerifiableInference.Desc.Chain.strike
