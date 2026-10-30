-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FromYes.lean: WHAT LIES BEHIND THE SEATED BATCHING BLOCK, HAD FROM ITS YES.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

Honest/K9/YesAtSeat.lean and YesAll.lean say WHEN the seated block says yes, and hand on what lies behind
(`BatBehind`, no mark of failure, the reply as it was) together with that yes: so these facts are reached there
through the yes's premises alone. A law that has the yes IN HAND (what a member leaves behind; what it owes the next)
wants them from the yes itself.
  `addedAll_of_yes`   where the adding returns, it has left and turned what `AddedAll` says
      (Johnson/Desc/K9/Honest/AddYes.lean: `addList_only`, then `addList_yes`; at the empty list by the text)
  **`behind_of_yes`**   of a segment of which `SeatedFree` holds (Honest/K9/AtSeatAll.lean): EVERY yes of the seated
      block's decision at x, to a state t: there are y and G with `BatBehind p g s x y G t`, t bears no mark of
      failure, and its reply is the reply in front. (The sealed `IM.yes_alone` is an iff; the count by
      `SeatedFree.keeps`: no claim is counted behind the draw.)
  **`behind_of_step`**   EVERY yes of its STEP, at whatever rounds and columns: there is one round, it has drawn one
      element, of words tr; NO COLUMN IS TAKEN; and the same holds at x := the element of words tr
No member (`SeatedFree` is shown at no written description). `behind_of_yes` is called by `behind_of_step` and by
Honest/K9/Leaves.lean and Keeps.lean; `behind_of_step` by these two as well.
WHAT IS NOT CLAIMED. That the block says yes anywhere. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.YesAll
import Johnson.Desc.ProofFile.Honest.K9.AtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- Where the adding returns, it has left and turned what `AddedAll` says. -/
theorem addedAll_of_yes (cls : List Claim) (F G : Fork) (h : Desc.K9.addList F cls = .ok G) :
    Desc.K9H.AddedAll F G cls.length := by
  cases hc : cls with
  | nil =>
    rw [hc] at h
    obtain rfl : F = G := Except.ok.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons c0 l0 =>
    rw [← hc]
    obtain ⟨hf, hr⟩ := Desc.K9H.addList_only cls F G h
    obtain ⟨G', hG', hA⟩ := Desc.K9H.addList_yes cls F (hr (by rw [hc]; exact List.cons_ne_nil _ _)) hf
    obtain rfl : G' = G := Except.ok.inj (hG'.symm.trans h)
    exact hA

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
  {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **From a yes of the decision.** -/
theorem behind_of_yes (Sd : SeatedFree c Z l k Lk p w) (s t : S) (x : E)
    (hd : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    ∃ y G, BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x y G t ∧ t.failed = none ∧
      t.out.reply = s.out.reply := by
  obtain ⟨pl, hk, hb⟩ := Sd.alone
  obtain ⟨hbat, hf, hsame⟩ := (IM.yes_alone hb hk s t _ []).1 hd
  obtain ⟨e, a, cls, G, hy, hadd, ht⟩ := batch_split p _ s t x hbat
  obtain ⟨t₁, hdraw, hz, he⟩ := gathered_split p _ s x _ hy
  obtain ⟨a0, ha0⟩ := draw_open p s t₁ x hdraw
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a0 ha0 hdraw
  obtain ⟨a', ha', hcore⟩ := Sd.keeps t₁ e cls a₁ hz h1
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans he)
  have hA := addedAll_of_yes cls a'.F G hadd
  refine ⟨(e, a', cls), G, ⟨hy, hadd, hA, ht, ?_, ?_⟩, hf, ?_⟩
  · rw [ht]
    exact set_fork e a' _ he
  · show G.nClaim = cls.length
    rw [hA.count, hcore.count, hl.count, Nat.zero_add]
  · unfold ProofFile.sameReply at hsame
    exact (eq_of_beq hsame).symm

/-- **From a yes of the step.** -/
theorem behind_of_step (Sd : SeatedFree c Z l k Lk p w) (ft : ℕ) (s t : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (t, n)) :
    ∃ r tr, rs = [r] ∧ r.drawn.elems = [tr] ∧ n = 0 ∧
      ∃ y G, BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s (E.ofTriple tr) y G t ∧ t.failed = none ∧
        t.out.reply = s.out.reply := by
  obtain ⟨pl, hk, hb⟩ := Sd.alone
  obtain ⟨r, tr, rfl, hx⟩ := seated_step_shape hb ft s t rs cols n hy
  have h := (Sound.step_ok_iff ft _ s t [r] cols n).1 hy
  have hn : n = 0 := by
    have h3 := h.2.2.1
    rw [IM.alone_rounds hb] at h3
    exact h3
  have hd := P1K8.seated_reads hb hk s t (noDigest r) ⟨[], drawnOne (E.ofTriple tr)⟩ _ [] hx h.2.2.2
  exact ⟨r, tr, rfl, hx, hn, behind_of_yes Sd s t _ hd⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.addedAll_of_yes
#print axioms ProofFile.Honest.K9.behind_of_yes
#print axioms ProofFile.Honest.K9.behind_of_step
