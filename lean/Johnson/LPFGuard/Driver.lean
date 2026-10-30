-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Driver.lean: THE GUARD ON THE REPLY: from the driver's structure to its chain.

What the file is. The driver (Johnson/Desc/First/Driver/Chain.lean) builds the first chain from a
structure H : Blocks T Cl of what the kinds supply: firstChainWithoutReplyGuard is the chain as the blocks are, and
firstChain is firstChainWithoutReplyGuard behind the guard. Here: what is asked of that structure, so that the chain
is the same behind the guard and without it, and that it is enough. All is general in the state T,
the claims' type Cl, a reading h : T → α of the state and the structure H. "Leaves h" means: h is
behind the step as it was in front.

Main names.
* BlocksBut h H: WHAT IS ASKED OF THE STRUCTURE. Every block that H hands is handed at a place of
  the kind K7 or its decision leaves h; every block's runs leave h; every batching that H hands at a
  place of the kind K9 (the driver asks at no other), at a function of claims that leaves h, leaves
  h by its decision and its runs; what starts and what ends a segment leaves h; the chain's first
  block and its last block leave h.
* linkAt_parts, bare_parts: the driver's text unfolded once: every part of a segment or of the bare
  chain is a field of H, with the place stamped.
* bare_leavesBut, bare_runsLeave: BlocksBut h H gives the two premises of the library's
  firstChain_strike at the bare chain: Chain.LeavesBut h hearsReply and Chain.RunsLeave h.
* strike_at: THE DRIVER's GUARD FALLS. Where H.same is sameBy h and BlocksBut h H holds, a first
  chain has the flat list of a bare chain, and its last block has as many rounds.
* still_idle, linkStill_idle, chainStill_idle, idle_at: THE IDLE GUARD. The same end where H.same
  always says yes, with nothing asked of any block.
* bare_same_with, bare_same: firstChainWithoutReplyGuard does not read the field same.
* guarded_self, guarded_idle_self: ONE BLOCK's GUARD FALLS: a block that leaves h is its own
  guarded form at sameBy h; every block is its own guarded form at a test that always says yes.

What it leans on. Files of the library alone: firstChain_some, firstChain_strike
(Johnson/Desc/Sound/GuardAtDriver.lean); leavesClaimsInBy, Link.LeavesBut, Chain.LeavesBut
(Johnson/Desc/Sound/LeavesBut.lean); Block.RunsLeave, Chain.RunsLeave, still_of_leaves
(Johnson/Desc/Sound/StillOfLeaves.lean); Block.Still, Link.Still, Chain.Still,
Block.Still.guarded_eq, Chain.Still.guarded_flat_eq, Chain.guarded_last_rounds
(Johnson/Desc/Sound/SeatGuardChain.lean); Block.Leaves (Johnson/Desc/Sound/FoldHeard.lean);
mem_of_mapM (Johnson/Desc/First/Driver/PlacesLaw.lean).
Carried proofs. The unfolding of blockAt, linkAt and firstChainWithoutReplyGuard in blockAt_part, linkAt_parts and
bare_parts follows blockAt_hears, linkAt_hearsAt and bare_hearsAt
(Johnson/Desc/Sound/GuardAtDriver.lean), line by line up to "cases".

Limits. Rules at the driver's text, general in the structure: BlocksBut is shown of no structure
here. That a run goes by this chain is not said here. Two chains with the same flat list need not be
equal as structures: a segment's batching may differ at a function of claims that changes h. A
constant h meets BlocksBut at every structure; then sameBy h always says yes. Nothing on soundness.


-/
import Johnson.Desc.Sound.GuardAtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference.Desc
open VerifiableInference.Desc.First

variable {T Cl α : Type}

/-! ## 1 What is asked of the driver's structure -/

/-- **What is asked of the driver's structure**: every part that it hands leaves the reading h, but
for the decision of a block at a place of the kind K7. -/
structure BlocksBut (h : T → α) (H : Blocks T Cl) : Prop where
  block : ∀ a b, H.block a = some b → a.kind = KindName.K7 ∨ b.Leaves h
  runs : ∀ a b, H.block a = some b → b.RunsLeave h
  batch : ∀ a mk, a.kind = KindName.K9 → H.batch a = some mk →
    ∀ f : T → Except String (List Cl × T), (∀ s y, f s = .ok y → h y.2 = h s) →
      (mk f).Leaves h ∧ (mk f).RunsLeave h
  lay : ∀ l s s', H.lay l s = .ok s' → h s' = h s
  clear : ∀ l s s', H.clear l s = .ok s' → h s' = h s
  first : H.first.Leaves h ∧ H.first.RunsLeave h
  last : H.last.Leaves h ∧ H.last.RunsLeave h

/-! ## 2 The driver's text, unfolded once -/

/-- The stamp of a place turns neither the decision nor the runs. -/
theorem leaves_stamp {h : T → α} {b : Block T Cl} (a : Place) (k : b.Leaves h) :
    ({ b with place := a } : Block T Cl).Leaves h :=
  fun s rs gs s' D => k s rs gs s' D

theorem runsLeave_stamp {h : T → α} {b : Block T Cl} (a : Place) (k : b.RunsLeave h) :
    ({ b with place := a } : Block T Cl).RunsLeave h :=
  ⟨fun c m n s y e => k.1 c m n s y e, fun c m s s' e => k.2 c m s s' e⟩

section
variable {H : Blocks T Cl} {links : List ModelPart} {several : Bool} {c c₀ : Chain T Cl}

/-- The block at a place is the structure's block, with the place stamped. -/
theorem blockAt_part {a : Place} {b : Block T Cl} (e : blockAt H a = some b) :
    ∃ b₀, H.block a = some b₀ ∧ b = { b₀ with place := a } := by
  unfold blockAt at e
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨b₀, e₀, rfl⟩

/-- A segment's five parts that can write, each as a field of the structure. -/
theorem linkAt_parts {l : Nat} {sub : ModelPart} {L : Link T Cl} (e : linkAt H l sub = some L) :
    L.lay = H.lay l ∧ (∀ b ∈ L.hear, ∃ a, blockAt H a = some b) ∧
      (∃ a mk, H.batch a = some mk ∧ a.kind = KindName.K9 ∧
        L.batch = fun f => { mk f with place := a }) ∧
      (∀ b ∈ L.close, ∃ a, blockAt H a = some b) ∧ L.clear = H.clear l := by
  unfold linkAt at e
  simp only [Option.bind_eq_bind, Option.pure_def] at e
  obtain ⟨hear, hh, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨batch, hb, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨close, hc, e⟩ := Option.bind_eq_some_iff.1 e
  cases e
  refine ⟨rfl, fun b m => ?_, ⟨_, batch, hb, rfl, rfl⟩, fun b m => ?_, rfl⟩
  · obtain ⟨a, _, k⟩ := mem_of_mapM (blockAt H) _ _ hh b m
    exact ⟨a, k⟩
  · obtain ⟨a, _, k⟩ := mem_of_mapM (blockAt H) _ _ hc b m
    exact ⟨a, k⟩

/-- The bare chain's five parts, each as a field of the structure or a segment of the driver's. -/
theorem bare_parts (h₀ : firstChainWithoutReplyGuard H links several = some c₀) :
    (∃ a, c₀.first = { H.first with place := a }) ∧ c₀.front = [] ∧
      (∀ L ∈ c₀.links, ∃ l sub, linkAt H l sub = some L) ∧
      (∀ b ∈ c₀.back, ∃ a, blockAt H a = some b) ∧
      ∃ a, c₀.last = { H.last with place := a } := by
  unfold firstChainWithoutReplyGuard at h₀
  simp only [Option.bind_eq_bind, Option.pure_def] at h₀
  split at h₀
  · cases h₀
  obtain ⟨_, _, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨ls, hl, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨back, hb, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  cases h₀
  refine ⟨⟨_, rfl⟩, rfl, fun L m => ?_, fun b m => ?_, ⟨_, rfl⟩⟩
  · obtain ⟨x, _, k⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L m
    exact ⟨x.2, x.1, k⟩
  · obtain ⟨a, _, k⟩ := mem_of_mapM (blockAt H) _ _ hb b m
    exact ⟨a, k⟩

/-! ## 3 From the structure to the bare chain's two debts -/

variable {h : T → α}

theorem blockAt_leavesBut (K : BlocksBut h H) {a : Place} {b : Block T Cl}
    (e : blockAt H a = some b) : hearsReply b.place = true ∨ b.Leaves h := by
  obtain ⟨b₀, e₀, rfl⟩ := blockAt_part e
  rcases K.block a b₀ e₀ with k | k
  · exact Or.inl (show (a.kind == KindName.K7) = true from beq_iff_eq.2 k)
  · exact Or.inr (leaves_stamp a k)

theorem blockAt_runsLeave (K : BlocksBut h H) {a : Place} {b : Block T Cl}
    (e : blockAt H a = some b) : b.RunsLeave h := by
  obtain ⟨b₀, e₀, rfl⟩ := blockAt_part e
  exact runsLeave_stamp a (K.runs a b₀ e₀)

theorem linkAt_leavesBut (K : BlocksBut h H) {l : Nat} {sub : ModelPart} {L : Link T Cl}
    (e : linkAt H l sub = some L) : L.LeavesBut h hearsReply := by
  obtain ⟨e1, e2, ⟨a, mk, hb, h9, e3⟩, e4, e5⟩ := linkAt_parts e
  refine ⟨fun s s' k => ?_, fun b m => ?_, fun b m => ?_, fun b m => ?_, fun f hf => Or.inr ?_,
    fun b m => ?_, fun s s' k => ?_⟩
  · rw [e1] at k
    exact K.lay l s s' k
  · obtain ⟨p, k⟩ := e2 b m
    exact blockAt_leavesBut K k
  · obtain ⟨p, k⟩ := e2 b m
    exact (blockAt_runsLeave K k).1
  · obtain ⟨p, k⟩ := e2 b m
    exact (blockAt_runsLeave K k).2
  · rw [e3]
    exact leaves_stamp a (K.batch a mk h9 hb f hf).1
  · obtain ⟨p, k⟩ := e4 b m
    exact blockAt_leavesBut K k
  · rw [e5] at k
    exact K.clear l s s' k

/-- A segment's runs outside "hear": the batching's, at the segment's own function of claims, and
the closing's. -/
theorem linkAt_runsLeave (K : BlocksBut h H) {l : Nat} {sub : ModelPart} {L : Link T Cl}
    (e : linkAt H l sub = some L) :
    (L.batch (claimsInBy L.each L.hear L.order)).RunsLeave h ∧ ∀ b ∈ L.close, b.RunsLeave h := by
  obtain ⟨_, _, ⟨a, mk, hb, h9, e3⟩, e4, _⟩ := linkAt_parts e
  refine ⟨?_, fun b m => ?_⟩
  · rw [e3]
    exact runsLeave_stamp a (K.batch a mk h9 hb _ fun s y k =>
      leavesClaimsInBy h L.each L.hear L.order (linkAt_leavesBut K e).claims s y k).2
  · obtain ⟨p, k⟩ := e4 b m
    exact blockAt_runsLeave K k

/-- **The bare chain leaves h, but at the place that hears the reply.** -/
theorem bare_leavesBut (K : BlocksBut h H) (h₀ : firstChainWithoutReplyGuard H links several = some c₀) :
    c₀.LeavesBut h hearsReply := by
  obtain ⟨⟨a, e1⟩, e2, e3, e4, ⟨z, e5⟩⟩ := bare_parts h₀
  refine ⟨Or.inr ?_, fun b m => ?_, fun L m => ?_, fun b m => ?_, Or.inr ?_⟩
  · rw [e1]
    exact leaves_stamp a K.first.1
  · rw [e2] at m
    exact nomatch m
  · obtain ⟨l, sub, k⟩ := e3 L m
    exact linkAt_leavesBut K k
  · obtain ⟨p, k⟩ := e4 b m
    exact blockAt_leavesBut K k
  · rw [e5]
    exact leaves_stamp z K.last.1

/-- **The bare chain's runs outside "hear" leave h.** -/
theorem bare_runsLeave (K : BlocksBut h H) (h₀ : firstChainWithoutReplyGuard H links several = some c₀) :
    c₀.RunsLeave h := by
  obtain ⟨⟨a, e1⟩, e2, e3, e4, ⟨z, e5⟩⟩ := bare_parts h₀
  refine ⟨?_, fun b m => ?_, fun L m => ?_, fun L m => ?_, fun b m => ?_, ?_⟩
  · rw [e1]
    exact runsLeave_stamp a K.first.2
  · rw [e2] at m
    exact nomatch m
  · obtain ⟨l, sub, k⟩ := e3 L m
    exact (linkAt_runsLeave K k).1
  · obtain ⟨l, sub, k⟩ := e3 L m
    exact (linkAt_runsLeave K k).2
  · obtain ⟨p, k⟩ := e4 b m
    exact blockAt_runsLeave K k
  · rw [e5]
    exact runsLeave_stamp z K.last.2

/-! ## 4 The driver's guard falls -/

/-- **THE DRIVER's GUARD FALLS**: where the structure's test is sameBy h and every part that the
structure hands leaves h but K7's decision, a first chain has a bare chain's flat list, and its last
block has as many rounds. -/
theorem strike_at [BEq α] [LawfulBEq α] (hs : H.same = sameBy h) (K : BlocksBut h H)
    (hc : firstChain H links several = some c) :
    ∃ c₀, firstChainWithoutReplyGuard H links several = some c₀ ∧ c.blocksInOrder = c₀.blocksInOrder ∧
      c.last.rounds = c₀.last.rounds := by
  obtain ⟨c₀, h₀, e⟩ := firstChain_some hc
  refine ⟨c₀, h₀, firstChain_strike hs hc h₀ (bare_leavesBut K h₀) (bare_runsLeave K h₀), ?_⟩
  rw [e]
  exact Chain.guarded_last_rounds c₀

end

/-! ## 5 The idle guard -/

section
variable {same : T → T → Bool}

/-- At a test that always says yes every block is still. -/
theorem still_idle (hs : ∀ t s, same t s = true) (but : Place → Bool) (b : Block T Cl) :
    b.Still same but :=
  ⟨fun _ t _ _ s _ => hs t s, fun _ _ _ t y _ => hs t y.2, fun _ _ t s _ => hs t s⟩

theorem linkStill_idle (hs : ∀ t s, same t s = true) (but : Place → Bool) (L : Link T Cl) :
    L.Still same but where
  lay := fun t s _ => hs t s
  hear := fun b _ => still_idle hs but b
  batch := still_idle hs but _
  close := fun b _ => still_idle hs but b
  clear := fun t s _ => hs t s

theorem chainStill_idle (hs : ∀ t s, same t s = true) (but : Place → Bool) (c : Chain T Cl) :
    c.Still same but where
  first := still_idle hs but _
  front := fun b _ => still_idle hs but b
  links := fun L _ => linkStill_idle hs but L
  back := fun b _ => still_idle hs but b
  last := still_idle hs but _

end

/-- **THE IDLE GUARD**: where the structure's test always says yes, a first chain has a bare chain's
flat list, and its last block has as many rounds. Nothing is asked of any block. -/
theorem idle_at {H : Blocks T Cl} {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (hs : ∀ t s, H.same t s = true) (hc : firstChain H links several = some c) :
    ∃ c₀, firstChainWithoutReplyGuard H links several = some c₀ ∧ c.blocksInOrder = c₀.blocksInOrder ∧
      c.last.rounds = c₀.last.rounds := by
  obtain ⟨c₀, h₀, e⟩ := firstChain_some hc
  refine ⟨c₀, h₀, ?_, ?_⟩
  · rw [e]
    exact (chainStill_idle hs hearsReply c₀).guarded_flat_eq
  · rw [e]
    exact Chain.guarded_last_rounds c₀

/-! ## 6 firstChainWithoutReplyGuard does not read the test -/

/-- **firstChainWithoutReplyGuard does not read the field same.** -/
theorem bare_same_with (H : Blocks T Cl) (same : T → T → Bool) (links : List ModelPart)
    (several : Bool) :
    firstChainWithoutReplyGuard { H with same := same } links several = firstChainWithoutReplyGuard H links several := rfl

/-- The same, for two structures that part in that field alone. -/
theorem bare_same (H H' : Blocks T Cl) (e : H' = { H with same := H'.same }) (links : List ModelPart)
    (several : Bool) : firstChainWithoutReplyGuard H' links several = firstChainWithoutReplyGuard H links several :=
  (congrArg (fun X => firstChainWithoutReplyGuard X links several) e).trans
    (bare_same_with H H'.same links several)

/-! ## 7 One block's guard falls -/

/-- **ONE BLOCK's GUARD FALLS**: a block whose decision and runs leave h is its own guarded form,
whatever places are told apart. -/
theorem guarded_self [BEq α] [LawfulBEq α] {h : T → α} {b : Block T Cl} (hd : b.Leaves h)
    (hr : b.RunsLeave h) (but : Place → Bool) : b.guarded (sameBy h) but = b :=
  (still_of_leaves (Or.inr hd) hr).guarded_eq

/-- At a test that always says yes every block is its own guarded form. -/
theorem guarded_idle_self {same : T → T → Bool} (hs : ∀ t s, same t s = true)
    (but : Place → Bool) (b : Block T Cl) : b.guarded same but = b :=
  (still_idle hs but b).guarded_eq

end LPFGuard

#print axioms LPFGuard.linkAt_parts
#print axioms LPFGuard.bare_parts
#print axioms LPFGuard.bare_leavesBut
#print axioms LPFGuard.bare_runsLeave
#print axioms LPFGuard.strike_at
#print axioms LPFGuard.idle_at
#print axioms LPFGuard.bare_same_with
#print axioms LPFGuard.bare_same
#print axioms LPFGuard.guarded_self
#print axioms LPFGuard.guarded_idle_self
