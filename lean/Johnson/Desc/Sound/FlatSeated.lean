-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FlatSeated.lean: A BLOCK OF THE DRIVER'S OWN FIRST CHAIN, AT A PLACE OF A KIND
OTHER THAN K9 AND "frame", NARROWS WHAT THE SEAT LAYS AT THAT PLACE. One definition, three lemmas,
one theorem. By unfolding of the driver's text (Johnson/Desc/First/Driver/Chain.lean).

Why. A kind's law speaks of the kind's block; a seat hands the driver a block for each place
(`Blocks.block`); the driver stamps the place into it, lays the guard on the reply's seat around it
(`firstChain`) and Block.lean's makers lay it into the flat list. A law is carried to the piece that
holds a block of the flat list under "that block narrows the kind's" (`goodIn_of_narrows`,
Johnson/Desc/Sound/MergeNarrowMakers.lean). Here the first half of that premise is paid, for every
seat: from the flat list's entry to the seat's own block at the entry's place.

  `SeatedAt H B`: the seat H has a block at B's place, and B narrows it.
  **`flat_seated`**: every block B of `(firstChain H links several)`'s flat list whose place is of a
    kind other than K9 and "frame" is so.

Limits. The batching (a maker, `Blocks.batch`) and the closing's two blocks of the kind K9 are left
out; so are Block.lean's own blocks without a round, the front and the seal. Rounds and `decide`
alone. That a run goes by this chain is not said. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GuardAtDriver
import Johnson.Desc.Sound.SeatNarrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {S Cl : Type}

/-- The seat has a block at B's place, and B narrows it. -/
def SeatedAt (H : Blocks S Cl) (B : Block S Cl) : Prop :=
  ∃ b₀, H.block B.place = some b₀ ∧ B.Narrows b₀

/-- What the driver makes of the seat's block at a place, behind the guard. -/
theorem seatedAt_blockAt (H : Blocks S Cl) {a : Place} {b : Block S Cl}
    (h : blockAt H a = some b) : SeatedAt H (b.guarded H.same hearsReply) := by
  unfold blockAt at h
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨b₀, e₀, (guarded_narrows H.same hearsReply _).trans ⟨rfl, fun _ _ _ _ e => e⟩⟩

/-- Another test on the plan turns neither the place, nor the rounds, nor `decide`. -/
theorem SeatedAt.planOk {H : Blocks S Cl} {B : Block S Cl} (h : SeatedAt H B) (x : Bool) :
    SeatedAt H { B with planOk := x } := by
  obtain ⟨b₀, e, n⟩ := h
  exact ⟨b₀, e, n.1, n.2⟩

/-- In a segment. -/
theorem link_flat_seated (H : Blocks S Cl) {l : Nat} {sub : ModelPart} {L : Link S Cl}
    (h : linkAt H l sub = some L) (B : Block S Cl)
    (hB : B ∈ (L.guarded H.same hearsReply).blocksInOrder) (hf : B.place.kind ≠ .frame)
    (h9 : B.place.kind ≠ .K9) : SeatedAt H B := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  simp only [Link.blocksInOrder, Link.guarded, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at hB
  rcases hB with (((rfl | ⟨b, hb, rfl⟩) | rfl | rfl) | ⟨b, hb, rfl⟩) | rfl
  · exact absurd rfl hf
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hh b hb
    exact seatedAt_blockAt H e
  · exact absurd rfl h9
  · exact absurd rfl hf
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hc b hb
    exact seatedAt_blockAt H e
  · exact absurd rfl hf

/-- **EVERY BLOCK OF THE DRIVER's FIRST CHAIN AT A PLACE OF A KIND OTHER THAN K9 AND "frame" NARROWS
WHAT THE SEAT LAYS THERE.** -/
theorem flat_seated {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) (B : Block S Cl) (hB : B ∈ c.blocksInOrder)
    (hf : B.place.kind ≠ .frame) (h9 : B.place.kind ≠ .K9) : SeatedAt H B := by
  obtain ⟨c₀, h₀, rfl⟩ := firstChain_some h
  unfold firstChainWithoutReplyGuard at h₀
  simp only [Option.bind_eq_bind, Option.pure_def] at h₀
  split at h₀
  · cases h₀
  obtain ⟨_, _, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨ls, hl, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨back, hb, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  cases h₀
  simp only [Chain.blocksInOrder, Chain.guarded, List.map_nil, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_flatMap, List.not_mem_nil, or_false, false_or] at hB
  rcases hB with ((rfl | ⟨L', ⟨L, hL, rfl⟩, hB⟩) | ⟨b', ⟨b, hbm, rfl⟩, rfl⟩) | rfl
  · exact absurd rfl hf
  · obtain ⟨x, _, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L hL
    exact link_flat_seated H e B hB hf h9
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hb b hbm
    exact (seatedAt_blockAt H e).planOk _
  · exact absurd rfl hf

#print axioms seatedAt_blockAt
#print axioms link_flat_seated
#print axioms flat_seated

end VerifiableInference.Desc.First
