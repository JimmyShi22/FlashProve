-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsChains
/-
Johnson/Desc/K12/Law/SitsOnly.lean: BY THE LABEL: NO OTHER ENTRY OF THE THREE CHAINS' FLAT LISTS
BEARS THE KIND K12 IN ITS FIELD place THAN THE FOUR OF Johnson/Desc/K12/Law/SitsChains.lean. Of the
chains' own makers in the library's tree. BOOK-KEEPING ON
LABELS. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  blocksOr_kinds · shared_only     the shared chain: an entry of the kind K12 is guEntry or, where
      the plan has that test, omegaEntry.
  second_only          the last chain: it is ownEntry.
  addresses_kind · hearKinds_no · linkPlaces_kinds · linkAt_kinds · back_k12 · firstChain_only    
      the first chain (off Shape.firstChain_shape · First.guarded_link_places ·
      place_of_blockAt): the driver stamps every place: K12 stands in backKinds alone, once: the
      entry is firstEntry.
LIMITS. «place» is a label that a maker or the driver stamps: which block bears it no table says:
what block it is: SitsChains.lean and a file over the seat.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

theorem blocksOr_kinds (P : _root_.Desc.K14.P14) :
    ∀ b ∈ _root_.Desc.K14.blocksOr P, b.place.kind ≠ .K12 := by
  intro b hb
  unfold _root_.Desc.K14.blocksOr at hb
  cases hB : _root_.Desc.K14.blocks P with
  | none =>
    rw [hB] at hb
    simp only [Option.getD_none, List.mem_singleton] at hb
    subst hb
    intro e; cases e
  | some l =>
    rw [hB] at hb
    simp only [Option.getD_some] at hb
    unfold _root_.Desc.K14.blocks at hB
    simp only [bind, Option.bind, pure] at hB
    split at hB
    · cases hB
    · cases hB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (intro e; cases e)

/-- The shared chain. -/
theorem shared_only (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) :
    ∀ E ∈ ((_root_.Desc.K14.chainOf c P (Seat.tests N) Seat.last).retype (Cl' := Cl')).blocksInOrder,
      E.place.kind = .K12 → E = guEntry Cl' N ∨ ∃ nO, N.O = some nO ∧ E = omegaEntry Cl' nO := by
  intro E hE hk
  rw [shared_cut] at hE
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false,
    sharedPre] at hE
  rcases hE with (rfl | ⟨b, hb, rfl⟩) | rfl | ⟨nO, hO, rfl⟩ | rfl
  · cases hk
  · exact absurd hk (blocksOr_kinds P b hb)
  · exact Or.inl rfl
  · exact Or.inr ⟨nO, by simpa using hO, rfl⟩
  · cases hk

/-- The last chain. -/
theorem second_only (Cl' : Type) (p : Third.P₁₄) (K : Blk') :
    ∀ E ∈ ((Third.lastChainWithOwnTest p (onOwn K)).retype (Cl' := Cl')).blocksInOrder,
      E.place.kind = .K12 → E = ownEntry Cl' K := by
  intro E hE hk
  rw [second_cut] at hE
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, secondPre] at hE
  rcases hE with (rfl | rfl) | rfl | rfl
  · cases hk
  · cases hk
  · rfl
  · cases hk

/-! ### the first chain -/

theorem addresses_kind (link : Option Nat) (ks : List KindName) :
    ∀ a ∈ First.addresses link ks, a.kind ∈ ks := by
  intro a ha
  unfold First.addresses at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  exact (List.mem_zipIdx' hx).2 ▸ List.getElem_mem _

theorem hearKinds_no (sub : First.ModelPart) (first : Bool) :
    KindName.K12 ∉ First.kindsBeforeBatching sub first := by
  cases sub <;> cases first <;> decide

/-- No place of a segment's table bears the kind K12. -/
theorem linkPlaces_kinds (l : Nat) (sub : First.ModelPart) :
    ∀ a ∈ First.linkPlaces l sub, a.kind ≠ .K12 := by
  intro a ha
  simp only [First.linkPlaces, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
  rcases ha with (((rfl | ha) | (rfl | rfl)) | ha) | rfl
  · intro e; cases e
  · intro e
    exact hearKinds_no sub (l == 0) (e ▸ addresses_kind _ _ a ha)
  · intro e; cases e
  · intro e; cases e
  · unfold First.closeAddresses at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    have hx' : x.1 ∈ First.closeKinds := (List.mem_zipIdx' hx).2 ▸ List.getElem_mem _
    intro e
    rw [show x.1 = KindName.K12 from e] at hx'
    exact absurd hx' (by decide)
  · intro e; cases e

/-- No block of a segment bears the kind K12: by the table of a guarded segment's places. -/
theorem linkAt_kinds {S Cl : Type} (H : First.Blocks S Cl) (l : Nat) (sub : First.ModelPart)
    (L : Link S Cl) (h : First.linkAt H l sub = some L) (same : S → S → Bool)
    (but : Place → Bool) : ∀ E ∈ (L.guarded same but).blocksInOrder, E.place.kind ≠ .K12 := by
  intro E hE
  apply linkPlaces_kinds l sub
  rw [← First.guarded_link_places same but H l sub L h]
  exact List.mem_map.2 ⟨E, hE, rfl⟩

theorem back_k12 (several : Bool) :
    ∀ a ∈ First.addresses none (First.backKinds several), a.kind = .K12 → a = a12 := by
  cases several <;> decide

/-- The first chain: the one entry of the kind K12 is the entry at a12. -/
theorem firstChain_only {S Cl : Type} (H : First.Blocks S Cl) (links : List First.ModelPart)
    (several : Bool) (c : Chain S Cl) (h : First.firstChain H links several = some c)
    (b : Block S Cl) (hb : H.block a12 = some b) :
    ∀ E ∈ c.blocksInOrder, E.place.kind = .K12 → E = firstEntry H.same b := by
  obtain ⟨_, c0, ⟨hFirst, hFront, hLinks, hBack, hLast⟩, rfl⟩ := Shape.firstChain_shape h
  intro E hE hK
  rw [Chain.flat_eq] at hE
  simp only [Chain.guarded, hFront, List.map_nil, List.mem_cons, List.mem_append,
    List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hE
  rcases hE with ((rfl | ⟨_, ⟨L, hL, rfl⟩, hE⟩) | ⟨_, ⟨b', hb', rfl⟩, rfl⟩) | rfl
  · rw [show (Block.asBare (Block.guarded H.same First.hearsReply c0.first)).place.kind =
      c0.first.place.kind from rfl, hFirst] at hK
    cases hK
  · have hm : some L ∈ c0.links.map some := List.mem_map.2 ⟨L, hL, rfl⟩
    rw [hLinks] at hm
    obtain ⟨x, _, e⟩ := List.mem_map.1 hm
    exact absurd hK (linkAt_kinds H x.2 x.1 L e _ _ E hE)
  · have hm : some b' ∈ c0.back.map some := List.mem_map.2 ⟨b', hb', rfl⟩
    rw [hBack] at hm
    obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
    have hp := First.place_of_blockAt H a b' e
    have ha12 : a = a12 := back_k12 several a ha (hp ▸ hK)
    subst ha12
    unfold First.blockAt at e
    rw [hb] at e
    cases e
    rfl
  · rw [show (Block.asBare (Block.guarded H.same First.hearsReply c0.last)).place.kind =
      c0.last.place.kind from rfl, hLast] at hK
    cases hK

end H2K.JointK

#print axioms H2K.JointK.firstChain_only
#print axioms H2K.JointK.linkAt_kinds
#print axioms H2K.JointK.shared_only
#print axioms H2K.JointK.second_only
