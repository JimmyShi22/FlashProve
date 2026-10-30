-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/LaterKinds.lean: of which kinds the blocks of the proof file's two later
chains are. Theorems only; no file of the description imports this one.
Why. A law on one kind of block has to know every place of the description where a block of that
kind stands. The first chain's places are the driver's table (KindPlaces.lean). Here: the shared
chain has blocks of the kinds `frame`, K14, K1 and K12 alone, the last chain of the kinds `frame`,
K14 and K12 alone.
  `p12At_place`, `k12_place`   the proximity test's block stands at the place that it is made at
                      (fellows by statement: `place_of_p12At`, `place_of_k12` in
                      Johnson/Desc/K12/Law/SharedPlaces.lean, which this file does not import, so
                      that little has to lie beneath it)
  `mem_retype_flat`   a block of the flat list of `c.retype` stands at the place of a block of `c`
  `blocks_kinds`      the kinds of the eight blocks of K14/Blocks.lean, in order
  `shared_kinds`, `second_kinds`   the two chains, from `onlineSharedChain Z = some A` and
                      `onlineLastChain Z = some B`
  `second_places`     the four places of the last chain's flat list, in order
  `no_k10_later`      so in a description that `fileDescBy` makes of these two records no block of
                      the two later chains is of the kind K10
All are unfoldings of the texts that make the blocks. A place is a label: nothing is said here on
what a block does.

-/
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)

theorem p12At_place (a : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

theorem k12_place {T γ : Type} (X : VerifiableInference.Desc.K12.Parts T)
    (p : VerifiableInference.Desc.K12.P12) :
    (VerifiableInference.Desc.K12.proximityTestKind X p : Block T γ).place = p.place := by
  unfold VerifiableInference.Desc.K12.proximityTestKind
  split <;> rfl

/-- A block of the flat list of `c.retype` stands at the place of a block of `c`. -/
theorem mem_retype_flat {σ γ γ' : Type} (c : Chain σ γ) {b : Block σ γ'}
    (h : b ∈ (c.retype : Chain σ γ').blocksInOrder) :
    ∃ b0, (b0 = c.first ∨ b0 ∈ c.front ∨ b0 ∈ c.back ∨ b0 = c.last) ∧ b.place = b0.place := by
  unfold Chain.blocksInOrder Chain.retype at h
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.flatMap_nil, List.not_mem_nil,
    or_false] at h
  rcases h with ((rfl | ⟨_, ⟨y, hy, rfl⟩, rfl⟩) | ⟨_, ⟨y, hy, rfl⟩, rfl⟩) | rfl
  · exact ⟨c.first, .inl rfl, rfl⟩
  · exact ⟨y, .inr (.inl hy), rfl⟩
  · exact ⟨y, .inr (.inr (.inl hy)), rfl⟩
  · exact ⟨c.last, .inr (.inr (.inr rfl)), rfl⟩

/-! ### The shared chain -/

theorem blocks_kinds {P : Desc.K14.P14} {l : List (Block Desc.K14.St Unit)}
    (h : Desc.K14.blocks P = some l) :
    l.map (·.place.kind) = [.K14, .K1, .K14, .K14, .K1, .K14, .K14, .K14] := by
  unfold Desc.K14.blocks at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  rfl

/-- The four kinds of the shared chain. -/
abbrev sharedKind (k : KindName) : Prop := k = .frame ∨ k = .K14 ∨ k = .K1 ∨ k = .K12

theorem blocksOr_kinds (P : Desc.K14.P14) :
    ∀ b ∈ Desc.K14.blocksOr P, sharedKind b.place.kind := by
  intro b hb
  unfold Desc.K14.blocksOr at hb
  cases hl : Desc.K14.blocks P with
  | none =>
    rw [hl] at hb
    have e : b = _ := List.mem_singleton.1 hb
    rw [e]
    exact .inl rfl
  | some l =>
    rw [hl] at hb
    have hk : b.place.kind ∈ l.map (·.place.kind) := List.mem_map.2 ⟨b, hb, rfl⟩
    rw [blocks_kinds hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inl h)

theorem tests_kinds (N : H2U.Places4) :
    ∀ b ∈ VerifiableInference.Desc.K12.Seat.tests N, b.place.kind = KindName.K12 := by
  intro b hb
  unfold VerifiableInference.Desc.K12.Seat.tests at hb
  rcases List.mem_append.1 hb with h | h
  · rw [List.mem_singleton.1 h]
    show (VerifiableInference.Desc.K12.proximityTestKind _ _ : Block _ Unit).place.kind = _
    rw [k12_place, p12At_place]
  · obtain ⟨nO, _, rfl⟩ := List.mem_map.1 h
    show (VerifiableInference.Desc.K12.proximityTestKind _ _ : Block _ Unit).place.kind = _
    rw [k12_place, p12At_place]

theorem shared_kinds {Z : Pub} {A : SharedSeat} (hA : onlineSharedChain Z = some A) {γ : Type} :
    ∀ b ∈ (A.chain.retype : Chain A.σ γ).blocksInOrder, sharedKind b.place.kind := by
  unfold onlineSharedChain laterShared Desc.K14.sharedSeatAt at hA
  split at hA
  · rename_i N _
    cases hA
    intro b hb
    obtain ⟨b0, h0, e⟩ := mem_retype_flat _ hb
    rw [e]
    rcases h0 with rfl | h0 | h0 | rfl
    · exact .inl rfl
    · exact (List.not_mem_nil h0).elim
    · have h1 : b0 ∈ Desc.K14.blocksOr _ ++ VerifiableInference.Desc.K12.Seat.tests N := h0
      rcases List.mem_append.1 h1 with h | h
      · exact blocksOr_kinds _ b0 h
      · exact .inr (.inr (.inr (tests_kinds N b0 h)))
    · exact .inl rfl
  · cases hA

/-! ### The last chain -/

/-- The three kinds of the last chain. -/
abbrev secondKind (k : KindName) : Prop := k = .frame ∨ k = .K14 ∨ k = .K12

theorem second_kinds {Z : Pub} {B : SecondSeat} (hB : onlineLastChain Z = some B) {γ : Type} :
    ∀ b ∈ (B.chain.retype : Chain B.σ γ).blocksInOrder, secondKind b.place.kind := by
  unfold onlineLastChain laterSecond P2Third.secondSeat at hB
  split at hB
  · rename_i N _
    cases hB
    intro b hb
    obtain ⟨b0, h0, e⟩ := mem_retype_flat _ hb
    rw [e]
    rcases h0 with rfl | h0 | h0 | rfl
    · exact .inr (.inl rfl)
    · exact (List.not_mem_nil h0).elim
    · rcases List.mem_cons.1 h0 with rfl | h0
      · exact .inl rfl
      · rw [List.mem_singleton.1 h0]
        refine .inr (.inr ?_)
        show (VerifiableInference.Desc.K12.proximityTestKind _ _ : Block _ Unit).place.kind = _
        rw [k12_place, p12At_place]
    · exact .inl rfl
  · cases hB

/-- The places of the last chain's flat list, in order. -/
theorem second_places {Z : Pub} {B : SecondSeat} (hB : onlineLastChain Z = some B) {γ : Type} :
    (B.chain.retype : Chain B.σ γ).blocksInOrder.map (·.place) =
      [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, ⟨3, none, 2, .K12⟩, ⟨3, none, 3, .frame⟩] := by
  unfold onlineLastChain laterSecond P2Third.secondSeat at hB
  split at hB
  · rename_i N _
    cases hB
    have e : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) :
          Block VerifiableInference.Desc.K12.T12 Unit).place = ⟨3, none, 2, .K12⟩ := by
      rw [k12_place, p12At_place]
    show [(⟨3, none, 0, .K14⟩ : Place), ⟨3, none, 1, .frame⟩,
      { (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
          (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) :
            Block VerifiableInference.Desc.K12.T12 Unit).place with
        chain := 3, link := none, piece := 2 }, ⟨3, none, 3, .frame⟩] = _
    rw [e]
  · cases hB

/-! ### The description -/

/-- In a description that `fileDescBy` makes of the two records of the proof file's later chains, no
block of these two chains is of the kind K10. -/
theorem no_k10_later {σ : Type} {o : SecondHashFunctionArgument} {mk : LinksBy} {Z : Pub} {A : SharedSeat}
    {B : SecondSeat} {get : σ → VerifiableInference.Desc.First.S} {start : InstPub → σ}
    {c : Chain σ Cl} (hA : onlineSharedChain Z = some A) (hB : onlineLastChain Z = some B) :
    (∀ b ∈ (fileDescBy o mk Z A B get start c).shared.blocksInOrder, b.place.kind ≠ KindName.K10) ∧
      (∀ b ∈ (fileDescBy o mk Z A B get start c).second.blocksInOrder, b.place.kind ≠ KindName.K10) := by
  refine ⟨fun b hb hk => ?_, fun b hb hk => ?_⟩
  · have h := shared_kinds hA (γ := Cl) b hb
    rw [hk] at h
    rcases h with h | h | h | h <;> cases h
  · have h := second_kinds hB (γ := Cl) b hb
    rw [hk] at h
    rcases h with h | h | h <;> cases h

end ProofFile.Law

#print axioms ProofFile.Law.shared_kinds
#print axioms ProofFile.Law.second_kinds
#print axioms ProofFile.Law.second_places
#print axioms ProofFile.Law.no_k10_later
