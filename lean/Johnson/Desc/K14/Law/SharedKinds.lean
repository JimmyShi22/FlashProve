-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SharedKinds.lean: THE KINDS OF THE SHARED CHAIN's PLACES, IN THE PROOF FILE's
WRITTEN DESCRIPTION: the frame's, K14, K1 and K12, AND NO OTHER. Theorems.

WHY. A statement that a kind's sub-protocols stand where its theorems expect them has to cover every
place of that kind in the whole IOP as written in Lean. A proof that has gone through the first
chain then needs one fact about each later chain: none of its sub-protocols stands at a place of
that kind.
  k12_place · p12At_place   the proximity test's sub-protocol stands at its parameters' place, and
                 these at the place that they are handed: in every arm.
  own_kinds      the kind's own list (blocksOr): K14, K1 (the two sendings), or the frame's (the one
                 fallback sub-protocol, whose test on the plan is false, where the rounds cannot be
                 made).
  tests_kinds    the proximity tests (one, or two where the places' numbers hold a second): K12.
  shared_kinds   every sub-protocol of the carried chain's flat list, at K12.Seat's tests and last
                 (the chain's closing sub-protocol).
  shared_kinds_pure   **at what onlineDescription returns.**
  no_other_kind  so a kind that is none of the four has no place there: K10 among them.
What is not claimed. Anything on the last chain or the first. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.K14Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (P12 Parts proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (tests last onGu onGomega)

/-- One of the four. -/
def SharedKind (κ : KindName) : Prop := κ = .frame ∨ κ = .K14 ∨ κ = .K1 ∨ κ = .K12

theorem k12_place {T Cl : Type} (X : Parts T) (p : P12) :
    (proximityTestKind X p : Block T Cl).place = p.place := by
  unfold proximityTestKind
  split <;> rfl

theorem p12At_place (place : VerifiableInference.Desc.Place) (x : H2U.PlaceNums) :
    (H2U.proximityTestParametersAt place x).place = place := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

theorem own_kinds (P : P14) : ∀ x ∈ blocksOr P, SharedKind x.place.kind := by
  intro x hx
  unfold blocksOr at hx
  cases hb : blocks P with
  | none =>
    rw [hb] at hx
    simp only [Option.getD_none, List.mem_singleton] at hx
    subst hx
    exact Or.inl rfl
  | some l =>
    rw [hb] at hx
    simp only [Option.getD_some] at hx
    unfold blocks at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hb
    obtain ⟨_, _, rfl⟩ := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)

theorem tests_kinds (N : H2U.Places4) : ∀ x ∈ tests N, SharedKind x.place.kind := by
  intro x hx
  unfold tests at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at hx
  rcases hx with rfl | ⟨nO, _, rfl⟩
  · refine Or.inr (Or.inr (Or.inr ?_))
    show (proximityTestKind guardedProximityTestParts _ : Block _ Unit).place.kind = _
    rw [k12_place, p12At_place]
  · refine Or.inr (Or.inr (Or.inr ?_))
    show (proximityTestKind guardedProximityTestParts _ : Block _ Unit).place.kind = _
    rw [k12_place, p12At_place]

theorem shared_kinds {Cl' : Type} (c : OnBytes.Model.Verify.Chains) (P : P14) (N : H2U.Places4) :
    ∀ x ∈ ((chainOf c P (tests N) last).retype (Cl' := Cl')).blocksInOrder, SharedKind x.place.kind := by
  intro x hx
  simp only [chainOf, Chain.retype, Chain.blocksInOrder, List.map_nil, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | ⟨y, ⟨z, hz, rfl⟩, rfl⟩) | rfl
  · exact Or.inl rfl
  · rcases hz with hz | hz
    · exact own_kinds P z hz
    · exact tests_kinds N z hz
  · exact Or.inl rfl

/-- **At what onlineDescription returns.** -/
theorem shared_kinds_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) : ∀ x ∈ F.shared.blocksInOrder, SharedKind x.place.kind := by
  obtain ⟨Z, N, B', c, -, -, rfl⟩ := shared_seat_of_pure h
  exact shared_kinds Z.p.chains (p14Of Z.p.chains (beforePointOf N)) N

/-- A kind that is none of the four has no place on the shared chain. -/
theorem no_other_kind {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (κ : KindName) (hκ : ¬ SharedKind κ) :
    ∀ x ∈ F.shared.blocksInOrder, x.place.kind ≠ κ :=
  fun x hx e => hκ (e ▸ shared_kinds_pure h x hx)

/-- K10 has none. -/
theorem no_K10 {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) : ∀ x ∈ F.shared.blocksInOrder, x.place.kind ≠ .K10 :=
  no_other_kind h .K10 (by unfold SharedKind; decide)

end Desc.K14.Law
