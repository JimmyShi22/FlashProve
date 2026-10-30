-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverCut.lean: the five fields of `FirstAsks`
(Honest/Law/CoverAsks.lean) that speak of the first chain's sub-protocols alone, and that the
chain's last sub-protocol has exactly one round, from one hypothesis: the chain's cut into
sub-protocols is the library's written one. The library writes the cut out at the full size:
`cutFirstFull` (Johnson/Desc/Ok/PlanWritten/CutLit.lean) has a row for each of the 358
sub-protocols, with its place and its number of rounds. `cutOf`
(Johnson/Desc/Ok/PlanWritten/CutTest.lean) computes such rows from a list of sub-protocols. The
hypothesis is `hcut : cutOf all = cutFirstFull`. Under it, where a sub-protocol is and whether it
has a round are closed facts on a written list.

The two tests on a place are `fallSeat` and `markSeat` (Honest/Law/CoverSeats.lean). The lemmas use
`he_places`, `hend_places` and `Hs_places` (Honest/Law/CoverPlaces.lean). Three closed statements
are proved by `decide +kernel`, each with a control that rejects.

  1  `cut_places_yes`, `cut_rounds_yes`, `cut_ends_yes`, with `cut_places_control`,
     `cut_rounds_control`, `cut_ends_control`   the closed statements
  2  `cut_row`, `cutOf_at`, `hps_cut`   a sub-protocol's row; the chain's places
  3  `round_cut`, `hlast_cut`, `seal_cut`   which sub-protocol has a round
  4  `members_cut`   the six statements together

Limits.
  * `hcut` is a hypothesis here. The library proves it of the proof file's first chain under a
    hypothesis of its own: `cut_of_head` (Johnson/Road/K4/K4HeadWritten.lean). That theorem is not
    applied here.
  * The written list was printed by a program. No theorem says that it is a description's cut except
    under such a hypothesis.
  * The closed statements are decided at the lists as written in the library: if a
    list changes, the theorems have to be decided anew. The statements are at the library's
    full-size parameter set alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverPlaces
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldRounds)

variable {S Cl : Type}

/-! ## 1 The closed statements -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The written cut's places are the written list of places. -/
theorem cut_places_yes : cutFirstFull.map (·.2.1) = P5J.At.ps := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: without its first row the written cut has other places. -/
theorem cut_places_control : ¬ (cutFirstFull.drop 1).map (·.2.1) = P5J.At.ps := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Every row at a mark's seat, and every row at a fall's seat whose kind is not `frame`, has a
round. -/
theorem cut_rounds_yes : (cutFirstFull.all fun r =>
    !(markSeat r.2.1 || (fallSeat P5J.At.links r.2.1 && r.2.1.kind != KindName.frame)) ||
      r.2.2.1 != 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: not every row has a round. -/
theorem cut_rounds_control : (cutFirstFull.all fun r => r.2.2.1 != 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The row number 356 (counted from 0) has a round, and the row number 357 has exactly one. -/
theorem cut_ends_yes : ((cutFirstFull[356]?).any fun r => r.2.2.1 != 0) = true ∧
    ((cutFirstFull[357]?).any fun r => r.2.2.1 == 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: the row number 352 has no round. -/
theorem cut_ends_control : ((cutFirstFull[352]?).any fun r => r.2.2.1 != 0) = false := by
  decide +kernel

/-! ## 2 A sub-protocol's row -/

/-- The row of a sub-protocol of the list is a row of the written cut. -/
theorem cut_row {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull) {b : Block S Cl}
    (hb : b ∈ all) :
    (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) ∈
      cutFirstFull := by
  rw [← hcut]
  exact List.mem_map.2 ⟨b, hb, rfl⟩

/-- The row of the sub-protocol after `A` is the row number `A.length`. -/
theorem cutOf_at {all A B : List (Block S Cl)} {c : Block S Cl} (e : all = A ++ c :: B) :
    (cutOf all)[A.length]? =
      some (c.name, c.place, c.rounds.length, c.oracles.length, toldRounds c, c.before) := by
  have h1 : (A ++ c :: B)[A.length]? = some c := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  unfold cutOf
  rw [e, List.getElem?_map]
  exact congrArg (Option.map _) h1

/-- The chain's places are the written list of places. -/
theorem hps_cut {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull) :
    all.map (·.place) = P5J.At.ps := by
  have e : (cutOf all).map (·.2.1) = all.map (·.place) := by
    unfold cutOf
    exact List.map_map
  rw [← e, hcut]
  exact cut_places_yes

/-! ## 3 Which sub-protocol has a round -/

/-- A sub-protocol at a mark's seat, or at a fall's seat whose kind is not `frame`, has a round. -/
theorem round_cut {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull) :
    ∀ b ∈ all, (markSeat b.place = true ∨
      (fallSeat P5J.At.links b.place = true ∧ b.place.kind ≠ KindName.frame)) →
      b.rounds ≠ [] := by
  intro b hb h e
  have t : (!(markSeat b.place ||
      (fallSeat P5J.At.links b.place && b.place.kind != KindName.frame)) ||
      b.rounds.length != 0) = true := List.all_eq_true.1 cut_rounds_yes _ (cut_row hcut hb)
  rw [e] at t
  rcases h with h | ⟨h1, h2⟩
  · rw [h] at t
    simp at t
  · rw [h1, bne_iff_ne.2 h2] at t
    simp at t

/-- The last gated sub-protocol (the last of `pre`: all but the chain's last one) has a round. -/
theorem hlast_cut {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hcut : cutOf all = cutFirstFull) (cut : all = pre ++ [e₁]) :
    ∀ A b, pre = A ++ [b] → b.rounds ≠ [] := by
  intro A b e h0
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps_cut hcut, List.length_map]
  have hA : A.length = 356 := by
    rw [cut, e, List.length_append, List.length_append, List.length_singleton,
      List.length_singleton] at hlen
    omega
  have e' : all = A ++ b :: [e₁] := by
    rw [cut, e, List.append_assoc, List.singleton_append]
  have hr := cutOf_at e'
  rw [hcut, hA] at hr
  have t := cut_ends_yes.1
  rw [hr] at t
  have t' : (b.rounds.length != 0) = true := t
  rw [h0] at t'
  simp at t'

/-- The chain's last sub-protocol has exactly one round. -/
theorem seal_cut {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hcut : cutOf all = cutFirstFull) (cut : all = pre ++ [e₁]) : ∃ z, e₁.rounds = [z] := by
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps_cut hcut, List.length_map]
  have hpre : pre.length = 357 := by
    rw [cut, List.length_append, List.length_singleton] at hlen
    omega
  have hr := cutOf_at cut
  rw [hcut, hpre] at hr
  have t := cut_ends_yes.2
  rw [hr] at t
  have t' : (e₁.rounds.length == 1) = true := t
  cases hz : e₁.rounds with
  | nil =>
    rw [hz] at t'
    simp at t'
  | cons z l =>
    cases l with
    | nil => exact ⟨z, rfl⟩
    | cons y l' =>
      rw [hz] at t'
      simp at t'

/-! ## 4 Together -/

/-- Five fields of `FirstAsks` (Honest/Law/CoverAsks.lean) on the first chain's sub-protocols (`Hs`,
`he`, `hlast`, `hend`, `hmr`), and that the last one has exactly one round, at `fallSeat` and
`markSeat`. -/
theorem members_cut {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hcut : cutOf all = cutFirstFull) (cut : all = pre ++ [e₁]) :
    (∀ (A : List (Block S Cl)) (c d : Block S Cl) (B : List (Block S Cl)),
      all = A ++ c :: d :: B → fallSeat P5J.At.links d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ fallSeat P5J.At.links c.place = true) ∧
    fallSeat P5J.At.links e₁.place = false ∧
    (∀ A b, pre = A ++ [b] → b.rounds ≠ []) ∧
    (∀ A b, pre = A ++ [b] →
      ¬ (markSeat b.place = true ∨ (fallSeat P5J.At.links b.place = true ∧ b.rounds ≠ []))) ∧
    (∀ b ∈ pre, markSeat b.place = true → b.rounds ≠ []) ∧ ∃ z, e₁.rounds = [z] :=
  ⟨Hs_places (hps_cut hcut) fun b hb h1 h2 => round_cut hcut b hb (Or.inr ⟨h1, h2⟩),
    he_places (hps_cut hcut) cut, hlast_cut hcut cut, hend_places (hps_cut hcut) cut,
    fun b hb h => round_cut hcut b (by rw [cut]; exact List.mem_append_left _ hb) (Or.inl h),
    seal_cut hcut cut⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_places_yes
#print axioms ProofFile.Honest.cut_places_control
#print axioms ProofFile.Honest.cut_rounds_yes
#print axioms ProofFile.Honest.cut_rounds_control
#print axioms ProofFile.Honest.cut_ends_yes
#print axioms ProofFile.Honest.cut_ends_control
#print axioms ProofFile.Honest.cut_row
#print axioms ProofFile.Honest.cutOf_at
#print axioms ProofFile.Honest.hps_cut
#print axioms ProofFile.Honest.round_cut
#print axioms ProofFile.Honest.hlast_cut
#print axioms ProofFile.Honest.seal_cut
#print axioms ProofFile.Honest.members_cut
