-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverPlaces.lean: three of the hypotheses of `debts_letter`
(Honest/Law/CoverDebts.lean) and `localDebts_sorts` (Honest/Law/CoverSorts.lean; not in the sealed
library) on where falls and marks may be, proved from the written list of the first chain's places.
The two theorems ask several things of the chain's sub-protocols: `Hs`, `he`, `hend`, `hmr`, `hlast`
(they are also fields of `FirstAsks`, Honest/Law/CoverAsks.lean; not in the sealed library). Here
the two tests on a place are `fallSeat` and `markSeat` (Honest/Law/CoverSeats.lean), and the chain's
places are the list `P5J.At.ps` (Johnson/P5J/LettersAt.lean; hypothesis `hps`). Then `he` and `hend`
hold, and `Hs` follows from one hypothesis, `hround`: a sub-protocol at a fall's seat whose kind is
not `frame` has a round.

They use `seat_front` and `seats_counts` (Honest/Law/Rule/SeatsFacts.lean). `seats_end_yes` and
`seats_end_control` are closed statements on the written list, proved by `decide +kernel`.

  1  `placeOf_at`, `placeOf_next`   the place of a sub-protocol, by its number in the list
  2  `seats_end_yes`, `seats_end_control`, `seats_end`   the last two places are neither a fall's
     seat nor a mark's
  3  `he_places`, `hend_places`, `Hs_places`   the three hypotheses

Limits.
  * `hps` (the chain's places are the written list) is a hypothesis. The library proves it of the
    proof file's first chain under a hypothesis of its own.
  * `hround` is a hypothesis: that a sub-protocol has a round is not proved here of any
    sub-protocol. `hmr` and `hlast` are hypotheses of the same form and are not treated.
  * The closed statements are decided at the list as written in the library: if the
    list changes, the theorems have to be decided anew.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.SeatsFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block)

variable {S Cl : Type}

/-! ## 1 A sub-protocol's place, by its number -/

/-- The place of the sub-protocol after `A` is the list's entry number `A.length`. -/
theorem placeOf_at {all : List (Block S Cl)} {ps : List Place} (hps : all.map (·.place) = ps)
    {A B : List (Block S Cl)} {c : Block S Cl} (e : all = A ++ c :: B) :
    ps[A.length]? = some c.place := by
  have h1 : (A ++ c :: B)[A.length]? = some c := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  rw [← hps, e, List.getElem?_map]
  exact congrArg (Option.map (·.place)) h1

/-- The same for the next one. -/
theorem placeOf_next {all : List (Block S Cl)} {ps : List Place} (hps : all.map (·.place) = ps)
    {A B : List (Block S Cl)} {c d : Block S Cl} (e : all = A ++ c :: d :: B) :
    ps[A.length + 1]? = some d.place := by
  have e' : all = (A ++ [c]) ++ d :: B := e.trans (List.append_assoc A [c] (d :: B)).symm
  have h := placeOf_at hps e'
  have hl : (A ++ [c]).length = A.length + 1 := by simp
  rw [hl] at h
  exact h

/-! ## 2 The last two places -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem seats_end_yes : ((List.range 358).all fun i => decide (i < 356) ||
    match P5J.At.ps[i]? with
    | some p => !fallSeat P5J.At.links p && !markSeat p
    | none => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: the same test from the place number 340 on rejects. -/
theorem seats_end_control : ((List.range 358).all fun i => decide (i < 340) ||
    match P5J.At.ps[i]? with
    | some p => !fallSeat P5J.At.links p && !markSeat p
    | none => true) = false := by
  decide +kernel

/-- From the place number 356 on no place is a seat of a fall or of a mark. -/
theorem seats_end (i : Nat) (p : Place) (hi : 356 ≤ i) (hp : P5J.At.ps[i]? = some p) :
    fallSeat P5J.At.links p = false ∧ markSeat p = false := by
  have hi' : i < 358 := by
    by_contra hn
    have e : P5J.At.ps[i]? = none :=
      List.getElem?_eq_none (by rw [seats_counts.1]; omega)
    rw [e] at hp
    cases hp
  have h := List.all_eq_true.1 seats_end_yes i (List.mem_range.2 hi')
  have hn : decide (i < 356) = false := decide_eq_false (by omega)
  rw [hp, hn, Bool.false_or] at h
  simpa using h

/-! ## 3 The three hypotheses -/

/-- The chain's last sub-protocol is at no seat of a fall. -/
theorem he_places {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hps : all.map (·.place) = P5J.At.ps) (cut : all = pre ++ [e₁]) :
    fallSeat P5J.At.links e₁.place = false := by
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps, List.length_map]
  have hpre : pre.length = 357 := by
    rw [cut, List.length_append, List.length_singleton] at hlen
    omega
  exact (seats_end pre.length e₁.place (by omega) (placeOf_at hps cut)).1

/-- The last gated sub-protocol (the last of `pre`: all but the chain's last one) is at no seat of a
mark, and is not at a seat of a fall with a round: the form in which `hend` is asked. -/
theorem hend_places {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hps : all.map (·.place) = P5J.At.ps) (cut : all = pre ++ [e₁]) :
    ∀ A b, pre = A ++ [b] →
      ¬ (markSeat b.place = true ∨ (fallSeat P5J.At.links b.place = true ∧ b.rounds ≠ [])) := by
  intro A b e
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps, List.length_map]
  have hA : A.length = 356 := by
    rw [cut, e, List.length_append, List.length_append, List.length_singleton,
      List.length_singleton] at hlen
    omega
  have e' : all = A ++ b :: [e₁] := by
    rw [cut, e, List.append_assoc, List.singleton_append]
  obtain ⟨h1, h2⟩ := seats_end A.length b.place (by omega) (placeOf_at hps e')
  rintro (h | ⟨h, -⟩)
  · rw [h2] at h
    cases h
  · rw [h1] at h
    cases h

/-- Right before a sub-protocol without a round at a fall's seat there is one with a round at a
fall's seat. `hround`: a sub-protocol at a fall's seat whose kind is not `frame` has a round. -/
theorem Hs_places {all : List (Block S Cl)} (hps : all.map (·.place) = P5J.At.ps)
    (hround : ∀ b ∈ all, fallSeat P5J.At.links b.place = true → b.place.kind ≠ KindName.frame →
      b.rounds ≠ []) :
    ∀ (A : List (Block S Cl)) (c d : Block S Cl) (B : List (Block S Cl)),
      all = A ++ c :: d :: B → fallSeat P5J.At.links d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ fallSeat P5J.At.links c.place = true := by
  intro A c d B e hd h0
  have hc : c ∈ all := by
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  have hdm : d ∈ all := by
    rw [e]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hk : d.place.kind = KindName.frame := by
    by_contra hn
    exact hround d hdm hd hn h0
  obtain ⟨h1, h2⟩ :=
    seat_front A.length c.place d.place (placeOf_at hps e) (placeOf_next hps e) hd hk
  refine ⟨hround c hc h1 ?_, h1⟩
  rw [h2]
  decide

end ProofFile.Honest

#print axioms ProofFile.Honest.placeOf_at
#print axioms ProofFile.Honest.placeOf_next
#print axioms ProofFile.Honest.seats_end_yes
#print axioms ProofFile.Honest.seats_end_control
#print axioms ProofFile.Honest.seats_end
#print axioms ProofFile.Honest.he_places
#print axioms ProofFile.Honest.hend_places
#print axioms ProofFile.Honest.Hs_places
