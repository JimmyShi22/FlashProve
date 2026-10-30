-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K5Spots.lean: K5's LOT's ROW FOR THE ROUNDS AT THE FULL SIZE, AT THE WRITTEN
SPOTS: IF THE WORK IS 0 AND EVERY ATTENTION SEGMENT's GROUP's PLAN HAS THE WRITTEN own: for every
block b of the lot (H2K5.lotN) and every written spot p with p.place = b.place:
b.rounds = listAt p.name. It is Johnson/AtFull/Rounds/K5At.lean's row with its third premise (on the
names) met at the written list of spots (Johnson/AtFull/Desc/SpotsWritten.lean) by one closed fact.

  k5_spots_names   BY LEAN's KERNEL: a written spot of the kind K5 bears one of the twelve names;
      and there are twelve such spots.
  **k5_row_spots**   THE ROW: hw · hA ⊢ ∀ b ∈ (lotN Z).blocks G, ∀ p ∈ spotsWritten,
      p.place = b.place → b.rounds = listAt p.name.

Limits. hw AND hA ARE PREMISES: nothing here shows that they hold at any public files. That the
description's own spots are the written ones is another file's.

The full size alone. Raised limit: maxRecDepth 1000000. Nothing on soundness.

-/
import Johnson.AtFull.Rounds.K5At
import Johnson.AtFull.Desc.SpotsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Rounds
open VerifiableInference.Desc (KindName)
open Johnson.AtFull.Desc (spotsWritten)

/-- A written spot of the kind K5 bears one of the twelve names; there are twelve such spots. -/
theorem k5_spots_names :
    (spotsWritten.filter fun p => decide (p.place.kind = KindName.K5)).length = 12 ∧
      spotsWritten.all
        (fun p => !decide (p.place.kind = KindName.K5) || decide (p.name ∈ k5Names)) = true := by
  decide +kernel

/-- **THE ROW AT THE WRITTEN SPOTS.** -/
theorem k5_row_spots (Z : ProofFile.Pub) (G : ProofFile.Ground) (hw : k5Work G.W = 0)
    (hA : ∀ x ∈ H2K5.k5Places G, ∀ a, G.W.A[x.2.2]? = some a → a.own = k5OwnW a.own.rows) :
    ∀ b ∈ (H2K5.lotN Z).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = listAt p.name := by
  intro b hb p hp e
  obtain ⟨x, hx, a, ha, hpl, hr⟩ := k5_member hb
  have hk : p.place.kind = KindName.K5 := by rw [e, hpl]
  have c := List.all_eq_true.1 k5_spots_names.2 p hp
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [Bool.not_eq_true', decide_eq_false_iff_not] at c
    exact absurd hk c
  · rw [hr, hw, hA x hx a ha]
    exact k5_list _ (of_decide_eq_true c)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k5_spots_names
#print axioms Johnson.AtFull.Rounds.k5_row_spots
