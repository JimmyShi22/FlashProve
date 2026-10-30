-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean: THE NAME COLUMN, ONCE FOR ALL LOTS: the rows of the
rounds' column (SkelRoundsParts.lean: hL) speak of "the spot p at the block's place" and of p's
name. Where the places are the written ones, that name is a closed function of the block's place.
Definitions, statements and proofs.
  `nameW a`         the written name at the place a; the empty name where no written place is a
  `names_full`      A CLOSED FACT, DECIDED BY LEAN's KERNEL: at each written place's place the name
                    that is looked up is its own. It would fail if two written places had one place
                    and two names
  `rows_by_place`   from "Q holds of `nameW b.place` and b's rounds, at every block of every lot":
                    hL, at every Q
Limits. Nothing is paid. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Data
import Johnson.Desc.ProofFile.Law.Skel.SkelParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc

/-- The written name at a place. -/
def nameW (a : Place) : String := nameAtSk spotsW a ""

theorem names_full : (spotsW.all fun p => nameW p.place == p.name) = true := by
  decide +kernel

theorem rows_by_place {Q : String → List Fmt.DeclaredRound → Prop} {T : PureSeat} {B : PureBase}
    (h₁ : B.spots = spotsW)
    (w : ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, Q (nameW b.place) b.rounds) :
    ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Q p.name b.rounds := by
  intro L hL b hb p hp e
  rw [h₁] at hp
  have n : nameW p.place = p.name := eq_of_beq (List.all_eq_true.1 names_full p hp)
  rw [← n, e]
  exact w L hL b hb

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.names_full
#print axioms ProofFile.Sk.Full.rows_by_place
