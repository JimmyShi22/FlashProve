-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HearsAsLot.lean: a term of the form that the description seats at K4's places (by
reading: Johnson/Desc/ProofFile/Lot/K4Yes.lean's Limits) hears as K4's own block at the first
chain's record, and declares K4's rounds. The term: `Block.guarded same but { { guardMark (k4Block
x) with name := n } with place := a }`; the parameters: p := { x.2 with k3Runs := true }, x a
letter. Three theorems of a few lines: calls.

  `hearsAs_seatedLot`: `HearsAs seatS p` (Johnson/Desc/Plain/K04Plain.lean), the second premise
    inside `K04Law` and `K04LawAt`, at that term: `hearsAs_of_yes` at `k4Seated_under` (K4Yes.lean)
    and `hearsAs_atS` (Johnson/Desc/First/K4/SeatS.lean).
  `declares_seatedLot`: `Declares` (Johnson/Road/K4/PieceTiled.lean) at that term and p: none of the
    layers laid over K4's own block turns the field rounds: by unfolding.
  `k4_owed_seatedLot`: so a piece that holds that term below the test on the words, with K4's
    written rounds and no round behind its own, is owed just its stretch (`k4_owed`).

Limits. same, but, x, n and a are letters. That the first chain holds this term at K4's places is
not said here (K4Yes.lean's Limits: at a place behind which a lot's block of the kind frame is
joined the seated term is another). That a piece holds the term is a premise. `HearsAs` speaks of
the field decide alone, `Declares` of the field rounds alone. No law is called: K04_law is not
proved by this. Nothing on soundness.
-/
import Johnson.Desc.Plain.K04Plain
import Johnson.Desc.First.K4.SeatS
import Johnson.Desc.ProofFile.Lot.K4Yes
import Johnson.Road.K4.PieceTiled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes.Desc.First.K4 (Par blockAtS seatS hearsAs_atS k4Ds)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.Plain.K04 (HearsAs hearsAs_of_yes)

/-- **A term of the seated form hears as K4's own block at the first chain's record.** -/
theorem hearsAs_seatedLot (same : S → S → Bool) (but : Place → Bool) (x : Bool × Par) (n : String)
    (a : Place) :
    HearsAs seatS { x.2 with k3Runs := true }
      (Block.guarded same but
        { { ProofFile.guardMark (ProofFile.k4Block x) with name := n } with place := a }) :=
  hearsAs_of_yes seatS { x.2 with k3Runs := true } (blockAtS { x.2 with k3Runs := true }) _
    (ProofFile.k4Seated_under same but x n a) (hearsAs_atS { x.2 with k3Runs := true })

/-- **A term of the seated form declares K4's rounds.** -/
theorem declares_seatedLot (same : S → S → Bool) (but : Place → Bool) (x : Bool × Par)
    (n : String) (a : Place) :
    Declares
      (Block.guarded same but
        { { ProofFile.guardMark (ProofFile.k4Block x) with name := n } with place := a })
      { x.2 with k3Runs := true } :=
  rfl

/-- **A piece that holds a term of the seated form is owed just its stretch.** -/
theorem k4_owed_seatedLot {W : Type} {C : CK} {F : Frame} (pc : Piece C F S ProofFile.Cl W)
    (same : S → S → Bool) (but : Place → Bool) (x : Bool × Par) (n : String) (a : Place)
    (hb : pc.b = below (Block.guarded same but
      { { ProofFile.guardMark (ProofFile.k4Block x) with name := n } with place := a }))
    (hds : k4Ds { x.2 with k3Runs := true } = some pc.ds) (hback : pc.back = []) : pc.Owed :=
  k4_owed pc (by rw [hb]; exact declares_below (declares_seatedLot same but x n a)) hds hback

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hearsAs_seatedLot
#print axioms OnBytes.Road.K4.declares_seatedLot
#print axioms OnBytes.Road.K4.k4_owed_seatedLot
