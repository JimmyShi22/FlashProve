-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsLot.lean: every block of the kind "lookup"'s lot is the kind's constant at the
block's own place. One theorem and a corollary.

Why. The law of a link takes, for each run of claims that stands in a link's order, a tie down to
the run that the kind's own block states. At the seat that tie ends at "some block of some lot that
bears the place". Which block that is must be said of EVERY block of the lot: nothing says that only
one block bears a place.

Main names:
  `k03_lot_is`: a block of the lot's blocks, at any letters of the ground, is what `K3.theStated`
    returns at the lot's letters and the block's own place.
  `k03_lot_at`: so a block of the lot that bears the place a is what `K3.theStated` returns at a:
    two blocks of the lot at one place are one block.

Whose lemmas: `IM.blocks_mem` and `IM.k3Hear_mem` are those of the files of Johnson/IMR/.

Limits: nothing on which runs the constant states (Johnson/Desc/First/Look/K3OwnIs.lean has their
names), nor on what they are worth. Nothing on soundness; nothing on hiding.


-/
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **Every block of the lot is the constant at its own place.** -/
theorem k03_lot_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {b' : Block S Cl}
    (h : b' ∈ (K3Lot.lot Z).blocks G) :
    VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X
      Z.first.codes Z.first.shape b'.place = some b' := by
  rcases IM.blocks_mem h with ⟨y, hy, -⟩ | h
  · exact nomatch hy
  · exact IM.k3Hear_mem h

/-- A block of the lot at the place a is the constant at a. -/
theorem k03_lot_at {Z : ProofFile.Pub} {G : ProofFile.Ground} {b' : Block S Cl} {a : Place}
    (h : b' ∈ (K3Lot.lot Z).blocks G) (ha : b'.place = a) :
    VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X
      Z.first.codes Z.first.shape a = some b' := by
  subst ha
  exact k03_lot_is h

end K3Lot
