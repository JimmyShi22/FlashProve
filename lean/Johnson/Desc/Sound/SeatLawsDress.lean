-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatLawsDress.lean: SeatLaws (Johnson/Desc/Sound/TiedSeat.lean) reads its block Bst through SeatOf alone, and SeatOf through
"narrows" (Johnson/Desc/Sound/MergeNarrow.lean), which reads of Bst its rounds and its decision alone: SO A BLOCK DRESSED WITH ANOTHER TEST ON THE PLAN (planOk) OR
ANOTHER NAME HAS THE SAME SeatLaws. For a lot that lays { blk with planOk := … } where a kind's law speaks of blk.
  `seatLaws_same`: two blocks with one list of rounds and one decision have the same SeatLaws. `seatLaws_dress`: at { blk with planOk := p }.
A rule over letters. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {Cl P W : Type} {C : CK} {Fr : Frame}

theorem seatOf_same {Bst Bst' B' : Block First.S Cl} (hr : Bst'.rounds = Bst.rounds) (hd : Bst'.decide = Bst.decide)
    (h : SeatOf Bst' B') : SeatOf Bst B' := by
  unfold SeatOf Block.Narrows at h ⊢
  rw [hr, hd] at h
  exact h

theorem seatLaws_same (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Piece C Fr (P × First.S) Cl W) (N : Numbers)
    (Mg : Meaning P W) {Bst Bst' : Block First.S Cl} (hr : Bst'.rounds = Bst.rounds) (hd : Bst'.decide = Bst.decide)
    (H : SeatLaws links ps k q N Mg Bst) : SeatLaws links ps k q N Mg Bst' :=
  ⟨fun B' hS => H.1 B' (seatOf_same hr hd hS), fun B' hS => H.2.1 B' (seatOf_same hr hd hS),
    fun B' hS => H.2.2.1 B' (seatOf_same hr hd hS), fun B' hS => H.2.2.2 B' (seatOf_same hr hd hS)⟩

theorem seatLaws_dress (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Piece C Fr (P × First.S) Cl W) (N : Numbers)
    (Mg : Meaning P W) (blk : Block First.S Cl) (p : Bool) (H : SeatLaws links ps k q N Mg blk) :
    SeatLaws links ps k q N Mg { blk with planOk := p } :=
  seatLaws_same links ps k q N Mg rfl rfl H

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seatLaws_same
#print axioms VerifiableInference.Desc.Sound.seatLaws_dress
