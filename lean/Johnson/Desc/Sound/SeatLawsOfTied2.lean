-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatLawsOfTied2.lean: THE LAST STEP, BY LEAN: the proposition SeatLawsN (Johnson/Desc/Sound/SeatLawsOfTied.lean) at a
piece q's own four fields gives SeatLaws (Johnson/Desc/Sound/TiedSeat.lean) at q: one projection a
clause. And so: `seatLaws_of_tied'`: **TiedAt at the kind's own block's piece, for every value of the public part, gives SeatLaws.**
For a row whose extractor is the identity. [Nonempty P] as there. A RULE OVER LETTERS. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.Sound.SeatLawsOfTied
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {Cl P W : Type} {C : CK} {Fr : Frame}

theorem seatLaws_of_N (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Piece C Fr (P × First.S) Cl W) (N : Numbers)
    (Mg : Meaning P W) (Bst : Block First.S Cl)
    (h : SeatLawsN (Fr := Fr) (W := W) N Mg links ps k q.base q.ds q.back q.err Bst) :
    SeatLaws links ps k q N Mg Bst :=
  ⟨fun B' hS => h.1 B' hS.1, fun B' hS => h.2.1 B' hS.1, fun B' hS => h.2.2.1 B' hS.1,
    fun B' hS => h.2.2.2 B' hS.1⟩

/-- **THE TIE AT THE KIND's OWN BLOCK GIVES SeatLaws.** -/
theorem seatLaws_of_tied' [Nonempty P] (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W) (Bst : Block First.S Cl)
    (H : ∀ z : P, TiedAt N Mg links ps (fun s => (z, s)) k
      (⟨Bst, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr First.S Cl W)) :
    SeatLaws links ps k q N Mg Bst :=
  seatLaws_of_N links ps k q N Mg Bst (seatLaws_of_tied N Mg links ps k q.base q.ds q.back q.err Bst H)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seatLaws_of_N
#print axioms VerifiableInference.Desc.Sound.seatLaws_of_tied'
