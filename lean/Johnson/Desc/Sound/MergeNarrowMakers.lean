-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeNarrowMakers.lean: `Block.Narrows` (the same declared rounds; a yes only
where the other says yes, with the same record: Johnson/Desc/Sound/MergeNarrow.lean) IN A ROW AND
UNDER THE STRICT READING; and the rule read from the given piece's side. Small lemmas with their
proofs.

Why. A seat lays a kind's block into a chain with tests of its own behind the block's `decide` (no
mark in the record behind; a field that no block but one may write is unturned), one around the
other, under a name of the seat's. Each narrows. A description's piece holds `below` of the
outermost.

Main names:
  `Block.Narrows.refl`, `.trans`; `Block.Same.narrows`.
  `Block.Narrows.below`: b'.Narrows b gives (below b').Narrows (below b).
  `goodIn_of_narrows`: a piece that holds a block which narrows B owes what the piece with B in its
    place owes.

Limits: nothing is gained here from what the narrower block's yes adds (`goodIn_narrow` has that).
Rounds and `decide` alone. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

theorem Block.Narrows.refl (b : Block S Cl) : b.Narrows b := ⟨rfl, fun _ _ _ _ h => h⟩

theorem Block.Narrows.trans {b'' b' b : Block S Cl} (h : b''.Narrows b') (h' : b'.Narrows b) :
    b''.Narrows b :=
  ⟨h.1.trans h'.1, fun s rs gs t e => h'.2 s rs gs t (h.2 s rs gs t e)⟩

theorem Block.Same.narrows {b' b : Block S Cl} (h : b'.Same b) : b'.Narrows b :=
  ⟨h.1, fun s rs gs t e => by rw [← h.2]; exact e⟩

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- A block that refuses more still does so under the strict reading. -/
theorem _root_.VerifiableInference.Desc.Block.Narrows.below {b' b : Block S Cl}
    (h : b'.Narrows b) : (below b').Narrows (below b) := by
  refine ⟨h.1, fun s rs gs t e => ?_⟩
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime") = .ok t := e
  show (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok t
  split at e'
  · rename_i hk
    rw [if_pos hk]
    exact h.2 s rs gs t e'
  · cases e'

/-- **From the given piece's side**: p's block narrows B; the piece with B in its place owes. -/
theorem goodIn_of_narrows (p : Piece C F S Cl W) (B : Block S Cl) (h : p.b.Narrows B)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (g : ({ p with b := B } : Piece C F S Cl W).GoodIn on on' R R') : p.GoodIn on on' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (g a ha)
  intro τ hτ b hb
  exact hτ b (out_narrow ({ p with b := B } : Piece C F S Cl W) p.b h a b τ hb)


end VerifiableInference.Desc.Sound
