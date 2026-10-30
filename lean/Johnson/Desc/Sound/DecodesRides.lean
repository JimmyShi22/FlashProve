-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DecodesRides.lean: "THE STORED TABLE DECODES WITH THE RECORD" RIDES PAST EVERY
BLOCK, FOR ALL KINDS AT ONCE. Three small theorems. A file BESIDE the table of joints: it turns
nothing of it.

Why. The table's promise begins with `decodes`; every block owes that it rides. At the filling
`decodesOf decT` (Johnson/Desc/Sound/MeaningSig.lean) the sentence reads the stored table's cells
and, through the letter decT, the public part with the record. That a stage leaves the stored table
as it is lies in the library (`cellStays`, Johnson/Desc/Sound/StringsStay.lean). So what a kind owes
is one fact on decT and the fields that its yes turns.

What is said. `cell_behind`: the cells behind a block are the cells in front. `decodes_rides`: where
decT answers at the record in front it answers at the record behind: then `decodes` rides.
`pinW_back`: where decT gives one thing at both records, the stored table's pin behind is the pin
in front: for the riding of `pinW`.

Limits. (1) Rules over letters. (2) That a piece's strings behind ARE `behind ...` of the strings in
front is the piece's make: not said here. (3) The premise on decT is paid only at a filling of decT.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK SgX)

/-- The stored table's cells behind a block are the cells in front of it. -/
theorem cell_behind (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT C ds)) : (strsOf F (behind C F b ds y τ)).cell = (strsOf F y).cell :=
  funext fun x => cellStays C F b ds y τ x

/-- **`decodes` rides past a block** whose yes turns nothing that makes decT fall silent. -/
theorem decodes_rides {A Cells : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (C : CK) (F : Frame) (b : ℕ)
    (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (a a' : A)
    (h : (decT (strsOf F y).cell a).isSome = true → (decT (strsOf F y).cell a').isSome = true) :
    decodesOf decT a (strsOf F y) → decodesOf decT a' (strsOf F (behind C F b ds y τ)) := by
  intro hd
  unfold decodesOf at hd ⊢
  rw [cell_behind]
  exact h hd

/-- **The stored table's pin behind a block is the pin in front**, where decT gives one thing at
both records. -/
theorem pinW_back {A Cells Tok : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (C : CK) (F : Frame) (b : ℕ)
    (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (a a' : A) (w : Wit Cells Tok MsgT)
    (h : decT (strsOf F y).cell a' = decT (strsOf F y).cell a) :
    pinWOf decT a' (strsOf F (behind C F b ds y τ)) w → pinWOf decT a (strsOf F y) w := by
  intro hp
  unfold pinWOf at hp ⊢
  rw [cell_behind, h] at hp
  exact hp

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.decodes_rides
#print axioms VerifiableInference.Desc.Sound.pinW_back
