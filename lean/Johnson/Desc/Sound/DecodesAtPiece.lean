-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DecodesAtPiece.lean: "THE STORED TABLE DECODES WITH THE RECORD" RIDES PAST EVERY
PIECE's YES: in the form in which a block's ties to the table of joints ask it. Four small
theorems. A file BESIDE the table: it turns nothing of it.

Why. The last clause of `TiedAt` (Johnson/Desc/Sound/ChainOfPromises.lean) asks, of every piece q
and every yes of it from a to b: `Mg.decodes` at a gives `Mg.decodes` at b. `decodes_rides`
(Johnson/Desc/Sound/DecodesRides.lean) says it of the strings `behind ...`; that a piece's strings
behind a yes ARE these is in the library (`out_behind`, Johnson/Desc/Sound/SendLaw.lean). Here the
two are joined, once for all kinds.

What is said. `decodes_at_piece`: at the filling `decodesOf decT`: a yes of the piece from a to b,
and "where decT answers at the record in front it answers at the record behind": then `decodes`
rides. `decodes_at_piece_pub`: so wherever decT reads of the record's pair its first part alone
(what was handed to the chain) and the yes leaves that part. `decodes_at_seat`: so at a piece over
the bare record, read beside a fixed public part: there nothing is asked of the yes.
`pinW_at_piece`: the stored table's pin goes back from b to a, where decT gives one thing at both.

Limits. (1) That a yes leaves the first part is the piece's make (a lifted piece's): a premise here.
(2) That decT reads the first part alone is a fact on its filling: a premise here. (3) Nothing on
soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.DecodesRides
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK SgX)

section
variable {C : CK} {Fr : Frame} {A Cl W X Cells : Type}

/-- **`decodes` rides past a piece's yes.** get: what the meaning reads of the piece's statement. -/
theorem decodes_at_piece (decT : (ℕ → Option (ℕ × List UInt64)) → X → Option Cells)
    (get : A → X) (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b)
    (h : (decT (strsOf Fr a.2).cell (get a.1)).isSome = true →
      (decT (strsOf Fr a.2).cell (get b.1)).isSome = true) :
    decodesOf decT (get a.1) (strsOf Fr a.2) → decodesOf decT (get b.1) (strsOf Fr b.2) := by
  rw [out_behind p a b τ hb]
  exact decodes_rides decT C Fr p.base p.ds a.2 τ (get a.1) (get b.1) h

/-- So where decT reads the pair's first part alone and the yes leaves that part. -/
theorem decodes_at_piece_pub {P S : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (hd : ∀ c (x x' : P × S), x'.1 = x.1 → decT c x' = decT c x)
    (get : A → P × S) (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (hp : (get b.1).1 = (get a.1).1) :
    decodesOf decT (get a.1) (strsOf Fr a.2) → decodesOf decT (get b.1) (strsOf Fr b.2) :=
  decodes_at_piece decT get p a b τ hb fun h => by rw [hd _ _ _ hp]; exact h

/-- At a piece over the bare record, read beside a fixed public part z: the yes leaves z by the
make of the reading. -/
theorem decodes_at_seat {P S : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (hd : ∀ c (x x' : P × S), x'.1 = x.1 → decT c x' = decT c x) (z : P)
    (p : Piece C Fr S Cl W) (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) :
    decodesOf decT (z, a.1) (strsOf Fr a.2) → decodesOf decT (z, b.1) (strsOf Fr b.2) :=
  decodes_at_piece_pub decT hd (fun s => (z, s)) p a b τ hb rfl

/-- **The stored table's pin goes back past a piece's yes**, where decT gives one thing at both. -/
theorem pinW_at_piece {Tok : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → X → Option Cells)
    (get : A → X) (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (w : Wit Cells Tok MsgT)
    (h : decT (strsOf Fr a.2).cell (get b.1) = decT (strsOf Fr a.2).cell (get a.1)) :
    pinWOf decT (get b.1) (strsOf Fr b.2) w → pinWOf decT (get a.1) (strsOf Fr a.2) w := by
  rw [out_behind p a b τ hb]
  exact pinW_back decT C Fr p.base p.ds a.2 τ (get a.1) (get b.1) w h

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.decodes_at_piece
#print axioms VerifiableInference.Desc.Sound.decodes_at_piece_pub
#print axioms VerifiableInference.Desc.Sound.decodes_at_seat
#print axioms VerifiableInference.Desc.Sound.pinW_at_piece
