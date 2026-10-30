-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Dec.lean: "THE COMMITTED TABLE DECODES" AND THE COMMITTED TABLE's PIN PAST ANY
PIECE, where the decoder of the committed table does not read the verifier's state. One definition,
three theorems. A law file: no sub-protocol imports it. Typed for the code switch; nothing in it
names the kind.

Why. What is owed at a sub-protocol in the chain of promises (`TiedAtR`,
Johnson/Desc/Sound/ChainOfPromisesR.lean) ends in the clause: wherever the piece accepts, "the
committed table decodes" in front gives it behind. THAT CLAUSE HAS NEITHER THE TABLE's PROMISE, NOR
"no mark", NOR "reached" IN HAND: it is asked at every state. At the filling `decodesOf decT`
(Johnson/Desc/Sound/MeaningSig.lean) the sentence reads the committed table's cells, which no piece
turns (`cell_behind`, Johnson/Desc/Sound/DecodesRides.lean), and whatever the parameter decT reads
of the public part and the state.

What is said.
  `DecBlind decT`: decT gives one thing at two states under one public part.
  `dec_at_yes`: so at an accept of any piece over the state alone, the public part z beside it,
    decT gives behind what it gives in front.
  `dec_of_blind`: `decodesOf decT` rides forward past the piece: the last clause of `TiedAtR`, in
    the form of the field dec of `TiesAt` (Johnson/Top/H0/Tw/K2C/TiedForm.lean).
  `pinW_of_blind`: `pinWOf decT` goes back past the piece, at every witness.

Limits. (1) `DecBlind` IS A PREMISE ON A PARAMETER: it is paid only at a closed decT. At a decT that
reads the state it is false. (2) Nothing of any sub-protocol's text is spent. (3) No soundness is
claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.DecodesRides
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound

/-- The decoder of the committed table does not read the verifier's state. -/
def DecBlind {P S Cells : Type}
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) : Prop :=
  ∀ c z s s', decT c (z, s) = decT c (z, s')

section
variable {P S Cl W Cells : Type} {C : CK} {F : Frame}
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)

/-- At an accept of a piece the decoder gives behind what it gives in front. -/
theorem dec_at_yes (hd : DecBlind decT) (p : Piece C F S Cl W) (z : P) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b) :
    decT (strsOf F b.2).cell (z, b.1) = decT (strsOf F a.2).cell (z, a.1) := by
  rw [out_behind p a b τ hb, cell_behind, hd _ z b.1 a.1]

/-- **"The committed table decodes" rides forward past any piece.** -/
theorem dec_of_blind (hd : DecBlind decT) (p : Piece C F S Cl W) (z : P) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (h : decodesOf decT (z, a.1) (strsOf F a.2)) : decodesOf decT (z, b.1) (strsOf F b.2) := by
  unfold decodesOf at h ⊢
  rw [dec_at_yes decT hd p z a b τ hb]
  exact h

/-- **The committed table's pin goes back past any piece**, at every witness. -/
theorem pinW_of_blind {Tok : Type} (hd : DecBlind decT) (p : Piece C F S Cl W) (z : P)
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (w : Wit Cells Tok MsgT) (h : pinWOf decT (z, b.1) (strsOf F b.2) w) :
    pinWOf decT (z, a.1) (strsOf F a.2) w := by
  unfold pinWOf at h ⊢
  rw [← dec_at_yes decT hd p z a b τ hb]
  exact h

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.dec_at_yes
#print axioms VerifiableInference.Desc.First.K2Ties.dec_of_blind
#print axioms VerifiableInference.Desc.First.K2Ties.pinW_of_blind
