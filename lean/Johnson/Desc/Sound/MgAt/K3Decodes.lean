-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Decodes.lean: the kind "lookup" (K3): "DECODES RIDES PAST THE BLOCK's YES"
AT THE COMPOSED MEANING `mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean), AT ALL FIFTY PLACES
AT ONCE: the field `decodes` of `AttAtTable`, `LayAtTable` and `HeadAtTable`, and the field `hDec`
of `DigMean` (Johnson/Desc/First/Look/K3Means.lean).

Main names:
  `firstAlone_of_noRec`: a decoder that does not read the first chain's verifier's state reads the
    pair's first part alone.
  `k3Mg_decodes`: at ANY piece over the verifier's state, whatever its block: where it says yes at
    a and puts out b, "the stored table decodes" at (z, a) gives it at (z, b).
  `k3Mg_decodes_yes`: the same in the three tables' field's form (Yes a b := there is a transcript
    at which the piece says yes); the premise "all but the open link's own part is the same" of
    that field goes unspent.

A joining: `decodes_at_seat` (Johnson/Desc/Sound/DecodesAtPiece.lean) at
`mgAll_decodes`. Kind-free in truth: nothing of K3 is spent.

Limits: hS (the decoder does not read the first chain's state) is a premise on 𝔇: it holds by
unfolding at the seated term's decoder (Johnson/P5J/LettersAt.lean: `noRec_decT`). Nothing on
soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.DecodesAtPiece
import Johnson.Desc.First.Look.K3StoredThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker Run
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Wit)

/-- A decoder that does not read the state reads the pair's first part alone. -/
theorem firstAlone_of_noRec {P S Cells : Type}
    {decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells}
    (hS : ∀ c z s s', decT c (z, s) = decT c (z, s')) :
    ∀ c (x x' : P × S), x'.1 = x.1 → decT c x' = decT c x := by
  rintro c ⟨z, s⟩ ⟨z', s'⟩ h
  obtain rfl : z' = z := h
  exact hS c z' s' s

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  {C : Run.PQ.CK}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **"Decodes" rides past any piece's yes.** -/
theorem k3Mg_decodes (hS : ∀ c z s s', 𝔇.decT c (z, s) = 𝔇.decT c (z, s')) (z : P)
    (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT))
    (a b : Desc.First.S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b)
    (h : (mgAll 𝔇 Mg).decodes (z, a.1) (strsOf Fr a.2)) :
    (mgAll 𝔇 Mg).decodes (z, b.1) (strsOf Fr b.2) :=
  decodes_at_seat 𝔇.decT (firstAlone_of_noRec hS) z p a b τ hb h

/-- **The three tables' field.** -/
theorem k3Mg_decodes_yes (hS : ∀ c z s s', 𝔇.decT c (z, s) = 𝔇.decT c (z, s')) (z : P)
    (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT)) :
    ∀ a b : Desc.First.S × Fr.E.Str, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      (mgAll 𝔇 Mg).decodes (z, a.1) (strsOf Fr a.2) →
      (mgAll 𝔇 Mg).decodes (z, b.1) (strsOf Fr b.2) :=
  fun a b ⟨τ, hb⟩ _ h => k3Mg_decodes 𝔇 Mg hS z p a b τ hb h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.firstAlone_of_noRec
#print axioms VerifiableInference.OnPublicFiles.k3Mg_decodes
#print axioms VerifiableInference.OnPublicFiles.k3Mg_decodes_yes
