-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/DecAtMgAll.lean: THE CODE SWITCH's TIE "dec" AT THE COMPOSED MEANING OF THE
OPEN CLAIMS (`mgAll D Mg`, Johnson/Desc/Sound/MgAll.lean). One theorem. A law file: no
sub-protocol imports it.

What is said. `k02_dec`: the field dec of `TiesAt` (Johnson/Top/H0/Tw/K2C/TiedForm.lean), to the
letter, at Mg := `mgAll D Mg₀`; it is also the last clause of `TiedAtR`
(Johnson/Desc/Sound/ChainOfPromisesR.lean), read at the state alone with the public part z beside
it. By `mgAll_decodes` (the field is `decodesOf D.decT`) and `dec_of_blind` (Dec.lean).

THE ONE PREMISE. `DecBlind D.decT`: the parameter decT, the decoder of the committed table, does not
read the verifier's state. decT IS ONE OF THE PARAMETERS OF D: NO CLOSED TERM HERE. At `constD h`
the premise is paid: `decBlind_at` (AtConstant.lean).
(Where this and lean/THEOREM.md differ, the page
holds.)

Limits. Nothing of the code switch's text is spent: q, B, ext and err are free. No example at the
release's values. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.Tw.K2C.TiedForm
import Johnson.Top.H0.K2Ties.Dec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.K2 (ownPiece)

variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {C : CK}
  {F : Frame}

/-- **The code switch's tie "dec" at the composed meaning.** -/
theorem k02_dec (D : MgData Xi P Tok rows cols nR X)
    (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (hd : DecBlind D.decT)
    (q : Piece C F (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT)) (B : Block First.S Cl)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT) (err : Err (uLT C q.ds)) :
    ∀ z a τ b, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      (mgAll D Mg₀).decodes (z, a.1) (strsOf F a.2) →
      (mgAll D Mg₀).decodes (z, b.1) (strsOf F b.2) := by
  intro z a τ b hb h
  rw [mgAll_decodes] at h ⊢
  exact dec_of_blind D.decT hd (ownPiece q B (ext z) err) z a b τ hb h

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.k02_dec
