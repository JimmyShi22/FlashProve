-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HpubMw1.lean: K01_law: TWO SMALL TOOLS FOR LAYING hpub_point (Johnson/Desc/K1/Law/HpubPointwise.lean) INTO THE TOP AT mw1:
  yesOf_of_piece    (it stands in Johnson/Desc/K1/Law/YesOfPiece.lean, which this file imports) the piece's accept is an accept of the place's bare sub-protocol in the top's own form YesOf (after yes_of_piece)
  tiedL_true_none   at the closed wider door nothing comes at a digits' place (made_mw [kernel])
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaidMw1
import Johnson.Desc.K1.Law.YesOfPiece
import Johnson.Desc.K1.Law.HpubPointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat KObj
open Cb Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open ProofFile (Cl)
open IM (k1Ix)

theorem tiedL_true_none {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT)) (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (q : Pub) :
    q ∉ tiedL (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more l true := by
  intro hq
  rw [plus13_more_closed Dm dk Mg₀ hM] at hq
  have hmade := List.all_eq_true.1 made_mw l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hmade
  have hq' : q ∈ [] ++ madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) := hq
  rw [hmade.1] at hq'
  simp at hq'

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tiedL_true_none
