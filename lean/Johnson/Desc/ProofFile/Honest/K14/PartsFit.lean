-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PartsFit.lean: pieces for Honest/K14/PartsPlay.lean: the two
messages that the parts of Honest/K14/Parts.lean send pass the frame's test Sending.fits at a
declared round of the right form; and what the part at "SPLIT" sends, under a name.

  quiet_fits      the empty message fits a declared round that cuts no item and has no oracle
                  message
  split_fits      one element fits a declared round that cuts one element and has no oracle
                  message
  scalarAt        the element that the part at "SPLIT" sends: of its public data, the coins that it
                  is handed, and where the run stands
  says_split      the part's one move returns that element, at all that it is handed: it never fails

That the kind's sub-protocols declare rounds of these forms: declares3, declares_split
(Honest/K14/Debts.lean).

What is not claimed. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The empty message fits a declared round that cuts no item and has no oracle message. -/
theorem quiet_fits (d : Fmt.DeclaredRound) (h : d.items = []) :
    (⟨[], []⟩ : Sending).fits d [] = true := by
  simp [Sending.fits, h]

/-- One element fits a declared round that cuts one element and has no oracle message. -/
theorem split_fits (d : Fmt.DeclaredRound) (h : d.items = [.e]) (y : Cb.Gl.E) :
    (⟨[.e y], []⟩ : Sending).fits d [] = true := by
  simp [Sending.fits, h, Said.got, VerifiableInference.Desc.itemOf]

/-- **The element that the part at "SPLIT" sends.** -/
def scalarAt (A : Data) (c : (splitPart A).Coins) (t : State Ask Unit) : Cb.Gl.E :=
  OnBytes.Slice.toE (Desc.K14.Honest.muAtE A.S (elems (heardFrom t A.atPoint 1))
    (elems (heardFrom t A.atZeta 1)) t.input.rows
    ((coinsE c.2.1.1).headD OnBytes.zeroE)).triple

/-- The one move of the part at "SPLIT" returns that element, at all that it is handed. -/
theorem says_split (A : Data) (c : (splitPart A).Coins) (s : Seen) (t : State Ask Unit) :
    (splitPart A).moves.map (fun mv => mv.say c s t) = [.ok ⟨[.e (scalarAt A c t)], []⟩] := rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.quiet_fits
#print axioms ProofFile.Honest.K14.split_fits
#print axioms ProofFile.Honest.K14.says_split
