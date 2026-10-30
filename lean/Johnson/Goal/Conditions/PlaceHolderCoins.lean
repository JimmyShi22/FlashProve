-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/PlaceHolderCoins.lean: **A PLACE-HOLDER.** One value of `TheCoins`
(Johnson/Goal/Conditions/BindsAtThe.lean): THE HONEST SIDE THAT DRAWS NOTHING: so that a closed term
can stand behind a name. A definition. IT IS NOT THE HONEST SIDE OF ANY PROGRAM AND IS MEANT
TO BE REPLACED.

Main name (namespace `FlashProve`).
  `placeHolderCoins : TheCoins`: both enumerations of coins have ONE member (pads and random tails
    are zero; every salt is zeros, of the length compilerParameters.sMT that the verifier asks of a salt); no
    randomness (`Unit`); the stored table's shape is no bytes; the
    generator returns 0; both provers hand over empty things.

WHAT IS TRUE AT IT. The theorems on binding of Johnson/Goal/Conditions/BindsAtThe.lean and
Johnson/Goal/Conditions/RowAtThe.lean: they hold AT EVERY VALUE of `TheCoins`, so here too.
WHAT IS FALSE OR EMPTY AT IT.
- NOTHING IS HIDDEN: the commitment is a function of the weights and the public files alone: whoever
  can guess the weights can test the guess. A statement on hiding or zero knowledge of a description
  with this value is FALSE, not merely unproved, wherever it asks more than that.
- NOTHING ON COMPLETENESS: the provers prove nothing.


- AT `theBound K` THE SAME HOLDS OF EVERY VALUE K, NOT OF THIS ONE ALONE: there the number of coins
  is 0 (`bound_the`, Johnson/Goal/Conditions/WideAtThe.lean), so the commitment is a function of the
  weights and the files at every K. A value that draws wants `theWide K W`.
- The coins' algorithm still asks its two strings, at a shape of no bytes: these are not the
  strings of any stored table.
WHOSE THE CHOICE OF THE TRUE VALUE IS: not this file's: it is part of what the description is.

It stands over `theCoding` := `codingCells` (Johnson/Goal/Description/Coding.lean turned so): at
another
coding of an index the two zeros below do not have the types.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **A PLACE-HOLDER: the honest side that draws nothing.** -/
def placeHolderCoins : TheCoins where
  ri := fun _ => ⟨0, fun _ => (fun _ _ => 0, fun _ _ => 0)⟩
  sl := fun Z => ⟨0, fun _ _ => List.replicate (flashProveDescription.input Z allZeroDigest []).compilerParameters.sMT false⟩
  b₀ := fun _ => []
  proveT := fun Z _ b => .pure ⟨b.map fun _ =>
    ⟨0, none, (fun _ => false, (dataAtFiles flashProveData Z).G.rec₀, none), none⟩, List.length_map ..⟩
  Rand := Unit
  sample := .done ()
  shape := fun _ => ByteArray.empty
  gen := fun _ _ _ => 0
  prove := fun _ _ _ _ _ _ => .done
    ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

end FlashProve
