-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/TwinFeels.lean: IF PUBLIC FILES ARE READ AND HAVE A FRAME WITH SALTS OF 40 BYTES,
THE COMMIT FIELD's VALUE FEELS THE WEIGHTS AT THE FULL SIZE: ANY TWO DIFFERENT WEIGHTS, AT EVERY
SEED OR COINS, ARE PARTED BY SOME HASH FUNCTION; and the running committer is not blind there. The
tie and the negative tests, met in one sentence. Four theorems, each by a few calls. THEY ARE CHECKS
ON THE COMMIT FIELD: corollaries of bindsAt_salt or of tieAt (Johnson/Bind/Cpp/TheTie.lean), and the
count, not a further property of the committer.
"Binds": the opening form, BindsWith, as defined in the head of Johnson/Bind/Cpp/Controls.lean.

Why. Johnson/Bind/Cpp/Controls.lean shows that a committer whose value is one at two different
weights, at every hash function, does not bind (one_le_of_blindValue), and that a committer that
does not read the table's plain entries (BlindAt) cannot meet the tie together with the count
(blindAt_fails), at public files that are read. Johnson/Bind/Cpp/TheTie.lean shows that the running
committer of Johnson/Bind/Twin.lean meets the tie and binds where the frame's salts have 40 bytes
(tieAt, bindsAt_salt), and Johnson/Bind/Cpp/AtTwin.lean proves its count (count_theTwin). At the
full size's shape the running committer cannot be run, so no evaluation can show there that its
value feels the weights.

Main names (namespace Bind.Cpp).
  **`commit_parts_weights`**: at such files, at any two different weights and every randomness (a
    seed or coins), the commit field of theCpp (theTwin g) has not one value at every hash function:
    nothing of the weights goes unfelt.
  `commit_feels_weights`: so it has not one value at all weights, all randomness and every hash
    function. A committer that read one digit alone would meet this weaker form too.
  `twin_not_blindAt`: at the full size's shape and these files the running committer is not blind.
  `twin_not_blind`: so it is not blind at every shape and all files.
Limits. Under two premises at public files Z: they are read, and the frame's salts have 40 bytes
(SaltAt Z). THAT SaltAt Z HOLDS AT ANY Z IS NO THEOREM OF THE MAIN LIBRARY: there the premise is not
paid, and no member is shown by a theorem. By evaluation the number is 40 at storedPublicFiles and at zGap
(Johnson/Bind/Cpp/SaltAtNamed.lean), and both are read (VerifierAndGoals.filesRead). "Parted by some hash
function" names no hash function and counts none: it comes by contradiction, at valid weights and
the same randomness at both; how likely it is that a random one parts them is what
noTwoOpenings_salt (TheTie.lean) bounds. "Weights" are the library's integer weights: that two of
them have different tables of digits follows; how the programs lay weights into the table is
compared nowhere. That one bent entry turns the ID at a toy shape is evaluated in
Johnson/Bind/Cpp/Known.lean: by that evaluation, which is no theorem, `twin_not_blind`'s conclusion
is had without a premise. This is not the proposition Feels (Johnson/Bind/Cpp/Guards.lean: the ID
feels each kind of coin), which is proved nowhere. Nothing on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.TheTie
import Johnson.Bind.Cpp.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)
open Bind.Control

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

/-- **THE COMMIT FIELD's VALUE FEELS THE WEIGHTS AT THE FULL SIZE**: at public files that are read
and whose frame has salts of 40 bytes, any two different weights, at every seed or coins, are parted
by some hash function: were the value one at both at every hash function, the committer would not
bind, and it binds there. -/
theorem commit_parts_weights (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z)
    (w w' : ModelWeights (settingsOfRead pp)) (hne : w ≠ w') (ρ : Rand) :
    ¬ ∀ hash : Hash, (cppCommit (theTwin g) Z (settingsOfRead pp) w ρ).evaluate hash =
      (cppCommit (theTwin g) Z (settingsOfRead pp) w' ρ).evaluate hash := by
  intro hv
  obtain ⟨prove⟩ := exists_prove Z pp hr
  exact not_one_le_bitsBinding (one_le_of_blindValue (bindsAt_salt prove g Z pp hr hs).2 hne ρ hv
    (commit_count (theTwin g) Z (count_theTwin g Z) (settingsOfRead pp) w ρ))

/-- So the commit field's value at the full size is not one and the same at all weights: there are
two different weights. -/
theorem commit_feels_weights (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) :
    ¬ ∀ (w w' : ModelWeights (settingsOfRead pp)) (ρ : Rand) (hash : Hash),
      (cppCommit (theTwin g) Z (settingsOfRead pp) w ρ).evaluate hash =
        (cppCommit (theTwin g) Z (settingsOfRead pp) w' ρ).evaluate hash := by
  intro hv
  obtain ⟨w, w', hne⟩ := two_weights (valid_of_read hr)
  exact commit_parts_weights g Z pp hr hs w w' hne (Sum.inl 0 : Rand) (hv w w' (Sum.inl 0 : Rand))

/-- **At the full size's shape and these files the running committer reads the table's plain
entries**: else it would fail the tie, which it meets there. -/
theorem twin_not_blindAt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) :
    ¬ BlindAt (theTwin g) shapeFull Z.pol Z.lay Z.KL :=
  fun hB => blindAt_fails hB pp hr (count_theTwin g Z) (tieAt Z hs g)

/-- So it is not blind at every shape and all files. -/
theorem twin_not_blind (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) : ¬ Blind (theTwin g) :=
  fun hB => twin_not_blindAt g Z pp hr hs (hB shapeFull Z.pol Z.lay Z.KL)

end Bind.Cpp

end

#print axioms Bind.Cpp.commit_parts_weights
#print axioms Bind.Cpp.commit_feels_weights
#print axioms Bind.Cpp.twin_not_blindAt
#print axioms Bind.Cpp.twin_not_blind
