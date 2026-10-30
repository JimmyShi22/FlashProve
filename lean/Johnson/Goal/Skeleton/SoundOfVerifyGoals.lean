-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean: two statements that this library already defines,
proved with no further hypothesis: `ProofSound`, and the goal `G7bits` of `theDescription`. No
definition is made here, and no goal is stated; one small theorem, `read_of_scope`, is proved here.
Over the verifier with fourteen entry tests alone.

  `read_of_scope`: a set of public files in scope is read: `InScope` (Ladder.lean) says no where
    `readFiles` gives an error. By cases on the reading.
  **`proofSound_of_verify`**: `ProofSound` (Johnson/Goal/Conditions/RowsAtTheRecord.lean), the row
    in scope, where `protocolDataWellFormed` says yes: `proofSoundAt_of_verify` (SoundOfVerifyMore.lean) has it at
    the Z whose files are read: by `read_of_scope`, all. It is stated of the term that that file
    writes (`dataAtFiles flashProveData Z` at two fixed values), not of the name `theDescription`, which no
    declaration of that file names. It lies beneath the soundness theorems, not above them.
  **`g7bits_of_verify`**: the goal `G7bits theDescription` (Ladder/Bits.lean): soundness at exact
    match at the error `soundnessErrorInQueries`, for every proof parser within n queries, with the verifier's own
    queries within the allowance: by `g7bits_of_g8bits` (Ladder/BitsTies.lean) at `g8bits_of_verify`
    (SoundOfVerifyPolicy.lean). It does not call `sound_of_verify_at`.

Limits. But for `read_of_scope`, CALLS ALONE. What they are worth is what the called theorems and
the definitions in the statements are worth.
The limits of
SoundOfVerifyPolicy.lean, of SoundOfVerifyAt.lean and of Ladder/Bits.lean travel whole, to BOTH
theorems. Among them: where `protocolDataWellFormed` says no, `verify` rejects everything: there `ProofSound` asks
nothing (it asks its body only where `protocolDataWellFormed` says yes), and the bound in `G7bits` holds for that
reason; what else `G7bits` asks (`VerifierWithin`; the description's own parser within
`honestBudget`) only counts queries. By the head of Ladder.lean (point 2) all goals on soundness and
binding together, those of Ladder/Bits.lean too, are met by a verifier that always refuses with a
commitment that binds. THAT `protocolDataWellFormed` SAYS YES AT THE RELEASE'S FILES AS BYTES, AND THAT THE HONEST
PROOF IS ACCEPTED THERE, IS EVALUATED, NOT PROVED; at the library's written copies of the public
files the first is proved (`theLive_zFull`, `theLive_zGap`, `theLive_zAt`, AtFullSide/Top/, a side
library). The level is 124 BITS FOR EACH QUERY, NOT 128: `soundnessErrorInQueries t n` is 16 (t + n + 2^23) / 2^128 +
(t + n + 2^23 + 2)^2 / 2^256, and it grows with n. By the head of Ladder/Bits.lean a protocol that
checks nothing but a proof of work of 124 bits meets all four goals of that file. By reading (not
checked here) `verify` does not itself test for exact match: that is a premise on the files. Nothing
on correctness of extraction, on binding of the commitment, on no two openings, on completeness or
on hiding.

-/
import Johnson.Goal.Skeleton.SoundOfVerifyPolicy
import Ladder.BitsTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- **A set of public files in scope is read.** -/
theorem read_of_scope (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true) :
    ∃ pp : Inst.Model.ScalesAndPolicy, readFiles Z = .ok pp := by
  cases hr : readFiles Z with
  | ok pp => exact ⟨pp, rfl⟩
  | error e =>
    exfalso
    unfold InScope at scope
    rw [hr] at scope
    simp at scope

/-- **`ProofSound` is a theorem: the proof file's row, in scope, wherever `protocolDataWellFormed` says yes.** -/
theorem proofSound_of_verify : ProofSound :=
  proofSound_iff_at.2 fun Z scope =>
    (read_of_scope Z scope).elim fun pp read => proofSoundAt_of_verify Z pp scope read

/-- **The goal `G7bits` of `theDescription`**: at 124 bits for each query; met also where the
verifier rejects everything (the head's limits). -/
theorem g7bits_of_verify : G7bits theDescription :=
  g7bits_of_g8bits _ g8bits_of_verify

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.read_of_scope
#print axioms VerifierAndGoals.AtTheName.proofSound_of_verify
#print axioms VerifierAndGoals.AtTheName.g7bits_of_verify
