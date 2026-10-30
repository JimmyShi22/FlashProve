-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimBlock.lean: the closing of a segment (K10): the rounds and the oracle messages of
the block as the first chain seats it. Two lemmas.

  `seated_lists`    at `IM.seatedAs ProofFile.sameReply (K9.closing Q).retype name a`, at every name and address: its rounds
                   are the first members of `closeRounds Q` (Honest/K10/Sim.lean), its oracle messages the second:
                   each list by itself
  `seated_rounds`   the two zipped are `closeRounds Q`: by `closeRounds_is` (Sim.lean)

Limits. That a chain's block is of that form: Johnson/Desc/K10/Honest/KeepsSeat.lean (`K10Seated`); the two are joined
in Honest/K10/SimLot.lean. No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Sim
import Johnson.Desc.K10.Honest.KeepsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par entries)

/-- **The block as the first chain seats it: its rounds; its oracle messages**: each list by itself: the first and the
second members of `closeRounds Q`. -/
theorem seated_lists (Q : Par) (name : String) (a : Place) :
    (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).rounds =
        (closeRounds Q).map (·.1) ∧
      (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).oracles =
        (closeRounds Q).map (·.2) := by
  refine ⟨?_, ?_⟩
  · show (entries Q).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) = _
    unfold closeRounds
    rw [List.map_map]
    rfl
  · show (entries Q).map (fun _ => ([] : List Oracle)) = _
    unfold closeRounds
    rw [List.map_map]
    rfl

/-- So the two zipped. -/
theorem seated_rounds (Q : Par) (name : String) (a : Place) :
    (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).rounds.zip
        (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).oracles =
      closeRounds Q :=
  closeRounds_is (Cl' := Unit) Q

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seated_lists
#print axioms ProofFile.Honest.K10.seated_rounds
