-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PureIs.lean:
WHAT THE PROOF FILE's DESCRIPTION IS, WHERE IT IS MADE:
where `ProofFile.onlineDescription o pol lay KL` returns F, F is `ProofFile.fileDescBy` at o, the road's maker of links,
some public part Z, two later seats A, B, the identity as the reading of the carried record, `startS
Z` and some first chain c.
  `descPure_is`: the statement. ITS PROOF IS ONE
    CALL: `ProofFile.Law.descPure_parts` (Johnson/Desc/ProofFile/Law/PureMade.lean), WHICH SAYS MORE
    (which public part; that the two seats are the ones that the seat lays; how c is made):
    NEW CODE CALLS THAT ONE.
Limits. Nothing on whether the description is made at any files. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (FileDescription Chain)
open VerifiableInference.Desc.First (S)

/-- **Where the proof file's description is made, it is `fileDescBy` at the carried record.** -/
theorem descPure_is {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : SharedSeat) (B : SecondSeat) (c : Chain S Cl),
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c := by
  obtain ⟨Z, -, -, c, A, B, -, -, -, -, -, -, -, -, rfl⟩ := Law.descPure_parts h
  exact ⟨Z, A, B, c, rfl⟩

end ProofFile

#print axioms ProofFile.descPure_is
