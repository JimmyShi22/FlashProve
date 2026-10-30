-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/LengthsOfPub.lean: WHEREVER A PUBLIC PART IS MADE, ITS
CODE TABLE's LENGTHS ARE IN ORDER: the maker refuses otherwise.
  lengthsOk_of_pubT   lengthsOk_of_pub (Johnson/Goal/Numbers/LengthsOkWritten.lean),
  STATEMENT AND PROOF WORD FOR WORD, under a name with a letter behind it: that file also holds the
  written codes' facts and so imports Johnson/Goal/Numbers/KeyInScope.lean, which does not stand in
  the set of files over which the first chain's kinds' files are written. Johnson/Desc/AtSeats/K13PlanM3At.lean:177 calls the original, lengthsOk_of_pub; Johnson/Desc/AtSeats/Fit/TidyPaid.lean:63 calls lengthsOk_of_pubT.
What is not claimed. Nothing on soundness.

-/
import Johnson.G.DataEntries
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Johnson.G Johnson.G.OfPlan

theorem lengthsOk_of_pubT
    {made : ByteArray → ByteArray → ByteArray → Except String Made} {st : _root_.ProofFile.Starts}
    {pol lay KL : ByteArray} {Z : _root_.ProofFile.Pub}
    (h : _root_.ProofFile.pubBy made st pol lay KL = .ok Z) : Z.first.codes.lengthsOk = true := by
  unfold _root_.ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, h', _⟩ := bind_ok h
    exact absurd h' (throw_ne _ _)
  · rename_i hc
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨D, _, h⟩ := bind_ok h
    obtain ⟨told, _, h⟩ := bind_ok h
    obtain ⟨depth, _, h⟩ := bind_ok h
    obtain ⟨cuts, _, h⟩ := bind_ok h
    obtain ⟨s₀, _, h⟩ := bind_ok h
    obtain rfl := Except.ok.inj h
    show m.p.chains.proof.first.codes.lengthsOk = true
    simpa using hc

end VerifiableInference.Desc.K13.Law
