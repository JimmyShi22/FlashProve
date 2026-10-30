-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/ReturnBody.lean: WHERE THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS, AT ANY FILLING AND ANY PUBLIC FILES, UNDER NO OTHER PREMISE: the places and the first chain are made, and the return's
description is `F0T` at them. A join of three: what the return gives (`atPure_ok`), that any return of `onlineDescription` opens (`descPure_open`), and that the first chain reads no second hash (`chain_free`).

  `returnIsTheDescription_body`   **the statement**

Limits. It says where the maker returns: that it returns is another proposition. No property of the protocol is claimed.
-/
import Johnson.P5J.LaidOpens
import Johnson.P5J.ChainFree
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **The body of `ReturnIsTheDescription`, written out, at any filling.** -/
theorem returnIsTheDescription_body {W₀ Rc Tr X₀ X : Type} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL P = .ok A) :
    ∃ places firstChain, H2U.placesOfMade A.Z.made = .ok places ∧
      ProofFile.onlineFirstChainAt A.Z = .ok firstChain ∧ A.F = P5J.F0T OnBytes.secondHashFunction A.Z places firstChain := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  obtain ⟨Z, Bs, base, c, N, hN, O⟩ := Desc.K14.Law.descPure_open OnBytes.secondHashFunction _ _ _ _ hF
  have eZ : A.Z = Z := Except.ok.inj (hZ.symm.trans O.pub)
  refine ⟨N, c, ?_, ?_, ?_⟩
  · rw [eZ]
    exact hN
  · rw [eZ]
    exact P5J.chain_free O
  · rw [eZ]
    exact O.desc

end ProofFile.Honest

#print axioms ProofFile.Honest.returnIsTheDescription_body
