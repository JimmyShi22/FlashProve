-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/BothFrontS.lean: BothFront.lean's end in SampleReach.lean's letters:
`KeepsBoth (c.blocksInOrder.take k)` at every cut k in front of the last code switch, at the first chain of
the proof file's IOP as written in Lean (`ProofFile.onlineDescription`). A law file; no running text imports it.

  `keepsBoth_front`   LotsK1.lean's both_front_good, the code switch's own share paid by
                      SampleChainS.lean's keepsS_k2. NO NAMED PREMISE IS LEFT: `onlineDescription` returns F,
                      and F.planOk = true.
Limits. Those of BothFront.lean. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.LotsK1
import Johnson.Top.H0.K2Hands.SampleReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Keeps1
open Meaning.K2 (frontOf)

/-- **The keepers' table as one term.** -/
theorem keepsBoth_front {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hpl : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧ (frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 ∧
      ∀ k, k ≤ (frontOf c).length → KeepsBoth (c.blocksInOrder.take k) := by
  obtain ⟨Z, c, A, B', hZ, hE, h0, hlen, hall⟩ := both_front_good h hpl fun p => keepsS_k2 p
  exact ⟨Z, c, A, B', hZ, hE, h0, hlen, fun k hk => ⟨(hall k hk).1, (hall k hk).2⟩⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keepsBoth_front
