-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaTail.lean: kind K14: TailLike AND TailAt
(Honest/K14/OmegaTwelve.lean) AT THE FLAT LIST OF THE SHARED CHAIN CARRIED TO ANOTHER TYPE OF
CLAIMS: the form in which a proof file's IOP as written in Lean holds that chain
(Johnson/Desc/K14/Law/SharedFlat.lean: flat_retype_all), with the library's two proximity tests and
its closing sub-protocol laid (Johnson/Desc/K12/Seat/Fill.lean). In the manner of flatOf_carried
(Johnson/Desc/K14/Honest/FlatForm.lean), which speaks of the first nine members. Two statements with
their proofs.

  tailLike_carried **TailLike at that list**, at p₉ and p₁₀ the library's own numbers of the two
                  tests (H2U.proximityTestParametersAt at ⟨2, none, 9, .K12⟩ and ⟨2, none, 10, .K12⟩) and front the
                  eight sub-protocols of the linear claim's shared rounds with the two tests behind
                  them. Asked: the library's maker of the eight returns them (hb); the plan has a
                  second test (N.O = some nO). The three members are like the library's three by
                  unfolding: carrying to another type of claims keeps rounds, oracles, place and
                  decide function, and the wrap of Chain.blocksInOrder turns the test on the plan alone. That
                  Seat.tests N is the two tests under N.O = some nO is unfolded inside the proof, in
                  three lines: the library's Sh.tests_two
                  (Johnson/Desc/K14/Law/SharedConstChain.lean) says it, and ToldDesc.tests_two
                  (Johnson/ToldDescR/OmegaAtLaid.lean) its length; neither is imported, for their
                  wide cones
  tailAt_carried  TailAt there, where beside the two tests' own tests on the plan accept (h9, h10:
                  handed through)

What is not claimed. That the list of any Thread (Honest/Thread/Thr.lean) is this list
(Honest/K14/OmegaAtShared.lean has it at the Thread that is laid for the shared chain). The two
tests on the plan (Honest/K14/OmegaAtPlan.lean: plans_at_shared). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaTwelve
import Johnson.Desc.K14.Law.SharedFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St blocks chainOf)
open Desc.K14.Law (flat_retype_all)

/-- **TailLike at the carried chain's flat list.** The equation on Seat.tests N inside the proof is
the library's Sh.tests_two, unfolded again. -/
theorem tailLike_carried {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (N : H2U.Places4) (nO : H2U.PlaceNums)
    (hO : N.O = some nO) (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    TailLike ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
        VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++ VerifiableInference.Desc.K12.Seat.tests N) := by
  have e : VerifiableInference.Desc.K12.Seat.tests N =
      [VerifiableInference.Desc.K12.Seat.onGu
          (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block T12 Unit),
        VerifiableInference.Desc.K12.Seat.onGomega
          (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit)] := by
    unfold VerifiableInference.Desc.K12.Seat.tests
    rw [hO]
    rfl
  rw [flat_retype_all c P b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb, e]
  exact ⟨⟨_, rfl, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- TailAt at the carried chain's flat list, where the two tests' own tests on the plan accept. -/
theorem tailAt_carried {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (N : H2U.Places4) (nO : H2U.PlaceNums)
    (hO : N.O = some nO) (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (h9 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block T12 Unit).planOk = true)
    (h10 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).planOk = true) :
    TailAt ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
        VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++ VerifiableInference.Desc.K12.Seat.tests N) :=
  ⟨tailLike_carried c P b1 b2 b3 b4 b5 b6 b7 b8 N nO hO hb, h9, h10⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.tailLike_carried
#print axioms ProofFile.Honest.K14.tailAt_carried
