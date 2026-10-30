-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/AtBase.lean: kind K13, the members' batching: the kind's rows, as
one term made from public data, are the prover's sides at the places of the kind where `onlineProverFromPublicFiles`
(Johnson/Desc/ProofFile/Honest/AtPure.lean) returns at the filling `onlineProverPartsInUse`
(Johnson/Desc/ProofFile/Honest/K1/Law/WSideAtFill.lean). One definition; statements with their
proofs.

  `k13BaseRows`   the kind's rows at a reader of the index that may hang on the public part, and a
     filler of the pile: a function of the public part and the ground. Its other two arguments are
     these two functions
  `k13BaseRows_public`   of such a row the place, the simulators, `On` and `bud` hang on the public
     part alone: neither function is read for them
  `k13_at_base`   where `onlineProverFromPublicFiles` returns at that filling: among the returned prover's sides of the
     first chain, in their order, those at a place of the kind K13 are just the sides of these rows
  `k13_none_elsewhere`   under the library's head h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), where
     `onlineProverFromPublicFiles` returns at the head's files, at any filling: the returned prover has no side at a
     place of the kind in the shared chain or in the second chain

Limits.
  * That `onlineProverFromPublicFiles` returns is a hypothesis.
  * The parts of a row read the index through the first function and the instance through the
    second; only the rest of the row is public by `k13BaseRows_public`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.AtFill
import Johnson.Desc.ProofFile.Honest.K13.KindPlaces
import Johnson.Desc.ProofFile.Honest.K7.AtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.K13 (whereOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **The kind's rows at a reader of the index and a filler of the pile**, as a function of the
public part and the ground. -/
def k13BaseRows {W₁ Rc Tr X : Type} (weights : Pub → W₁ → Weights)
    (pile : Pub → Ground → PileOf Inst) (Z : Pub) (G : Ground) :
    List (Unlettered (Local W₁ Rc Inst Tr) (Local W₁ Rc Inst Tr) X Inst) :=
  (k13SLot (weights Z) pile).rows Z G

/-- **Of such a row the place, the simulators, `On` and `bud` hang on the public part alone.** -/
theorem k13BaseRows_public {W₁ Rc Tr X : Type} (weights : Pub → W₁ → Weights)
    (pile : Pub → Ground → PileOf Inst) (Z : Pub) (G : Ground) :
    ∀ r ∈ k13BaseRows (Rc := Rc) (Tr := Tr) (X := X) weights pile Z G,
      r.place = k13Place (whereOf Z) ∧ r.row.map (·.2) = k13Sims (whereOf Z) ∧ r.On = k13On ∧
        r.bud = k13Bud := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Where `onlineProverFromPublicFiles` returns at the filling: among the returned prover's sides of the first chain,
in their order, those at a place of the kind K13 are just the sides of the kind's rows**: none twice
and none beside. -/
theorem k13_at_base {W₁ : Type} {I : WiderIn W₁} {o o' : SecondHashFunctionArgument}
    {Sz : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₁ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A) :
    A.H.first.filter atK13 = (k13BaseRows I.weights O.pile A.Z A.G).map (·.half) := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok hA
  rw [hf, k13_filter_wider]
  exact (k13SLot_halves _ _ A.Z A.G).symm

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- **The returned prover has no side at a place of the kind in the shared or in the second chain**:
under h, where `onlineProverFromPublicFiles` returns at the head's files, at any filling. `onlineProverFromPublicFiles` refuses a side that is
at no sub-protocol's place, and these two chains have no sub-protocol of the kind. -/
theorem k13_none_elsewhere {W₁ Rc Tr X₀ X : Type} {P : OnlineProverParts W₁ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₁ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.H.shared.filter atK13 = [] ∧ A.H.second.filter atK13 = [] := by
  obtain ⟨-, s2, s3⟩ := atPure_strays hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  have key : ∀ F : FileDescription ProofFile.Inst, F = P5J.F0T OnBytes.secondHashFunction Zp Np cF →
      (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K13) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K13 := by
    intro F e
    subst e
    exact (k13_places_of_kind h).2
  obtain ⟨p2, p3⟩ := key A.F eF
  refine ⟨filter_atK13_nil fun x hx e => ?_, filter_atK13_nil fun x hx e => ?_⟩
  · obtain ⟨b, hb, hpl⟩ := side_on_chain s2 hx
    exact p2 b hb (by rw [hpl]; exact e)
  · obtain ⟨b, hb, hpl⟩ := side_on_chain s3 hx
    exact p3 b hb (by rw [hpl]; exact e)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13BaseRows
#print axioms ProofFile.Honest.K13.k13BaseRows_public
#print axioms ProofFile.Honest.K13.k13_at_base
#print axioms ProofFile.Honest.K13.k13_none_elsewhere
