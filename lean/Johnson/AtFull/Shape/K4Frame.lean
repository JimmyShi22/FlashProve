-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K4Frame.lean: THE LAYERS' OWN ROUNDS (K4) IN THE FRAME's OWN FORM: the two
premises that the rule for acceptance asks at a member, Carries and Returns
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at K4's twelve members of the proof file's own
first chain. Under the head P5J.AtMgA; nothing is evaluated.

  k4A p           THE STEP ON THE WHOLE SHAPE (ShA, Johnson/AtFull/Shape/FrameForm.lean: the chain's
                  shape with the rows' makes): liftO (Johnson/AtFull/Shape/FrameOpt.lean: a step on
                  the chain's shape alone that may refuse; the makes stand) of the step at the seat
                  (k4StepS, Johnson/AtFull/Shape/K4AtHead.lean).
  **k4_frame**    for g < 12: with Bs what the maker's own ProofFile.baseOf returns at the public part,
                  and a record y of K4's own list of places, of which the three fields that the step
                  and the tests read are tied (k4StepS_reads, k4ValsB_reads): for every ft, G and
                  vals with G (28 g + 4) = k4A ... and vals (28 g + 4) = k4ValsB ...:
                  Carries cF.blocksInOrder ft (firstZA G vals) (28 g + 4) and Returns likewise.

Limits. TWO PREMISES OF THE RULE AT TWELVE MEMBERS: the rule asks them at every member, and more
(that the run on shapes returns; the values; the fits). G and vals are letters: no table of steps is
laid. k4_frame does not say that a member stands at 28 g + 4 (K4AtHead.lean's k4_at has it): where
none stood, Carries and Returns would say nothing: both begin "for every member at that number". NO
STATE IS SHOWN AT WHICH THE STEP RETURNS. The test that the stretch fits K4's table stands among the
tests on values and rounds: it is not drawn from the fit of the member's declared rounds, which the
two laws are handed and do not spend (K4Fit.lean spends it). The head is taken at OnBytes.secondHashFunction,
its first letter, alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K4AtHead
import Johnson.AtFull.Shape.FrameOpt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open OnBytes.Desc.First.K4 (Par)
open ProofFile.Honest (Carries Returns)

/-- **The step on the whole shape**: the rows' makes stand. -/
def k4A (p : Par) : ShA → Except String ShA := liftO (k4StepS p)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k4_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (y : Bool × Par),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      y ∈ ProofFile.k4From Zp Bs.G₀ Bs.G₀.built.toList 0 none ∧
      y.2.P = Bs.G₀.W.layers ∧ y.2.g = g ∧ Bs.G₀.W.G[g]? = some y.2.hp ∧
      ∀ (ft : Nat) G vals,
        G (28 * g + 4) = k4A { y.2 with k3Runs := true } →
        (∀ s rs gs, vals (28 * g + 4) s rs gs = k4ValsB { y.2 with k3Runs := true } s rs) →
        Carries cF.blocksInOrder ft (firstZA G vals) (28 * g + 4) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (28 * g + 4) := by
  obtain ⟨Bs, y, b, e1, e2, e3, e4, e5, q, hc, hr⟩ := k4_at h g hg
  refine ⟨Bs, y, e1, e2, e3, e4, e5, fun ft G vals hG hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨w, hw, rfl⟩ := liftO_ok.1 hu
    obtain ⟨k1, k2⟩ := hc s _ gs t w hd hw
    subst k1
    show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
    rw [k2]
  · refine returns_of_seat q fun s rs gs u _ hu hvv => ?_
    rw [hG] at hu
    rw [hv] at hvv
    obtain ⟨w, hw, -⟩ := liftO_ok.1 hu
    exact hr s _ gs w hw hvv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k4_frame
#print axioms Johnson.AtFull.Shape.k4A
