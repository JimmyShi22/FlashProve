-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstAt.lean: THE SHARED TABLE's CONSTANT AT A PROOF FILE's SEAT: the
parameters (ShPlan, Johnson/Desc/K14/Law/SharedConst.lean) as TERMS off the verifier's public value
Z and the places N that it makes, and how the named tests (Sh.tests,
Johnson/Desc/K14/Law/SharedConstTests.lean) are paid there by theorems that lie.

  Sh.planAt Z N G      Q := p14Of Z.p.chains (beforePointOf N) · the two functions of radii :=
                       rad2At 2 Q, rad5At 2 Q · the written list of rounds := dryProofFull.2.1 ·
                       the file := 2 · the last chain's parameters p := p₁₄Z at Z's own sized
                       values, as the seated last chain reads them
                       (Johnson/Desc/ProofFile/Lot/LastChain.lean). STILL A LETTER: G (the IOP as
                       written in Lean).
  Sh.tests_of          all 23 tests, at every ShPlan, from four structures of facts that lie
                       (SeatBinders, Ten, PlanY3, ShPlain3) and two plain premises: hpS (one shape
                       for o_omega on both chains) and hp (each of the kind's eight sub-protocols
                       passes its own test on its parameters)
  Sh.chainOkAt Z N     ONE Bool on Z and N: every sub-protocol of the seated shared chain passes its
                       own test on its parameters. The verifier's own test on the IOP as written in
                       Lean asks it (ToldDesc.shared_ok_of_planOk).
  Sh.tests_at          **Written Z x → chainOkAt Z N = true → Tests (planAt Z N G)**
The proof term of tests_of is written by program off the table of tests and a table test → payer.
WHAT IS NOT HERE. No law. Written Z x (its payers: Johnson/HB/LLHARD/WrittenOfPins.lean). That
chainOkAt says yes where the verifier accepts. The tests that read open letters, and K12's.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K14.Law.SharedConstPlain
import Johnson.Goal.Numbers.K14RadiiTerms
import Johnson.Goal.Numbers.K14PlanY
import Johnson.ToldDescR.PlacesAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.G (dryProofFull codesFull2)
open VerifiableInference.Desc.K1 (realSized)

namespace Sh

variable {Xi : Type} (A : ShPlan Xi)

/-- **The tests from the facts that lie**, at every ShPlan. -/
theorem tests_of {work : ℕ} (B : SeatBinders A.fl work A.Q A.Wr (sentU A) A.rad2 A.rad5)
    (T : ∃ s lU lO, Ten A.Q.codes A.Q.S s lU lO) (Y : PlanY3 A.Q.codes A.Q.S)
    (Pl : ShPlain3 A.Q.codes A.Q.S) (hpS : A.p.S.omega = A.Q.S.omega)
    (hp : (blocksOr A.Q).all (·.planOk) = true) : Tests A := by
  obtain ⟨s, lU, lO, T⟩ := T
  have e : sentU A = s := Option.some.inj (B.hUw.symm.trans T.hU)
  exact (Tests_iff A).2 ⟨(by rw [B.hUw]; rfl),
    B.hS,
    B.hm,
    B.hok,
    (by rw [e, T.hlU]; rfl),
    (by rw [T.hlO]; rfl),
    B.hl,
    Pl.hlinOk,
    hp,
    B.hC2,
    B.hC5,
    (decide_eq_true hpS),
    (decide_eq_true Y.1),
    (decide_eq_true Y.2.1),
    (decide_eq_true Y.2.2),
    B.hix,
    B.hIx,
    (decide_eq_true B.ha),
    (decide_eq_true B.hroom),
    (decide_eq_true Pl.fU9),
    (decide_eq_true Pl.fO10),
    B.hN64,
    B.hsL⟩

/-- **The parameters at a proof file's seat.** -/
def planAt (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi) : ShPlan Xi where
  Q := p14Of Z.p.chains (Desc.K14.beforePointOf N)
  G := G
  p := VerifiableInference.Desc.Third.p₁₄Z Z.p.chains.made.sized.proof.set
    Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch
  rad2 := rad2At 2 (p14Of Z.p.chains (Desc.K14.beforePointOf N))
  rad5 := rad5At 2 (p14Of Z.p.chains (Desc.K14.beforePointOf N))
  Wr := dryProofFull.2.1
  fl := 2

/-- **Every sub-protocol of the seated shared chain passes its own test on its parameters.** -/
def chainOkAt (Z : ProofFile.Pub) (N : H2U.Places4) : Bool :=
  VerifiableInference.Desc.blocksOk (Desc.K14.chainOf Z.p.chains
    (p14Of Z.p.chains (Desc.K14.beforePointOf N))
    (VerifiableInference.Desc.K12.Seat.tests N) VerifiableInference.Desc.K12.Seat.last).blocksInOrder

/-- **At the seat.** -/
theorem tests_at {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) (G : FileDescription Xi)
    (hc : chainOkAt Z N = true) : Tests (planAt Z N G) := by
  have e : p14Of Z.p.chains (Desc.K14.beforePointOf N) =
      ⟨recordSet, .shared, codesFull2, x.shape, 0, Desc.K14.beforePointOf N⟩ := by
    unfold p14Of
    simp only [h.set, h.codes, h.shape, h.batch, Bool.false_eq_true, if_false]
  obtain ⟨x1, a1, T⟩ := ten_real
  obtain rfl := sized_one hx a1
  obtain ⟨x2, b1, Y⟩ := planY_real
  obtain rfl := sized_one hx b1
  obtain ⟨x3, c1, Pl⟩ := shPlain_real
  obtain rfl := sized_one hx c1
  refine tests_of (planAt Z N G) (seat_radii_terms hx h hN).binders ?_ ?_ ?_ rfl
    (ToldDesc.blocksOr_ok _ _ _ _ hc)
  · show ∃ s lU lO, Ten (p14Of Z.p.chains (Desc.K14.beforePointOf N)).codes
      (p14Of Z.p.chains (Desc.K14.beforePointOf N)).S s lU lO
    rw [e]
    exact T
  · show PlanY3 (p14Of Z.p.chains (Desc.K14.beforePointOf N)).codes
      (p14Of Z.p.chains (Desc.K14.beforePointOf N)).S
    rw [e]
    exact Y
  · show ShPlain3 (p14Of Z.p.chains (Desc.K14.beforePointOf N)).codes
      (p14Of Z.p.chains (Desc.K14.beforePointOf N)).S
    rw [e]
    exact Pl

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.tests_of
#print axioms Desc.K14.Law.Sh.tests_at
