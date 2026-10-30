-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstScope.lean: IN THE GOALS' SCOPE, AT THE VALUE THAT IS LAID, THE
TESTS IN THE PROMISE's SLOT (Sh.X, Johnson/Desc/K14/Law/SharedConst.lean) ARE MET BY EVERY STATE OF
THE SHARED CHAIN THAT THE VERIFIER's OWN ACCEPTING STEPS REACH, WITH NOTHING ELSE IN FRONT. What
stood in front of Sh.X_reached_seat (Johnson/Desc/K14/Law/SharedConstChain.lean) is paid by calls:
the named tests on the parameters (Sh.tests_in_scope) · that the places name a second proximity test
(omega_some_in_scope) · the six facts on the two proximity tests' parameters
(closedL_in_scope_U | _O, ownMask_in_scope_U | _O, nums_of_planOk, places_firstTree).

  Sh.six_U, Sh.six_O   the three facts at each of the two proximity tests, in scope
  Sh.tests12_in_scope  **the ten named tests on the two proximity tests' parameters** (Sh.tests12,
                       Johnson/Desc/K14/Law/SharedConstTests.lean), in scope, at rUFull | rOFull
  Sh.front_in_scope    what stands in front of the laws at the seat, in scope, in one sentence: Z,
      N,
                       c, nO · what the verifier makes · the named tests · the six facts
  Sh.front_at          the same at a given Z and N that the road and the places make, and a given nO
  Sh.laid_at           what "the written data are laid" gives at a given spelling F of what the
                       verifier makes: its test accepts · its data are the laid ones · the seat's
                           pin
  Sh.omega_at          so the places name a second proximity test, as a term: N.O.getD N.U
  Sh.X_reached_in_scope    **InScope S → "the written data are laid" → the door's two pins → there
                       are Z, N, c: the verifier makes descN … Z N c of its files, and RchAt₂
                       (descN …) k a → Sh.X (planAt Z N (descN …)) k a.1.2 = true**
WHAT IS NOT HERE. No law. The two pins' accept.
What is not claimed. Nothing on the other clauses of the promise. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstChain
import Johnson.Desc.K14.Law.SharedConstLaid
import Johnson.Loose.H2K12.NineTenAtLaid

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

open Johnson.Desc.First.Walk.Tied (RchAt₂)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open H2K.JointK (descN)

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub)
  (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (N : H2U.Places4)
  (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
  (hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).planOk = true)
  (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
    (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) = true)

include hS hZ hN hp hpin in
/-- The three facts at the proximity test on G_u. -/
theorem six_U : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).early = true ∧
    (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).answers = 1 ∧
    (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).nums.firstTree = 0 := by
  have hC := (H2K.JointK.closedL_in_scope_U hS Z hZ ProofFile.pureRoad.links N c hN hp hpin).1
  have ho := H2K.JointK.ownMask_in_scope_U hS Z hZ ProofFile.pureRoad.links N c hN hp
  have hA := hC.atPlace ho 0 0 0 [] (fun _ => 0) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨hA.early, hA.answers,
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan)).trans
      (H2K.Made.places_firstTree Z.made N hN).2.1⟩

include hS hZ hN hp hpin in
/-- The three facts at the proximity test on G_omega. -/
theorem six_O (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1 ∧
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = 0 := by
  have hC := (H2K.JointK.closedL_in_scope_O hS Z hZ ProofFile.pureRoad.links N nO hO c hN hp hpin).1
  have ho := H2K.JointK.ownMask_in_scope_O hS Z hZ ProofFile.pureRoad.links N nO hO c hN hp
  have hA := hC.atPlaceOwn ho 0 0 0 [] (fun _ => 0) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨hA.early, hA.answers,
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan)).trans
      ((H2K.Made.places_firstTree Z.made N hN).2.2.1 nO hO)⟩

include hS hZ hN hp hpin in
/-- **The ten named tests on the two proximity tests' parameters, in scope.** -/
theorem tests12_in_scope (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    Tests12 (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) H2K.Member.rUFull
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull := by
  obtain ⟨_, hC, _, hlb, _⟩ := H2K.JointK.gu_facts o S hS Z hZ ProofFile.pureRoad.links N c hN hp hpin
  obtain ⟨_, hC', ho', hPl, _, _⟩ :=
    H2K.JointK.gomega_facts o S hS Z hZ ProofFile.pureRoad.links N nO hO c hN hp hpin
  exact (Tests12_iff _ _ _ _).2 ⟨(six_U hS Z hZ N c hN hp hpin).1, hC.joh,
    H2K.Made.batOneOk_of_planOk guardedProximityTestParts _ hC.plan, H2K.JointK.ownLabelsB_of_free _ hlb, hC.plan,
    (six_O hS Z hZ N c hN hp hpin nO hO).1, ho', hPl, hC'.joh, hC'.plan⟩

omit hS Z hZ N c hN hp hpin in
/-- **What stands in front, in the goals' scope, at the value that is laid.** -/
theorem front_in_scope {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hS : VerifierAndGoals.InScope S = true) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r))
    (hpins : ∀ Z, ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z →
      VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true ∧
        VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2)) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
      (nO : H2U.PlaceNums), ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      N.O = some nO ∧ Tests (planAt Z N (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) ∧
      Tests12 (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) H2K.Member.rUFull
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull ∧
      ((H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).early = true ∧
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).answers = 1 ∧
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).nums.firstTree = 0) ∧
      ((H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1 ∧
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = 0) := by
  obtain ⟨F, hF, hp, _, hs', _⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs'
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := H2K.JointK.k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hS Z _ N c hp hpin
  exact ⟨Z, N, c, nO, hZ, hN, hF, hO,
    tests_in_scope hS hF hp hZ hN (hpins Z hZ).1 (hpins Z hZ).2 hL hx,
    tests12_in_scope hS Z hZ N c hN hp hpin nO hO, six_U hS Z hZ N c hN hp hpin,
    six_O hS Z hZ N c hN hp hpin nO hO⟩

omit hS Z hZ N c hN hp hpin in
/-- The verifier's test on what it has made asks that the first chain's last sub-protocol has a
round. -/
theorem seal_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    F.sealLast = true := by
  unfold FileDescription.planOk at h
  exact (Bool.and_eq_true_iff.1 h).2

omit hS Z hZ N c hN hp hpin in
/-- **What "the written data are laid" gives at a given spelling of what the verifier makes.** -/
theorem laid_at {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {pol lay KL : ByteArray}
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    F.planOk = true ∧ F.data "proof file" = .ok D ∧
      VerifiableInference.PlanWritten.seatPinnedProof pol F = true := by
  obtain ⟨F', hF', hp, hD, hs', _⟩ := LPFD.Full.laidPOf_ok hL
  obtain rfl : F' = F := Except.ok.inj (hF'.symm.trans hF)
  exact ⟨hp, hD, LPFD.asks_written hs'⟩

omit hS Z hZ N c hN hp hpin in
/-- **The places name a second proximity test**, as a term. -/
theorem omega_at {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (hS : VerifierAndGoals.InScope S = true) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r))
    {Z : ProofFile.Pub} {N : H2U.Places4} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) :
    N.O = some (N.O.getD N.U) := by
  obtain ⟨hp, _, hpin⟩ := laid_at hL hF
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hS Z _ N c hp hpin
  rw [hO]
  rfl

omit hS Z hZ N c hN hp hpin in
/-- **The front at a given Z, N and nO.** -/
theorem front_at {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hS : VerifierAndGoals.InScope S = true) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r))
    {Z : ProofFile.Pub} (hZ : ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2)) {N : H2U.Places4}
    (hN : H2U.placesOfMade Z.made = .ok N) {nO : H2U.PlaceNums} (hO : N.O = some nO) :
    Tests12 (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) H2K.Member.rUFull
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull ∧
      ((H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).early = true ∧
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).answers = 1 ∧
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).nums.firstTree = 0) ∧
      ((H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1 ∧
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = 0) := by
  obtain ⟨Z', N', c, nO', hZ', hN', _, hO', _, h12, hU, hOm⟩ := front_in_scope hS hL
    (fun Z'' h'' => by
      obtain rfl : Z = Z'' := Except.ok.inj (hZ.symm.trans h'')
      exact ⟨hs, hf⟩) hx
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain rfl : N' = N := Except.ok.inj (hN'.symm.trans hN)
  obtain rfl : nO' = nO := Option.some.inj (hO'.symm.trans hO)
  exact ⟨h12, hU, hOm⟩

omit hS Z hZ N c hN hp hpin in
/-- **In the goals' scope, at the value that is laid.** -/
theorem X_reached_in_scope {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hS : VerifierAndGoals.InScope S = true) (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r))
    (hpins : ∀ Z, ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z →
      VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true ∧
        VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2)) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl),
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      ∀ {Str : Type} (k : ℕ)
        (a : (((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).XiPub ×
          (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₁) ×
          (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₂) × Str),
        RchAt₂ (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) k a →
          X (planAt Z N (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) k a.1.2 = true := by
  obtain ⟨Z, N, c, nO, _, _, hF, hO, hT, _, ⟨u1, u2, u3⟩, o1, o2, o3⟩ :=
    front_in_scope hS hL hpins hx
  exact ⟨Z, N, c, hF, fun k a hR =>
    X_reached_seat o Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c nO hO hT u1 u2 u3 o1 o2 o3 k a hR⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.six_U
#print axioms Desc.K14.Law.Sh.six_O
#print axioms Desc.K14.Law.Sh.tests12_in_scope
#print axioms Desc.K14.Law.Sh.front_in_scope
#print axioms Desc.K14.Law.Sh.front_at
#print axioms Desc.K14.Law.Sh.seal_of_planOk
#print axioms Desc.K14.Law.Sh.laid_at
#print axioms Desc.K14.Law.Sh.omega_at
#print axioms Desc.K14.Law.Sh.X_reached_in_scope
