-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaAtPlan.lean: kind K14: second_door_shared
(Honest/K14/OmegaAtShared.lean) WITH ITS PREMISES ON THE PLAN HAD FROM THE LIBRARY's OWN LAWS. The
IOP as written in Lean, P5J.F0T, is the library's descN at the same arguments by unfolding
(f0T_is_descN, Johnson/Road/Tables/FlatLengths.lean); so the two proximity tests' own tests on the
plan follow from F0T's test on the plan (plan_at_seat_U, plan_at_seat_O:
Johnson/Loose/H2K12/ClosedAtSeats.lean), and that the plan has a second test follows, in the goals'
scope, from that test and the pin on the declared rounds (omega_some_in_scope:
Johnson/Loose/H2K12/OmegaIsSome.lean). Under the library's LaidAt (Johnson/P5J/LaidOpens.lean) Plan2
follows too (Honest/K14/PlanAtHead.lean). Statements with their proofs; no definition.

  plans_at_shared from F0T's test on the plan and Np.O = some nO: the two tests' own tests on the
                  plan accept, at the library's numbers
  second_door_plan second_door_shared without h9 and h10: asked of the plan: Plan2, Np.O = some nO,
                  (F0T …).planOk = true
  second_door_scope **without Np.O = some nO too**: asked of the plan: Plan2; a public S in the
                  goals' scope; (F0T …).planOk = true; the pin on the declared rounds accepts.
                  (Against second_door_shared three premises on the plan, h9, h10 and Np.O = some
                  nO, are traded for three others. Of these the library's LaidAt gives the last two:
                  F0T's test on the plan is its field planOk; the pin's accept follows from its
                  field asks by the library's LPFD.asks_written. The scope stands beside it)
  second_door_laid **in the goals' scope, under LaidAt: NOTHING ELSE ON THE PLAN IS ASKED**: LaidAt
                  gives both accepts, as said, and Plan2 follows from it (plan2_of_laid)

THE THREE second_door_… STAND AT THE BORDER (F0T …).shared.blocksInOrder.length: the border at which the
frame's DoorBehind (Honest/Thread/File.lean) speaks of the shared chain: its second premise is Thr
of the shared chain's Thread at that border.

s: the state that the start of the last chain (FileDescription.start₃ of P5J.F0T) returns. hW: the weights
at the border of s name no written-out variable twice and only their own variables (WeightsFit,
Honest/K14/DotPads.lean); sW: each place of W's pad in its main table, in the statement of s, lies
inside W's table at an entry numbered at least 2 ^ kCol (PadsBehind, DotPads.lean); h5: secondRest5
is all true (Honest/K14/OmegaJoin.lean: five tests where the taking-over and linDotRow return, fewer
elsewhere).

OF THE ELEVEN TESTS OF secondDoor (Honest/K14/SecondDoor.lean: a list of this kind's own; that it is
all true is by itself no accept of the sub-protocol: door_owed there) SIX ARE READ OFF THE RUN THAT
Thr HOLDS, THE LAST FOLLOWS FROM hW, sW AND THE RUN, AND THE REST ARE PREMISES: three of
secondRest5's five are entries of secondDoor to the letter.

What is not claimed. No example of LaidAt, of F0T's test on the plan or of the pin is shown in this
file; one, at VerifierAndGoals.storedPublicFiles, is AtFullSide/Top/HeadMemberAtFull.lean's. That Thr holds at any run.
hW, sW and secondRest5 at any state. Nothing on any property of the protocol: nothing on
completeness, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead
import Johnson.Road.Tables.FlatLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay linLayW)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St p14Of beforePointOf)

/-- From F0T's test on the plan, where the plan has a second proximity test: the two tests' own
tests on the plan accept. -/
theorem plans_at_shared (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk = true) :
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) : Block T12 Unit).planOk = true ∧
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).planOk = true := by
  rw [OnBytes.Road.Tables.f0T_is_descN] at hp
  exact ⟨H2K.JointK.plan_at_seat_U _ Zp _ Np cF hp, H2K.JointK.plan_at_seat_O _ Zp _ Np nO hO cF hp⟩

section letters
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

section plan
variable {sentU : Array OracleNotice} {layO : TreeLay}

/-- second_door_shared, with the two proximity tests' own tests on the plan had from F0T's. -/
theorem second_door_plan (hQ : Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO)
    (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk = true)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  second_door_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w hQ nO
    hO (plans_at_shared Zp Np cF nO hO hp).1 (plans_at_shared Zp Np cF nO hO hp).2 hA x s₁ s hs hW
    sW h5

/-- **second_door_plan, with the plan's second proximity test had too**, in the goals' scope. -/
theorem second_door_scope (hQ : Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO)
    {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hS Zp ProofFile.pureRoad.links Np cF hp hpin
  exact second_door_plan Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w hQ
    nO hO hp hA x s₁ s hs hW sW h5

end plan

/-- **In the goals' scope, under the library's LaidAt: secondDoor from secondRest5, hW and sW, with
nothing else asked of the plan.** Thr at the shared chain's last border at s₂ (hA) and the start's
return s at that s₂ (hs) stay premises. -/
theorem second_door_laid {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_of_laid hZ L
  exact second_door_scope Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w
    hQ hZ L.planOk (LPFD.asks_written L.asks) hA x s₁ s hs hW sW h5

end letters

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.plans_at_shared
#print axioms ProofFile.Honest.K14.second_door_plan
#print axioms ProofFile.Honest.K14.second_door_scope
#print axioms ProofFile.Honest.K14.second_door_laid
