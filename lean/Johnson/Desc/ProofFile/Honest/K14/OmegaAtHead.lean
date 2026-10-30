-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaAtHead.lean: kind K14: second_door_laid
(Honest/K14/OmegaAtPlan.lean) UNDER THE LIBRARY's HEAD (P5J.AtMg, Johnson/P5J/AtMg.lean, and
P5J.AtMgA, Johnson/P5J/MgAtAll.lean, which extends it): the head holds both what second_door_laid
asks of the plan: that the public files are in the goals' scope, and LaidAt. AND THE SAME FROM ThrS
(Honest/Thread/Said.lean: Thr and what is said) at the same border: the form of the second premise
of the frame's DoorBehind (Honest/Thread/File.lean) with ThrS, at a letter Said, in the place of
Thr. Statements with their proofs: calls; no definition. IT IMPORTS Honest/Thread/Said.lean: it can
stand only behind that folder.

  second_door_at_mg under h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF
  second_door_at_head **under h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀: NOTHING ELSE ON THE
                  PLAN IS ASKED**
  second_door_saidS **the same with ThrS … Said (F0T …).shared.blocksInOrder.length k s₂ m E in the place of
                  Thr, at every Said**: its first half is taken

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

What is not claimed. What stays a premise: Thr (Honest/Thread/Thr.lean) at lettersShared's own
Thread (Honest/Thread/SharedHead.lean) at the shared chain's last border, at s₂; the return of the
start of the last chain at that same s₂; hW, sW and secondRest5. No example of the head is shown in
this file. The side library has a member of the head at each of the goals' two named sets of public
files (headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean; headMember_zGap and headMember_named,
AtFullSide/Top/HeadMemberAtGap.lean); this file calls none of them. Nothing on any property of the
protocol: nothing on completeness, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtPlan
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linLayW)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

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

/-- Under the library's head in its shorter form: secondDoor from secondRest5, hW and sW. -/
theorem second_door_at_mg {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
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
  second_door_laid Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w
    h.scope h.laid hA x s₁ s hs hW sW h5

/-- **Under the library's head: secondDoor from secondRest5, hW and sW.** Thr at the shared chain's
last border at s₂ (hA) and the start's return s at that s₂ (hs) stay premises. -/
theorem second_door_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
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
  second_door_at_mg Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w
    h.toAtMg hA x s₁ s hs hW sW h5

/-- **Under the library's head, from ThrS at the shared chain's last border, at every Said**:
secondDoor; the start's return s at that s₂ (hs), hW, sW and h5 stay premises. -/
theorem second_door_saidS {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  second_door_at_head Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w
    h hA.1 x s₁ s hs hW sW h5

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.second_door_at_mg
#print axioms ProofFile.Honest.K14.second_door_at_head
#print axioms ProofFile.Honest.K14.second_door_saidS
