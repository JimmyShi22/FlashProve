-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HeadAt.lean: THE SECOND OF THE NAMED TESTS OF THE CLOSED CONSTANT's HEAD
(At.Nine, Johnson/P5J/AtNameA.lean): (headAt (At.X Zp)).isSome = true: FOLLOWS FROM "LAID", IN
SCOPE. Theorems with their proofs.

  head_of_open     in scope · readFiles returns · IM.Open … · F.planOk = true ⊢
                   (headAt Z.p.X).isSome: k3_of hands K3's own
                   sub-protocol at the address ⟨1, some 24, 3, K3⟩, alone in its place; plan_alone
                   hands its test on the plan;
                   theStated_head (Johnson/Desc/First/Link/Law/HeadAtOfPlan.lean) does the rest
  At.head_at       in scope · readFiles returns · LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF ⊢
                   (headAt (At.X Zp)).isSome = true: at LaidAt's own fields "opened" and "planOk"

A second road, not taken here: calls_place (Johnson/Desc/Kinds/Law/K6PubInScope.lean) gives
placeAt X 24 false with its shape from "in scope" and publicOf's return alone;
its file is not imported here.

Limits. IN SCOPE, at OnBytes.secondHashFunction. It shows none of the other named tests. Nothing on soundness or
on hiding.

-/
import Johnson.P5J.LaidOpens
import Johnson.P5J.LettersAt
import Johnson.IMR.K3Seat
import Johnson.IMR.PlanAt
import Johnson.Desc.First.Link.Law.HeadAtOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (headAt)
open ProofFile (Cl)

/-- In the letters of `IM.Open` (Johnson/IMR/SeatOpen.lean). -/
theorem head_of_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true) :
    (headAt Z.p.X).isSome = true := by
  obtain ⟨Lk, b, b', h1, h2, h3, hla⟩ := IM.k3_of hS hR O 24 (by omega) false
  have hb' : b'.planOk = true := IM.plan_alone O hp h1 h2 hla
  rw [← O.W]
  exact theStated_head _ _ _ _ _ _ h3 hb' rfl

end VerifiableInference.Desc.LinkJoin

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- **"The output head's lookup has its place" follows from "laid", in scope.** -/
theorem At.head_at {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hR : VerifierAndGoals.readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp)).isSome = true := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact VerifiableInference.Desc.LinkJoin.head_of_open hZ hR O L.planOk

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.head_of_open
#print axioms P5J.At.head_at
