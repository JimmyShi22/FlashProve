-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/SeatsNamedFull.lean: the test `P5J.seatsNamedC`, in the form off the view and the
keys (`seatsKeyV`, Johnson/HB/LLHARD/SeatsNamedKey.lean), accepts at the written values of the full
size; and so the test itself, at the closed letters of the head's law, wherever the value is laid in
scope and the test that holds the made plan to the written one accepts.

Row or tool. Closed facts on written values, and the law in scope by rewriting through named ties. A
payer for a premise of another law.

The test's arguments at the head's law, their written terms and their ties.
  `At.X Zp`, read through its view: `xShapeFull` (Johnson/G/XShapeLit.lean). Tie: `xShape_in_scope`
    (Johnson/Goal/Numbers/MadeInScope.lean).
  `At.layout Zp`: `layoutFull` (Johnson/G/LayoutLit.lean). Tie: `layout_in_scope`, there.
  `At.num Zp`, `At.arr Zp`: `numOfPlan`, `arrOf` at `P5T.seatsAllFull`. `At.N Zp cF`, read through
    its field `sent`: `P5T.N0Full`. Tie: `seats_in_scope` (Johnson/P5T/PlanSeatsTie.lean).

The premises of `seatsNamedC_at_name` beyond scope, the files read, and the value laid. One:
`madePinnedAt … = true`: a yes of the law form of a row that the verifier's entry tests for the
proof file ask (`madeRow`, the ninth); in scope it follows from `LaidAt` (`pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean).
(Where this and lean/THEOREM.md differ, the page holds.)
That attention is there and there are twelve groups comes of `publicO_at_scope` at
`LaidAt.publicO`. That the value is laid comes of `laidPOf_of` at four fields of `LaidAt`. What the
sub-protocols tell is not read.

What is here.
  `groupsFound_full`: every seat of the 25 groups of `N0Full` is a seat of `seatsAllFull`.
  `seatsKeyV_full`: the test accepts. `seatsKeyV_walks`: it walks 176 entries, and none of the 25
    groups is empty.
  `seatsKeyV_rejects`: negative tests: at the empty layout; and at numbers in which the first
    segment's opening seats stand twice.
  `seatsNamedC_at_name`.
By evaluations in Lean's kernel (`decide +kernel`): the first four.

Limits. Nothing in this file says that `madePinnedAt` accepts at any files. Nothing on soundness.


-/
import Johnson.HB.LLHARD.SeatsNamedKey
import Johnson.P5T.PlanSeatsTie
import Johnson.P5J.LettersAt
import Johnson.P5J.LaidOpens
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.G.XShapeLit
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model Johnson.G
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope layout_in_scope)
open Meaning (viewTail)
open P5T (seatsAllFull N0Full seats_in_scope)

set_option maxRecDepth 1000000 in
theorem groupsFound_full : groupsFound seatsAllFull N0Full = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written values.** -/
theorem seatsKeyV_full : seatsKeyV xShapeFull layoutFull seatsAllFull N0Full = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It walks 176 entries, and none of the 25 groups is empty. -/
theorem seatsKeyV_walks :
    ((List.range 25).map fun k => (viewTail xShapeFull k).1).sum = 176 ∧
      ((List.range 25).all fun k => !(N0Full.group k).isEmpty) = true := by decide +kernel

/-- The numbers with the first segment's opening seats laid twice. -/
def sentTwice : Numbers :=
  { N0Full with
    sent := fun m t =>
      if m == 0 && t == 0 then N0Full.sent 0 0 ++ N0Full.sent 0 0 else N0Full.sent m t }

set_option maxRecDepth 1000000 in
/-- **Negative tests.** -/
theorem seatsKeyV_rejects :
    seatsKeyV xShapeFull ⟨[]⟩ seatsAllFull N0Full = false ∧
      seatsKeyV xShapeFull layoutFull seatsAllFull sentTwice = false := by decide +kernel

/-- **At the closed letters of the head's law.** -/
theorem seatsNamedC_at_name {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (_ : VerifierAndGoals.readFiles Z = .ok pp) (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hM : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    seatsNamedC (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) (At.num Zp) (At.arr Zp)
      (At.N Zp cF) = true := by
  have hF := H2K.Sizes.publicO_at_scope hZ L.publicO
  have hl := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  obtain ⟨-, hAll, hN0⟩ := seats_in_scope hZ L.pub hM hl
  have hs : (At.N Zp cF).sent = N0Full.sent := by
    rw [← hN0]
    rfl
  rw [seatsNamedC_same hs]
  show seatsNamedC Zp.p.X (Meaning.sizesOf Zp.p.X) Zp.first.layout
    (P5T.numOfPlan (P5T.planSeatsAll Zp Zp.D)) (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) N0Full = true
  rw [hAll, seatsNamedC_view hF.p4 hF.groups _ groupsFound_full, xShape_in_scope hZ L.pub hM,
    layout_in_scope hZ L.pub hM]
  exact seatsKeyV_full

end P5J

#print axioms P5J.groupsFound_full
#print axioms P5J.seatsKeyV_full
#print axioms P5J.seatsKeyV_walks
#print axioms P5J.seatsKeyV_rejects
#print axioms P5J.seatsNamedC_at_name
