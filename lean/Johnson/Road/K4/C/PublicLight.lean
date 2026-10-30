-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PublicLight.lean: CONDITIONAL: UNDER THE HEAD.

What is here. The layers' own rounds (sub-protocol K4): tests with code on the plan alone, at the
head's own public parameters, at each of the twelve groups: by the library's door withPlans_public
(RowHead/FrontOfHead.lean): a fact at the makers' twins with free letters is a fact at what
publicOf returns. Statements and proofs.

  `twins_head`, `twins_head_all`   the door under the head: for a test on the public parameters; for
                    a test at each group's plan.
  **`light_head`**  the plan's numbers · four tests on the lookup's shape · the slots · the tables ·
                    the points.

Not shown here. THE HEAD (hA here; h in the clause that follows: the library's hypothesis
`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the side library AtFullSide proves, with no hypothesis, that
h has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). `twins_head` and `twins_head_all` ask besides a fact at the
makers' twins (hf, hT), which the five closed facts under Free/ give for `light_head`;
`twins_head_all` and `light_head` ask besides g < 12 (hg) and that the plan at g is there (hG): hG
asks nothing beyond hA: it is a field of `LaidK4`, which hA gives at each of the twelve groups
(`laid_at`, Johnson/Desc/ProofFile/Honest/K4/Law/LaidAtGroup.lean; not called here). THE FULL SIZE
ALONE, and the format's second hash function alone. NOT ALL OF THE TEST k4PublicX
(Johnson/Desc/ProofFile/Honest/K4/Law/PublicX.lean): not here: the panels' test, the weight claims'
test, the test on the join's factors, and that the count of padding keys by the host (the
sub-protocol that calls the lookup) is the layout's. BENEATH EACH OF THE FIVE CLOSED FACTS THAT ARE
CALLED (Free/) STAND EIGHT USES OF kernel_rfl, which its head names: comparisons by Lean's own
kernel; no independent checker has replayed them. The import closure, by a program's walk along the
imports that stops unopened at Johnson/Goal/, Johnson/D/, Johnson/Bridge/ and ThirdParty/ and at
every name that begins Cb.Bridge (so these are floors): 18 modules under Johnson/Goal/ (through the
library's Johnson/Road/K4/RowHead/FrontOfHead.lean), 4 under Johnson/Bridge/, 46 whose name holds
RecCompile; none at the other three; none of RecCompile's Honest*, Both or PassH*. An earlier walk,
which went on through Johnson/Bridge/, met 2 modules under ThirdParty/. No line of them is restated
here and no goal is stated. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one. Nothing on soundness, on completeness or on any other property.

Kin. `twins_head` is the term of the library's `front_of_head` (RowHead/FrontOfHead.lean) with the
test left free; that law has it for the one test frontB at the groups 0 and 1.
No property is claimed.
-/
import Johnson.Road.K4.RowHead.FrontOfHead
import Johnson.Road.K4.C.Free.FreeNums
import Johnson.Road.K4.C.Free.FreeDepth
import Johnson.Road.K4.C.Free.FreeSlots
import Johnson.Road.K4.C.Free.FreeTables
import Johnson.Road.K4.C.Free.FreePoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (withPlans withPlans_public)
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (publicSteps_of)
open OnBytes.Desc.First.K4.Rt (planNumsB k4Takes pointsB)
open OnBytes.Desc.First.K4.RtPub (tablesB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The door under the head**: a test that is true at the makers' twins, at all four free letters,
is true at the head's own public parameters. -/
theorem twins_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (f : Layer.Pub → Array Layer.HPlan2 → Bool)
    (hf : ∀ v pub sc rope, withPlans v pub sc rope f = true) :
    f (P5J.At.X Zp).layers (P5J.At.X Zp).G = true :=
  withPlans_public (OnBytes.Road.Hd.scan_of_scope hA.scope hA.reads hA.pubOne)
    (publicSteps_of hA.pubOne) f (hf _)

/-- The same for a test at each of the twelve groups' plans. -/
theorem twins_head_all (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (T : Layer.Pub → Layer.HPlan2 → Nat → Bool)
    (hT : ∀ v pub sc rope, withPlans v pub sc rope
      (fun L G => (List.range 12).all fun g => (G[g]?).any fun hp => T L hp g) = true)
    {g : ℕ} (hg : g < 12) {hp : Layer.HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    T (P5J.At.X Zp).layers hp g = true := by
  have t := List.all_eq_true.1 (twins_head hA _ hT) g (List.mem_range.2 hg)
  rw [hG] at t
  exact t

/-- **THE LIGHT TESTS ON THE PLAN, UNDER THE HEAD**, at each group below 12 and its plan.
CONDITIONAL: on the head (hA), hg and hG. -/
theorem light_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {hp : Layer.HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    planNumsB (P5J.At.X Zp).layers hp g = true ∧
      (P5J.At.X Zp).layers.y.h.la ≤ (P5J.At.X Zp).layers.y.fo.dT ∧
      (P5J.At.X Zp).layers.y.h.lt ≤ (P5J.At.X Zp).layers.y.fo.dT ∧
      ((P5J.At.X Zp).layers.y.fo.calls.size == (P5J.At.X Zp).layers.y.calls.size) = true ∧
      (Forest.planeCols (P5J.At.X Zp).layers.y.fo (P5J.At.X Zp).layers.y.h.lmb).toBool = true ∧
      Forest.elems (P5J.At.X Zp).layers.y.fo + k4Takes (P5J.At.X Zp).layers hp g ≤ hp.ns ∧
      hp.tl.funOpen = true ∧ (hp.tl.ix.U.getD 2 none).isSome = true ∧
      tablesB (P5J.At.X Zp).layers hp g = true ∧
      ((OnBytes.Desc.First.K4.RtPub.tablesAt (P5J.At.X Zp).layers g).any fun r =>
        pointsB (P5J.At.X Zp).layers g r.2.1) = true := by
  have a := twins_head_all hA _ Free.freeNums hg hG
  have b := twins_head hA _ Free.freeDepth
  have c := twins_head_all hA _ Free.freeSlots hg hG
  have d := twins_head_all hA _ Free.freeTables hg hG
  have e := twins_head_all hA _ Free.freePoints hg hG
  simp only [Bool.and_eq_true, decide_eq_true_eq] at b c d
  exact ⟨a, b.1.1.1, b.1.1.2, b.1.2, b.2, c, d.1.1, d.1.2, d.2, e⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.twins_head
#print axioms OnBytes.Road.K4.C.twins_head_all
#print axioms OnBytes.Road.K4.C.light_head
