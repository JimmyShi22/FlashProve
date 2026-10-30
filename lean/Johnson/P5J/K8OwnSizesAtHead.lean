-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K8OwnSizesAtHead.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES AT EVERY BUILT
SEGMENT (ProofFile.smallSizesOwnB, Johnson/Desc/ProofFile/Lot/K8SmallSizes.lean: the fourth conjunct of
the kind's frozen condition) IS A THEOREM UNDER THE HEAD. Three theorems.
  colsAt_att         K8N.ColsAt Zp (2 * g + 1), g < 12: u3_cols_att
                     (Johnson/Desc/First/Att/Door/Law/K5U3Cols.lean): the law on the tables' end at
                     the twelve attention segments.
  **ownSizes_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ∀ G,
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true**: NO PREMISE BUT
    THE HEAD: ownSizes_of_att_law (Johnson/P5J/K8OwnSizesHead.lean) at it.
  k8Cond_own         A TRIPWIRE: laid into a value of the frozen condition (P5J.AtMgA.K8Cond,
                     Johnson/Goal/Skeleton/Kinds/K8Bridge.lean) at its fourth place, it types. It
                     shows nothing else: a value of the condition goes in, a value comes out.
THE ROAD, WHOLE. The test is cut into three sorts of box (Johnson/P5J/K8ThreeBoxes.lean). A box
reads a segment's list of names at one index: there stand: at a matrix's tree what the names' tie
says (three kinds' laws, joined in a fourth file) · at ZZ and at the third vector of reads the
segment's own number with "ZZ" | "U3" (laws of the maker's text). The boxes at the trees and at ZZ
are closed facts on values that the head's two pins fix: Lean's kernel decides them at all 25, with
negative tests (Johnson/P5J/K8OwnSizesAt.lean). The box at the third vector asks that the tables'
end be at most the array's columns: three kinds' laws "by the make": the feed-forward segments',
the attention segments', the output head's (Johnson/P5J/K8EndsJoin.lean · K8EndsJoinLay.lean). That
the plans' shapes have their matrices' numbers is a theorem at whatever publicOf returns.
Limits. The head is a premise: over the entry tests' second and third lists (both pins are
spent); a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone.
The written values rest on their files' own heads. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8OwnSizesHead
import Johnson.Desc.First.Att.Door.Law.K5U3Cols

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes.Flat
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open K8N

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The law at the twelve attention segments: another file's (`u3_cols_att`). -/
theorem colsAt_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ g < 12, ColsAt Zp (2 * g + 1) :=
  fun _ hg _ _ hG e3 =>
    H2K5.Door.u3_cols_att h.toAtMg.scope h.toAtMg.reads h.toAtMg.laid.pub hG hg e3

/-- **THE NAMED TEST ON SIZES AT EVERY BUILT SEGMENT, FROM THE HEAD ALONE.** -/
theorem ownSizes_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true :=
  ownSizes_of_att_law h (colsAt_att h)

/-- A tripwire: the end is the frozen condition's fourth conjunct. -/
theorem k8Cond_own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (C : h.K8Cond 𝔏) : h.K8Cond 𝔏 :=
  ⟨C.1, C.2.1, C.2.2.1, ownSizes_at_head h, C.2.2.2.2⟩

end P5J

#print axioms P5J.colsAt_att
#print axioms P5J.ownSizes_at_head
#print axioms P5J.k8Cond_own
#print axioms H2K5.Door.u3_cols_att
