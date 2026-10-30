-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/K4MarksTwelve.lean: CONDITIONAL.

What is here. THE LIST `k4Marks` (Law/K4Marks.lean) IS NOT HOLLOW UNDER THE LIBRARY's HYPOTHESIS ON
THE PUBLIC FILES, IN TWO WAYS: IT HAS TWELVE MARKS, AND AT EACH MARK's PLACE STANDS A MEMBER OF THE
CHAIN. A mark (`Mark`, Honest/Law/Marks.lean) is a place, a test on the challenges and a stated
number: it names an event on the challenges at which the verifier rejects nothing; it is counted,
not tested by the verifier. A mark is silent where its test returns none. (It is not the verifier's
own sign of a failure, which other files of this folder call a mark too.) Under h : AtMgA and hB,
that the library's maker of the base returns Bs at h's public part: `k4Marks Zp Bs.G₀` has TWELVE
marks: no look-up that does not return leaves a mark out in silence. The same at a ground under hG :
`ProofFile.blankBy ProofFile.pureRoad.links Zp` = some G₀. By the library's `IM.k4_of` (Johnson/IMR/K4Seat.lean)
and `IM.Open.made`, `IM.Open.blank` (Johnson/IMR/SeatOpen.lean). Under h alone, at every ground: at
each mark's place stands a member of the chain's flat list (`k4Marks_member`). Why: the frame looks
a mark up by the place of a member of the chain (`markOf`, Honest/Law/Marks.lean, takes a place); a
mark at a place without a member would be in the list and be looked up at no member. By `IM.k4_of`,
`IM.hear_at_flat` (Johnson/IMR/FlatIx.lean) and `IM.alone_place`. ITS IMPORT LINES NAME
Law/K4Marks.lean AND THREE OF THE LIBRARY's (Johnson/IMR/K4Seat.lean, Johnson/IMR/FlatIx.lean,
Johnson/P5J/MgAtAll.lean), no other file of this folder.

Not shown here. Which member stands at a mark's place (its number; that it is K4's own
sub-protocol): `IM.k4_of` has it; not stated here. That the frame's test admits each place:
Law/K4MarksSeat.lean. THE BOUND AT A MEMBER IS OWED: `k4_markDebt_table` (Law/MarkDebt.lean) has the
frame's sentence `MarkDebt` at `k4Mark Q`, at the number `(k4Mark Q).share.val`, under three
hypotheses, and between it and a member of the chain stand, one by one: that the data of the
member's rounds have the entries of the verifier's table of K4's rounds, and each round's kind its
name's (hent, hkind); that la ≤ muV, or the three hypotheses on the plan's makers from which
Law/MarkPlan.lean has it, AT THE GROUND's LAYERS under the library's hypothesis on the public files:
shown nowhere; and the kit of typed challenges: that sentence stands at `Run.ckP .two` alone. WHAT A
MARK's SILENCE GIVES AT ANY STATE OF THE VERIFIER IS SHOWN NOWHERE. EACH SHARE IS A WRITTEN PAIR OF
NUMBERS AND NO BOUND. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that
h has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). h IS `k4Marks_member`'s ONLY HYPOTHESIS. hB AND hG ASK
NOTHING BEYOND h: at h's opening the base and the ground are there (`IM.Open.made`,
`IM.Open.blank`). THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one: its imports reach modules
under Johnson/Goal/: Johnson/IMR/K4Seat.lean imports one. Which modules it imports in all has not
been counted. No property is claimed.

  `k4Plans_head`   under h the ground has a plan at each group below 12.
  `k4Marks_twelve`, `k4Marks_twelve_ground`   **twelve marks.**
  `k4Marks_member`   **a member of the chain at each mark's place.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.K4Marks
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatIx
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and hB. The ground has a plan at each group below 12. -/
theorem k4Plans_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ g, g < 12 → (Bs.G₀.W.G[g]?).isSome = true := by
  intro g hg
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨_, _, x, -, -, -, -, -, -, -, e, -⟩ := IM.k4_of h.scope h.reads O g hg
  rw [e]
  rfl

/-- CONDITIONAL: on h and hB. **THE LIST HAS TWELVE MARKS.** -/
theorem k4Marks_twelve (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (k4Marks Zp Bs.G₀).length = 12 :=
  k4Marks_length (k4Plans_head h hB)

/-- CONDITIONAL: on h and hG. The same at the ground that is made of the public part. -/
theorem k4Marks_twelve_ground (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) : (k4Marks Zp G₀).length = 12 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  exact k4Marks_twelve h O.made

/-- CONDITIONAL: on h. **AT EACH MARK's PLACE STANDS A MEMBER OF THE CHAIN**, at every ground. -/
theorem k4Marks_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ k4Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place := by
  intro mk hm
  obtain ⟨g, hg, e⟩ := k4Marks_place hm
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, _, e1, e2, -, hla, -⟩ := IM.k4_of h.scope h.reads O g hg
  exact ⟨b, List.mem_of_getElem? (IM.hear_at_flat e1 e2), by rw [IM.alone_place hla, e]⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Plans_head
#print axioms ProofFile.Honest.K4.k4Marks_twelve
#print axioms ProofFile.Honest.K4.k4Marks_twelve_ground
#print axioms ProofFile.Honest.K4.k4Marks_member
