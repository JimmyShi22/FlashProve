-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FrontCount.lean: CONDITIONAL on h, the library's hypothesis on
the public files (`P5J.AtMgA`), and on `LaidK4`. Four statements with their proofs.

What is here. Two of the four hypotheses that `k4Seated_letters` (Law/SeatedHead.lean) and
`seated_all_head` (Law/W/ExchangeParts.lean) ask, beside h and `LaidK4`, for the seat of the layers'
own rounds (the sub-protocol K4; `K4Seated`, Law/Seated.lean): hQ, that `k4PubOf`
(Honest/K4/Part.lean) returns the place's public data at the member's parameters, and front, that
these data count as many rounds in front as stand in front of the member in the chain's flat list.
BOTH UNDER h, the hypothesis on the public files (`P5J.AtMgA`), AND `LaidK4` (Law/SeatedHead.lean)
ALONE. How. Under h the public part's table of stretches is the written one (`cuts_head`: the
library's `cuts_of_plans` and `plans_front`, Johnson/Desc/First/Att/Row/, at the accept of the entry
tests' pin on the plan), and the chain's cut into sub-protocols is the written one (the library's
`cut_of_head`, Johnson/Road/K4/K4HeadWritten.lean). That the two written lists count alike is the
closed fact of Law/FrontClosed.lean.

  `roundsTo_cut`   the rounds in front of member k, off the chain's cut
  `cuts_head`   under h the table of stretches is the written one
  `k4Pub_head`   **hQ: `k4PubOf` returns, and what**
  `front_head`   **front**, in `seated_all_head`'s letters

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). h is the only hypothesis of `cuts_head`; `k4Pub_head` and
`front_head` ask `LaidK4`, which h gives at each group (`laid_at`, Law/LaidAtGroup.lean), besides,
and `front_head` hQ, a name of a public value. THE FULL SIZE ALONE, and the format's second hash
function alone (`OnBytes.secondHashFunction`). `cuts_head` spends the accept of the pin on the plan
(`madePinnedAt`), which the laid value's tests hold. The two other hypotheses of the seat, half and
fits, are not here. IT CALLS BY NAME A STATEMENT OF A FILE UNDER Johnson/Goal/ (`P5J.pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean), in the way in which the library's
Johnson/Road/K4/K4PlanOfLaid.lean calls it; that file was not read for this one. A LAW, NOT A PART:
no file that defines a part of the proof file's description may import this one. Nothing on
soundness, on completeness or on any other property.

Kin. `roundsTo_cut` IS, WORD FOR WORD, `K5.roundsTo_cut` (Honest/K5/Law/BaseAt.lean, of other
writers), with the same proof, typed again here; `cuts_head` IS THE SAME SENTENCE AS
`K3.Law.AtThr.cuts_head` (Honest/K3/Law/Thread/RngHead.lean, of other writers), by another road to
the library's `cuts_of_plans`. Neither file is imported: by a walk over import lines each would add
some 900 modules to this file's 8,700, among them modules under Johnson/Goal/ or Johnson/Bridge/
that this file does not reach. Sought: by statement, to the letter and up to the bound letters,
among the theorems of the library and of files that are no part of it yet, as they lay with the
writer: no hit (these two part from ours in how a name is spelt); by short name: each that stands
elsewhere sought out: `front_head` stands in three further files of the library; two were read:
other matters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontClosed
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.Road.K4.K4HeadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- The rounds in front of member k of a list of sub-protocols, off the list's cut. -/
theorem roundsTo_cut {S Cl : Type} (bs : List (Block S Cl)) (k : Nat) :
    roundsTo bs k = (((VerifiableInference.PlanWritten.cutOf bs).take k).map (·.2.2.1)).sum := by
  unfold roundsTo declsTo VerifiableInference.PlanWritten.cutOf
  rw [List.length_flatMap, ← List.map_take, List.map_map]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h. **The public part's table of stretches is the written one.** -/
theorem cuts_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    Zp.cuts = Johnson.AtFull.Cut.cutWritten := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  exact H2K5.Row.cuts_of_plans (H2K5.Row.asBy h.laid.pub)
    (H2K5.Row.plans_front h.scope h.laid.pub hy)

/-- CONDITIONAL on h and Lh. **hQ: `k4PubOf` RETURNS AT THE MEMBER's PARAMETERS**, with the count of
the rounds that stand in front of the member in the chain's flat list. -/
theorem k4Pub_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    k4PubOf Zp x.2 = some
      { P := x.2.P, hp := x.2.hp, g := x.2.g, link := x.2.link, piece := x.2.piece,
        r0 := roundsTo cF.blocksInOrder k, seg := 2 * x.2.g } := by
  have e1 : Zp.roundsBefore? (k4StepOf g) = some (roundsWritten (28 * g + 4)) := by
    rw [H2K5.Row.roundsBefore_by, cuts_head h]
    have t := List.all_eq_true.1 k4_front_closed g (List.mem_range.2 Lh.lt)
    exact of_decide_eq_true t
  have e2 : roundsTo cF.blocksInOrder k = roundsWritten (28 * g + 4) := by
    rw [roundsTo_cut, OnBytes.Road.K4.cut_of_head h.toAtMg, Lh.num]
    rfl
  unfold k4PubOf
  rw [Lh.name]
  show (Zp.roundsBefore? (k4StepOf g)).map _ = _
  rw [e1, e2]
  rfl

/-- CONDITIONAL on h, Lh and hQ. **front.** -/
theorem front_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) : Qp.r0 = roundsTo cF.blocksInOrder k := by
  obtain rfl := Option.some.inj ((k4Pub_head h Lh).symm.trans hQ)
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.roundsTo_cut
#print axioms ProofFile.Honest.K4.cuts_head
#print axioms ProofFile.Honest.K4.k4Pub_head
#print axioms ProofFile.Honest.K4.front_head
