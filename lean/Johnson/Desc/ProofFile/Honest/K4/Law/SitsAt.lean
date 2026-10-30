-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SitsAt.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THE HYPOTHESES `K4Sits` (Law/Sits.lean), `K4NoMark` (Law/KeepsStep.lean) AND
`K4SitsBack` (Law/Accepted.lean) AT A MEMBER THAT IS K4's LOT's OWN SUB-PROTOCOL, SEATED ALONE AS
THE DESCRIPTION SEATS IT. K4 is the sub-protocol of the feed-forward layers' own rounds. The proofs
are calls of the library's `IM.k4_yes` (Johnson/IMR/K4Seat.lean) and `step_ok_iff`
(Johnson/Desc/Sound/RunIsDecide.lean).

  hb: the member number b of T's flat list is `IM.seatedAs` of K4's lot's sub-protocol at the
      parameters x (`ProofFile.k4Block x`), alone, under some name at K4's place of some group
      (`IM.LaidAlone`, Johnson/IMR/SeatForm.lean).
  `k4Sits_of_laid`, `k4NoMark_of_laid`   under hb: K4Sits at the parameters x.2 with the flag that
      the lookup states its own claims; K4NoMark.
  `k4SitsBack_of_laid`   under hb: `K4SitsBack`: the way back: the library's statement is an
      equivalence.
  `k4_keepsM_of_laid`   **SO K4's CLAUSE OF keeps FROM THE WHOLE MEMBER's ACCEPTING STEP, under hb
      alone.**

Not shown here. THAT A THREAD's MEMBER IS SO SEATED: hb is a hypothesis: an equation on the member.
By reading, the library's `IM.k4_of` and `IM.k4_alone_z` (Johnson/IMR/K4Seat.lean) have that
equation at the third hearing sub-protocol of each of the twelve layers' segments of the full-size
description, under their own hypotheses. Following import lines, and stopping unopened at every
module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose
name begins Cb.Bridge, its imports reach 2 modules under Johnson/Goal/ and 2 under Johnson/Bridge/,
and none of the others; what lies behind these is not counted; 7 of the modules that it reaches have
RecCompile in their names. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.ProofFile.Honest.K4.Law.Accepted
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Bk : ProverCoinCounts} {V W X Pb : Type} {T : Thread Bk First.S Claim V W X Pb} {b : Nat}
  {x : Bool × Par}

/-- **`K4Sits` at a member that is the lot's own sub-protocol, seated alone.** CONDITIONAL: on hb.
-/
theorem k4Sits_of_laid
    (hb : ∀ blk, T.bs[b]? = some blk → ∃ name g,
      IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) :
    K4Sits T b { x.2 with k3Runs := true } := by
  intro blk hblk s rs cols s' n e
  obtain ⟨name, g, h⟩ := hb blk hblk
  exact ⟨_, ((IM.k4_yes h s s' _ _).1 ((step_ok_iff T.ft blk s s' rs cols n).1 e).2.2.2).1⟩

/-- **`K4NoMark` there.** CONDITIONAL: on hb. -/
theorem k4NoMark_of_laid
    (hb : ∀ blk, T.bs[b]? = some blk → ∃ name g,
      IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) : K4NoMark T b := by
  intro blk hblk s rs cols s' n e
  obtain ⟨name, g, h⟩ := hb blk hblk
  exact ((IM.k4_yes h s s' _ _).1 ((step_ok_iff T.ft blk s s' rs cols n).1 e).2.2.2).2.1

/-- **`K4SitsBack` there.** CONDITIONAL: on hb. -/
theorem k4SitsBack_of_laid
    (hb : ∀ blk, T.bs[b]? = some blk → ∃ name g,
      IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) :
    K4SitsBack T b { x.2 with k3Runs := true } := by
  intro blk hblk s rs gs s' h1 h2 h3
  obtain ⟨name, g, h⟩ := hb blk hblk
  exact (IM.k4_yes h s s' rs gs).2 ⟨h1, h2, h3⟩

/-- **K4's CLAUSE OF keeps FROM THE WHOLE MEMBER's ACCEPTING STEP.** CONDITIONAL: on hb alone. -/
theorem k4_keepsM_of_laid
    (hb : ∀ blk, T.bs[b]? = some blk → ∃ name g,
      IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) :
    ∀ blk, T.bs[b]? = some blk → ∀ s s', StepYes T.ft blk s s' → K4KeepsM s s' :=
  k4_keepsM_step (k4Sits_of_laid hb) (k4NoMark_of_laid hb)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Sits_of_laid
#print axioms ProofFile.Honest.K4.k4NoMark_of_laid
#print axioms ProofFile.Honest.K4.k4SitsBack_of_laid
#print axioms ProofFile.Honest.K4.k4_keepsM_of_laid
