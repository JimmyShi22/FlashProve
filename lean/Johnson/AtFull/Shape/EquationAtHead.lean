-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/EquationAtHead.lean: the sub-protocol without a round "K9: the one equation" of
the proof file's own first chain, at all 25 links: under the head at which the library's laws on
that chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): what the seated member's decision is. A
joining of laws of the library; nothing is evaluated.

  `putFork_failed`, `putFork_out` (both stand in the library too, to the letter:
    Johnson/Desc/K1/Law/SeedAtRecord.lean; out_putFork in Johnson/Desc/First/StateOut.lean),
    `set_keeps`: laying the segment's part back leaves the mark of failure and the field out.
  **`equation_at`**: at l < 25 there are a link L of the chain, a member b of the chain's flat list
    at number 14 l + (the number of L's hearing sub-protocols) + 4, and numbers p (tied to nothing),
    with: b's decision accepts from s to t JUST IF the bare sub-protocol K9.oneEquation atS p
    accepts from s to t and s bears no mark of failure. So the laws of
    Johnson/Desc/First/Batch/Shape/DoorAtS.lean and DoorMember.lean (one_turns, one_core,
    one_accepts) speak of the seated member.

By IM.close_of (Johnson/IMR/CloseSeat.lean), IM.close_numbers (Johnson/IMR/FirstSeats.lean) and
IM.yes_alone (Johnson/IMR/SeatForm.lean).

Limits. NO STEP ON THE SHAPE IS GIVEN HERE: see DoorMember.lean's limits. p stands under "there is"
and is tied to nothing; oneEquation lays it into the block's place alone. UNDER THE HEAD: that it
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorMember
import Johnson.AtFull.Shape.ShutAtHead
import Johnson.IMR.FirstSeats
import Johnson.IMR.CloseSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where atS oneEquation)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem putFork_failed (s : S) (F : Fork) : (s.putFork F).failed = s.failed := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem putFork_out (s : S) (F : Fork) : (s.putFork F).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem set_keeps (s : S) (Q : VerifiableInference.Desc.K9.Part) :
    (atS.set s Q).failed = s.failed ∧ (atS.set s Q).out = s.out :=
  ⟨(putFork_failed (s.putLink Q.L) Q.F).trans (putLink_failed s Q.L),
    (putFork_out (s.putLink Q.L) Q.F).trans (putLink_out s Q.L)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem equation_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl) (p : Where), cF.links[l]? = some L ∧
      cF.blocksInOrder[14 * l + L.hear.length + 4 + 0]? = some b ∧
      ∀ s t rs gs, b.decide s rs gs = .ok t ↔
        (oneEquation (Cl := Unit) atS p).decide s rs gs = .ok t ∧ s.failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, p, Q, eL, -, -, hall⟩ := IM.close_of h.scope h.reads O l hl
  obtain ⟨b, y, e1, e2, la⟩ := hall 0 .K9 rfl
  obtain rfl : ({ oneEquation atS p with planOk := VerifiableInference.Desc.K9.fits p Q } :
      Block S Unit) = y := Option.some.inj e2
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨L, b, p, eL, IM.close_numbers h.scope h.reads O hl eL e1, fun s t rs gs => ?_⟩
  rw [hy s t rs gs]
  show ((oneEquation (Cl := Unit) atS p).decide s rs gs = .ok t ∧ t.failed = none ∧
    ProofFile.sameReply s t = true) ↔ _
  constructor
  · rintro ⟨h1, h2, -⟩
    obtain ⟨P, o, -, -, rfl⟩ := (one_iff p s t rs gs).1 h1
    exact ⟨h1, (set_keeps s _).1.symm.trans h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨P, o, -, -, rfl⟩ := (one_iff p s t rs gs).1 h1
    refine ⟨h1, (set_keeps s _).1.trans h2, ?_⟩
    unfold ProofFile.sameReply
    rw [(set_keeps s _).2]
    exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.equation_at
#print axioms Johnson.AtFull.Shape.putFork_failed
#print axioms Johnson.AtFull.Shape.putFork_out
#print axioms Johnson.AtFull.Shape.set_keeps
