-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Law/SeatAtHead.lean: CONDITIONAL: UNDER THE LIBRARY's HYPOTHESIS ON THE
PUBLIC INPUT THE MEMBER NUMBER 354 OF THE FIRST CHAIN's FLAT LIST IS THE PROXIMITY TEST's ENTRY AT
THE CHAIN's FINISH (kind K12): it sits over the test, and two tests on the test's own numbers
accept. On the verifier's own text; no prover in it. IT IMPORTS A FILE OF THE LIBRARY ALONE. One
statement with its proof; no definition.

Why. The library has these facts on the way to its game at that number (`H2K12.game_at_354`,
Johnson/Loose/H2K12/TieAt354.lean), but that theorem's end does not say where in the flat list the
entry stands. A law at a member's step wants the member itself.

How. The calls of `game_at_354`'s proof, at the hypothesis's own fields as
Johnson/Loose/H2K12/K12LeftOfRest.lean lays them: `k12_sits` (SitsAtDescPure.lean) cuts the flat
list at the entry; `pre_length_354` counts what stands in front, from a closed fact on the written
list of places that the kernel decides (`k12AllB_full`, Johnson/Loose/H2K12/K12LawR.lean);
`firstJ_sitsCore` (FirstSeatForm.lean) has "sits"; `public_at_seat_L` (ChainAtLast.lean) has the
tests on the plan; `lastTypedAt_at_head` (K12AtFree.lean) pays its premise on the typed stages.

Main name:
  `seat_354`   **there is a J: the member number 354 is `firstEntry ProofFile.sameReply J`; it sits over
      `proximityTestKind guardedProximityTestParts (pL Np)` with the way out `outCore ProofFile.sameReply`; that test's `planOk` accepts;
      it has no mask of its own**

CONDITIONAL on the hypothesis h on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean).
ON h. It can be met: at the full-size public files as Ladder/Stored.lean spells them it has a member
with no premise (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). This file does not call
it. These files are tied to the package's files by no theorem.

Limits. At the library's full size and at the format's second hash function alone: h is typed there. Through
its import the file stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under
ThirdParty/ (Johnson/Loose/H2K12/K12AtHead.lean's own limit). What lies deeper beneath the calls was
not walked. The file sets `maxRecDepth` to 100000.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.K12AtFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace H2K12.AtStep

open OnBytes OnBytes.Maker
open VerifiableInference.Desc (KindName Block)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The member number 354 of the first chain's flat list is the proximity test's entry at the
chain's finish: it sits, and the test's own test on the plan accepts.** After `H2K12.game_at_354`.
CONDITIONAL: the hypothesis h. -/
theorem seat_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ J, cF.blocksInOrder[354]? = some (H2K.JointK.firstEntry ProofFile.sameReply J) ∧
      H2K.JointK.Sits (H2K.JointK.firstEntry ProofFile.sameReply J)
        (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2K.JointK.pL Np) :
          H2K.JointK.Blk') VerifiableInference.Desc.K12.enterFinish
        (H2K.JointK.outCore ProofFile.sameReply) ∧
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2K.JointK.pL Np) :
        H2K.JointK.Blk').planOk = true ∧
      (H2K.JointK.pL Np).nums.ownMask = false := by
  have hT := lastTypedAt_at_head h
  obtain ⟨Z', N', c', _, hZ', hN', e, _, pre, l, J, hb, _, hJ⟩ :=
    H2K.JointK.k12_sits OnBytes.secondHashFunction Z.pol Z.lay Z.KL _ h.laid.value
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  obtain rfl : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  obtain rfl : c' = cF := (first_inj e).symm
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  have hLs := hT _ h.laid.pub
  obtain ⟨hW, _, _⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
    (LPFD.asks_written h.laid.asks)
  have hX : (H2K.JointK.firstEntry ProofFile.sameReply J).place.kind = KindName.K12 := rfl
  have h354 : pre.length = 354 := pre_length_354 hb hX (places_at_mg h.toAtMg) k12AllB_full
  have hPub := H2K.JointK.public_at_seat_L OnBytes.secondHashFunction Z.pol Z.lay Z.KL _ h.laid.pub _ _ _
    h.laid.places h.laid.planOk A hLs hW ProofFile.sameReply pre l J hb hJ
  obtain ⟨_, C, _, ho, _, _, _⟩ := hPub
  refine ⟨J, ?_, H2K.JointK.firstJ_sitsCore ProofFile.sameReply _ J hJ, C.plan, ho⟩
  rw [hb, List.getElem?_append_right (Nat.le_of_eq h354), h354, Nat.sub_self]
  rfl

end H2K12.AtStep

#print axioms H2K12.AtStep.seat_354
