-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ShutAtHead.lean: the sub-protocol without a round "K9: the segment is shut" of
the proof file's own first chain, at all 25 links: under the head at which the library's laws on
that chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): one step on the shape of the chain's state,
with the laws "carries" and "returns". A joining of laws of the library; nothing is evaluated.

  `shutGS`: the step at the seat: no mark of failure; then shutG
    (Johnson/Desc/First/Batch/Shape/ShutChain.lean).
  `putLink_failed`, `putLink_out`: laying a link's context leaves the mark of failure and the field
    out. (Both stand in the library too: Johnson/Desc/K1/Law/SeedAtRecord.lean; out_putLink in
    Johnson/Desc/First/StateOut.lean.)
  **`shut_at`**: at l < 25 there are a link L of the chain and a member b of the chain's flat list,
    at number 14 l + (the number of L's hearing sub-protocols) + 6: b's decision carries shutGS, and
    accepts wherever shutGS returns at the state's shape. NO TEST ON VALUES.

By IM.close_of (Johnson/IMR/CloseSeat.lean), IM.close_numbers (Johnson/IMR/FirstSeats.lean) and
IM.yes_alone (Johnson/IMR/SeatForm.lean).

Limits. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. "Carries" is under the step's own return. The
number hangs on L (Numbers.lean: 14 l + 13; 351 at l = 24). That b has no round is not said. That
shutGS returns at a shape that the chain reaches is not shown. At the earlier hash OnBytes.secondHashFunction.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.ShutChain
import Johnson.IMR.FirstSeats
import Johnson.IMR.CloseSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step at the seat.** -/
def shutGS (a : ChainSh) : Except String ChainSh :=
  if a.marked then .error "a mark of failure" else shutG a

theorem putLink_failed (s : S) (L : LinkCtx) : (s.putLink L).failed = s.failed := by
  unfold S.putLink
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem putLink_out (s : S) (L : LinkCtx) : (s.putLink L).out = s.out := by
  unfold S.putLink
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem shut_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), cF.links[l]? = some L ∧
      cF.blocksInOrder[14 * l + L.hear.length + 4 + 2]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t → shutGS (chainSh s) = .ok u → u = chainSh t) ∧
      ∀ s rs gs u, shutGS (chainSh s) = .ok u → ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, p, Q, eL, -, -, hall⟩ := IM.close_of h.scope h.reads O l hl
  obtain ⟨b, y, e1, e2, la⟩ := hall 2 .K9 rfl
  obtain rfl : VerifiableInference.Desc.K9.shut p (Q.piece + 1) = y := Option.some.inj e2
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨L, b, eL, IM.close_numbers h.scope h.reads O hl eL e1,
    fun s rs gs t u hd hg => ?_, fun s rs gs u hg => ?_⟩
  · have hd' : (VerifiableInference.Desc.K9.shut (Cl := Unit) p (Q.piece + 1)).decide s rs gs =
        .ok t := ((hy s t rs gs).1 hd).1
    unfold shutGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      exact shut_carries p (Q.piece + 1) s t rs gs u hd' hg
  · unfold shutGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      obtain ⟨t, ht⟩ := shut_returns (Cl := Unit) p (Q.piece + 1) s rs gs u hg
      obtain ⟨C, -, rfl⟩ := (shut_iff p (Q.piece + 1) s t rs gs).1 ht
      have hf : s.failed = none := by
        have : s.failed.isSome = false := hm
        simpa using this
      refine ⟨_, (hy s _ rs gs).2 ⟨ht, (putLink_failed s _).trans hf, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [putLink_out]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.shut_at
#print axioms Johnson.AtFull.Shape.shutGS
#print axioms Johnson.AtFull.Shape.putLink_failed
#print axioms Johnson.AtFull.Shape.putLink_out
