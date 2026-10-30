-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerAtFreeHead.lean: k14_at_free WITH ITS PREMISE hR PROVED: P5J.FiveF's
FIELD shared_joint_count AT THE FILLING AT WHICH THE PROOF FILE's TOP IS TAKEN, FROM THREE NAMES.
One theorem.

  k14_at_free_head   the end of k14_at_free (Johnson/Desc/K14/Law/LedgerAtFree.lean), AT THE SECOND
  HASH FUNCTION o := OnBytes.secondHashFunction, from: the head h · hP1 (the one pin) · hn. hR :=
  Sh.reachOwed_closed (Johnson/Desc/K14/Law/SharedConstReachClosed.lean). Each of its premises is a
  field of the head, follows from fields of the head (LPFD.Full.laidPOf_of), is hP1, or is the
  closed fact map14_hx.
On what it rests. The proof calls Cb.Bridge.foldErr_ix (Johnson/Bridge/FoldErrIx.lean), which rests
on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Work is counted in the cap (Johnson/Desc/K14/Law/LedgerAtCap.lean). At "LOC" the share 2⁻¹ ^ 128
holds only with the written round's bits of work (28 at the release's list); "LIN point" and
"LIN zeta" bear none; the two rounds of seeds bear the sendings' own.
What is not claimed. hP1; whether the head can be met (see `AtFullSide.Top.headMember_zFull`). At
another o nothing is said. The other four fields of h.Five. No soundness of a verifier.
Of h the proof uses at most these fields (by a Lean print of the proof's constants; this
file's text reaches h.scope, h.laid.{pub, value, planOk, data, run, asks}, h.𝔇, freeOf and, through
Sh.reachOwed_closed and map14_hx, the rest): scope, reads, pubOne; of «laid»: places, pub, value,
planOk, data, run, asks; of «plan»: shape, laid, named, fit, groups. The five fields of «plan» are
Boolean tests on values computed from the public files; they are not themselves entry tests. None of
these fields is proved in this file: all are assumed with h. The head of
Johnson/Goal/Skeleton/CondsOfLaid.lean lists from what each follows where h is built.

-/
import Johnson.Desc.K14.Law.LedgerAtFree
import Johnson.Desc.K14.Law.SharedConstReachClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open VerifiableInference.OnPublicFiles (kcReq)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (hP1 : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made =
    true) (depthReq : ℕ) (hn : 2 ^ depthReq ≤ 64)
  (ML : VerifiableInference.Desc.Last.MeaningL (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
  (PLm : VerifiableInference.Desc.Last.PromMeaningL (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T
                OnBytes.secondHashFunction Zp Np cF).S₃
    ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁))
  (e₁ : (i : ℕ) → (ds : List RDT) → ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T
                OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁) × (P5J.F0T
                                OnBytes.secondHashFunction Zp Np cF).S₂) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ × (P5J.F0T
                                OnBytes.secondHashFunction Zp Np cF).S₂) ×
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (dW wEnd : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

include hP1 hn in
/-- **The field, from three names.** -/
theorem k14_at_free_head :
    fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq =>
      P5J.FiveF.shared_joint_count V) :=
  k14_at_free h hP1 depthReq hn
    (Sh.reachOwed_closed h.scope
      (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)
      h.laid.value h.laid.pub hP1 map14_hx h.laid.planOk) ML PLm e₁ e₂ e₃ dW wEnd

end

end Desc.K14.Law

#print axioms Desc.K14.Law.k14_at_free_head
