-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstHeldAt.lean: THE SHARED TABLE's CONSTANT AT A PROOF FILE's SEAT: THE
CELLS' THREE OPEN LETTERS (c₀, matC, held: arguments of Sh.openAt₀,
Johnson/Desc/K14/Law/SharedConstOpenAt.lean) AT THE RELEASE's CONFIGURATION's OWN TERMS
(heldFull, matN: Johnson/Desc/Sound/DataAlong.lean, HeldAlong.lean, PlanAsk.lean).

  Sh.hfs_at            the test under which held is typed (fullShapeB) accepts at the seat, from
                       Written Z x (full_real, Johnson/Desc/K14/Law/SharedConstFull.lean)
  Sh.openAt …          ShOpen at the seat, seven of its thirteen letters closed: Cells := the
                       configuration's own cells · c₀ := the zero table · matC := matN … numsFull ·
                       held := heldFull … TWO LETTERS OF THE CONFIGURATION COME WITH THEM: pp and E.
  Sh.hH_at             the ledger's top's hH at the seat (heldTie_asked)
WHAT IS NOT HERE. No law. The first table's constant's six (Sh.Open₁).
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Desc.K14.Law.SharedConstFull

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
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)

namespace Sh

variable {Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)

/-- **The test under which held is typed accepts at the seat.** -/
theorem hfs_at {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x) :
    fullShapeB (planAt Z N (seatF o Z N B' cF)).Q.par.S = true := by
  obtain ⟨x', a1, hf⟩ := full_real
  obtain rfl := sized_one hx a1
  show fullShapeB Z.p.chains.made.sized.proof.batch.shape = true
  rw [h.shape]
  exact hf

variable (hfs : fullShapeB (planAt Z N (seatF o Z N B' cF)).Q.par.S = true) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
  (O₁ : Open₁ (kcReq numsFull pp E).conf.I Tok (planAt Z N (seatF o Z N B' cF)).Q)

/-- **The open letters at the seat.** -/
def openAt : ShOpen ProofFile.InstPub (ProofFile.InstPub × First.S) (kcReq numsFull pp E).conf.I Tok
    (planAt Z N (seatF o Z N B' cF)).Q :=
  openAt₀ o Z N B' cF (fun _ _ => 0) (matN (frS.toDecR frZ 402653181) numsFull)
    (heldFull (planAt Z N (seatF o Z N B' cF)).Q.par 0
      (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.saltBytes
      (full_index (planAt Z N (seatF o Z N B' cF)).Q.par.S hfs) numsFull pp E) O₁

/-- **The top's hH at the seat.** -/
theorem hH_at : HeldTie (planAt Z N (seatF o Z N B' cF)).Q.par 0 2852142980
    (rank (planAt Z N (seatF o Z N B' cF))) (openAt o Z N B' cF hfs pp E O₁).held
    (openAt o Z N B' cF hfs pp E O₁).matC :=
  heldTie_asked (planAt Z N (seatF o Z N B' cF)).Q.par 0 hfs pp E

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hfs_at
#print axioms Desc.K14.Law.Sh.hH_at
