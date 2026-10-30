-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstEv.lean: AT THE SHARED TABLE's CONSTANT
(Johnson/Desc/K14/Law/SharedConst.lean) THE LEDGER's TOP's TWO PREMISES ev9 AND ev10 (EvKept,
Johnson/Desc/K14/Law/LedgerRidesApart.lean: inside the promise at border k the slot's own sentence
on the evaluation is kept by sub-protocol k's extractor) ARE ONE CALL of evKept_of
(Johnson/Desc/Sound/EvalKept.lean), at every border k, from the fold facts of
Johnson/Desc/K14/Law/SharedConstFold.lean.

  Sh.evKeptP   FoldFacts A O → EvKept … at Sh.nums, Sh.mg, Sh.own, Sh.ex, AT EVERY PROMISE's MEANING
               Pm (the ledger's top's own spelling of the promise among them), at every k
  Sh.evKept    the same at Sh.pm
WHAT IS NOT HERE. No law. The fold facts.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstFold
import Johnson.Desc.K14.Law.SharedConstJoint
import Johnson.Desc.Sound.EvalKept
import Johnson.Desc.K14.Law.LedgerRidesApart

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


namespace Sh

variable {Xi P₀ P₁ Cl Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)
  {Fr : Frame}

/-- **The top's ev9 and ev10, at the constant's letters, at every promise's meaning and border.** -/
theorem evKeptP (Pm : PromMeaning St)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (J : Joint A O) (F : FoldFacts A O) :
    EvKept (nums A O) (mg A O) Pm (own A O) true f l (ex A O Fr) k :=
  evKept_of A.Q.codes A.G O.arr (smp₂ A) (ms A) (decT₂ A O) O.c₀ (nums A O) (mg A O) Pm
    (own A O) true f l k O.get O.Pw stOf₁ (tabP₁ A O) (fun p y w => by
      show O.Mg₁.wrow (O.get p) y w ↔ _
      rw [J.wrow]) (fun _ h => h)
    (hcod_own A O F) (hsz_own A O F) (hbook_own A O F)
    (fun q y ho hm n j t hp m _ => hfar_own A O F q y ho hm n j t hp m)

/-- The same at the constant's promise. -/
theorem evKept (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (J : Joint A O) (F : FoldFacts A O) :
    EvKept (nums A O) (mg A O) (pm A O) (own A O) true f l (ex A O Fr) k :=
  evKeptP A O (pm A O) f l k J F

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.evKeptP
#print axioms Desc.K14.Law.Sh.evKept
