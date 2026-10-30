-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsWithoutPlaceAtMg.lean: the fields k14 and k15 of `KindsLaws`
(Johnson/Goal/Skeleton/SoundOfKindsTop.lean) are free: `P5J.AtMgA.Kind h 𝔏 K`
(Johnson/P5J/RowsAtAll.lean) at K14 and at K15, under every head h and at every filling 𝔏.
`AtMgA.Kind` is `KindTiedR` at the list of places `P5J.At.ps`, which is
`flatPlacesOf fullLinks true` by definition (Johnson/P5J/LettersAt.lean); on that list neither kind
has a place (Johnson/Goal/Skeleton/KindsWithoutPlace.lean: `noPlaceB_K14`, `noPlaceB_K15`, by the
kernel).
Limits. IT PAYS NO LAW: the two fields were empty. K14's and K15's laws are owed elsewhere (the
shared chain's row `shared_joint_count`; the copy's file): nothing here speaks of them.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.KindsWithoutPlace
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Chain KindName)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **K14's field is free.** -/
theorem AtMgA.kind_K14 (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : h.Kind 𝔏 KindName.K14 :=
  fun i _ a _ ha hk =>
    absurd hk (VerifierAndGoals.AtTheName.noPlace_of_B VerifierAndGoals.AtTheName.noPlaceB_K14 i a ha)

/-- **K15's field is free.** -/
theorem AtMgA.kind_K15 (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : h.Kind 𝔏 KindName.K15 :=
  fun i _ a _ ha hk =>
    absurd hk (VerifierAndGoals.AtTheName.noPlace_of_B VerifierAndGoals.AtTheName.noPlaceB_K15 i a ha)

end P5J

#print axioms P5J.AtMgA.kind_K14
#print axioms P5J.AtMgA.kind_K15
