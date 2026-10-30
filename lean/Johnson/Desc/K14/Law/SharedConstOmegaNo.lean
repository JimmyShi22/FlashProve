-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstOmegaNo.lean: WHICH NUMBER o_omega BEARS, at the shared table's
constant: two small lemmas for the joint with the last chain. The tests in the promise's slot at the
last border say that the state's own note of o_omega's number is the number of messages that "send
o_u" sends; and the constant's numbering of its members gives that same number to the member that
sits at Omega's tenant.

  Sh.omega_number **inside Sh.X at border 12: d.loc.oOmega = (sentU A).size** (by sharedX_twelve).
  Sh.oNo_omega    **a member of the constant's that sits at Omega's tenant bears that number**
                  (msSh_is; the three tenants are three: tenants_apart).
  Sh.omega_number_of, Sh.oNo_omega_of   the same under the constant's named tests (Sh.Tests A)
                  alone.
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstLast
import Johnson.Desc.K14.Law.SharedConstTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

variable {Xi : Type} (A : ShPlan Xi)

/-- **Inside Sh.X at border 12: the number that o_omega bears.** -/
theorem omega_number (hO : 0 < (withOmega A.Q.S).size) (d : St) (h : X A 12 d = true) :
    d.loc.oOmega = (sentU A).size := by
  have hK := ((XW_iff A.Q (sentU A) (layU A) (layO A)
    (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A) (sentU A).size A.p 12 d).1 h).1
  have g1 := ((XK_iff A.Q (sentU A).size (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
    (sentU A) (layU A) (layO A) 12 d).1 hK).1
  exact (sharedX_twelve A.Q (sentU A) (layU A) (layO A) d hO g1).2.1

/-- **A member that sits at Omega's tenant bears that number.** -/
theorem oNo_omega (hlU : layTrees A.Q.codes (sentU A) = some (layU A))
    (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A)) (hU : 0 < (sentU A).size)
    (hO : 1 < (withOmega A.Q.S).size) (x : Mem) (hx : x ∈ ms A)
    (hs : x.1.seat x.2 = tenantSh (t₁ A) (layU A) (layO A) .oOmega) :
    oNo A x = (sentU A).size := by
  obtain ⟨m, e1, e2⟩ := msSh_is A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (t₁ A) (sentU A).size
    (layU A) (layO A) x hx
  obtain rfl : m = .oOmega := tenants_apart A.Q.codes (sentU A) (withOmega A.Q.S) (layU A) (layO A)
    hlU hlO hU hO (t₁ A) m .oOmega (e1.symm.trans hs)
  exact e2

/-- The first under the constant's named tests. -/
theorem omega_number_of (hT : Tests A) (d : St) (h : X A 12 d = true) :
    d.loc.oOmega = (sentU A).size :=
  omega_number A (by rw [tests_hsO A hT]; decide) d h

/-- The second under the constant's named tests. -/
theorem oNo_omega_of (hT : Tests A) (x : Mem) (hx : x ∈ ms A)
    (hs : x.1.seat x.2 = tenantSh (t₁ A) (layU A) (layO A) .oOmega) :
    oNo A x = (sentU A).size :=
  oNo_omega A (tests_hlU A hT) (tests_hlO A hT) (by rw [tests_hsU A hT]; decide)
    (by rw [tests_hsO A hT]; decide) x hx hs

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.omega_number
#print axioms Desc.K14.Law.Sh.oNo_omega
#print axioms Desc.K14.Law.Sh.omega_number_of
#print axioms Desc.K14.Law.Sh.oNo_omega_of
