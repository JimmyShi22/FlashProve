-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLast.lean: WHAT Sh.X SAYS OF OMEGA's MESSAGE AT THE SHARED CHAIN's
LAST BORDER, for the last chain's table. From the tests in the promise's slot at border 12
(Johnson/Desc/K14/Law/SharedConst.lean): the message that the chain's state notes as o_omega is
there, has the parameters' shape, and passes the proximity test's own test on a member's OOD sample
(H2K.Pin.sampleL).

  Sh.omega_sampled   **the sentence.** By sharedX_twelve (which number o_omega bears) · omY (the
                  shape) · smpK's second part (the sample).
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstWalk
import Johnson.Desc.K14.Law.LedgerSmpK

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

theorem omega_sampled (hO : 0 < (withOmega A.Q.S).size) (d : St) (h : X A 12 d = true) :
    ∃ x, d.st.oracles[d.loc.oOmega]? = some x ∧ x.shape = A.Q.S.omega ∧
      H2K.Pin.ok (H2K.Pin.sampleL A.Q.codes (seatY A.Q.S.omega d.loc.oOmega) x) = true := by
  have hK := ((XW_iff A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit,
      Y A) (sentU A).size A.p 12 d).1 h).1
  obtain ⟨g1, _, g3, _, _, _, g7⟩ :=
    (XK_iff A.Q (sentU A).size (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A) (sentU A) (layU
        A) (layO A) 12 d).1 hK
  have e := (sharedX_twelve A.Q (sentU A) (layU A) (layO A) d hO g1).2.1
  obtain ⟨x, hx, hs, _, _⟩ := ((omY_iff _ (sentU A).size 12 d).1 g3).resolve_left (by omega)
  obtain ⟨⟨_, kO⟩, _⟩ := (smpK_iff _ _ _ _ _ _ _).1 g7
  obtain ⟨x', hx', hok⟩ := ((smpY_iff _ _ _ _ _ _).1 kO).resolve_left (by omega)
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  rw [e]
  exact ⟨x, hx, hs, hok⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.omega_sampled
