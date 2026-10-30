-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstShape.lean: WHAT THE CONSTANT's PROMISE's BOOK-KEEPING CLAUSE SAYS,
READ OFF THE CLAUSE ALONE. (Sh.pm A O).shape k d is three tests (at 10, 11 and 12 the first is
"true"): the innermost meaning's own, the layouts', and Sh.X A k d
(Johnson/Desc/K14/Law/SharedConst.lean). For whoever has that clause in hand at the shared chain's
last border and no more.

  Sh.shape_twelve the clause at the last border, written out: as terms.
  Sh.X_of_shape   **at border 12 the clause gives Sh.X.**
  Sh.door_of_shape   **at border 12 the clause gives the last chain's door's tests on the shared
                  chain's last state** (doorSharedB at the last chain's parameters A.p).
What is not claimed. No soundness; no level.
-/
import Johnson.Desc.K14.Law.SharedConstStart

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

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- The book-keeping clause at the last border, written out. -/
theorem shape_twelve (d : St) : (pm A O).shape 12 d =
    ((pmZ A.Q.par idleP).shape 12 d && (layX A.Q 12 d && X A 12 d)) := rfl

/-- **At border 12 the clause gives Sh.X.** -/
theorem X_of_shape (d : St) (h : (pm A O).shape 12 d = true) : X A 12 d = true := by
  rw [shape_twelve, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.2.2

/-- **At border 12 the clause gives the last chain's door's tests.** -/
theorem door_of_shape (d : St) (h : (pm A O).shape 12 d = true) :
    VerifiableInference.Desc.Last.doorSharedB A.p d = true := by
  have hX := X_of_shape A O d h
  have hD := ((XW_iff A.Q (sentU A) (layU A) (layO A)
    (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A) (sentU A).size A.p 12 d).1 hX).2
  exact ((XD_iff A.p 12 d).1 hD).2.resolve_left (fun e => e rfl)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.shape_twelve
#print axioms Desc.K14.Law.Sh.X_of_shape
#print axioms Desc.K14.Law.Sh.door_of_shape
