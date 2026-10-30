-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstWalk.lean: THE WALK OF THE TESTS IN THE PROMISE's SLOT, AT THE
SHARED TABLE's CONSTANT (Johnson/Desc/K14/Law/SharedConst.lean). Sh.X is XK with the door, at the
plan's three shapes and Y := smpK. The ledger's theorems on its walk (LedgerNineTen, LedgerDoor,
LedgerSmpPaid) are stated at the shapes as K1 reads them off the two sendings; HERE they are brought
to the constant's own letters.

  Sh.shapes_are, Sh.X_is   the three shapes as K1 reads them ARE the plan's; so Sh.X is the ledger's
                  XW at those terms.
  Sh.X_first, Sh.X_front, Sh.X_point   at the chain's first state by make · over the front · over
                  "LIN point" at the piece.
  Sh.X_hands      HandsAt for Sh.X inside the constant's promise: what share_seamed asks as hX.
WHAT STAYS. The facts on the parameters, as premises in the form in which Sh.Tests gives them.
What is not claimed. No soundness; no level. NO MEMBER OF THE PROMISE IS SHOWN.

-/
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.K14.Law.LedgerSmpPaid
import Johnson.Desc.K14.Law.PlanShapes

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

variable {Xi P₀ P₁ Cl Cells Tok : Type} {Fr : Frame} (A : ShPlan Xi)
  (O : ShOpen P₀ P₁ Cells Tok A.Q)
  (hUw : withU A.Q.S = some (sentU A)) (hS : A.Q.S.sharedSplitNeeded = true)

/-- **The three shapes as K1 reads them off the two sendings are the plan's.** -/
theorem shapes_are : shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩ = A.Q.S.fold.u ∧
    shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩ = A.Q.S.omega ∧
    shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩ = A.Q.S.sharedSplit :=
  ⟨shapeAtU A.Q (sentU A) hUw _, shape_omega A.Q _, shape_split A.Q hS _⟩

/-- So Sh.X is the ledger's XW at those terms. -/
theorem X_is : (XW A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
    (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
    (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
    (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
    (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size A.p) = X A := by
  obtain ⟨e1, e2, e3⟩ := shapes_are A hUw hS
  rw [e1, e2, e3]
  rfl

theorem X_first (key : TableKey) : X A 0 (first A.Q.codes key) = true :=
  XW_first A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
      (sentU A).size A.p key
    (smpK_first_paid A.Q A.Q.S.fold.u A.Q.S.omega A.Q.S.sharedSplit (sentU A) key)

theorem X_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hx : X A 0 d = true) : X A 1 d' = true :=
  XW_front A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
      (sentU A).size A.p c d d' rs gs h
    (smpK_front_paid A.Q A.Q.S.fold.u A.Q.S.omega A.Q.S.sharedSplit (sentU A)) hx

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks A.Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (hlU : layTrees A.Q.codes (sentU A) = some (layU A))
  (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A))
  (hm : A.Q.par.S.masksAhead = true)
  (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)

include hUw hS hbl hlU hlO hm hp

theorem X_point (c1 : Block St Cl) (hc : DecidesAs c1 b1) (hr : c1.rounds = b1.rounds)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c1) (a : (P₁ × St)
        × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (h : X A 1 a.1.2 = true) : X A 2 y.1.2 = true :=
  XW_point A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
      (sentU A).size A.p b1 b2 b3 b4 b5 b6 b7 b8 hbl hUw hlU hlO hS hm hp
      c1
    hc hr x hx a τ y hout (smpK_two_paid A.Q A.Q.S.fold.u A.Q.S.omega A.Q.S.sharedSplit (sentU A)
        y.1.2)
        h

/-- **HandsAt for Sh.X.** -/
theorem X_hands (on : ℕ → (P₁ × St) × Fr.E.Str → Prop) (hok : A.Q.S.ok = true)
    (hC2 : condPort (parU A.Q (sentU A)) A.rad2 = true) (hC5 : condPort (parO A.Q) A.rad5 = true)
    (pyU : PlanY A.Q.codes A.Q.S.fold.u) (pyO : PlanY A.Q.codes A.Q.S.omega)
    (pyS : PlanY A.Q.codes A.Q.S.sharedSplit) (hpS : A.p.S.omega = A.Q.S.omega)
    (hon : ∀ k a, on k a → X A k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8] (X A) := by
  obtain ⟨e1, e2, e3⟩ := shapes_are A hUw hS
  have hXi := X_is A hUw hS
  have hsm := sampled A.Q (sentU A) hok
  rw [← hXi] at hon ⊢
  refine handsAt_XW A.Q (sentU A) (layU A) (layO A) A.p b1 b2 b3 b4 b5 b6 b7 b8 hbl hUw hlU hlO hS
      hm hp
    on _ (hsm.1 hUw _) _ (hsm.2.1 _) _ (hsm.2.2 _) (by rw [e2]; exact hpS) (by rw [e2]; exact pyO.1)
    (by rw [sizeOmega A.Q.S hS]; decide) _ ?_ hon
  exact smpK_hands_paid A.Q (sentU A) (layU A) (layO A) b1 b2 b3 b4 b5 b6 b7 b8 hbl hUw
    (hp b2 (by simp)) (hp b5 (by simp)) on _ (hsm.1 hUw _) _ (hsm.2.1 _) _ (hsm.2.2 _) A.rad2 A.rad5
    hC2 hC5 (by rw [e1]; exact pyU) (by rw [e2]; exact pyO) (by rw [e3]; exact pyS)
    fun k a ha => ((XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p k _).1 (hon k a ha)).1

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.shapes_are
#print axioms Desc.K14.Law.Sh.X_is
#print axioms Desc.K14.Law.Sh.X_first
#print axioms Desc.K14.Law.Sh.X_front
#print axioms Desc.K14.Law.Sh.X_point
#print axioms Desc.K14.Law.Sh.X_hands
