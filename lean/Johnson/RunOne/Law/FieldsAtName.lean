-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldsAtName.lean: THE
FIELDS r1_4 AND r1_10 AT THE VERY TERMS AT WHICH THE JOINING TERM ASKS THEM
(LPFD.The21AtName, Johnson/Top/Fire/Code/KeyAtName.lean): the reading baseAt X decN recBack, the
seats atSix, the reader readAt tab, the event collN, the rests capRest, the witnesses' type Unit,
the data DK.at frS.P.T.a. There FIVE of the six premises of r1_4_free and r1_10_free
(FieldsFree.lean) on letters of other files fall by calls: the cap (capRest's own definition) ·
CellOnly (cellOnly_collN) · SmReads (the filling's smReadsK) · R.same (kreadFam's own definition) ·
a witness (exhibited); and the premise on the pinned trees is taken in the form of The21AtName's own
fourth conjunct.

Main names:
  r1_4_at_name, r1_10_at_name: the two fields of The21 at these terms.
  terms_fit: a witness for the forms: The21AtName, taken apart, has the very types of hb₁ and of the
    two conclusions.

Object: the fields r1_4 and r1_10 of LPFD.The21 at The21AtName's terms.
User: r1_4_in_scope, r1_10_in_scope (FieldsAtNameScope.lean).
Letters: X, N, P, DK, tab; the frame's heads and tails.
PREMISE LEFT ON THE FRAME, ONE: the first chain's bases: The21AtName's own fourth conjunct
(hb₁).
Premises that The21AtName binds itself: q₁, q₂, q₃ · two lookups.
Premises that are theorems in scope: planOk · the data · RoomFor · the own message counts an answer
· target = 128 · LookHeld.

Limits. Two fields of twenty-one. Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldsFree
import Johnson.Top.Fire.Code.KeyAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldsAtName
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where pinned)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly smReadsK atSix)
open Johnson.RunOne.KeyRows1 (open₁)
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.FieldsFree
open LPFD (On₁' KeepsAt baseAt readAt decN recBack collN cellOnly_collN capRest MsgN)

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (DK : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))

/-- **THE FIELD r1_4 AT The21AtName's TERMS.** -/
theorem r1_4_at_name (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok (DK.at frS.P.T.a)) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))))
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 4 :=
  r1_4_free X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN c₁ k₁ c₂ k₂ c₃
      k₃
    capRest capRest capRest () () hp file hD q₁ q₂ q₃ hR ha hn ht hL (fun _ _ => rfl)
    (fun n p h2 h14 hx j hj => hb₁ n p hx j (by rw [pinned_link n h2 h14]; exact hj))
    cellOnly_collN (smReadsK _ _ _ _ _ _ _) rfl ⟨(⟨fun _ => 0, (), fun _ _ _ => 0, fun _ _ _ _ =>
        0⟩, ())⟩

/-- **THE FIELD r1_10 AT The21AtName's TERMS.** -/
theorem r1_10_at_name (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok (DK.at frS.P.T.a)) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))))
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 10 :=
  r1_10_free X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN c₁ k₁ c₂ k₂ c₃
      k₃
    capRest capRest capRest () () hp file hD q₁ q₂ q₃ hR ha hn ht hL (fun _ _ => rfl)
    (fun n p h2 h14 hx j hj => hb₁ n p hx j (by rw [pinned_link n h2 h14]; exact hj))
    cellOnly_collN (smReadsK _ _ _ _ _ _ _) rfl ⟨(⟨fun _ => 0, (), fun _ _ _ => 0, fun _ _ _ _ =>
        0⟩, ())⟩

open VerifiableInference.Desc.Key in
/-- **A WITNESS FOR THE FORMS**: what The21AtName holds, taken apart, HAS the very types of the
premise hb₁ and of the two conclusions above: Lean's own check that these are its fourth conjunct
    and
its fields r1_4 and r1_10. It proves nothing else. -/
theorem terms_fit {Xr : Type} (A : LPFD.DN.Claims Xr) (E : OnBytes.Flat.Coding A)
    (h : LPFD.The21AtName A E X N P DK) (x₀ x₁ : VerifiableInference.Desc.Key.Lookup)
    (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hl : VerifiableInference.Desc.Key.lookupsOf X.Y.k.oneTime = [x₀, x₁])
    (hw : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hin : (Johnson.RunOne.KeyRows23.inFront₂ X P).length = 10) :
    ∃ tab : MsgN → ℕ → ℕ → OnBytes.F,
      (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃
          k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
              P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some
                  p → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) ∧
      KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
        (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
            capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
                (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 4 ∧
      KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
        (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
            capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
                (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 10 := by
  obtain ⟨tab, enc, rad, off₂, off₃, dS, H, off, hh, hb₁, -⟩ :=
    h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  exact ⟨tab, hb₁, H.r1_4, H.r1_10⟩

end Johnson.RunOne.Law.FieldsAtName

#print axioms Johnson.RunOne.Law.FieldsAtName.r1_4_at_name
#print axioms Johnson.RunOne.Law.FieldsAtName.r1_10_at_name
#print axioms Johnson.RunOne.Law.FieldsAtName.terms_fit
