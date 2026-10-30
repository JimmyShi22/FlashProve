-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldsFree.lean:
THE FIELDS r1_4 AND r1_10 WITHOUT
TWO OF THEIR PREMISES: "a value of the riding type": Keeps speaks of every statement a, and a
statement holds such a value · "no two trees of the frame have one number": the frame's list of
trees is made by their numbers (allOf, Johnson/Desc/Sound/Tiles.lean): a theorem at every D.

Main names:
  frame_nodup: no two trees of the frame have one number.
  r1_4_free, r1_10_free: the fields' statements, under SIX premises on the table's letters and the
    frame: the cap · the two pinned trees below the pieces' places · CellOnly coll · B.SmReads ·
    R.same is "read alike" · a witness; besides q₁, q₂, q₃ and the seven that are theorems in scope.

Object: the fields r1_4 and r1_10 of LPFD.The21 (Johnson/Top/Fire/Code/The35.lean), at any D.
User: r1_4_at_name, r1_10_at_name (FieldsAtName.lean); r1_5, r1_11 (FieldsLayer.lean).
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests.

Limits. IMPLICATIONS: that the premises on the table's letters and the frame can hold together is
shown by
nobody.
(Where this
and lean/THEOREM.md differ, the page holds.)
Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldR110

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldsFree
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.FieldR14X
open Johnson.RunOne.Law.FieldR110
open LPFD (On₁' KeepsAt)

variable {W Cells Mm Smp Rec : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD) (B : BaseSt Cells Mm Smp Rec)
  (at_ : Where) (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

omit W in
/-- **No two trees of the frame have one number**: the frame's trees are made by their numbers. -/
theorem frame_nodup (D : WholeD) : ((fr₁ D).all.map (·.no)).Nodup := by
  show ((VerifiableInference.Desc.Sound.allOf D).map (·.no)).Nodup
  unfold VerifiableInference.Desc.Sound.allOf
  rw [List.map_map]
  have e : (List.range (nAll D)).map ((fun x : LeftT => x.no) ∘ fun j => ⟨j, (D.depth j).getD 0⟩) =
      List.range (nAll D) := by
    rw [show ((fun x : LeftT => x.no) ∘ fun j => (⟨j, (D.depth j).getD 0⟩ : LeftT)) = id from rfl]
    exact List.map_id _
  rw [e]
  exact List.nodup_range

/-- **THE FIELD r1_4**, the value of the riding type taken off the statement in hand. -/
theorem r1_4_free (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok D) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))))
    (hcap : ∀ n ds, (rest₁ n ds).err = Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hbase : ∀ n p, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
        k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some p → ∀ j ∈ [0, 1], (at_ j).1 < p.base)
    (hcell : CellOnly coll) (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hw : Nonempty (Wit Cells Unit Mm × Unit)) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 4 :=
  fun p hq a hon => r1_4 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp file hD
    q₁ q₂ q₃ hR ha hn ht hL (frame_nodup D) hcap hbase hcell hS hsame (stK a.1.1 0 a.1.2) hw p hq a
        hon

/-- **THE FIELD r1_10**, likewise. -/
theorem r1_10_free (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok D) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))))
    (hcap : ∀ n ds, (rest₁ n ds).err = Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hbase : ∀ n p, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
        k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some p → ∀ j ∈ [0, 1], (at_ j).1 < p.base)
    (hcell : CellOnly coll) (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hw : Nonempty (Wit Cells Unit Mm × Unit)) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 10 :=
  fun p hq a hon => r1_10 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp file
    hD q₁ q₂ q₃ hR ha hn ht hL (frame_nodup D) hcap hbase hcell hS hsame (stK a.1.1 0 a.1.2) hw p hq
        a hon

end Johnson.RunOne.Law.FieldsFree

#print axioms Johnson.RunOne.Law.FieldsFree.frame_nodup
#print axioms Johnson.RunOne.Law.FieldsFree.r1_4_free
#print axioms Johnson.RunOne.Law.FieldsFree.r1_10_free
