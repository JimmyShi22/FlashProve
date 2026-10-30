-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldR14X.lean:
the table's bitVec IS bitVecL
(TiePlanes.lean). So the ninth premise of r1_4_whole (FieldR14W.lean), on the bits,
is a theorem, and THE FIELD r1_4 STANDS UNDER EIGHT PREMISES ON THE TABLE'S LETTERS AND THE FRAME.

Main names:
  bitVec_is: the table's bitVec is bitVecL (TiePlanes.lean): by rfl.
  read_bitVec: read, the table's bitVec is the library's Planes.bitsOf: NO PREMISE.
  r1_4: the field's statement.

Object: the field r1_4 of LPFD.The21 (Johnson/Top/Fire/Code/The35.lean), at any D.
User: r1_4_free (FieldsFree.lean).
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests.
PREMISES ON THE TABLE'S LETTERS AND THE FRAME, PAID BY NOBODY HERE: no two trees of the frame have
one number · the first chain's rests have the cap at 128 as their errors · the two pinned trees lie
below the place of every piece from the third to the fifteenth · coll reads the stored table's
cells alone · B.SmReads · R.same is "read alike" · a witness · a value of the riding type.
Premises on the frame's letters besides: the description's three flat lists of blocks are the
frame's heads and tails: c₁ :: k₁, c₂ :: k₂, c₃ :: k₃ (q₁, q₂, q₃).
Premises that are theorems in scope: planOk · the data · RoomFor · the own message counts an answer
· two lookups · target = 128 · LookHeld.

Limits. AN IMPLICATION: THE FIELD IS PAID ONLY UNDER THESE PREMISES, AND THAT THOSE ON
THE TABLE'S LETTERS AND THE FRAME CAN HOLD TOGETHER IS SHOWN BY NOBODY:
no B, at_, R, coll and rests are exhibited.
(Where this
and lean/THEOREM.md differ, the page holds.)
The first
lookup's block alone. Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldR14W

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldR14X
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.TiePlanes
open Johnson.RunOne.Law.FieldR14W
open LPFD (On₁' KeepsAt)

/-- The table's bitVec is bitVecL (TiePlanes.lean). -/
theorem bitVec_is : @VerifiableInference.Desc.Key.bitVec = @bitVecL := rfl

/-- **Read, the table's bitVec is the library's reading of the bit.** -/
theorem read_bitVec (x : WfPublic) (codes : Codes) (l : ℕ) (valB : ℕ → E) (i : ℕ) :
    readE (VerifiableInference.Desc.Key.bitVec x codes l valB i) =
      Planes.bitsOf x codes l (fun k => readE (valB k)) (i / 2 ^ (x.lookups.getD l default).mu)
        (i % 2 ^ (x.lookups.getD l default).mu) := by
  rw [bitVec_is]
  exact read_bitVecL x codes l valB i

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

/-- **THE FIELD r1_4.** -/
theorem r1_4 (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok D) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))))
    (hnd : ((fr₁ D).all.map (·.no)).Nodup)
    (hcap : ∀ n ds, (rest₁ n ds).err = Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hbase : ∀ n p, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
        k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some p → ∀ j ∈ [0, 1], (at_ j).1 < p.base)
    (hcell : CellOnly coll) (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (st0 : TK Xi) (hw : Nonempty (Wit Cells Unit Mm × Unit)) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 4 :=
  r1_4_whole X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp file hD q₁ q₂ q₃ hR
    ha hn ht hL hnd hcap hbase hcell hS hsame st0 hw fun valB n _ =>
      read_bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 valB n

end Johnson.RunOne.Law.FieldR14X

#print axioms Johnson.RunOne.Law.FieldR14X.bitVec_is
#print axioms Johnson.RunOne.Law.FieldR14X.read_bitVec
#print axioms Johnson.RunOne.Law.FieldR14X.r1_4
