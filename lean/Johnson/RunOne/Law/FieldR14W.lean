-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldR14W.lean: THE FIELD
r1_4 OF THE FRAME LPFD.The21, WITH ALL FOUR IMPLICATIONS OF THE TIE TYPED: KeepsAt of the table's
promise with its history and the table's claim, at piece 4 of the maker's row of the key file's
first chain (the kind's own block of the first lookup), at any data D: r1_4_of_h4 (FieldR14.lean)
with its premise h4 paid by claim_behind₀ (TieClaimBehind.lean) over on_behind_k3
(TieBehindK3.lean).

Main names:
  r1_4_whole: THE FIELD's STATEMENT, under the premises listed below.

Object: the field r1_4 of LPFD.The21 (Johnson/Top/Fire/Code/The35.lean), at any D.
User: r1_4 (FieldR14X.lean).
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests.
PREMISES ON THE TABLE'S LETTERS AND THE FRAME, PAID BY NOBODY HERE: no two trees of the frame have
one number · the first chain's rests have the cap at 128 as their errors · the two pinned trees lie
below the place of every piece from the third to the fifteenth · coll reads the stored table's
cells alone · B.SmReads · R.same is "read alike" · a witness · a value of the riding type · THE
BITS: the table's bitVec, read, is Planes.bitsOf at every real index of lookup 0 (a theorem
without a premise: FieldR14X.lean).

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
import Johnson.RunOne.Law.FieldR14
import Johnson.RunOne.Law.TieClaimBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldR14W
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.TieBehindK3
open Johnson.RunOne.Law.TieClaimBehind
open Johnson.RunOne.Law.FieldR14
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

/-- **THE FIELD r1_4, ALL FOUR IMPLICATIONS TYPED.** -/
theorem r1_4_whole (hp : (FK X N P).planOk = true) (file : String)
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
    (st0 : TK Xi) (hw : Nonempty (Wit Cells Unit Mm × Unit))
    (hbit : ∀ (valB : ℕ → E) (n : ℕ),
      n < 2 ^ ((faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))).mu + (faceOfLkp (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  0))).d) →
      readE (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 valB n)
          =
        Planes.bitsOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 (fun k => readE (valB k))
          (n / 2 ^ (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))).mu) (n % 2 ^ (faceOfLkp (Wf.lookupOf
                  X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                      0))).mu)) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 4 :=
  r1_4_of_h4 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp file hD q₁ q₂ q₃ hR
    ha hn ht hL hnd hcap hbase hcell hS hsame st0 hw fun p hq a τ b hon hout hT hcl =>
      claim_behind₀ hS hsame hp hn hbit b
        (on_behind_k3 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp hR ha hn
          q₁ (collCell_of_cellOnly hcell) 0 (by omega) p hq (hbase 4 p (by omega) (by omega) hq) a b
              τ hon
          hout) hT hcl

end Johnson.RunOne.Law.FieldR14W

#print axioms Johnson.RunOne.Law.FieldR14W.r1_4_whole
