-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldR14.lean: THE FIELD
r1_4 OF THE FRAME LPFD.The21 (KeepsAt of the table's promise with its history and the table's
claim, at piece 4 of the maker's row of the key file's first chain), FROM THE LINKS' LAW, BY ONE
CALL OF keeps_conseq: with ONE of the four implications left as a premise.

Main names:
  collCell_of_cellOnly: the one notion on the letter coll gives the other.
  r1_4_of_h4: KeepsAt (On₁' …) (Cl₁ …) ‹the maker's row› 4, at any data D, from: Keeps between the
    links' rows (keeps_k3) · the promises' tie (tie_promise) · the claims' tie in front
    (claim_front₀) · the table's promise behind (on_behind_k3) · the history behind
    (keeps_reached) · AND THE PREMISE h4: behind the block the table's claim gives the links'
    relation.

Object: the field r1_4 of LPFD.The21 (Johnson/Top/Fire/Code/The35.lean), at any D.
User: r1_4_whole (FieldR14W.lean).
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests.
Premises on the table's letters and the frame: no two trees of the frame have one number · the first
chain's rests have the cap at 128 as their errors · the two pinned trees lie below the place of
every piece from the third to the fifteenth · coll reads the stored table's cells alone ·
B.SmReads · R.same is "read alike" · a witness · a value of the riding type.
Premises on the frame's letters besides: the description's three flat lists of blocks are the
frame's heads and tails: c₁ :: k₁, c₂ :: k₂, c₃ :: k₃ (q₁, q₂, q₃).
Premises that are theorems in scope: planOk · the data · RoomFor · the own message counts an answer
· two lookups · target = 128 · LookHeld.

Limits. h4 IS NOT PROVED. So the field is not paid.
(Where this
and lean/THEOREM.md differ, the page holds.)
Nothing on soundness.

-/
import Johnson.RunOne.Law.TieBehindK3
import Johnson.RunOne.Law.TieClaimFront
import Johnson.RunOne.Law.TieLow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldR14
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly)
open Johnson.RunOne.KeyRows1 (CollCell)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieLow
open Johnson.RunOne.Law.TieBehindK3
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.KeepsAtRows
open LPFD (On₁' KeepsAt)

/-- The one notion on the letter coll gives the other. -/
theorem collCell_of_cellOnly {Rec : Type} {coll : Strs → Rec → Prop} (h : CellOnly coll) :
    CollCell coll := fun y y' r hc hx => (h y y' r hc).1 hx

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

/-- **THE FIELD r1_4, WITH ONE IMPLICATION LEFT AS A PREMISE.** -/
theorem r1_4_of_h4 (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok D) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (ht : X.set.target = 128)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
      (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))))
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
    (h4 : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
        rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[4]? = some p → ∀ a τ b, On₁' X N P D B at_ R coll 4 a →
      p.ior.red.out a τ = some b → (rowT X N P D B at_ R coll 0 3).on b →
      Cl₁ X N P D B at_ R 5 b → (rowT X N P D B at_ R coll 0 3).rel b) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 4 := by
  intro p hq
  have low : ∀ n q, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
      k₂ c₃ k₃
      rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some q → _ := fun n q h2 h14 hx =>
    lowDec_T (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_) (coll := coll) hcell
      (hbase n q h2 h14 hx 0 (by simp)) (hbase n q h2 h14 hx 1 (by simp))
  have hk := keeps_k3 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp file hD
    q₁ q₂ q₃ hnd ht 0 (by rw [hn]; omega) hL hcap st0 hw (fun q hx => low 2 q (Nat.le_refl _) (by
        omega) hx) p
    hq (low 4 p (by omega) (by omega) hq)
  have hb : ((Fk X N P).first.blocksInOrder.map held)[4]? = some p.b := by
    rw [q₁]
    exact LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 4 p
      hq
  exact LPFD.keeps_reached _ _ 4 p hb _ _ _ _ (keeps_conseq hk
    (tie_promise hS hp hR ha hn 0 2 (by omega) (by omega))
    (fun a hon hrel => claim_front₀ hS hsame hp hn a hon hrel)
    (fun a τ b hon hout _ => on_behind_k3 X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
      dW wEnd hp hR ha hn q₁ (collCell_of_cellOnly hcell) 0 (by omega) p hq
      (hbase 4 p (by omega) (by omega) hq) a b τ hon hout)
    (h4 p hq))

end Johnson.RunOne.Law.FieldR14

#print axioms Johnson.RunOne.Law.FieldR14.r1_4_of_h4
