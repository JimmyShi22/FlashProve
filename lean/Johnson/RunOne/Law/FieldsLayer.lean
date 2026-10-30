-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldsLayer.lean: IT WANTS
THE TABLE'S bitVec (KeyK3W.lean).
THE FIELDS r1_5 AND r1_11 OF THE FRAME LPFD.The21, WITH ALL FOUR IMPLICATIONS OF THE TIE
TYPED: KeepsAt of the table's promise with its history and the table's claim, at pieces 5 and 11 of
the maker's row of the key file's first chain (the layer behind each lookup's rounds), at any data
D: by one call of keeps_conseq_yes (TieClaimLayer.lean) and one of keeps_reached: keeps_layer
(KeepsAtRows.lean) · tie_promise (TiePromise.lean) · claim_front_layer₀ | ₁ (TieFrontLayer.lean) ·
on_behind_layer (LayerBehind.lean) · claim_layer₀ | ₁.

Main names:
  layer_yes: the piece's out is the layer's own yes.
  r1_5, r1_11: the fields' statements.

Object: the fields r1_5 and r1_11 of LPFD.The21 (Johnson/Top/Fire/Code/The35.lean), at any D.
User: r1_5_in_scope, r1_11_in_scope (FieldsLayerScope.lean).
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests.
PREMISES ON THE TABLE'S LETTERS AND THE FRAME, PAID BY NOBODY HERE, FOUR: the two pinned trees lie
below the place of every piece from the third to the fifteenth · coll reads the stored table's cells
alone · B.SmReads · R.same is "read alike".
Premise on the frame's letters besides: the description's first flat list of blocks is c₁ :: k₁
(q₁).
Premises that are theorems in scope: planOk · RoomFor · the own message counts an answer · two
lookups.

Limits. IMPLICATIONS: that the premises on the table's letters and the frame can hold together is
not shown
here, nor a member of the promise. Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldsFree
import Johnson.RunOne.Law.TieFrontLayer
import Johnson.RunOne.Law.LayerBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldsLayer
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where lookupSeat lookupPlace
  layer caller)
open Johnson.RunOne.Sound (FK fk_link_at)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ CellOnly)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieLow
open Johnson.RunOne.Law.TieBehindK3
open Johnson.RunOne.Law.TieClaimLayer
open Johnson.RunOne.Law.TieFrontLayer
open Johnson.RunOne.Law.LayerBehind
open Johnson.RunOne.Law.KeepsAtRows
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.FieldR14
open Johnson.RunOne.Law.FieldR14X
open Johnson.RunOne.Law.FieldsFree
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

omit B at_ R coll in
/-- **The piece's out is the layer's own yes.** -/
theorem layer_yes (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (l : ℕ) (hl : l < 2) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 3]? = some p) (a b : (Xi × FirstState) × (fr₁ D).E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) (hout : p.ior.red.out a τ = some b) :
    ∃ rs gs, (layer X.Y.k.oneTime X.set l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))
      (claimsIn [caller X.Y.k.oneTime l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l)),
        lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l
              (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
                  X.Y.k.oneTime l)))]
        [(1, "objects"), (1, "planes"), (1, "guests")])).decide a.1.2 rs gs = .ok b.1.2 := by
  have hl' : l < X.Y.k.oneTime.ranges.lookups.length := by rw [hn]; exact hl
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = (layer X.Y.k.oneTime X.set l (Wf.lookupOf
      X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))
      (claimsIn [caller X.Y.k.oneTime l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l)),
        lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l
              (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
                  X.Y.k.oneTime l)))]
        [(1, "objects"), (1, "planes"), (1, "guests")])) := ⟨_, rfl⟩
  have hpb : p.b = held blk := by
    have h1 := LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (2 + 6 * l + 3) p hq
    obtain ⟨c0, c4, c5, hF, -, -, -⟩ := link_flat X.Y.k.oneTime X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))
    have h2 := fk_link_at X N P l 3 (by omega) _ (look_at X.Y.k.oneTime l hl')
    rw [hF] at h2
    have h3 : (c₁ :: k₁)[2 + 6 * l + 3]? = some blk := by
      rw [← q₁, Nat.add_assoc, hblk]
      exact h2
    rw [List.getElem?_map, h3] at h1
    exact (Option.some.inj h1).symm
  have hd := piece_decides_at p a τ b hout
  rw [hpb] at hd
  obtain ⟨-, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  rw [hblk] at hd'
  exact ⟨_, _, hd'⟩

/-- **THE FIELD r1_5.** -/
theorem r1_5 (hp : (FK X N P).planOk = true) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hbase : ∀ n p, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some p → ∀ j ∈ [0, 1], (at_ j).1 < p.base)
    (hcell : CellOnly coll) (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 5 := by
  intro p hq
  have hk := keeps_layer X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp q₁
    (frame_nodup D) 0 (by rw [hn]; omega) p hq
    (lowDec_T (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_) (coll := coll) hcell
      (hbase 5 p (by omega) (by omega) hq 0 (by simp))
      (hbase 5 p (by omega) (by omega) hq 1 (by simp)))
  have hb : ((Fk X N P).first.blocksInOrder.map held)[5]? = some p.b := by
    rw [q₁]
    exact LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 5 p
      hq
  have behind : ∀ a τ b, On₁' X N P D B at_ R coll 5 a → p.ior.red.out a τ = some b →
      On₁ X N P D B at_ R coll 6 b := fun a τ b hon hout =>
    on_behind_layer X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp hR ha hn q₁
      (collCell_of_cellOnly hcell) 0 (by omega) p hq (hbase 5 p (by omega) (by omega) hq) a b τ
      hon hout
  have h1 := tie_promise (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_) (R := R)
    (coll := coll) hS hp hR ha hn 0 3 (by omega) (by omega)
  exact LPFD.keeps_reached _ _ 5 p hb _ _ _ _ (keeps_conseq_yes hk h1
    (fun a τ b hon hout _ hrel => by
      obtain ⟨rs, gs, hy⟩ := layer_yes X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hn q₁ 0
        (by omega) p hq a b τ hout
      exact claim_front_layer₀ hS hsame hp hn
        (fun valB n _ => read_bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 valB n) a hon.1
        (h1 a hon)
        (outsOne_of_hist D a.2 hp hR ha 0 (by rw [hn]; omega) a.1 hon.2) _ rs gs hy hrel)
    (fun a τ b hon hout _ => behind a τ b hon hout)
    (fun a τ b hon hout _ hcl =>
      have hist := LPFD.reached_step _ _ 5 p hb a τ b hout hon.2
      claim_layer₀ hS hsame hp hn b (behind a τ b hon hout)
        (off_of_hist D b.2 hp hR ha 6 (by omega) (by omega) b.1 hist)
        (low_of_hist D b.2 hp hR ha 6 (by omega) (by omega) b.1 hist) hcl))

/-- **THE FIELD r1_11.** -/
theorem r1_11 (hp : (FK X N P).planOk = true) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hbase : ∀ n p, 2 ≤ n → n ≤ 14 → ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some p → ∀ j ∈ [0, 1], (at_ j).1 < p.base)
    (hcell : CellOnly coll) (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b) :
    KeepsAt (On₁' X N P D B at_ R coll) (Cl₁ X N P D B at_ R)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁) 11 := by
  intro p hq
  have hk := keeps_layer X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp q₁
    (frame_nodup D) 1 (by rw [hn]; omega) p hq
    (lowDec_T (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_) (coll := coll) hcell
      (hbase 11 p (by omega) (by omega) hq 0 (by simp))
      (hbase 11 p (by omega) (by omega) hq 1 (by simp)))
  have hb : ((Fk X N P).first.blocksInOrder.map held)[11]? = some p.b := by
    rw [q₁]
    exact LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 11 p
      hq
  have behind : ∀ a τ b, On₁' X N P D B at_ R coll 11 a → p.ior.red.out a τ = some b →
      On₁ X N P D B at_ R coll 12 b := fun a τ b hon hout =>
    on_behind_layer X N P D B at_ R coll c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hp hR ha hn q₁
      (collCell_of_cellOnly hcell) 1 (by omega) p hq (hbase 11 p (by omega) (by omega) hq) a b τ
      hon hout
  have h1 := tie_promise (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_) (R := R)
    (coll := coll) hS hp hR ha hn 1 3 (by omega) (by omega)
  exact LPFD.keeps_reached _ _ 11 p hb _ _ _ _ (keeps_conseq_yes hk h1
    (fun a τ b hon hout _ hrel => by
      obtain ⟨rs, gs, hy⟩ := layer_yes X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hn q₁ 1
        (by omega) p hq a b τ hout
      exact claim_front_layer₁ hS hsame hp hn
        (fun valB n _ => read_bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1 valB n) a hon.1
        (off_of_hist D a.2 hp hR ha 11 (by omega) (by omega) a.1 hon.2) (h1 a hon)
        (outsOne_of_hist D a.2 hp hR ha 1 (by rw [hn]; omega) a.1 hon.2) _ rs gs hy hrel)
    (fun a τ b hon hout _ => behind a τ b hon hout)
    (fun a τ b hon hout _ hcl =>
      have hist := LPFD.reached_step _ _ 11 p hb a τ b hout hon.2
      claim_layer₁ hS hsame hp hn b (behind a τ b hon hout)
        (off_of_hist D b.2 hp hR ha 12 (by omega) (by omega) b.1 hist)
        (low_of_hist D b.2 hp hR ha 12 (by omega) (by omega) b.1 hist) hcl))

end Johnson.RunOne.Law.FieldsLayer

#print axioms Johnson.RunOne.Law.FieldsLayer.layer_yes
#print axioms Johnson.RunOne.Law.FieldsLayer.r1_5
#print axioms Johnson.RunOne.Law.FieldsLayer.r1_11
