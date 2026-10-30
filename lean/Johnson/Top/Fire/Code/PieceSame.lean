-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/PieceSame.lean: «THE ROW's PIECE IS THE KIND's PIECE»: how a kind's law, proved at its own piece, becomes a numbered field of the frame. Book-keeping, general in the description.
Main names.
  `ior_pieceOf`: WHAT A LAW READS OF A PIECE: two pieces of one block, base, stretch and «put behind» have ONE reduction: the extractor and the errors do not enter it. `piece_eta`: every piece is a `pieceOf` of its own parts.
  `keeps_same` | `leads_same`: FROM A KIND's ERRORS UP: a law at a piece q holds at `pieceOf q.b q.base q.ds q.back x'` wherever q's errors are at most x''s. `keeps_same_cap`: so at the cap, from `Err.Below q.err (2⁻¹ ^ 128)`: the ramp at ONE piece.
  `keepsAt_of_law₁` | `₂` | `₃`: THE CALL AT THE MAKER's ROW: the caller IS HANDED THE EQUATION «the row's n-th piece is `pieceOf (held b) base ds back (restⱼ n ds)`, b the chain's n-th block», names its own extractor and errors x at that stretch, shows its law there and `Err.le x.err (restⱼ n ds).err`: that is the field `KeepsAt on L ‹the row› n`.
THE ROAD OF A KIND's LAW, WHOLE: GoodIn at its own piece q of THE KIND's block at the kind's record ⟹ (`keeps_of_goodIn`, Johnson/Desc/Plain/FromGood.lean | `leads_of_goodIn`, Johnson/Desc/Key/KeySendRow.lean) Keeps | Leads at q ⟹ (`keeps_held` | `keeps_heldU`, Johnson/Desc/Plain/PaidKeeps.lean: the kind's block ↦ `held b`, the record ↦ the pair) at the held piece ⟹ (`keeps_same`) at the maker's piece, the errors raised ⟹ (`keepsAt_of_lawⱼ`) the field of `The35`.
WHAT IT DOES NOT GIVE: that the kind's base and stretch ARE the maker's: that is left to the kind's files, from the equation and what the maker's cut is known to fit.
THE SILLY MEMBERS. The same block and ANOTHER stretch: another shape, another reduction: nothing crosses · the same block, base, stretch and another «put behind»: likewise · errors larger than the row's: `Err.le` fails: a law at greater errors pays nothing at the cap.
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowPieces
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {C : CK} {Fr : Frame} {S Cl W : Type}

/-- **What a law reads of a piece.** -/
theorem ior_pieceOf (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView) (x x' : Rest C Fr S W ds) :
    (pieceOf b base ds back x).ior = (pieceOf b base ds back x').ior := rfl

/-- Every piece is a `pieceOf` of its own parts. -/
theorem piece_eta (q : Piece C Fr S Cl W) : q = pieceOf q.b q.base q.ds q.back ⟨q.ext, q.err⟩ := rfl

/-- **From a kind's errors up.** -/
theorem leads_same (q : Piece C Fr S Cl W) (x' : Rest C Fr S W q.ds) {on : S × Fr.E.Str → Prop} {Q : S × Fr.E.Str → S × Fr.E.Str → Prop}
    (h : q.ior.red.Leads on Q q.err) (hle : Err.le q.err x'.err) : (pieceOf q.b q.base q.ds q.back x').ior.red.Leads on Q x'.err :=
  Iop.Reduction.Leads.mono_err h hle

theorem keeps_same (q : Piece C Fr S Cl W) (x' : Rest C Fr S W q.ds) {on on' L L' : S × Fr.E.Str → Prop}
    (h : q.ior.red.Keeps on on' L L' q.err) (hle : Err.le q.err x'.err) : (pieceOf q.b q.base q.ds q.back x').ior.red.Keeps on on' L L' x'.err :=
  leads_same q x' h hle

/-- **The ramp at one piece.** -/
theorem keeps_same_cap (q : Piece C Fr S Cl W) (x' : Rest C Fr S W q.ds) {on on' L L' : S × Fr.E.Str → Prop}
    (h : q.ior.red.Keeps on on' L L' q.err) (hb : Err.Below q.err ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hc : x'.err = Err.cap 128 (uLT C q.ds)) :
    (pieceOf q.b q.base q.ds q.back x').ior.red.Keeps on on' L L' x'.err :=
  keeps_same q x' h (hc ▸ Err.le_cap_of_below_inv 128 _ hb)

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- **The call at the maker's row of chain 1.** -/
theorem keepsAt_of_law₁ (on L) (n : ℕ)
    (law : ∀ (b : Block F.S₁ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₁ :: k₁)[n]? = some b →
      ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some (pieceOf (held b) base ds back (rest₁ n ds)) →
      ∃ x : Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds, (pieceOf (held b) base ds back x).ior.red.Keeps (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₁ n ds).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) n := fun p hp => by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b base ds back hb hp
  exact keeps_same (pieceOf (held b) base ds back x) (rest₁ n ds) hx hle

/-- **The call at the maker's row of chain 2.** -/
theorem keepsAt_of_law₂ (on L) (n : ℕ)
    (law : ∀ (b : Block F.S₂ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₂ :: k₂)[n]? = some b →
      ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some (pieceOf (held b) base ds back (rest₂ n ds)) →
      ∃ x : Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds, (pieceOf (held b) base ds back x).ior.red.Keeps (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₂ n ds).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) n := fun p hp => by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₂ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b base ds back hb hp
  exact keeps_same (pieceOf (held b) base ds back x) (rest₂ n ds) hx hle

/-- **The call at the maker's row of chain 3.** -/
theorem keepsAt_of_law₃ (on L) (n : ℕ)
    (law : ∀ (b : Block F.S₃ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView), (c₃ :: k₃)[n]? = some b →
      ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some (pieceOf (held b) base ds back (rest₃ n ds)) →
      ∃ x : Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds, (pieceOf (held b) base ds back x).ior.red.Keeps (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₃ n ds).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) n := fun p hp => by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₃ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b base ds back hb hp
  exact keeps_same (pieceOf (held b) base ds back x) (rest₃ n ds) hx hle

end

end LPFD

#print axioms LPFD.ior_pieceOf
#print axioms LPFD.piece_eta
#print axioms LPFD.leads_same
#print axioms LPFD.keeps_same
#print axioms LPFD.keeps_same_cap
#print axioms LPFD.keepsAt_of_law₁
#print axioms LPFD.keepsAt_of_law₂
#print axioms LPFD.keepsAt_of_law₃
