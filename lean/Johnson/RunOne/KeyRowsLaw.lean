-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsLaw.lean: THE KEY FILE, ROWS 2.7 · 2.4 · 2.1 IN THE FORM OF THE FRAME's CALL:
what keepsAt_of_law₂ (the key file's frame on the
plain road) asks as «law» at one row: THERE IS a piece's rest x (extractor and errors) with Keeps at
pieceOf (held b) base ds back x AND
Err.le x.err ‹the maker's rest's errors›: at ds = [d], back = [], where the maker's errors are the
cap Err.cap 128.

  r2_7_law | r2_4_law | r2_1_law   from r2_k_seat (Johnson/RunOne/KeyRowsWholeAtSeat.lean) and
  Err.le_cap_of_below_inv (Iop/ErrCap.lean):
                                   the law's own written count lies below the cap because it is a
                                   share of at most 2^-128.
x takes the maker's own extractor (a law in the plain form reads none).

OBJECT   pieceOf (held b) base [d] [] x, b := (Key.descriptionFromSource X N P).shared.blocksInOrder[7 | 4 | 1]
USER     the frame's keepsAt_of_law₂ at n = 7 | 4 | 1 (then KeepsAt.reached for the woven promise):
not called here
LEFT     r2_k_seat's premises · hcap: the maker's errors at the row are the cap · that the maker's
stretch at the row is [d] with nothing laid behind
What is not claimed. NO MEMBER SHOWN of on₂ … k: the laws may be true and empty at the real
protocol. No soundness of a verifier.

-/
import Johnson.RunOne.KeyRowsWholeAtSeat
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law (atW)
open VerifiableInference.Desc.K13.Law (ρg)
open Johnson.RunOne.KeyRows1 (plan₁)
open scoped ENNReal

section
variable {XI Cells M Smp Rec W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp Rec)
    (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem r2_7_law (hS : (p14At X P).S = Lk6.AtPlan.keyFull.once.shape) (b : Block St₂ Claim) (hbk :
    (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 6 = some (d.entry, d.kind)) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 7) (on₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc rad a coll last₁ off₂ (7 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 7) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc
            rad (7 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have H := r2_7_seat F Fr₂ T at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS
      b hbk d hW base x'.ext hbase hcC hsame
  exact ⟨⟨x'.ext, _⟩, H.1, hcap ▸ Err.le_cap_of_below_inv 128 _ H.2⟩

theorem r2_4_law {K : Type} [Field K] (ρ : Model.Reading K) (hS : (p14At X P).S =
    Lk6.AtPlan.keyFull.once.shape) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 3 = some (d.entry, d.kind)) (dep : Nat → Option
        Nat)
    (hm : Matches Fr₂.a dep b4.rounds [d]) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (henc : EncIs ρ (p14At X P).par.S.fold enc)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂
            (4 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius 4) (L₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc OnBytes.Params.recordRadius (4 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have H := r2_4_seat F Fr₂ T at_ K₁ R enc a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h ρ hS b
      hbk d hW dep hm base x'.ext hbase hcC hsame henc
  exact ⟨⟨x'.ext, _⟩, H.1, hcap ▸ Err.le_cap_of_below_inv 128 _ H.2⟩

theorem r2_1_law (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (hK : one.lin = (p14At X
    P).par.S)
    (err eM : Nat) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X
        P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → Nat)
    (hS : (p14At X P).S = Lk6.AtPlan.keyFull.once.shape) (hSp : (p14At X P).S.sharedSplitNeeded =
        true) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 0 = some (d.entry, d.kind)) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg (p14At X P).par.S.fold enc)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At
        one) off₂ err eM rank)
    (hdec : DecTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At one)
        off₂ err eM rank)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ 1)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂
            (1 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 1) (L₂ F Fr₂ T.h₂ at_ (p14At X
            P).S (plan₁ one) R enc 2852142980 (1 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have H := r2_1_seat F Fr₂ T at_ R enc a coll off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h one hst hK err
      eM rank hS hSp b hbk d hW base x'.ext hbase hcC
    hsame hof henc hle hM hcoll hdec
  exact ⟨⟨x'.ext, _⟩, H.1, hcap ▸ Err.le_cap_of_below_inv 128 _ H.2⟩

end

end Johnson.RunOne.KeyRows23
