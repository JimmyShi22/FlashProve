-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsWholeAtSeat.lean: THE KEY FILE, ROWS 2.7 · 2.4 · 2.1 WHOLE, WITH THEIR CALLS
MADE: at the tables' own reading T.h₂, at the piece
that holds held of THE DESCRIPTION's OWN BLOCK at one written round, with the number beside:
keeps₂_of_halves'
(Johnson/RunOne/KeyHalves23.lean) at the forward halves (KeyForward.lean) and at K14's files'
chance's halves AT THE SEAT
(zeta_half₂_rounds, KeyRow27Number.lean ·
loc_back₂_seat | point_back₂_seat, KeyRowsBackAtSeat.lean).

PAID HERE, BY CALLS:

  hl | hb     the block's yes is the kind's function: the description's own blocksInOrder[k] is seat b_k
  (shared_1 | shared_4, KeyForward.lean; hb_of_flat7)
  hP | hpins  the reading's samples and record stay: at every BaseSt's h₂ (samePins_h₂ ·
  pinsStay_h₂_zeta)
  PileTies    inside point_back₂_seat (pileTies_at)
  hA | ho     at 2.4: out of ONE fact on the frame's tiling: Matches Fr₂.a dep b4.rounds [d]
  (loc_match, KeyRow24Depth.lean)
  the carriage, SendsDraws and the number: out of hW (the written round has the entry and kind of
  the key file's written list) and hS
  hR          is no premise: a theorem at every shape (le_two_pow_ceilLog2)
LEFT, IN THE THREE BINDER LISTS: h (the kind's blocks can be said) · hS (the description's shape is
the key file's typed shape) · hbk · hW · hbase ·
CellOnly coll · hsame · at 2.4: henc · hm · at 2.1: the split is needed · the plan has a stage · hK
· hof · henc · the radius' two bounds · CollTie · DecTie.

OBJECT   (Key.descriptionFromSource X N P).shared.blocksInOrder[7 | 4 | 1], held, at one written round d
USER     the frame's keepsAt_of_law₂ (with Err.le out of Err.Below at the cap): the fields r2_7 |
r2_4 | r2_1: not called here
What is not claimed. That the maker's pieces ARE these pieces. NO MEMBER SHOWN of on₂ … k: the
laws may be true and empty at the real protocol.
No soundness of a verifier.

-/
import Johnson.RunOne.KeyForward
import Johnson.RunOne.KeyHalves23
import Johnson.RunOne.KeyRow27Sits
import Johnson.RunOne.KeyRow27Pins
import Johnson.RunOne.KeyRow27Number
import Johnson.RunOne.KeyRow24Depth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law (atW posAt vecAt efReal k14_rounds_key)
open VerifiableInference.Desc.K13.Law (ρg)
open Johnson.RunOne.KeyRows1 (plan₁)
open scoped ENNReal

/-- One sample and one record at all seats give it at the seats of a list. -/
theorem pinsStay_of_samePins {A₁ A₂ Cells M Smp Rec : Type} {G : Reading (A₁ × A₂) Cells M Smp Rec}
    (at_ : Where) (l : List Nat) {u v : A₁ × A₂}
    (H : SamePins G u v) : PinsStay G at_ l u v := ⟨fun _ _ => (H.smp _ _).symm, H.recOf.symm⟩

section
variable {XI Cells M Smp Rec W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp Rec)
    (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

/-- **ROW 2.7, WHOLE, AT THE SEAT, WITH ITS NUMBER.** -/
theorem r2_7_seat (hS : (p14At X P).S = Lk6.AtPlan.keyFull.once.shape) (b : Block St₂ Claim) (hbk :
    (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 6 = some (d.entry, d.kind)) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y) :
    (zetaSeat Fr₂ b base d (p14At X P).S.kRow ((p14At X P).S.kRow * Fintype.card OnBytes.Slice.GE ^
        ((p14At X P).S.kRow - 1)) ext).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 7) (on₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc rad a coll last₁ off₂ (7 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 7) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc
            rad (7 + 1))
        (zetaSeat Fr₂ b base d (p14At X P).S.kRow ((p14At X P).S.kRow * Fintype.card
            OnBytes.Slice.GE ^ ((p14At X P).S.kRow - 1)) ext).err ∧
      Err.Below (zetaSeat Fr₂ b base d (p14At X P).S.kRow ((p14At X P).S.kRow * Fintype.card
          OnBytes.Slice.GE ^ ((p14At X P).S.kRow - 1)) ext).err ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have H := zeta_half₂_rounds F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ (hS ▸
      k14_rounds_key) d hW b
    (hb_of_flat7 X N P _ h b hbk) base ext hsame hbase (fun x _ z => pinsStay_h₂_zeta T at_ _ x.1.1
        x.1.2 z)
  exact ⟨keeps₂_of_halves' F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ _ 7 hbase (by
      decide) hcC
    (fwd₂₇ F T.h₂ at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h b hbk _ rfl
      fun z d₀ d' r y hl _ => pinsStay_of_samePins at_ _ (samePins_h₂ T (z, d₀) (z, d') rfl (by rw
          [hl.is]) (by rw [hl.is]))) H.1, H.2⟩

/-- **ROW 2.4, WHOLE, AT THE SEAT, WITH ITS NUMBER** (32 of the 128 bits are work). -/
theorem r2_4_seat {K : Type} [Field K] (ρ : Model.Reading K) (hS : (p14At X P).S =
    Lk6.AtPlan.keyFull.once.shape) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 3 = some (d.entry, d.kind)) (dep : Nat → Option
        Nat)
    (hm : Matches Fr₂.a dep b4.rounds [d]) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (henc : EncIs ρ (p14At X P).par.S.fold enc) :
    (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d (p14At X
        P).par.S.fold.index.code.logN (p14At X P).par.S.fold.columns ((2 ^ (p14At X
        P).par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ (p14At X
        P).par.S.fold.columns) ext).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂
            (4 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius 4) (L₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc OnBytes.Params.recordRadius (4 + 1))
        (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d (p14At X
            P).par.S.fold.index.code.logN (p14At X P).par.S.fold.columns ((2 ^ (p14At X
            P).par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ (p14At X
            P).par.S.fold.columns) ext).err ∧
      Err.Below (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d (p14At X
          P).par.S.fold.index.code.logN (p14At X P).par.S.fold.columns ((2 ^ (p14At X
          P).par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ (p14At X
          P).par.S.fold.columns) ext).err ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain rfl : seat b4 = b := Option.some.inj ((shared_4 X N P b1 b2 b3 b4 b5 b6 b7 b8 h).symm.trans
      hbk)
  obtain ⟨hA, ho⟩ := loc_match (p14At X P) b1 b2 b3 b4 b5 b6 b7 b8 h Fr₂.a dep d hm
  have H := loc_back₂_seat F Fr₂ T at_ (p14At X P) b1 b2 b3 b4 b5 b6 b7 b8 h (seat b4) K₁ R enc a
      coll last₁ off₂ ρ rfl hS d hW ho base ext hbase
    hsame henc (Nat.le_of_eq hA)
  exact ⟨keeps₂_of_halves' F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll
      last₁ off₂ _ 4 hbase (by decide) hcC
    (fwd₂₄ F T.h₂ at_ K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6
        b7 b8 h (seat b4) hbk _ rfl
      fun z d₀ d' r GU rows y hl _ => pinsStay_of_samePins at_ _ (samePins_h₂ T (z, d₀) (z, d') rfl
          hl.oracles hl.codes)) H.1, H.2⟩

/-- **ROW 2.1, WHOLE, AT THE SEAT, WITH ITS NUMBER.** -/
theorem r2_1_seat (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (hK : one.lin = (p14At X
    P).par.S)
    (err eM : Nat) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X
        P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → Nat)
    (hS : (p14At X P).S = Lk6.AtPlan.keyFull.once.shape) (hSp : (p14At X P).S.sharedSplitNeeded =
        true) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 0 = some (d.entry, d.kind)) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg (p14At X P).par.S.fold enc)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At
        one) off₂ err eM rank)
    (hdec : DecTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At one)
        off₂ err eM rank) :
    (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d ((p14At X P).par.S.kLo + (p14At X
        P).par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ (p14At X P).par.S.kLo + ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v) * Fintype.card Cb.Gl.E ^ ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v - 1)) ext).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ 1)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂
            (1 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 1) (L₂ F Fr₂ T.h₂ at_ (p14At X
            P).S (plan₁ one) R enc 2852142980 (1 + 1))
        (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d ((p14At X P).par.S.kLo + (p14At X
            P).par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ (p14At X P).par.S.kLo + ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v) * Fintype.card Cb.Gl.E ^ ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v - 1)) ext).err ∧
      Err.Below (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Claim) base d ((p14At X P).par.S.kLo +
          (p14At X P).par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ (p14At X P).par.S.kLo + ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v) * Fintype.card Cb.Gl.E ^ ((p14At X P).par.S.kLo + (p14At X
              P).par.S.fold.index.v - 1)) ext).err ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain rfl : seat b1 = b := Option.some.inj ((shared_1 X N P b1 b2 b3 b4 b5 b6 b7 b8 h).symm.trans
      hbk)
  have H := point_back₂_seat F Fr₂ T at_ (p14At X P) b1 b2 b3 b4 b5 b6 b7 b8 h (seat b1) R enc a
      coll off₂ one hst hK err eM rank rfl hS d hW base ext
    hbase hsame hof henc hle hM hcoll hdec
  exact ⟨keeps₂_of_halves' F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At
      one) off₂ _ 1 hbase (by decide) hcC
    (fwd₂₁ F T.h₂ at_ (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ X N P b1 b2 b3 b4 b5 b6
        b7 b8 h hSp (seat b1) hbk _ rfl
      fun z d₀ d' r y hl _ => pinsStay_of_samePins at_ _ (samePins_h₂ T (z, d₀) (z, d') rfl
          hl.oracles hl.codes)) H.1, H.2⟩

end

end Johnson.RunOne.KeyRows23
