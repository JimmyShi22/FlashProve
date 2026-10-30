-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow27Number.lean: THE KEY FILE, ROW 2.7 ("LIN zeta"): THE CHANCE's HALF WITH ITS
NUMBER: the half at the seat (zeta_half₂_seat, Johnson/RunOne/KeyRow27Chance.lean) at the count kRow
|K| ^ (kRow - 1) itself, and beside
it: the seat's written errors are shares of at most 2^-128 of the round's written challenges: both
from ONE premise on the written
round: it has the entry and kind of a written list's round number 6, at which K14Rounds holds
(Johnson/Goal/Numbers/K14RoundsAt.lean: one comparison
of natural numbers).

  zeta_half₂_rounds   at any shape and written list with K14Rounds
  zeta_half₂_key      at the key file's typed shape keyFull.once.shape and the written rounds
  dryKeyFull.2.1 of a key file's second
                      chain, where K14Rounds is k14_rounds_key: an evaluation in Lean's kernel. NO
                      BIT OF THE 128 IS WORK at this round.

What is not claimed. That the frame's data hold, at the maker's piece number 7 of the shared chain,
a round with that entry and kind
(hW): the frame's. That the table's letter S is keyFull.once.shape at the seat. The premises of
zeta_half₂_seat but hd and he stay.
NO MEMBER SHOWN of on₂ … 7: the law may be true and empty at the real protocol (and the condition
on the letter M at
KeyRow27Chance.lean's head). No soundness of a verifier.

-/
import Johnson.RunOne.KeyRow27Chance
import Johnson.Goal.Numbers.K14RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law (K14Rounds atW k14_rounds_key cMax)
open scoped ENNReal

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **ROW 2.7, THE CHANCE's HALF, WITH ITS NUMBER.** -/
theorem zeta_half₂_rounds {Wr : Rounds} {rd cmax work : Nat} (H : K14Rounds S Wr rd cmax work)
    (d : RDT) (hW : atW Wr 6 = some (d.entry, d.kind))
    (b7 : Block St₂ Cl) (hb : ∀ d rs gs d', b7.decide d rs gs = .ok d' → _root_.Desc.K14.linZeta d
        rs = some d') (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → Iop.Tr (uLT (_root_.Run.ckP .two) [d]) → W → W)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base)
    (hpins : ∀ x, on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → ∀ z,
      PinsStay G₂ at_ (pinned (open₂ 8)) (x.1.1, x.1.2) (x.1.1, { x.1.2 with loc := { x.1.2.loc with
          zFd := z } })) :
    (zetaSeat Fr₂ b7 base d S.kRow (S.kRow * Fintype.card OnBytes.Slice.GE ^ (S.kRow - 1))
        ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7)
        (fun x x' => L₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 7 x)
        (zetaSeat Fr₂ b7 base d S.kRow (S.kRow * Fintype.card OnBytes.Slice.GE ^ (S.kRow - 1))
            ext).err ∧
      Err.Below (zetaSeat Fr₂ b7 base d S.kRow (S.kRow * Fintype.card OnBytes.Slice.GE ^ (S.kRow -
          1)) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨zeta_half₂_seat F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ b7 hb base d (H.zeta d hW).1 _
      (Nat.le_refl _) ext hsame hbase hpins,
    (H.zeta d hW).2.2 W Fr₂ (b7.retype : Block St₂ Unit) base⟩

/-- **AT THE KEY FILE's OWN TYPED SHAPE AND WRITTEN ROUNDS**: K14Rounds is k14_rounds_key, an
evaluation in Lean's kernel. -/
theorem zeta_half₂_key (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 6 = some (d.entry, d.kind))
    (b7 : Block St₂ Cl) (hb : ∀ d rs gs d', b7.decide d rs gs = .ok d' → _root_.Desc.K14.linZeta d
        rs = some d') (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → Iop.Tr (uLT (_root_.Run.ckP .two) [d]) → W → W)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base)
    (hpins : ∀ x, on₂ F Fr₂ G₂ at_ Lk6.AtPlan.keyFull.once.shape K₁ R enc rad a coll last₁ off₂ 7 x
        → ∀ z,
      PinsStay G₂ at_ (pinned (open₂ 8)) (x.1.1, x.1.2) (x.1.1, { x.1.2 with loc := { x.1.2.loc with
          zFd := z } })) :
    (zetaSeat Fr₂ b7 base d Lk6.AtPlan.keyFull.once.shape.kRow
          (Lk6.AtPlan.keyFull.once.shape.kRow * Fintype.card OnBytes.Slice.GE ^
              (Lk6.AtPlan.keyFull.once.shape.kRow - 1)) ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ Lk6.AtPlan.keyFull.once.shape K₁ R enc rad a coll last₁ off₂ 7)
        (fun x x' => L₂ F Fr₂ G₂ at_ Lk6.AtPlan.keyFull.once.shape K₁ R enc rad 8 x' →
          L₂ F Fr₂ G₂ at_ Lk6.AtPlan.keyFull.once.shape K₁ R enc rad 7 x)
        (zetaSeat Fr₂ b7 base d Lk6.AtPlan.keyFull.once.shape.kRow
          (Lk6.AtPlan.keyFull.once.shape.kRow * Fintype.card OnBytes.Slice.GE ^
              (Lk6.AtPlan.keyFull.once.shape.kRow - 1)) ext).err ∧
      Err.Below (zetaSeat Fr₂ b7 base d Lk6.AtPlan.keyFull.once.shape.kRow
          (Lk6.AtPlan.keyFull.once.shape.kRow * Fintype.card OnBytes.Slice.GE ^
              (Lk6.AtPlan.keyFull.once.shape.kRow - 1)) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  zeta_half₂_rounds F Fr₂ G₂ at_ _ K₁ R enc rad a coll last₁ off₂ k14_rounds_key d hW b7 hb base ext
    hsame hbase hpins

end

end Johnson.RunOne.KeyRows23
