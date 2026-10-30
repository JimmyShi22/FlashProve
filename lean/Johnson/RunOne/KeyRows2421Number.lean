-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRows2421Number.lean: ROWS 2.4 («LOC») AND 2.1 («LIN
point») OF THE KEY FILE's TABLE OF JOINTS, THE CHANCE's HALVES (Johnson/RunOne/KeyRow24At.lean:
loc_back₂_at · KeyRow21At.lean: point_back₂_at), EACH WITH ITS NUMBER BESIDE IT: the seat's written
errors are shares of at most 2^-128 of the round's written challenges: both from ONE premise on the
written round: it has the entry and kind of a written list's round number 3 | 0, at which K14Rounds
holds (Johnson/Goal/Numbers/K14RoundsAt.lean: one comparison of natural
numbers a round). After the pattern of row 2.7's (Johnson/RunOne/KeyRow27Number.lean).
ON EMPTINESS: as the rows' heads: NO MEMBER OF on₂ … 4 | on₂ … 1 IS SHOWN BY ANYBODY: THEY MAY BE
TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNT AS CLOSING NOTHING.
OBJECT: posAt | vecAt at the law's own count · USER: keeps₂_of_halves', then
keeps_same_cap (Err.Below to the cap: le_cap_of_below_inv) · LETTERS: the rows'; Wr rd cmax work:
K14Rounds'.
  loc_back₂_rounds     at any shape and written list with K14Rounds AT THE TABLES' OWN LETTER rad
  loc_back₂_key        at the key file's typed shape keyFull.once.shape, the written rounds
    dryKeyFull.2.1 of a key file's second chain AND rad := recordRadius, where K14Rounds is
    k14_rounds_key: an evaluation in Lean's kernel. 32 OF THE 128 BITS AT THIS ROUND ARE WORK.
  point_back₂_rounds   the like at round 0, at ef ≤ cmax |K| ^ 10. NO BIT IS WORK.
What is not claimed. That the frame's data hold, at the maker's pieces number 4 | 1 of the shared
chain, a round with that entry and kind (hW), which opens no tree (ho): the frame's. That the
tables' letters S | rad are keyFull.once.shape | recordRadius at the seat. The other premises of
loc_back₂_at | point_back₂_at stay. No soundness of a verifier.

-/
import Johnson.RunOne.KeyRow24At
import Johnson.RunOne.KeyRow21At
import Johnson.Goal.Numbers.K14RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open _root_.Prob (cnt)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (K14Rounds atW k14_rounds_key cMax posAt vecAt idlePiece ixOf2)
open VerifiableInference.Desc.K13.Law (ρg)
open scoped ENNReal

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **ROW 2.4, THE CHANCE's HALF, WITH ITS NUMBER.** -/
theorem loc_back₂_rounds {K : Type} [Field K] (ρ : Model.Reading K) {Wr : OnBytes.Params.Rounds}
    {cmax work : Nat} (H : K14Rounds p.S Wr rad cmax work)
    (d : RDT) (hW : atW Wr 3 = some (d.entry, d.kind)) (ho : d.opens = [])
    (b : Block (P₂ × St₂) Cl) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.loc p z.2 rs gs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (henc : EncIs ρ p.S.fold enc) (hA : p.S.fold.index.code.logN ≤ Fr₂.a) :
    (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
        p.S.fold.index.code.logN - rad - 1) ^ p.S.fold.columns) ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 4)
        (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 5 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 4 x)
        (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
            p.S.fold.index.code.logN - rad - 1) ^ p.S.fold.columns) ext).err ∧
      Err.Below (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
          p.S.fold.index.code.logN - rad - 1) ^ p.S.fold.columns) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨loc_back₂_at F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρ b base d (H.loc d hW).1 ho _
      (Nat.le_refl _) ext hl hbase hsame hpins henc hA,
    (H.loc d hW).2.2 W Fr₂ (idlePiece (ckP .two) Fr₂ W 0).b base⟩

variable (err eM : Nat) (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r +
    p.S.fold.index.code.ell) → Cb.Gl.E) → Nat)

/-- **ROW 2.1, THE CHANCE's HALF, WITH ITS NUMBER.** -/
theorem point_back₂_rounds {Wr : OnBytes.Params.Rounds} {rd cmax work : Nat} (H : K14Rounds p.S Wr
    rd cmax work)
    (d : RDT) (hW : atW Wr 0 = some (d.entry, d.kind))
    (b : Block (P₂ × St₂) Cl) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2 rs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg p.S.fold enc) (hK : K₁.lin = p.S)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (ef : Nat) (hef : ef ≤ cmax * Fintype.card Cb.Gl.E ^ 10)
    (hbad : ∀ f rec, ¬ (ixOf2 p.S.fold err eM rank).Coll f rec.1 → cnt ((ixOf2 p.S.fold err eM
        rank).Bad f rec rad) ≤ ef)
    (hcoll : CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hdec : DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hties : PileTies F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂) :
    (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (ef * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card Cb.Gl.E
              ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1)
        (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 2 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 1 x)
        (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (ef * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card Cb.Gl.E
              ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).err ∧
      Err.Below (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (ef * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card Cb.Gl.E
              ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨point_back₂_at F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank b base d (H.point d
      hW).1 ext hl hbase hsame hpins hof henc hK
      ha ef _ (Nat.le_refl _) hbad hcoll hdec hties, by
    have point : ∀ q : Nat, Fintype.card OnBytes.Slice.GE = q → ef ≤ cmax * q ^ 10 →
        Err.Below (_root_.Desc.K14.Law.vecPiece (W := W) (F := Fr₂) (idlePiece (ckP .two) Fr₂ W 0).b
          base d p.S.kCol (ef * q ^ p.S.kLo + p.S.kCol * q ^ (p.S.kCol - 1))).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun q hq hq10 => by
      subst hq
      exact (H.point d hW).2.2 W Fr₂ (idlePiece (ckP .two) Fr₂ W 0).b base ef hq10
    have below : ∀ q : Nat,
        Err.Below (_root_.Desc.K14.Law.vecPiece (W := W) (F := Fr₂) (idlePiece (ckP .two) Fr₂ W 0).b
          base d p.S.kCol (ef * q ^ p.S.kLo + p.S.kCol * q ^ (p.S.kCol - 1))).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) →
        Err.Below (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (ef * q ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * q ^ (p.S.kLo + p.S.fold.index.v - 1))
          ext).err ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun _ h => h
    exact below (Fintype.card Cb.Gl.E) (point (Fintype.card Cb.Gl.E) rfl hef)⟩

end

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **ROW 2.4 AT THE KEY FILE's OWN TYPED SHAPE, WRITTEN ROUNDS AND RADIUS**: K14Rounds is
k14_rounds_key, an evaluation in Lean's kernel. -/
theorem loc_back₂_key {K : Type} [Field K] (ρ : Model.Reading K) (hS : p.S =
    Lk6.AtPlan.keyFull.once.shape)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 3 = some (d.entry, d.kind)) (ho : d.opens = [])
    (b : Block (P₂ × St₂) Cl) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.loc p z.2 rs gs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (henc : EncIs ρ p.S.fold enc) (hA : p.S.fold.index.code.logN ≤ Fr₂.a) :
    (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
        p.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ p.S.fold.columns)
        ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ p.S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
        (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc OnBytes.Params.recordRadius 5 x' → L₂ F Fr₂ G₂ at_
            p.S K₁ R enc OnBytes.Params.recordRadius 4 x)
        (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
            p.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ p.S.fold.columns) ext).err
            ∧
      Err.Below (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns ((2 ^
          p.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^ p.S.fold.columns) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  loc_back₂_rounds F Fr₂ G₂ at_ p K₁ R enc _ a coll last₁ off₂ ρ (hS ▸ k14_rounds_key) d hW ho b
      base ext hl hbase hsame hpins henc hA

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.loc_back₂_rounds
#print axioms Johnson.RunOne.KeyRows23.point_back₂_rounds
#print axioms Johnson.RunOne.KeyRows23.loc_back₂_key
