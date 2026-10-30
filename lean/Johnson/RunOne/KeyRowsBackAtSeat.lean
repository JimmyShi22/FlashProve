-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsBackAtSeat.lean: FOUR ROWS OF THE KEY
FILE's TABLE OF JOINTS (2.1 · 2.2 · 2.4 · 2.5) AT THE CONSTANTS THAT THE SEAT CALLS, EVERYTHING THAT
IS PAID LAID IN: the tables' own reading BaseSt.h₂ (samePins_h₂ | smpGrows_h₂) · K14's own blocks as
the maker holds them (held b; hl_… | hS_…) · at 2.1: the tables' own plan₁ one and last₁At one
(pileTies_at) · at 2.1 | 2.4: the key file's typed shape, written rounds and radius (k14_rounds_key
| k14_point_key: the numbers and the count of the bad points). SO THAT WHAT IS LEFT OF EACH ROW
STANDS IN ONE BINDER LIST.
ON EMPTINESS: NO MEMBER OF on₂ … 1 | 2 | 4 | 5 IS SHOWN: EVERY LAW HERE MAY BE TRUE AND
EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING.
OBJECT: posAt | vecAt | sendPiece at held b, b.decide = bᵢ.decide, blocks Q = some [b1, …, b8] ·
USER: keeps₂_of_halves' (2.1 | 2.4) · keepsAt_of_law₂ (2.2 | 2.5) · LETTERS: T : BaseSt · Q : P14 ·
one : OneTime · the tables' others.
  loc_back₂_seat     LEFT: hS (the shape is the key file's) · hW | ho (the frame's data) · hbase ·
    hsame · henc (encOf is a member) · hA (nobody's)
  point_back₂_seat   LEFT: hS · hW · hbase · hsame · hof · henc · hK · the plan has a stage · rad ≤
    eM < the distance · CollTie · DecTie
  keeps₂_send2_seat | keeps₂_send5_seat   LEFT: the sending kind's eight at the key file's numbers
    with fOf | fIn | hf · hbase · (2.5: hsame) · hnew · yes (the promise's half) · tieS · three
    public facts on the place
Nothing on soundness by itself.
-/
import Johnson.RunOne.KeyRow21Key
import Johnson.RunOne.KeyPileTies
import Johnson.RunOne.KeyReadsH2
import Johnson.RunOne.KeyRowsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open OnBytes.Slice hiding ofF tabOf
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt
    errPort)
open Johnson.Pack (portOmZ)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)
open _root_.Desc.K14.Law (atW posAt vecAt efReal isSend_of_blocks)
open VerifiableInference.Desc.K13.Law (ρg)
open Johnson.RunOne.KeyRows1 (plan₁)
open scoped ENNReal

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp
           Rec) (at_ : Where)
  (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1, b2, b3, b4, b5,
      b6, b7, b8]) (b : Block St₂ Cl)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
include hbl

/-- **ROW 2.4 AT THE SEAT.** -/
theorem loc_back₂_seat {K : Type} [Field K] (ρ : Model.Reading K) (hd4 : b.decide = b4.decide) (hS :
    Q.par.S = Lk6.AtPlan.keyFull.once.shape)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 3 = some (d.entry, d.kind)) (ho : d.opens = [])
        (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (henc : EncIs ρ Q.par.S.fold enc) (hA : Q.par.S.fold.index.code.logN ≤ Fr₂.a) :
    (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
        Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^
        Q.par.S.fold.columns) ext).ior.red.Leads
        (on₂ F Fr₂ T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
        (fun x x' => L₂ F Fr₂ T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius 5 x' → L₂ F Fr₂
            T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius 4 x)
        (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
            Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius -
            1) ^ Q.par.S.fold.columns) ext).err ∧
      Err.Below (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
          Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1)
          ^ Q.par.S.fold.columns) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  loc_back₂_key F Fr₂ T.h₂ at_ Q.par K₁ R enc a coll last₁ off₂ ρ hS d hW ho (held b) base ext
    (hl_loc Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd4) hbase hsame (samePins_h₂ T) henc hA

/-- **ROW 2.1 AT THE SEAT.** -/
theorem point_back₂_seat (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (hK : one.lin =
    Q.par.S)
    (err eM : Nat) (rank : ((Fin Q.par.S.fold.index.v → Bool) → Fin (Q.par.S.fold.index.code.r +
        Q.par.S.fold.index.code.ell) → Cb.Gl.E) → Nat)
    (hd1 : b.decide = b1.decide) (hS : Q.par.S = Lk6.AtPlan.keyFull.once.shape)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 0 = some (d.entry, d.kind)) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg Q.par.S.fold enc)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ T.h₂ at_ Q.par (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ err
        eM rank)
    (hdec : DecTie F Fr₂ T.h₂ at_ Q.par (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ err
        eM rank) :
    (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d (Q.par.S.kLo + Q.par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ Q.par.S.kLo + (Q.par.S.kLo + Q.par.S.fold.index.v) *
              Fintype.card Cb.Gl.E ^ (Q.par.S.kLo + Q.par.S.fold.index.v - 1)) ext).ior.red.Leads
        (on₂ F Fr₂ T.h₂ at_ Q.par.S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ 1)
        (fun x x' => L₂ F Fr₂ T.h₂ at_ Q.par.S (plan₁ one) R enc 2852142980 2 x' → L₂ F Fr₂ T.h₂ at_
            Q.par.S (plan₁ one) R enc 2852142980 1 x)
        (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d (Q.par.S.kLo + Q.par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ Q.par.S.kLo + (Q.par.S.kLo + Q.par.S.fold.index.v) *
              Fintype.card Cb.Gl.E ^ (Q.par.S.kLo + Q.par.S.fold.index.v - 1)) ext).err ∧
      Err.Below (vecAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d (Q.par.S.kLo +
          Q.par.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ Q.par.S.kLo + (Q.par.S.kLo + Q.par.S.fold.index.v) *
              Fintype.card Cb.Gl.E ^ (Q.par.S.kLo + Q.par.S.fold.index.v - 1)) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  point_back₂_key F Fr₂ T.h₂ at_ Q.par (plan₁ one) R enc a coll (last₁At one) off₂ err eM rank hS d
      hW (held b) base ext
    (hl_point Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd1) hbase hsame (samePins_h₂ T) hof henc hK hle hM
        hcoll hdec
    (pileTies_at F Fr₂ T.h₂ at_ Q.par R enc 2852142980 a coll off₂ one hst)

end

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp
           Rec) (at_ : Where)
  (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1, b2, b3, b4, b5,
      b6, b7, b8]) (b : Block St₂ Cl)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
include hbl

/-- **ROW 2.2 AT THE SEAT.** -/
theorem keeps₂_send2_seat (hd2 : b.decide = b2.decide) (sentU : Array OracleNotice) (hU : withU Q.S
    = some sentU)
    (P₁ : VerifiableInference.Desc.K1.Par) (hP₁ : P₁ = parK1 Q 2 "o_u and the first mask" sentU)
        (base : Nat) (d₁ d₂ : RDT)
    (radP : Nat → Nat) (hC : condPort P₁ radP = true) (h1 : P₁.seeds = 1)
    (hpl : PlainDraws (_root_.Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (_root_.Fmt.dsOf d₁.entry
        d₁.kind) = P₁.coordinates + 1)
    (hP : nP (_root_.Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (_root_.Fmt.dsOf d₁.entry d₁.kind)
        P₁.coordinates) (hl64 : d₁.entry.logN ≤ 64)
    (e : Nat) (he : errPort P₁ radP ≤ e)
    (fOf : Fr₂.E.Str → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (fIn : Fr₂.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂
        P₁.coordinates e).ior.imp y τ) = fIn y τ.1)
    (hbase : ∀ j ∈ pinned (open₂ 2), (at_ j).1 < base)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) x
        → (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂ P₁.coordinates
        e).ior.red.out x τ = some x' → New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit (held b : Block (P₂ × St₂) Cl).rounds rs = true → (held b :
        Block (P₂ × St₂) Cl).decide z (rs.map noDigest) gs = .ok z' → StrsStay F at_ (open₂ 2) y y'
        → New y' →
      onAt F T.h₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 2
          d)) (Free₂ F T.h₂ at_ S K₁ R coll last₁ off₂ 2) (open₂ 2) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 z'.2) = true ∧ Free₂ F T.h₂ at_ S K₁ R coll last₁
          off₂ 3 z' y')
    (hlen : (shapesOf P₁).length = 2) (k₀ : Fin (shapesOf P₁).length) (hk₀ : sampledAt P₁ k₀) (hk :
        k₀.val = 0)
    (tieS : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 2 →
      Sealed P₁.codes (shapeAt P₁ k₀) (radP k₀.val) (fOf x'.2 k₀) x'.1.2.st 0 →
      hasSmp T.h₂ (at_ 3).1 (at_ 3).2 x'.1 = true ∧ NoColl F T.h₂ (at_ 3).1 (at_ 3).2 x'.1 (strsOf
          Fr₂ x'.2)) :
    (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂ P₁.coordinates
        e).ior.red.Keeps (on₂ F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) (on₂ F Fr₂ T.h₂ at_
        S K₁ R enc rad a coll last₁ off₂ 3) (L₂ F Fr₂ T.h₂ at_ S K₁ R enc rad 2) (L₂ F Fr₂ T.h₂ at_
        S K₁ R enc rad 3) (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂
        P₁.coordinates e).err := by
  have hS : IsSend P₁ (fun z : P₂ × St₂ => z.2.st) (held b : Block (P₂ × St₂) Cl) := by
    obtain ⟨sentU', hU', h⟩ := hS_sends (P := P₂) Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2
    obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
    rw [hP₁]
    exact h
  exact keeps₂_send2_at F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ (held b) base d₁ d₂ P₁ radP
      hC h1 hS hpl hE hP hz hl64 e he fOf fIn hf
    (hl_send2 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2) hbase (smpGrows_h₂ T) New hnew yes hlen k₀ hk₀ hk
        tieS

/-- **ROW 2.5 AT THE SEAT.** -/
theorem keeps₂_send5_seat {K : Type} [Field K] (ρ : Model.Reading K) (hsame : ∀ x y, R.same x y ↔
    ρ.val x = ρ.val y) (hd5 : b.decide = b5.decide)
    (P₁ : VerifiableInference.Desc.K1.Par) (hP₁ : P₁ = parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))
        (base : Nat) (d₁ d₂ : RDT)
    (radP : Nat → Nat) (hC : condPort P₁ radP = true) (h1 : P₁.seeds = 1)
    (hpl : PlainDraws (_root_.Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (_root_.Fmt.dsOf d₁.entry
        d₁.kind) = P₁.coordinates + 1)
    (hP : nP (_root_.Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (_root_.Fmt.dsOf d₁.entry d₁.kind)
        P₁.coordinates) (hl64 : d₁.entry.logN ≤ 64)
    (e : Nat) (he : errPort P₁ radP ≤ e)
    (fOf : Fr₂.E.Str → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (fIn : Fr₂.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂
        P₁.coordinates e).ior.imp y τ) = fIn y τ.1)
    (hbase : ∀ j ∈ pinned (open₂ 5), (at_ j).1 < base)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) x
        → (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂ P₁.coordinates
        e).ior.red.out x τ = some x' → New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit (held b : Block (P₂ × St₂) Cl).rounds rs = true → (held b :
        Block (P₂ × St₂) Cl).decide z (rs.map noDigest) gs = .ok z' → StrsStay F at_ (open₂ 5) y y'
        → New y' →
      onAt F T.h₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 5
          d)) (Free₂ F T.h₂ at_ S K₁ R coll last₁ off₂ 5) (open₂ 5) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 z'.2) = true ∧ Free₂ F T.h₂ at_ S K₁ R coll last₁
          off₂ 6 z' y')
    (hlen : (shapesOf P₁).length = 2) (k₄ k₅ : Fin (shapesOf P₁).length) (hk₄ : sampledAt P₁ k₄)
        (hk₅ : sampledAt P₁ k₅) (h4 : k₄.val = 0) (h5 : k₅.val = 1)
    (tie4 : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 4 →
      Sealed P₁.codes (shapeAt P₁ k₄) (radP k₄.val) (fOf x'.2 k₄) x'.1.2.st 2 →
      hasSmp T.h₂ (at_ 4).1 (at_ 4).2 x'.1 = true ∧ NoColl F T.h₂ (at_ 4).1 (at_ 4).2 x'.1 (strsOf
          Fr₂ x'.2))
    (tie5 : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 4 →
      Sealed P₁.codes (shapeAt P₁ k₅) (radP k₅.val) (fOf x'.2 k₅) x'.1.2.st 3 →
      hasSmp T.h₂ (at_ 5).1 (at_ 5).2 x'.1 = true ∧ NoColl F T.h₂ (at_ 5).1 (at_ 5).2 x'.1 (strsOf
          Fr₂ x'.2)) :
    (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂ P₁.coordinates
        e).ior.red.Keeps (on₂ F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) (on₂ F Fr₂ T.h₂ at_
        S K₁ R enc rad a coll last₁ off₂ 6) (L₂ F Fr₂ T.h₂ at_ S K₁ R enc rad 5) (L₂ F Fr₂ T.h₂ at_
        S K₁ R enc rad 6) (sendPiece (W := W) (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d₁ d₂
        P₁.coordinates e).err := by
  have hS : IsSend P₁ (fun z : P₂ × St₂ => z.2.st) (held b : Block (P₂ × St₂) Cl) := by
    rw [hP₁]
    exact hS_send5 (P := P₂) Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5
  exact keeps₂_send5_at F Fr₂ T.h₂ at_ S K₁ R enc rad a coll last₁ off₂ ρ hsame (held b) base d₁ d₂
      P₁ radP hC h1 hS hpl hE hP hz hl64 e he fOf fIn hf
    (hl_send5 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5) hbase (smpGrows_h₂ T) New hnew yes hlen k₄ k₅ hk₄
        hk₅ h4 h5 tie4 tie5

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.loc_back₂_seat
#print axioms Johnson.RunOne.KeyRows23.point_back₂_seat
#print axioms Johnson.RunOne.KeyRows23.keeps₂_send2_seat
#print axioms Johnson.RunOne.KeyRows23.keeps₂_send5_seat
