-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Tiles.lean: the laws of the shared chain's blocks in the form of the rule of
composition TILE: what stands behind one block is what stands in front of the next (EachGoodIn), on
the two stretches of K14's own blocks that no sending parts.

  Front5, On6     the places up to the note behind o_omega's sending have said yes and have led to
                  this record; with the joinings' yes that is On7.
  tabOf_imp       a stretch leaves the stored table as it is.
  NearAt.back     the claim "near" goes back through a block that goes onward, leaves the small
                  record and leaves the stored table.
  tile34          **"(rec_gamma)", "LOC"**: promises On4 and Prm at all three borders; relations:
                  Base and near · Base and near · Base.
  tile678         **the joinings, "LIN zeta", "SPLIT"**: promises On6, On7, On8, On9, each with Prm;
                  relations: Base and omega_col = col_psi_lo(u) · the same · Base and (fold)'s
                  equation · Base.

What is not claimed. THE TWO STRETCHES DO NOT MEET: between them stands the sending of o_omega, in
front of the first the sending of o_u and "LIN point": these three have no law here. The premises of
the five laws stay, at each piece, EACH UNDER THE PROMISE IN FRONT OF THAT PIECE ALONE:
at a yes the pin goes back and the promise Prm stays; the pin
determines the words that are read; the written rounds send and draw as declared; the round of "LOC"
opens no tree. Pin and Prm are letters; within a tile Prm is ONE letter at all its borders: a
promise that names a piece's base cannot be that: the row with a letter a border is
Johnson/Desc/K14/Law/Borders.lean's. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.OnFront
import Johnson.Desc.K14.Law.StoredCols
import Johnson.Desc.K14.Law.ZetaRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)
open _root_.Run.PQ (CK)

/-- **The places up to the note behind o_omega's sending have said yes.** -/
structure Front5 (p : Par) (d0 d2 d3 d5 : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) : Prop where
  twoCodes : p.S.sharedSplitNeeded = true
  run : ∃ (d1 a1 a2 d4 b1 b2 : St) (rs1 rs3 : List Fmt.RoundView)
    (ftU ftO : Nat) (sentU : Array OracleNotice) (idsU idsO : Array Nat),
    linPoint p d0 rs1 = some d1 ∧
    withU p.S = some sentU ∧ recvP ftU d1 sentU = some (idsU, a1) ∧
    Onward a1 a2 ∧ a2.loc = a1.loc ∧ behindU p a2 idsU = some d2 ∧
    laysRec p d2 rs3 = some d3 ∧ loc p d3 [r4] [cols] = some d4 ∧
    recvP ftO d4 (withOmega p.S) = some (idsO, b1) ∧
    Onward b1 b2 ∧ b2.loc = b1.loc ∧ behindOmega p b2 idsO = some d5

/-- With the joinings' yes the front is whole. -/
theorem Front5.toFront {p : Par} {d0 d2 d3 d5 : St} {r4 : Fmt.RoundView}
    {cols : List (Nat × List UInt64)} (h : Front5 p d0 d2 d3 d5 r4 cols) (d6 : St)
    (rs6 : List Fmt.RoundView) (h6 : joins p d5 rs6 = some d6) : SharedFront p d0 d2 d3 d6 r4 cols := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, rs1, rs3, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5⟩ := h
  exact ⟨hS, d1, a1, a2, d4, b1, b2, d5, rs1, rs3, rs6, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6⟩

variable {W : Type} {F : Frame}

/-- The places up to the note behind o_omega's sending have said yes and have led to this record. -/
def On6 (p : Par) (a : St × F.E.Str) : Prop :=
  ∃ d0 d2 d3 r4 cols, Front5 p d0 d2 d3 a.1 r4 cols

/-- A stretch leaves the stored table as it is. -/
theorem tabOf_imp {C : CK} {S Cl : Type} (pc : Piece C F S Cl W) (y : F.E.Str)
    (τ : Tr (uLT C pc.ds)) : tabOf (pc.ior.imp y τ) = tabOf y := rfl

/-- "Near" goes back through a block that goes onward, leaves the small record and leaves the stored
table. -/
theorem NearAt.back {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (p : Par) (d d' : St)
    (m : Words K) (tab : Nat → List UInt64) (e' : Nat) (l : d'.loc = d.loc)
    (h : NearAt ρ p d' m tab e') : NearAt ρ p d m tab e' := by
  unfold NearAt LocAt at h ⊢
  rw [l] at h
  exact h

variable (rg : W → Words GE) (Pin : St × F.E.Str → W → Prop) (Prm : St × F.E.Str → Prop)

/-- **"(rec_gamma)" and "LOC" tile.** -/
theorem tile34 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (p3 : Piece (ckP .two) F St Unit W) (hp3 : p3.b = b3) (hext3 : ∀ a τ w, p3.ext a τ w = w)
    (hback3 : ∀ a τ b w, On4 P.par a → Prm a → p3.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep3 : ∀ a τ b, On4 P.par a → Prm a → p3.ior.red.out a τ = some b → Prm b)
    (base : Nat) (d : RDT) {ns n : Nat}
    (hd : SendsDraws (toRD d) ns 0 n P.par.S.fold.index.code.logN) (ho : d.opens = [])
    (e' e : Nat) (he : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (hback4 : ∀ x τ b w, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Pin b w → Pin x w)
    (hkeep4 : ∀ x τ b, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Prm b)
    (hdet : ∀ (x : St × F.E.Str) w w', On4 P.par x → Prm x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oU.oracle (rg w) (rg w')) :
    EachGoodIn (fun _ x => On4 P.par x ∧ Prm x)
      (fun i x w => Base OnBytes.Model.Reading.gl rg Pin x w ∧
        (i < 2 → NearAt OnBytes.Model.Reading.gl P.par x.1 (rg w) (tabOf x.2) e')) 0
      [p3, posPiece (W := W) (F := F) b4 base d P.par.S.fold.index.code.logN n e] := by
  refine ⟨?_, ?_, trivial⟩
  · have h := rec_goodIn3' OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p3 hp3
      hext3 Prm hback3 (fun x m => NearAt OnBytes.Model.Reading.gl P.par x.1 m (tabOf x.2) e')
      (fun a τ b m hy _ l hq => by
        have hq' : NearAt OnBytes.Model.Reading.gl P.par b.1 m (tabOf b.2) e' := hq
        rw [hy, tabOf_imp] at hq'
        exact NearAt.back _ _ _ _ _ _ _ l hq')
    exact fun a ha => Doomed.mono _ _ (fun τ hτ b hb =>
      ⟨⟨(hτ b hb).1, hkeep3 a τ b ha.1 ha.2 hb⟩, fun w hw =>
      ⟨((hτ b hb).2 w ⟨hw.1, hw.2 (by decide)⟩).1,
        fun _ => ((hτ b hb).2 w ⟨hw.1, hw.2 (by decide)⟩).2⟩⟩) (h a ha)
  · have h := loc_goodIn4' Pin rg P b1 b2 b3 b4 b5 b6 b7 b8 hbl base d hd ho e' e he Prm Prm
      hback4 hkeep4 hdet
    exact fun a ha => Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw =>
      ⟨((hτ b hb).2 w hw.1).1, fun _ => ((hτ b hb).2 w hw.1).2⟩⟩) (h a ha)

/-- The promise at border i of the second stretch, from 0. -/
def onB (p : Par) : Nat → St × F.E.Str → Prop
  | 0 => On6 p
  | 1 => On7 p
  | 2 => On8 p
  | _ => On9 p

/-- The claim beside Base at border i of the second stretch, from 0. -/
def claimB (S : LinShape) : Nat → St → Words GE → Prop
  | 0 => OmegaCol OnBytes.Model.Reading.gl S
  | 1 => OmegaCol OnBytes.Model.Reading.gl S
  | 2 => FoldAt OnBytes.Model.Reading.gl S
  | _ => fun _ _ => True

/-- **The joinings, "LIN zeta" and "SPLIT" tile.** -/
theorem tile678 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (p6 p8 : Piece (ckP .two) F St Unit W) (hp6 : p6.b = b6) (hp8 : p8.b = b8)
    (hext6 : ∀ a τ w, p6.ext a τ w = w) (hext8 : ∀ a τ w, p8.ext a τ w = w)
    (hback6 : ∀ a τ b w, On6 P.par a → Prm a → p6.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hback8 : ∀ a τ b w, On8 P.par a → Prm a → p8.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep6 : ∀ a τ b, On6 P.par a → Prm a → p6.ior.red.out a τ = some b → Prm b)
    (hkeep8 : ∀ a τ b, On8 P.par a → Prm a → p8.ior.red.out a τ = some b → Prm b)
    (base : Nat) (d : RDT) {ns a : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kRow 0 a) (e : Nat)
    (he : P.par.S.kRow * Fintype.card GE ^ (P.par.S.kRow - 1) ≤ e)
    (hback7 : ∀ x τ b w, On7 P.par x → Prm x →
      (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e).ior.red.out x τ = some b →
      Pin b w → Pin x w)
    (hkeep7 : ∀ x τ b, On7 P.par x → Prm x →
      (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e).ior.red.out x τ = some b → Prm b)
    (hdet : ∀ (x : St × F.E.Str) w w', On7 P.par x → Prm x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oOmega (rg w) (rg w') ∧ AgreeOn x.1.loc.oU.oracle (rg w) (rg w')) :
    EachGoodIn (fun i x => onB P.par i x ∧ Prm x)
      (fun i x w => Base OnBytes.Model.Reading.gl rg Pin x w ∧ claimB P.par.S i x.1 (rg w)) 0
      [p6, vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e, p8] := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · have h := joins_goodIn6 OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p6 hp6
      hext6 (fun x => On6 P.par x ∧ Prm x) (On7 P.par)
      (fun a τ b w ha => hback6 a τ b w ha.1 ha.2)
      (fun x y rs hx h => by
        obtain ⟨⟨d0, d2, d3, r4, cols, hF⟩, _⟩ := hx
        exact ⟨d0, d2, d3, r4, cols, hF.toFront y.1 rs h⟩)
      (fun x m => OmegaCol OnBytes.Model.Reading.gl P.par.S x.1 m)
      (fun x τ y m _ o l hq => OmegaCol.back _ _ _ _ _ o l hq)
    exact fun a ha => Doomed.mono _ _ (fun τ hτ b hb =>
      ⟨⟨(hτ b hb).1, hkeep6 a τ b ha.1 ha.2 hb⟩, (hτ b hb).2⟩) (h a ha)
  · exact zeta_goodIn7 rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl base d hd e he Prm Prm hback7 hkeep7
      hdet
  · have h := split_goodIn8 OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p8 hp8
      hext8 Prm Prm hback8 hkeep8
    exact fun x hx => Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw =>
      (hτ b hb).2 w hw.1⟩) (h x hx)

end Desc.K14.Law
