-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointKey2.lean: the law of "LIN point" with the key's sort of lost points the
library's, AT TYPED DATA WHOSE MATRIX IS THE LIBRARY's OWN generator matrix
(OnBytes/Slice/LinkAt.lean: genOf, at codeOf of the program's code) on ONE range of places, the tail
first: so that a count of the bad points that is stated of such data fits without a turn.

Johnson/Desc/K14/Law/PointKey.lean has the same law at typed data whose matrix is the program's
generator row, read, on the sum of the message's and the tail's ranges. The two are tied by
Johnson/Desc/K14/Law/GenTie.lean: mulVec_tie.
  ixOf2           the typed data: v, the sample and the letters err, eM as in ixOf; G := genOf at
                  the code's sizes; the message's places stand behind the tail's; rank: a letter
                  over the one range.
  near2_iff       the library's NearW at ixOf2 and full2 is NearW at ixOf and fullOf.
  recRow2_iff     so is RecRow.
  BadX2, DecX2, TabX2   the library's bad points and decoder at ixOf2: that it returns a table;
                  which.
  good_of_notBad2 what not bad gives.
  point_goodInY2  **the law**: its premises on the key's sort: at every table and record without a
                  collision at the record's seed no more than ef points are bad; beside Prm the
                  stored table has no collision at the key's seeds.

What is not claimed. The two premises named last stay premises. The code has at most 2 ^ 32
positions: a premise. That BadX2 and BadX, DecX2 and DecX, or TabX2 and TabX, are one is NOT shown:
the decoders order tables by two letters rank over two types. The other premises are
PointKey.lean's. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointKey
import Johnson.Desc.K14.Law.GenTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- **The encoded index's typed data, with the library's own matrix.** err, eM, rank: letters. -/
def ixOf2 (S : FoldeqShape) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat) :
    Cb.LdIx GE (Fin (2 ^ S.index.code.logN)) (Fin (S.index.code.r + S.index.code.ell))
      (Fin S.index.code.ell) where
  v := S.index.v
  G := genOf (codeOf S.index.code)
  pl := Fin.natAdd S.index.code.r
  Z := sampleOf S.index (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err
  eM := eM
  rank := rank

/-- NearW at the two typed data. -/
theorem near2_iff (S : FoldeqShape) (ha : S.index.code.logN ≤ 32) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin S.index.code.ell ⊕ Fin S.index.code.r → GE) → Nat)
    (rank2 : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat)
    (e' : Nat) (w : Fin (2 ^ S.index.code.logN) → GE) (U : Nat → GE) :
    (ixOf2 S err eM rank2).NearW e' w (full2 S U) ↔
      (ixOf OnBytes.Model.Reading.gl S err eM rank).NearW e' w (fullOf S U) := by
  unfold Cb.LdIx.NearW
  have e : (ixOf2 S err eM rank2).G.mulVec (full2 S U) =
      (ixOf OnBytes.Model.Reading.gl S err eM rank).G.mulVec (fullOf S U) :=
    funext fun x => mulVec_tie S ha U x
  rw [e]

/-- The message part of the full message on one range. -/
theorem msg2_eq (S : FoldeqShape) (err eM : Nat)
    (rank2 : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat)
    (U : Nat → GE) (j : Fin S.index.code.ell) :
    (ixOf2 S err eM rank2).msg (full2 S U) j = U j.val := by
  show full2 S U (Fin.natAdd S.index.code.r j) = U j.val
  simp [full2]

/-- RecRow at the two typed data. -/
theorem recRow2_iff (S : FoldeqShape) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin S.index.code.ell ⊕ Fin S.index.code.r → GE) → Nat)
    (rank2 : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat)
    (rec : (ixOf OnBytes.Model.Reading.gl S err eM rank).Rec) (gam : Fin S.index.v → GE)
    (U : Nat → GE) :
    (ixOf2 S err eM rank2).RecRow rec gam (full2 S U) ↔
      (ixOf OnBytes.Model.Reading.gl S err eM rank).RecRow rec gam (fullOf S U) := by
  have e : (ixOf2 S err eM rank2).msg (full2 S U) =
      (ixOf OnBytes.Model.Reading.gl S err eM rank).msg (fullOf S U) :=
    funext fun j => msg2_eq S err eM rank2 U j
  unfold Cb.LdIx.RecRow
  rw [e]
  exact Iff.rfl

/-- The bad points of the fold at ixOf2. -/
def BadX2 (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (e' : Nat) (tab : Nat → List UInt64) (key : TableKey) (gam : Fin p.S.fold.index.v → GE) :
    Prop :=
  (ixOf2 p.S.fold err eM rank).Bad (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
    (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
      recOf p.S.fold.index fun k => OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) e' gam

/-- What the stored table decodes to at ixOf2, with the record: row r, place k; 0 where it does not
decode, and beyond a row's message. -/
noncomputable def TabX2 (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) (r k : Nat) : GE :=
  match (ixOf2 p.S.fold err eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
      (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
        recOf p.S.fold.index fun k => OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) with
  | some U => if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0
  | none => 0

/-- The stored table decodes at ixOf2, with the record. -/
def DecX2 (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) : Prop :=
  ((ixOf2 p.S.fold err eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
    (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
      recOf p.S.fold.index fun k =>
        OnBytes.Model.Reading.gl.val (key.record.getD k zeroE))).isSome = true

/-- **What not bad gives**, at ixOf2. -/
theorem good_of_notBad2 (p : Par) (ha : p.S.fold.index.code.logN ≤ 32) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (e' : Nat) (tab : Nat → List UInt64) (d : St) (m : Words GE)
    (gam : Fin p.S.fold.index.v → GE) (hi : p.S.fold.index.ok = true)
    (hroom : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.plain)
    (hfit : d.loc.key.fits p.S.fold.index = true)
    (hnb : ¬ BadX2 p err eM rank e' tab d.loc.key gam)
    (hg : (gamma p.S d.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam)
    (hnear : NearAt OnBytes.Model.Reading.gl p d m tab e')
    (hrec : RecAll OnBytes.Model.Reading.gl p d m) :
    DecX2 p err eM rank tab d.loc.key ∧
      UIsFold p.S.matrixRows p.S.kLo p.S.fold.index.v (TabX2 p err eM rank tab d.loc.key)
        (List.ofFn gam) (uOf d.loc m) := by
  have hN := (near_iff OnBytes.Model.Reading.gl p d m tab e' err eM fun _ => 0).1 hnear
  have hfc : (fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
      foldCol OnBytes.Model.Reading.gl p d tab x.val) =
      Cb.foldAll gam (tabF OnBytes.Model.Reading.gl p.S.fold.index tab) :=
    funext fun x => foldCol_eq OnBytes.Model.Reading.gl p d tab gam hg x
  rw [hfc] at hN
  have hN2 := (near2_iff p.S.fold ha err eM (fun _ => 0) rank e' _ (uOf d.loc m)).2 hN
  have hR := recRow_of_all OnBytes.Model.Reading.gl p d m err eM (fun _ => 0) gam hg hi hfit hrec
  have hR2 := (recRow2_iff p.S.fold err eM (fun _ => 0) rank _ gam (uOf d.loc m)).2 hR
  have hW : ¬ (ixOf2 p.S.fold err eM rank).Wrong
      (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
      (seedsFn OnBytes.Model.Reading.gl p.S.fold.index d.loc.key,
        recOf p.S.fold.index fun k =>
          OnBytes.Model.Reading.gl.val (d.loc.key.record.getD k zeroE)) gam
      (full2 p.S.fold (uOf d.loc m)) := fun hw => hnb ⟨_, hN2, hR2, hw⟩
  unfold Cb.LdIx.Wrong at hW
  push Not at hW
  obtain ⟨U, hU, hmsg⟩ := hW
  refine ⟨by unfold DecX2; rw [hU]; rfl, ?_⟩
  intro k hk
  have hkl : k < p.S.fold.index.code.ell :=
    Nat.lt_of_lt_of_le hk (Nat.le_trans hroom (Nat.sub_le _ _))
  have e := congrFun hmsg ⟨k, hkl⟩
  rw [msg2_eq] at e
  have e2 : uOf d.loc m k = Cb.foldV gam U ⟨k, hkl⟩ := e
  rw [e2]
  unfold Cb.foldV
  rw [sum_bits]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqK_ofFn]
  unfold TabX2
  rw [hU]
  show _ = _ * (if h : k < p.S.fold.index.code.ell then
    U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0)
  rw [dif_pos hkl]
  rfl

variable {W : Type} {F : Frame}

/-- **The law of "LIN point" at the typed data with the library's own matrix.** -/
theorem point_goodInY2 (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
    (Prm Prm' : St × F.E.Str → Prop) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat) (base : Nat) (d : RDT)
    {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (ef e : Nat)
    (he : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e)
    (hbad : ∀ f rec, ¬ (ixOf2 P.par.S.fold err eM rank).Coll f rec.1 →
      cnt ((ixOf2 P.par.S.fold err eM rank).Bad f rec e') ≤ ef)
    (hcoll : ∀ a : St × F.E.Str, Prm a → ¬ (ixOf2 P.par.S.fold err eM rank).Coll
      (tabF OnBytes.Model.Reading.gl P.par.S.fold.index (tabOf a.2))
      (seedsFn OnBytes.Model.Reading.gl P.par.S.fold.index a.1.loc.key))
    (hi : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hfit : ∀ a : St × F.E.Str, Prm a → a.1.loc.key.fits P.par.S.fold.index = true)
    (c1 : Carries (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e) Pin Prm Prm')
    (hdetV : ∀ (x : St × F.E.Str) w w', Prm x → Pin x w → Pin x w' → wv w = wv w') :
    (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).GoodIn
      (fun a => Prm a) (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm' a)
      (fun a w => Pin a w ∧ DecX2 P.par err eM rank (tabOf a.2) a.1.loc.key ∧
        VIs P.par.S g (TabX2 P.par err eM rank (tabOf a.2) a.1.loc.key) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w))) :=
  point_goodIn rg wv Pin Prm Prm' P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS g e' base d hd
    (fun a => BadX2 P.par err eM rank e' (tabOf a.2) a.1.loc.key)
    (fun a => TabX2 P.par err eM rank (tabOf a.2) a.1.loc.key)
    (fun a => DecX2 P.par err eM rank (tabOf a.2) a.1.loc.key) ef e he
    (fun a hp => hbad _ _ (hcoll a hp))
    (fun a x m gam hp hnb hg hk _ hnear hrec => by
      have h := good_of_notBad2 P.par ha err eM rank e' (tabOf a.2) x m gam hi hroom
        (by rw [hk]; exact hfit a hp) (by rw [hk]; exact hnb) hg hnear hrec
      rw [hk] at h
      exact h)
    c1 hdetV

end Desc.K14.Law
