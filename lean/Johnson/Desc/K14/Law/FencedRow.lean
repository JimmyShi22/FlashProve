--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/FencedRow.lean: **THE ROW OF THE EIGHT, APPLIED**: all eight blocks of the
shared chain's place as one row of the rule of composition (EachGoodIn), with the two letters Pin
and Prm of Johnson/Desc/K14/Law/Eight.lean FILLED: Pin := the functional pin at a decoder; Prm i :=
the fence at the base of the piece behind border i, and PrmK. Every premise of the row that names
Pin or Prm is PAID here; what stays is listed below.

  QU, QO          the sending kind's parameters at "send o_u" and at "send o_omega".
  baseAt          the base of the piece behind border i: B0 in front of "LIN point" and of "send
                  o_u"; B0 + tU up to "send o_omega"; B0 + tU + tO behind it. tU, tO: the trees that
                  the two sendings' stretches list.
  PrmD            the promise's letter at border i: PrmAt (Johnson/Desc/K14/Law/Fenced.lean) at
                  baseAt i.
  row1to8_fenced  **the row**, at any decoders D and DV that meet the fence's two conditions.
  row1to8_decoded **the row at decoders that read the trees**, in their general form (decOf,
                  decVOf): the two conditions are paid; the other vector's decoder reads the oracle
                  strings (the stored table; the trees below lo) and, of the record, the key.

WHAT STAYS, BY NAME. On codes: hbad (the count of the bad points). On the public data: two codes
(hS) · logN ≤ 32 (ha) · hi · hroom · the five written rounds send and draw as declared (hd1, hd4,
hd7; hpU … hlU; hpO … hlO) · "LOC" opens no tree (ho4) · the six quiet stretches list no tree (ht1,
ht3, ht4, ht6, ht7, ht8) · THE BASES ARE TILED (the pieces' bases as written; hb3, hb6, hb8) · lo ≤
B0 · the sending kind's conditions (hCU, h1U, hCO, h1O) · the errors' floors (he1, he2, he4, he5,
he7) · the readers of the sent words (hfU, hfO) · at the two sendings the planner's layout has as
many shapes as the stretch lists trees (hTU, hTO; in row1to8_decoded on the public data alone: hyU,
hyO: the stretch lists as many trees as the block's declared rounds have roots).

What is not claimed. THAT ANY STATEMENT MEETS THE PROMISE AT BORDER 0 (the fence at B0; no collision
at the key's seeds; the key fits) IS NOT SHOWN. Which function decodes is a letter: what the pin is
worth is shown only where the chain's closing tests lay a witness that has the decoder's words. g
and wv lie on another chain. A row of blocks that refuse all has EachGoodIn too. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.Fenced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (IsSend sendPiece send_goodIn Sealed sampledAt shapeAt shapesOf
  condPort errPort)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn ReadsSeat ReadsLow Received)
open _root_.Run.PQ (CK)

/-- The sending kind's parameters at "send o_u". -/
abbrev QU (P : P14) (sentU : Array OracleNotice) : VerifiableInference.Desc.K1.Par :=
  parK1 P 2 "o_u and the first mask" sentU

/-- The sending kind's parameters at "send o_omega". -/
abbrev QO (P : P14) : VerifiableInference.Desc.K1.Par :=
  parK1 P 5 "o_omega and o_sp" (withOmega P.S)

/-- The base of the piece behind border i. -/
def baseAt (B0 tU tO : Nat) : Nat → Nat
  | 0 => B0
  | 1 => B0
  | 2 => B0 + tU
  | 3 => B0 + tU
  | 4 => B0 + tU
  | _ => B0 + tU + tO

variable {W : Type} {F : Frame}

/-- **The promise's letter at border i.** -/
def PrmD (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (B0 tU tO i : Nat) : St × F.E.Str → Prop :=
  PrmAt lo low P err eM rank (baseAt B0 tU tO i)

/-- **The eight blocks are one row, at the functional pin and the fenced promise.** -/
theorem row1to8_fenced {ρ' : Type} (rg : W → Words GE) (wv : W → Nat → GE)
    (D : St × F.E.Str → Words GE) (DV : St × F.E.Str → Nat → GE)
    (lo : Nat) (low : OnBytes.Tree → Option Nat) (recV : St → ρ') (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat)
    (hD : ReadsSeat (bookK lo low) recK agK D) (hV : ReadsLow lo recV DV)
    (hrV : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      recV d' = recV d)
    (B0 : Nat) (hlo : lo ≤ B0)
    (d1 : RDT) {ns1 a1 : Nat} (hd1 : SendsDraws (toRD d1) ns1 P.par.S.kCol 0 a1)
    (ht1 : d1.trees = []) (ha : P.par.S.fold.index.code.logN ≤ 32) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (ef e1 : Nat)
    (he1 : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e1)
    (hbad : ∀ f rec, ¬ (ixOf2 P.par.S.fold err eM rank).Coll f rec.1 →
      cnt ((ixOf2 P.par.S.fold err eM rank).Bad f rec e') ≤ ef)
    (hi : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (sentU : Array OracleNotice) (hU : withU P.S = some sentU) (radU : Nat → Nat)
    (hCU : condPort (QU P sentU) radU = true) (h1U : (QU P sentU).seeds = 1)
    (u₁ u₂ : RDT) (hpU : PlainDraws (Fmt.dsOf u₁.entry u₁.kind))
    (hEU : nE (Fmt.dsOf u₁.entry u₁.kind) = (QU P sentU).coordinates + 1)
    (hPU : nP (Fmt.dsOf u₁.entry u₁.kind) = 0)
    (hzU : IsNZ (Fmt.dsOf u₁.entry u₁.kind) (QU P sentU).coordinates)
    (hlU : u₁.entry.logN ≤ 64) (e2 : Nat) (he2 : errPort (QU P sentU) radU ≤ e2)
    (fOfU : F.E.Str → ∀ k, (Johnson.Pack.portOmZ (QU P sentU).codes (shapeAt (QU P sentU) k)
      (radU k.val)).Str)
    (fInU : F.E.Str → (wT u₁).Msg → ∀ k, (Johnson.Pack.portOmZ (QU P sentU).codes
      (shapeAt (QU P sentU) k) (radU k.val)).Str)
    (hfU : ∀ y τ, fOfU ((sendPiece (W := W) (F := F) b2 B0 u₁ u₂ (QU P sentU).coordinates
      e2).ior.imp y τ) = fInU y τ.1)
    (tU : Nat) (htU : u₁.trees.length + u₂.trees.length = tU)
    (hTU : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, b2.decide d rs gs = .ok d') → lay.shapes.size = tU)
    (p3 p6 p8 : Piece (ckP .two) F St Unit W) (hp3 : p3.b = b3) (hp6 : p6.b = b6)
    (hp8 : p8.b = b8) (hext3 : ∀ a τ w, p3.ext a τ w = w) (hext6 : ∀ a τ w, p6.ext a τ w = w)
    (hext8 : ∀ a τ w, p8.ext a τ w = w)
    (ht3 : p3.trees = 0) (ht6 : p6.trees = 0) (ht8 : p8.trees = 0)
    (d4 : RDT) {ns4 n : Nat}
    (hd4 : SendsDraws (toRD d4) ns4 0 n P.par.S.fold.index.code.logN) (ho4 : d4.opens = [])
    (ht4 : d4.trees = []) (e4 : Nat)
    (he4 : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
    (radO : Nat → Nat) (hCO : condPort (QO P) radO = true) (h1O : (QO P).seeds = 1)
    (o₁ o₂ : RDT) (hpO : PlainDraws (Fmt.dsOf o₁.entry o₁.kind))
    (hEO : nE (Fmt.dsOf o₁.entry o₁.kind) = (QO P).coordinates + 1)
    (hPO : nP (Fmt.dsOf o₁.entry o₁.kind) = 0)
    (hzO : IsNZ (Fmt.dsOf o₁.entry o₁.kind) (QO P).coordinates)
    (hlO : o₁.entry.logN ≤ 64) (e5 : Nat) (he5 : errPort (QO P) radO ≤ e5)
    (fOfO : F.E.Str → ∀ k, (Johnson.Pack.portOmZ (QO P).codes (shapeAt (QO P) k)
      (radO k.val)).Str)
    (fInO : F.E.Str → (wT o₁).Msg → ∀ k, (Johnson.Pack.portOmZ (QO P).codes (shapeAt (QO P) k)
      (radO k.val)).Str)
    (hfO : ∀ y τ, fOfO ((sendPiece (W := W) (F := F) b5 (B0 + tU) o₁ o₂ (QO P).coordinates
      e5).ior.imp y τ) = fInO y τ.1)
    (tO : Nat) (htO : o₁.trees.length + o₂.trees.length = tO)
    (hTO : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, b5.decide d rs gs = .ok d') → lay.shapes.size = tO)
    (hb3 : p3.base = B0 + tU) (hb6 : p6.base = B0 + tU + tO) (hb8 : p8.base = B0 + tU + tO)
    (d7 : RDT) {ns7 a7 : Nat} (hd7 : SendsDraws (toRD d7) ns7 P.par.S.kRow 0 a7)
    (ht7 : d7.trees = []) (e7 : Nat)
    (he7 : P.par.S.kRow * Fintype.card GE ^ (P.par.S.kRow - 1) ≤ e7) :
    EachGoodIn (onD (PrmD lo low P err eM rank B0 tU tO) P.par)
      (relD rg wv (PinF rg wv D DV) P.par e' g
        (fun a => TabX2 P.par err eM rank (tabOf a.2) a.1.loc.key)
        (fun a => DecX2 P.par err eM rank (tabOf a.2) a.1.loc.key)) 0
      [vecPiece (W := W) (F := F) b1 B0 d1 P.par.S.kCol e1,
        sendPiece (W := W) (F := F) b2 B0 u₁ u₂ (QU P sentU).coordinates e2, p3,
        posPiece (W := W) (F := F) b4 (B0 + tU) d4 P.par.S.fold.index.code.logN n e4,
        sendPiece (W := W) (F := F) b5 (B0 + tU) o₁ o₂ (QO P).coordinates e5, p6,
        vecPiece (W := W) (F := F) b7 (B0 + tU + tO) d7 P.par.S.kRow e7, p8] := by
  have hlo2 : lo ≤ B0 + tU := Nat.le_trans hlo (Nat.le_add_right _ _)
  have hlo3 : lo ≤ B0 + tU + tO := Nat.le_trans hlo2 (Nat.le_add_right _ _)
  have c1 : Carries (vecPiece (W := W) (F := F) b1 B0 d1 P.par.S.kCol e1) (PinF rg wv D DV)
      (PrmD lo low P err eM rank B0 tU tO 0) (PrmD lo low P err eM rank B0 tU tO 1) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by show b1 ∈ _; simp) (by simp [vecPiece_trees, ht1]) B0 rfl hlo _ (fun _ h => h)
  have c2 : Carries (sendPiece (W := W) (F := F) b2 B0 u₁ u₂ (QU P sentU).coordinates e2)
      (PinF rg wv D DV) (fun a => (∃ d0, H1 P.par d0 a.1) ∧ PrmD lo low P err eM rank B0 tU tO 1 a)
      (PrmD lo low P err eM rank B0 tU tO 2) :=
    carriesTwo rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (Or.inl rfl) tU ((sendPiece_trees _ _ _ _ _ _).trans htU) hTU B0 rfl hlo _ (fun _ h => h.2)
  have c3 : Carries p3 (PinF rg wv D DV) (fun a => histB P.par 0 a ∧ PrmD lo low P err eM rank B0 tU
      tO 2 a)
      (PrmD lo low P err eM rank B0 tU tO 3) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by rw [hp3]; simp) ht3 (B0 + tU) hb3 hlo2 _ (fun _ h => h.2)
  have c4 : Carries (posPiece (W := W) (F := F) b4 (B0 + tU) d4 P.par.S.fold.index.code.logN n e4)
      (PinF rg wv D DV) (fun a => histB P.par 1 a ∧ PrmD lo low P err eM rank B0 tU tO 3 a)
      (PrmD lo low P err eM rank B0 tU tO 4) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by show b4 ∈ _; simp) (by simp [posPiece_trees, ht4]) (B0 + tU) rfl hlo2 _ (fun _ h => h.2)
  have c5 : Carries (sendPiece (W := W) (F := F) b5 (B0 + tU) o₁ o₂ (QO P).coordinates e5)
      (PinF rg wv D DV) (fun a => histB P.par 2 a ∧ PrmD lo low P err eM rank B0 tU tO 4 a)
      (PrmD lo low P err eM rank B0 tU tO 5) :=
    carriesTwo rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (Or.inr rfl) tO ((sendPiece_trees _ _ _ _ _ _).trans htO) hTO (B0 + tU) rfl hlo2 _
      (fun _ h => h.2)
  have c6 : Carries p6 (PinF rg wv D DV) (fun a => histB P.par 3 a ∧ PrmD lo low P err eM rank B0 tU
      tO 5 a)
      (PrmD lo low P err eM rank B0 tU tO 6) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by rw [hp6]; simp) ht6 (B0 + tU + tO) hb6 hlo3 _ (fun _ h => h.2)
  have c7 : Carries (vecPiece (W := W) (F := F) b7 (B0 + tU + tO) d7 P.par.S.kRow e7)
      (PinF rg wv D DV) (fun a => histB P.par 4 a ∧ PrmD lo low P err eM rank B0 tU tO 6 a)
      (PrmD lo low P err eM rank B0 tU tO 7) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by show b7 ∈ _; simp) (by simp [vecPiece_trees, ht7]) (B0 + tU + tO) rfl hlo3 _ (fun _ h =>
          h.2)
  have c8 : Carries p8 (PinF rg wv D DV) (fun a => histB P.par 5 a ∧ PrmD lo low P err eM rank B0 tU
      tO 7 a)
      (PrmD lo low P err eM rank B0 tU tO 8) :=
    carriesSix rg wv D DV lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS err eM rank recV hD hV hrV _
      (by rw [hp8]; simp) ht8 (B0 + tU + tO) hb8 hlo3 _ (fun _ h => h.2)
  have r6 := row3to8 rg wv (PinF rg wv D DV) (fun i => PrmD lo low P err eM rank B0 tU tO (i + 1 +
      1)) P
    b1 b2 b3 b4 b5 b6 b7 b8 hbl g p3 p6 p8 hp3 hp6 hp8 hext3 hext6 hext8 (B0 + tU) d4 hd4 ho4 e' e4
      he4
    (B0 + tU + tO) d7 hd7 e7 he7 radO hCO h1O (B0 + tU) o₁ o₂ hpO hEO hPO hzO hlO e5 he5 fOfO fInO
    hfO c3 c4 (fun a τ b w h hp => c5.back a τ b w ⟨h, hp⟩)
    (fun a τ b h hp hout _ => c5.keep a τ b ⟨h, hp⟩ hout) c6 c7 c8
    (hdetU_fun rg wv D DV P.par (PrmD lo low P err eM rank B0 tU tO 3))
    (hdetO_fun rg wv D DV P.par (PrmD lo low P err eM rank B0 tU tO 6))
  have r7 := row2to8 rg wv (PinF rg wv D DV) (fun i => PrmD lo low P err eM rank B0 tU tO (i + 1))
      P.par e' g _ _
    (sendU_goodIn rg wv (PinF rg wv D DV) (PrmD lo low P err eM rank B0 tU tO 1)
      (PrmD lo low P err eM rank B0 tU tO 2) P b1 b2 b3 b4 b5 b6 b7 b8 hbl g e' sentU hU radU hCU
          h1U B0 u₁ u₂
      hpU hEU hPU hzU hlU e2 he2 fOfU fInU hfU (fun a τ b w h hp => c2.back a τ b w ⟨h, hp⟩)
      (fun a τ b h hp hout _ => c2.keep a τ b ⟨h, hp⟩ hout)) r6
  exact row1to8 rg wv (PinF rg wv D DV) (PrmD lo low P err eM rank B0 tU tO) P.par e' g _ _ _ _
    (point_goodInY2 rg wv (PinF rg wv D DV) (PrmD lo low P err eM rank B0 tU tO 0)
      (PrmD lo low P err eM rank B0 tU tO 1) P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS g e' B0 d1 hd1 ha err
          eM rank ef e1
      he1 hbad (fun _ h => h.2.1) hi hroom (fun _ h => h.2.2) c1 (hdetVK rg wv D DV _)) r7

/-- **The eight blocks are one row, at decoders that read the trees.** δ, δV: which functions
decode: letters. -/
theorem row1to8_decoded (rg : W → Words GE) (wv : W → Nat → GE)
    (δ : Nat → RecK → Option (Nat × (Nat → List UInt64)) → Words GE)
    (δV : TableKey → (Nat → Option (Nat × List UInt64)) → (Nat → Nat → List UInt64) → Nat → GE)
    (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat)
    (B0 : Nat) (hlo : lo ≤ B0)
    (d1 : RDT) {ns1 a1 : Nat} (hd1 : SendsDraws (toRD d1) ns1 P.par.S.kCol 0 a1)
    (ht1 : d1.trees = []) (ha : P.par.S.fold.index.code.logN ≤ 32) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (ef e1 : Nat)
    (he1 : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e1)
    (hbad : ∀ f rec, ¬ (ixOf2 P.par.S.fold err eM rank).Coll f rec.1 →
      cnt ((ixOf2 P.par.S.fold err eM rank).Bad f rec e') ≤ ef)
    (hi : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (sentU : Array OracleNotice) (hU : withU P.S = some sentU) (radU : Nat → Nat)
    (hCU : condPort (QU P sentU) radU = true) (h1U : (QU P sentU).seeds = 1)
    (u₁ u₂ : RDT) (hpU : PlainDraws (Fmt.dsOf u₁.entry u₁.kind))
    (hEU : nE (Fmt.dsOf u₁.entry u₁.kind) = (QU P sentU).coordinates + 1)
    (hPU : nP (Fmt.dsOf u₁.entry u₁.kind) = 0)
    (hzU : IsNZ (Fmt.dsOf u₁.entry u₁.kind) (QU P sentU).coordinates)
    (hlU : u₁.entry.logN ≤ 64) (e2 : Nat) (he2 : errPort (QU P sentU) radU ≤ e2)
    (fOfU : F.E.Str → ∀ k, (Johnson.Pack.portOmZ (QU P sentU).codes (shapeAt (QU P sentU) k)
      (radU k.val)).Str)
    (fInU : F.E.Str → (wT u₁).Msg → ∀ k, (Johnson.Pack.portOmZ (QU P sentU).codes
      (shapeAt (QU P sentU) k) (radU k.val)).Str)
    (hfU : ∀ y τ, fOfU ((sendPiece (W := W) (F := F) b2 B0 u₁ u₂ (QU P sentU).coordinates
      e2).ior.imp y τ) = fInU y τ.1)
    (tU : Nat) (htU : u₁.trees.length + u₂.trees.length = tU)
    (hyU : tU = (b2.rounds.map (·.entry.roots)).sum)
    (p3 p6 p8 : Piece (ckP .two) F St Unit W) (hp3 : p3.b = b3) (hp6 : p6.b = b6)
    (hp8 : p8.b = b8) (hext3 : ∀ a τ w, p3.ext a τ w = w) (hext6 : ∀ a τ w, p6.ext a τ w = w)
    (hext8 : ∀ a τ w, p8.ext a τ w = w)
    (ht3 : p3.trees = 0) (ht6 : p6.trees = 0) (ht8 : p8.trees = 0)
    (d4 : RDT) {ns4 n : Nat}
    (hd4 : SendsDraws (toRD d4) ns4 0 n P.par.S.fold.index.code.logN) (ho4 : d4.opens = [])
    (ht4 : d4.trees = []) (e4 : Nat)
    (he4 : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
    (radO : Nat → Nat) (hCO : condPort (QO P) radO = true) (h1O : (QO P).seeds = 1)
    (o₁ o₂ : RDT) (hpO : PlainDraws (Fmt.dsOf o₁.entry o₁.kind))
    (hEO : nE (Fmt.dsOf o₁.entry o₁.kind) = (QO P).coordinates + 1)
    (hPO : nP (Fmt.dsOf o₁.entry o₁.kind) = 0)
    (hzO : IsNZ (Fmt.dsOf o₁.entry o₁.kind) (QO P).coordinates)
    (hlO : o₁.entry.logN ≤ 64) (e5 : Nat) (he5 : errPort (QO P) radO ≤ e5)
    (fOfO : F.E.Str → ∀ k, (Johnson.Pack.portOmZ (QO P).codes (shapeAt (QO P) k)
      (radO k.val)).Str)
    (fInO : F.E.Str → (wT o₁).Msg → ∀ k, (Johnson.Pack.portOmZ (QO P).codes (shapeAt (QO P) k)
      (radO k.val)).Str)
    (hfO : ∀ y τ, fOfO ((sendPiece (W := W) (F := F) b5 (B0 + tU) o₁ o₂ (QO P).coordinates
      e5).ior.imp y τ) = fInO y τ.1)
    (tO : Nat) (htO : o₁.trees.length + o₂.trees.length = tO)
    (hyO : tO = (b5.rounds.map (·.entry.roots)).sum)
    (hb3 : p3.base = B0 + tU) (hb6 : p6.base = B0 + tU + tO) (hb8 : p8.base = B0 + tU + tO)
    (d7 : RDT) {ns7 a7 : Nat} (hd7 : SendsDraws (toRD d7) ns7 P.par.S.kRow 0 a7)
    (ht7 : d7.trees = []) (e7 : Nat)
    (he7 : P.par.S.kRow * Fintype.card GE ^ (P.par.S.kRow - 1) ≤ e7) :
    EachGoodIn (onD (PrmD lo low P err eM rank B0 tU tO) P.par)
      (relD rg wv (PinF rg wv (decOf lo low recK δ) (decVOf lo (fun d : St => d.loc.key) δV))
        P.par e' g
        (fun a => TabX2 P.par err eM rank (tabOf a.2) a.1.loc.key)
        (fun a => DecX2 P.par err eM rank (tabOf a.2) a.1.loc.key)) 0
      [vecPiece (W := W) (F := F) b1 B0 d1 P.par.S.kCol e1,
        sendPiece (W := W) (F := F) b2 B0 u₁ u₂ (QU P sentU).coordinates e2, p3,
        posPiece (W := W) (F := F) b4 (B0 + tU) d4 P.par.S.fold.index.code.logN n e4,
        sendPiece (W := W) (F := F) b5 (B0 + tU) o₁ o₂ (QO P).coordinates e5, p6,
        vecPiece (W := W) (F := F) b7 (B0 + tU + tO) d7 P.par.S.kRow e7, p8] :=
  row1to8_fenced rg wv (decOf lo low recK δ) (decVOf lo (fun d : St => d.loc.key) δV) lo low
    (fun d : St => d.loc.key) P
    b1 b2 b3 b4 b5 b6 b7 b8 hbl hS g e' (readsSeat_decOf lo low recK δ)
    (readsLow_decVOf lo (fun d : St => d.loc.key) δV)
    (key_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS) B0 hlo d1 hd1 ht1 ha err eM rank
    ef e1 he1 hbad hi hroom sentU hU radU hCU h1U u₁ u₂ hpU hEU hPU hzU hlU e2 he2 fOfU fInU hfU tU
    htU (shapes_at_sends P b1 b2 b3 b4 b5 b6 b7 b8 hbl b2 (Or.inl rfl) tU hyU) p3 p6 p8 hp3 hp6
      hp8 hext3 hext6 hext8 ht3 ht6 ht8 d4 hd4 ho4 ht4 e4 he4 radO hCO h1O
    o₁ o₂ hpO hEO hPO hzO hlO e5 he5 fOfO fInO hfO tO htO
    (shapes_at_sends P b1 b2 b3 b4 b5 b6 b7 b8 hbl b5 (Or.inr rfl) tO hyO) hb3 hb6 hb8 d7 hd7 ht7
        e7 he7

end Desc.K14.Law
