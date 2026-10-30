-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Borders.lean: ONE TABLE OF THE BORDERS behind the sending of o_u, and the six
blocks from "(rec_gamma)" to "SPLIT" as ONE row of the rule of composition (EachGoodIn): what stands
behind a block is what stands in front of the next, promise and relation.

THE TABLE. Border i stands in front of block i + 3 of the eight. Every promise holds, beside the
history, A LETTER OF ITS OWN BORDER, Prm i; every relation holds Base beside the claims.
  i   in front of      the history (histB)                     the claims (claimsB)
  0   "(rec_gamma)"    o_u is sent and noted (H2)              near · RecAll · DotU
  1   "LOC"            and "(rec_gamma)" has said yes (H3)     near · DotU
  2   "send o_omega"   and "LOC" (H4)                          DotU
  3   the joinings     and o_omega is sent and noted (On6)     OmegaCol · DotOm
  4   "LIN zeta"       and the joinings (On7)                  OmegaCol · DotOm
  5   "SPLIT"          and "LIN zeta" (On8)                    FoldAt · DotOm
  6   behind "SPLIT"   and "SPLIT" (On9)                       DotOm
The claims: near: the code word of the folded row is within e' locations of the fold of the stored
table's columns · RecAll: (rec_gamma)'s equation at every seed · DotU: (Dot)'s equation with what is
read off u at psi_lo in omega_col's place · OmegaCol: omega_col is what is read off u · DotOm:
(Dot)'s equation · FoldAt: (fold)'s equation. g (the row weights, read) and wv (the other vector's
words, off the witness) are letters: they lie on another chain.

  goodIn_weave    the one tool: a law goes over to a stronger promise in front, to what a yes gives
                  behind, and to relations with passengers.
  send_of_blocks  what a yes of the second and of the fifth block is made of.
  H2, H3, H4, on4_of_H2 … the histories, and that they give the promise On4.
  DotOmAt, DotUAt, with what they read.
  histB, claimsB  the table.
  row3to8         **the six blocks are one row.**

What is not claimed. "LIN point" and "send o_u" stand in front of this row and have no law here. The
premises of the six laws stay, piece by piece, EACH ASKED UNDER THE WHOLE PROMISE OF THE BORDER IN
FRONT OF THE PIECE (the history and Prm i) AND OF NO OTHER STATEMENT: at a yes the pin goes back,
and the next border's Prm (i + 1) holds behind; the pin determines the words that are read WHERE
THEY ARE READ: in front of "LOC" those of o_u, in front of "LIN zeta" those of o_omega and o_u; the
written rounds send and draw as declared; the round of "LOC" opens no tree; the sending kind's
premises at "send o_omega", and that the promise in front with its new messages sealed gives Prm 3
behind. WHY BY THE BORDER: a piece writes or clears every tree from its own base on: a pin that
reads trees goes back only where the record's book counts just the trees below that base: a clause
that is meant to stand in Prm i. Pin, Prm, g, wv are letters. No member is shown. A row of blocks
that refuse all has EachGoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.RecRow
import Johnson.Desc.K14.Law.SendGood

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
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)
open _root_.Run.PQ (CK)

/-- **The one tool.** A law goes over to a promise in front that gives its own, to a promise behind
that a yes gives, and to relations with passengers. -/
theorem goodIn_weave {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W)
    (on on' on₂ on₂' : S × F.E.Str → Prop) (R R' R₂ R₂' : S × F.E.Str → W → Prop)
    (h : p.GoodIn on on' R R') (h1 : ∀ a, on₂ a → on a)
    (h2 : ∀ a τ b, on₂ a → p.ior.red.out a τ = some b → on' b → on₂' b)
    (h3 : ∀ a τ b w, on₂ a → p.ior.red.out a τ = some b → on' b → R₂' b w → R' b w)
    (h4 : ∀ a τ b w, on₂ a → p.ior.red.out a τ = some b → on' b → R₂' b w →
      R a (p.ext a τ w) → R₂ a (p.ext a τ w)) :
    p.GoodIn on₂ on₂' R₂ R₂' :=
  fun a ha => Doomed.mono _ _
    (fun τ hτ b hb => ⟨h2 a τ b ha hb (hτ b hb).1, fun w hw =>
      h4 a τ b w ha hb (hτ b hb).1 hw ((hτ b hb).2 w (h3 a τ b w ha hb (hτ b hb).1 hw))⟩)
    (h a (h1 a ha))

/-- What a yes of the second and of the fifth block is made of. -/
theorem send_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (∃ sentU, withU P.S = some sentU ∧ ∀ d rs gs d', b2.decide d rs gs = .ok d' →
      ∃ ft ids a1 a2, recvP ft d sentU = some (ids, a1) ∧ Onward a1 a2 ∧ a2.loc = a1.loc ∧
        behindU P.par a2 ids = some d') ∧
    ∀ d rs gs d', b5.decide d rs gs = .ok d' →
      ∃ ft ids a1 a2, recvP ft d (withOmega P.S) = some (ids, a1) ∧ Onward a1 a2 ∧
        a2.loc = a1.loc ∧ behindOmega P.par a2 ids = some d' := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  refine ⟨⟨sentU, hU, fun d rs gs d' h => ?_⟩, fun d rs gs d' h => ?_⟩
  · obtain ⟨ids, a1, a2, r, c, cl, k⟩ := sendAt_inv _ _ _ _ _ _ d d' rs gs h
    rw [parK1_sent] at r
    exact ⟨_, ids, a1, a2, r, c, cl, k⟩
  · obtain ⟨ids, a1, a2, r, c, cl, k⟩ := sendAt_inv _ _ _ _ _ _ d d' rs gs h
    rw [parK1_sent] at r
    exact ⟨_, ids, a1, a2, r, c, cl, k⟩

/-! ## The histories -/

/-- "LIN point" has said yes, o_u is sent and noted, and that has led to this record; two codes. -/
def H2 (p : Par) (d0 d2 : St) : Prop :=
  p.S.sharedSplitNeeded = true ∧
  ∃ (d1 a1 a2 : St) (rs1 : List Fmt.RoundView) (ftU : Nat) (sentU : Array OracleNotice)
    (idsU : Array Nat),
    linPoint p d0 rs1 = some d1 ∧ withU p.S = some sentU ∧
    recvP ftU d1 sentU = some (idsU, a1) ∧ Onward a1 a2 ∧ a2.loc = a1.loc ∧
    behindU p a2 idsU = some d2

/-- And "(rec_gamma)" has said yes. -/
def H3 (p : Par) (d0 d2 d3 : St) : Prop := H2 p d0 d2 ∧ ∃ rs3, laysRec p d2 rs3 = some d3

/-- And "LOC". -/
def H4 (p : Par) (d0 d2 d3 d4 : St) (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)) : Prop :=
  H3 p d0 d2 d3 ∧ loc p d3 [r4] [cols] = some d4

variable {W : Type} {F : Frame}

/-- The first history gives the promise at the borders of "(rec_gamma)" and "LOC". -/
theorem on4_of_H2 {p : Par} {d0 d2 : St} (h : H2 p d0 d2) (y : F.E.Str) :
    On4 p ((d2, y) : St × F.E.Str) := by
  obtain ⟨_, d1, a1, a2, rs1, ftU, sentU, idsU, h1, hU, rU, cU, _, h2⟩ := h
  exact on4_behind p d0 d1 a1 a2 d2 rs1 ftU sentU idsU h1 hU rU cU h2 y

/-- So does the second. -/
theorem on4_of_H3 {p : Par} {d0 d2 d3 : St} (h : H3 p d0 d2 d3) (y : F.E.Str) :
    On4 p ((d3, y) : St × F.E.Str) := by
  obtain ⟨h2, rs3, h3⟩ := h
  exact (on4_of_H2 h2 y).onward (b := (d3, y)) (onward_laysRec p d2 d3 rs3 h3).1
    (onward_laysRec p d2 d3 rs3 h3).2

/-- The third history with o_omega's sending is the front up to the note behind it. -/
theorem H4.toFront5 {p : Par} {d0 d2 d3 d4 d5 b1 b2 : St} {r4 : Fmt.RoundView}
    {cols : List (Nat × List UInt64)} (h : H4 p d0 d2 d3 d4 r4 cols) (ftO : Nat)
    (idsO : Array Nat) (rO : recvP ftO d4 (withOmega p.S) = some (idsO, b1)) (cO : Onward b1 b2)
    (cOl : b2.loc = b1.loc) (h5 : behindOmega p b2 idsO = some d5) :
    Front5 p d0 d2 d3 d5 r4 cols := by
  obtain ⟨⟨⟨hS, d1, a1, a2, rs1, ftU, sentU, idsU, h1, hU, rU, cU, cUl, h2⟩, rs3, h3⟩, h4⟩ := h
  exact ⟨hS, d1, a1, a2, d4, b1, b2, rs1, rs3, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5⟩

/-! ## The two claims on (Dot) -/

/-- (Dot)'s equation, at the point and at o_omega's number that the record notes. V: the other
vector. -/
def DotOmAt (S : LinShape) (g : Nat → GE) (d : St) (m : Words GE) (V : Nat → GE) : Prop :=
  DotEq S.matrixRows S.kCol g (omegaOf d.loc (linLayOmega d.st.codes S) m)
    (d.loc.psiSh.map OnBytes.Model.Reading.gl.val) V

/-- The same with what is read off u at psi_lo in omega_col's place. -/
def DotUAt (S : LinShape) (g : Nat → GE) (l : Lin) (m : Words GE) (V : Nat → GE) : Prop :=
  ∑ y ∈ Finset.range S.matrixRows, g y * ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK ((l.psiSh.take S.kLo).map OnBytes.Model.Reading.gl.val) t *
        uOf l m (t + 2 ^ S.kLo * y) =
    ∑ c ∈ Finset.range (2 ^ S.kCol), eqK (l.psiSh.map OnBytes.Model.Reading.gl.val) c * V c

/-- What DotOmAt reads of the record. -/
theorem DotOmAt.of_same {S : LinShape} {g : Nat → GE} {d d' : St} {m : Words GE} {V : Nat → GE}
    (hc : d'.st.codes = d.st.codes) (hp : d'.loc.psiSh = d.loc.psiSh)
    (ho : d'.loc.oOmega = d.loc.oOmega) (h : DotOmAt S g d' m V) : DotOmAt S g d m V := by
  unfold DotOmAt omegaOf at h ⊢
  rw [hc, hp, ho] at h
  exact h

/-- With omega_col = col_psi_lo(u), DotOm is DotU. -/
theorem DotUAt.of_omega {S : LinShape} {g : Nat → GE} {d : St} {m : Words GE} {V : Nat → GE}
    (hO : OmegaCol OnBytes.Model.Reading.gl S d m) (h : DotOmAt S g d m V) :
    DotUAt S g d.loc m V :=
  dotU_of S.matrixRows S.kCol S.kLo g _ (uOf d.loc m) _ _ V hO h

/-! ## The table -/

/-- The history at border i. -/
def histB (p : Par) : Nat → St × F.E.Str → Prop
  | 0 => fun a => ∃ d0, H2 p d0 a.1
  | 1 => fun a => ∃ d0 d2, H3 p d0 d2 a.1
  | 2 => fun a => ∃ d0 d2 d3 r4 cols, H4 p d0 d2 d3 a.1 r4 cols
  | 3 => On6 p
  | 4 => On7 p
  | 5 => On8 p
  | _ => On9 p

/-- The claims at border i. -/
def claimsB (p : Par) (e' : Nat) (g : Nat → GE) : Nat → St × F.E.Str → Words GE → (Nat → GE) → Prop
  | 0 => fun a m V => NearAt OnBytes.Model.Reading.gl p a.1 m (tabOf a.2) e' ∧
      RecAll OnBytes.Model.Reading.gl p a.1 m ∧ DotUAt p.S g a.1.loc m V
  | 1 => fun a m V => NearAt OnBytes.Model.Reading.gl p a.1 m (tabOf a.2) e' ∧
      DotUAt p.S g a.1.loc m V
  | 2 => fun a m V => DotUAt p.S g a.1.loc m V
  | 3 => fun a m V => OmegaCol OnBytes.Model.Reading.gl p.S a.1 m ∧ DotOmAt p.S g a.1 m V
  | 4 => fun a m V => OmegaCol OnBytes.Model.Reading.gl p.S a.1 m ∧ DotOmAt p.S g a.1 m V
  | 5 => fun a m V => FoldAt OnBytes.Model.Reading.gl p.S a.1 m ∧ DotOmAt p.S g a.1 m V
  | _ => fun a m V => DotOmAt p.S g a.1 m V

/-- At a piece, UNDER THE WHOLE PROMISE on IN FRONT OF IT: at a yes the pin goes back, and the next
border's promise Prm' holds behind. -/
structure Carries {C : CK} (pc : Piece C F St Unit W) (Pin : St × F.E.Str → W → Prop)
    (on Prm' : St × F.E.Str → Prop) : Prop where
  back : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w
  keep : ∀ a τ b, on a → pc.ior.red.out a τ = some b → Prm' b

variable (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
  (Prm : Nat → St × F.E.Str → Prop)

/-- **The six blocks from "(rec_gamma)" to "SPLIT" are one row.** -/
theorem row3to8 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (g : Nat → GE)
    (p3 p6 p8 : Piece (ckP .two) F St Unit W) (hp3 : p3.b = b3) (hp6 : p6.b = b6)
    (hp8 : p8.b = b8) (hext3 : ∀ a τ w, p3.ext a τ w = w) (hext6 : ∀ a τ w, p6.ext a τ w = w)
    (hext8 : ∀ a τ w, p8.ext a τ w = w)
    (base4 : Nat) (d4 : RDT) {ns4 n : Nat}
    (hd4 : SendsDraws (toRD d4) ns4 0 n P.par.S.fold.index.code.logN) (ho4 : d4.opens = [])
    (e' e4 : Nat) (he4 : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
    (base7 : Nat) (d7 : RDT) {ns7 a7 : Nat} (hd7 : SendsDraws (toRD d7) ns7 P.par.S.kRow 0 a7)
    (e7 : Nat) (he7 : P.par.S.kRow * Fintype.card GE ^ (P.par.S.kRow - 1) ≤ e7)
    (rad : Nat → Nat)
    (hC : condPort (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) rad = true)
    (h1 : (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).seeds = 1)
    (base5 : Nat) (d₁ d₂ : RDT) (hp : PlainDraws (Fmt.dsOf d₁.entry d₁.kind))
    (hE : nE (Fmt.dsOf d₁.entry d₁.kind) =
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates + 1)
    (hP : nP (Fmt.dsOf d₁.entry d₁.kind) = 0)
    (hz : IsNZ (Fmt.dsOf d₁.entry d₁.kind)
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates)
    (hl : d₁.entry.logN ≤ 64) (e5 : Nat)
    (he5 : errPort (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) rad ≤ e5)
    (fOf : F.E.Str → ∀ k, (Johnson.Pack.portOmZ
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).codes
      (shapeAt (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (Johnson.Pack.portOmZ
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).codes
      (shapeAt (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b5 base5 d₁ d₂
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5).ior.imp y τ) = fIn y τ.1)
    (c3 : Carries p3 Pin (fun a => histB P.par 0 a ∧ Prm 0 a) (Prm 1))
    (c4 : Carries (posPiece (W := W) (F := F) b4 base4 d4 P.par.S.fold.index.code.logN n e4)
      Pin (fun a => histB P.par 1 a ∧ Prm 1 a) (Prm 2))
    (back5 : ∀ a τ b w, histB P.par 2 a → Prm 2 a → (sendPiece (W := W) (F := F) b5 base5 d₁ d₂
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5).ior.red.out a τ = some b →
      Pin b w → Pin a w)
    (prm5 : ∀ a τ b, histB P.par 2 a → Prm 2 a → (sendPiece (W := W) (F := F) b5 base5 d₁ d₂
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5).ior.red.out a τ = some b →
      (∀ k, sampledAt (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) k →
        Sealed (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).codes
          (shapeAt (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) k) (rad k.val) (fOf b.2 k) b.1.st
          (b.1.st.oracles.size -
            (shapesOf (parK1 P 5 "o_omega and o_sp" (withOmega P.S))).length + k.val)) → Prm 3 b)
    (c6 : Carries p6 Pin (fun a => histB P.par 3 a ∧ Prm 3 a) (Prm 4))
    (c7 : Carries (vecPiece (W := W) (F := F) b7 base7 d7 P.par.S.kRow e7) Pin
      (fun a => histB P.par 4 a ∧ Prm 4 a) (Prm 5))
    (c8 : Carries p8 Pin (fun a => histB P.par 5 a ∧ Prm 5 a) (Prm 6))
    (hdetU : ∀ (x : St × F.E.Str) w w', histB P.par 1 x → Prm 1 x → Pin x w →
      Pin x w' → AgreeOn x.1.loc.oU.oracle (rg w) (rg w'))
    (hdetO : ∀ (x : St × F.E.Str) w w', histB P.par 4 x → Prm 4 x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oOmega (rg w) (rg w') ∧ AgreeOn x.1.loc.oU.oracle (rg w) (rg w')) :
    EachGoodIn (fun i a => histB P.par i a ∧ Prm i a)
      (fun i a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        claimsB P.par e' g i a (rg w) (wv w)) 0
      [p3, posPiece (W := W) (F := F) b4 base4 d4 P.par.S.fold.index.code.logN n e4,
        sendPiece (W := W) (F := F) b5 base5 d₁ d₂
          (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5,
        p6, vecPiece (W := W) (F := F) b7 base7 d7 P.par.S.kRow e7, p8] := by
  obtain ⟨_, hs5⟩ := send_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain ⟨_, _, _, is5⟩ := isSend_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  have hq := quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  -- "(rec_gamma)"
  have k3 : p3.GoodIn (fun a => (∃ d0, H2 P.par d0 a.1) ∧ Prm 0 a)
      (fun a => (∃ d0 d2, H3 P.par d0 d2 a.1) ∧ Prm 1 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par a.1 (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par a.1 (rg w) ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par a.1 (rg w) (tabOf a.2) e' ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w))) := by
    refine goodIn_weave p3 _ _ _ _ _ _ _ _
      (rec_goodInR OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p3 hp3 hext3
        (fun a => (∃ d0, H2 P.par d0 a.1) ∧ Prm 0 a) (fun a τ b w _ hp => c3.back a τ b w hp)
        (fun x m => NearAt OnBytes.Model.Reading.gl P.par x.1 m (tabOf x.2) e')
        (fun a τ b m hy _ l hq => by
          have hq' : NearAt OnBytes.Model.Reading.gl P.par b.1 m (tabOf b.2) e' := hq
          rw [hy, tabOf_imp] at hq'
          exact NearAt.back _ _ _ _ _ _ _ l hq'))
      (fun a ha => ⟨by obtain ⟨⟨d0, h2⟩, _⟩ := ha; exact on4_of_H2 h2 a.2, ha⟩)
      (fun a τ b ha hout _ => ?_) (fun a τ b w _ _ _ hw => ⟨hw.1, hw.2.1⟩)
      (fun a τ b w _ hout _ hw hR => ?_)
    · have hk := c3.keep a τ b ha hout
      obtain ⟨⟨d0, h2⟩, _⟩ := ha
      obtain ⟨_, gs, hd⟩ := piece_yes p3 a τ b hout
      exact ⟨⟨d0, a.1, h2, _, hq.1 _ _ gs _ (hp3 ▸ hd)⟩, hk⟩
    · obtain ⟨_, gs, hd⟩ := piece_yes p3 a τ b hout
      have l := (onward_laysRec P.par a.1 b.1 _ (hq.1 _ _ gs _ (hp3 ▸ hd))).2
      rw [hext3] at hR ⊢
      exact ⟨hR.1.1, hR.1.2, hR.2, l ▸ hw.2.2⟩
  -- "LOC"
  have k4 : (posPiece (W := W) (F := F) b4 base4 d4 P.par.S.fold.index.code.logN n e4).GoodIn
      (fun a => (∃ d0 d2, H3 P.par d0 d2 a.1) ∧ Prm 1 a)
      (fun a => (∃ d0 d2 d3 r4 cols, H4 P.par d0 d2 d3 a.1 r4 cols) ∧ Prm 2 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par a.1 (rg w) (tabOf a.2) e' ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        DotUAt P.par.S g a.1.loc (rg w) (wv w)) := by
    have yes4 : ∀ a τ b, (posPiece (W := W) (F := F) b4 base4 d4
        P.par.S.fold.index.code.logN n e4).ior.red.out a τ = some b →
        ∃ r4 cols, loc P.par a.1 [r4] [cols] = some b.1 := by
      intro a τ b hout
      have k := loc_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ _ _ (piece_groups _ a τ b hout)
      obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k
      rw [hr, hg] at k
      exact ⟨r4, cols, k⟩
    refine goodIn_weave _ _ _ _ _ _ _ _ _
      (loc_goodIn4' Pin rg P b1 b2 b3 b4 b5 b6 b7 b8 hbl base4 d4 hd4 ho4 e' e4 he4
        (fun x => (∃ d0 d2, H3 P.par d0 d2 x.1) ∧ Prm 1 x) (Prm 2)
        (fun x τ b w _ hx => c4.back x τ b w hx) (fun x τ b _ hx => c4.keep x τ b hx)
        fun x w w' _ hx => hdetU x w w' hx.1 hx.2)
      (fun a ha => ⟨by obtain ⟨⟨d0, d2, h3⟩, _⟩ := ha; exact on4_of_H3 h3 a.2, ha⟩)
      (fun a τ b ha hout hb => ?_) (fun a τ b w _ _ _ hw => hw.1)
      (fun a τ b w _ hout _ hw hR => ?_)
    · obtain ⟨⟨d0, d2, h3⟩, _⟩ := ha
      obtain ⟨r4, cols, k⟩ := yes4 a τ b hout
      exact ⟨⟨d0, d2, a.1, r4, cols, h3, k⟩, hb.2⟩
    · obtain ⟨r4, cols, k⟩ := yes4 a τ b hout
      have l := (onward_loc P.par a.1 b.1 r4 cols k).2
      exact ⟨hR.1, hR.2, l ▸ hw.2⟩
  -- "send o_omega"
  have yes5 : ∀ a τ b, (sendPiece (W := W) (F := F) b5 base5 d₁ d₂
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5).ior.red.out a τ = some b →
      ∃ ft ids c1 c2, recvP ft a.1 (withOmega P.S) = some (ids, c1) ∧ Onward c1 c2 ∧
        c2.loc = c1.loc ∧ behindOmega P.par c2 ids = some b.1 := by
    intro a τ b hout
    obtain ⟨_, gs, hd⟩ := piece_yes _ a τ b hout
    exact hs5 _ _ gs _ hd
  have k5 : (sendPiece (W := W) (F := F) b5 base5 d₁ d₂
      (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).coordinates e5).GoodIn
      (fun a => (∃ d0 d2 d3 r4 cols, H4 P.par d0 d2 d3 a.1 r4 cols) ∧ Prm 2 a)
      (fun a => On6 P.par a ∧ Prm 3 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        DotUAt P.par.S g a.1.loc (rg w) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (OmegaCol OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w))) := by
    refine goodIn_weave _ _ _ _ _ _ _ _ _
      (send_goodIn (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) rad hC h1 b5
        (fun s : St => s.st) is5 base5 d₁ d₂ hp hE hP hz hl e5 he5 fOf fIn hf
        (fun a => (∃ d0 d2 d3 r4 cols, H4 P.par d0 d2 d3 a.1 r4 cols) ∧ Prm 2 a)
        (fun b => On6 P.par b)
        (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w))
        (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
          (OmegaCol OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
            DotOmAt P.par.S g a.1 (rg w) (wv w)))
        (fun a τ x ha hout => ?_) (fun a τ x w ha hout hw => ?_))
      (fun a ha => ha) (fun a τ b ha hout hb => ⟨hb.1, prm5 a τ b ha.1 ha.2 hout hb.2⟩)
      (fun a τ b w _ _ _ hw => hw) (fun a τ b w _ _ _ _ hR => hR)
    · obtain ⟨⟨d0, d2, d3, r4, cols, h4⟩, _⟩ := ha
      obtain ⟨ft, ids, c1, c2, rO, cO, cOl, h5⟩ := yes5 a τ x hout
      exact ⟨d0, d2, d3, r4, cols, h4.toFront5 ft ids rO cO cOl h5⟩
    · obtain ⟨ft, ids, c1, c2, rO, cO, cOl, h5⟩ := yes5 a τ x hout
      obtain ⟨o1, l1⟩ := onward_recvP ft a.1 c1 _ ids rO
      obtain ⟨s5, oo, sp, _, l5⟩ := behindOmega_inv P.par c2 x.1 ids h5
      have o : Onward a.1 x.1 := (o1.trans cO).trans (Onward.of_st s5)
      have l : x.1.loc = { a.1.loc with oOmega := oo, oSp := sp } := by rw [l5, cOl, l1]
      obtain ⟨⟨hpin, hU, hO⟩, hom, hdot⟩ := hw
      have hgU : x.1.loc.gU = a.1.loc.gU := by rw [l]
      have hgO : x.1.loc.gOmega = a.1.loc.gOmega := by rw [l]
      refine ⟨⟨back5 a τ x w ha.1 ha.2 hout hpin, ?_, ?_⟩, ?_⟩
      · rw [← hgU]; exact hU.back _ o
      · rw [← hgO]; exact hO.back _ o
      · have hD := DotUAt.of_omega hom hdot
        unfold DotUAt uOf at hD ⊢
        rw [l] at hD
        exact hD
  -- the joinings
  have k6 : p6.GoodIn (fun a => On6 P.par a ∧ Prm 3 a) (fun a => On7 P.par a ∧ Prm 4 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (OmegaCol OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (OmegaCol OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w))) := by
    refine goodIn_weave p6 _ _ _ _ _ _ _ _
      (joins_goodIn6 OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p6 hp6 hext6
        (fun a => On6 P.par a ∧ Prm 3 a) (On7 P.par) c6.back
        (fun x y rs hx h => by
          obtain ⟨⟨d0, d2, d3, r4, cols, hF⟩, _⟩ := hx
          exact ⟨d0, d2, d3, r4, cols, hF.toFront y.1 rs h⟩)
        (fun x m => OmegaCol OnBytes.Model.Reading.gl P.par.S x.1 m)
        (fun x τ y m _ o l hq => OmegaCol.back _ _ _ _ _ o l hq))
      (fun a ha => ha) (fun a τ b ha hout hb => ⟨hb, c6.keep a τ b ha hout⟩)
      (fun a τ b w _ _ _ hw => ⟨hw.1, hw.2.1⟩) (fun a τ b w _ hout _ hw hR => ?_)
    obtain ⟨_, gs, hd⟩ := piece_yes p6 a τ b hout
    obtain ⟨o, l⟩ := onward_joins P.par a.1 b.1 _ (hq.2 _ _ gs _ (hp6 ▸ hd))
    rw [hext6] at hR ⊢
    exact ⟨hR.1, hR.2, DotOmAt.of_same o.grows.1 (by rw [l]) (by rw [l]) hw.2.2⟩
  -- "LIN zeta"
  have k7 : (vecPiece (W := W) (F := F) b7 base7 d7 P.par.S.kRow e7).GoodIn
      (fun a => On7 P.par a ∧ Prm 4 a) (fun a => On8 P.par a ∧ Prm 5 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (OmegaCol OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (FoldAt OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w))) := by
    have yes7 : ∀ a τ b, (vecPiece (W := W) (F := F) b7 base7 d7 P.par.S.kRow e7).ior.red.out a τ =
        some b → ∃ r7, linZeta a.1 [r7] = some b.1 := by
      intro a τ b hout
      obtain ⟨_, gs, hd⟩ := piece_yes _ a τ b hout
      have k := zeta_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hd
      obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k
      rw [hr] at k
      exact ⟨r7, k⟩
    refine goodIn_weave _ _ _ _ _ _ _ _ _
      (zeta_goodIn7 rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl base7 d7 hd7 e7 he7 (Prm 4) (Prm 5)
        (fun x τ b w h7 hx => c7.back x τ b w ⟨h7, hx⟩) (fun x τ b h7 hx => c7.keep x τ b ⟨h7, hx⟩)
        hdetO)
      (fun a ha => ha) (fun a τ b _ _ hb => hb) (fun a τ b w _ _ _ hw => ⟨hw.1, hw.2.1⟩)
      (fun a τ b w _ hout _ hw hR => ?_)
    obtain ⟨r7, k⟩ := yes7 a τ b hout
    have e := linZeta_inv a.1 b.1 r7 k
    exact ⟨hR.1, hR.2, DotOmAt.of_same (by rw [e]) (by rw [e]) (by rw [e]) hw.2.2⟩
  -- "SPLIT"
  have k8 : p8.GoodIn (fun a => On8 P.par a ∧ Prm 5 a) (fun a => On9 P.par a ∧ Prm 6 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (FoldAt OnBytes.Model.Reading.gl P.par.S a.1 (rg w) ∧
          DotOmAt P.par.S g a.1 (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        DotOmAt P.par.S g a.1 (rg w) (wv w)) := by
    refine goodIn_weave p8 _ _ _ _ _ _ _ _
      (split_goodIn8 OnBytes.Model.Reading.gl rg Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl p8 hp8 hext8
        (Prm 5) (Prm 6) (fun a τ b w h8 hx => c8.back a τ b w ⟨h8, hx⟩)
        fun a τ b h8 hx => c8.keep a τ b ⟨h8, hx⟩)
      (fun a ha => ha) (fun a τ b _ _ hb => hb)
      (fun a τ b w _ _ _ hw => hw.1) (fun a τ b w ha hout _ hw hR => ?_)
    obtain ⟨_, gs, hd⟩ := piece_yes p8 a τ b hout
    have k := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ (hp8 ▸ hd)
    have hS := ha.1.twoCodes
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k
    rw [hr] at k
    obtain ⟨o, l⟩ := onward_split P.par a.1 b.1 r8 hS k
    rw [hext8] at hR ⊢
    exact ⟨hR.1, hR.2, DotOmAt.of_same o.grows.1 (by rw [l]) (by rw [l]) hw.2⟩
  exact ⟨k3, k4, k5, k6, k7, k8, trivial⟩

end Desc.K14.Law
