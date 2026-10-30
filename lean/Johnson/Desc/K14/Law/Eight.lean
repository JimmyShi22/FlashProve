--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/Eight.lean: **all eight blocks of the shared chain's place, from "LIN point" to
"SPLIT", as one row of the rule of composition** (EachGoodIn), out of the law of "LIN point"
(Johnson/Desc/K14/Law/PointGood.lean) and the row of the seven (BordersU.lean).

THE TABLE, WHOLE. Border i stands in front of block i + 1.
  i   in front of      the promise                  the relation
  0   "LIN point"      Prm 0                        the pin · the table decodes · VIs
  1   "send o_u"       H1 and Prm 1                 Base · near, RecAll, DotU of the message to come
  2   "(rec_gamma)"    H2 and Prm 2                 Base · near · RecAll · DotU
  3   "LOC"            H3 and Prm 3                 Base · near · DotU
  4   "send o_omega"   H4 and Prm 4                 Base · DotU
  5   the joinings     On6 and Prm 5                Base · OmegaCol · DotOm
  6   "LIN zeta"       On7 and Prm 6                Base · OmegaCol · DotOm
  7   "SPLIT"          On8 and Prm 7                Base · FoldAt · DotOm
  8   behind "SPLIT"   On9 and Prm 8                Base · DotOm
READ BACKWARD: a witness of whose words all constraints on the two groups hold at their tests, and
(Dot)'s equation, is, but for the lost draws of three rounds and the bad seeds of two sendings, a
witness at a statement whose stored table decodes (Dec a), whose other vector is the row weights
applied to the matrix matOf kLo (Tab a). Dec AND Tab ARE LETTERS HERE, tied to the stored table by
the two premises of the law of "LIN point" (hkey, hgood) alone: neither is paid in this file or
beneath it.

  eachGoodIn_cons  a block in front of a row is a row, of the tables with one border more in front.
  onD, relD        the table.
  row1to8          the eight.

What is not claimed. Every premise of the eight laws stays; they are taken here as the two laws that
hold them. Pin, Prm, BadKey, Dec, Tab, g, wv are letters. No member is shown. What stands at the
last border has to ride on through the two proximity tests and the chain's end. A row of blocks that
refuse all has EachGoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)
open _root_.Run.PQ (CK)

variable {W : Type} {F : Frame}

/-- A block in front of a row is a row, of the tables with one border more in front. -/
theorem eachGoodIn_cons {S Cl : Type} {C : CK} (on : Nat → S × F.E.Str → Prop)
    (R : Nat → S × F.E.Str → W → Prop) (on0 : S × F.E.Str → Prop) (R0 : S × F.E.Str → W → Prop)
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (h0 : p.GoodIn on0 (on 0) R0 (R 0))
    (h : EachGoodIn on R 0 l) :
    EachGoodIn (fun i => Nat.casesOn i on0 on) (fun i => Nat.casesOn i R0 R) 0 (p :: l) := by
  have key : ∀ (l : List (Piece C F S Cl W)) (i : Nat), EachGoodIn on R i l →
      EachGoodIn (fun i => Nat.casesOn i on0 on) (fun i => Nat.casesOn i R0 R) (i + 1) l := by
    intro l
    induction l with
    | nil => exact fun _ _ => trivial
    | cons q l ih => exact fun i hq => ⟨hq.1, ih (i + 1) hq.2⟩
  exact ⟨h0, key l 0 h⟩

variable (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
  (Prm : Nat → St × F.E.Str → Prop)

/-- The promise at border i of the whole table. -/
def onD (p : Par) (i : Nat) : St × F.E.Str → Prop :=
  Nat.casesOn i (fun a => Prm 0 a) fun j a => histC p j a ∧ Prm (j + 1) a

/-- The relation at border i of the whole table. -/
def relD (p : Par) (e' : Nat) (g : Nat → GE) (Tab : St × F.E.Str → Nat → Nat → GE)
    (Dec : St × F.E.Str → Prop) (i : Nat) : St × F.E.Str → W → Prop :=
  Nat.casesOn i (fun a w => Pin a w ∧ Dec a ∧ VIs p.S g (Tab a) (wv w)) fun j a w =>
    Base OnBytes.Model.Reading.gl rg Pin a w ∧ claimsC p e' g j a (rg w) (wv w)

/-- **The eight blocks are one row**, given the law of "LIN point" and the row of the seven. -/
theorem row1to8 (p : Par) (e' : Nat) (g : Nat → GE) (Tab : St × F.E.Str → Nat → Nat → GE)
    (Dec : St × F.E.Str → Prop) (p1 : Piece (ckP .two) F St Unit W)
    (l : List (Piece (ckP .two) F St Unit W))
    (h1 : p1.GoodIn (fun a => Prm 0 a) (fun a => (∃ d0, H1 p d0 a.1) ∧ Prm 1 a)
      (fun a w => Pin a w ∧ Dec a ∧ VIs p.S g (Tab a) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl p (withNext p a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl p (withNext p a.1) (rg w) ∧
          DotUAt p.S g (withNext p a.1).loc (rg w) (wv w))))
    (h : EachGoodIn (fun i a => histC p i a ∧ Prm (i + 1) a)
      (fun i a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        claimsC p e' g i a (rg w) (wv w)) 0 l) :
    EachGoodIn (onD Prm p) (relD rg wv Pin p e' g Tab Dec) 0 (p1 :: l) :=
  eachGoodIn_cons _ _ _ _ p1 l h1 h

end Desc.K14.Law
