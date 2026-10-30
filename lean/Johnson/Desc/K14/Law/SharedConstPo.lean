-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SharedConstPo.lean: TWO FIELDS OF "THE TABLES FIT" (the structure
TablesFitR, Johnson/P5J/TopTablesR.lean), POf AND POb, IN THE FIELDS' OWN LETTERS, AT THE SHARED
TABLE's CONSTANT: N₁ := O.N₁ · Mg₁ := O.Mg₁ · get := O.get · Ns := the shared chain's numbers · Pm
:= Sh.pm A O · Mg := Sh.mg A O: after the pattern of Sh.TP_at | Sh.PW_at
(Johnson/Desc/K14/Law/SharedConstFitR.lean). This file does not import that structure: the two
statements are its fields' texts, letter for letter, so that whoever fills it lays them by name.
A JOINING: EVERY BRICK LAY: none is typed here.

  Sh.readsTree_at   at the constant's letters "shown", "no collision" and the pin of a tenant read
                    the oracles through that tenant's tree alone (ReadsTree,
                    Johnson/Desc/Sound/OmegaCrosses.lean): `readsTree_sig`
                    (Johnson/Desc/Sound/ReadsTreeAt.lean) as it lies: beside the promise's shape
                    and the tie to the first table nothing of these three fields is turned.
  Sh.window_at      o_omega's tree, numbered through the file, is one of the shared chain's own that
                    are sent at its last border: `omega_window`
                    (Johnson/Desc/K14/Law/OmegaWindow.lean) at the constant's numbers.
  Sh.POf_of_window · Sh.POb_of_window   the two fields from the window itself (two comparisons of
                    numbers at the row): for whoever holds the window at the seat.
  Sh.POf_at         **the field POf**: "no collision at Omega" goes from the acting part's strings
                    at the shared chain's last border to the last chain's frame's strings:
                    `omegaForward`.
  Sh.POb_at         **the field POb**: Omega's pin goes back: `omegaBack`.
WHAT STAYS, ALL ON THE ROW T.p₂ :: T.l₂ AND THE PLAN: hlO · hO (the layout of o_omega's sending is
the constant's layO; it has two notices) · Tiled T.p₂ T.l₂ · the piece number 6 and its base (b6) ·
5 ≤ T.l₂.length: `omega_window`'s own premises.
What is not claimed. That these five hold at the seated row. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.K14.Law.OmegaWindow
import Johnson.Desc.Sound.ReadsTreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

namespace Sh

variable {Xi P S₁' S₃' Y X₁ X₂ Cl Cells Tok : Type} (A : ShPlan Xi)
  (O : ShOpen P (P × S₁') Cells Tok A.Q)

/-- At the constant the three letters on a tenant read the oracles through its tree alone. -/
theorem readsTree_at : ReadsTree (tiedMeaning O.get O.Mg₁ (mg A O)) (pm A O) :=
  ⟨fun j t y y' h hp => shownJT_col A.Q.codes A.G (ms A) j t y y' h hp,
    fun j t s y y' h hp => noCollJT_col A.Q.codes A.G (smp₂ A) (ms A) j t s y y' h hp,
    fun j t s y y' w h hp => pinJT_col A.Q.codes A.G O.arr (smp₂ A) (ms A) j t s y y' w h hp⟩

/-- o_omega's tree is one of the shared chain's own that are sent at its last border. -/
theorem window_at {C : CK} {Fr : Frame}
    (f : Piece C Fr ((P × S₁') × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr ((P × S₁') × St) Cl (Wit Cells Tok MsgT)))
    (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A)) (hO : 1 < (withOmega A.Q.S).size)
    (hT : Tiled f l) (x6 : Piece C Fr ((P × S₁') × St) Cl (Wit Cells Tok MsgT))
    (h6 : (f :: l)[6]? = some x6)
    (b6 : x6.base = t₁ A + (layU A).shapes.size + (layO A).shapes.size) (hl : 5 ≤ l.length) :
    (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).lo ≤
        ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 ∧
      ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 <
        hiAt (1 + l.length) f l :=
  omega_window (t₁ A) (layU A) (layO A) A.Q.codes (withOmega A.Q.S) hlO hO O.N₁ _ rfl rfl f l hT x6
    h6 b6 hl

/-- The field POf from the window itself: for whoever holds the window at the seat. -/
theorem POf_of_window (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hw : (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).lo ≤
        ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 ∧
      ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 <
        hiAt (1 + T.l₂.length) T.p₂ T.l₂) :
    ∀ b : ((P × S₁') × St) × (EAll D all).Str,
      (PromS.noColl .oOmega).holds
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) (pm A O)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
          (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂)
          ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
            (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) (pm A O) b.1.2
        (strsOf (frameAt D all D.key₃ T.ft₃) b.2) :=
  omegaForward _ D all Y P S₁' St S₃' X₁ X₂ Cl _ T _ _ _ (readsTree_at A O) hw.1 hw.2

/-- The field POb from the window itself. -/
theorem POb_of_window (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hw : (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).lo ≤
        ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 ∧
      ((tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))).tenant .oOmega).1 <
        hiAt (1 + T.l₂.length) T.p₂ T.l₂) :
    ∀ (b : ((P × S₁') × St) × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      (ItemS.pin .oOmega).holdsSh
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)))
        (tiedMeaning O.get O.Mg₁ (mg A O)) b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)))
        (tiedMeaning O.get O.Mg₁ (mg A O)) T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
          (1 + T.l₂.length)).2 b) w :=
  omegaBack _ D all Y P S₁' St S₃' X₁ X₂ Cl _ T _ _ _ (readsTree_at A O) hw.1 hw.2

/-- **TablesFitR's field POf, at the constant.** -/
theorem POf_at (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A)) (hO : 1 < (withOmega A.Q.S).size)
    (hT : Tiled T.p₂ T.l₂) (x6) (h6 : (T.p₂ :: T.l₂)[6]? = some x6)
    (b6 : x6.base = t₁ A + (layU A).shapes.size + (layO A).shapes.size)
    (hl : 5 ≤ T.l₂.length) :
    ∀ b : ((P × S₁') × St) × (EAll D all).Str,
      (PromS.noColl .oOmega).holds
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) (pm A O)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
          (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂)
          ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
            (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) (pm A O) b.1.2
        (strsOf (frameAt D all D.key₃ T.ft₃) b.2) :=
  omegaForward _ D all Y P S₁' St S₃' X₁ X₂ Cl _ T _ _ _ (readsTree_at A O)
    (window_at A O T.p₂ T.l₂ hlO hO hT x6 h6 b6 hl).1
    (window_at A O T.p₂ T.l₂ hlO hO hT x6 h6 b6 hl).2

/-- **TablesFitR's field POb, at the constant.** -/
theorem POb_at (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A)) (hO : 1 < (withOmega A.Q.S).size)
    (hT : Tiled T.p₂ T.l₂) (x6) (h6 : (T.p₂ :: T.l₂)[6]? = some x6)
    (b6 : x6.base = t₁ A + (layU A).shapes.size + (layO A).shapes.size)
    (hl : 5 ≤ T.l₂.length) :
    ∀ (b : ((P × S₁') × St) × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      (ItemS.pin .oOmega).holdsSh
        (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)))
        (tiedMeaning O.get O.Mg₁ (mg A O)) b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)))
        (tiedMeaning O.get O.Mg₁ (mg A O)) T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂
          (1 + T.l₂.length)).2 b) w :=
  omegaBack _ D all Y P S₁' St S₃' X₁ X₂ Cl _ T _ _ _ (readsTree_at A O)
    (window_at A O T.p₂ T.l₂ hlO hO hT x6 h6 b6 hl).1
    (window_at A O T.p₂ T.l₂ hlO hO hT x6 h6 b6 hl).2

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.readsTree_at
#print axioms Desc.K14.Law.Sh.window_at
#print axioms Desc.K14.Law.Sh.POf_of_window
#print axioms Desc.K14.Law.Sh.POb_of_window
#print axioms Desc.K14.Law.Sh.POf_at
#print axioms Desc.K14.Law.Sh.POb_at
