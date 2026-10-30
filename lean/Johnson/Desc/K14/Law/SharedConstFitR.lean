-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFitR.lean: TWO FIELDS OF "THE TABLES FIT" (the structure
TablesFitR, Johnson/P5J/TopTablesR.lean), TP AND PW, IN THE FIELDS' OWN LETTERS, AT THE SHARED
TABLE's CONSTANT: N₁ := O.N₁ · Mg₁ := O.Mg₁ · get := O.get · Ns := the shared chain's numbers · Pm
:= Sh.pm A O · Mg := Sh.mg A O. They are Sh.hdec_by_make | Sh.hPW_by_make
(Johnson/Desc/K14/Law/SharedConstByMake.lean): the constant's nums A O is tiedNumbers O.N₁ Ns, and
its promise's "the committed table decodes" is the decoder's, as terms. This file does not import
that structure: the two statements are its fields' texts, letter for letter, so that whoever fills
it lays them by name.

  Sh.nums_is      the constant's numbers are the tied numbers: as terms.
  Sh.TP_at        **the field TP.**
  Sh.PW_at        **the field PW.**
WHAT STAYS. hget (the reader get keeps the public part: rfl at the seat: Sh.hget_at) · Sh.OneDec A O
start₂ (the first table's decodes | pinW are made of the shared chain's decoder: two equations on
O.Mg₁).
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstByMake

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

/-- The constant's numbers are the tied numbers. -/
theorem nums_is : nums A O = tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)) :=
    rfl

/-- **TablesFitR's field TP, at the constant.** -/
theorem TP_at (D : WholeD) (all : List LeftT) (start₂ : P → St)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hget : ∀ a, (O.get a).1 = a.1) (h : OneDec A O start₂) :
    ∀ b : (P × S₁') × (EAll D all).Str,
      O.Mg₁.decodes (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      (pm A O).tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂ 0).2
            ((b.1, start₂ b.1.1), b.2))) :=
  fun b => hdec_by_make A O D all start₂ T hget h b

/-- **TablesFitR's field PW, at the constant.** -/
theorem PW_at (D : WholeD) (all : List LeftT) (start₂ : P → St)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hget : ∀ a, (O.get a).1 = a.1) (h : OneDec A O start₂) :
    ∀ (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      (mg A O).pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))) T.p₂ T.l₂ 0).2
            ((b.1, start₂ b.1.1), b.2))) w →
      O.Mg₁.pinW (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w :=
  fun b w => hPW_by_make A O D all start₂ T hget h b w

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.nums_is
#print axioms Desc.K14.Law.Sh.TP_at
#print axioms Desc.K14.Law.Sh.PW_at
