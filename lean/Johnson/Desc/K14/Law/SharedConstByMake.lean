-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstByMake.lean: THE JOINT's TWO PREMISES ON THE COMMITTED TABLE's
DECODER ARE CALLS, AT THE SHARED TABLE's CONSTANT. Sh.on_zero_at asks hdec ("where the first table's
meaning says that the committed table decodes, the shared table's decoder decodes, at the shared
chain's first state"); Sh.rel_end_of_zero asks hPW (the like for the pin on the witness's cells, the
other way). tp_by_make | pw_by_make (Johnson/Desc/Sound/OneByMake.lean) give both, at
every b, WHERE THE FIRST TABLE's DECODER IS MADE OF THE SHARED CHAIN's: decShared: decK at the state
that start₂ makes of the public part. HERE they are called at the constant's letters; the shared
table's side is met by rfl.

  Sh.OneDec       what is asked of the first table's own meaning: two equations: its decodes and its
                  pinW are decShared's, at the constant's decoder's parameters.
  Sh.hdec_by_make **hdec, at every b.**
  Sh.hPW_by_make  **hPW, at every b and w.**
What is not claimed. That the two equations hold at a laid meaning: not shown here. No soundness; no
    level.

-/
import Johnson.Desc.K14.Law.SharedConstZero
import Johnson.Desc.Sound.OneByMake

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

/-- **The first table's decoder is made of the shared chain's.** -/
structure OneDec (start₂ : P → St) : Prop where
  dec : O.Mg₁.decodes =
    decodesOf (decShared A.Q.par 0 2852142980 (rank A) O.held start₂)
  pin : O.Mg₁.pinW = pinWOf (decShared A.Q.par 0 2852142980 (rank A) O.held start₂)

/-- **hdec, at every b: by make.** -/
theorem hdec_by_make (D : WholeD) (all : List LeftT) (start₂ : P → St)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hget : ∀ a, (O.get a).1 = a.1) (h : OneDec A O start₂)
    (b : (P × S₁') × (EAll D all).Str) :
    O.Mg₁.decodes (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
    decodesOf (decT₂ A O) (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (nums A O) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) :=
  tp_by_make A.Q.par 0 2852142980 (rank A) O.held (ckP .two) D all Y P S₁' S₃' X₁ X₂ Cl _ start₂ T
    O.get hget O.N₁ O.Mg₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)) (pm A O) h.dec rfl b

/-- **hPW, at every b and w: by make.** -/
theorem hPW_by_make (D : WholeD) (all : List LeftT) (start₂ : P → St)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (hget : ∀ a, (O.get a).1 = a.1) (h : OneDec A O start₂)
    (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT) :
    (mg A O).pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (nums A O) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
    O.Mg₁.pinW (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w :=
  pw_by_make A.Q.par 0 2852142980 (rank A) O.held (ckP .two) D all Y P S₁' S₃' X₁ X₂ Cl start₂ T
    O.get hget O.N₁ O.Mg₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)) (mg A O) h.pin rfl b w

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hdec_by_make
#print axioms Desc.K14.Law.Sh.hPW_by_make
