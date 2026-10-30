-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstJoint.lean: WHAT THE SHARED TABLE's CONSTANT ASKS OF THE FIRST
TABLE's OWN MEANING AT THE JOINT. The constant lays Sh.mg₁ := O.Mg₁: the first
table's own meaning, nothing overlaid. The law at "LIN point" in the form of
Johnson/Desc/Sound/PointReader.lean asks of that meaning four equations and one implication at
reached states. HERE these, with what the front's ride asks, are ONE NAMED PREMISE, in the
    constant's letters.

  Sh.Joint        pin · wrow · evalLaid · wSits: four fields of the first table's meaning are what
                  the joint says of them · pile: inside the first chain's last promise, at a reached
                  last state that has not failed, the sentence on the pending rows that the step
                  back from (Eval) proves gives the first table's own pileOne · po: that pileOne
                      does not read the strings.
  Sh.Reads lo     the letters that the first chain's last promise reads read below lo alone (what
                  the rides of the slot's own condition spend).
WHO PAYS. At the first table's reference form: the four: through Lean in the files on the last
chain's first row (JointFour, JointFour.lean) · pile: by a theorem hpile_end, which is not in this
library (from onlineDescription's return and planOk, with two equations on the data).
What is not claimed. That the five hold at a laid value: not shown here. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.Sound.PointReader

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
open VerifiableInference.Desc.K13.Law

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- **What the constant asks of the first table's own meaning.** -/
structure Joint : Prop where
  pin : O.Mg₁.pin = fun j t a y w => pinJT A.Q.codes A.G O.arr O.smp₁ O.ms₁ j t a y w
  wrow : O.Mg₁.wrow = fun a _ w => WRow O.Pw a.2 (wordsOn (stOf₁ a) (tabP₁ A O a w))
  evalLaid : ∀ a, O.Mg₁.pub .evalLaid a = evalLaidB O.Pw a.2
  wSits : ∀ a, O.Mg₁.pub wSitsItem a = (wSitsB A.Q.codes O.Pw a.2 && wSeatB O.N₁.w a.2)
  pile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd O.get O.N₁ O.Mg₁ O.links (ps A O) p y → O.R p →
    (O.get p).2.failed = none → pileStep stOf₁ (tabP₁ A O) O.Pw O.matC (O.get p) w →
    O.Mg₁.pileOne (O.get p) y w
  po : ∀ a (y y' : Strs) (w : Wit Cells Tok MsgT), O.Mg₁.pileOne a y w → O.Mg₁.pileOne a y' w

/-- The letters that the first chain's last promise reads read the oracles below lo alone. -/
def Reads (lo : ℕ) : Prop :=
  LettersReadBelow lo O.N₁ O.Mg₁
    ((openSets O.links (ps A O) (start O.links))[(ps A O).length]?.getD [])

end Sh

end Desc.K14.Law
