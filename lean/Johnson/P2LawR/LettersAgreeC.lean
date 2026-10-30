-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LettersAgreeC.lean: THE LETTERS OF row0B_at_head (Johnson/P2LawR/RowZeroBAtHead.lean)
AGAINST THE TERMS IN WHICH THE LAST CHAIN's FIELD AT THE VALUE SPELLS THEM (AtMgA.LastLeft's field
row0B, Johnson/P5J/L0/LastFreeT.lean): FIRST PART: THE ROWS THAT NAME NOTHING OF THAT FILE's OWN
CONE. Twelve theorems: eleven stated to be proved by rfl (a refused rfl is a find), one by two
lemmas that lie. No mathematics.

  N₁_is · ms₁_is · get_is · R_is: four fields of `Sh.openAll h (Sh.eCodes_at h)` against
    `P5J.At.N Zp cF` · `P5J.At.ms Zp Z.lay` · the identity · "reached at the first chain's end, at a
    typed instance's public part".
  G_is · arr_is: two fields of `h.𝔇` against `P5J.F0T o Zp Np cF` · `P5J.At.arr Zp`.
  M₁_is: `mgAll h.𝔇 mgBase = h.toAtMg.mq h.𝔇`: `P5J.mgAtAll_is` · `P5J.mgAt_is_mq`.
  links_is: `Sound.linksFull = P5J.fullLinks`.   Cells_is: `CellsQ … = P5J.CellsM numsFull`.
  plan_is: `planAt Zp Np (seatF …) = planAt Zp Np (P5J.F0T …)`.
  S₃_is · piece_is: the pulled IOP as written in Lean (`LLT25.FL`) against the unpulled
    (`P5J.F0T`): the last chain's type of states, and the maker's piece number 0 at any rest.
NOT HERE: the rows that name `L0.getL` · `AtMg.shPlan` · `AtMg.shOpen` ·
`AtMg.rc`.
Limits. Equations of terms. Nothing on soundness.
-/
import Johnson.P2LawR.RowZeroBAtHead
import Johnson.P5J.RowsAtMg
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.LettersC
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat Fo.Peel
    Cb Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (vecAt)
open VerifiableInference.Desc.K1 (shapeAt)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq gLaid parO omegaShapes_pos)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.mem Sh.mg secondAt)
open _root_.Desc.K14.Law.Sh (seatF openAll eCodes_at)
open P5J (AtMgA colsAt)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

open Johnson.Desc.First.Walk.Tied (EndAt₁)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA o Z D₀ r₀ Zp Np cF x₀)

theorem N₁_is : (openAll h (eCodes_at h)).N₁ = P5J.At.N Zp cF := rfl

theorem ms₁_is : (openAll h (eCodes_at h)).ms₁ = P5J.At.ms Zp Z.lay := rfl

theorem get_is (a : ProofFile.InstPub × First.S) : (openAll h (eCodes_at h)).get a = a := rfl

theorem R_is (p : ProofFile.InstPub × First.S) : (openAll h (eCodes_at h)).R p ↔
    (EndAt₁ (P5J.F0T o Zp Np cF) p ∧
      ∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) := Iff.rfl

theorem G_is : h.𝔇.G = P5J.F0T o Zp Np cF := rfl

theorem arr_is : h.𝔇.arr = P5J.At.arr Zp := rfl

theorem M₁_is : mgAll h.𝔇 mgBase = h.toAtMg.mq h.𝔇 :=
  (P5J.mgAtAll_is h).trans (P5J.mgAt_is_mq h.toAtMg h.𝔇)

theorem links_is : Sound.linksFull = P5J.fullLinks := rfl

theorem Cells_is : CellsQ numsFull.rows (colsAt numsFull) = P5J.CellsM numsFull := rfl

theorem plan_is : planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF) =
    planAt Zp Np (P5J.F0T o Zp Np cF) := rfl

theorem S₃_is : (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₃ =
    (P5J.F0T o Zp Np cF).S₃ := rfl

theorem piece_is {Cells Tok : Type} (D : WholeD)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt D (allOf D) D.key₃ (P5J.F0T o Zp Np cF).lastChainFirstTreeNumber)
      (((P5J.F0T o Zp Np cF).XiPub × (P5J.F0T o Zp Np cF).S₁ × (P5J.F0T o Zp Np cF).S₂) ×
        (P5J.F0T o Zp Np cF).S₃) (Wit Cells Tok MsgT) ds) :
    pieceZeroAt (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF) D (c0 Zp) rest₃ =
      pieceZeroAt (P5J.F0T o Zp Np cF) D (c0 Zp) rest₃ := rfl

end P2Law.LettersC

#print axioms P2Law.LettersC.M₁_is
#print axioms P2Law.LettersC.piece_is
