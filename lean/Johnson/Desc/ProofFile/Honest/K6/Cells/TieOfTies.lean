-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/TieOfTies.lean: the tie on the cells of the sub-protocol "the
output head's own rounds" (K6): the honest side's cells of the head are, inside the ranges that the
head's relation names, the cells that the head's law reads off the thread's witness: AT THE FIRST
CHAIN's THREAD AT THE LIBRARY's OWN LETTERS (`lettersHead`, Honest/Thread/FirstHead.lean), border
341. One lemma, by calls. No goal is stated.

WHAT IT IS NOT. CONDITIONAL ON THE LIBRARY's ONE HYPOTHESIS h, ON ONE EQUATION ON THE GROUND (hGW)
AND ON THREE PREMISES THAT NOTHING HERE PAYS: hM (`CellsTieOn`, Honest/Law/Rule/TiesOn.lean, at
these letters), hU (`WeightsLaid`, Cells/TensorLaid.lean), hW (the cells that the script makes of
the input hold an index whose entries, in the output matrix's two bands of rows, the reader of the
committed digits reads). (The library has a member of that hypothesis, `P5J.AtMgA`, under four
premises on the three public files: `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean;
nothing here calls that.) That the thread holds at any run is shown nowhere. THE TRACE's TYPE Tr AND
THE TYPE W₀ ARE LETTERS, and so are the two readers cells and weights: no trace of any model is
named. INSIDE THE RANGES ALONE. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as h. The proof
opens neither the thread's half nor Said's: it hands the pair to hM and hW. No measure.

  `cellsTie_of_ties`   **the field cellsTie of the structure of premises `K6Script`
                    (Honest/K6/Law/OutAtThread.lean, which is not imported here), at b := 341, W :=
                    At.X Zp, wit := `headWit'` cells weights Zp G and cut := `compCut` at the
                    library's letters; at every continuation ds** [by reading: the field writes the
                    thread's wit where this statement writes the script's; laid into the structure
                    by nobody yet]

WHO PAYS WHAT. The frame-free half: `sameCells_ours` (Cells/SameOurs.lean). Its geometry:
`inRanges_in_scope` (Johnson/Desc/Kinds/Law/HeadRangesOfNumbers.lean). The full size's two numbers:
`sizes_five` (Law/TablesPlanInScope.lean). The four ranges: hM. The weights: `tensor_of_laid`
(Cells/TensorLaid.lean) on our side, `whOf_index` and `whOfBand` (Law/WhBand.lean) on the law's, hW
between. `seatLay`, `plAt`: Law/PlanK6At.lean. OF THE FOLDER lean/Johnson/Goal/ one definition is
named in the statement: `Meaning.sizesOf` (Johnson/Goal/Meaning/HidPlan.lean); no file of that
folder is imported by this one directly.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.SameOurs
import Johnson.Desc.ProofFile.Honest.K6.Cells.TensorLaid
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOn
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.Kinds.Law.HeadRangesOfNumbers
import Johnson.Desc.Kinds.Law.WhBand
import Johnson.Desc.Kinds.Law.PlanK6At
import Johnson.Desc.Kinds.Law.TablesPlanInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K6
open Inst.Model.Head (oH nD)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (SameCells InFour compCut seatLay plAt workOf)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD cellsTie OF `K6Script`, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS,
FROM TIES IN WHICH THE TRACE's TYPE IS A LETTER**: under the one hypothesis h and one equation on
the ground G. hM: inside the four ranges the honest side's cell of the head's segment, as the
integer of least absolute value, is segment 24's own integer off the thread's witness, at every
continuation: `CellsTieOn` (Honest/Law/Rule/TiesOn.lean) at these letters. hU: five facts on the
public part's layout of the committed weights (`WeightsLaid`): on public data alone. hW: the cells
that the script makes of the input hold an index, and the reader of the committed digits, as the
integer of least absolute value, reads that index's entries in the output matrix's two bands of
rows. The three are premises' forms: nothing is claimed of them. -/
theorem cellsTie_of_ties (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (cells : Tr → Cells) (weights : W₀ → Weights) (G : Ground) (hGW : G.W = P5J.At.X Zp)
    (hM : CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun _ => some ())
      (fun w a rr c =>
        (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells w.trace) a rr c) : Int))
      (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
        (P5J.At.N Zp cF) (Meaning.sizesOf (P5J.At.X Zp))
        (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) v 24 a rr c)
      (InFour (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y)))
    (hU : WeightsLaid (P5J.At.X Zp))
    (hW : ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      ∃ i : Cm.Idx, Holds (Q.cells m.st.input) i ∧ ∀ row col, oH ≤ row → row < oH + 2 * 5120 →
        col < 202048 →
        (ZMod.valMinAbs ((weights m.st.input.w₀).entry row col) : Int) = i.mat row col) :
    ∀ k s m E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E → ∀ ds,
      letI : VerifiableInference.Desc.Kinds.Head.Given :=
        (headWit' cells weights Zp G m.st.input).given
          (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard
      SameCells (headWit' cells weights Zp G m.st.input).cells
        (compCut (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
          (Meaning.sizesOf (P5J.At.X Zp))
          (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
          (plAt (P5J.At.num Zp 24 0) 0) (Q.wit k m.st.input (m.st.heard ++ ds))).1 := by
  intro k s m E hThr ds
  obtain ⟨i, hi, hRd⟩ := hW k s m E hThr
  have hG := VerifiableInference.Desc.Kinds.Head.Law.Came.inRanges_in_scope h.scope h.reads
    h.pubOne (workOf (P5J.At.X Zp))
  obtain ⟨-, -, -, -, -, -, hd5, hV2⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.sizes_five h.scope h.reads h.pubOne
  letI : VerifiableInference.Desc.Kinds.Head.Given :=
    (headWit' cells weights Zp G m.st.input).given
      (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard
  refine sameCells_ours _ _ _ _ _ _ (P5J.At.X Zp) _ (headWhereOf Zp G) (cells m.st.input.trace) _ _
    (by show G.W.hS = _; rw [hGW]) (by show G.W.HLy = _; rw [hGW])
    (by show borderOf G.W.y = _; rw [hGW]) hG
    (fun a rr c hin => hM k s m E hThr () rfl ds a rr c hin) (fun kk vv hk hv => ?_)
  have hk' : kk < 5120 := by
    have : kk < (P5J.At.X Zp).hS.d := hk
    rw [hd5] at this
    exact this
  have hv' : vv < 202048 := by
    have : vv < (P5J.At.X Zp).hS.V := hv
    rw [hV2] at this
    exact this
  show headTensorOf G.W.layers.wsLay (weights m.st.input.w₀) kk vv =
    VerifiableInference.Desc.Kinds.Head.Law.whOf (Q.cells m.st.input) kk vv
  have hwi : VerifiableInference.Desc.Kinds.Head.Law.whOf (Q.cells m.st.input) =
      VerifiableInference.Desc.Kinds.Head.Law.Sym.whOfBand fun q v => i.mat (oH + q) v :=
    VerifiableInference.Desc.Kinds.Head.Law.Sym.whOf_index (Nat.le_refl _) (by decide) hi
  rw [hGW, tensor_of_laid hU hd5 hV2 _ kk vv hk' hv', hwi]
  unfold VerifiableInference.Desc.Kinds.Head.Law.Sym.whOfBand
  rw [if_pos (⟨hk', hv'⟩ : kk < nD ∧ vv < Inst.Model.Head.nV),
    hRd (oH + kk) vv (Nat.le_add_right _ _) (by omega) hv',
    hRd (oH + (5120 + kk)) vv (by omega) (by omega) hv']
  rfl

#print axioms cellsTie_of_ties

end ProofFile.Honest.K6
