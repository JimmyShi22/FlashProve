-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/MaskLettersAtMg.lean (kind K10): THE TIES BETWEEN THE CLOSED FACTS ON THE FRESH MASK's NUMBER (`mask_letters`, Johnson/Desc/First/Close/Law/MaskLaidFull.lean) AND THE CONSTANT's OWN LETTERS, COMPOSED BY LEAN. Theorems: calls.

Why. `AtMg.mask_all` (MaskAtMgAll.lean beside this file) ends at maskNo (At.seats Zp) (At.pseats Zp) l. `mask_letters` stands at maskNo seatsPlanW P5T.psFull l and at the written list `LFull`. That the two numbers are one, and that the list at which the facts on reached states hold is `LFull`, are said and composed here.

What is said. h : AtMg | AtMgA at OnBytes.secondHashFunction.
  `AtMg.maskNo_is`: maskNo (At.seats Zp) (At.pseats Zp) l = maskNo seatsPlanW P5T.psFull l.
  `AtMg.laid_full`: **At.laid? Zp = some LFull**: by `laid_at` (Johnson/HB/LLHARD/LaidWritten.lean) from `AtMg.codes_full` and `written_at_head` (Johnson/P5J/StartAtHead.lean).
  `AtMgA.fold_full`: **FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF LFull) At.reqW fullLinks At.ps**: the list of `AtMgA.fold_at` (NoFoldAtHead.lean beside this file) IS the written one.
  `AtMg.mask_letters_at`: **hfL · hfs · hfa · hfskip of `hCar_end`, at Lp := LFull and fresh := maskNo (At.seats Zp) (At.pseats Zp) l.**
  `AtMg.mask_at_letters`: l < 25 · a reached in front of K10's own sub-protocol ⊢ ∃ mk, the frame's mask is some mk ∧ LFull.places[mk]? = some (maskTree l, maskPart l) ∧ LFull.shapes[maskTree l]? = some (maskShape l).

Limits. AtMg | AtMgA are premises (WITH THE FOURTEEN ENTRY TESTS). rows.fresh behind the closing is not named here (`closeFrame_reads`).
OF `mask_letters_at`'s FOUR CONJUNCTS the third and the fourth hold by the definitions of maskA and
maskSkip, and the second says only that the list has a shape at that tree (MaskLaidFull.lean).
AT THE SECOND HASH FUNCTION. Nothing on soundness.

-/
import Johnson.P5J.MaskAtMgAll
import Johnson.P5J.NoFoldAtHead
import Johnson.Desc.First.Close.Law.MaskLaidFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.First.Close (rdK maskNo seatsPlanW maskTree maskPart maskShape maskA
  maskSkip mask_letters)
open VerifiableInference.Desc.K13.Law (LFull laid_at)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The two spellings of the number are one. -/
theorem AtMg.maskNo_is {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) (l : ℕ) :
    maskNo (At.seats Zp) (At.pseats Zp) l = maskNo seatsPlanW P5T.psFull l := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  rw [e1, e2]

/-- **THE PLAN's LIST AT THE CONSTANT IS THE WRITTEN ONE.** -/
theorem AtMg.laid_full (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.laid? Zp = some LFull :=
  laid_at h.codes_full (written_at_head h).1

/-- **FoldFacts AT THE WRITTEN LIST, FROM THE HEAD ALONE.** -/
theorem AtMgA.fold_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF LFull) At.reqW fullLinks At.ps := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  obtain rfl : L = LFull := Option.some.inj (R.listed.symm.trans h.toAtMg.laid_full)
  exact R.fold

/-- **hfL · hfs · hfa · hfskip AT THE CONSTANT's NUMBER.** -/
theorem AtMg.mask_letters_at {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) (l : ℕ)
    (hl : l < 25) :
    LFull.places[maskNo (At.seats Zp) (At.pseats Zp) l]? = some (maskTree l, maskPart l) ∧
      LFull.shapes[maskTree l]? = some (maskShape l) ∧ (maskShape l).logN = maskA l ∧
      (maskShape l).mainWidth + ((maskShape l).maskSymbols.extract 0 (maskPart l)).foldl (· + ·) 0 =
        maskSkip l := by
  rw [h.maskNo_is l]
  exact mask_letters l hl

/-- **AT A REACHED STATE IN FRONT OF THE CLOSING: THE MASK, ITS SEAT, ITS TREE's SHAPE.** -/
theorem AtMg.mask_at_letters (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps l + 3) a) :
    ∃ mk, (rdK a.1.2).2.1.mask = some mk ∧ LFull.places[mk]? = some (maskTree l, maskPart l) ∧
      LFull.shapes[maskTree l]? = some (maskShape l) :=
  ⟨_, h.mask_all hl a hr, (h.mask_letters_at l hl).1, (h.mask_letters_at l hl).2.1⟩

end P5J

#print axioms P5J.AtMg.maskNo_is
#print axioms P5J.AtMg.laid_full
#print axioms P5J.AtMgA.fold_full
#print axioms P5J.AtMg.mask_letters_at
#print axioms P5J.AtMg.mask_at_letters
