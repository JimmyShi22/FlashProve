-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Accepted.lean: the closing of a segment (K10): at all 25 closings of the proof file's
first chain the closing's block accepts whatever the closing's part sends: the form `AcceptedS` (Honest/Thread/PaysS.lean)
at the first chain's thread under the library's head, at any prover whose list of halves serves the closings' places by the
closings' own halves. The prover H, the types of the index and of the stored tables' randomness, and all the thread's
further parameters are letters.

  `maskFresh_at_stand`   at a stand (`Thr`) in front of a closing the message that the frame names as the fresh mask is
                       neither sampled nor spent as a mask (Pay/FreshAtClosing.lean, at what Pay/Run.lean and Pay/FoldAt.lean
                       give at a stand)
  `closeBase_stand`      under the head, at the block that `Tied` names, at a stand at `SaidOk`: the twenty facts of
                       `CloseBase` (Johnson/Desc/K10/Honest/Base.lean) hold of the record of the verifier's state
  **`acceptedS_at_closing`**   `AcceptedS 𝕋 Said fall b` at each closing's border b, at every fall and at every Said that gives
                       `SaidOk`, from `ClosingsFirst` (Honest/K10/Thr/HalfOfLot.lean) of the prover's list of halves

Limits.
  * The head is a premise, and so is `ClosingsFirst`.
  * That the thread's invariant holds at any run is not said, here or in a file beneath: where it holds at no stand of a
    border, `AcceptedS` holds there for nothing. So this is not the sentence that the verifier accepts a run.
  * Four of the twenty facts (nothing is owed; a test can begin; the count of rows; the mask is not spent) draw on the
    stand's clause on the table's promise, which the member in front of the closing has to hand on.
  * `AcceptedS` at a closing is a fact on the verifier's state: the block's yes depends on nothing that is sent beyond the
    rounds' shape. It holds as well of a part that sends the fold's words at empty tables: what the part sends is not said.
  * It asks nothing where `chainSteps` returns no steps for the block.
  * The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Ready
import Johnson.Desc.ProofFile.Honest.K10.Pay.FreshAtClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head, written out once. The option turns off one early look of the notation
-- command, which has no case for a field access; each use is elaborated and type-checked as any term is.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a stand in front of a closing the fresh mask's message is neither sampled nor spent.** -/
theorem maskFresh_at_stand {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) : MaskFresh s := by
  intro mk y hm hy
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hl : l < 25 := link_lt h hlt
  have hf : s.failed = none := (run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT).1
  have hr := thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT
  have hbegin := run_begin h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT (frame_there h hl hr)
  obtain ⟨y', hy', -, -, -, ha⟩ := mask_message h hl hr hf hm
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  exact fresh_of_begin h.toAtMg hl hr hbegin hm hy ha

/-- **At a stand in front of a closing the twenty facts hold of the record of the verifier's state.** -/
theorem closeBase_stand {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : ThrS 𝕋 SaidOk (14 * l + IM.nAt l + 5) k s m En) : ∃ B : BaseData, CloseBase Qc (recOf s) B :=
  closeBase_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT
    (maskFresh_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT.1)

/-- **The closing's block accepts at each of the 25 closings**, at every fall and at every Said that gives `SaidOk`,
given the premise on the prover's list of halves. -/
theorem acceptedS_at_closing (l : Nat) (hl : l < 25) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS 𝕋 Said fall (14 * l + IM.nAt l + 5) := by
  obtain ⟨p, Qc, blk, Td⟩ := tied_at_head h.toAtMg l hl
  exact acceptedS_of_fresh h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl readers rows stAt Gr hF hSaid fall
    fun _ _ _ _ hT => maskFresh_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT.1

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.maskFresh_at_stand
#print axioms ProofFile.Honest.K10.closeBase_stand
#print axioms ProofFile.Honest.K10.acceptedS_at_closing
