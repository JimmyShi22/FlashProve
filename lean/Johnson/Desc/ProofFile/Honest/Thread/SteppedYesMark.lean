-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/SteppedYesMark.lean: `head_hK_of_yes` and `head_hK_of_families`
(SteppedYes.lean) with one hypothesis more handed to the clause's proof: the state before the step
bears no mark of failure. At two sorts of sub-protocol of the kind `frame` (the front, and the step
after a segment's batching) the sub-protocol itself does not test the mark, so "every `StepYes`
gives the clause" is false at a marked state. The column `hK` of `owesS_head` (GatherHead.lean) has
the invariant before the step at hand, and the invariant says that there is no mark
(`head_unmarked`, Law/NoHouse/FirstFrontYes.lean). No definition.

  1  `head_hK_of_yesM`   the column `hK`, from the clause at every `StepYes` from an unmarked state
  2  `head_hK_of_familiesM`   the same, family by family (`all_numbers`, Numbers358.lean)

Limits.
  * `f` is an argument. Nothing shows that a clause holds at any step.
  * Full size only, and only under `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says which
    that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FirstFrontYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The column `hK` from `StepYes` at unmarked states.** -/
theorem head_hK_of_yesM (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (f : KindName → Place → TS → TS → Prop)
    (hY : ∀ b, b < 358 → ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ s s', s.failed = none →
      StepYes 0 blk s s' → f blk.place.kind blk.place s s') :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA hd hS
  have hb' : b < cF.blocksInOrder.length := hb
  rw [head_len h] at hb'
  exact hY b hb' blk hblk s s'
    (head_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA.1) (stepYes_of_stepped _ hd hS)

/-- **The same, family by family.** `K b`: the clause holds at every `StepYes` from an unmarked
state at number `b`. -/
theorem head_hK_of_familiesM (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (f : KindName → Place → TS → TS → Prop) {K : Nat → Prop}
    (hKdef : ∀ b, K b ↔ ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ s s', s.failed = none →
      StepYes 0 blk s s' → f blk.place.kind blk.place s s')
    (hfront : K 0) (hlaid : ∀ l, l < 25 → K (14 * l + 1))
    (hhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → K (14 * l + i + 2))
    (hback : ∀ l, l < 25 → ∀ j, 2 ≤ j → j ≤ 7 → K (14 * l + IM.nAt l + j))
    (h353 : K 353) (h354 : K 354) (h355 : K 355) (h356 : K 356) (h357 : K 357) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' :=
  head_hK_of_yesM h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said f fun b hb =>
    (hKdef b).1 (all_numbers K hfront hlaid hhear hback h353 h354 h355 h356 h357 b hb)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_hK_of_yesM
#print axioms ProofFile.Honest.FirstThread.head_hK_of_familiesM
