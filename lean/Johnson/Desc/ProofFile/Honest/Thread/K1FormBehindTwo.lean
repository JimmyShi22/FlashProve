-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1FormBehindTwo.lean: the part `Form` of the first chain's
invariant at `lettersHead` holds after sub-protocol number 2, the opening of the first segment (kind
K1), from the invariant before it and the sub-protocol's accepting step alone. No definition.

`k1_form_behind_opening` (K1FormBehindEnds.lean) shows this under one hypothesis more: the test on
the samples after the step. The authors of kind K1 now show that test under the library's head
(`K1.samples_opening_head`, Honest/K1/Law/HeldAtTwo.lean), from three facts before the step. The
invariant gives the three: the meaning's `held` (`head_held_smp`), "the state is reached"
(`thr_reach`) and the test on the list of commitment trees (the fourth part of `xk_ew_front`). This
file joins the two lemmas.

  1  `k1_form_behind_two`   from `Thr`, `Stepped` and the library's `StepYes`
  2  `k1_formBehindAtS_two`   the hypothesis `FormBehindAtS` (FormShare.lean) at number 2, at every
     `Said`. `StepYes` comes from `Stepped` and "the draws fit" (`stepYes_of_stepped`,
     SteppedYes.lean)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that the invariant holds at any state of a run, or that the sub-protocol
    accepts anywhere.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K1FormBehindEnds
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.Thread.FormShare
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The part `Form` of the invariant after sub-protocol number 2. -/
theorem k1_form_behind_two {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[2]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    (hy : Johnson.Desc.First.Walk.Tied.StepYes 0 blk s s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (2 + 1) k s' y.2 := by
  have hF := hT.2.2.1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hb : 2 ≤ cF.blocksInOrder.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hblk
    exact Nat.le_of_lt hlt
  have hxE := xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  have hs := K1.samples_opening_head h hblk
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
    (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) m.st.input.x.pub 0
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (IM.xk_parts hxE).2.2.2.1 hyes
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hs
  exact k1_form_behind_opening h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hS hy hs

/-- The hypothesis `FormBehindAtS` at number 2. -/
theorem k1_formBehindAtS_two
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 2 :=
  fun _ hblk _ _ _ _ _ _ _ _ hA hd hS =>
    k1_form_behind_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA.1 hS
      (stepYes_of_stepped _ hd hS)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1_form_behind_two
#print axioms ProofFile.Honest.FirstThread.k1_formBehindAtS_two
