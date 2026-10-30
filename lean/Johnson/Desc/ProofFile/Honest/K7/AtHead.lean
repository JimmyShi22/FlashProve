-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtHead.lean: behind the yes of the next token's member (kind K7,
number 338) at the first chain's thread of `lettersHead`: the statement `BehindS` without the record
`K7Ties`. The form behind is `k7_form_behindS`, the reply's clause is `k7_laysS`. Two premises stay: what
the letter `Rd` says at border 339, and that the accepting step gives the clause of `keeps`.

  `k7_behind_at_head`   `BehindS` at the member

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtSeat
import Johnson.Desc.ProofFile.Honest.K7.Law.FormBehindS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **Behind its yes, at the thread of `lettersHead`.** -/
theorem k7_behind_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {V : Nat} {blk : Block TS ProofFile.Cl} {G : ProofFile.Ground} {x₀ : Block TS Unit} {a : Place}
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (K : K7Stands (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 338 24 V blk)
    (Dm : K7Made Zp G 24 blk x₀ a fs f)
    (hRd : ∀ v s, Rd 339 v s)
    (hK : ∀ k s m E ds y cols s', ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 338 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 338 s s') :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 338 := by
  intro blk' hblk k s mm E ds y cols s' hA hd hS
  obtain rfl : blk = blk' := Option.some.inj (K.member.symm.trans hblk)
  have hr : s'.out.reply = some mm.st.input.x.asked :=
    k7_laysS Said K Dm 0 0 blk hblk k s mm E ds y cols s' hA hd hS
  have hin : y.2.st.input = mm.st.input := (play_mid _ _ _ _ _ hS.1.1.choose_spec.2).1
  refine ⟨K7.k7_form_behindS h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said blk hblk k s mm E ds y
    cols s' hA hd hS, ⟨fun _ => by rw [hin]; exact hr, hRd _ _⟩, hK k s mm E ds y cols s' hA hd hS⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k7_behind_at_head
