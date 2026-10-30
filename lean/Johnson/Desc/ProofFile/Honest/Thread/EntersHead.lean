-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/EntersHead.lean: `Enters₁` (Honest/Thread/File.lean) AT THE
FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), CUT INTO
NAMED PREMISES. By `enters₁_of` (Honest/Thread/Enters.lean). What is paid here by unfolding: the
stored columns; no tree is taken over, no round stands in front; the thread begins with the
description's own first state; the reply's clause of `rides` asks nothing at the start (since `b₀`
is above 0); the input is the run's. All of it where `ready` returns. WHAT IS LEFT, BY NAME: the
first state bears no mark (the request passes the start's own test) · the library's promise at the
start · THE ITEMS THAT ARE OPEN AT THE START · the clauses of `rides` beside the reply's, at the
start · what else an input must meet. One lemma.

  `enters_head`

Where the weight lies. The items open at the start (the seal's `start`,
Johnson/Desc/First/Borders.lean) are: no mark; the stored table's pin; the pile; and FOR EACH
SEGMENT the four parts of its relaxed relation, said of the Script's witness. That premise is
handed through as it stands.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`); none of our files calls it; no member of the head
together with the thread's sentence is shown. None is one of the library's goals. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Enters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIRST CHAIN's START, AT THE HEAD.** A conditional lemma on our own definitions. It is none
of the library's goals. -/
theorem enters_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ k = .ok R) (hb₀ : 0 < b₀)
    (hV : Vd R.own) (hRd : Rd 0 R.own (ProofFile.startS Zp ξ.pub))
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none)
    (hP : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.formP 0
      (ξ.pub, ProofFile.startS Zp ξ.pub))
    (hItems : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.Items
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opened 0) k
      (ProofFile.startS Zp ξ.pub) (R.start₁ H) (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])) :
    Enters₁ (F0T OnBytes.secondHashFunction Zp Np cF) H
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread w₀ rc ξ k R := by
  obtain ⟨-, tr, -, hown, -, -, -, -⟩ := ready_ok hR
  have ex : R.own.x = ξ := by rw [hown]
  refine enters₁_of hR (fun _ => rfl) rfl rfl ?_ ⟨?_, ?_⟩ hItems
    ⟨fun hb => absurd hb (Nat.not_le.2 hb₀), hRd⟩ ⟨rfl, hV⟩
  · show ProofFile.startS Zp ξ.pub = ProofFile.startS Zp R.own.x.pub
    rw [ex]
  · show (ProofFile.startS Zp ξ.pub).failed.isNone = true
    rw [hmark]
    rfl
  · show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.formP 0
      (R.own.x.pub, ProofFile.startS Zp ξ.pub)
    rw [ex]
    exact hP

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.enters_head
