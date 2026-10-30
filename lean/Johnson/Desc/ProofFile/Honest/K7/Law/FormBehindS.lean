-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Law/FormBehindS.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE
STEP OF THE MEMBER NUMBER 338, THE NEXT TOKEN's (kind K7), WITH MORE IN FRONT: from the pair "the
thread and what is said" (ThrS, Honest/Thread/Said.lean) and "the challenges fit the member's
rounds", at the member of the thread's own list. One statement with its proof: one call of
k7_form_behind (Honest/K7/Law/FormBehind.lean), which asks less: the thread alone.

  k7_form_behindS   CONDITIONAL: at every Said

What it is for. A caller that gathers the form behind every member may ask it from these premises.

Limits. Conditional. h (the library's head, P5J.AtMgA, Johnson/P5J/MgAtAll.lean) is a hypothesis.
NOTHING SHOWS THAT THE THREAD, WHAT IS SAID, OR THE MEMBER's STEP IS MET ANYWHERE: where one of them
is not met the statement says nothing; Said is a letter, and one premise more that can be empty.
"The challenges fit" is a premise that the proof does not spend. It speaks of the form alone.
Through its imports the file stands above the library's folder ThirdParty/. At the library's full
size and the format's second hash function alone. All further Limits of Honest/K7/Law/FormBehind.lean hold
here too. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K7.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K7
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FORM BEHIND THE STEP OF THE MEMBER NUMBER 338, FROM THE PAIR.** CONDITIONAL: under the
hypothesis h; blk is the member number 338 of the thread's list; the thread and what is said, in
front; the challenges fit (not spent); the member's step. -/
theorem k7_form_behindS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[338]? = some blk →
      ∀ k s m E ds y cols s',
        ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 338 k s m E →
        drawsFit blk.rounds ds = true →
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
          cols s' →
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (338 + 1) k s' y.2 :=
  fun blk hb k s m E ds y cols s' hT _ hS =>
    k7_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hb k s m E ds y cols s' hT.1 hS

end ProofFile.Honest.K7

#print axioms ProofFile.Honest.K7.k7_form_behindS
