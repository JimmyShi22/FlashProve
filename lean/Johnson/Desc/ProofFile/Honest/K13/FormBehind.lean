-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/FormBehind.lean: kind K13, the members' batching: CONDITIONAL: THE
THREAD's FORM BEHIND THE STEP OF THE KIND's MEMBER (number 355 of the first chain's 358), at the
first chain's thread at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean). One
statement with its proof; no definition. IT SHOWS NOTHING NEW: it is `k13_thread_form_at`
(BehindAtM3At.lean of this folder), which is general in all parameters of `lettersAt`, called at
the parameters that `lettersHead` lays.

Main name: `k13_form_behind`: **from the thread in front and the member's step: the form one border
on, at where the prover's run then stands.**

The one premise beside its own two (the thread in front; the member's step): h: the library's head
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). General in all parameters of `lettersHead`.

How, all beneath `k13_thread_form_at`. The form at a border is "no mark" and the table's promise
at the honest parameters. The promise behind the batching follows from the promise in front by
`onAt_behind` (Johnson/Desc/K13/Honest/PromiseBehind.lean), general in the meaning: from what is
asked of the table (`RowM3`) and of the meaning's public items (`PubM3`), that the masks are taken,
that the shape fits, no mark, and five implications on the meaning's parameters, which are shown at
the honest parameters in `form_behind` (BehindAtM3.lean). At the library's own parameters the
first two are `m3_rowM3`, `pubM3_at` and `m3_noPub_at` (BehindAtM3At.lean); that the member's yes is
the kind's own sub-protocol's: `k13_memberIs_at` (FromThreadAt.lean).

Limits. Conditional: where the thread does not hold, or the member's step does not say yes, nothing
is said. The full size and the format's second hash function alone, as h. It speaks of the form
alone: not
of what rides, of what the step keeps, or of the items that the row owes. BENEATH IT LIE CLOSED
FACTS THAT LEAN's KERNEL DECIDES BY EVALUATION at the written list of 358 places: three in files of
this folder: `m3_rowB`, `m3_noPub` (BehindAtM3At.lean), `m3_place` (FromThreadAt.lean); and at least
`HashBuild.places_nodup_full` (Johnson/Desc/AtSeats/CountsAtFour.lean), which `counts_at` calls;
what lies deeper was not walked. The first two have not been tried at a second proof checker (so
their file's head).

What is not claimed. That h can be met (on that: the head of Honest/Thread/FirstHead.lean). That the
thread holds at any run, or that the member's step accepts. It is none of the library's goals.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.BehindAtM3At
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FORM BEHIND THE STEP OF THE MEMBER OF KIND K13.** CONDITIONAL: under the hypothesis h; blk
is the member number 355 of the first chain's flat list; the thread in front; the member's step. -/
theorem k13_form_behind :
    ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (355 + 1) k s' y.2 :=
  fun _ hb _ _ _ _ _ _ _ _ hT hS =>
    k13_thread_form_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hb hT.2.2.1 hS

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_form_behind
