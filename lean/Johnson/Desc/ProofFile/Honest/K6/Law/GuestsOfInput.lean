-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/GuestsOfInput.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE FIELD guests OF `K6HeadBelow` (Honest/K6/Law/ScriptBelowFree.lean), A SENTENCE ON EVERY STATE AT
WHICH THE THREAD STANDS, EXCHANGED FOR ONE PREMISE hw ON THE ONE INPUT w: UNDER h, hG AND hw, WHERE
THE THREAD STANDS. AN EXCHANGE, NOT A PAYMENT: hw IS PAID BY NOBODY: that the prover's trace is the
library's trFull where the head reads. No definition; one theorem.

What hw says. Under Vd w there are an index i, an instance xI and planes pl with: the planes have
the values 0 and 1, and i serves xI (the library's `ServesAt`); the reader's matrices off w.trace
are the images of list 24 of the library's honest trace `trFull` at the places that the head's
relation names (`ReaderMeets`, Honest/K6/Law/SameCellsTraceAt.lean); the head's weights off w.w₀ are
the index's; the request and the token that the small input reads off w.x are xI's.

Whose debt hw is. THE SAME DEBT HAS BEEN NAMED BY THREE AUTHORS' GROUPS: "that the input's trace is
theTrace at the input's own index and instance"; "which trace". The library names the form of its
first half: `TraceHinge` (Johnson/HonestTrace/TraceHinge.lean: where a trace, as a function of an
index and an input, is there, it is `theTrace` at a served instance read off the input). At one
filling of the frame, which nobody runs, its authors have that form (their fullTrace_some, by their
own word); at the fillings that are run it is a premise on the filling's trace, paid by nobody.
From `TraceHinge` to hw there lack: that the input's trace is the prover's own field's; the reader;
the weights; the instance's two spellings.

The road. The thread's last clause says that the input is valid: at these letters: it is w, and Vd
w. The letters that `CornerGuests` reads (sizes, policy, request, token) come of the place's public
numbers and of the small input's request and token, not of the challenges heard
(`HeadAsk.given`, Honest/K6/Ask.lean). At the cells read off trFull the guests are 0
(`headCells_honest_in_scope`, Honest/K6/Law/TraceCellsInScope.lean: the first field of
`HonestHead`); the prover's cells agree with these on what the head's relation names
(`sameCells_trace_at`); the guests read no cell beyond (the library's `rider_same`).

Limits.
  * hw IS A PREMISE ON THE PROVER's INPUT (w.trace, w.w₀, w.x). No law may take it unseen.
  * THAT THE THREAD STANDS AT ANY RUN: by nothing that we hold: where it stands nowhere the theorem
    holds for nothing.
  * h: the full size and the format's second hash function alone.
  * That the segment which the reader's numbers name is number 24 is neither asked nor used.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure, and it calls
    `meetsAll_in_scope` and `ok_in_scope`, which are declared there.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptBelowFree
import Johnson.Desc.ProofFile.Honest.K6.Law.SameCellsTraceAt
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCellsInScope
import Johnson.Desc.Kinds.Law.HeadCellsAtCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (trFull ServesAt meetsAll_in_scope)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headWit' headWhereOf headTensorOf headCellsOf ReaderMeets sameCells_trace_at)
open VerifiableInference.Desc.Kinds.Head.Law.Came (traceCells headCells_honest_in_scope rider_same)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- hw IS PAID BY NOBODY: that the prover's trace is the library's trFull where the head reads.
CONDITIONAL: the hypothesis h; hG; the thread; hw. **THE FIELD guests OF `K6HeadBelow`, EXCHANGED
FOR ONE PREMISE ON THE ONE INPUT w.** -/
theorem k6_guests_of_input (cells : Tr → ProofFile.Honest.Cells) (weights : W₀ → ProofFile.Honest.Weights)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hw : Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref) (pl : ℕ → ℕ → ℕ → ℤ),
      (∀ k r c, pl k r c = 0 ∨ pl k r c = 1) ∧ ServesAt (At.X Zp) i xI ∧
      (letI := sizesOf (At.X Zp).hS
       ReaderMeets (At.X Zp) (headWhereOf Zp G) (cells w.trace) (trFull (At.X Zp) pl i xI) ∧
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v) ∧
      requestOf (ProofFile.startS Zp w.x.pub) = reqX xI ∧
      OnBytes.Desc.Reply.tokOf w.x.asked = xI.y.val) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    letI : Given := (headWit' cells weights Zp G m.st.input).given
      (parOf (At.X Zp).hS (workOf (At.X Zp))) m.st.heard
    CornerGuests (headWit' cells weights Zp G m.st.input).cells.toCells := by
  intro k s m E hT
  have hv : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  obtain ⟨ew, hVd⟩ := hv
  rw [ew] at hVd
  obtain ⟨i, xI, pl, h01, Sv, ⟨hM, hWh⟩, hreq, hy⟩ := hw hVd
  have eW : G.W = (At.X Zp) := ground_of_blank hG
  show (letI : Sizes := sizesOf (At.X Zp).hS
        letI : Policy := (parOf (At.X Zp).hS (workOf (At.X Zp))).policy
        letI : Request := requestOf (ProofFile.startS Zp m.st.input.x.pub)
        letI : Token := ⟨OnBytes.Desc.Reply.tokOf m.st.input.x.asked⟩
        CornerGuests (headCellsOf (headWhereOf Zp G) (cells m.st.input.trace)
          (headTensorOf G.W.layers.wsLay (weights m.st.input.w₀))).toCells)
  rw [ew, hreq, hy]
  letI : Sizes := sizesOf (At.X Zp).hS
  letI : Policy := (parOf (At.X Zp).hS (workOf (At.X Zp))).policy
  letI : Request := reqX xI
  letI : Token := ⟨xI.y.val⟩
  have g0 : CornerGuests (traceCells (At.X Zp) i (trFull (At.X Zp) pl i xI)).toCells :=
    (headCells_honest_in_scope h.scope h.reads h.pubOne h01 Sv (workOf (At.X Zp))).2.1.guests
  have hs : ∀ a r c, |trFull (At.X Zp) pl i xI 24 a r c| < 129 := fun a r c =>
    (meetsAll_in_scope h.scope h.reads h.pubOne h01 Sv).small 24 a r c
  have S := sameCells_trace_at (X := (At.X Zp)) (i := i) (T := trFull (At.X Zp) pl i xI)
    (headWhereOf Zp G) (cells w.trace) (headTensorOf G.W.layers.wsLay (weights w.w₀))
    (by show G.W.hS = _; rw [eW]) (by show G.W.HLy = _; rw [eW])
    (by show OnBytes.Model.Verify.borderOf G.W.y = _; rw [eW]) hM hs hWh
  have P : PlanFacts := planFacts (sT := (At.X Zp).hS.tabS)
    (InScope.ok_in_scope h.scope h.reads h.pubOne (workOf (At.X Zp)))
  exact rider_same (Came.SameCells.symm' S) P g0

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_guests_of_input
