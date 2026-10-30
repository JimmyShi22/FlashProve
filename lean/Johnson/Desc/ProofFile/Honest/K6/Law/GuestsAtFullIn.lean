-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/GuestsAtFullIn.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE PREMISE hβ OF k6_guests_of_theTrace (Honest/K6/Law/GuestsOfTheTrace.lean), AND SO THE FIELD
guests OF THE STRUCTURE OF PREMISES K6HeadBelow, AT THE LETTERS OF ProofFile's fullIn
(Honest/AtPureFullIn.lean). THREE FENCES FIRST. (1) hβ HOLDS THERE BY CONSTRUCTION: fullIn's trace
is cellOf at fullTrace, and fullTrace is DEFINED as theTrace at a served instance that instOf reads
(Honest/AtPureFull.lean). (2) NEVER "hβ is paid" without "by construction, at ProofFile's fullIn, which no
program runs". (3) THE DEBT "TraceHinge at the filling that is run" IS NOT TOUCHED.

The letters. W₀ := Cm.Idx and Tr := Cells: fullIn's type. cells := id and weights := fun i =>
⟨entryOf i⟩: K6's own lot in the filling widerFillAt fullIn o S O is headLot headFitsB (headWit' id
wt) at wt := fullIn.weights Z (Honest/AtPureWiderAt.lean). Rc, Ky, X₀, X stay free. Vd STAYS FREE,
with one premise hVd: at a valid input the trace is what fullIn's own function answers at the
input's index and instance. hVd speaks of the input alone; it has the form in which the frame's run
makes a trace (H.trace w₀ x, Honest/Frame.lean); that a run's input meets it is not said here. ONE
INDEX: the input's w₀ stands in the trace and in the weights' tie.

What it is not. THE FILLING THAT IS RUN: by its authors' own head the test programs run widerFillAt
at another value of WiderIn, over a runnable trace at a small example, and nothing compares the two.
fullIn is noncomputable. Nothing says that onlineProverFromPublicFiles returns at widerFillAt fullIn o S O. THAT THE
THREAD STANDS AT ANY RUN: by nothing that we hold. That any input meets Vd is not said
(fullIn_trace_served gives a trace at every served instance that instOf reads). One field of the
structure's twelve. h: the full size and the format's second hash function alone. A law, no part:
modules under lean/Johnson/Goal/ lie in its import closure. Nothing on soundness, on completeness or
on what a proof hides.
It defines nothing.
  k6_beta_at_fullIn     h, hG, hVd ⊢ hβ at these letters
  k6_guests_at_fullIn   h, hG, hVd, the thread ⊢ the field guests at these letters
CALLED: fullIn_trace_some (Honest/AtPureFullIn.lean); headTensor_entryOf_in_scope
(Honest/K6/Law/TensorAtEntryOf.lean); ground_of_blank (Honest/K6/Law/DebtsLess.lean);
public_of_core (Johnson/Meaning/PublicCore.lean); core_of_scope
(Johnson/Goal/Meaning/ScopeCore.lean); k6_guests_of_theTrace.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.GuestsOfTheTrace
import Johnson.Desc.ProofFile.Honest.K6.Law.TensorAtEntryOf
import Johnson.Desc.ProofFile.Honest.AtPureFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (theTrace cellOf ServesAt entryOf)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS fullIn fullIn_trace_some)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headWit' headTensorOf headTensor_entryOf_in_scope)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- hβ HOLDS HERE BY CONSTRUCTION: fullTrace is DEFINED as theTrace at a served instance that instOf
reads. NEVER "hβ is paid" without "by construction, at ProofFile's fullIn, which no program runs". THE
DEBT "TraceHinge at the filling that is run" IS NOT TOUCHED. CONDITIONAL: h; hG; hVd. **hβ AT THE
LETTERS OF fullIn**, at the index i := the input's w₀. -/
theorem k6_beta_at_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Rc : Type} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (w : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells)
    (Vd : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
    (hVd : ∀ v, Vd v → fullIn.trace Zp v.w₀ v.x = some v.trace) :
    Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ProofFile.instOf w.x = some xI ∧
      ServesAt (At.X Zp) i xI ∧ id w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ ∧
      (letI := sizesOf (At.X Zp).hS
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay
           ((fun i : Cm.Idx => (⟨entryOf i⟩ : ProofFile.Honest.Weights)) w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v) := by
  intro hV
  obtain ⟨xI, hx, Sv, hC⟩ := fullIn_trace_some (hVd w hV)
  refine ⟨w.w₀, xI, hx, Sv, hC, ?_⟩
  intro k v hk hv
  have B := OnBytes.Road.Hd.public_of_core h.pubOne
    (OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne)
  have hk' : k < (At.X Zp).hS.d := hk
  have hv' : v < (At.X Zp).hS.V := hv
  rw [B.full.d] at hk'
  rw [B.full.V] at hv'
  rw [ground_of_blank hG]
  exact headTensor_entryOf_in_scope h.scope h.reads h.pubOne w.w₀ k v hk' hv'

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {Rc Ky X₀ X : Type}
  (H : Prover Cm.Idx Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀ X)
  (Q : Script Bk (Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells) (CellsM OnBytes.Flat.numsFull)
    P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
  (Rd : Nat → Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells)
  (Said : Nat → Coins Bk → Mid (Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop)

/-- hβ HOLDS HERE BY CONSTRUCTION: fullTrace is DEFINED as theTrace at a served instance that instOf
reads. NEVER "hβ is paid" without "by construction, at ProofFile's fullIn, which no program runs". THE
DEBT "TraceHinge at the filling that is run" IS NOT TOUCHED. CONDITIONAL: h; hG; hVd; the thread.
**THE FIELD guests OF K6HeadBelow AT THE LETTERS OF fullIn.** -/
theorem k6_guests_at_fullIn {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hVd : ∀ v, Vd v → fullIn.trace Zp v.w₀ v.x = some v.trace) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    letI : Given := (headWit' id (fun i : Cm.Idx => (⟨entryOf i⟩ : ProofFile.Honest.Weights)) Zp G
      m.st.input).given (parOf (At.X Zp).hS (workOf (At.X Zp))) m.st.heard
    CornerGuests (headWit' id (fun i : Cm.Idx => (⟨entryOf i⟩ : ProofFile.Honest.Weights)) Zp G
      m.st.input).cells.toCells :=
  k6_guests_of_theTrace h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id
    (fun i : Cm.Idx => (⟨entryOf i⟩ : ProofFile.Honest.Weights)) hG (k6_beta_at_fullIn h hG w Vd hVd)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_beta_at_fullIn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_guests_at_fullIn
