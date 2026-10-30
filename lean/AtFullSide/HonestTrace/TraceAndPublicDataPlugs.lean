-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/TraceAndPublicDataPlugs.lean

Nothing on hiding. No property of the protocol is claimed. Theorems alone; joinings by calls.

TWO MORE PLUGS FOR THE THREADS' ONE OBJECT.
(1) THE TRACE AT A TIED INSTANCE, AT THE BASE PROVER. No payment of a kind and no "okStart" is asked.
* "trace_at_a_tied_instance": scope, read, live, the base return, a head at it, "TiedYes … (ServedRequest committerCoinCountLessOne files read) n w x" ⊢ A.H.inRange w.1 = true ∧ (A.H.trace w.1 x).isSome = true: the two
  premises on the input of "ready_of_sides" (Johnson/Desc/ProofFile/Honest/Law/ReadyOfSides.lean).
* "trace_value_at_a_tied_instance": the same with the value: there are an index i that the matrix w.1 holds and a typed request x' that i serves, x is written of x', and the trace IS the honest
  trace of that index and request, read by "cellOf".
* "ready_returns_at_a_tied_instance_by_the_sides": so under "ReadyDebts A.F A.B A.H" "ready" returns there, at the return's own description A.F and at all coins: by "ready_of_sides" alone: the cone on the
  kinds' payments is not beneath this form.
(2) THE PUBLIC DATA UNDER A HEAD.
* "public_data_at_a_head": under a head at a return, at any files: publicOfO secondHashFunction files.pol files.KL (some files.lay) = .ok (P5J.At.X A.Z): the head's field "pubOne" with "publicOfO_older".
* "public_data_is_the_heads": whatever "publicOfO" returns there IS that value: so two letters X₀ in two statements at the same files are one.
That "publicOfO" returns at the stored files, with no premise, is another file's theorem and is not repeated here; these two say WHAT it returns.

Limits. The socket "traceAtTied" of the one object asks the second conjunct of "trace_at_a_tied_instance" at closed letters; that object is not imported: the fit is by reading. "ReadyDebts A.F A.B A.H" is a premise, shown of no return here. The served request's relation
is "ServedRequest committerCoinCountLessOne files read". AT A RETURN OF THE BASE FILLING, NOT AT THE ONLINE PROVER. The hash "OnBytes.secondHashFunction" alone.
-/
import AtFullSide.HonestTrace.EntersAtStoredFilesInput
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace HonestTraceRun.Meets

open OnBytes (TableKey)
open OnBytes.HonestTrace (ServesAt cellOf theTrace)
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc (Chain)
open P5J (TS)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles WZ TiedYes descZ ServedRequest)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (tableCoins baseMaker)
open LPFD.Full (XF instanceAsPlainRecord)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {pp : Inst.Model.ScalesAndPolicy}
  {R₂ R₃ : Type} [Inhabited R₃] {run₂ : R₂ → ByteArray} {run₃ : R₃ → ByteArray} {Tr X₀ X' : Type}
  {B : ProverCoinCounts} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Tr X₀ X'}
  {Hp : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X'} {n : ℕ} {w : WZ files} {x : ProofFile.Inst}

/-- **At a tied instance the index is in range and the base prover has a trace.** -/
theorem trace_at_a_tied_instance (scope : VerifierAndGoals.InScope files = true)
    (read : VerifierAndGoals.readFiles files = .ok pp) (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : baseMaker files = .ok A) (H : HeadAtReturn files A)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp (ServedRequest committerCoinCountLessOne files read) n w x) :
    A.H.inRange w.1 = true ∧ (A.H.trace w.1 x).isSome = true := by
  obtain ⟨x', yes, rfl⟩ := tied.1
  exact (OnBytes.HonestTrace.EntersAtStoredFiles.servedInput_atBaseReturn files scope read live H
    made yes).1 _

/-- **The same with the value**: the trace is the honest trace of an index that the run's own matrix holds and of the typed request of which the instance is written. -/
theorem trace_value_at_a_tied_instance (scope : VerifierAndGoals.InScope files = true)
    (read : VerifierAndGoals.readFiles files = .ok pp) (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : baseMaker files = .ok A) (H : HeadAtReturn files A)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp (ServedRequest committerCoinCountLessOne files read) n w x) :
    ∃ (i : Cm.Idx) (x' : XF), Holds w.1 i ∧ ServesAt (P5J.At.X A.Z) i x'.val ∧
      x = instanceAsPlainRecord (x', (protocolAtFiles files).recOf w.1 w.2.1 w.2.2) ∧
      A.H.trace w.1 x = some ⟨cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x'.val)⟩ := by
  obtain ⟨x', yes, rfl⟩ := tied.1
  obtain ⟨-, i, holds, serves⟩ :=
    OnBytes.HonestTrace.EntersAtStoredFiles.servedInput_atBaseReturn files scope read live H made
      yes
  refine ⟨i, x', holds, serves, rfl, ?_⟩
  rw [atPure_trace made]
  show ((indexOf w.1).bind fun j => fullIn.trace A.Z j (instanceAsPlainRecord (x', _))) = _
  rw [fullIn_trace_through_of_holds A.Z holds]
  exact OnBytes.HonestTrace.fullIn_trace_of_servesAt serves x'.property _

/-- **"ready" returns at a tied instance, by the sides' debts alone**, at the return's own description. -/
theorem ready_returns_at_a_tied_instance_by_the_sides (scope : VerifierAndGoals.InScope files = true)
    (read : VerifierAndGoals.readFiles files = .ok pp) (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : baseMaker files = .ok A) (H : HeadAtReturn files A) (debts : ReadyDebts A.F A.B A.H)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp (ServedRequest committerCoinCountLessOne files read) n w x)
    (rc : IndexCommitterCoins) (k : Coins A.B) : ∃ R, ready A.F A.B A.H w.1 rc x k = .ok R :=
  ready_of_sides debts (trace_at_a_tied_instance scope read live made H tied).1
    (trace_at_a_tied_instance scope read live made H tied).2 rc k

omit [Inhabited R₃] in
/-- **The public data under a head at a return**: what "publicOfO" returns at the files is the return's own public data. -/
theorem public_data_at_a_head {W₀ Rc Tr' X₀' X'' : Type} {A' : OnlineProverWithDescription W₀ Rc Tr' X₀' X''}
    (H : HeadAtReturn files A') :
    publicOfO OnBytes.secondHashFunction files.pol files.KL (some files.lay) = .ok (P5J.At.X A'.Z) := by
  rw [VerifiableInference.PlanWritten.publicOfO_older]
  exact H.head.toAtMg.pubOne

omit [Inhabited R₃] in
/-- **Whatever "publicOfO" returns there is that value.** -/
theorem public_data_is_the_heads {W₀ Rc Tr' X₀' X'' : Type} {A' : OnlineProverWithDescription W₀ Rc Tr' X₀' X''}
    (H : HeadAtReturn files A') {X : OnBytes.Model.Verify.Public}
    (returned : publicOfO OnBytes.secondHashFunction files.pol files.KL (some files.lay) = .ok X) :
    X = P5J.At.X A'.Z :=
  Except.ok.inj (returned.symm.trans (public_data_at_a_head H))

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.trace_at_a_tied_instance
#print axioms HonestTraceRun.Meets.trace_value_at_a_tied_instance
#print axioms HonestTraceRun.Meets.ready_returns_at_a_tied_instance_by_the_sides
#print axioms HonestTraceRun.Meets.public_data_at_a_head
#print axioms HonestTraceRun.Meets.public_data_is_the_heads
