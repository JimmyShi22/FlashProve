-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/TraceTiedAndStartSocketsFilled.lean

Nothing on hiding. No property of the protocol is claimed. Instances of this folder's tops; no new proof.

SIX SOCKETS OF "AtFullSide/Honest/TheOneObject.lean", WHICH IS IMPORTED, FILLED BY NAME: each theorem "‹field›_filled" ends in the field's own type, at that file's own constants ("TiedRequest", "TiedRun", "Socket.‹field›", "TheLetters.first",
"TheLetters.reads", "TheLetters.J₁"); and two examples at the end lay them into a value of "TheThreadsHalf" and of "TheOneObject" by "{ … with … }": that these elaborate is Lean's word that the types fit.
  in "TheThreadsHalf": traceAtTied · tied · startFit · requestParses · served          in "TheOneObject": startJ
Of "TheLetters.OpenFiles" (the letter "files" of "TheOneObject") the fields "seat" and "publicData" bind their own letters, so they are not laid by "with".

THE PREMISES, BY NAME: a head at the return, and the reading hr, which stand in the sockets' own types ("in scope" is the head's first field) · live: the files pass the verifier's test on them (all but "tied") · made: the maker's return at the base filling (traceAtTied, served). "tied" asks nothing more; startFit, requestParses and startJ ask live alone.
NO OTHER PREMISE IS LEFT. That the first, public test of the description accepts the written form of some instance, which the laws beneath four of the six ask, is paid inside ("first_test_accepts_one_written_instance"): by "AtPublicFiles.Start.okStart_of_live" (AtFullSide/T3/StartOfLive.lean), from the head's scope and laid description;
"live" is a binder of that law and is not read by its proof, by its file's word.

Limits. THE EXAMPLES TAKE A VALUE OF THE STRUCTURE AND RETURN ONE: THEY SHOW NO VALUE TO EXIST:
the other fields are not filled here. The library's bar on "validAt" goes with "tied": nothing on hiding follows. What lies beneath through Honest/K3/Term/PlaneNumbersInScope.lean
goes with "served" (Joint/EntersSymbolsPlanesSizesPaid.lean). AtFullSide/K12/Pays* does not lie beneath this file; "KindPays" (Honest/Law/ReadyOfSides.lean) and the forms on it in Honest/Law/ReadyAtOnline.lean, ReadyAtBaseProver.lean do: through TraceAndPublicDataPlugs.lean and TheOneObject.lean. AT A RETURN OF THE BASE FILLING, NOT AT THE ONLINE PROVER: the online return stands in the tie's letters alone. The hash "OnBytes.secondHashFunction" alone.
MODULES Johnson/HonestTrace/Run/SetUp* OF THE EXECUTABLE MODEL's FOLDER LIE BENEATH: beneath
AtFullSide/Honest/TheOneObject.lean (fourteen, through three files in Shape/Scope) and beneath
AtFullSide/T3/StartOfLive.lean (which brings in SetUpScan): by their import lines they bring in
nothing else of that folder. Closed facts by Lean's kernel lie
beneath (among them ClosingW0 to ClosingW4; "theLive_zFull"): replayed by no independent
checker.
-/
import AtFullSide.Honest.TheOneObject
import AtFullSide.HonestTrace.StartFieldsAtTheWrittenScript
import AtFullSide.HonestTrace.StartShapeAtTheFirstState
import AtFullSide.HonestTrace.TiedAtATiedInstance
import AtFullSide.HonestTrace.TraceAndPublicDataPlugs
import AtFullSide.T3.StartOfLive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace HonestTraceRun.Meets

open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes (TableKey)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput tableCoins baseMaker)
open AtFullSide.Honest
open LPFD.Full (instanceAsPlainRecord)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) nonemptyPadZSocketsFilled : Nonempty PadZ :=
  AtPublicFiles.Committed.pads_nonempty OnBytes.Slice.frS 402653181

/- The very instances at which "TiedRequest" is typed. -/
local instance (priority := high) nonemptyRunValueSocketsFilled : Nonempty RunValue :=
  AtFullSide.Honest.nonemptyRunValue_theOneObject

local instance (priority := high) inhabitedRunValueSocketsFilled : Inhabited RunValue :=
  AtFullSide.Honest.inhabitedRunValue_theOneObject

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : VerifierAndGoals.readFiles Z = .ok pp)

/-- **The first, public test of the description accepts the written form of some instance**: under the head and "live". -/
theorem first_test_accepts_one_written_instance (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ z₀, h.description.okStart (instanceAsPlainRecord z₀) = true :=
  ⟨(FlashProve.dataAtFiles FlashProve.flashProveData Z).G.z₀,
    AtPublicFiles.Start.okStart_of_live h.head.scope live h.head.laid _⟩

/-- **"traceAtTied", filled.** -/
theorem traceAtTied_filled (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A) :
    ∀ n w x, TiedRequest h hr n w x → (A.H.trace w.1 x).isSome = true :=
  fun _ _ _ tied => (trace_at_a_tied_instance h.head.scope hr live made h tied.2).2

/-- **"tied", filled.** -/
theorem tied_filled : ∀ r : TiedRun h hr, Socket.tied (A := A) (TheLetters.reads h) r.R :=
  fun r => tied_at_a_tied_instance h (TheLetters.reads h) (fun _ => rfl) _ _ _ _ _ _ _ _ r.tied.2
    r.ready

/-- **"startFit", filled.** -/
theorem startFit_filled (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ r : TiedRun h hr, Socket.startFit h r.x :=
  fun r => HonestTraceRun.StartFields.first_test_accepts_a_tied_instance h
    (first_test_accepts_one_written_instance h live) r.tied.2

/-- **"requestParses", filled.** -/
theorem requestParses_filled (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ r : TiedRun h hr, Socket.requestParses h r.x :=
  fun r => HonestTraceRun.Enters.requestIsReadBackAtFirstThread
    (HonestTraceRun.StartFields.first_test_accepts_a_tied_instance h
      (first_test_accepts_one_written_instance h live) r.tied.2)

/-- **"served", filled.** -/
theorem served_filled (made : baseMaker Z = .ok A) (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ r : TiedRun h hr, Socket.served h (TheLetters.first h) r.R (pursesOf r.c) :=
  fun r => (HonestTraceRun.StartFields.start_fields_at_the_written_script made h
    (TheLetters.numbers h) r.ready
    (HonestTraceRun.StartFields.first_test_accepts_a_tied_instance h
      (first_test_accepts_one_written_instance h live) r.tied.2)).2.2

/-- **"startJ", filled**, at every value of the named holes at the stored files. -/
theorem startJ_filled (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (F : TheLetters.OpenFiles A) :
    ∀ r : TiedRun h hr, Socket.startJ h (TheLetters.J₁ h F) r.x :=
  fun r => start_shape_at_the_first_state h F.base
    (HonestTraceRun.StartFields.first_test_accepts_a_tied_instance h
      (first_test_accepts_one_written_instance h live) r.tied.2)

/-- The five laid into a value of "TheThreadsHalf": a check of types. -/
example [Inhabited P5J.TS] [Inhabited Desc.K14.St] (T : TheThreadsHalf h hr)
    (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) : TheThreadsHalf h hr :=
  { T with
    traceAtTied := traceAtTied_filled h hr live made
    tied := tied_filled h hr
    startFit := startFit_filled h hr live
    requestParses := requestParses_filled h hr live
    served := served_filled h hr made live }

/-- The sixth laid into a value of "TheOneObject": a check of types. -/
example [Inhabited P5J.TS] [Inhabited Desc.K14.St] (O : TheOneObject h hr)
    (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) : TheOneObject h hr :=
  { O with startJ := startJ_filled h hr live O.files }

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.first_test_accepts_one_written_instance
#print axioms HonestTraceRun.Meets.traceAtTied_filled
#print axioms HonestTraceRun.Meets.tied_filled
#print axioms HonestTraceRun.Meets.startFit_filled
#print axioms HonestTraceRun.Meets.requestParses_filled
#print axioms HonestTraceRun.Meets.served_filled
#print axioms HonestTraceRun.Meets.startJ_filled
