-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersItemsOverMatrices.lean

Nothing on hiding. No property of the protocol is claimed. Theorems and one structure of premises.

THE ITEMS THAT ARE OPEN AT THE FIRST CHAIN's START, AT A PROVER OVER THE MATRICES. At a return A of the maker "onlineProverFromPublicFiles" at ANY filling over
the matrices ("AtPublicFiles.AtFiles.FullSizeMatrix") whose trace is "fullIn"'s read through the index that the matrix holds (the field "trace" of
"matrixInput", E2E/TheHonestProver.lean); the types of the coins and of the own states are letters, so it stands at the online filling
of that file and at the filling inside it alike. Under the head h : AtMgA ..., at an input that meets "ReadyInput" at the returned
prover, and at ANY Script Q that reads that input as "ScriptReadsTheInput" says: "ScriptTies" (Johnson/Goal/HonestTrace/ConstrAtThread.lean) holds at an index
that the input's matrix holds and at the instance that the input's bytes are read as; so all 100 items "constr l p" hold, and, where
the state bears no mark and the pile's item holds, all 103 items that are open at border 0
("opened_at_start_of_mark_pile", Johnson/Goal/HonestTrace/ConstrItemsAtStart.lean).

Main definitions and theorems:
* "ScriptReadsTheInput": three clauses on the Script at one run's coins and one input: its cells hold what the input's matrix holds;
  its token makes the request; its messages at the layout's seats are the packing of the model's trace. Each clause is asked only
  under what "ReadyInput" yields there, so that its payer may spend all of it.
* "scriptTies_of_readyInput": ReadyInput and ScriptReadsTheInput give an index, an instance, ServesAt and ScriptTies.
* "constr_items_over_matrices", "items_open_at_the_start_over_matrices": the 100 items; the 103.
* "items_open_at_the_start_of_ready": the same where "ready" returns and "okStart" accepts.

Limits. NO SCRIPT IS SHOWN TO MEET "ScriptReadsTheInput": Q is a letter, and so all four theorems may hold emptily. Its third clause
is the weight: that the messages which a Script lays hold the packing of the input's own trace. The head h, the maker's return,
"no mark" and the pile's item are premises. The limits of the files called come with them: the full
size alone; the hash "OnBytes.secondHashFunction" alone; the theorems speak of the witness that Q makes, not of
every witness.
Not claimed: that "ready" returns; that a part plays; that a verifier accepts.
-/
import Johnson.HonestTrace.Joint.JointMeetsD
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Goal.HonestTrace.ConstrItemsAtStart
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.HonestTrace
open Inst.Model Inst.Model.All
open OnBytes.Road
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (Item Part)
open P5J (TS AtMgA CellsM)
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles.Flat (indexOf Holds)

variable {files : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}
  {Rc X₀ X : Type}

/-- A prover's input over the matrices: a matrix, coins of the type Rc, the instance's bytes, the cells. -/
abbrev InputOverMatrices (Rc : Type) : Type := Local FullSizeMatrix Rc ProofFile.Inst Cells

/-- **What is asked of a Script at one run's coins k and one input v of a prover over the matrices.** A structure of premises: nothing here
shows that a Script meets it. -/
structure ScriptReadsTheInput {Bk : ProverCoinCounts} (Zp : ProofFile.Pub)
    (Q : Script Bk (InputOverMatrices Rc) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : InputOverMatrices Rc) : Prop where
  /-- the Script's cells hold every index that the input's matrix holds -/
  cells : ∀ i : Cm.Idx, Holds v.w₀ i → Holds (Q.cells v) i
  /-- the request file's bytes, read back, with the Script's token laid in, are the instance that the input's bytes are read as -/
  token : ∀ x : Instance ppref, ProofFile.instOf v.x = some x →
    (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf (Q.tok v))).val = x
  /-- the Script's messages at the layout's seats are the packing of the model's trace, where the input's own trace is that trace
  read by "cellOf" -/
  messages : ∀ (i : Cm.Idx) (x : Instance ppref), Holds v.w₀ i → ProofFile.instOf v.x = some x →
    ServesAt (P5J.At.X Zp) i x →
    v.trace = ⟨cellOf (P5J.At.X Zp) (theTrace (P5J.At.X Zp) i x)⟩ →
    ScriptSymsRawOn Zp Q k v (theTrace (P5J.At.X Zp) i x) fun _ _ => True

/-- **"ScriptTies" at a prover over the matrices**, at an index that the input's matrix holds and the instance that its bytes are read as. -/
theorem scriptTies_of_readyInput (h : AtMgA OnBytes.secondHashFunction files D r Zp Np cF xp)
    {P : OnlineProverParts FullSizeMatrix Rc Cells X₀ X} {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells X₀ X}
    (traceField : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned) {Bk : ProverCoinCounts}
    {Q : Script Bk (InputOverMatrices Rc) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : InputOverMatrices Rc} {Fd : FileDescription ProofFile.Inst}
    (ready : ReadyInput Fd returned.H v) (reads : ScriptReadsTheInput Zp Q k v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), Holds v.w₀ i ∧ ProofFile.instOf v.x = some x ∧
      ServesAt (P5J.At.X Zp) i x ∧ ScriptTies files Zp cF Q k v i x := by
  obtain ⟨i, x, -, hh, hx, hs, hc⟩ :=
    cells_of_readyInput_over_matrices traceField made ready
  obtain ⟨eZ, -⟩ := ProofFile.Honest.atPure_at_laid h.toAtMg.laid made
  rw [eZ] at hs hc
  have R := reads.messages i x hh hx hs hc
  exact ⟨i, x, hh, hx, hs,
    scriptTies_of_rawOn h (fun _ _ => Or.inl trivial) (reads.cells i hh) (reads.token x hx) R R⟩

section Items
variable (h : AtMgA OnBytes.secondHashFunction files D r Zp Np cF xp) {P : OnlineProverParts FullSizeMatrix Rc Cells X₀ X}
  {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells X₀ X}
  (traceField : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned) {Bk : ProverCoinCounts}
  (Q : Script Bk (InputOverMatrices Rc) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : ℕ) (Vd : InputOverMatrices Rc → Prop) (Rd : ℕ → InputOverMatrices Rc → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w₁ : InputOverMatrices Rc) (k : Coins Bk)
  (mm : Mid (InputOverMatrices Rc) X) {Fd : FileDescription ProofFile.Inst}
include traceField made

/-- **The hundred items "constr l p".** -/
theorem constr_items_over_matrices (ready : ReadyInput Fd returned.H mm.st.input)
    (reads : ScriptReadsTheInput Zp Q k mm.st.input) (s : TS) (E : Env) :
    ∀ l sub, P5J.At.links[l]? = some sub →
      ∀ p ∈ [Part.idn, Part.lookCalls, Part.rider, Part.small],
        (lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
          [Item.constr l p] k s mm E := by
  obtain ⟨i, x, -, -, Sv, Ti⟩ := scriptTies_of_readyInput h traceField made ready reads
  exact constr_parts_at_start h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm Sv Ti s E

/-- **All that is open at border 0**, where the state bears no mark and the pile's item holds. -/
theorem items_open_at_the_start_over_matrices (ready : ReadyInput Fd returned.H mm.st.input)
    (reads : ScriptReadsTheInput Zp Q k mm.st.input) (s : TS) (E : Env)
    (noMark : s.failed = none)
    (pile : (lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
      [Item.pile] k s mm E) :
    (lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
      ((lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened 0) k s mm
      E := by
  obtain ⟨i, x, -, -, Sv, Ti⟩ := scriptTies_of_readyInput h traceField made ready reads
  exact opened_at_start_of_mark_pile h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm Sv
    Ti s E noMark pile

/-- **The same where "ready" returns** and the description's first test accepts the instance: at a value of "Mid" whose input is
the one that "ready" hands. -/
theorem items_open_at_the_start_of_ready {B : ProverCoinCounts} {w₀ : FullSizeMatrix} {rc : Rc} {ξ : ProofFile.Inst}
    {c : Coins B} {R : Ready FullSizeMatrix Rc ProofFile.Inst OnBytes.TableKey Cells X₀ X}
    (returns : ProofFile.Honest.ready Fd B returned.H w₀ rc ξ c = .ok R) (accepts : Fd.okStart ξ = true)
    (input : mm.st.input = R.own) (reads : ScriptReadsTheInput Zp Q k mm.st.input) (s : TS)
    (E : Env) (noMark : s.failed = none)
    (pile : (lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
      [Item.pile] k s mm E) :
    (lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
      ((lettersHead h returned.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened 0) k s mm
      E :=
  items_open_at_the_start_over_matrices h traceField made Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm
    (input ▸ readyInput_of_ready returns accepts) reads s E noMark pile

end Items

end HonestTraceRun.Meets

#check @HonestTraceRun.Meets.scriptTies_of_readyInput
#print axioms HonestTraceRun.Meets.scriptTies_of_readyInput
#print axioms HonestTraceRun.Meets.constr_items_over_matrices
#print axioms HonestTraceRun.Meets.items_open_at_the_start_over_matrices
#print axioms HonestTraceRun.Meets.items_open_at_the_start_of_ready
