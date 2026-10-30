-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendStays.lean: the sample of an older message, read off the statement
(smpAt, GoodSendForms.lean), stays along a step that leaves the older messages (OldMsgs,
GoodSend5.lean): so past each block that keeps the older messages the record behind holds, for each
older message, the sample that the record in front holds.

Main names: formsAt_old, ansAt_old, smpAt_old; smp_stays.

What is not claimed. Which blocks stand between a sending and its closing. Nothing on soundness of a
protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.K1.Law.GoodSend5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)

/-- The sample rows of an older message are as they were. -/
theorem rows_old {A B : Statement} (h : OldMsgs A B) (o : Nat) (ho : o < A.oracles.size) :
    (B.oracles[o]?).map (fun x : OnBytes.Oracle => x.sampleRows) =
      (A.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows := by
  have e := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row => t.2.2) (h.2 o ho)
  simpa [Option.map_map, Function.comp_def] using e

theorem formsAt_rows (cs : Codes) (s : OracleShape) (St : Statement) (o : Nat) :
    formsAt cs s St o = ((St.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows).bind
      fun rs => (rs[0]?).map fun r _ => formRow cs s o r := by
  unfold formsAt
  cases St.oracles[o]? <;> rfl

theorem ansAt_rows (St : Statement) (o : Nat) :
    ansAt St o = ((St.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows).bind
      fun rs => (rs[0]?).map fun r _ => readE r.target := by
  unfold ansAt
  cases St.oracles[o]? <;> rfl

theorem formsAt_old (cs : Codes) (s : OracleShape) {A B : Statement} (h : OldMsgs A B) (o : Nat)
    (ho : o < A.oracles.size) : formsAt cs s B o = formsAt cs s A o := by
  rw [formsAt_rows, formsAt_rows, rows_old h o ho]

theorem ansAt_old {A B : Statement} (h : OldMsgs A B) (o : Nat) (ho : o < A.oracles.size) :
    ansAt B o = ansAt A o := by
  rw [ansAt_rows, ansAt_rows, rows_old h o ho]

/-- **The sample of an older message stays.** -/
theorem smpAt_old (cs : Codes) (s : OracleShape) (e : Nat) {A B : Statement} (h : OldMsgs A B)
    (o : Nat) (ho : o < A.oracles.size) : smpAt cs s e B o = smpAt cs s e A o := by
  unfold smpAt
  simp only [formsAt_old cs s h o ho, ansAt_old h o ho]

variable {T Cl : Type}

/-- **Past a block that keeps the older messages the samples stay.** -/
theorem smp_stays (stOf : T → Statement) (b : Block T Cl) (hb : KeepsOld stOf b) (cs : Codes)
    (s : OracleShape) (e : Nat) (t t' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide t rs gs = .ok t') (o : Nat)
    (ho : o < (stOf t).oracles.size) : smpAt cs s e (stOf t') o = smpAt cs s e (stOf t) o :=
  smpAt_old cs s e (hb t t' rs gs h) o ho

end VerifiableInference.Desc.K1
