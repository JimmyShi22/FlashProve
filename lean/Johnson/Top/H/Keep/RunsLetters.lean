-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsLetters.lean: The kind "lookup" (K3): THE LETTERS OF
Johnson/Top/H/Keep/RunsPlain.lean, WRITTEN OUT AT THE TWO SEATS THAT RUN: what is fixed of the other
kinds is what was heard at the seat; the promise on the fixed part is K3's own. So of the premises
of objects_runOk none is left, at either seat. Definitions, statements and proofs.

Main names:
  pf_lookHeard, pf_tlHeard: S.putFork turns neither what the lookup on the calls heard nor what the
    lookup on the digits heard.
  objects_runOk_calls, objects_runOk_digits: RunOk of the run "objects", at phi := what was heard at
    the seat, hd := the identity, Ok := K3Ok: WITHOUT A PREMISE; Fu, lm, jLK stay letters.
  planes_plainOk_calls, join_plainOk_calls: the like for the two other runs at the seat of the
    calls, under the three sentences on the caller's forms (Johnson/Top/H/Keep/RunsWorth.lean).

Limits. THE PROMISE Ok := K3Ok IS MET BY NO WRITTEN FIXED PART HERE: where no fixed part meets it
the premise on a run holds of nothing. A table that carries more in phi, or promises more in Ok,
wants these again at its own letters. The premises are not shown to be satisfiable.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsWorth
import Johnson.Top.H.Keep.SeatsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits joinRun planesRun Readers)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (worldAt Bound PlainOk RunOk plainTm Pub9 Fx9 O9)

theorem pf_lookHeard (s : S) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.lookHeard?, ho]
  | _ => rfl

theorem pf_tlHeard (s : S) (G : Fork) :
    (s.putFork G).tl?.bind (·.heard) = s.tl?.bind (·.heard) := by rw [pf_tl]

variable (Fu : S → Prop) (lm jLK : ℕ)

/-- **"objects" at the seat of the calls: no premise is left.** -/
theorem objects_runOk_calls :
    RunOk Reading.gl atS (O9 (K := GE) (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu)
      (Fx9 (fun s : S => s.lookHeard?) (K3Ok id lm jLK)) (objectsRun (seatCalls plain))
      (plainTm (objVals id lm jLK)) (objLen id lm jLK) :=
  objects_runOk (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu id lm jLK (seatCalls plain)
    seatCalls_atS2 seatCalls_fitsP pf_lookHeard (fun _ => rfl) (fun _ h => h)

/-- **"objects" at the seat of the digits: no premise is left.** -/
theorem objects_runOk_digits :
    RunOk Reading.gl atS
      (O9 (K := GE) (fun s : S => s.tl?.bind (·.heard)) (K3Ok id lm jLK) Fu)
      (Fx9 (fun s : S => s.tl?.bind (·.heard)) (K3Ok id lm jLK)) (objectsRun (seatDigits plain))
      (plainTm (objVals id lm jLK)) (objLen id lm jLK) :=
  objects_runOk (fun s : S => s.tl?.bind (·.heard)) (K3Ok id lm jLK) Fu id lm jLK
    (seatDigits plain) seatDigits_atS2 seatDigits_fitsP pf_tlHeard (fun _ => rfl) (fun _ h => h)

/-- "planes" at the seat of the calls, under the three sentences on the caller's forms. -/
theorem planes_plainOk_calls (readers : Readers S) {bQ : ℕ × ℕ → Option Heard → Aff}
    {pQ : ℕ → Option Heard → Aff}
    {ent : Option Heard × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HB : CallerForms (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu
      (fun (i : ℕ × ℕ) e => bitOf readers e i.1 i.2) bQ ent)
    (HP : CallerForms (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu
      (fun (col : ℕ) e => pinOf readers e col) pQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu)
      (Fx9 (fun s : S => s.lookHeard?) (K3Ok id lm jLK)) (planesRun (seatCalls plain) lm readers)
      (plVals id lm jLK (fun q y k col => refVal bQ ent (k, col) q y)
        (fun q y col => refVal pQ ent col q y)) (pickLen id lm jLK 3) :=
  planes_plainOk_of (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu id lm jLK (seatCalls plain)
    seatCalls_atS2 seatCalls_fitsP pf_lookHeard (fun _ => rfl) (fun _ h => h) readers HB HP

/-- "join" at the seat of the calls, under the three sentences on the caller's key forms. -/
theorem join_plainOk_calls (keys : S → Option (Array Aff)) {kQ : ℕ → Option Heard → Aff}
    {ent : Option Heard × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HK : CallerForms (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu
      (fun (k : ℕ) e => (keysOf keys e).getD k (Aff.ofConst zeroE)) kQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu)
      (Fx9 (fun s : S => s.lookHeard?) (K3Ok id lm jLK)) (joinRun (seatCalls plain) keys)
      (jnVals id lm jLK fun q y k => refVal kQ ent k q y) (pickLen id lm jLK 1) :=
  join_plainOk_of (fun s : S => s.lookHeard?) (K3Ok id lm jLK) Fu id lm jLK (seatCalls plain)
    seatCalls_atS2 seatCalls_fitsP pf_lookHeard (fun _ => rfl) (fun _ h => h) keys HK

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_runOk_calls
#print axioms VerifiableInference.OnPublicFiles.objects_runOk_digits
#print axioms VerifiableInference.OnPublicFiles.planes_plainOk_calls
#print axioms VerifiableInference.OnPublicFiles.join_plainOk_calls
