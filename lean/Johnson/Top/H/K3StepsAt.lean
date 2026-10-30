-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3StepsAt.lean: the kind "lookup" (K3): its share of a link's frame
(Johnson/Top/H/K3Steps.lean) IN THE LETTERS OF THE TWO FORMS THAT A LINK's LAW ASKS:
Block.Steps, Block.RunsStep, Block.AfterStep at Carries (Johnson/Desc/Sound/FoldSteps.lean; at the
library's ledger: CarriesFo, Johnson/Desc/First/LedgerAtFo.lean), and "a ledger in front is followed
by a later one" for one partial reader of the whole record (`LedgerKeepsAtK3`). Statements and
proofs: each is one call of a theorem of K3Steps.lean.

Main names:
  `Frame.carriesFo`: Frame gives CarriesFo.
  `k3_steps`, `k3_runsStep`, `k3_afterStep`: at any seat and any reader of "heard" that the seat's
    put and mark leave. The runs' laws ask of the seat that a ledger laid by the mark is the one
    that is read (hmf), and no more: they hold at every type of claims.
  `calls_steps_calls`, `calls_steps_digits`, `digits_steps_digits`, `digits_steps_calls` and the
    like for the runs: at the two seats of Johnson/Desc/First/Look/K3Seat.lean, for both readings of
    "heard".
  `join_step`, `planes_step`: the two runs that a calling kind states: what RunsStep asks of them.
  `LedgerKeepsAtK3`, `k3_ledgerKeepsAt`: no premise on the view's words or on the ledger's sizes.

Limits. Those of Johnson/Top/H/K3Steps.lean. LedgerKeepsAtK3 is typed here after a statement
("LedgerKeepsAt") that lies in no file of this library yet; it bears a name of its own so that no
name stands twice when that file comes; it is then to be struck for that one.
Not claimed: anything on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H.K3Steps
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Carries CarriesFo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits joinRun planesRun Readers)

section Seat
variable {T Cl : Type}

theorem Frame.carriesFo {fork : T → Option Fork} {hd : T → Option Forest.Heard} {s s' : T}
    (h : Frame fork hd s s') : CarriesFo fork hd s s' := h.carries

theorem k3_steps (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) (hk : SeatKeeps seat)
    (hd : T → Option Forest.Heard)
    (hput : ∀ s g G x, seat.heard s = none → hd s = some x → hd (seat.put s g G) = some x) :
    (Desc.K3.block seat piece laid before p guests).Steps (CarriesFo seat.fork hd) :=
  fun s rs gs s' h =>
    (decide_frame seat piece laid before p guests hk hd hput s s' rs gs h).carriesFo

theorem k3_runsStep (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Forest.Heard)
    (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) :
    (Desc.K3.block seat piece laid before p guests).RunsStep (CarriesFo seat.fork hd) :=
  fun c hc n s cl s' h =>
    (block_runs_frame seat hmf hd hmark piece laid before p guests c hc n s cl s' h).carriesFo

theorem k3_afterStep (R : T → T → Prop) (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) :
    (Desc.K3.block seat piece laid before p guests).AfterStep R :=
  fun _ hc => absurd hc (List.not_mem_nil)

/-- What RunsStep asks of "join", which a calling kind states. -/
theorem join_step (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Forest.Heard)
    (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (keys : T → Option (Array Aff)) (n : ℕ) (s s' : T) (cl : List Cl)
    (h : joinRun seat keys n s = .ok (cl, s')) : CarriesFo seat.fork hd s s' :=
  (join_frame seat hmf hd hmark keys n s s' cl h).carriesFo

/-- What RunsStep asks of "planes". -/
theorem planes_step (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Forest.Heard)
    (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s) (lm : ℕ)
    (readers : Readers T) (n : ℕ) (s s' : T) (cl : List Cl)
    (h : planesRun seat lm readers n s = .ok (cl, s')) : CarriesFo seat.fork hd s s' :=
  (planes_frame seat hmf hd hmark lm readers n s s' cl h).carriesFo

/-- A ledger in front of a block's yes is followed by a later one: for one partial reader of the
whole record. -/
def LedgerKeepsAtK3 (ledger? : T → Option Fork) (b : Block T Cl) : Prop :=
  ∀ s rs gs s' F, b.decide s rs gs = .ok s' → ledger? s = some F →
    ∃ F', ledger? s' = some F' ∧ OnBytes.PscRun.Later F F'

theorem k3_ledgerKeepsAt (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) (hk : SeatKeeps seat) :
    LedgerKeepsAtK3 seat.fork (Desc.K3.block seat piece laid before p guests) :=
  fun s rs gs s' F h hF =>
    (decide_frame_own seat piece laid before p guests hk s s' rs gs h).2 F hF

end Seat

section AtS
variable {Cl : Type}

theorem calls_steps_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatCalls claim) piece laid before p guests).Steps
      (CarriesFo S.fork? S.lookHeard?) :=
  fun s rs gs s' h => (calls_decide_calls claim piece laid before p guests s s' rs gs h).carriesFo

theorem calls_steps_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatCalls claim) piece laid before p guests).Steps
      (CarriesFo S.fork? tlHeard) :=
  fun s rs gs s' h => (calls_decide_digits claim piece laid before p guests s s' rs gs h).carriesFo

theorem digits_steps_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatDigits claim) piece laid before p guests).Steps
      (CarriesFo S.fork? tlHeard) :=
  fun s rs gs s' h => (digits_decide_digits claim piece laid before p guests s s' rs gs h).carriesFo

theorem digits_steps_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatDigits claim) piece laid before p guests).Steps
      (CarriesFo S.fork? S.lookHeard?) :=
  fun s rs gs s' h => (digits_decide_calls claim piece laid before p guests s s' rs gs h).carriesFo

theorem calls_runs_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatCalls claim) piece laid before p guests).RunsStep
      (CarriesFo S.fork? S.lookHeard?) :=
  k3_runsStep (seatCalls claim) (fun s F G h => fork_putFork s F G h) S.lookHeard?
    (mark_calls claim)
    piece laid before p guests

theorem calls_runs_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatCalls claim) piece laid before p guests).RunsStep
      (CarriesFo S.fork? tlHeard) :=
  k3_runsStep (seatCalls claim) (fun s F G h => fork_putFork s F G h) tlHeard (mark_digits claim)
    piece laid before p guests

theorem digits_runs_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatDigits claim) piece laid before p guests).RunsStep
      (CarriesFo S.fork? tlHeard) :=
  k3_runsStep (seatDigits claim) (fun s F G h => fork_putFork s F G h) tlHeard (mark_digits claim)
    piece laid before p guests

theorem digits_runs_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block (seatDigits claim) piece laid before p guests).RunsStep
      (CarriesFo S.fork? S.lookHeard?) :=
  k3_runsStep (seatDigits claim) (fun s F G h => fork_putFork s F G h) S.lookHeard?
    (mark_calls claim) piece laid before p guests

end AtS

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_steps_calls
#print axioms VerifiableInference.OnPublicFiles.digits_steps_calls
#print axioms VerifiableInference.OnPublicFiles.digits_runs_calls
#print axioms VerifiableInference.OnPublicFiles.k3_ledgerKeepsAt
