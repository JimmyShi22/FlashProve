--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySendSeats.lean: THE THREE JOBS OF E2E/KeySendJobs.lean STAND AT THE PLACES OF THE
DESCRIPTION's OWN THREE SENDINGS: each of the three sub-protocols of the key file's IOP as written
in Lean (Johnson/Desc/Key/One.lean) IS the description's own text at the public data P that stands
in the job. Statements, each by unfolding.

Why. The jobs call the library's `sendingPar` with the same strings and notices as One.lean does. As
long as that is held by reading alone, a string turned there turns nothing here. `idx_whole`,
`msg_whole`, `w_whole` fail to compile if the two texts part in anything that the sub-protocol reads
of P, a string among it. (`idx_seat`, `msg_seat`, `w_seat` alone would not: the three functions of P
that they compare read no string.)

What is shown, for each of "idx.1.send", "msg.1.send", "w.1.send":
  `idx_seat`, `msg_seat`, `w_seat`: the sub-protocol's place, its declared rounds and the oracle
    messages that it states are the kind's own (`K1.rounds`, `K1.oracles`) at the job's public data
    P. For W: where the shape has a message with W, there is a job exactly if there is a
    sub-protocol.
  **`idx_whole`**, **`msg_whole`**, **`w_whole`**: THE WHOLE SUB-PROTOCOL, its names and its
    decision among it, is the description's own text with the job's P in the place of its own call
    of `sendingPar`.

Limits. The letters N, groups are one letter in both texts by the statements' form; first, the fresh
tables and the rounds of the batching are no letters of the description's sub-protocols, and nothing
is said of them. Nothing on any prover. Nothing on hiding follows from this file.


-/
import E2E.KeySendJobs
import Johnson.Desc.Key.One

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params
open OnBytes.Slice (GF)
open ProofFile.Honest.K1 (SendJob Ride)
open VerifiableInference.Desc (K1.rounds K1.oracles)
open VerifiableInference.Desc.Key (Pieces sendIndexMasks sendOwnMessage sendW)

variable {W X β Cl : Type}

/-- "idx.1.send". -/
theorem idx_seat (one : OneTime) (N : Pieces) (groups : List (List Nat)) (first : Nat) :
    (sendIndexMasks (β := β) (Cl := Cl) one N groups).place =
        (idxJob (W := W) (X := X) one N groups first).P.place ∧
      (sendIndexMasks (β := β) (Cl := Cl) one N groups).rounds =
        K1.rounds (idxJob (W := W) (X := X) one N groups first).P ∧
      (sendIndexMasks (β := β) (Cl := Cl) one N groups).oracles =
        K1.oracles (idxJob (W := W) (X := X) one N groups first).P :=
  ⟨rfl, List.append_nil _, List.append_nil _⟩

/-- "msg.1.send". -/
theorem msg_seat (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
    (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride) :
    (sendOwnMessage (β := β) (Cl := Cl) one N groups).place =
        (msgJob (X := X) entry one N groups first ride).P.place ∧
      (sendOwnMessage (β := β) (Cl := Cl) one N groups).rounds =
        K1.rounds (msgJob (X := X) entry one N groups first ride).P ∧
      (sendOwnMessage (β := β) (Cl := Cl) one N groups).oracles =
        K1.oracles (msgJob (X := X) entry one N groups first ride).P :=
  ⟨rfl, List.append_nil _, List.append_nil _⟩

/-- "w.1.send": a job exactly if a sub-protocol; and then the same three. -/
theorem w_seat (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
    (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
    (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt) (sent : Nat) :
    match sendW (β := β) (Cl := Cl) one N sent groups,
        wJob (X := X) entry one N groups first ride points a with
    | some b, some J => b.place = J.P.place ∧ b.rounds = K1.rounds J.P ∧
        b.oracles = K1.oracles J.P
    | none, none => True
    | _, _ => False := by
  unfold sendW wJob
  cases linMessageW one.lin with
  | none => trivial
  | some msg => exact ⟨rfl, by simp [VerifiableInference.Desc.Block.andThen,
      VerifiableInference.Desc.Key.quietAt, VerifiableInference.Desc.Key.sendingSeat,
      VerifiableInference.Desc.K1.sendOwn, VerifiableInference.Desc.K13.rowsB,
      VerifiableInference.Desc.K13.still], by simp [VerifiableInference.Desc.Block.andThen,
      VerifiableInference.Desc.Key.quietAt, VerifiableInference.Desc.Key.sendingSeat,
      VerifiableInference.Desc.K1.sendOwn, VerifiableInference.Desc.K13.rowsB,
      VerifiableInference.Desc.K13.still]⟩

/-! ## The whole sub-protocols, at the jobs' public data -/

/-- **"idx.1.send" IS the seat of a sending at the job's own P**, joined with the description's own
step behind it: names, the place's public data whole, and the decision. -/
theorem idx_whole (one : OneTime) (N : Pieces) (groups : List (List Nat)) (first : Nat) :
    sendIndexMasks (β := β) (Cl := Cl) one N groups =
      (VerifiableInference.Desc.Key.sendingSeat "K1: the index masks' sending"
        (idxJob (W := W) (X := X) one N groups first).P).andThen "idx.1.send"
        (VerifiableInference.Desc.Key.quietAt "the index-mask message's number"
          (idxJob (W := W) (X := X) one N groups first).P.place fun s => do
            let i ← VerifiableInference.Desc.named "the sending has left no number" s.sent[0]?
            pure { s with idx := i }) := rfl

/-- **"msg.1.send"**, the like. -/
theorem msg_whole (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
    (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride) :
    sendOwnMessage (β := β) (Cl := Cl) one N groups =
      (VerifiableInference.Desc.Key.sendingSeat "K1: the own message's sending"
        (msgJob (X := X) entry one N groups first ride).P).andThen "msg.1.send"
        (VerifiableInference.Desc.Key.quietAt "the ranges' group"
          (msgJob (X := X) entry one N groups first ride).P.place
          (VerifiableInference.Desc.Key.openRangesGroup one)) := rfl

/-- **"w.1.send"**, the like, where there is a job: the four steps of the description's own text, at
the job's P. -/
theorem w_whole (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
    (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
    (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt) (sent : Nat) (J : SendJob W X)
    (hJ : wJob entry one N groups first ride points a = some J) :
    sendW (β := β) (Cl := Cl) one N sent groups = some
      ((((VerifiableInference.Desc.Key.quietAt "what is announced" J.P.place fun s => do
          VerifiableInference.Desc.need "K1: the record does not announce what ROUNDS says"
            (s.msgW == J.P.sent)
          pure s).andThen "announced and sent"
        (VerifiableInference.Desc.Key.sendingSeat "K1: W's sending" J.P)).andThen
        "sent and numbered"
        (VerifiableInference.Desc.Key.quietAt "the numbers sent with W" J.P.place fun s =>
          pure { s with ids := s.sent })).andThen "w.1.send"
        (VerifiableInference.Desc.K13.rowsB VerifiableInference.Desc.Key.batchLens
          (VerifiableInference.Desc.Key.batchWhere one N sent))) := by
  unfold wJob at hJ
  unfold sendW
  cases hm : linMessageW one.lin with
  | none =>
    rw [hm] at hJ
    cases hJ
  | some msg =>
    rw [hm] at hJ
    obtain rfl := Option.some.inj hJ
    rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.idx_seat
#print axioms AtPublicFiles.Key.msg_seat
#print axioms AtPublicFiles.Key.w_seat
#print axioms AtPublicFiles.Key.idx_whole
#print axioms AtPublicFiles.Key.msg_whole
#print axioms AtPublicFiles.Key.w_whole
