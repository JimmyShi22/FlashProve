-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/StepAny.lean: the four theorems of OnBytes/Chain/Step.lean, at any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Chain.Step
import OnBytes.Chain.EngineLaws

namespace OnBytes.TwoPort.M

open Fmt (Qry Hash Plan St Round Stored SpecX Seen ChainOut)

/-- The step of a chain that a hash induces. -/
abbrev stepOf (h : Hash) : Qry :=
  fun c msg kind work nonce K => Fmt.Chain.queryW (m := Id) h c msg kind work nonce K

/-- At any hash h and the step that it induces `roundQ` equals `Fmt.roundX` at the identity monad.
-/
theorem roundQ_any (h : Hash) (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray)
    (s : St) (r : Round) (ts : List Stored) :
    roundQ (stepOf h) h cfg statement P run b s r ts =
      Fmt.roundX (m := Id) h cfg statement P run b s r ts := by
  unfold roundQ Fmt.roundX
  cases Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some x => rfl

/-- At any hash h and the step that it induces `foldRoundsQ` equals `Fmt.foldRoundsX` at the
identity monad. -/
theorem foldRoundsQ_any (h : Hash) (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) : ∀ (rs : List (Round × List Stored)) (s : St),
    foldRoundsQ (stepOf h) h cfg statement P run b rs s =
      Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s
  | [], _ => rfl
  | r :: rs, s => by
    unfold foldRoundsQ Fmt.foldRoundsX
    rw [roundQ_any]
    show _ = (match Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => none
      | some s' => Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s')
    cases Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
    | none => rfl
    | some s' => exact foldRoundsQ_any h cfg statement P run b rs s'

/-- At any hash h and the step that it induces `restQ` equals the part of `Fmt.readChainX` that
follows the chain's random bytes. -/
theorem restQ_any (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) :
    restQ (stepOf h) h S seen b x i0 =
      (match Fmt.startChainW (m := Id) h S.base.label
          (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
      | none => none
      | some hd =>
        match Fmt.foldRoundsX (m := Id) h S.base.cfg S.base.statement S.base.plan hd.run b
            (S.base.rounds.zip S.stored) ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
        | none => none
        | some s =>
          some (⟨Fmt.paramsDigestW (m := Id) h S.base.params, hd.run, hd.rho0, s.chain.rho,
            s.seen, s.out⟩, s.pos)) := by
  unfold restQ
  cases Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
  | none => rfl
  | some hd =>
    dsimp only
    rw [foldRoundsQ_any] <;> rfl

/-- At any hash h and the step that it induces the text of this file is the strict reader. -/
theorem readChainQ_any (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    readChainQ (stepOf h) h S seen b i = Fmt.readChainX (m := Id) h S seen b i := by
  unfold readChainQ Fmt.readChainX
  cases !S.ok with
  | true => rfl
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    cases S.base.rand with
    | inFile =>
      dsimp only
      cases Fmt.slice b i 32 with
      | none => rfl
      | some x => exact restQ_any h S seen b (some x) (i + 32)
    | given x => exact restQ_any h S seen b (some x) i
    | none => exact restQ_any h S seen b none i

end OnBytes.TwoPort.M
