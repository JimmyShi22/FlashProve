-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ReplyClause.lean: the compiler's conclusion for a written batch protocol whose chain
takes in the early part of the instance alone, with one hypothesis on the protocol in the place of a
given state function.

OnBytes/Slice/BatchClause.lean gets the compiler's conclusion on an accepted string of one slot
(`BatchAt`) from a state function with two properties: the laws `StLaws` for the language, and the
law on verifier messages `Joint` at some error counts. OnBytes/Slice/ReplyState.lean has a state
function, `replySt`, under one hypothesis on the protocol, `ReplyLost`: for every early part and
every external string the prover has lost at the start, with the errors ε, towards "every instance
with this early part that the verifier accepts is in the language". This file puts the two together,
for an interface in which no later query holds the instance (L.late = none), at early := L.early.
(Meant: the early part is the request and the reply is a prover's message; see
OnBytes/Slice/ReplyState.lean. No reply occurs in this file, and L.early may be the identity.)

Two lists of errors occur. The state function is made from ε. The set of bad traces is bounded at ε
with the shared rounds' errors multiplied. Nothing asks that the two be one list: the set does not
hang on the errors at which it is bounded.

Main theorems.
 `stLaws_reply`    `StLaws` for `replySt`, under L.late = none and `ReplyLost`.
 `joint_reply`     `Joint` for `replySt`, with the shared rounds' errors multiplied by the number of
                   slots. No hypothesis.
 `batchAt_reply`   so `BatchAt`, if every error count, the shared rounds' multiplied by the number
                   of slots, is at most the share e of its round's verifier messages.
 `sndBL_of_replyLost_times`   under `ReplyLost`, the library's `SndBL` at late = none for any
                   annotation of the rounds, with the shared rounds' errors multiplied by the number
                   of slots. Free of an interface.
`batchAt_reply` has the form with "there is" (`BatchAt`), which is for use in one world (see
OnBytes/Slice/BatchClause.lean). Where the set must be named, it is `batBad` at the multiplied
errors and at `replySt`; `stLaws_reply` and `joint_reply` are what `batBad_lang` and `batBad_rare`
ask of it; the like clause for the verifier with the strict format, over these types, is not in this
library.

Not claimed. `ReplyLost` is a hypothesis: it is shown of no protocol in this library. No interface
is given here: none with L.late = none whose `early` leaves
anything out. The factor, the number of slots, stands on every shared round: that a shared round can
be had without it is not shown. With 2 ^ depthReq slots the factor costs depthReq bits on each
shared round. `Z.OK` and the number of slots are hypotheses as in OnBytes/Slice/BatchClause.lean.
Nothing on the programs' chains, on files or on BLAKE2b.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BatchClause
import OnBytes.Slice.ReplyState

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The laws of a state function for the language Lg hold of `replySt` at early := L.early, if no
later query holds the instance and the protocol has `ReplyLost`. -/
theorem stLaws_reply {W : QueryLayout lam L} (Z : WrittenB W) (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop)
    (ε : Err Z.Q.loc.shape) (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg) :
    StLaws Z (replySt Z.Q.loc ε L.early Lg) Lg where
  start := fun y _ _ => replySt_start h y _
  prover := fun y x τ m h0 => replySt_prover y x τ m h0
  switch := fun _ _ _ _ hn => by
    rw [hlate] at hn
    cases hn
  full := fun y x τ hL h0 => by
    rw [hlate] at h0
    exact replySt_full y x τ hL h0

/-- The law on verifier messages holds of `replySt`, at the errors ε with those of the shared rounds
multiplied by the number of slots. -/
theorem joint_reply {W : QueryLayout lam L} (Z : WrittenB W) (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop)
    (ε : Err Z.Q.loc.shape) :
    Joint Z (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε L.early Lg) :=
  fun y x => replySt_joint_times L.maxBatchSize Z.Q.ann y x

/-- From `ReplyLost` to the compiler's conclusion, for the language Lg and the reading R: if no
later query holds the instance, the protocol has `ReplyLost` with the errors ε, every one of these,
the shared rounds' multiplied by the number of slots, is at most the share e of its round's verifier
messages, `Z.OK` holds, and there are 2 ^ depthReq slots. The set is `batBad` at these multiplied
errors and at `replySt` with the errors ε. -/
theorem batchAt_reply {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg)
    (hb : Err.Below (Err.timesShared L.maxBatchSize Z.Q.ann ε) εs) (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ W.depthReq) :
    BatchAt Z R Lg εs :=
  batchAt Z R Lg εs (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε L.early Lg) hb
    (joint_reply Z Lg ε) (stLaws_reply Z Lg ε hlate h) hZ hN

/-- Under `ReplyLost`: the library's late form of soundness of a batch at late = none, for any
annotation of the rounds, with the shared rounds' errors multiplied by the number N of slots. -/
theorem sndBL_of_replyLost_times {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    {ε : Err Q.loc.shape} {early : Y → Y} {Lg : Y → E.Str → Prop}
    (h : ReplyLost Q.loc ε early Lg) (N : ℕ) :
    Q.SndBL N early none Lg (Err.timesShared N Q.ann ε) :=
  ⟨fun n hn => (by cases hn), replySt Q.loc ε early Lg, fun y x _ => replySt_start h y _,
    fun y x τ m h0 => replySt_prover y x τ m h0, fun y x τ _ hn => (by cases hn),
    fun y x τ hL h0 => replySt_full y x τ hL h0, fun y x => replySt_joint_times N Q.ann y x⟩

end OnBytes.Slice
