-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SoundAt.lean: round-by-round soundness of Test, Link and Batch for explicit lists of errors.

`BatchProtocol.Sound` (Iop/Batch.lean) says that there are error lists each of whose errors, as a
probability, is at most εs. After two rounds whose challenges both have several values are merged,
the new errors are sums (`Err.recut`, Iop/Recut.lean; `BatchProtocol.SoundAt.recut`,
Iop/BatchRecutProofs.lean). Whether these, as probabilities, stay at most εs can only be seen on
the lists. So this file names the lists. `Rno` is the relation between indices and requests in
Batch's language, the language of the field `sndB` below (a language of pairs (x, y), y a value of
the external strings).
  `BatchProtocol.SoundAt L Rno εT εL εB`   soundness of Test, Link and Batch for the lists εT, εL, εB. Test,
      Link and Batch are the protocols `L.offline`, `L.link`, `L.onlineBatch` of `BatchProtocol`. The three fields are
      labelled (Snd-T), (Snd-L), (Snd-B), as at `BatchProtocol.Sound`, Iop/Batch.lean. Test's and Link's are
      `InteractiveOracleProof.Sound` (Iop/InteractiveOracleProof.lean); Batch's is in its late form (`BatchInteractiveOracleProof.SndBL`,
      Iop/Batch.lean). Their languages, with "good" for `L.decodeIndex y ≠ none`: Test's: the string y is
      good; Link's: the parent y.1 is not good, or the child y.2 decodes as the parent; Batch's: y
      is not good, or it decodes to an index i with `Rno i x`.
  `BatchProtocol.SoundAt.sound`            from `L.SoundAt Rno εT εL εB`, if every error of the three lists,
      as a probability, is at most εs: `BatchProtocol.Sound L Rno εs`.
  `BatchProtocol.SoundAt.split`            after rounds are split, under `APlan.OK` and `APlan.LoTo`: the
      lists `Err.split P ε` (the new rounds have the error 0).

Notation: `Err s : Type` (Iop/Rbr.lean): one number for each round; in `Doomed s ε bad` (there),
how many values of the challenge may lead from a doomed transcript to one that is not doomed;
`Err.Below ε c : Prop` (Iop/InteractiveOracleProof.lean): every error of the list, as a probability, is at most c,
for a round r with the error e: `(e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞)`; fields of `BatchProtocol`
(Iop/Batch.lean): `decodeIndex : (Fin wordLength → Symbol) → Option I`: the decoder; `maxBatchSize : ℕ`: the
number of slots; `early : X → X`: what of an instance layer 1 writes into the first query of the
chain of a slot of Batch; `late : Option ℕ`: the round of Batch (counted from 0) into whose query
layer 1 writes the whole instance, none: there is no such round; layer 1: the compiler (Compile/).

Limits: nothing is said on the size of any error (but that the new rounds of `Err.split` have the
error 0).
-/
import Iop.BatchJoinProofs
import Iop.BatchSplitProofs

namespace Iop
open scoped ENNReal

variable {I X : Type}

/-- Round-by-round soundness of Test, Link and Batch, (Snd-T), (Snd-L), (Snd-B), for three explicit
lists of errors. -/
structure BatchProtocol.SoundAt (L : BatchProtocol I X) (Rno : I → X → Prop) (εT : Err L.offline.shape)
    (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) : Prop where
  sndT : L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) εT
  sndL : L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) εL
  sndB : L.onlineBatch.SndBL L.maxBatchSize L.early L.late
    (fun x y => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x) εB

variable {L : BatchProtocol I X} {Rno : I → X → Prop} {εT : Err L.offline.shape}
  {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape}

theorem BatchProtocol.SoundAt.sound (h : L.SoundAt Rno εT εL εB) {εs : ℝ≥0∞} (bT : Err.Below εT εs)
    (bL : Err.Below εL εs) (bB : Err.Below εB εs) : L.Sound Rno εs :=
  ⟨⟨εT, bT, h.sndT⟩, ⟨εL, bL, h.sndL⟩, ⟨εB, bB, h.sndB⟩⟩

/-- `SoundAt` carries over to `L.split`, with the lists `Err.split`, under `APlan.OK` and
`APlan.LoTo`. -/
theorem BatchProtocol.SoundAt.split (h : L.SoundAt Rno εT εL εB) {PT : SPlan L.offline.shape}
    {PL : SPlan L.link.shape} {PB : SPlan L.onlineBatch.loc.shape} {ZB : APlan PB L.onlineBatch.ann}
    (hZ : APlan.OK PB L.onlineBatch.ann ZB) (hl : ∀ n, L.late = some n → APlan.LoTo PB L.onlineBatch.ann ZB n) :
    (L.split PT PL PB ZB).SoundAt Rno (Err.split PT εT) (Err.split PL εL) (Err.split PB εB) :=
  ⟨h.sndT.split PT, h.sndL.split PL, BatchSplit.sndBL_split hZ hl h.sndB⟩

end Iop
