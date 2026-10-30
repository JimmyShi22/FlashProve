-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/Protocol.lean: what a protocol is, before any hash function.

 1. A protocol is Iop.HolographicProtocol (Hiop/RecInterface.lean).
 2. It has an encoder of an index, and a decoder that gives that index back.
 3. Every oracle the prover commits to, in the key file's proof, the link proof and a request's proof
    alike, carries an out-of-domain sample with one answer at the released sizes, and each committed
    table carries its 2,048 out-of-domain answers; the only unsampled oracles are two kinds of mask, a
    fold's fresh mask and a proximity test's base-case masking word, which carry no data.
 4. It has three interactive oracle proofs: offline, link and online.
 5. It has three seats, which the library's types of keys hang on. Nothing in these files reads a seat.
 6. HonestProvers are the provers of the three proofs. They stand beside the seats.
 7. The online prover is told the number of the copy that it proves on.
 8. A model is what is committed, with its next token.
 9. No hash function occurs in this file.
-/
import Hiop.RecInterface
import Compile.Life
import VerifiableInference.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Compilation
open _root_.Iop
open _root_.Compile.Lifetime (SimOf)

/-- A model: what is committed, and the next token. -/
structure Model where
  /-- What is committed: the weights. -/
  Weights : Type
  /-- The next token after the given tokens; none where the model has no value on them. -/
  nextToken : Weights → List Token → Option Token

/-- The honest provers of a protocol's three interactive oracle proofs. -/
structure HonestProvers {Index Instance : Type} (protocol : HolographicProtocol Index Instance) where
  /-- The offline prover: it holds the index, the encoding's randomness and the seed. -/
  offlineProver : Honest protocol.offline
    (Index × protocol.EncodingRandomness × protocol.OutOfDomainSeed)
  /-- The link prover: it holds the index, and the randomness and seed of both encodings. -/
  linkProver : Honest protocol.link
    (Index × (protocol.EncodingRandomness × protocol.OutOfDomainSeed) ×
      (protocol.EncodingRandomness × protocol.OutOfDomainSeed))
  /-- The online prover: it holds the index, the randomness and seed of the copy, and its number. -/
  onlineProver : Honest protocol.onlineBatch.loc
    (Index × protocol.EncodingRandomness × protocol.OutOfDomainSeed × ℕ)

variable {Index Instance : Type} {protocol : HolographicProtocol Index Instance}

/-- The online prover at a fixed number of the copy. -/
def HonestProvers.onlineAtCopy (provers : HonestProvers protocol) (copy : ℕ) :
    Honest protocol.onlineBatch.loc
      (Index × protocol.EncodingRandomness × protocol.OutOfDomainSeed) where
  Coin := provers.onlineProver.Coin
  ext := fun w => provers.onlineProver.ext (w.1, w.2.1, w.2.2, copy)
  strat := fun w x c => provers.onlineProver.strat (w.1, w.2.1, w.2.2, copy) x c
  Bad := provers.onlineProver.Bad
  Hid := fun w x => provers.onlineProver.Hid (w.1, w.2.1, w.2.2, copy) x

/-- The same provers, but that the online prover withholds at every message of a request that is not
served: it shows nothing there. At a served request nothing turns. -/
def HonestProvers.refuseUnserved (provers : HonestProvers protocol)
    (Served : Index → Instance → Prop) : HonestProvers protocol where
  offlineProver := provers.offlineProver
  linkProver := provers.linkProver
  onlineProver :=
    { Coin := provers.onlineProver.Coin
      ext := provers.onlineProver.ext
      strat := provers.onlineProver.strat
      Bad := provers.onlineProver.Bad
      Hid := fun w y => {_ρ | ¬ Served w.1 y.1} ∪ provers.onlineProver.Hid w y }

/-- One simulator for each of the three proofs; the online one for each number of a copy. By type a
simulator is handed the instance, the verifier's messages and the tables' symbols at the positions
that the verifier reads, and no index, no encoding randomness and no prover's coin. -/
structure RunSimulators (protocol : HolographicProtocol Index Instance) where
  offline : SimOf protocol.offline
  link : SimOf protocol.link
  online : ℕ → SimOf protocol.onlineBatch.loc

/-- The tables of which each prover speaks are the encodings of its own index. -/
structure HonestProvers.SpeakOfTheirTables (provers : HonestProvers protocol) : Prop where
  offline : ∀ i r e, provers.offlineProver.ext (i, r, e) = protocol.encodeIndex i r
  link : ∀ i r e r' e', provers.linkProver.ext (i, (r, e), (r', e')) =
    (protocol.encodeIndex i r, protocol.encodeIndex i r')
  online : ∀ i r e n, provers.onlineProver.ext (i, r, e, n) = protocol.encodeIndex i r

end VerifiableInference.Compilation
