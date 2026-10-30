-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SerB.lean: what the serialization of the scheme's queries needs of a protocol with slots.

The compiled scheme's typed queries are encoded as strings (Iop/Ser.lean). All of this file is data
(words of this library: lean/GLOSSARY.md). In a protocol with slots (`BatchInteractiveOracleProof`, Iop/Batch.lean; a
slot is one request's part of the protocol Batch) a round is shared or local (its kind), and its
annotation (`RAnn`) divides the prover message into a shared component and the slot's component.
Beside the data of Iop/SerS.lean (for each round a serializer of the pairs (position, symbol) and
one of the plain part) there is, for each round of an annotated list of rounds (`RoundSplits`,
Iop/Batch.lean), a serializer of the plain part of the shared component and one of the plain part of
a slot's component (`SerA`), since the compiler (Compile/) hashes the two components separately.
For annotations in which only the slots send, or only the shared component is sent, these data are
computed from those of Iop/SerS.lean; `SerA.app` and `SerA.cons` compose them.
For a record of protocols (`BatchProtocol`, Iop/Batch.lean: encoder, decoder and the protocols Test, Link and
Batch): serializers of requests (the type X) and of the symbols of encoded indices (`L.Symbol`), the
data of its three protocols and of the annotation of Batch, and a constant tag (`SerLHB`). Whoever
builds a protocol supplies them; the compiler reads them (Compile/Batch/Ser.lean).
-/
import Iop.SerS
import Iop.Batch

set_option autoImplicit false

namespace Iop

/-- For each round of an annotated list: serializers of the plain parts of the shared component and
of a slot's component. -/
def SerA : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | _ :: s, (a, A) => (Ser a.P0 × Ser a.Pj) × SerA s A

/-- A round in which only the slots send: the shared component's plain part is empty, and a slot's
is the plain part of the round. -/
def SerR.ofSlot (k : Kind) {r : Round} (a : SerR r) :
    Ser (RAnn.ofSlot k r).P0 × Ser (RAnn.ofSlot k r).Pj := (Ser.unit, a.2)

/-- A round in which only the shared component is sent: its plain part is the plain part of the
round, and a slot's is empty. -/
def SerR.ofShared (k : Kind) {r : Round} (a : SerR r) :
    Ser (RAnn.ofShared k r).P0 × Ser (RAnn.ofShared k r).Pj := (a.2, Ser.unit)

/-- the same rule of annotation in every round -/
def SerA.const (f : ∀ r : Round, RAnn r) (g : ∀ r : Round, SerR r → Ser (f r).P0 × Ser (f r).Pj) :
    (s : Shape) → SerS s → SerA s (RoundSplits.const f s)
  | [], _ => ()
  | r :: s, (a, e) => (g r a, SerA.const f g s e)

/-- in every round only the slots send -/
def SerA.constSlot (k : Kind) (s : Shape) (e : SerS s) : SerA s (RoundSplits.const (RAnn.ofSlot k) s) :=
  SerA.const (RAnn.ofSlot k) (fun _ a => SerR.ofSlot k a) s e

/-- in every round only the shared component is sent -/
def SerA.constShared (k : Kind) (s : Shape) (e : SerS s) :
    SerA s (RoundSplits.const (RAnn.ofShared k) s) :=
  SerA.const (RAnn.ofShared k) (fun _ a => SerR.ofShared k a) s e

/-- local rounds only: an ordinary IOP -/
def SerA.allLocal (s : Shape) (e : SerS s) : SerA s (RoundSplits.allLocal s) := SerA.constSlot .lo s e

/-- the data of two annotated lists, one after the other -/
def SerA.app :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → SerA s A → SerA t B → SerA (s ++ t) (RoundSplits.app A B)
  | [], _, _, _, _, b => b
  | _ :: _, _, (_, _), _, (a, as), b => (a, SerA.app as b)

/-- one more round at the start -/
def SerA.cons {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    (x : Ser a.P0 × Ser a.Pj) (e : SerA s A) : SerA (r :: s) (a, A) := (x, e)

variable {I X : Type}

/-- What the serialization of the queries needs of the record of protocols. -/
structure SerLHB (L : BatchProtocol I X) where
  /-- a constant prefix of every string of `serReal` (Compile/Batch/Ser.lean): a tag for the
  parameter set -/
  tag : List Bool
  x : Ser X
  sg : Ser L.Symbol
  T : SerS L.offline.shape
  Lk : SerS L.link.shape
  O : SerS L.onlineBatch.loc.shape
  /-- the two plain parts of each round of Batch -/
  A : SerA L.onlineBatch.loc.shape L.onlineBatch.ann

end Iop
