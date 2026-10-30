-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SerBPull.lean: the data of Iop/SerB.lean along a pull-back (Iop/BatchPull.lean).

The data carry over when challenges are computed from other uniform values: the pull-back changes no
prover message. The definitions follow `SerS.pull` of Iop/SerS.lean.

Notation: `Samplers s : Type 1` (Iop/Pull.lean): one sampler for each round; `σT`, `σL`, `σB`:
`Samplers` of `L.offline.shape`, `L.link.shape`, `L.onlineBatch.loc.shape`; `SerS s : Type` (Iop/SerS.lean):
for each round of a list its two serializers; `SerA s A : Type` (Iop/SerB.lean): for each round of
an annotated list: serializers of the plain parts of the shared component and of a slot's
component; `SerLHB L` (a structure, there): what the serialization of the queries needs of the
record of protocols, with the fields `tag : List Bool` (a constant prefix of every string of
`serReal`, Compile/Batch/Ser.lean: a tag for the parameter set), `x : Ser X`, `sg : Ser L.Symbol`, `T`,
`Lk`, `O` (`SerS` of `L.offline.shape`, `L.link.shape`, `L.onlineBatch.loc.shape`) and
`A : SerA L.onlineBatch.loc.shape L.onlineBatch.ann` (the two plain parts of each round of Batch).
-/
import Iop.SerB
import Iop.BatchPull

namespace Iop

def SerA.pull :
    (s : Shape) → (σ : Samplers s) → (A : RoundSplits s) → SerA s A → SerA (s.pull σ) (A.pull σ)
  | [], _, _, _ => ()
  | _ :: s, (_, σs), (_, A), (x, e) => (x, SerA.pull s σs A e)

variable {I X : Type}

def SerLHB.pull {L : BatchProtocol I X} (D : SerLHB L) (σT : Samplers L.offline.shape)
    (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape) : SerLHB (L.pull σT σL σB) where
  tag := D.tag
  x := D.x
  sg := D.sg
  T := SerS.pull _ σT D.T
  Lk := SerS.pull _ σL D.Lk
  O := SerS.pull _ σB D.O
  A := SerA.pull _ σB _ D.A

end Iop
