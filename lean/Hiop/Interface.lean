-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Interface.lean: the information-theoretic object: a holographic IOP with an untrusted
committer, as the interface `Iop.BatchProtocol` of Iop/Batch.lean, and its soundness with a witness.

In standard terms: an interactive oracle proof whose verifier has oracle access to an encoding of
the index. The encoding may come from a cheating party, so soundness is stated for every word in
its place, through an index decoder (`BatchProtocol.Sound`, Iop/Batch.lean).

Definitions and one statement (`Spec.sound_of_soundK`, proved in Hiop/InterfaceProofs.lean).

The dictionary. `Iop.BatchProtocol I X` has, beside wordLength, Symbol, EncodingRandomness, `early` and `late`: the committer (encodeIndex i r:
the verifier encoded index for the index i under the randomness r; the prover encoded index is (i,
r)); the index decoder decodeIndex; the offline IOP `offline` on one encoded index; the link IOP `link` on a
first and a further encoded index; the online phase `onlineBatch`, a batch IOP with at most maxBatchSize instances on
one encoded index, whose verifier decides each instance from that instance's local transcript; the
honest sides. Among its properties: `BatchProtocol.Complete` (completeness, pointwise, with the probabilities
of the withheld sets), `BatchProtocol.Sound` (index-binding round-by-round soundness: the three languages
"decodes", "the first does not decode or the further one decodes alike", "does not decode or x is
in the language of the decoded index"), `BatchProtocol.Reads` with `BatchProtocol.Hiding` (honest-verifier zero
knowledge of each run in the exact form, and what an encoded index hides; that these give zero
knowledge of the whole object, any number of further encoded indices, links and sessions within the
budget, is proved in Compile/ for the compiled argument, and stated for the IOP itself in
`Spec.hvzk_whole` of Hiop/Whole.lean; from `BatchProtocol.Hiding`: `Spec.hvzk_whole_hiding` there; both
conclude `HVZKWhole` and take `BatchProtocol.Wired` too; in Compile/: `privacyKEGrWithBOf`
(Compile/Batch/PubProgMainBGr.lean); each under the hypotheses of its statement).
This file
names no term of `BatchProtocol`: that any protocol is an instance is not shown here.


Main names:
  `BatchProtocol.SoundK`: round-by-round knowledge soundness of the online phase, instance by instance: the
    named extractor `wit` computes a witness from an instance and from the oracles that the prover
    sent in that instance's full local transcript. For the offline and the link IOP the statement
    determines the witness (the decoding), so that soundness is knowledge soundness with the
    extractor "decode" (`Reduction.Know.of_sound`).
  `BatchProtocol.PropsK`: all properties, with a witness.

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {I X W : Type}

/-- Index-binding round-by-round knowledge soundness; εs bounds every error of the three lists, as
a probability. -/
structure BatchProtocol.SoundK (L : BatchProtocol I X) (Rno : I → X → W → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → W) (εs : ℝ≥0∞) : Prop where
  sndT : ∃ ε, Err.Below ε εs ∧ L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) ε
  sndL : ∃ ε, Err.Below ε εs ∧ L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) ε
  sndB : ∃ ε, Err.Below ε εs ∧ L.onlineBatch.SndBK L.maxBatchSize L.early L.late (fun x y w => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x w) wit ε

/-- All properties, with a witness. Ryes, Rno are relations with witnesses; the properties of
`Iop.BatchProtocol.Props` are asked for their languages. -/
structure BatchProtocol.PropsK (L : BatchProtocol I X) (Ryes Rno : I → X → W → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → W) (M : LH.Nums) : Prop where
  props  : L.Props (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) M
  soundK : L.SoundK Rno wit M.εs

namespace Spec

/-- States: knowledge soundness gives the soundness that the interface asks for. -/
def sound_of_soundK : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Rno : I → X → W → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → W) (εs : ℝ≥0∞),
    L.SoundK Rno wit εs → L.Sound (fun i x => ∃ w, Rno i x w) εs

end Spec
end Iop
