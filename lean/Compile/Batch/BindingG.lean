-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/BindingG.lean: index binding of the compiled scheme whose rounds may have
proof-of-work bits: the proof of `Spec.bindingBatchG` (Compile/Batch/SpecGrind.lean). Under
`L.PropsNoAcc Ryes Rno M` and `W.OKG`, `argB W WP p` has index binding (`HasIndexBindingWith`,
ZKCP/Gen.lean) with the extractor `extractorB W` and the bound `epsB W M`.

The verifier and the extractor are those of the scheme without such bits, run on the protocols with
them, and read nothing of the wire record's entries on them; so BCS with shared rounds
(`bcsSoundBatchG`, Compile/Batch/Sound.lean) and the step to index binding (`bindingBatchS`,
Compile/Batch/GlueBinding.lean) hold with `W.OKG` in the place of `W.OK`. The bound is the same
function as without such bits: `M.εs` bounds the round errors of the protocols with their
proof-of-work bits.

Notation: `L`: an `BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with
the honest sides; `W`: a `QueryLayout lam L` (Iop/BatchWire.lean): a wire record (lean/GLOSSARY.md: wire);
`WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and the
enumeration of the encoding randomness; `p`: a `Params` (Compile/Star.lean), with the fields sMT,
sFS, M, s1; the number of copies is `p.M` + 1; `Ryes`, `Rno`: `I → X → Prop`: the two indexed
relations of a `Gen.RelPair` (ZKCP/Gen.lean), by `relPair` (Compile/Spec.lean); `M`: an `LH.Nums`
(Iop/InteractiveOracleProof.lean): all numbers of the interface; `epsB W M`: the function of (tC, tP): (tC + tP +
`tVB W` + 1) · `M.εs` + 2 (tC + tP + `tVB W` + 2)² / 2^lam; `tVB W`: a natural number: a bound on
the queries of V on one proof: Test, Link, one slot of Batch (both: Compile/Batch/SpecBinding.lean).

Limits: not said: which εs protocols with proof-of-work bits have. Nothing on what a query stands
for: a cheating prover's attempt with a new nonce is counted as one query.
-/
import Compile.Batch.SpecGrind
import Compile.Batch.Sound
import Compile.Batch.GlueBinding

namespace Compile.Batch

theorem bindingBatchG : Spec.bindingBatchG :=
  fun _ _ _ _ W WP p Ryes Rno M h hW =>
    bindingBatchS bcsSoundBatchG W WP p Ryes Rno M h.sub h.sound h.localT
      h.localL h.localB h.cohB hW

end Compile.Batch
