-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Toy1Laws.lean: the conditions that a toy of this library's own does meet, in one place, without
a hypothesis; and the one theorem of this file that speaks of the verifier that is run (as a term
that asks oracles within a trace; not of a run on bytes).

Statements and proofs. The toy is that of Run/ToyQ.lean.
It joins three things: Run/ToyQLaws.lean (the toy's verifier is local; its wiring meets the
conditions on a wiring, given that uniform blocks give uniform positions); Run/ToyChalLaw.lean
(`toy1_unif`: they do); Compile/Batch/ForestSound.lean (`runsIn_verifyB_of_strict`: for any protocol
and any wiring that meets the conditions: what the strict verifier with pruned openings accepts, the
verifier without the strict format accepts with other paths, within the same trace of queries).

Main names:
  `Spec.toy1_wire`: `QT.IsLocal`; `wqT.OKG` (the wiring with pruned openings); `wqF.OKG` (with whole
    paths). Nothing assumed.
  `Spec.toy1_lax`: what `V` or `VF` (`Compile.Batch.verifyOneProtocol` at the toy) accepts within a trace of
    queries, `Compile.Batch.verifyB` at the same data accepts with other paths within the same
    trace.

Limits (what this is not): no soundness. The library's statement on soundness
(Compile/Batch/SpecSoundG.lean: `BcsAt`) speaks of `verifyB` at the three protocols of an interface,
with a wiring of the interface; the toy's protocol is none of the three protocols of its ambient
interface (that interface gives the queries their types; of its data the verifier's chain reads only
the fields `early` (the identity) and `late` (none)). `toy1_lax` carries `V`'s acceptances to
`verifyB` at these data. Theorems for any protocol and wiring speak of `verifyB`: among them
`avoids_verifyB` (Compile/Batch/SeedAvoid.lean), `detBound_verifyB` (Compile/Batch/GlueTools.lean)
and, under their hypotheses, `mem_of_accepted` (Compile/Batch/Sound.lean), `star_of_accepted`
(CompileK/KnowStar.lean); beyond `toy1_lax` no theorem of Run/ or Fmt/ is stated of `verifyB` at
these data. The toy's relation is not named. Nothing on the spellings, the reader or a run.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyQLaws
import Run.ToyChalLaw
import Compile.Batch.ForestSound

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch Prob

/-- How a symbol is written into a leaf's query. -/
abbrev embT : (p : OPos QT.shape) → OSym QT.shape p → Body Lt := fun p a =>
  some (.inr ⟨Tag.test, ⟨p, a⟩⟩)

namespace Spec

def toy1_wire : Prop := QT.IsLocal ∧ wqT.OKG ∧ wqF.OKG

def toy1_lax : Prop :=
  ∀ (tr : Trace (spec 256 2 Lt))
      (cms : List (Dig 256)) (c : E3) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT)),
    (RunsIn tr (V cms c π) true →
      ∃ P1 P2, RunsIn tr
        (verifyB (L := Lt) .test (BatchInteractiveOracleProof.ofProto QT) wqT embT id some (fun _ => none)
          0 cms c (π.withPaths P1 P2)) true) ∧
    (RunsIn tr (VF cms c π) true →
      ∃ P1 P2, RunsIn tr
        (verifyB (L := Lt) .test (BatchInteractiveOracleProof.ofProto QT) wqF embT id some (fun _ => none)
          0 cms c (π.withPaths P1 P2)) true)

end Spec

theorem chalUnif : ChalUnif := Run.toy1_unif

/-- The laws of a round's wire (`WireRB.OK`) do not speak of the flag (`prJ`). -/
theorem w1F_ok : ({ w1 with prJ := false } : WireRB 256 1 r1 (RAnn.allLocal r1)).OK :=
  have h := w1_ok chalUnif
  { place_lt0 := h.place_lt0, place_ltJ := h.place_ltJ, posAt0_place := h.posAt0_place,
    posAtJ_place := h.posAtJ_place, place_posAt0 := h.place_posAt0, place_posAtJ := h.place_posAtJ
    no0 := h.no0, noJ := h.noJ, chal_unif := h.chal_unif,
      gr0_none := h.gr0_none, grJ_none := h.grJ_none }

theorem wq0F_ok : wq0F.OK :=
  have h := wq0_ok chalUnif
  { sh := ⟨w0_ok, w1F_ok, w2_ok, trivial⟩, ext := h.ext, opens := h.opens, depth := h.depth }

theorem wqF_okg : wqF.OKG :=
  ProtocolQueryLayout.OKG.grindLocal wq0F_ok.toG (D := Dn) (n := 8) (fun _ _ _ _ => rfl) (by decide) (g := gW)
    ⟨Nat.zero_le _, le_refl 8, Nat.zero_le _, trivial⟩

theorem toy1_wire : Spec.toy1_wire := ⟨qT_local, wqT_okg chalUnif, wqF_okg⟩

theorem toy1_lax : Spec.toy1_lax := fun _ _ _ _ =>
  ⟨fun h => runsIn_verifyB_of_strict (wqT_okg chalUnif) h,
    fun h => runsIn_verifyB_of_strict wqF_okg h⟩

end Run.Toy1
