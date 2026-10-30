-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WideMain.lean: the compiler's door with a witness, for a witness map that reads the local
transcript up to a round: over the typed oracles, with one named hypothesis on the compiled scheme.

This file is about the compiler's end result, that under the hypotheses of its statements the
compiled scheme is a commit-and-prove argument (`Gen.IsZKCPArgWith`, ZKCP/Gen.lean), with a witness
extractor that reads the witness out of the proof and the lists of queries.
Definitions, statements and proofs: an assembly. The compiler's door: for any
interface L, any data D (`DataK`, CompileK/Main.lean) and any work o (`Work`,
CompileK/GrindMain.lean) over an inhabited type Nn of nonces, an option (CompileK/GrindOpt.lean: o =
none: no proof of work).

Main names, each statement under its hypotheses:
  `Spec.compileWireT_any`: for any interface L with the wide properties but acceptance
    (`BatchProtocol.PropsNoAccKT`, Hiop/KnowWide.lean), any map wit that reads no verifier message from round
    j on (`TrBlind j`, CompileK/KnowExtTo.lean), any wire with `W.OKG` that fits (rounds may have a
    test): states `Gen.IsZKCPArgWith` for `Gen.withW Wn (argBKE W WP p)`: see its statement.
  `witDoor D w o`: the door's map, by parts (`WitP`, Ior/KnowWidePass.lean): w on the symbols, plain
    parts and verifier messages after "blocks" (`WitP.push`) (and "tests" (`WitP.strip`): nonces and
    test bits dropped).
  `extractorTO D j w w0 o`: the extractor, total, on the five inputs of the definition. Index: as in
    `extractorB` (Compile/Batch/SpecBinding.lean). Witness: follow the slot's chain in the
    committer's trace followed by the prover's, up to round j; Merkle extraction under the roots of
    the proof; the plain parts of the proof; the map. If `extractorBKTo` answers none (so if a chain
    query before round j is missing): the fixed value w0.




Limits: the hypothesis κ (`MissLe`, CompileK/TotalExt.lean): Pr[ the verifier accepts and a chain
query before round j is in neither trace (in Lean: `extractorBKTo` answers none) ] ≤ κ tC tP, for
all cheating committers and provers with at most tC and tP queries. It is assumed here, not proved,
and it is a statement on the compiled scheme. At κ ≥ 1 the binding clause is empty. At j = 0 (the
map reads the encoded index, oracles and plain parts, no verifier message) it holds with κ = 0, and
the passage to one oracle applies: CompileK/WideZero.lean.
Status beside the compilation of this protocol's technical report (lean/CREDITS.md; a comparison by
reading, of one of its prints, not held against the report's latest edition; that report is
unrefereed): its witness extractor recomputes the witness from the extracted
index and the instance, so this file renders no step of it. Here a
witness is read out of what the prover sent.
Not over one oracle, so not the literal definition: the passage (Rom/Family.lean) asks that an
extractor read one-block answers only. The index decoder reads the encoded index alone.
A session has at least one round. What the heads of CompileK/KnowExtT.lean, CompileK/KnowExtTo.lean,
CompileK/GrindMain.lean and CompileK/Main.lean list as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowBindingTo
import CompileK.TotalExt
import CompileK.WideLang
import CompileK.KnowWidePass

set_option autoImplicit false

namespace Iop

theorem Shape.pull_ne_nil : ∀ {s : Shape} (σ : Samplers s), s ≠ [] → s.pull σ ≠ []
  | [], _, h => absurd rfl h
  | _ :: _, (_, _), _ => List.cons_ne_nil _ _

theorem Shape.grind_ne_nil {Nn : Type} [Inhabited Nn] :
    ∀ {s : Shape} (g : GBits s), s ≠ [] → s.grind Nn g ≠ []
  | [], _, h => absurd rfl h
  | _ :: _, (_, _), _ => List.cons_ne_nil _ _

end Iop

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

namespace Spec

/-- For any interface and any wire with `W.OKG` that fits it. (not all hypotheses are named here:
see the statement below) -/
def compileWireT_any : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i₀ : I)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (j : ℕ) (w0 : Wn) (M : LH.Nums) (κ : ℕ → ℕ → ℝ≥0∞),
    L.PropsNoAccKT Ryes Rno wit M → TrBlind j wit → L.onlineBatch.loc.shape ≠ [] → W.OKG →
    GrFitB W (fun i x => ∃ w, Ryes i x w) → WP.OK → L.onlineBatch.ann.Fmt → Budget p M →
    Gen.MissLe (argBKE W WP p) (extractorBKTo W j wit) κ →
    ∀ Sm : Sims L, Sm.Good (fun i x => ∃ w, Ryes i x w) M.zT M.zL M.zO →
      ∀ (Ry : I → X → Wn → Prop) (sub : ∀ i x w, Ry i x w → Rno i x w),
        (∀ i x w, Ry i x w → ∃ w', Ryes i x w') →
        Gen.IsZKCPArgWith (Gen.relPairW Ry Rno sub) (Gen.withW Wn (argBKE W WP p)) L.maxBatchSize
          (Gen.totalE w0 (extractorBKTo W j wit)) (simBKGr W p Sm i₀) (alphaBG W M)
          (fun tC tP => epsB W M tC tP + κ tC tP) (zetaBGen L p M (hashTermsBGTot W p))

end Spec

theorem compileWireT_any : Spec.compileWireT_any := by
  intro I X Wn lam L W WP p i₀ Ryes Rno wit j w0 M κ hK hbl hne hW hG hWP hF
    hBu hm Sm hSm Ry sub hLang
  have hL := mainBatchKEGrWithBOf W WP p _ _ M hK.props hW hG hWP hF hBu Sm hSm i₀ L.maxBatchSize
    le_rfl (hopU_of_hopB le_rfl (hopB_total W p))
  exact ⟨Gen.withW_completeness
      _ _ _ _ _ _ _ _ _ (relPair _ _ hK.props.sub) _ _ _ hLang hL.completeness,
    Gen.binding_total _ _ _ _ _ _ _ _ Ry Rno sub _ w0 _ κ
      (bindingUpTo I X Wn lam L W WP p j Ry Rno wit M sub hK.soundKT hbl hK.props.localT
        hK.props.localL hK.props.localB hK.props.cohB hW hne) hm,
    Gen.withW_privacy _ _ _ _ _ _ _ _ _ (relPair _ _ hK.props.sub)
      _ _ _ _ hLang rfl hL.indexPrivacy⟩

section Door
variable {I X Wn : Type} {L₀ : BatchProtocol I X} {lam : ℕ} {Nn : Type} [Inhabited Nn] (D : DataK L₀ lam)

/-- The door's witness map, by parts. -/
def witDoor (w : WitP X (oneExternalString L₀.wordLength L₀.Symbol) L₀.onlineBatch.loc.shape Wn) :
    (o : Option (Work Nn L₀)) → X → (oneExternalString (D.LO o).wordLength (D.LO o).Symbol).Str →
    Tr (D.LO o).onlineBatch.loc.shape → Wn
  | none => witOf (w.push (Samplers.ofDraws _ D.dr.B))
  | some wk => witOf ((w.push (Samplers.ofDraws _ D.dr.B)).strip (D.gBd wk))

/-- The extractor. -/
def extractorTO (j : ℕ) (w : WitP X (oneExternalString L₀.wordLength L₀.Symbol) L₀.onlineBatch.loc.shape Wn)
    (w0 : Wn) (o : Option (Work Nn L₀)) :
    Gen.Extractor (spec lam (D.WO o).K (D.LO o)) I X Wn (IVKK lam (D.LO o)) (PrfK lam (D.LO o)) :=
  Gen.totalE w0 (extractorBKTo (D.WO o) j (witDoor D w o))

end Door

-- Limit: the statement has the hypothesis `Gen.MissLe` at the round j, which this library proves
--   for j = 0 alone (`missLe_zero`, CompileK/WideZero.lean).
end Compile.Batch
