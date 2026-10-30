-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindHonest.lean: under `L.Wired`, at any lawful wire (`W.OKG`), for the honest committer
the extracted index is the committed one, but for a hash event among the queries for its first
tree, also when rounds have tests (proof of work, "grinding").

Statements and proofs.
The optional requirement of the work that this protocol builds on (lean/CREDITS.md, "Further work").
`Gen.HasExtractionError A E δ` (ZKCP/GenOptional.lean): for every index i, `E.Ei`, applied to the
honest committer's verification key and its trace, returns i except with probability at most δ.

Why: Compile/Batch/Extraction.lean has the title's statement for a wire without tests
(`extractsHonestB` asks `W.OK`).
Of the wire's laws that proof uses two facts only, which the laws of a wire with tests (`W.OKG`)
have too: the encoded index fits under the tree (`fits`), and the reading of the external oracle's
symbols off the leaves (`B.ext.build_rd`). The committer's searches do not enter: the committer
builds the tree under the root in the key first, and the extractor takes, for every digest, the
first query of the trace with that answer; whatever the committer asks afterwards, tries of nonces
included, comes later in the trace.

Main names, each under the hypotheses of its statement:
  `Spec.extractsHonestBG`: the theorem `extractsHonestB` of Compile/Batch/Extraction.lean, for
    `W.OKG`: one application of the rule for any committer that first builds the tree under the
    root in its key (`extraction_of_first`, Compile/Batch/ExtractionSeed.lean, which of the wire's
    laws asks `W.OKG` only).
  `Spec.compileWire_honest`, `Spec.compileWire_honest_literal`: for any interface and any lawful
    wire: the scheme with the links in the key, with witnesses; over the typed oracles; in the
    literal form over one oracle.
  `Spec.compileWk_honest`, `Spec.compileWk_honest_literal`: for the scheme with work
    (CompileK/GrindMain.lean).


  `deltaB_Wk`: the bound is `deltaB D.W`: the
    tree under the root has the same depth.
The bound: deltaB W = 2 (2 · 2^depth)² / 2^λ: a hash event among the queries for the first tree
(`hashEvents`, Compile/Batch/Hash.lean, bounds its chance). No number of tries occurs in it.

Limits: what the heads of CompileK/Main.lean and CompileK/GrindMain.lean list as not said is not
said here either. One limit of the second does not hold here: this file has the forms with work for
the honest committer, `Spec.compileWk_honest`.
This file does not say that the honest
committer's key is good: a failed search of the committer leaves a key under which the verifier
rejects (that is inside α, CompileK/GrindMain.lean);
the index is extracted from such a key all the same. It says nothing on a dishonest committer
(index binding).

Terms: lean/GLOSSARY.md.
-/
import CompileK.GrindOpt
import Compile.Batch.ExtractionSeed

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob MeasureTheory Compile.Extr Compile.Batch.Cmpl Compile.Batch.Extr
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- If `L.Wired`: for the honest committer of the base scheme the extracted index is i, but for a
hash event among the queries for its first tree: at any lawful wire (`W.OKG`), with tests or
without. -/
def Spec.extractsHonestBG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params), L.Wired →
    W.OKG →
    ∀ i : I, pr (C W WP p i).withTrace.law {o | (extractorB W).Ei o.1.1 o.2 ≠ some i} ≤ deltaB W

theorem extractsHonestBG : Spec.extractsHonestBG := by
  intro I X lam L W WP p hwd hW i
  have h := extraction_of_first W WP p hwd hW i (erase (nodeP' W WP p i) []) id
    (fun x => (eraseR (Extr.restC W WP p i x.1) x.2).bind fun o => OComp.pure (o.1.1, (o.1.2, o.2)))
    (fun o => o.1.cm) (2 * 2 ^ W.depth)
    ((sq_nodeP' W WP p i).erase []) (fun f a ha => outsIn_of_withTrace ha)
    (fun f a b hb => by
      obtain ⟨z, hz, hbz⟩ := mem_outs_bind.1 hb
      rw [mem_outs_pure.1 hbz]
      exact Extr.tri_restC W WP p (realF f) i a.1 a.2 z (outs_realQ hz))
  rw [← Pr_eq_law, Extr.C_eq]
  exact h

end Compile.Batch

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open scoped ENNReal

namespace Spec

/-- Under `L.Wired` and `W.OKG`, `Gen.HasExtractionError` holds with error `deltaB W` for the
scheme with the links in the key, with witnesses, over the typed oracles. -/
def compileWire_honest : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn),
    L.Wired → W.OKG →
    Gen.HasExtractionError (Gen.withW Wn (argBKE W WP p)) (extractorBKW W wit w0) (deltaB W)

/-- The same for the literal form, over one oracle. (not all hypotheses are named here: see the
statement below) -/
def compileWire_honest_literal : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) (m : OracleCoding (spec lam W.K L) lam),
    m.blocks OracleName.leaf = 1 → m.blocks OracleName.node = 1 → L.Wired → W.OKG →
    ZKCP.HasExtractionError (SpecialAny.oneOf (schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))))
      (Special.extOf (extractorOverOneHashFunction m (extractorBKW W wit w0))) (deltaB W)

/-- Under the hypotheses below, `Gen.HasExtractionError` holds with error `deltaB (D.WWk w)` for
the scheme with work, `schemeWk` (CompileK/GrindMain.lean). -/
def compileWk_honest : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X Wn : Type) (L : BatchProtocol I X) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (w0 : Wn) (lam : ℕ) (D : DataK L lam) (w : Work Nn L),
    L.Wired → L.Opens D.no → L.maxBatchSize = 2 ^ D.ax.depthReq → FitWk lam w →
    Gen.HasExtractionError (schemeWk D w Wn) (extractorWk D w wit w0) (deltaB (D.WWk w))

def compileWk_honest_literal : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X Wn : Type) (L : BatchProtocol I X) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (w0 : Wn) (lam : ℕ) (D : DataK L lam) (w : Work Nn L)
      (m : OracleCoding (spec lam (D.WWk w).K (D.LWk w)) lam),
    m.blocks OracleName.leaf = 1 → m.blocks OracleName.node = 1 → L.Wired → L.Opens D.no →
    L.maxBatchSize = 2 ^ D.ax.depthReq → FitWk lam w →
    ZKCP.HasExtractionError (SpecialAny.oneOf (schemeOverOneHashFunction m (schemeWk D w Wn)))
      (Special.extOf (extractorOverOneHashFunction m (extractorWk D w wit w0))) (deltaB (D.WWk w))

end Spec

theorem compileWire_honest : Spec.compileWire_honest := by
  intro I X Wn lam L W WP p wit w0 hw hW i
  have h := extractsHonestBG _ _ lam L W WP p hw hW i
  rw [← Pr_eq_law] at h
  refine le_trans (le_of_eq ?_) h
  show Rom.Pr
      ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)).withTrace _ = _
  rw [withTrace_bind]
  exact Pr_bind_pure (C W WP p i).withTrace (fun out => (((out.1.1, linksOf (keyOf out.1.2.1)), out.1.2), out.2 ++ [])) _ |>.trans (by
    congr 1
    funext _
    ext o
    simp only [Set.mem_preimage, Set.mem_setOf_eq, List.append_nil]
    rfl)

theorem compileWire_honest_literal : Spec.compileWire_honest_literal := by
  intro I X Wn lam L W WP p wit w0 m h1 h2 hw hW
  refine extraction_oneOf _ _ fun i => ?_
  exact le_trans
    (le_of_eq (Top.extraction_overOne m (Gen.withW Wn (argBKE W WP p)) (extractorBKW W wit w0)
        (knowLocal _ _ _ lam L W _ w0 m h1 h2) i))
    (compileWire_honest I X Wn lam L W WP p wit w0 hw hW i)

section
variable {Nn : Type} [Inhabited Nn] {I X : Type} {L : BatchProtocol I X} {lam : ℕ}
  (D : DataK L lam) (w : Work Nn L)

/-- If `L.Wired`: the interface on blocks with tests (`D.LWk w`) decodes what it encodes, and its
honest sides speak of the encodings. -/
theorem wk_wired (hw : L.Wired) : (D.LWk w).Wired := ⟨hw.dec_enc, hw.extT, hw.extL, hw.extB⟩

/-- Under the hypotheses below, the wire with tests is lawful (`OKG`). -/
theorem wk_okg (ho : L.Opens D.no) (hN : L.maxBatchSize = 2 ^ D.ax.depthReq) (hf : FitWk lam w) :
    (D.WWk w).OKG :=
  (wireBDOK _ _ lam L D.pT D.pL D.pB D.z D.no D.dr D.ax ho hN).1.toG.grind
    hf.read hf.le (hf.allT.pull _) (hf.allL.pull _) (hf.allB.pull _)

/-- The bound is that of the wire without tests, `D.W`. -/
theorem deltaB_Wk : deltaB (D.WWk w) = deltaB D.W := rfl

end

theorem compileWk_honest : Spec.compileWk_honest := fun _ _ I X Wn _ _ w0 lam D w hw ho hN hf =>
  compileWire_honest I X Wn lam (D.LWk w) (D.WWk w) (D.WPWk w) D.p _ w0
    (wk_wired D w hw) (wk_okg D w ho hN hf)

theorem compileWk_honest_literal :
    Spec.compileWk_honest_literal := fun _ _ I X Wn _ _ w0 lam D w m h1 h2 hw ho hN hf =>
  compileWire_honest_literal I
    X Wn lam (D.LWk w) (D.WWk w) (D.WPWk w) D.p _ w0 m h1 h2 (wk_wired D w hw) (wk_okg D w ho hN hf)

end Compile.Batch
