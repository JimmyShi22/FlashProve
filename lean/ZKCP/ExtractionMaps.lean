-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/ExtractionMaps.lean: "the extracted index is the committed one" carries over to two schemes.

`HasExtractionError` (ZKCP/Optional.lean) is an optional requirement: i* = i for the honest
committer. It carries over from a scheme G with batches over one oracle to `SpecialAny.oneOf G`, the
scheme of the form of ZKCP/Defs.lean (`Arg`) that G gives, and from the members of a family to the
combined scheme (`Arg.sigma`). Generic. Not part of the definitions of ZKCP/Defs.lean.

  `extraction_oneOf`   `Gen.HasExtractionError G E δ` (ZKCP/GenOptional.lean) implies
      `HasExtractionError (SpecialAny.oneOf G) (Special.extOf E) δ`.
  `extraction_sigma`   if each member `A t` has it with an extractor `E t` and the error δ (one δ
      for all t), and an extractor `Ex` of the combined scheme returns, on a key that names t, what
      `E t` returns, paired with t: `HasExtractionError (Arg.sigma A) Ex δ`.

Limits: nothing on a committer that is not the honest one. The condition on `Ex` is a hypothesis.
-/
import ZKCP.SpecialAny
import ZKCP.Sigma
import ZKCP.KeyTag
import ZKCP.Optional
import ZKCP.GenOptional

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP
open Rom (rom toRom ofRom trTo trOf famOf)

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

theorem extraction_oneOf (G : Gen.Arg (rom lam) I X W IVK ISK Pf)
    (E : Gen.Extractor (rom lam) I X W IVK Pf) {δ : ℝ≥0∞} (H : Gen.HasExtractionError G E δ) :
    HasExtractionError (SpecialAny.oneOf G) (Special.extOf E) δ := by
  intro i
  refine le_trans (le_of_eq ?_) (H i)
  rw [← Rom.Pr_toRom ((SpecialAny.oneOf G).C i).withTrace
        (fun _ => {o | (Special.extOf E).Ei o.1.1 o.2 ≠ some i}),
    Rom.toRom_withTrace, Rom.Pr_bind_pure]
  have e : toRom ((SpecialAny.oneOf G).C i) = G.C i := Rom.toRom_ofRom _
  rw [e]
  congr 1
  funext _
  ext o
  show E.Ei o.1.1 (trTo (trOf o.2)) ≠ some i ↔ E.Ei o.1.1 o.2 ≠ some i
  rw [Rom.trTo_trOf]

variable {T : Type} [DecidableEq T] {IVK ISK Pf : T → Type}

theorem extraction_sigma (A : ∀ t, Arg lam I X W (IVK t) (ISK t) (Pf t))
    (E : ∀ t, Extractor lam I X W (IVK t) (Pf t))
    (Ex : Extractor lam (T × I) X W (Σ t, IVK t) (Σ t, Pf t)) {δ : ℝ≥0∞}
    (hE : ∀ t (v : IVK t) tr, Ex.Ei ⟨t, v⟩ tr = ((E t).Ei v tr).map fun i => (t, i))
    (H : ∀ t, HasExtractionError (A t) (E t) δ) :
    HasExtractionError (Arg.sigma A) Ex δ := by
  rintro ⟨t, i⟩
  refine le_trans (le_of_eq ?_) (H t i)
  show Pr (((A t).C i).mapO fun k => ((⟨t, k.1⟩ : Σ t, IVK t), (⟨t, k.2⟩ : Σ t, ISK t))).withTrace
      _ = _
  rw [OComp.withTrace_mapO, Pr_mapO]
  congr 1
  funext _
  ext o
  show Ex.Ei ⟨t, o.1.1⟩ o.2 ≠ some (t, i) ↔ (E t).Ei o.1.1 o.2 ≠ some i
  rw [hE]
  cases (E t).Ei o.1.1 o.2 with
  | none => simp
  | some j => simp

end ZKCP
