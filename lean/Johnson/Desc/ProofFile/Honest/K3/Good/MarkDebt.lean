-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkDebt.lean: the kind "lookup" (K3): what the lookup owes
for its mark, at the frame's own name: `MarkDebt` (Honest/Law/CoverJoin.lean), at the letter P :=
"true": the mark reads no challenge in front of the member. Conditional. Two theorems: the two
bounds of Honest/K3/Good/MarkShare.lean, restated.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: a is the lookup's place and f its face. C, the kit, is
a variable; dsb is the data of the rounds of the lookup's member; kap is a letter for a share.

What is shown.
  `markK3_debt`: `MarkDebt C (markK3 a f) dsb (fun _ => True) (events f * kap)`.
  `markRun_debt`: the like for one run's mark, at `eventsRun f r * kap`.

Hypotheses that remain. Neither is shown in this file.
  `hc`, `hf`: the two named hypotheses of MarkShare.lean: `CanAll` and `FewAll`.

Imported: Honest/Law/CoverJoin.lean.

Limits. As those of MarkShare.lean: no number is evaluated. `member` (Honest/K3/Good/MarkToy.lean)
exhibits the two hypotheses together at a synthetic kit; by its head it shows nothing of the
release's kit. The bound for `markOut` is not here: `markOut_debt` (Honest/K3/Good/MarkOut.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkShare
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open VerifiableInference.Desc (Place)
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- **What the lookup owes for its mark.** -/
theorem markK3_debt (C : CK) (a : Place) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewAll C f dsb kap) :
    MarkDebt C (markK3 a f) dsb (fun _ => True) ((events f : ℝ≥0∞) * kap) :=
  fun fr _ => markK3_le C a f dsb kap hc hf fr

/-- **The like for one run's mark.** -/
theorem markRun_debt (C : CK) (a : Place) (f : LFace) (r : Run) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewAll C f dsb kap) :
    MarkDebt C (markRun a f r) dsb (fun _ => True) ((eventsRun f r : ℝ≥0∞) * kap) :=
  fun fr _ => markRun_le C a f r dsb kap hc hf fr

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.markK3_debt
#print axioms ProofFile.Honest.K3.Good.markRun_debt
