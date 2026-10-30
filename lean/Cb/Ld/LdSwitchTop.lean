-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchTop.lean: the code switch "with lists": the proof of `Spec.ldSwitch_goodT` (stated,
with all its hypotheses, in Cb/Ld/LdSwitch.lean).
What is proved: under the hypotheses of its statement, the code switch has all that the bundle
`IOR.GoodT` (Ior/KnowCollGood.lean) asks, with the core `Unit`; and nothing is withheld, in this
sense: `pBad` = 0 (`IOR.Nums`, Ior/Chain.lean). One of these hypotheses is privacy of the sample
with a simulator at error 0 (`D.Zo.PrivateSim E`).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

The code switch is the reduction of Cb/Ld/LdSwitch.lean, from a claim on a word under one code to
the same kind of claim on a new word under another code.
The proof puts together `Spec.ldSwitch_good` (proved in Cb/Ld/LdSwitchProofs.lean) at "all seeds are
good" and `Spec.ldSwitch_blind_of_sim` (proved in Cb/Ld/LdSwitchPrivProofs.lean). Nothing is defined
here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSwitchProofs
import Cb.Ld.LdSwitchPrivProofs

set_option autoImplicit false

namespace Cb
open Iop Prob

theorem ldSwitch_goodT : Spec.ldSwitch_goodT := by
  intro E P P' St _ _ _ _ _ D e e' L t' hL hR hl hZo hZb hP hZ
  refine ⟨goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _
      (ldSwitch_good E P P' St D Unit (fun _ => ()) (fun _ => True) e e' L t' hL hR hl hZo hZb
        (ldSwitch_blind_of_sim E _ _ D.Zo hP) hZ),
    ?_⟩
  exact le_antisymm (prRho_empty _ fun _ h => h trivial) (zero_le _)

end Cb
