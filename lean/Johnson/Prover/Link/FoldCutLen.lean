-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldCutLen.lean: A FOLD's CUT HAS ONE ROUND AND ONE FOR EACH ROW VARIABLE. One
statement and its proof, off foldCut's text (Johnson/Prover/Link/FormFold.lean). A file of its own,
over FormFold alone, so that both FormStep.lean (the form of the verifier's state) and BodyCuts.lean
(how many rounds and openings the blocks have) can call it.

Not shown here. That a plan's cut passes foldCut. Nothing on a decision, on soundness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link

theorem length_of_foldCut {k : Nat} : ∀ {cut : List Fmt.DeclaredRound}, foldCut k cut = true →
    cut.length = 1 + k
  | [], h => by cases h
  | dE :: dR, h => by
    unfold foldCut at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    show dR.length + 1 = 1 + k
    rw [h.1.1.2, Nat.add_comm]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.length_of_foldCut
