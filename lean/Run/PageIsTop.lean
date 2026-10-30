-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsTop.lean: the four main statements of Run/PageIs.lean follow from its parts.

Run/PageIs.lean compares two verifiers of a proof file, the compiled verifier behind a lenient
reader and the format's strict verifier. It cuts its main statements into parts that are proved
separately.

1. What the file contains. One statement (`Run.PQ.Spec.pi_top`). No other definition.

2. What is checked when the file compiles. Nothing beyond the type of the statement; there are no
tests (#guard) here.

3. Theorems. The statement is proved in Run/PageIsTopProofs.lean.
   `pi_top`: the four main statements, from `pi_facts`, `pi_strict1`, `pi_strict2`, `pi_chain`,
     `pi_after`.
   This is a conditional statement: five parts are its hypotheses. (The sixth part, `pi_typed`, is
   not among them: the Proofs file proves it outright.) What it shows: whoever proves these five, as
   they are stated in Run/PageIs.lean, has the four main statements; none of the five need be stated
   otherwise for their sake.

4. What is not claimed.
   That any of the five holds is not shown here. Which of them is proved, and where, stands in the
   head of Run/PageIs.lean (all five are).
   One of the five, `pi_strict2`, and with it `pi_core`, was false in its first form and has been
   restated. An implication from a false hypothesis says nothing; this statement names the five, so
   it is compiled anew whenever one of them is restated.
   So none of `pi_formula`, `pi_half`, `pi_core`, `pi_kits` is proved by this file alone.
   All that the head of Run/PageIs.lean leaves out is left out here too.

Sources. No text from outside enters.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIs

set_option autoImplicit false

namespace Run.PQ

/-- States: the four main statements of Run/PageIs.lean follow from five of its parts. -/
def Spec.pi_top : Prop :=
  Spec.pi_facts → Spec.pi_strict1 → Spec.pi_strict2 → Spec.pi_chain → Spec.pi_after →
  Spec.pi_formula ∧ Spec.pi_half ∧ Spec.pi_core ∧ Spec.pi_kits

end Run.PQ
