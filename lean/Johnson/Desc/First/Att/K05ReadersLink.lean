-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05ReadersLink.lean: kind K5: WHO PAYS hRds: the readers "of the link"
(K9.readersOfLink, Johnson/Desc/First/Batch/ReadersOfLink.lean), whatever stands in their two holes,
give at a name other than the approximate range proof's what the reader of the link's own stated
runs gives.

A LIGHT FILE, CUT OUT OF Johnson/Desc/First/Att/K05BehindWorthReaders.lean:
the one lemma stands here TO THE LETTER, moved by program, over the one import that it needs. Why:
the joins at the seated link call it, and so need not bring in that file's other imports (the law's
whole family).

Main name:
  hRds_of_link: at every link L, hearing block b, filling H of the two holes.
THE LETTERS UNDER "FOR ALL": H, L, b, name, s: free on purpose (a law of the readers' make); R: tied
by the premise readerOf … = some R.
IS IT EMPTY HERE? An implication; by unfolding.
Nothing is claimed on soundness, completeness or hiding.

-/
import Mathlib.Data.Nat.Notation
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K9 (readerOf)

/-- **Who pays hRds**: the readers "of the link", whatever stands in their two holes, at what the link's own blocks state. -/
theorem hRds_of_link (H : VerifiableInference.Desc.K9.LinkHoles) (L : VerifiableInference.Desc.Link First.S VerifiableInference.Desc.Claim) (b : ℕ) :
    ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf (VerifiableInference.Desc.K9.statesOfLink L) b name s = some R →
      (VerifiableInference.Desc.K9.readersOfLink H L).forms b name s = some R := by
  intro name s R hn hr
  show (if name == "K8.equations" then H.small s
    else match readerOf (VerifiableInference.Desc.K9.statesOfLink L) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = some R
  rw [hn, hr]
  rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.hRds_of_link
