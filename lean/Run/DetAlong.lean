-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DetAlong.lean: two families of oracle functions that agree on the queries which a run asks give
the same result of that run.

A definition that computes, one theorem. Generic. An oracle computation `c : OComp S α`
(Rom/OComp.lean) asks typed oracles; a family `g : Fam S` (Rom/OSpec.lean) has one function for
each of them. The run is the one in which every coin toss yields 0 (Rom/Cache.lean: `OComp.det`).

Main names:
  `OComp.askedOK g P c`: a test that can be run.
  `det_congr_asked`: if g and g' agree wherever P holds, and askedOK g P c, then c.det g = c.det
    g'.

Why: an encoding sends only the typed queries that fit a format's plan to the format's strings, and
all others behind an escape (Run/CodingPage.lean: `total`). A family of typed oracles written
directly from the format, and the family that the encoding of the queries reads out of the single
oracle (Run/DetOverOne.lean), agree on the queries that fit (Run/CodingAgree.lean: `agree`, under
its hypothesis `PageFit`). So on a given input the two runs have one answer as soon as askedOK says
that the verifier asked nothing else: a computation on that input.

Limits: this file does not say that a verifier asks only fitting queries on every input.

Terms: lean/GLOSSARY.md.
-/
import Rom.Cache

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {α : Type}

/-- Every query of the run under g, every coin toss yielding 0, passes the test P. -/
def OComp.askedOK (g : Fam S) (P : (o : S.ι) → S.Dom o → Bool) : OComp S α → Bool
  | .pure _ => true
  | .sample _ k => (k 0).askedOK g P
  | .query o q k => P o q && (k (g o q)).askedOK g P

theorem det_congr_asked (g g' : Fam S) (P : (o : S.ι) → S.Dom o → Bool)
    (h : ∀ o q, P o q = true → g o q = g' o q) (c : OComp S α) (hc : c.askedOK g P = true) :
    c.det g = c.det g' := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact ih 0 hc
  | query o q k ih =>
      have h2 : (P o q && (k (g o q)).askedOK g P) = true := hc
      rw [Bool.and_eq_true] at h2
      show (k (g o q)).det g = (k (g' o q)).det g'
      rw [← h o q h2.1]
      exact ih (g o q) h2.2

end Rom
