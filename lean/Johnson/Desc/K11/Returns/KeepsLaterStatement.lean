-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsLaterStatement.lean: PAST THE MERGE OF THE CLAIMS ON THE WEIGHTS THE
HEAD's LEDGER ONLY GROWS: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN
THIS FILE, and it is none of the library's goals: it is a lemma's statement. The texts are the
description's; no prover is named.

The library has that from a yes of the kind's decision (`decide_later`,
Johnson/Top/H0/MergeLaw/Keeps.lean). Here: from the kind's clause on what its member's step leaves
and turns (`K11Keeps`, KeepsStatement.lean of this folder) alone, for a caller that has the clause
and not the yes.

  `HeadMergeKeepsLater`   under the clause: the states in front and behind stand in the head's link,
                          at parts a and a'; the ledger a'.F is later than a.F in both of the
                          library's forms (`Fo.Later`, OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean;
                          `PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean): no fewer slots are
                          taken; as many slots are there; every slot that was filled is filled, and
                          holds the same shown value and the same factor; (the second form) the
                          three arrays keep their sizes

Limits. The clause is a premise. Nothing on which values are laid. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsStatement
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open VerifiableInference.Desc.First (S HeadOwn)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeKeepsLater : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11Keeps P s s' →
    ∃ a a' : HeadOwn, s.here = .head a ∧ s'.here = .head a' ∧ _root_.Fo.Later a.F a'.F ∧
      OnBytes.PscRun.Later a.F a'.F

end Johnson.Desc.First.ForkMerge.Returns
