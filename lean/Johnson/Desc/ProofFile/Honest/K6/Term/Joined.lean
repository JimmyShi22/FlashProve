-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/Joined.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the
online proof): three statements of Honest/K6/Term/Statements.lean, each joined of its clauses:
UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, where the kind stands; AND WHERE THE MAKER
RETURNS, which side the prover has there.

WHAT IT IS NOT. Joins alone: every clause is proved in another file. Facts on places and on lists of
sides: nothing on whether the side plays or is accepted. The library's hypothesis on the first chain
(P5J.AtMgA: the full size and the format's second hash function alone) and "the maker returns" are premises,
so the second and the third statement hold of nothing where the maker does not return. The maker is
onlineProverFromPublicFiles (Honest/AtPure.lean); the row is this kind's sender, headRow (Honest/K6/Part.lean). Nothing
on soundness, completeness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  standsAtOneBorderUnderTheHead   StandsAtOneBorderUnderTheHead: the first chain by
                                  firstChainHasTheKindOnce (Places.lean), the two later chains by
                                  laterChainsLackTheKind (LaterChains.lean)
  sideIsTheHeadRowAtTheBase       SideIsTheHeadRowAtTheBase: the first chain by sideAtTheBase
                                  (SideAtFilling.lean), the two later chains by
                                  laterSidesLackTheKind (LaterChains.lean)
  sideIsTheHeadRowAtTheFilling    SideIsTheHeadRowAtTheFilling: likewise, by sideAtTheFilling
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.Places
import Johnson.Desc.ProofFile.Honest.K6.Term.SideAtFilling
import Johnson.Desc.ProofFile.Honest.K6.Term.LaterChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term

/-- **Under the library's hypothesis on the first chain, the kind stands at one member of the online
description**: number 341 of the first chain, counted from 0. -/
theorem standsAtOneBorderUnderTheHead : StandsAtOneBorderUnderTheHead := by
  intro Z D r Zp Np cF x h
  obtain ⟨isThere, onlyThere⟩ := firstChainHasTheKindOnce h
  obtain ⟨sharedLacks, lastLacks⟩ := laterChainsLackTheKind h
  exact ⟨isThere, onlyThere, sharedLacks, lastLacks⟩

/-- **At the prover that the maker returns at the base filling, the side at the member's place is
the row, and no other side of the three chains is of this kind.** Two premises: the library's
hypothesis on the first chain and "the maker returns at the base filling". -/
theorem sideIsTheHeadRowAtTheBase : SideIsTheHeadRowAtTheBase := by
  intro W₀ Z D r Zp Np cF x I S O A h hA
  exact ⟨sideAtTheBase h I S O hA, laterSidesLackTheKind h hA⟩

/-- **The same at the filling read through** two readers, which is the form of the honest prover's
own filling. Two premises: the hypothesis and "the maker returns at that filling". -/
theorem sideIsTheHeadRowAtTheFilling : SideIsTheHeadRowAtTheFilling := by
  intro W₀ W₀' Rc' Z D r Zp Np cF x readIndex readRandomness namedIndex I S O A h hA
  exact ⟨sideAtTheFilling h readIndex readRandomness namedIndex I S O hA,
    laterSidesLackTheKind h hA⟩

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.standsAtOneBorderUnderTheHead
#print axioms ProofFile.Honest.K6.Term.sideIsTheHeadRowAtTheBase
#print axioms ProofFile.Honest.K6.Term.sideIsTheHeadRowAtTheFilling
