-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HeadExistsAtName.lean: THERE IS A HEAD: the one head of the counted statements at the closed constant (AtMgA, Johnson/P5J/MgAtAll.lean) HAS A MEMBER AT THE NAME, under four premises on the three public files Z. Two theorems. One call in another.
  Why. Every counted statement stands "under every head h : AtMgA …". A reader asks beneath each: is there one? Here: yes, in Lean, under what is evaluated.
  head_exists_at_name: in scope · readFiles returns · the verifier's own three values are laid (protocolDataWellFormed (asDescriptionFiles Z) = true) · At.CondsOwed Z (what conds_of_laid still owes: Johnson/Goal/Skeleton/CondsOfLaid.lean) → ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x.
  BY: conds_of_laid (the four → At.Conds Z) · headA_at_name (Johnson/P5J/AtNameA.lean): the same two calls that the proof file's share of the top makes, ended in the head itself.
  head_exists_of_rows: the same from rowsRead Z: wherever this file compiles At.CondsOwed Z has that one field (⟨rows⟩ types).
  AtMgA is a Prop: so the bare ∃.
Limits. The four premises are premises: at the release's full-size public files the first three are evaluated true by name (runs, no theorem); the fourth is other files' to speak of (Johnson/Goal/Skeleton/CondsOfLaid.lean). It says nothing on how many heads there are (other files' law). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtNameA
import Johnson.Goal.Skeleton.CondsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- **THERE IS A HEAD AT THE NAME.** -/
theorem head_exists_at_name (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (owed : At.CondsOwed Z) :
    ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x :=
  headA_at_name scope hl read (conds_of_laid scope hl read owed)

/-- The same from the one field that At.CondsOwed has in this build: LEAN's OWN WORD THAT IT HAS NO
OTHER (the anonymous constructor takes this one argument). -/
theorem head_exists_of_rows (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (rows : rowsRead Z) :
    ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x :=
  head_exists_at_name Z scope read hl ⟨rows⟩

end P5J

#print axioms P5J.head_exists_at_name
#print axioms P5J.head_exists_of_rows
