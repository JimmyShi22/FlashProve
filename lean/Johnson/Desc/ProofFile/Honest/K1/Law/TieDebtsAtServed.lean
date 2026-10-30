-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieDebtsAtServed.lean: THE ITEM "tie
m": THE TWO PREMISES OF exchangeAtS_tie_wide
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShareWide.lean) THAT NAME THE INPUT, hOwn AND hSmall,
BOTH FROM ONE SENTENCE ON THE INPUT, hTr: at a valid input the reader's cells are the reader cellOf
X at the model's own full-size trace theTrace X i x, at an index i and a request x that i serves.
Three theorems; NO DEFINITION.
NO PROPERTY IS
CLAIMED.

  - small_of_reader   at letters X, T, C: if every entry of T is below 129 in absolute value and
                  C's cell is cellOf X T, signedOf of every cell of C is at most 128 in absolute
                  value. By the library's cellOf_int and signedOf_cast
                  (Johnson/HonestTrace/DigitsAtTrace.lean), as inside its cellsSmall_cellOf.
  - hOwn_of_served   hOwn, to the sign, at Sz.ref and the place's own list K3.matsOwn X m (m < 25).
  - hSmall_of_served   hSmall, to the sign.

THE TWO BINDERS. hTr, ON TWO TERMS. (h1) A BINDER, NEVER A DEFINITION: no new name for
"the cells are a trace's": the library's named form of it is CellsOwnAt
(Johnson/FrontRoad/CellsOwnAtSpec.lean). A payer at a filling, hTr_at_base
(AtFullSide/K1/TieAtBase.lean), goes BESIDE it, from a binder hI on the filling's trace: the tie
to CellsOwnAt is not typed. (h2) i AND x ARE FIXED ONLY UP TO WHAT cellOf X READS OF
theTrace X i x; AND hTr MAY HOLD EMPTILY WHERE NO w IS VALID: then both ends hold for nothing.
OF COMPLETENESS's KIND: IT NAMES THE INPUT: never told as public. hMA, ON THREE TERMS:
(m1) a binder, never a definition · (m2) its payer is named in this head
(meetsAll_theTrace at X := P5J.At.X Zp: one call, in a file that may stand in the goals' scope) ·
(m3) it feeds premises of completeness's kind: NOT IN FRONT OF A LAW OVER COINS (the rule:
Johnson/Bind/ForProver/FiveFieldsAt.lean's head). hMA stays a binder rather than draw
61 Goal modules beneath this file. THE PAYER: under the library's
head h (P5J.AtMg, Johnson/P5J/AtMg.lean: its fields scope, reads and pubOne are that theorem's
three premises), at X := P5J.At.X Zp: fun i x S => meetsAll_theTrace h.scope h.reads h.pubOne S:
TYPED AT AtFullSide/K1/TieAtBase.lean. WHAT IT IS: a sentence on X at every index and request: the
library's own theorem meetsAll_theTrace (Johnson/Goal/HonestTrace/FullPlanesInScope.lean) under
three premises on the public files (Z is in the goals' scope; the goals' reader returns pp;
publicOf returns X); HERE A PREMISE; no w, no run, no coin is named. WHY A BINDER: an import of
that file would draw 2,187 of the library's modules more beneath this one (3,273 today), 61 of them
under Johnson/Goal/, where none lies beneath it today [counted by import lines, this file's own
cone against that file's].

Limits. hTr, hMA, PartsFit X AND PlanMarks X ARE PREMISES: proved here of nothing. THAT THE THREE
PREMISES ON THE PUBLIC FILES ARE HAD AT ProofFile's LETTERS IS SAID BY NO LAW OF THIS FILE (the head's
three fields say it: see above). WHAT STAYS: hTr is paid here at no letters; the tie to CellsOwnAt
is not typed; the one rewriting that lays X beside the ground's G.W (IM.Open.W,
Johnson/IMR/SeatOpen.lean) is typed in TieShareServed.lean and AtFullSide/K1/TieAtBase.lean, not
here. AT Sz.ref ALONE. The other premises of exchangeAtS_tie_wide (hM, hSt, hF1, hF2) are untouched.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.OwnersAgreeAtTrace
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes
open OnBytes.HonestTrace (Sz Tr cellOf PartsFit PlanMarks ServesAt MeetsAll theTrace)
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (signedOf)

variable {X : Model.Verify.Public}

/-- At letters: a reader whose cell is the trace's reader's, at a trace of small entries, has small
cells. -/
theorem small_of_reader {T : Tr} (hs : ∀ k a r c, |T k a r c| < 129) {C : Cells}
    (hC : C.cell = cellOf X T) (k : ℕ) (s : String) (r c : ℕ) :
    (signedOf (C.cell k s r c)).natAbs ≤ 128 := by
  obtain ⟨z, hz, e⟩ := HonestTrace.cellOf_int X T hs k s r c
  rw [hC, e, HonestTrace.signedOf_cast z hz]
  rw [Int.abs_eq_natAbs] at hz
  omega

/-- **hOwn OF exchangeAtS_tie_wide, FROM hTr.** hTr: a binder, never a definition; i and x are fixed
only up to what cellOf X reads of theTrace X i x; it may hold emptily where no w is valid. OF
COMPLETENESS's KIND; never told as public. hMA: a premise here: see the head. -/
theorem hOwn_of_served {W : Type} {valid : W → Prop} {cells : W → Cells} (Mk : PlanMarks X)
    (N : PartsFit X)
    (hMA : ∀ i x, ServesAt X i x → MeetsAll X i x (theTrace X i x))
    (hTr : ∀ w, valid w → ∃ i x, (cells w).cell = cellOf X (theTrace X i x) ∧ ServesAt X i x)
    {m : ℕ} (hm : m < 25) :
    ∀ w, valid w → OwnersAgree Sz.ref (cells w) (K3.matsOwn X m) m := by
  intro w hw
  obtain ⟨i, x, hC, hS⟩ := hTr w hw
  exact ownersAgree_of_reader_own Mk N (HonestTrace.borrowedSame_of_meetsAll (hMA i x hS)) hC hm

/-- **hSmall OF exchangeAtS_tie_wide, FROM THE SAME hTr.** The same two binders, on the same terms.
-/
theorem hSmall_of_served {W : Type} {valid : W → Prop} {cells : W → Cells}
    (hMA : ∀ i x, ServesAt X i x → MeetsAll X i x (theTrace X i x))
    (hTr : ∀ w, valid w → ∃ i x, (cells w).cell = cellOf X (theTrace X i x) ∧ ServesAt X i x) :
    ∀ w, valid w → ∀ k s r c, (signedOf ((cells w).cell k s r c)).natAbs ≤ 128 := by
  intro w hw k s r c
  obtain ⟨i, x, hC, hS⟩ := hTr w hw
  exact small_of_reader (hMA i x hS).small hC k s r c

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.small_of_reader
#print axioms ProofFile.Honest.K1.hOwn_of_served
#print axioms ProofFile.Honest.K1.hSmall_of_served
