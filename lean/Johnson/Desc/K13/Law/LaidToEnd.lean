-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LaidToEnd.lean: "(Eval) IS LAID" (EvalLaid, Johnson/Desc/K13/Law/Laid.lean)
FROM ITS MAKER TO THE FIRST CHAIN's LAST RECORD, AND THE TABLE's ONE TEST THAT ITS PUBLIC ITEM IS
OPEN AT THE CHAIN's LAST BORDER. Theorems; no definition.

WHY. Row 0 of the last chain's table spends EvalLaid at the first chain's last record
(Johnson/Flat/Last/RowZeroAtSig.lean: hEL). The table's files have it from the first chain's last
promise (hEL_at_ocEnd, Johnson/Desc/Sound/JointFilling.lean) under ONE TEST on the promise's table:
Pub.evalLaid is among the public items open at the last border. Here: that test, by evaluation in
the kernel, at the two lists of segments as the table's walk writes them; and, on records, that what
W's sending lays the chain's last block keeps.

OBJECT   atM4 P (K1.sendAtS P') · First.firstEnd piece front: the two blocks' decisions ·
         First.pubSets: the table's own text.
USER     h2 of hEL_at_ocEnd | ocEnd_laid (evalLaid_open) · whoever ties the promise at the chain's
         last two blocks (laid_to_end): nobody calls it.
LETTERS  P · P' · piece · front; the lists linksSmall | linksFull
         (Johnson/Desc/K13/Law/AtTableRow.lean).
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0's hEL.

  firstEnd_laid        KEPT: the first chain's last block returns the record: by
                       Keeps.chainEnd_same, as firstEnd_sits (Johnson/Desc/K13/Law/SitsMade.lean).
                       (A file that is not in this library had it at row names: EndKeeps.lean.)
  laid_to_end          MADE AND KEPT: W's sending's yes from a record with FrontOk, then the last
                       block's yes: EvalLaid at the last record: atM4_laid CALLED.
  evalLaid_open        **the test**, at the door's filling wSitsMore, bare and merged into the empty
                       filling (the form in which hEL_at_ocEnd asks it at Mg₁.more := {}), at both
                       lists: borders 78 | 358, which are the lists' lengths (lengths_are).
What is not claimed. That the two lists are a real plan's: they are as the table's walk writes them.
At a filling into which other kinds' items are merged the test is to be run anew. That no block
stands between W's sending and the chain's last block: the chain's maker's. That the promise at the
last border is EARNED: the promise is not tied at the chain's last block. No member. No
soundness.

-/
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.K13.Law.SitsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame)

variable {Cl : Type}

/-- **KEPT**: the first chain's last block returns the record. -/
theorem firstEnd_laid (P : Where) (piece : ℕ) (front : List (Block S Cl)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (First.firstEnd piece front).decide s rs gs = .ok s') (hL : EvalLaid P s) :
    EvalLaid P s' := by
  rw [Keeps.chainEnd_same _ _ _ _ _ h]
  exact hL

/-- **MADE AND KEPT.** -/
theorem laid_to_end {F : Frame} {P : Where} {P' : K1.Par} (piece : ℕ) (front : List (Block S Cl))
    {s s₁ s' : S} {r₁ r₂ : Fmt.RoundView} {gs gs' : List (List (Nat × List UInt64))} {rs : List Fmt.RoundView}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s₁) (y : F.E.Str)
    (hon : FrontOk P ((s, y) : S × F.E.Str))
    (h' : (First.firstEnd piece front).decide s₁ rs gs' = .ok s') : EvalLaid P s' :=
  firstEnd_laid P piece front h' (atM4_laid h y y hon).1

/-- The two lists of places have 78 and 358 blocks. -/
theorem lengths_are : (First.flatPlaces true linksSmall true).length = 78 ∧
    (First.flatPlaces true linksFull true).length = 358 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The table's test: "(Eval) is laid" is open at the first chain's last border.** -/
theorem evalLaid_open :
    First.Pub.evalLaid ∈ (First.pubSets wSitsMore linksSmall
        (First.flatPlaces true linksSmall true))[(First.flatPlaces true linksSmall
          true).length]?.getD [] ∧
      First.Pub.evalLaid ∈ (First.pubSets wSitsMore linksFull
        (First.flatPlaces true linksFull true))[(First.flatPlaces true linksFull
          true).length]?.getD [] ∧
      First.Pub.evalLaid ∈ (First.pubSets (({} : First.More).merge wSitsMore) linksSmall
        (First.flatPlaces true linksSmall true))[(First.flatPlaces true linksSmall
          true).length]?.getD [] ∧
      First.Pub.evalLaid ∈ (First.pubSets (({} : First.More).merge wSitsMore) linksFull
        (First.flatPlaces true linksFull true))[(First.flatPlaces true linksFull
          true).length]?.getD [] := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
