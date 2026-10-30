-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/GrowsSays.lean: "EVERY OPEN ROW OF THE GROUP, AND EVERY SAMPLE ROW
OF ITS MEMBER, HOLDS AT THE WITNESS" GIVES THE LAST CLAUSE OF `DataFront` (ShapeAll.lean in this
folder): the rows that a proximity test takes in say true things of the words that the job's plain
rows make. The first is a sentence of the key file's first chain (the item `grows` of `meaning₁`,
Johnson/Desc/Key/KeyMeaning.lean), in the text `RowHolds` (Johnson/Desc/Key/KeyWords.lean); the
second is in the text `Says` (Johnson/Desc/Means/Says.lean), behind the test's beginning, at
`wordsAt` (Johnson/Desc/K12/Honest/LaidState.lean), which is 0 off the group's members. THE OTHER
DIRECTION STANDS IN THE LIBRARY (Johnson/RunOne/Law/GrowsOfAllSay.lean: `grows_of_allSay`); this
file is its converse and calls its lemma `says_members` (what a row that has passed the adding's
tests says hangs on the members' tables alone), the library's `rowHolds_iff_says_of_rowIn`
(Johnson/Desc/Key/RowHoldsSays.lean), `runRows_iff_items` and `allSay_begun`
(Johnson/Desc/Means/ItemsAt.lean, ItemsBegun.lean). Statements and proofs.

  **`allSay_of_holds`**   the statement is in order · no open row is marked as a sample row · every
                 open row of the group and every sample row of its members holds at val · val reads,
                 on the members' tables, as the job's words ⟹ the clause
  **`allSay_of_grows`**   the same from the item `grows`, where the group has one member: the oracle
                 message that the plan names as the witness's message 1

Limits. THE PREMISE "val reads as the job's words" IS THE TIE BETWEEN THE WITNESS AND THE JOB: it is
asked. The letter for sameness is taken at the filling "the two read as one element". Nothing on
completeness, on soundness or on what is hidden.


-/
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.Desc.Means.ItemsBegun
import Johnson.Desc.K12.Honest.LaidState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc.Key (RowHolds rowHolds_iff_says_of_rowIn)
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)
open H2K.First

/-- **From "every row holds at the witness" to the clause.** val: the statement's oracle messages'
entries, read off the witness. -/
theorem allSay_of_holds (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (hI : InOrder S) (hK : OpenKinds S) (val : ℕ → Part → ℕ → E) (Ly : GroupLayout)
    (R : PlainRows)
    (h1 : ∀ r ∈ G.rows.toList, RowHolds (fun a b => readE a = readE b) S val r)
    (h2 : ∀ o ∈ G.members.toList, ∀ x : Oracle, S.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, RowHolds (fun a b => readE a = readE b) S val r)
    (hw : ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize S o pt,
      readE (val o pt i) = wordsAt (begun S g G) Ly R o pt i) :
    AllSay rdE (begun S g G) (runRows S G).toList (wordsAt (begun S g G) Ly R) := by
  have hval : AllSay rdE S (runRows S G).toList fun o pt i => readE (val o pt i) := by
    refine (runRows_iff_items rdE hK g hG _).2 ⟨fun i r hr => ?_, fun o ho x hx r hr => ?_⟩
    · obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
      rw [hG] at hG'
      obtain rfl := Option.some.inj hG'
      have hmem : r ∈ G.rows.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hi)
      exact (rowHolds_iff_says_of_rowIn rdE S G val r (hI.rows g G hG r hmem)).1 (h1 r hmem)
    · exact (rowHolds_iff_says_of_rowIn rdE S G val r ((hI.samples o x hx r hr).isIn ho)).1
        (h2 o ho x hx r hr)
  exact (allSay_begun rdE hI g hG _).2 fun r hr =>
    (says_members (hI.runRows g G hG r hr) _ _ hw).1 (hval r hr)

open VerifiableInference.Desc (Strs Wit) in
open VerifiableInference.Desc.Key (KPlan KRead KReaders meaning₁ valOf) in
/-- **From the item `grows`.** -/
theorem allSay_of_grows {P St Cells M : Type} (K : KPlan) (Rd : KRead Cells M) (X : KReaders St)
    (near : ℕ → P × St → Strs → Prop)
    (forms worth other : ℕ → String → P × St → Strs → Wit Cells Unit M → Prop) (a : P × St)
    (y : Strs) (w : Wit Cells Unit M) (g : ℕ) (G : Group) (o : ℕ)
    (hg : X.grpB a.2 = some g) (hG : (X.st a.2).groups[g]? = some G) (ho : K.orc 1 = some o)
    (hm : G.members.toList = [o]) (hsame : Rd.same = fun a b => readE a = readE b)
    (hI : InOrder (X.st a.2)) (hK : OpenKinds (X.st a.2)) (Ly : GroupLayout) (R : PlainRows)
    (hw : ∀ pt, ∀ i < tableSize (X.st a.2) o pt,
      readE (valOf K Rd w o pt i) = wordsAt (begun (X.st a.2) g G) Ly R o pt i)
    (h : (meaning₁ K Rd X near forms worth other).grows a y w) :
    AllSay rdE (begun (X.st a.2) g G) (runRows (X.st a.2) G).toList
      (wordsAt (begun (X.st a.2) g G) Ly R) := by
  obtain ⟨g', G', o', x, hg', hG', ho', hx, -, h1, h2⟩ := h
  obtain rfl := Option.some.inj (hg.symm.trans hg')
  obtain rfl := Option.some.inj (hG.symm.trans hG')
  obtain rfl := Option.some.inj (ho.symm.trans ho')
  rw [hsame] at h1 h2
  refine allSay_of_holds (X.st a.2) g G hG hI hK (valOf K Rd w) Ly R h1 (fun o' ho' x' hx' => ?_)
    fun o' ho' => ?_
  · rw [hm] at ho'
    obtain rfl := List.mem_singleton.1 ho'
    obtain rfl := Option.some.inj (hx.symm.trans hx')
    exact h2
  · rw [hm] at ho'
    obtain rfl := List.mem_singleton.1 ho'
    exact hw

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.allSay_of_holds
#print axioms ProofFile.Honest.K12.allSay_of_grows
