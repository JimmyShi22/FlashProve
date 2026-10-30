-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnSays.lean: `SaysAt` (K12/AsksWhole.lean) at a state in front of the key
file's own test, from what the thread's items give: words m of which every open row of the own group and every
member's sample rows hold, and that tie to the job's own rows on the members' tables.

  `says_at_stand`   `SaysAt` at the job, from these three, at a state whose way in is the job's state on entry and
                    whose statement is tidy

By what. `saysAt_of_items` (E2E/ItemLaws.lean); `tidy_of`: in order, no open row marked as a sample row.

Limits.
- hO, hS, hw are premises; hw, `WordsTied`, is the tie of the witness's words to the rows made at the lent coins:
  it binds the thread's witness. That a thread's witness meets it is not said here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnMarks
import E2E.ItemLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Means OnBytes.Slice
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob SaysAt plainMany WordsTied)
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items)

variable {W X : Type}

/-- **`SaysAt` from the three.** -/
theorem says_at_stand (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) {st : S₃}
    (he : enterOwn st = .ok (A.rec₀ w fr)) (ht : stTidyB st.st = true) (m : Words GE)
    (hO : ∀ i, OpenSays rdE st.st st.loc.own i m)
    (hS : ∀ G, st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList m)
    (hw : ∀ G, st.st.groups[st.loc.own]? = some G →
      WordsTied st.st st.loc.own G m (layoutOf st.st G) (plainMany A w fr C)) :
    SaysAt A w fr C := by
  have e : A.rec₀ w fr =
      { st := st.st, book := st.book, roots := st.roots, g := st.loc.own, pass := .nothing,
        mask := st.loc.mask } := (Except.ok.inj he).symm
  have hst : (A.rec₀ w fr).st = st.st := by rw [e]
  have hg : (A.rec₀ w fr).g = st.loc.own := by rw [e]
  refine saysAt_of_items A w fr C m ?_ ?_ ?_ (fun G hG => ?_) (fun G hG => ?_)
  · rw [hst]
    exact (tidy_of ht).inOrder
  · rw [hst]
    exact (tidy_of ht).kinds
  · rw [hst, hg]
    exact hO
  · rw [hst, hg] at hG
    rw [hst]
    exact hS G hG
  · rw [hst, hg] at hG
    rw [hst, hg]
    exact hw G hG

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.says_at_stand
