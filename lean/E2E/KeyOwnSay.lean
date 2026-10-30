-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSay.lean: the clause `say` of `OwnAsks`: the rows that the own test takes in hold of the words that the job's plain rows
make, from three statements at words w: the open rows hold of w, the members' sample rows hold of w, and on the members' tables w
is what the job's rows make. The twin of `allSay_of_holds` (198's K12/GrowsSays.lean) in the text `Says`, at a group of any number
of members.

  `say_of_items`: at a statement.
  `say_at_entry`: at the test's state on entry, from the chain's state.

What stays open. The three premises. `htie` is the tie of the words to the job: the members' tables as the run sent them.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.Means.ItemsBegun
import Johnson.Desc.K12.Honest.LaidState
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.Desc.Third.Law.Row0
import Johnson.Desc.K12.Seat.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Slice OnBytes.Means OnBytes.Slice.ProxRun
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)
open ProofFile.Honest.K12 (wordsAt PlainRows)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold)

/-- **From the words w to the job's words.** -/
theorem say_of_items (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) (hI : InOrder S)
    (hK : OpenKinds S) (w : Words GE) (Ly : GroupLayout) (R : PlainRows)
    (h1 : ∀ r ∈ G.rows.toList, Says rdE S r w)
    (h2 : ∀ o ∈ G.members.toList, ∀ x : Oracle, S.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says rdE S r w)
    (hw : ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize S o pt, w o pt i = wordsAt (begun S g G) Ly R o pt i) :
    AllSay rdE (begun S g G) (runRows S G).toList (wordsAt (begun S g G) Ly R) := by
  have hval : AllSay rdE S (runRows S G).toList w := by
    refine (runRows_iff_items rdE hK g hG _).2 ⟨fun i r hr => ?_, fun o ho x hx r hr => h2 o ho x hx r hr⟩
    obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
    rw [hG] at hG'
    obtain rfl := Option.some.inj hG'
    exact h1 r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))
  exact (allSay_begun rdE hI g hG _).2 fun r hr =>
    (says_members (hI.runRows g G hG r hr) _ _ hw).1 (hval r hr)

/-- **At the test's state on entry.** -/
theorem say_at_entry {st : S₃} {t : T12} (he : enterOwn st = .ok t) (hI : InOrder st.st) (hK : OpenKinds st.st)
    (w : Words GE) (R : PlainRows) (h1 : RowsHold rdE st w)
    (h2 : ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ x : Oracle,
      st.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says rdE st.st r w)
    (hw : ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
      w o pt i = wordsAt (begun st.st st.loc.own G) (layoutOf st.st G) R o pt i) :
    ∀ G, t.st.groups[t.g]? = some G →
      AllSay rdE (begun t.st t.g G) (runRows t.st G).toList (wordsAt (begun t.st t.g G) (layoutOf t.st G) R) := by
  have e : t = {
      st := st.st, book := st.book, roots := st.roots, g := st.loc.own, pass := .nothing,
      mask := st.loc.mask } := (Except.ok.inj he).symm
  subst e
  intro G hG
  exact say_of_items st.st st.loc.own G hG hI hK w _ R (h1 G hG) (h2 G hG) (hw G hG)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.say_of_items
#print axioms AtPublicFiles.KeyLastChain.say_at_entry
