-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSays.lean: THE DOORS OF `SaysAt` AT THE KEY FILE's OWN TEST: in which forms
the two debts on values (the open rows; the members' sample rows) may be handed in.

  `items_agree`        the open rows and the members' sample rows say of two families of words alike, where these agree
                       on the members' tables
  `openSays_of_group`  «every row of the own group says of the words» (the body of the item `rows`) gives every open
                       row's sentence
  `saysAt_at_term`     `SaysAt` FROM THE TWO DEBTS AT THE TERM `wordsAtKeyOwnTest`: no witness, no reader is named
  `items_at_term`      a thread's two debts at its witness's words are the two at the term, under the thread's debt
                       `WitnessHoldsOwnTestWords`

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `lendRow`'s return is a premise.
- Every debt is a premise.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnTied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Group)
open OnBytes.Means (Words tableSize OpenKinds OpenSays sampleItem AllSay runRows_iff_items rowAt_iff)
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyLay (pWK doorKW)
open ProofFile.Honest.K12.Light (SaysAt)
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items openSays_of_rows)

/-- **The two debts read the members' tables alone.** -/
theorem items_agree (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (hI : OnBytes.Means.InOrder S) (hK : OpenKinds S) (m m' : Words GE)
    (h : ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize S o pt, m o pt i = m' o pt i) :
    ((∀ i, OpenSays rdE S g i m) ∧ sampleItem rdE S G.members.toList m) ↔
      ((∀ i, OpenSays rdE S g i m') ∧ sampleItem rdE S G.members.toList m') := by
  rw [← runRows_iff_items rdE hK g hG m, ← runRows_iff_items rdE hK g hG m']
  exact ⟨fun a r hr => (says_members (hI.runRows g G hG r hr) _ _ h).1 (a r hr),
    fun a r hr => (says_members (hI.runRows g G hG r hr) _ _ h).2 (a r hr)⟩

/-- **From the body of the item `rows` to every open row's sentence.** -/
theorem openSays_of_group (S : Statement) (g : ℕ) (m : Words GE)
    (h : ∀ G : Group, S.groups[g]? = some G → AllSay rdE S G.rows.toList m) (i : ℕ) :
    OpenSays rdE S g i m := by
  cases hG : S.groups[g]? with
  | none =>
    intro r hr
    obtain ⟨G, hG', -⟩ := rowAt_iff.1 hr
    rw [hG] at hG'
    cases hG'
  | some G => exact openSays_of_rows rdE S m g G hG (h G hG) i

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk V Wt : Type}
  (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (N : OwnTestNumbers)

/-- **`SaysAt` AT THE KEY FILE's OWN TEST, FROM THE TWO DEBTS AT THE TERM.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem saysAt_at_term (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K (pWK Pl).place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hear : HeardAtOwnTest K N fr.heard heard)
    (c : RowCoins [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest : Part V _ _),
      restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobAtKeyOwnTest K Xs Nr Pl).p.place
      [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest : Part V _ _),
        restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest] 0 = .ok c)
    (hS : StatementAtOwnTest ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st
      ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g K N)
    (order : OnBytes.Means.InOrder ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st)
    (kinds : OpenKinds ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st)
    (openRows : ∀ G : Group, ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st.groups[
        ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g]? = some G →
      AllSay rdE ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st G.rows.toList
        (wordsAtKeyOwnTest K N k input heard))
    (sampleRows : ∀ G : Group, ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st.groups[
        ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g]? = some G →
      sampleItem rdE ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st G.members.toList
        (wordsAtKeyOwnTest K N k input heard)) :
    SaysAt (jobAtKeyOwnTest K Xs Nr Pl) input fr
      (restCoins (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest c.2.1) :=
  saysAt_of_items _ _ _ _ (wordsAtKeyOwnTest K N k input heard) order kinds
    (openSays_of_group _ _ _ openRows) sampleRows
    (wordsTied_at_key_own_test K Xs Nr Pl N reads book plan hfirst k input fr heard hear c hc _ _ hS)

/-- **A thread's two debts at its witness's words are the two at the term**, under the thread's debt. -/
theorem items_at_term (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (hI : OnBytes.Means.InOrder S) (hK : OpenKinds S) (get : Wt → Words GE)
    (wit : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Wt) (k : Coins Bk) (input : In1 W₀ Rc)
    (heard : List Fmt.Drawn) (debt : WitnessHoldsOwnTestWords K N get wit S g k input heard) :
    ((∀ i, OpenSays rdE S g i (get (wit k input heard))) ∧
        sampleItem rdE S G.members.toList (get (wit k input heard))) ↔
      ((∀ i, OpenSays rdE S g i (wordsAtKeyOwnTest K N k input heard)) ∧
        sampleItem rdE S G.members.toList (wordsAtKeyOwnTest K N k input heard)) :=
  items_agree S g G hG hI hK _ _ (debt G hG)

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.items_agree
#print axioms ProofFile.Honest.K12.AtKey.openSays_of_group
#print axioms ProofFile.Honest.K12.AtKey.saysAt_at_term
#print axioms ProofFile.Honest.K12.AtKey.items_at_term
