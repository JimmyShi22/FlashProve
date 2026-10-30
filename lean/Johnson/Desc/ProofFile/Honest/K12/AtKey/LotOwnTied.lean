-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnTied.lean: `WordsTied` (K12/SaysOfMet.lean) AT THE KEY FILE's OWN TEST, in
the form that `says_at_stand` (OwnSays.lean) asks as hw: at the term `wordsAtKeyOwnTest`, at the coins that the frame
lends the test's row; what a thread's witness then owes, by name; and `SaysAt` from these.

  `find_three`                   a layout of three members that differ finds each at its place
  `tableSize_begun`              the test's beginning changes no table's size
  `wordsTied_at_letters`, `wordsTied_at_key_own_test`    THE STATEMENT, at the term: at the job with letters; at the chain's
  `WitnessHoldsOwnTestWords`     THE THREAD's DEBT: on the members' tables the words that a reader reads off the witness
                                 are the term
  `wordsTied_of_witness_at_letters`   so `WordsTied` at the witness's words
  `saysAt_at_letters`, `saysAt_at_key_own_test`   `SaysAt` at the job, from the debt, the open rows (hO) and the sample rows (hS) at the
                                 witness's words, at a state on entry that is in order

What stays a premise. On the parts `SendersReadInFront`; on the book `BookAtOwnTest`; on the plan
`SharedPlanAtOwnTest`; on the state `StatementAtOwnTest`; on the challenges `HeardAtOwnTest`; that the frame lends; the
thread's debt; hO, hS.

Can it be empty. m is no longer free: hO and hS are asked AT THE WITNESS's WORDS, which the debt ties to a term made of
the senders' own texts, purses and fronts: so `wordsTied_at_key_own_test` ties two terms written apart, and can say
no: at a part whose data reads the test's longer front, at a book whose carried entry starts elsewhere, at another
round for "LIN point". That the five structures can be met together at the written sizes is shown by nothing here.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `lendRow`'s return is a premise.
- No thread is named: a stand's facts come in as the structures.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnTies
import E2E.ItemLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Group Oracle GroupLayout)
open OnBytes.Means (Words tableSize layoutOf OpenKinds OpenSays sampleItem)
open OnBytes.Slice (GE rdE begun)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open AtPublicFiles.KeyFile (KeyParts In1)
open VerifiableInference.Desc.K12 (P12 T12)
open AtPublicFiles.KeyLay (pWK doorKW)
open ProofFile.Honest.K12.Light (WordsTied SaysAt plainMany lendRow_snd)
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items)

/-- A layout of three members that differ finds each at its place. -/
theorem find_three (L : GroupLayout) (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : L.members = #[a, b, c]) : L.find a = some 0 ∧ L.find b = some 1 ∧ L.find c = some 2 := by
  unfold GroupLayout.find
  rw [hm]
  have e1 : (a == b) = false := by simpa using hab
  have e2 : (a == c) = false := by simpa using hac
  have e3 : (b == c) = false := by simpa using hbc
  refine ⟨?_, ?_, ?_⟩
  · simp [List.idxOf?, List.findIdx?_cons]
  · simp [List.idxOf?, List.findIdx?_cons, e1]
  · simp [List.idxOf?, List.findIdx?_cons, e2, e3]

/-- The test's beginning changes no table's size. -/
theorem tableSize_begun (S : Statement) (g : ℕ) (G : Group) (o : ℕ) (pt : OnBytes.Part) :
    tableSize (begun S g G) o pt = tableSize S o pt := by
  unfold tableSize OnBytes.Statement.tableBits
  rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk V Wt : Type}

section
variable (K : KeyParts W₀ Rc X₀ X Wk) (q : P12) (door : Local W₀ Rc Xi Unit → Front X → T12)
  (firstChain : ℕ) (N : OwnTestNumbers)

/-- **`WordsTied` at the term**, in hw's form, at the job with its numbers, door and count as letters.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem wordsTied_at_letters (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = firstChain)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hear : HeardAtOwnTest K N fr.heard heard)
    (c : RowCoins [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
      restPart (jobAtLetters K q door firstChain).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobAtLetters K q door firstChain).p.place
      [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
        restPart (jobAtLetters K q door firstChain).toRun.toTest] 0 = .ok c)
    (S : Statement) (g : ℕ) (hS : StatementAtOwnTest S g K N) :
    ∀ G, S.groups[g]? = some G →
      WordsTied S g G (wordsAtKeyOwnTest K N k input heard) (layoutOf S G)
        (plainMany (jobAtLetters K q door firstChain) input fr
          (restCoins (jobAtLetters K q door firstChain).toRun.toTest c.2.1)) := by
  intro G hG o ho pt i hi
  have hlp := lendRow_snd Bk _ _ _ _ _ c hc
  have hmem := hS.members G hG
  have a1 := hS.apart.1
  have a2 := hS.apart.2
  have s1 := hS.sendsIndexMasks
  have s2 := hS.sendsVectorW
  obtain ⟨f0, f1, f2⟩ := find_three (layoutOf S G) _ _ _ (by omega) (by omega) (by omega)
    (show G.members = _ from hmem)
  have hoo : o = N.indexMasksFirst + (K.idx.P.sent.size - 1) ∨ o = N.vectorWFirst ∨
      o = N.omegaCopy := by
    have h' : o ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl | rfl
  · obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1
      ((OnBytes.Slice.begun_shape S g G _).trans hS.shapeIndexMasks)
    exact tie_at_index_masks K q door firstChain N reads book a1 a2 s1 k input fr heard
      hear.beforeIndexMasks c.2.1 hlp _ _ f0 y hy hys pt i
  · obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1
      ((OnBytes.Slice.begun_shape S g G _).trans hS.shapeVectorW)
    exact tie_at_vector_w K q door firstChain N reads book a2 s2 k input fr heard hear.beforeVectorW c.2.1
      hlp _ _ f1 y hy hys pt i
  · obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1
      ((OnBytes.Slice.begun_shape S g G _).trans hS.shapeOmega)
    exact tie_at_omega_copy K q door firstChain N reads book plan hfirst k input fr heard hear.point
      hear.pointHeard hear.pointLength c.2.1 hlp _ _ f2 y hy hys
      ((OnBytes.Slice.begun_codes S g G).trans hS.codes) pt i
      (by rw [tableSize_begun]; exact hi)

/-- **THE THREAD's DEBT**: on the tables of the own group's members the words that `get` reads off the witness are
the term. get: the reader at which the thread's items `rows` and the three pins are laid. -/
def WitnessHoldsOwnTestWords (get : Wt → Words GE)
    (wit : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Wt) (S : Statement) (g : ℕ) (k : Coins Bk)
    (input : In1 W₀ Rc) (heard : List Fmt.Drawn) : Prop :=
  ∀ G : Group, S.groups[g]? = some G → ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize S o pt,
    get (wit k input heard) o pt i = wordsAtKeyOwnTest K N k input heard o pt i

/-- **`WordsTied` at the witness's words.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem wordsTied_of_witness_at_letters (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = firstChain)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hear : HeardAtOwnTest K N fr.heard heard)
    (c : RowCoins [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
      restPart (jobAtLetters K q door firstChain).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobAtLetters K q door firstChain).p.place
      [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
        restPart (jobAtLetters K q door firstChain).toRun.toTest] 0 = .ok c)
    (S : Statement) (g : ℕ) (hS : StatementAtOwnTest S g K N) (get : Wt → Words GE)
    (wit : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Wt)
    (debt : WitnessHoldsOwnTestWords K N get wit S g k input heard) :
    ∀ G, S.groups[g]? = some G →
      WordsTied S g G (get (wit k input heard)) (layoutOf S G)
        (plainMany (jobAtLetters K q door firstChain) input fr
          (restCoins (jobAtLetters K q door firstChain).toRun.toTest c.2.1)) :=
  fun G hG o ho pt i hi => (debt G hG o ho pt i hi).trans
    (wordsTied_at_letters K q door firstChain N reads book plan hfirst k input fr heard hear c hc S g hS
      G hG o ho pt i hi)

/-- **`SaysAt` at the key file's own test**, from the thread's debt and its items at the witness's words.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem saysAt_at_letters (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = firstChain)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hear : HeardAtOwnTest K N fr.heard heard)
    (c : RowCoins [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
      restPart (jobAtLetters K q door firstChain).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobAtLetters K q door firstChain).p.place
      [(firstPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _),
        restPart (jobAtLetters K q door firstChain).toRun.toTest] 0 = .ok c)
    (hS : StatementAtOwnTest ((jobAtLetters K q door firstChain).rec₀ input fr).st
      ((jobAtLetters K q door firstChain).rec₀ input fr).g K N)
    (order : OnBytes.Means.InOrder ((jobAtLetters K q door firstChain).rec₀ input fr).st)
    (kinds : OpenKinds ((jobAtLetters K q door firstChain).rec₀ input fr).st)
    (get : Wt → Words GE) (wit : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Wt)
    (debt : WitnessHoldsOwnTestWords K N get wit ((jobAtLetters K q door firstChain).rec₀ input fr).st
      ((jobAtLetters K q door firstChain).rec₀ input fr).g k input heard)
    (openRows : ∀ i, OpenSays rdE ((jobAtLetters K q door firstChain).rec₀ input fr).st
      ((jobAtLetters K q door firstChain).rec₀ input fr).g i (get (wit k input heard)))
    (sampleRows : ∀ G, ((jobAtLetters K q door firstChain).rec₀ input fr).st.groups[
        ((jobAtLetters K q door firstChain).rec₀ input fr).g]? = some G →
      sampleItem rdE ((jobAtLetters K q door firstChain).rec₀ input fr).st G.members.toList
        (get (wit k input heard))) :
    SaysAt (jobAtLetters K q door firstChain) input fr
      (restCoins (jobAtLetters K q door firstChain).toRun.toTest c.2.1) :=
  saysAt_of_items _ _ _ _ (get (wit k input heard)) order kinds openRows sampleRows
    (wordsTied_of_witness_at_letters K q door firstChain N reads book plan hfirst k input fr heard hear c hc _ _ hS get
      wit debt)

end

section AtTheChain
variable (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (N : OwnTestNumbers)

/-- **`WordsTied` AT THE KEY FILE's OWN TEST, AT THE TERM**, in the form that `says_at_stand` asks
as hw: at the job `jobAtKeyOwnTest` (LotOwnTies.lean), at the coins that the frame lends the test's
row. NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem wordsTied_at_key_own_test (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K (pWK Pl).place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hear : HeardAtOwnTest K N fr.heard heard)
    (c : RowCoins [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest : Part V _ _),
      restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobAtKeyOwnTest K Xs Nr Pl).p.place
      [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest : Part V _ _),
        restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest] 0 = .ok c)
    (S : Statement) (g : ℕ) (hS : StatementAtOwnTest S g K N) :
    ∀ G, S.groups[g]? = some G →
      WordsTied S g G (wordsAtKeyOwnTest K N k input heard) (layoutOf S G)
        (plainMany (jobAtKeyOwnTest K Xs Nr Pl) input fr
          (restCoins (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest c.2.1)) :=
  wordsTied_at_letters K (pWK Pl) (doorKW Xs Nr Pl) _ N reads book plan hfirst k input fr heard hear
    c hc S g hS

/-- **`SaysAt` AT THE KEY FILE's OWN TEST**, from the thread's debt and its items at the witness's words.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem saysAt_at_key_own_test (reads : SendersReadInFront K N)
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
    (get : Wt → Words GE) (wit : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Wt)
    (debt : WitnessHoldsOwnTestWords K N get wit ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st
      ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g k input heard)
    (openRows : ∀ i, OpenSays rdE ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st
      ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g i (get (wit k input heard)))
    (sampleRows : ∀ G, ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st.groups[
        ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).g]? = some G →
      sampleItem rdE ((jobAtKeyOwnTest K Xs Nr Pl).rec₀ input fr).st G.members.toList
        (get (wit k input heard))) :
    SaysAt (jobAtKeyOwnTest K Xs Nr Pl) input fr
      (restCoins (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest c.2.1) :=
  saysAt_at_letters K (pWK Pl) (doorKW Xs Nr Pl) _ N reads book plan hfirst k input fr heard hear c
    hc hS order kinds get wit debt openRows sampleRows

end AtTheChain

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.find_three
#print axioms ProofFile.Honest.K12.AtKey.tableSize_begun
#print axioms ProofFile.Honest.K12.AtKey.wordsTied_at_letters
#print axioms ProofFile.Honest.K12.AtKey.WitnessHoldsOwnTestWords
#print axioms ProofFile.Honest.K12.AtKey.wordsTied_of_witness_at_letters
#print axioms ProofFile.Honest.K12.AtKey.saysAt_at_letters
#print axioms ProofFile.Honest.K12.AtKey.wordsTied_at_key_own_test
#print axioms ProofFile.Honest.K12.AtKey.saysAt_at_key_own_test
