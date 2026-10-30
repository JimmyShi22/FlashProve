-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/FirstAtLastWitness.lean: kind K14: what the second chain's honest
witness (lastWitness, Honest/Thread/TheFirstThread.lean) holds of the FIRST chain is what the first
chain's own honest witness holds: the cells, the token, and the words of every message that sits in
one of the first chain's trees. Statements with their proofs; no definition.

lastWitness is the first chain's witness with the shared chain's three sampled messages laid over
it at their seats. So a sentence on the first chain's witness that reads the cells, the token, and
words at seats of the first chain's trees alone holds of lastWitness as well. This file gives the
equations by which such a sentence is carried over.

  lastWitness_cells, lastWitness_tok   the two other components are the first chain's witness's
  tab_first           the library's accessor Wit.tab returns the same table off both witnesses at a
                      tenant of a tree of the first chain
  tabAt_first         so does tabAt (Johnson/Desc/Sound/TabAt.lean), at a message whose seat, if it
                      has one, lies in a tree of the first chain
  wordsBy_first       **so the library's reading wordsBy (Johnson/Desc/Sound/WordsAt.lean) takes the
                      same words off both witnesses at such a message**, at every part and index

From lastWitness_first (Honest/K14/WordsAtLastWitness.lean).

Limits.
  * BOTH SIDES STAND AT ONE LIST OF CHALLENGES: the right side is the first chain's witness at the
    list that the second chain's thread hands on, not at the list at which a sentence of the first
    chain's thread was had. Such a sentence holds at every continuation of what was heard
    (Thread.Items, Honest/Thread/Thr.lean), so a caller takes the rest of the list as the
    continuation.
  * h : HeadAtReturn holds the library's hypothesis on the public files at the full size
    (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). It is a hypothesis.
  * hs, that the message's seat lies in a tree of the first chain, is a premise. Which messages of a
    statement meet it is not said here.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.WordsAtLastWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.Sound (wordsBy tabAt)
open ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The cells are the first chain's witness's. -/
theorem lastWitness_cells (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) :
    (lastWitness h first reads k w heard).cells = (first.script.wit k w heard).cells := rfl

/-- The token is the first chain's witness's. -/
theorem lastWitness_tok (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) :
    (lastWitness h first reads k w heard).tok = (first.script.wit k w heard).tok := rfl

/-- At a tenant of a tree of the first chain the library's accessor returns the same table off both
witnesses. -/
theorem tab_first (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (j t : Nat) (hj : j < h.description.t₁) (cs : OnBytes.Codes)
    (s : OnBytes.OracleShape) :
    (lastWitness h first reads k w heard).tab cs s (P5J.At.arr A.Z j t) j t =
      (first.script.wit k w heard).tab cs s (P5J.At.arr A.Z j t) j t := by
  obtain ⟨e1, e2⟩ := lastWitness_first h first reads k w heard j t hj
  funext mask row place
  unfold VerifiableInference.Desc.Wit.tab
  rw [e1, e2]

/-- So does tabAt, at a message whose seat, if it has one, lies in a tree of the first chain. -/
theorem tabAt_first (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement) (o : Nat)
    (hs : ∀ q, seatAt o = some q → q.1 < h.description.t₁) (cs : OnBytes.Codes) :
    tabAt cs (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) o =
      tabAt cs (P5J.At.arr A.Z) seatAt S (first.script.wit k w heard) o := by
  unfold tabAt
  cases hq : seatAt o with
  | none => rfl
  | some q =>
    cases S.oracles[o]? with
    | none => rfl
    | some x => exact tab_first h first reads k w heard q.1 q.2 (hs q hq) cs x.shape

/-- **THE LIBRARY's READING TAKES THE SAME WORDS OFF BOTH WITNESSES AT A MESSAGE THAT SITS IN A TREE
OF THE FIRST CHAIN**, at every part and index. -/
theorem wordsBy_first (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement) (o : Nat)
    (hs : ∀ q, seatAt o = some q → q.1 < h.description.t₁) (part : OnBytes.Part) (i : Nat) :
    wordsBy (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) o part i =
      wordsBy (P5J.At.arr A.Z) seatAt S (first.script.wit k w heard) o part i := by
  unfold wordsBy
  exact VerifiableInference.Desc.Sound.wordsOn_congr S S _ _ o o rfl
    (tabAt_first h first reads k w heard seatAt S o hs S.codes) part i

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.lastWitness_cells
#print axioms ProofFile.Honest.K14.lastWitness_tok
#print axioms ProofFile.Honest.K14.tab_first
#print axioms ProofFile.Honest.K14.tabAt_first
#print axioms ProofFile.Honest.K14.wordsBy_first
