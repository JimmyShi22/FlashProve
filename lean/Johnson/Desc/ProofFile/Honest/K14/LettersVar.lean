-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/LettersVar.lean: kind K14: THE SHARED CHAIN's LETTERS AS A
VARIABLE: WHAT THIS KIND ASKS OF THEM, AS ONE STRUCTURE OF NAMED PREMISES, each an equation on one
letter. Under it the letters ARE letters2 (Honest/K14/Thread2.lean) at the letters' own other
fields: so whatever is shown at letters2's thread at every Others holds at the thread of every such
L. THE WITNESS's TYPE Wt IS A VARIABLE TOO: this kind's sentences read a witness through ℓ : WitLens
Wt (Honest/K14/Thread2.lean: a reader to the words of the oracle messages and a writer back, with
two laws): at WitLens.words the witness is these words; at WitLens.snd it is a pair whose second
component they are.

  othersOf        of letters L: the fields that are not this kind's to lay, as a term of Others
  Asked ℓ L Q sentU c tests last holds   **the structure**: nine equations, one a letter
  letters_eq      under it L = letters2 Q sentU (othersOf ℓ L …) Cl
  at_letters      so a sentence that holds of letters2 at every Others holds of L
  asked_letters2  letters2 itself meets it, at every Others: so it can be met

Four of the nine say that a letter is fixed by this kind's own maker at the kind's borders, members,
items and messages, and free elsewhere: L.shape = form2 Q L.shape · L.keeps = keepsAll Q sentU
L.keeps · L.Mg w = mgWords ℓ Q L.N (L.Mg w) · L.wit = witL ℓ Q sentU holds L.wit: the last is met
wherever what ℓ reads of L.wit agrees with the honest words at the numbers of this kind's four
messages (witL_of_agree, Honest/K14/Thread2.lean); what else the witness holds is free. OF L.rides,
L.valid, L.hs, L.table, L.fixed, L.stored NOTHING IS ASKED HERE.

What is not claimed. That the letters of a proof file's IOP as written in Lean meet it. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Thread2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words InOrder)
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St chainOf first)
open Desc.K14.Honest (Inputs words2)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type}

/-- Of letters L: the fields that are not this kind's to lay. ℓ, c, tests, last, holds: what Others
has and the letters do not. -/
def othersOf (ℓ : WitLens Wt) (L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
    (c : Model.Verify.Chains) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs) : Others Bk W₀ Rc X₀ P₁ Wt :=
  { lens := ℓ, c := c, tests := tests, last := last, N := L.N, Mg₀ := L.Mg, shape := L.shape
    nothingLeft := L.nothingLeft, hs := L.hs, table := L.table, fixed := L.fixed
    stored := L.stored, n₁ := L.n₁, n₂ := L.n₂, valid := L.valid, keeps := L.keeps
    rides := L.rides, holds := holds, rest := L.wit }

/-- **What this kind asks of the shared chain's letters.** -/
structure Asked (ℓ : WitLens Wt) (L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
    (Q : P14) (sentU : Array OracleNotice) (c : Model.Verify.Chains) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs) : Prop where
  split : L.split = true
  Mg : L.Mg = fun w => mgWords ℓ Q L.N (L.Mg w)
  shape : L.shape = form2 Q L.shape
  order : L.order = fun s => InOrder s.st
  bs : L.bs = ((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder
  wit : L.wit = witL ℓ Q sentU holds L.wit
  first : L.first = first Q.codes
  item : L.item = Q.item
  keeps : L.keeps = keepsAll Q sentU L.keeps

/-- **Under the nine equations the letters are letters2 at their own other fields.** -/
theorem letters_eq {ℓ : WitLens Wt} {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt}
    {Q : P14} {sentU : Array OracleNotice} {c : Model.Verify.Chains}
    {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit}
    {holds : Coins Bk → Common W₀ Rc TableKey → Inputs}
    (h : Asked ℓ L Q sentU c tests last holds) :
    L = letters2 Q sentU (othersOf ℓ L c tests last holds) Cl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases L
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp only [letters2, othersOf, SharedThread.Letters.mk.injEq, true_and]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A sentence that holds of letters2 at every Others holds of every L that meets Asked. -/
theorem at_letters {ℓ : WitLens Wt} {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt}
    {Q : P14} {sentU : Array OracleNotice} {c : Model.Verify.Chains}
    {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit}
    {holds : Coins Bk → Common W₀ Rc TableKey → Inputs}
    (h : Asked ℓ L Q sentU c tests last holds)
    (p : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt → Prop)
    (hp : p (letters2 Q sentU (othersOf ℓ L c tests last holds) Cl)) : p L := by
  rw [letters_eq h]
  exact hp

/-- **letters2 meets Asked**, at every Others: each of this kind's makers, laid over its own
result, returns it. -/
theorem asked_letters2 (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : Asked O.lens (letters2 Q sentU O Cl) Q sentU O.c O.tests O.last O.holds where
  split := rfl
  Mg := rfl
  shape := by
    funext b s
    show form2 Q O.shape b s = form2 Q (form2 Q O.shape) b s
    unfold form2
    split <;> rfl
  order := rfl
  bs := rfl
  wit := witL_idem O.lens Q sentU O.holds O.rest
  first := rfl
  item := rfl
  keeps := by
    funext b s s'
    show keepsAll Q sentU O.keeps b s s' = keepsAll Q sentU (keepsAll Q sentU O.keeps) b s s'
    unfold keepsAll
    split <;> rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.asked_letters2
#print axioms ProofFile.Honest.K14.letters_eq
#print axioms ProofFile.Honest.K14.at_letters
