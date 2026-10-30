-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Ties.lean: TWO TIES BETWEEN A THREAD's WITNESS
(Honest/Thread/Thr.lean) AND THE HONEST SIDE's OWN LETTERS: A COMMON FORM FOR EACH: NOT FOR ALL
CALLERS: BY CALLER BELOW. DEFINITIONS: PREMISES' FORMS; and one lemma. Of the library's they name
the program's element with its zero (`OnBytes.E`, `OnBytes.zeroE`) and a place (`Place`), and
nothing else; the rest is the frame's (`lendRow`, `RowCoins`, `Part`, `ProverCoinCounts.rowsOf`) and the
thread's: what a caller's reader reads, and of what state, are letters.

Why. The authors of several kinds have typed such premises at their own kinds. Those that fit
share: at the border IN FRONT of the member, at every continuation of the challenges heard, an entry
that a reader reads off the thread's witness is a value that is made of the honest side's letters.

  1  `MaskTie`   the j-th mask entry under the member's slots is the j-th of the row's coins, as
     the book lends them at the run's coins
  2  `MaskTieBook`   the same with the right side said of the book and the coins alone
     (`rowSpent`, Law/Rule/Spent.lean): no part stands in it: what whoever sends the mask can show
  3  `maskTie_of_book`   the second gives the first, AT `spentOf` ALONE
  4  `CellsTie`   the honest side's cell is the cell that an item's sentence reads off the
     witness: A COMMON FORM, NO MORE: no law of ours stands behind it

BY CALLER, EACH BY THE WORD OF THAT KIND's OWN AUTHORS (other threads of this project; none of it is
compiled here). K5: `maskTie` is `MaskTie` by unfolding at its authors' own `spentOf`; at ours by an
induction (two definitions by recursion, letter for letter alike, are two constants); `cellsTie`
and `PlanesTie` against `CellsTie`: a line each way. K13: `CoinsTie` against `MaskTie`: two lines
each way; its coins are `spentOf`'s, so `MaskTieBook` reaches it; `MatTie` GIVES an instance of
`CellsTie`, AND THERE IS NO WAY BACK. K4: `K4MaskTie` is `MaskTie` by unfolding AT ITS AUTHORS' OWN
`spentOf`; at ours by their lemma that the two functions yield one list, by induction, as at K5
(Honest/K4/Law/TieIs.lean); `MaskTieBook` gives it: compiled by its authors, by their word. K11: NO
INSTANCE: its ties read the verifier's state BEHIND the member's step, and its coins are a free
letter. AND `CellsTie` COVERS TWO TIES WITH TWO PAYERS: the trace's cells against the witness's sent
messages (K4, K5), and the index's weights against the witness's cells (K13, K11).

Limits. NONE OF THEM IS SHOWN AT ANY THREAD. With the letters free each can be met for
nothing (a reader that is constant; J or In empty; opn that never opens). Nothing says that the
row's coins are as many as the member takes slots. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.Law.Rule.Spent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The mask's entry under a slot of the member is the coin that the book lent.** p, ps: the
member's place and its row's parts. opn: what of the verifier's state must be open. entry: the
    reader
of the member's j-th mask entry, off what is open, the state, the input and the witness. val: the
reading into the reader's field. coins: which of the row's coins. J n j: at which j, of n coins. A
premise's form. -/
def MaskTie (T : Thread Bk S Cl V W X Pb) (b : Nat) (p : Place) (ps : List (Part V W X))
    {A G : Type} (opn : S → Option A) (entry : A → S → W → T.Wt → Nat → G) (val : E → G)
    (coins : RowCoins ps → List E) (J : Nat → Nat → Prop) : Prop :=
  ∀ k s m En, Thr T b k s m En → ∀ a c, opn s = some a →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) p ps 0 = .ok c →
    ∀ ds j, J (coins c).length j →
      entry a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) j =
        val ((coins c).getD j zeroE)

/-- **The same, of the book and the coins alone.** n: how many parts the row has. A premise's form.
-/
def MaskTieBook (T : Thread Bk S Cl V W X Pb) (b : Nat) (p : Place) (n : Nat) {A G : Type}
    (opn : S → Option A) (entry : A → S → W → T.Wt → Nat → G) (val : E → G)
    (J : Nat → Nat → Prop) : Prop :=
  ∀ k s m En, Thr T b k s m En → ∀ a, opn s = some a → ∀ ds j,
    J (rowSpent Bk (k.look T.chain) p n 0).length j →
      entry a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) j =
        val ((rowSpent Bk (k.look T.chain) p n 0).getD j zeroE)

theorem maskTie_of_book {T : Thread Bk S Cl V W X Pb} {b : Nat} {p : Place}
    {ps : List (Part V W X)} {A G : Type} {opn : S → Option A}
    {entry : A → S → W → T.Wt → Nat → G} {val : E → G} {J : Nat → Nat → Prop}
    (h : MaskTieBook T b p ps.length opn entry val J) :
    MaskTie T b p ps opn entry val (spentOf ps) J := by
  intro k s m En hT a c ha hc ds j hj
  rw [spentOf_row Bk _ _ p ps 0 c hc] at hj ⊢
  exact h k s m En hT a ha ds j hj

/-- **The honest side's cell is the witness's reader's.** mine: the honest side's cell, of the
    input.
seen: the cell that an item's sentence reads, off what is open, the state, the input and the
    witness.
In: at which (matrix, row, column). A premise's form. -/
def CellsTie (T : Thread Bk S Cl V W X Pb) (b : Nat) {A G : Type} (opn : S → Option A)
    (mine : W → Nat → Nat → Nat → G) (seen : A → S → W → T.Wt → Nat → Nat → Nat → G)
    (In : Nat → Nat → Nat → Prop) : Prop :=
  ∀ k s m En, Thr T b k s m En → ∀ a, opn s = some a → ∀ ds i r c, In i r c →
    mine m.st.input i r c = seen a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) i r c

end ProofFile.Honest

#print axioms ProofFile.Honest.maskTie_of_book
