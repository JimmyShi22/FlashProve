-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ExchangeOf.lean: a share of the debt `Exchange`
(Johnson/Desc/ProofFile/Honest/Thread/Pays.lean): general in the thread; no kind is named in it. One
definition, and statements with their proofs.

`Exchange T b` asks: from the thread in front of the member number b and the member's own step,
accepted: every item that the member's forward row owes holds behind. The items of one row can be
shown apart. `ExchangeOf T b O` is the same sentence for a list O of items.
Words of the frame for the honest side, which are explained in the heads of Honest/Thread/Thr.lean,
Pays.lean and First.lean: a chain's thread (the sentence that stands at each border between two
members of the chain's flat list); its parameters (the structure `Letters`); a debt (a statement
that is owed at a member); the forward row of a member (which items it asks, owes and shuts); the
Script (the functions from which the witness is made).
Main names:
  `ExchangeOf T b O`: from the thread in front and the member's accepted step, the items of O hold
    behind.
  `exchangeOf_all`: `Exchange` is `ExchangeOf` at all that the row owes.
  `exchangeOf_mem`: a list's share is the shares of its members, one by one: so the order and
    repeats do not matter.
  `exchangeOf_append`: a list's share is its two parts' shares.

What is not claimed. `ExchangeOf` at any thread. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13

variable {S' Cl' V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A share of `Exchange`**: from the thread in front and the member's accepted step, the items of
the list O hold behind. -/
def ExchangeOf (T : Thread Bk S' Cl' V W X Pb) (b : Nat) (O : List T.ι) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m En ds y cols s', Thr T b k s m En →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m En ds y cols s' →
    T.Items O k s' y.2 (En.add y.1)

/-- `Exchange` is `ExchangeOf` at all that the row owes. -/
theorem exchangeOf_all (T : Thread Bk S' Cl' V W X Pb) (b : Nat) :
    Exchange T b ↔ ExchangeOf T b (T.row b).owes := Iff.rfl

/-- A list's share is the shares of its members, one by one. -/
theorem exchangeOf_mem (T : Thread Bk S' Cl' V W X Pb) (b : Nat) (O : List T.ι) :
    ExchangeOf T b O ↔ ∀ i ∈ O, ExchangeOf T b [i] := by
  constructor
  · intro h i hi blk hb k s m En ds y cols s' hT hd hS ds' j hj
    obtain rfl := List.mem_singleton.1 hj
    exact h blk hb k s m En ds y cols s' hT hd hS ds' j hi
  · intro h blk hb k s m En ds y cols s' hT hd hS ds' i hi
    exact h i hi blk hb k s m En ds y cols s' hT hd hS ds' i (List.mem_singleton.2 rfl)

/-- A list's share is its two parts' shares. -/
theorem exchangeOf_append (T : Thread Bk S' Cl' V W X Pb) (b : Nat) (O₁ O₂ : List T.ι) :
    ExchangeOf T b (O₁ ++ O₂) ↔ ExchangeOf T b O₁ ∧ ExchangeOf T b O₂ := by
  rw [exchangeOf_mem T b (O₁ ++ O₂), exchangeOf_mem T b O₁, exchangeOf_mem T b O₂]
  constructor
  · intro h
    exact ⟨fun i hi => h i (List.mem_append_left _ hi),
      fun i hi => h i (List.mem_append_right _ hi)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact h1 i hi
    · exact h2 i hi

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.exchangeOf_all
#print axioms ProofFile.Honest.K13.exchangeOf_mem
#print axioms ProofFile.Honest.K13.exchangeOf_append
