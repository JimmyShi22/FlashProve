-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Shares.lean: the two hypotheses that are proved item by item
(`Exchange`, `RidesPast`: Honest/Thread/Pays.lean), split into one form for each item; and the lemma
for an item that is owed again. `Exchange T b` is one condition over all items that the
sub-protocol's row owes; each item is proved by whoever defines what it says, and at some rows that
is another author than the sub-protocol's: so the form for one item needs a definition of its own.
An item that is open before a sub-protocol and that its row owes after it (the table's "ctx": a pin,
a constraint) is owed again because the sub-protocol may change what the item reads: its form of
`Exchange` follows as `RidesPast` does: from the item before and the sub-protocol's clause of
`keeps`. Definitions, meant as hypotheses; and conditional lemmas on them. General in the `Thread`:
no kind is named.

  1  `ExchangeAt`, `exchange_iff`   `Exchange` at one item; the hypothesis holds exactly if it holds
     at each item that the row owes
  2  `RidesPastAt`, `ridesPast_of`   `RidesPast` at one item; the hypothesis from its forms at the
     items
  3  `exchangeAt_again`   an item owed again: `ExchangeAt` from `RidesPastAt`

Limits.
  * It is not proved that any of these forms can be met.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 `Exchange` at one item -/

/-- **`Exchange` at one item**: the definition of `Exchange` with the one item in the place of all
that the row owes. It is a definition, meant as a hypothesis. -/
def ExchangeAt (b : Nat) (i : T.ι) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items [i] k s' y.2 (E.add y.1)

theorem exchange_iff {b : Nat} : Exchange T b ↔ ∀ i ∈ (T.row b).owes, ExchangeAt T b i := by
  constructor
  · intro h i hi blk hblk k s m E ds y cols s' hA hd hS ds' j hj
    obtain rfl := List.mem_singleton.1 hj
    exact h blk hblk k s m E ds y cols s' hA hd hS ds' j hi
  · intro h blk hblk k s m E ds y cols s' hA hd hS ds' i hi
    exact h i hi blk hblk k s m E ds y cols s' hA hd hS ds' i (List.mem_singleton.2 rfl)

/-! ## 2 `RidesPast` at one item -/

/-- **`RidesPast` at one item**: if the item holds of a witness before the sub-protocol, it holds of
it after, at every state that the sub-protocol's clause of `keeps` allows, whatever rounds are
produced. It is a definition, meant as a hypothesis. -/
def RidesPastAt (b : Nat) (i : T.ι) : Prop :=
  ∀ k s m E s' ps v, Thr T b k s m E → T.keeps b s s' →
    T.means m.st.input i (T.seat k m s) (T.strs E) v →
    T.means m.st.input i (T.seat k m s') (T.strs (E.add ps)) v

theorem ridesPast_of {b : Nat}
    (h : ∀ i ∈ T.opened b, i ∉ (T.row b).shuts → i ∉ (T.row b).owes → RidesPastAt T b i) :
    RidesPast T b :=
  fun k s m E s' ps i v hA hK h1 h2 h3 h0 => h i h1 h2 h3 k s m E s' ps v hA hK h0

/-! ## 3 An item owed again -/

/-- **An item that is open before and owed after**: `ExchangeAt` follows from `RidesPastAt` and the
sub-protocol's `Behind` (for `keeps`). A conditional lemma on this folder's own definitions. It is
none of the library's goals. -/
theorem exchangeAt_again {b : Nat} {i : T.ι} (hi : i ∈ T.opened b) (hB : Behind T b)
    (hR : RidesPastAt T b i) : ExchangeAt T b i := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  obtain ⟨-, -, hK⟩ := hB blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨-, hF0, -, hI0, -, -, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  have es : T.seat k y.2 s' = T.seat k m s' := by
    unfold Thread.seat
    rw [ei, eh, List.take_append_of_le_length hfr]
  have h0 := hI0 (ds ++ ds') j hi
  have h3 := hR k s m E s' y.1 _ hA hK h0
  show T.means y.2.st.input j (T.seat k y.2 s') (T.strs (E.add y.1))
    (T.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [es, ei, eh, List.append_assoc]
  exact h3

end ProofFile.Honest

#print axioms ProofFile.Honest.exchange_iff
#print axioms ProofFile.Honest.ridesPast_of
#print axioms ProofFile.Honest.exchangeAt_again
