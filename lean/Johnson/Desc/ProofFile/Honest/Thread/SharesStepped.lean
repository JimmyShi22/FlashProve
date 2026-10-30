-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SharesStepped.lean: two lemmas that prove `ExchangeAtS`
(Honest/Thread/SharesS.lean) for an item that is open before a sub-protocol, that is, in the list
`T.opened b` of items that the invariant asserts there, and has to hold again after it.
`ExchangeAtS T Said b i` is the part of the hypothesis `ExchangeS` (Honest/Thread/PaysS.lean) that
concerns the one item `i`. It says: whenever the invariant with its extra condition (`ThrS`) holds
at border `b`, the position in the chain before sub-protocol number `b`, the challenges fit that
sub-protocol's declared rounds, and the prover's side has played and the sub-protocol has made an
accepting step from state `s` to state `s'` (`Thread.Stepped`), the item holds at `s'`, at the
witness of every continuation of the challenges. The file contains no definition. Both lemmas hold
for every `Thread`, the structure of the invariant's parameters, and every condition `Said`.

How it relates to SharesS.lean. `exchangeAtS_again` there proves the same conclusion from `hi`, that
the item is open at the border, and two more hypotheses. One is `BehindS`, of which it uses the
third clause alone, `T.keeps b s s'`. The other is `RidesPastAtS`, which says that the item's
meaning is preserved from `s` to `s'` at every pair of states with `T.keeps b s s'`. The first lemma
here also asks `hi`. It asks that the meaning is preserved only at pairs at which the sub-protocol
has stepped, gives the caller the step itself, and does not ask for `BehindS`. So a caller who can
derive what the item needs from the step needs neither `BehindS` nor any fact about `T.keeps`. The
second lemma proves in Lean that the first is at least as strong as `exchangeAtS_again`.

  1  `exchangeAtS_stepped`   an open item whose meaning is preserved across every pair of states at
     which the sub-protocol has stepped holds again after the step
  2  `exchangeAtS_again'`   the statement of `exchangeAtS_again`, proved from the first lemma

Where this comes from. The proof of `exchangeAtS_stepped` is the proof of `exchangeAtS_again` with
two lines changed: the line that opens `BehindS` is removed, and `hR` is called with the step where
`T.keeps b s s'` was. It was first written for the sub-protocol of the output head's own rounds,
where what an accepting step keeps of the state is proved from the step.

Limits.
  * Both lemmas are implications. They prove `ExchangeAtS` for no particular `Thread`, border or
    item.
  * `ExchangeAtS`, `ExchangeS`, `BehindS` and `RidesPastAtS` are definitions, meant as hypotheses.
    None is one of the library's goals.
  * It is not proved in this file that the invariant holds in any run, or that any sub-protocol
    accepts.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **An open item whose meaning is preserved across every stepped pair holds again after the
step.** `hi`: the item `i` is open at border `b`, that is, it is in `T.opened b`, the list of items
that the invariant asserts there. `hR`: wherever the invariant `ThrS` holds at `b`, the challenges
`ds` fit the declared rounds and the sub-protocol has stepped from `s` to `s'`, the item's meaning
at `s`, at any witness `v`, gives its meaning at `s'` with the played rounds `y.1` added to `E`. The
conclusion is the part of `ExchangeS` that concerns the item. `BehindS` is not a hypothesis. -/
theorem exchangeAtS_stepped {b : Nat} {i : T.ι} (hi : i ∈ T.opened b)
    (hR : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s' v, ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.means m.st.input i (T.seat k m s) (T.strs E) v →
      T.means m.st.input i (T.seat k m s') (T.strs (E.add y.1)) v) :
    ExchangeAtS T Said b i := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  have hA' := hA.1
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
  have h3 := hR blk hblk k s m E ds y cols s' _ hA hd hS h0
  show T.means y.2.st.input j (T.seat k y.2 s') (T.strs (E.add y.1))
    (T.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [es, ei, eh, List.append_assoc]
  exact h3

/-- The statement of `exchangeAtS_again` (Honest/Thread/SharesS.lean), proved from
`exchangeAtS_stepped`: at a stepped pair `BehindS` gives `T.keeps b s s'`, and `RidesPastAtS` then
preserves the item's meaning. -/
theorem exchangeAtS_again' {b : Nat} {i : T.ι} (hi : i ∈ T.opened b) (hB : BehindS T Said b)
    (hR : RidesPastAtS T Said b i) : ExchangeAtS T Said b i :=
  exchangeAtS_stepped T Said hi fun blk hblk k s m E ds y cols s' v hA hd hS h0 =>
    hR k s m E s' y.1 v hA (hB blk hblk k s m E ds y cols s' hA hd hS).2.2 h0

end ProofFile.Honest

#print axioms ProofFile.Honest.exchangeAtS_stepped
#print axioms ProofFile.Honest.exchangeAtS_again'
