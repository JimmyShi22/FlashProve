-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/From.lean: one lemma for proving `ExchangeAtS` (Honest/Thread/SharesS.lean) of
an item that need not be open before a sub-protocol, from items that are open there. It holds for every `Thread` and
every `Said`. No definition.

The words. A `Thread` (Honest/Thread/Thr.lean) is the structure of parameters of one chain's invariant `Thr`. Border b
is the position in the chain before sub-protocol number b. An item is an entry of the chain's table of joints;
`T.means` gives the sentence that it stands for: a sentence on the run's input, what the chain was given, the
verifier's state, the available tables and a witness. The items of the list `T.opened b` are open at border b: the
invariant asserts them there, at the run's witness at every continuation of the challenges heard. The run's witness is
`T.wit` at the run's coins, its input and a list of challenges. `ThrS` (Honest/Thread/Said.lean) is the invariant
together with a second condition `Said`.

What `ExchangeAtS T Said b i` says. Wherever `ThrS` holds at border b, the challenges ds fit the declared rounds of
sub-protocol number b, and that sub-protocol has stepped from state s to state s' (`Thread.Stepped`,
Honest/Thread/Pays.lean: the prover's side has played its rounds, the columns read are filled, and the verifier's own
step has accepted), the item i holds at s', at the run's witness at every continuation of the challenges.

  `exchangeAtS_from`   Js is a list of items. hJ: each of them is open at border b. hR: at every such step and every
      continuation ds' of the challenges, the sentences of the items of Js at s give the sentence of i at s' with the
      played rounds added to the available tables, all at the run's witness at the challenges heard before the step,
      then ds, then ds'. The conclusion is `ExchangeAtS` at b and i

How it relates to `exchangeAtS_stepped` (Honest/Thread/SharesStepped.lean). That lemma carries one open item across
the step, and its premise speaks of any witness. This one derives an item from several open ones, and its premise
speaks of the run's witness alone: a weaker premise, so that a caller may use what ties that witness to the run. The
proof is that lemma's proof with two lines changed: the invariant's clause on the open items is read at each item of
Js, and the caller's premise is called with the continuation.

Limits. The premises are hJ and hR. The lemma is an implication: it proves `ExchangeAtS` for no particular `Thread`,
border or item. `ExchangeAtS` and `ThrS` are definitions, meant as hypotheses; where `ThrS` holds at no state of
border b, `ExchangeAtS` holds there for nothing. It is not shown that the invariant holds in any run or that any
sub-protocol accepts. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **`ExchangeAtS` holds at an item whose sentence after each step follows, at the run's witness, from the sentences
before the step of items that are open there.** -/
theorem exchangeAtS_from {b : Nat} {i : T.ι} (Js : List T.ι) (hJ : ∀ j ∈ Js, j ∈ T.opened b)
    (hR : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s' ds', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      (∀ j ∈ Js, T.means m.st.input j (T.seat k m s) (T.strs E)
        (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) →
      T.means m.st.input i (T.seat k m s') (T.strs (E.add y.1))
        (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) :
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
  have h3 := hR blk hblk k s m E ds y cols s' ds' hA hd hS
    fun j' hj' => hI0 (ds ++ ds') j' (hJ j' hj')
  show T.means y.2.st.input j (T.seat k y.2 s') (T.strs (E.add y.1))
    (T.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [es, ei, eh, List.append_assoc]
  exact h3

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.exchangeAtS_from
