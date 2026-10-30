-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PubPAtHead.lean

What the open public items say beside their Boolean tests, at the first chain's letters.

The clause `Form` of the invariant at a border of the first chain has four parts (see FormXK.lean).
The fourth part asks, for every public item that is open at the border, a sentence `pubP` about the
verifier's state. This file shows that, at the letters `lettersHead`, only two sorts of item have a
sentence that reads the state: `left m` and `leftOn m`. The sentence of `hasRow m` is `True`. The
sentence of any other item is a closed test on the item itself (`saysNone` names a part), and Lean's
kernel evaluates that test to true for every item that is open at any border of the full-size list
of places.

So the fourth part of the form at a border follows from the sentences of the items `left m` and
`leftOn m` that are open there, and from nothing else.

  `head_pubP_left`, `head_pubP_leftOn`, `head_pubP_hasRow`, `head_pubP_said`
                          the sentence of each sort of item, by unfolding
  `said_every_set`        the closed test, at every open public set of the list (kernel evaluation)
  `said_every_border`     so the library's test accepts at every border
  `saidB_can_refuse`      control: the test on an item refuses an item that the table does not name
  `said_needs_left`       control: with `left` and `leftOn` not set apart the evaluation is false
  `said_without_hasRow`   the exception for `hasRow` is not used on this list
  `said_not_empty`        control: some set has an item
  `head_pubP_of_left`     the fourth part of the form from the two sorts' sentences

The observation that `hasRow` says nothing at these letters, and that the other items' sentences
read no state, comes from the lemmas for the kind K1. The tests
`saidB` and `saidSetB` and the lemma `said_of` are the library's
(Johnson/Desc/K1/Law/SaidAtFifty.lean), where they are evaluated at fifty borders of another list.

Limits. Full size only, and only under the library's hypothesis `AtMgA` at the format's second
hash function, which is a premise. Nothing here shows the sentences of `left m` or `leftOn m`. This is not
one of the library's goals, and it claims no property of the protocol. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.K1.Law.SaidAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (flatPlacesOf pubSets saysNone)
open VerifiableInference.Desc.K1 (saidB saidSetB said_of)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- In every open public set of the full-size list of places, every item is `left`, `leftOn`,
`hasRow`, or an item for which `saysNone` names a part. The list of sets is evaluated once. -/
theorem said_every_set :
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true)).all fun Q =>
      Q.all saidB) = true := by
  decide +kernel

/-- So the library's test on the open public set accepts at every border. -/
theorem said_every_border (c : Nat) :
    saidSetB moreAll linksFull (flatPlacesOf linksFull true) c saidB = true := by
  unfold saidSetB
  cases hQ : (pubSets moreAll linksFull (flatPlacesOf linksFull true))[c]? with
  | none => rfl
  | some Q => exact List.all_eq_true.1 said_every_set Q (List.mem_of_getElem? hQ)

/-- Control: the test on an item is not constant: it refuses an item that the table does not
name. -/
theorem saidB_can_refuse : saidB (.more none "a name that the table does not have") = false := by
  decide +kernel

/-- Control: on this very list the test can refuse: with `saysNone` alone, the items `left` and
`leftOn` not set apart, the evaluation over all sets is false. -/
theorem said_needs_left :
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true)).all fun Q =>
      Q.all fun q => (saysNone q).isSome) = false := by
  decide +kernel

/-- The exception for `hasRow` is not used on this list: with `left` and `leftOn` set apart and
`saysNone` for the rest, the evaluation over all sets is still true. -/
theorem said_without_hasRow :
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true)).all fun Q =>
      Q.all fun q => VerifiableInference.Desc.K1.leftish q || (saysNone q).isSome) = true := by
  decide +kernel

/-- Control: the evaluation is not empty: some set has an item. -/
theorem said_not_empty :
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true)).any fun Q => !Q.isEmpty) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The sentence of `left m`. -/
theorem head_pubP_left (m : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP (.left m) a =
      VerifiableInference.OnPublicFiles.k3LeftItemAt (P5J.At.X Zp) m a.2 := rfl

/-- The sentence of `leftOn m`. -/
theorem head_pubP_leftOn (m : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP (.leftOn m) a =
      VerifiableInference.OnPublicFiles.k3LeftOnItemAt (P5J.At.X Zp) m a.2 := rfl

/-- The sentence of `hasRow m` holds outright. -/
theorem head_pubP_hasRow (m : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP (.hasRow m) a := by
  rw [head_pubP_all]
  exact trivial

/-- Where `saysNone` names a part, the item's sentence holds at every state. -/
theorem head_pubP_said (q : VerifiableInference.Desc.First.Pub) (a : ProofFile.InstPub × TS)
    (hq : (saysNone q).isSome = true) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP q a :=
  VerifiableInference.Desc.Sound.mgAll_pubP_said h.𝔇 q a hq

/-- The fourth part of the form at border c, from the sentences of the open items `left m` and
`leftOn m` alone. -/
theorem head_pubP_of_left (c : Nat) (a : ProofFile.InstPub × TS)
    (hl : ∀ m, VerifiableInference.Desc.First.Pub.left m ∈
        P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c →
      VerifiableInference.OnPublicFiles.k3LeftItemAt (P5J.At.X Zp) m a.2)
    (ho : ∀ m, VerifiableInference.Desc.First.Pub.leftOn m ∈
        P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c →
      VerifiableInference.OnPublicFiles.k3LeftOnItemAt (P5J.At.X Zp) m a.2) :
    ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP q a := by
  intro q hq
  have hs := said_every_border c
  have hq' : q ∈ (pubSets moreAll linksFull (flatPlacesOf linksFull true))[c]?.getD [] := by
    have e := head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    unfold P1K2.pubAt at hq
    rw [e] at hq
    exact hq
  by_cases h1 : ∃ m, q = .left m
  · obtain ⟨m, rfl⟩ := h1
    exact hl m hq
  by_cases h2 : ∃ m, q = .leftOn m
  · obtain ⟨m, rfl⟩ := h2
    exact ho m hq
  rcases said_of hs q hq' (fun m e => h1 ⟨m, e⟩) (fun m e => h2 ⟨m, e⟩) with hp | hp
  · cases q with
    | hasRow m => exact head_pubP_hasRow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m a
    | _ => cases hp
  · exact head_pubP_said h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w q a hp

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.said_every_set
#print axioms ProofFile.Honest.FirstThread.said_every_border
#print axioms ProofFile.Honest.FirstThread.saidB_can_refuse
#print axioms ProofFile.Honest.FirstThread.said_needs_left
#print axioms ProofFile.Honest.FirstThread.said_without_hasRow
#print axioms ProofFile.Honest.FirstThread.said_not_empty
#print axioms ProofFile.Honest.FirstThread.head_pubP_left
#print axioms ProofFile.Honest.FirstThread.head_pubP_leftOn
#print axioms ProofFile.Honest.FirstThread.head_pubP_hasRow
#print axioms ProofFile.Honest.FirstThread.head_pubP_said
#print axioms ProofFile.Honest.FirstThread.head_pubP_of_left
