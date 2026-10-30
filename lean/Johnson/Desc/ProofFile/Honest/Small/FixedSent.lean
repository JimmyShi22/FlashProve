-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/FixedSent.lean: the fourth clause of `Thread.fits`, the
Bool-valued test on the fields of a `Thread` (Honest/Thread/Thr.lean), holds at one value of the
field `fixed`: the value that counts, for one of the chain's own trees, the challenges before the
chain and those before the round that sends the tree. The clause asks, for each b up to n and each
source σ in `T.hand b` (the trees that are taken over and the own trees that the first b
sub-protocols state), that `T.fixed σ` is at most `T.front + roundsTo T.bs b`: the number of the
rounds before the chain plus that of the rounds of the first b sub-protocols. A round has one entry
in the list of challenges, and `Thread.Fit b` (Thr.lean) asks that just as many were heard. General
in the `Thread`: no kind of sub-protocol and no description is named.

  `hand_fixed`: the main statement: for every b and every σ in `T.hand b`,
    `T.fixed σ ≤ T.front + roundsTo T.bs b`
  `hand_fixed_below`: the same, with h4' asked only at the numbers of the oracle messages that the
    chain's sub-protocols state; `hand_fixed` is a call of it
  `rootsSum l`: a definition: the sum of the entries' `roots` over a list l of rounds
  `sentIn l j`: a definition: the number, from 0, of the round of l that sends the tree number j
    (`sendRound`, Johnson/Desc/Block.lean); 0 where no round sends it
  `sentIn_le`: `sentIn l j` is at most the length of l
  `sender_none`, `sentIn_beyond`: where j is not below `rootsSum l`, no round sends the tree number
    j, and `sentIn l j` is 0
  `sentIn_front`: where j is below `rootsSum l₁`, `sentIn (l₁ ++ l₂) j` is at most the length of l₁
  `sender_below`: a number that `sendRound l j` returns is below the length of l
  `sender_found`: where j is below `rootsSum l`, `sendRound l j` returns a number
  `sender_front`: where j is below `rootsSum l₁`, `sendRound (l₁ ++ l₂) j` is `sendRound l₁ j`
  `Listed x`: a definition: the sub-protocol x has one list of oracle messages for each round, with
    one message for each root
  `lists_of_shaped`: a sub-protocol that passes `Block.shaped` (Johnson/Desc/Block.lean), a clause
    of the description's test on the plan, is `Listed`
  `trees_roots`: sub-protocols that are `Listed` state as many oracle messages as the `rootsSum` of
    their rounds
  `treesTo_roots`: the same for the first b sub-protocols: `treesTo bs b = rootsSum (declsTo bs b)`
  `treesTo_le_all`: `treesTo bs b ≤ treesTo bs bs.length`, at every b
  `decls_split`: the rounds of bs are `declsTo bs b`, followed by the rounds of the sub-protocols
    after the first b
  `same_symm`: `Table.same` (Honest/Thread/Thr.lean) is symmetric
  `rootsSum_cons`, `rootsSum_append`, `map_of_zip`: small facts on lists

By what. `Thread.hand`, `Thread.front`, `declsTo`, `roundsTo` and `treesTo` are definitions of
Honest/Thread/Thr.lean; `sendRound` and `Block.shaped` are definitions of Johnson/Desc/Block.lean.
No lemma of another file of this library is called. In `hand_fixed` a tree that is taken over is
bounded by h4. An own tree j in `T.hand b` is below `treesTo T.bs b`, which is
`rootsSum (declsTo T.bs b)` (`treesTo_roots`): it is sent in a round of the first b sub-protocols,
and `decls_split` and `sentIn_front` bound its `sentIn` by `roundsTo T.bs b`. Why the value has the
number of the sending round and not one more: `play` (Honest/Frame.lean) makes a round's message by
`Step.tell` at the state before that round's challenge is heard; `Step.hear` comes after it. This is
the reason for the choice; no statement here mentions `play` or `Step.tell`.

Hypotheses of `hand_fixed`. h2: every sub-protocol of `T.bs` is `Listed`. h4: at every σ in
`T.taken`, `T.fixed σ` is at most `T.front`. h4': at every j, `T.fixed (.own j)` is `T.front` plus
`sentIn` of all the chain's rounds, `T.bs.flatMap (·.rounds)`, at j. `hand_fixed_below` asks h4' at
j below `treesTo T.bs T.bs.length` alone: beyond the chain's last tree `sentIn` is 0
(`sentIn_beyond`), so h4' at every j says there that `T.fixed (.own j)` is `T.front`, which a
`Thread` that counts all the chain's rounds there does not meet.

Limits. The statements compare numbers. No tree's table is read: that a tree's table no longer
changes after the number of challenges that `fixed` gives is not shown. For a tree that is taken
over the bound is the hypothesis h4: nothing is proved of it. The conclusion of `hand_fixed` is the
proposition that the fourth clause decides, at every b; `Thread.fits` itself occurs in no statement
here. `sentIn` is 0 both where the round number 0 sends the tree and where no round sends it.
`Step.tell` has an argument `back` of type `Option Fmt.RoundView`, a stored run's round, and `Fmt.RoundView` has a
field `drawn`; it reads the field `vals` of it alone, and only where the step has no move.
`lists_of_shaped` goes one way, and of `Block.shaped` it uses the clauses on the lengths alone. No
`Thread` is shown here to meet the hypotheses together. No property of a protocol is stated: nothing
on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block sendRound)

/-! ## 1 The round that sends a tree -/

/-- The sum of the entries' `roots` over a list of rounds. -/
def rootsSum (l : List Fmt.DeclaredRound) : Nat := (l.map (·.entry.roots)).sum

theorem rootsSum_cons (r : Fmt.DeclaredRound) (l : List Fmt.DeclaredRound) :
    rootsSum (r :: l) = r.entry.roots + rootsSum l := by
  unfold rootsSum
  rw [List.map_cons, List.sum_cons]

theorem rootsSum_append (l₁ l₂ : List Fmt.DeclaredRound) :
    rootsSum (l₁ ++ l₂) = rootsSum l₁ + rootsSum l₂ := by
  unfold rootsSum
  rw [List.map_append, List.sum_append]

theorem sender_below : ∀ (l : List Fmt.DeclaredRound) (j i : Nat), sendRound l j = some i → i < l.length
  | [], _, _, h => by cases h
  | r :: l, j, i, h => by
    unfold sendRound at h
    by_cases hj : j < r.entry.roots
    · rw [if_pos hj] at h
      cases h
      exact Nat.succ_pos _
    · rw [if_neg hj] at h
      obtain ⟨i', h', rfl⟩ := Option.map_eq_some_iff.1 h
      exact Nat.succ_lt_succ (sender_below l _ _ h')

theorem sender_found : ∀ (l : List Fmt.DeclaredRound) (j : Nat), j < rootsSum l →
    ∃ i, sendRound l j = some i
  | [], _, h => by cases h
  | r :: l, j, h => by
    unfold sendRound
    by_cases hj : j < r.entry.roots
    · exact ⟨0, if_pos hj⟩
    · rw [if_neg hj]
      rw [rootsSum_cons] at h
      obtain ⟨i, hi⟩ := sender_found l (j - r.entry.roots) (by omega)
      exact ⟨i + 1, by rw [hi]; rfl⟩

theorem sender_front : ∀ (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat), j < rootsSum l₁ →
    sendRound (l₁ ++ l₂) j = sendRound l₁ j
  | [], _, _, h => by cases h
  | r :: l₁, l₂, j, h => by
    rw [List.cons_append]
    unfold sendRound
    by_cases hj : j < r.entry.roots
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj]
      rw [rootsSum_cons] at h
      rw [sender_front l₁ l₂ (j - r.entry.roots) (by omega)]

/-- No round sends a tree whose number is not below `rootsSum l`. -/
theorem sender_none : ∀ (l : List Fmt.DeclaredRound) (j : Nat), rootsSum l ≤ j → sendRound l j = none
  | [], _, _ => rfl
  | r :: l, j, h => by
    rw [rootsSum_cons] at h
    unfold sendRound
    rw [if_neg (by omega), sender_none l (j - r.entry.roots) (by omega)]
    rfl

/-- The number, from 0, of the round of l that sends the tree number j; 0 where no round does. -/
def sentIn (l : List Fmt.DeclaredRound) (j : Nat) : Nat := (sendRound l j).getD 0

/-- So `sentIn` is 0 there. This is why the statements `…_below` ask their equations below the
chain's last tree alone: asked at every j, `T.fixed (.own j) = T.front + sentIn … j` says beyond the
last tree that `T.fixed (.own j)` is `T.front`, and a `Thread` whose field `fixed` counts all the
chain's rounds there (`Script.ofLots`, Honest/Thread/ScriptLots.lean) does not meet it, unless the
chain has no round. -/
theorem sentIn_beyond (l : List Fmt.DeclaredRound) (j : Nat) (h : rootsSum l ≤ j) : sentIn l j = 0 := by
  unfold sentIn
  rw [sender_none l j h]
  rfl

theorem sentIn_le (l : List Fmt.DeclaredRound) (j : Nat) : sentIn l j ≤ l.length := by
  unfold sentIn
  cases h : sendRound l j with
  | none => exact Nat.zero_le _
  | some i => exact Nat.le_of_lt (sender_below l j i h)

/-- Where j is below `rootsSum l₁`, `sentIn (l₁ ++ l₂) j` is at most the length of l₁: `sendRound`
finds the sending round in l₁ (`sender_front`). -/
theorem sentIn_front (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat) (h : j < rootsSum l₁) :
    sentIn (l₁ ++ l₂) j ≤ l₁.length := by
  unfold sentIn
  rw [sender_front l₁ l₂ j h]
  exact sentIn_le l₁ j

section Lists
variable {S Cl : Type}

/-- The sub-protocol x has one list of oracle messages for each round, with one message for each
root. -/
def Listed (x : Block S Cl) : Prop :=
  x.rounds.length = x.oracles.length ∧ x.rounds.map (·.entry.roots) = x.oracles.map (·.length)

theorem map_of_zip {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (a : List α) (b : List β),
    a.length = b.length → (∀ x ∈ a.zip b, g x.2 = f x.1) → a.map f = b.map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | x :: a, y :: b, h, hz => by
    rw [List.map_cons, List.map_cons, (hz (x, y) List.mem_cons_self : g y = f x),
      map_of_zip f g a b (Nat.succ.inj h) fun z hz' => hz z (List.mem_cons_of_mem _ hz')]

/-- A sub-protocol that passes the test `Block.shaped` (Johnson/Desc/Block.lean) is `Listed`. -/
theorem lists_of_shaped {x : Block S Cl} (h : x.shaped = true) : Listed x := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1.symm, map_of_zip _ _ _ _ h.1.symm fun z hz => ?_⟩
  have hz' := h.2 z hz
  rw [Bool.and_eq_true, beq_iff_eq] at hz'
  exact hz'.1

theorem trees_roots : ∀ l : List (Block S Cl), (∀ x ∈ l, Listed x) →
    (l.flatMap fun x => x.oracles.flatMap id).length = rootsSum (l.flatMap (·.rounds))
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, rootsSum_append,
      trees_roots l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    congr 1
    rw [List.length_flatMap]
    unfold rootsSum
    rw [(h x List.mem_cons_self).2]
    rfl

/-- Where every sub-protocol of bs is `Listed`, the first b state as many oracle messages as the
`rootsSum` of their rounds. -/
theorem treesTo_roots (bs : List (Block S Cl)) (h : ∀ x ∈ bs, Listed x) (b : Nat) :
    treesTo bs b = rootsSum (declsTo bs b) :=
  trees_roots _ fun x hx => h x (List.mem_of_mem_take hx)

/-- The first b sub-protocols state at most as many oracle messages as the whole list, at every b,
also beyond the list's length. -/
theorem treesTo_le_all (bs : List (Block S Cl)) (b : Nat) :
    treesTo bs b ≤ treesTo bs bs.length := by
  have e : treesTo bs bs.length =
      treesTo bs b + ((bs.drop b).flatMap fun x => x.oracles.flatMap id).length := by
    unfold treesTo
    rw [List.take_length, ← List.length_append, ← List.flatMap_append, List.take_append_drop]
  rw [e]
  exact Nat.le_add_right _ _

theorem decls_split (bs : List (Block S Cl)) (b : Nat) :
    bs.flatMap (·.rounds) = declsTo bs b ++ (bs.drop b).flatMap (·.rounds) := by
  unfold declsTo
  rw [← List.flatMap_append, List.take_append_drop]

end Lists

/-- `Table.same` (Honest/Thread/Thr.lean) is symmetric. -/
theorem same_symm {t u : Table} (h : t.same u = true) : u.same t = true := by
  unfold Table.same at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 := eq_of_beq h1
  refine ⟨⟨beq_iff_eq.2 e1.symm, beq_iff_eq.2 (eq_of_beq h2).symm⟩, ?_⟩
  rw [← e1]
  rw [List.all_eq_true] at h3 ⊢
  exact fun x hx => beq_iff_eq.2 (eq_of_beq (h3 x hx)).symm

/-! ## 2 The fourth clause of `Thread.fits` -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **`hand_fixed`, with h4' asked below the chain's last tree alone.** Every own tree in
`T.hand b` is below `treesTo T.bs b`, and so below `treesTo T.bs T.bs.length`
(`treesTo_le_all`). -/
theorem hand_fixed_below (h2 : ∀ x ∈ T.bs, Listed x) (h4 : ∀ σ ∈ T.taken, T.fixed σ ≤ T.front)
    (h4' : ∀ j, j < treesTo T.bs T.bs.length →
      T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j) (b : Nat) :
    ∀ σ ∈ T.hand b, T.fixed σ ≤ T.front + roundsTo T.bs b := by
  intro σ hσ
  unfold Thread.hand at hσ
  rcases List.mem_append.1 hσ with hσ | hσ
  · exact Nat.le_trans (h4 σ hσ) (Nat.le_add_right _ _)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hσ
    rw [h4' j (Nat.lt_of_lt_of_le (List.mem_range.1 hj) (treesTo_le_all T.bs b)),
      decls_split T.bs b]
    refine Nat.add_le_add_left (sentIn_front _ _ j ?_) _
    rw [← treesTo_roots T.bs h2 b]
    exact List.mem_range.1 hj

/-- **At every tree in `T.hand b`, `T.fixed` is at most `T.front + roundsTo T.bs b`.** h2: every
sub-protocol is `Listed`. h4: at a tree that is taken over, `T.fixed` is at most `T.front`. h4': at
an own tree, `T.fixed` is `T.front` plus the number of the round that sends it (`sentIn`). -/
theorem hand_fixed (h2 : ∀ x ∈ T.bs, Listed x) (h4 : ∀ σ ∈ T.taken, T.fixed σ ≤ T.front)
    (h4' : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j) (b : Nat) :
    ∀ σ ∈ T.hand b, T.fixed σ ≤ T.front + roundsTo T.bs b :=
  hand_fixed_below T h2 h4 (fun j _ => h4' j) b

end

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.sentIn_front
#print axioms ProofFile.Honest.Small.lists_of_shaped
#print axioms ProofFile.Honest.Small.treesTo_roots
#print axioms ProofFile.Honest.Small.hand_fixed
#print axioms ProofFile.Honest.Small.sender_none
#print axioms ProofFile.Honest.Small.sentIn_beyond
#print axioms ProofFile.Honest.Small.treesTo_le_all
#print axioms ProofFile.Honest.Small.hand_fixed_below
#print axioms ProofFile.Honest.Small.same_symm
#print axioms ProofFile.Honest.Small.rootsSum
#print axioms ProofFile.Honest.Small.rootsSum_cons
#print axioms ProofFile.Honest.Small.rootsSum_append
#print axioms ProofFile.Honest.Small.sender_below
#print axioms ProofFile.Honest.Small.sender_found
#print axioms ProofFile.Honest.Small.sender_front
#print axioms ProofFile.Honest.Small.sentIn
#print axioms ProofFile.Honest.Small.sentIn_le
#print axioms ProofFile.Honest.Small.Listed
#print axioms ProofFile.Honest.Small.map_of_zip
#print axioms ProofFile.Honest.Small.trees_roots
#print axioms ProofFile.Honest.Small.decls_split
