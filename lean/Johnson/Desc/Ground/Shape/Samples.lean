-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Shape/Samples.lean: a Bool on a statement, `stSamplesB`: no tensor in a sample
row of the statement (`Oracle.sampleRows`, at each oracle message in `Statement.oracles`) has a
written-out factor (a `Tensor.denseVars` that is not empty). It is the second conjunct of the second
mark, `stPlainB` (Johnson/Desc/Ground/Shape/Marks.lean, where a mark is a Bool on a statement that
functions on a description's state are shown to keep), as a mark of its own. `stPlainB` says the
same of the open rows (`Group.rows`) too, and fails where an open row with such a factor is placed:
on the last chain of both files, the proof file and the key file. That is said in the comment at the
top of Marks.lean; no theorem there or here states it. No open row enters `stSamplesB`, so such a
row does not make it false; that it holds on that chain is not shown here. The file defines the
mark, proves what it gives, and proves that each function of Johnson/Desc/First/Base/Ground.lean
whose name ends in P keeps it: where the function, at a state d, returns a state d' (with or without
a further result) and the mark is true at `d.st`, it is true at `d'.st`. These theorems hold at
every type L in `DState L` and at all arguments.

  `stSamplesB`: a definition: the mark: `orcsPlainB` at the statement's oracle messages
  `orcsPlainB`: a definition: every sample row of every message of an array passes `rowPlainB`
    (Marks.lean): no tensor among the row's terms or in its whole coefficient vectors (`Row.forms`)
    has a written-out factor
  `samples_rows`: where the mark is true, every sample row of every message of the statement is a
    `PlainRow` (OnBytes/Slice/BlkPlain.lean)
  `samples_of_plain`: where `stPlainB` is true, `stSamplesB` is true
  `start_samples`: the mark is true at a statement without a message and without a group, at all
    codes
  `join_samples`, `addRow_samples`, `addRows_samples`, `adopt_samples`, `recv_samples`,
    `newGroup_samples`, `takeMask_samples`, `takeMasks_samples`, `closeLedger_samples`,
    `spend_samples`, `beginRun_samples`: `joinP`, `addRowP`, `addRowsP`, `adoptP`, `recvP`,
    `newGroupP`, `takeMaskP`, `takeMasksP`, `closeLedgerP`, `spendAsMaskP` and `beginRunP` keep the
    mark. No hypothesis on an argument: nothing has to be shown of a new open row
  `admit_samples`: `admitP` keeps the mark. Hypothesis: each new sample row passes `rowPlainB`
  `elsewhere_samples`: `elsewhereP` keeps the mark. Hypothesis: the mark is true at the other
    statement: at all its messages, not only at the one whose sample rows are copied
  `addRowsFrom_samples`, `takeMasksInto_samples`: the same for the recursions `addRowsFrom` and
    `takeMasksInto`, which `addRowsP` and `takeMasksP` call
  `orcs_iff`: `orcsPlainB` is true exactly where each sample row of each message passes `rowPlainB`
  `orcs_modify`: `orcsPlainB` is kept where one message is changed (`Array.modify`) by a function
    under which sample rows that all pass `rowPlainB` go to sample rows that all pass it
  `orcs_sent`: `stSent` (OnBytes/Slice/BlkSendRun.lean) keeps the mark: the messages that it appends
    have no sample row
  `orcs_shut`: `closeLedgers` (OnBytes/Slice/BlkBegin.lean) keeps the mark

By what. The mark reads only the statement's oracle messages. Each theorem on a function goes
through that function's definition. `addRow_samples` and `newGroup_samples` then close by the
hypothesis that the mark is true at `d.st`, since the messages are not changed; `adopt_samples` and
`recv_samples` by `orcs_sent`; `closeLedger_samples` and `beginRun_samples` by `orcs_shut`;
`join_samples`, `elsewhere_samples`, `takeMask_samples`, `spend_samples` and `admit_samples` by
`orcs_modify`; `addRows_samples` and `takeMasks_samples` by the theorems on the two recursions. From
Marks.lean: `mem_modify` (in `orcs_modify`), `plain_iff` (in `samples_of_plain`), `rowPlainB_iff`
(in `samples_rows` and `elsewhere_samples`), `rowPlainB_renamed` (in `elsewhere_samples`).

Limits. It is meant as a mark that the functions carry, as Marks.lean says of its two. It reads no
value: of a tensor only whether `denseVars` is empty. Where a function returns nothing, its theorem
is vacuous. Nothing is shown here of any description. No statement here names a kind, a chain or a
frame for an honest side. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.Ground.Shape.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-- Every sample row of each of these oracle messages passes `rowPlainB`: none of its tensors has a
written-out factor. -/
def orcsPlainB (A : Array OnBytes.Oracle) : Bool :=
  A.toList.all fun x => x.sampleRows.toList.all rowPlainB

/-- **The mark on sample rows**: every sample row of the statement passes `rowPlainB`. -/
def stSamplesB (S : Statement) : Bool := orcsPlainB S.oracles

theorem orcs_iff {A : Array OnBytes.Oracle} : orcsPlainB A = true ↔
    ∀ x ∈ A.toList, ∀ r ∈ x.sampleRows.toList, rowPlainB r = true := by
  unfold orcsPlainB
  simp only [List.all_eq_true]

theorem samples_of_plain {S : Statement} (h : stPlainB S = true) : stSamplesB S = true :=
  orcs_iff.2 (plain_iff.1 h).2

/-- Where the mark is true, every sample row of every oracle message of the statement is a
`PlainRow`. -/
theorem samples_rows {S : Statement} (h : stSamplesB S = true) {o : Nat} {x : OnBytes.Oracle}
    (hx : S.oracles[o]? = some x) : ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  intro r hr
  obtain ⟨ho, rfl⟩ := Array.getElem?_eq_some_iff.1 hx
  exact rowPlainB_iff.1 (orcs_iff.1 h _ (Array.getElem_mem_toList ho) r hr)

theorem start_samples (codes : Codes) :
    stSamplesB { codes := codes, oracles := #[], groups := #[] } = true := rfl

theorem orcs_modify {A : Array OnBytes.Oracle} (h : orcsPlainB A = true) (o : Nat)
    (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (∀ r ∈ x.sampleRows.toList, rowPlainB r = true) →
      ∀ r ∈ (f x).sampleRows.toList, rowPlainB r = true) : orcsPlainB (A.modify o f) = true := by
  refine orcs_iff.2 fun x hx => ?_
  rcases mem_modify hx with hx | ⟨x', hx', rfl⟩
  · exact orcs_iff.1 h x hx
  · exact hf x' (orcs_iff.1 h x' hx')

theorem orcs_sent {S : Statement} (h : stSamplesB S = true) (sent : Array OracleNotice) :
    stSamplesB (stSent S sent) = true := by
  refine orcs_iff.2 fun x hx => ?_
  have hx' : x ∈ (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle)).toList :=
    hx
  rw [Array.toList_append, Array.toList_map] at hx'
  rcases List.mem_append.1 hx' with hx' | hx'
  · exact orcs_iff.1 h x hx'
  · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx'
    intro r hr
    cases hr

theorem orcs_shut : ∀ (l : List Nat) (S : Statement), stSamplesB S = true →
    stSamplesB (closeLedgers S l) = true
  | [], _, h => h
  | o :: l, S, h => orcs_shut l _ (orcs_modify (A := S.oracles) h o _ fun _ x => x)

theorem join_samples (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d')
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact orcs_modify (A := d.st.oracles) hp o _ fun _ x => x
  · cases h

theorem addRow_samples (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold addRowP at h
  split at h
  · cases h
    exact hp
  · cases h

theorem addRowsFrom_samples (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → stSamplesB d.st = true → stSamplesB d'.st = true
  | [], d, d', h, hp => by
    cases h
    exact hp
  | r :: l, d, d', h, hp => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_samples g l e d' h (addRow_samples d e g r he hp)

theorem addRows_samples (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') (hp : stSamplesB d.st = true) :
    stSamplesB d'.st = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_samples g rows d d' h hp
  · cases h

theorem adopt_samples (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat) (h : adoptP d sent given = some (ids, d'))
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact orcs_sent hp sent
  · cases h

theorem recv_samples (first : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP first d sent = some (ids, d')) (hp : stSamplesB d.st = true) :
    stSamplesB d'.st = true := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact orcs_sent hp sent
  · cases h

theorem elsewhere_samples (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (hp : stSamplesB d.st = true)
    (ho : stSamplesB other = true) : stSamplesB d'.st = true := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    exact orcs_modify (A := d.st.oracles) hp mine _ fun _ _ r hr => by
      rw [Array.toList_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      rw [rowPlainB_renamed]
      exact rowPlainB_iff.2 (samples_rows ho hy r0 hr0)
  · cases h

theorem newGroup_samples (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) (hp : stSamplesB d.st = true) :
    stSamplesB d'.st = true := by
  unfold newGroupP at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hp
  · cases h

theorem takeMask_samples (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d'))
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact orcs_modify (A := d.st.oracles) hp o _ fun _ x => x
  · cases h

theorem takeMasksInto_samples (o : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') → stSamplesB d.st = true →
    stSamplesB d'.st = true
  | 0, d, d', acc, l, h, hp => by
    cases h
    exact hp
  | n + 1, d, d', acc, l, h, hp => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      exact takeMasksInto_samples o n e d' _ l h (takeMask_samples d e o i he hp)

theorem takeMasks_samples (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) (hp : stSamplesB d.st = true) :
    stSamplesB d'.st = true :=
  takeMasksInto_samples o count d d' #[] l h hp

theorem closeLedger_samples (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d')
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold closeLedgerP at h
  split at h
  · cases h
    exact orcs_shut [o] d.st hp
  · cases h

theorem spend_samples (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d')
    (hp : stSamplesB d.st = true) : stSamplesB d'.st = true := by
  unfold spendAsMaskP at h
  split at h
  · cases h
    exact orcs_modify (A := d.st.oracles) hp o _ fun _ x => x
  · cases h

theorem admit_samples (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') (hp : stSamplesB d.st = true)
    (hr : ∀ r ∈ rows.toList, rowPlainB r = true) : stSamplesB d'.st = true := by
  unfold admitP at h
  split at h
  · obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, _, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact orcs_modify (A := d.st.oracles) hp o _ fun _ _ r hr' => hr r hr'
  · cases h

theorem beginRun_samples (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) (hp : stSamplesB d.st = true) :
    stSamplesB d'.st = true := by
  unfold beginRunP at h
  split at h
  · obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact orcs_shut _ d.st hp
  · cases h

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.orcs_iff
#print axioms VerifiableInference.Desc.Ground.Sh.samples_of_plain
#print axioms VerifiableInference.Desc.Ground.Sh.samples_rows
#print axioms VerifiableInference.Desc.Ground.Sh.start_samples
#print axioms VerifiableInference.Desc.Ground.Sh.orcs_modify
#print axioms VerifiableInference.Desc.Ground.Sh.orcs_sent
#print axioms VerifiableInference.Desc.Ground.Sh.orcs_shut
#print axioms VerifiableInference.Desc.Ground.Sh.join_samples
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_samples
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_samples
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_samples
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_samples
#print axioms VerifiableInference.Desc.Ground.Sh.recv_samples
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_samples
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_samples
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_samples
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_samples
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_samples
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_samples
#print axioms VerifiableInference.Desc.Ground.Sh.spend_samples
#print axioms VerifiableInference.Desc.Ground.Sh.admit_samples
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_samples
#print axioms VerifiableInference.Desc.Ground.Sh.orcsPlainB
#print axioms VerifiableInference.Desc.Ground.Sh.stSamplesB
