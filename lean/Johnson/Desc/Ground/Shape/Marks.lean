-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/Marks.lean: TWO MARKS BESIDE THE SHAPE. What guards ask of ALL summands
of ALL rows of a statement cannot stand in the shape as lists (Johnson/Desc/Ground/Shape/Core.lean
says why). Here it stands as two Bools, each with a reader, with what it gives, and with the law
that each of the ground's eleven plain functions KEEPS it. No statement here names a kind, a chain
or a frame for an honest side.

  `stTidyB`    `tidy4B` (Johnson/Desc/Means/TestsBack.lean; there: true exactly where the statement
      is `Tidy`): every group is in order, every open row passes the tests on places and sizes at
      its group, every sample row lies on its own message; no open row is marked as a sample row;
      no sample row without the mark; every member is sampled.
  `stPlainB`   no tensor in an open row or a sample row has a written-out factor (`PlainRow`,
      OnBytes/Slice/BlkPlain.lean).

HOW THEY ARE MEANT. As marks that the functions CARRY: true at a statement without a message and
without a group (`start_tidy`, `start_plain`), kept by each function; a run on shapes asks the mark
and hands it on, and NEVER COMPUTES IT FROM ROWS. The readers are for the laws alone: they say of
which states the mark speaks. Whoever would rather count one of them among a member's named tests
on values can name the same reader there.

WHICH VALUES THE READERS READ. `stPlainB`: none: lists of numbers of variables. `stTidyB`: at one
spot: of each whole coefficient vector in a row (`Row.forms`) it asks `Form.fits`, which asks
`Tensor.ok` of each tensor, whose third clause compares, for each written-out variable d of that
tensor, the pair `pairs[d]` with (1, 1) (OnBytes/Iop/Tensor.lean). Of a row's terms it reads the
number of variables alone. Where `stPlainB` is true this comparison is idle: there is no
written-out variable.

WHERE THEY HOLD. Nothing is shown here of any description. For `stTidyB` the library has laws along
its chains (Johnson/Desc/Tidy/), each under named premises of its own (on the chain's other
sub-protocols; on the proximity tests'); the last chain's ends in front of that chain's own test.
`stPlainB` does NOT hold everywhere: a row with a written-out factor is laid on the last chain of
both files.

Main names. `tidy_of`, `tidy_mark`, `plain_rows`, `plain_samples`: what the marks give. `X_tidy`,
`X_plain` for X one of join, addRow, adopt, recv, elsewhere, newGroup, takeMask, closeLedger,
spend, admit, beginRun. What an argument owes: `admit_tidy`: the rows lie on their message
(`RowOn`); `elsewhere_tidy`: the other statement is tidy; `addRow_plain`, `admit_plain`: the new
rows are plain; `elsewhere_plain`: the other statement's rows are. `beginRun_rows_in`,
`beginRun_rows_plain`: FROM THE MARKS IN FRONT, the rows that the beginning of a test hands to the
batching pass the tests on places and sizes at the group, and are plain. (`beginRun_tidy` and
`beginRun_plain` say less than they seem to at the group under test: its rows have left the
statement.)

By what. `X_tidy`: the library's `quiet_joinP` and its like, and `Tidy.begun`
(Johnson/Desc/Means/Walk.lean). `beginRun_rows_in`: the library's `InOrder.runRows`
(Johnson/Desc/Means/Order.lean). `X_plain`: shown here.

Limits. WHAT THE TWO MARKS DO NOT PAY. A proximity test's front asks all clauses of the adding once
more of the rows that lie open, at the statement as it then is. `stTidyB` gives the clauses on
places and sizes (`RowIn`, Johnson/Desc/Means/Says.lean). It does not give: of a TERM's tensor any
of the four clauses of `tensorInOrder` (at most 63 variables; the slice lies inside its vector; a
written-out variable's pair is (1, 1); no written-out variable twice); of a run that its
coefficients lie inside their vector (`coeffsInside`); that no coefficient stands on a pad, also
not on the pads of members that joined later. WITH BOTH MARKS TRUE THERE IS STILL OWED: at most 63
variables in each term; `coeffsInside`; the pads. A third mark, or named tests, are owed for these;
they are not here. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.Ground.Shape.Ground
import Johnson.Desc.Means.TestsBack
import OnBytes.Slice.BlkPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice OnBytes.Means Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## 1 The two readers, and what they give -/

/-- The first mark. -/
def stTidyB (S : Statement) : Bool := tidy4B S

theorem tidy_of {S : Statement} (h : stTidyB S = true) : Tidy S := tidy4B_iff.1 h

theorem tidy_mark {S : Statement} (h : Tidy S) : stTidyB S = true := tidy4B_iff.2 h

/-- No tensor of the row has a written-out factor: with code. -/
def rowPlainB (r : OnBytes.Row) : Bool :=
  r.terms.toList.all (fun t => t.v.denseVars.isEmpty) &&
    r.forms.toList.all fun f => f.c.tensors.all fun v => v.denseVars.isEmpty

theorem rowPlainB_iff {r : OnBytes.Row} : rowPlainB r = true ↔ PlainRow r := by
  unfold rowPlainB PlainRow PlainForm
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff]

/-- The second mark: every open row and every sample row is plain. -/
def stPlainB (S : Statement) : Bool :=
  S.groups.toList.all (fun G => G.rows.toList.all rowPlainB) &&
    S.oracles.toList.all fun x => x.sampleRows.toList.all rowPlainB

/-- Every open row is plain. -/
theorem plain_rows {S : Statement} (h : stPlainB S = true) {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) : ∀ r ∈ G.rows.toList, PlainRow r := by
  have h' := h
  unfold stPlainB at h'
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h'
  intro r hr
  have hm : G ∈ S.groups.toList := by
    obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.1 hG
    rw [← e]
    exact Array.getElem_mem_toList hi
  exact rowPlainB_iff.1 (List.all_eq_true.1 (h'.1 G hm) r hr)

/-- Every sample row is plain. -/
theorem plain_samples {S : Statement} (h : stPlainB S = true) {o : Nat} {x : OnBytes.Oracle}
    (hx : S.oracles[o]? = some x) : ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  have h' := h
  unfold stPlainB at h'
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h'
  intro r hr
  have hm : x ∈ S.oracles.toList := by
    obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.1 hx
    rw [← e]
    exact Array.getElem_mem_toList hi
  exact rowPlainB_iff.1 (List.all_eq_true.1 (h'.2 x hm) r hr)


/-! ## 2 The first mark is kept -/

theorem join_tidy (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d')
    (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_joinP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem addRow_tidy (d d' : DState L) (g : Nat) (row : OnBytes.Row) (h : addRowP d g row = some d')
    (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_addRowP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem adopt_tidy (d d' : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (ids : Array Nat) (h : adoptP d sent given = some (ids, d')) (ht : stTidyB d.st = true) :
    stTidyB d'.st = true :=
  tidy_mark ((quiet_adoptP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem recv_tidy (first : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP first d sent = some (ids, d')) (ht : stTidyB d.st = true) :
    stTidyB d'.st = true :=
  tidy_mark ((quiet_recvP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem elsewhere_tidy (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (ht : stTidyB d.st = true)
    (ho : stTidyB other = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_elsewhereP OnBytes.Model.Reading.gl h (tidy_of ho).inOrder).tidy (tidy_of ht))

theorem newGroup_tidy (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) (ht : stTidyB d.st = true) :
    stTidyB d'.st = true :=
  tidy_mark ((quiet_newGroupP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem takeMask_tidy (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d'))
    (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_takeMaskP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem closeLedger_tidy (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d')
    (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_closeLedgerP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem spend_tidy (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d')
    (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  tidy_mark ((quiet_spendAsMaskP OnBytes.Model.Reading.gl h).tidy (tidy_of ht))

theorem admit_tidy (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d')
    (ht : stTidyB d.st = true) (hon : ∀ r ∈ rows.toList, RowOn d.st o r) :
    stTidyB d'.st = true :=
  tidy_mark ((quiet_admitP OnBytes.Model.Reading.gl h hon).tidy (tidy_of ht))

theorem beginRun_tidy (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) (ht : stTidyB d.st = true) : stTidyB d'.st = true := by
  unfold beginRunP at h
  split at h
  · obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact tidy_mark ((tidy_of ht).begun g G hG)
  · cases h

/-- At a statement without a message and without a group. -/
theorem start_tidy (codes : Codes) :
    stTidyB { codes := codes, oracles := #[], groups := #[] } = true :=
  tidy_mark (Tidy.start codes)

theorem start_plain (codes : Codes) :
    stPlainB { codes := codes, oracles := #[], groups := #[] } = true := rfl

/-- **From the first mark in front: the rows that the beginning of a test hands on pass the tests on
places and sizes at the group.** -/
theorem beginRun_rows_in (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) (ht : stTidyB d.st = true) :
    ∃ G, d.st.groups[g]? = some G ∧ ∀ r ∈ run.rows.toList, RowIn d.st G r := by
  unfold beginRunP at h
  split at h
  · obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨G, hG, (tidy_of ht).inOrder.runRows g G hG⟩
  · cases h

/-- **From the second mark in front: these rows are plain.** -/
theorem beginRun_rows_plain (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) (hp : stPlainB d.st = true) :
    ∀ r ∈ run.rows.toList, PlainRow r := by
  unfold beginRunP at h
  split at h
  · obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
    intro r hr
    have hr' : r ∈ (runRows d.st G).toList := hr
    unfold runRows at hr'
    simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr'
    rcases hr' with (c | c) | c
    · exact plain_rows hp hG r c.1
    · rw [← Array.foldl_toList] at c
      rcases mem_samples d.st r _ _ c with c' | ⟨o, _, x, hx, hr''⟩
      · simp at c'
      · exact plain_samples hp hx r hr''
    · exact plain_rows hp hG r c.1
  · cases h

/-! ## 3 The second mark is kept -/

theorem mem_modify {α : Type} {a : Array α} {i : Nat} {f : α → α} {y : α}
    (h : y ∈ (a.modify i f).toList) : y ∈ a.toList ∨ ∃ x ∈ a.toList, y = f x := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 h)
  have hj' : j < a.size := by simpa using hj
  rw [Array.getElem_modify]
  split
  · exact .inr ⟨a[j], Array.getElem_mem_toList hj', rfl⟩
  · exact .inl (Array.getElem_mem_toList hj')

theorem plain_iff {S : Statement} : stPlainB S = true ↔
    (∀ G ∈ S.groups.toList, ∀ r ∈ G.rows.toList, rowPlainB r = true) ∧
      ∀ x ∈ S.oracles.toList, ∀ r ∈ x.sampleRows.toList, rowPlainB r = true := by
  unfold stPlainB
  simp only [Bool.and_eq_true, List.all_eq_true]

/-- A change of one group that leaves its rows plain keeps the mark. -/
theorem plain_group {S : Statement} (h : stPlainB S = true) (g : Nat) (f : Group → Group)
    (hf : ∀ G, (∀ r ∈ G.rows.toList, rowPlainB r = true) →
      ∀ r ∈ (f G).rows.toList, rowPlainB r = true) :
    stPlainB { S with groups := S.groups.modify g f } = true := by
  obtain ⟨h1, h2⟩ := plain_iff.1 h
  refine plain_iff.2 ⟨fun G hG => ?_, h2⟩
  rcases mem_modify hG with hG | ⟨G', hG', rfl⟩
  · exact h1 G hG
  · exact hf G' (h1 G' hG')

/-- A change of one oracle message that leaves its sample rows plain keeps the mark. -/
theorem plain_oracle {S : Statement} (h : stPlainB S = true) (o : Nat)
    (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (∀ r ∈ x.sampleRows.toList, rowPlainB r = true) →
      ∀ r ∈ (f x).sampleRows.toList, rowPlainB r = true) :
    stPlainB { S with oracles := S.oracles.modify o f } = true := by
  obtain ⟨h1, h2⟩ := plain_iff.1 h
  refine plain_iff.2 ⟨h1, fun x hx => ?_⟩
  rcases mem_modify hx with hx | ⟨x', hx', rfl⟩
  · exact h2 x hx
  · exact hf x' (h2 x' hx')

/-- Both at once. -/
theorem plain_both {S : Statement} (h : stPlainB S = true) (g o : Nat) (fG : Group → Group)
    (fO : OnBytes.Oracle → OnBytes.Oracle)
    (hG : ∀ G, (∀ r ∈ G.rows.toList, rowPlainB r = true) →
      ∀ r ∈ (fG G).rows.toList, rowPlainB r = true)
    (hO : ∀ x, (∀ r ∈ x.sampleRows.toList, rowPlainB r = true) →
      ∀ r ∈ (fO x).sampleRows.toList, rowPlainB r = true) :
    stPlainB { S with groups := S.groups.modify g fG, oracles := S.oracles.modify o fO } = true :=
  plain_oracle (S := { S with groups := S.groups.modify g fG }) (plain_group h g fG hG) o fO hO

theorem sent_plain {S : Statement} (h : stPlainB S = true) (sent : Array OracleNotice) :
    stPlainB (stSent S sent) = true := by
  obtain ⟨h1, h2⟩ := plain_iff.1 h
  refine plain_iff.2 ⟨h1, fun x hx => ?_⟩
  have hx' : x ∈ (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle)).toList :=
    hx
  rw [Array.toList_append, Array.toList_map] at hx'
  rcases List.mem_append.1 hx' with hx' | hx'
  · exact h2 x hx'
  · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx'
    intro r hr
    cases hr

theorem rowPlainB_renamed (r : OnBytes.Row) (o : Nat) : rowPlainB (r.renamed o) = rowPlainB r := by
  unfold rowPlainB Row.renamed
  simp only [Array.toList_map, List.all_map]
  rfl

theorem closeLedgers_plain : ∀ (l : List Nat) (S : Statement), stPlainB S = true →
    stPlainB (closeLedgers S l) = true
  | [], _, h => h
  | o :: l, _, h => closeLedgers_plain l _ (plain_oracle h o _ fun _ x => x)

theorem join_plain (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    show stPlainB (withMessageInGroup d.st g o kept G) = true
    unfold withMessageInGroup
    refine plain_both hp g o _ _ ?_ ?_
    · exact fun _ x => x
    · exact fun _ x => x
  · cases h

theorem addRow_plain (d d' : DState L) (g : Nat) (row : OnBytes.Row) (h : addRowP d g row = some d')
    (hp : stPlainB d.st = true) (hr : rowPlainB row = true) : stPlainB d'.st = true := by
  unfold addRowP at h
  split at h
  · cases h
    exact plain_group hp g _ fun G hG r hr' => by
      rw [Array.toList_push] at hr'
      rcases List.mem_append.1 hr' with hr' | hr'
      · exact hG r hr'
      · rw [List.mem_singleton.1 hr']
        exact hr
  · cases h

theorem adopt_plain (d d' : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (ids : Array Nat) (h : adoptP d sent given = some (ids, d')) (hp : stPlainB d.st = true) :
    stPlainB d'.st = true := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact sent_plain hp sent
  · cases h

theorem recv_plain (first : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP first d sent = some (ids, d')) (hp : stPlainB d.st = true) :
    stPlainB d'.st = true := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact sent_plain hp sent
  · cases h

theorem elsewhere_plain (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (hp : stPlainB d.st = true)
    (ho : stPlainB other = true) : stPlainB d'.st = true := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    exact plain_oracle hp mine _ fun _ _ r hr => by
      rw [Array.toList_map] at hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      rw [rowPlainB_renamed]
      exact rowPlainB_iff.2 (plain_samples ho hy r0 hr0)
  · cases h

theorem newGroup_plain (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) (hp : stPlainB d.st = true) :
    stPlainB d'.st = true := by
  unfold newGroupP at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨h1, h2⟩ := plain_iff.1 hp
    refine plain_iff.2 ⟨fun G hG => ?_, h2⟩
    have hG' : G ∈ (d.st.groups.push { code := code, maskCode := maskCode }).toList := hG
    rw [Array.toList_push] at hG'
    rcases List.mem_append.1 hG' with hG' | hG'
    · exact h1 G hG'
    · rw [List.mem_singleton.1 hG']
      intro r hr
      cases hr
  · cases h

theorem takeMask_plain (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d'))
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact plain_oracle hp o _ fun _ x => x
  · cases h

theorem closeLedger_plain (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold closeLedgerP at h
  split at h
  · cases h
    exact closeLedgers_plain [o] d.st hp
  · cases h

theorem spend_plain (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold spendAsMaskP at h
  split at h
  · cases h
    exact plain_oracle hp o _ fun _ x => x
  · cases h

theorem admit_plain (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d')
    (hp : stPlainB d.st = true) (hr : ∀ r ∈ rows.toList, rowPlainB r = true) :
    stPlainB d'.st = true := by
  unfold admitP at h
  split at h
  · obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, _, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact plain_oracle hp o _ fun _ _ r hr' => hr r hr'
  · cases h

theorem beginRun_plain (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) (hp : stPlainB d.st = true) :
    stPlainB d'.st = true := by
  unfold beginRunP at h
  split at h
  · obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact plain_group (closeLedgers_plain _ _ hp) g _ fun _ _ r hr => by cases hr
  · cases h

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.tidy_of
#print axioms VerifiableInference.Desc.Ground.Sh.tidy_mark
#print axioms VerifiableInference.Desc.Ground.Sh.rowPlainB_iff
#print axioms VerifiableInference.Desc.Ground.Sh.plain_rows
#print axioms VerifiableInference.Desc.Ground.Sh.plain_samples
#print axioms VerifiableInference.Desc.Ground.Sh.join_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.recv_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.spend_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.admit_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.start_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.start_plain
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_rows_in
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_rows_plain
#print axioms VerifiableInference.Desc.Ground.Sh.mem_modify
#print axioms VerifiableInference.Desc.Ground.Sh.plain_iff
#print axioms VerifiableInference.Desc.Ground.Sh.plain_group
#print axioms VerifiableInference.Desc.Ground.Sh.plain_oracle
#print axioms VerifiableInference.Desc.Ground.Sh.plain_both
#print axioms VerifiableInference.Desc.Ground.Sh.sent_plain
#print axioms VerifiableInference.Desc.Ground.Sh.rowPlainB_renamed
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedgers_plain
#print axioms VerifiableInference.Desc.Ground.Sh.join_plain
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_plain
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_plain
#print axioms VerifiableInference.Desc.Ground.Sh.recv_plain
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_plain
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_plain
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_plain
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_plain
#print axioms VerifiableInference.Desc.Ground.Sh.spend_plain
#print axioms VerifiableInference.Desc.Ground.Sh.admit_plain
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_plain
