--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/AllMet.lean: for whoever writes an honest prover's side of a sub-protocol:
ONE proposition that goes forwards from step to step; a lemma for each of the thirteen plain
functions that change a statement (Johnson/Desc/First/Base/Ground.lean); the start; how the words
may be changed; and what a row's value reads of a statement.

AllMet ρ S m says: the statement S is in order (InOrder, Johnson/Desc/Means/Order.lean), and all
that it claims holds of the words m (Holds, Johnson/Desc/Means/Holds.lean).

Two ways to carry it along a run. In each lemma on a function the words are the same in front and
behind. A caller can hand ONE family of words for the whole run: the words at the numbers of
messages that are not yet received stand in m from the first step on; that does no harm, since a row
in order has no coefficient at a message that is not there. Such an m may hang on challenges that
come later: so AllMet speaks of a finished run's words, not of a strategy. Or the words GROW with
each sending: allMet_agree goes from one family to another that agrees with it at every message
which the statement has.

  AllMet          the proposition
  allMet_start    it holds of the statement with no message and no group, at all words
  allMet_agree    it reads the words at the statement's own messages alone (value_of_words,
                  says_of_words: so does every row)
  newGroupP_met, joinP_met, takeMaskP_met, takeMasksP_met, closeLedgerP_met, spendAsMaskP_met,
  recvP_met, adoptP_met, beginRunP_met
                  if the function returns a state and AllMet holds in front, AllMet holds behind:
                  these nine lay no new claim
  addRowP_met, addRowsP_met
                  the like, if moreover the new open rows hold at the statement in front (for a
                  list: in front of the first adding)
  admitP_met      the like, if the sample rows that are written are on the message and hold at the
                  statement in front
  elsewhereP_met  the like, if the other statement is in order and the copied sample rows hold at
                  the statement behind; elsewhereP_met_at: at the statement in front, row by row
  tableSize_of_shapes, size_of_shapes (also under the name oracles_size_of_shapes),
  value_of_shapes, says_of_shapes
                  a row's value reads of a statement the codes and the messages' shapes alone
  says_newGroupP, says_joinP, says_takeMaskP, says_takeMasksP, says_addRowP, says_addRowsP,
  says_closeLedgerP, says_spendAsMaskP, says_admitP, says_elsewhereP
                  so ANY row says behind one of these ten what it says in front (with
                  says_addRowsFrom and says_takeMasksInto, for the two that repeat a step): for a
                  step that calls several functions in a row and shows its new rows once. Not so
                  behind recvP and adoptP, which bring new messages in

Where the lemmas come from. Each lemma whose name ends in _met, but takeMasksP_met, pairs a lemma of
Johnson/Desc/Means/Page.lean (InOrder) with one of Forth/Holds.lean, Send.lean or More.lean (Holds);
takeMasksP_met is More.lean's alone; elsewhereP_met_at is elsewhereP_met with says_elsewhereP.
Lemmas like says_of_shapes and tableSize_of_shapes stand higher in the library, at other premises:
says_same and tableSize_same (Johnson/Top/H0/Walk/FrameFieldsBack.lean), value_same
(Johnson/Desc/K14/Law/Shapes.lean). Like value_of_words, for a group's members: value_agree
(Johnson/Desc/Means/ItemsRead.lean).

What is not claimed. That any function returns a state. Of the beginning of a proximity test only
that AllMet goes over it: nothing on the rows that the test takes in. No form of elsewhereP_met has
its premise at the OTHER statement: what a renamed row says there is says_renamed's
(Johnson/Desc/Third/Law/Renamed.lean), which stands above this folder: a caller joins the two.
Nothing on a verifier's decision, on soundness or on hiding.

-/
import Johnson.Desc.Means.Forth.Send
import Johnson.Desc.Means.Forth.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open VerifiableInference.Desc.Ground Desc.Plain

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) {m : Words K} {Lc : Type}

/-- **The statement is in order, and all that it claims holds of the words.** -/
def AllMet (S : Statement) (m : Words K) : Prop := InOrder S ∧ Holds ρ S m

/-- The start: the statement with no message and no group, at all words. -/
theorem allMet_start (codes : Codes) (m : Words K) :
    AllMet ρ { codes := codes, oracles := #[], groups := #[] } m :=
  ⟨InOrder.start codes, ⟨fun g G h => by simp at h, fun o x h => by simp at h⟩⟩

/-- If newGroupP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem newGroupP_met {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨newGroupP_keeps h hM.1, newGroupP_forth ρ h hM.1 hM.2⟩

/-- If joinP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem joinP_met {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨joinP_keeps h hM.1, joinP_forth ρ h hM.1 hM.2⟩

/-- If takeMaskP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem takeMaskP_met {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨takeMaskP_keeps h hM.1, takeMaskP_forth ρ h hM.1 hM.2⟩

/-- If takeMasksP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem takeMasksP_met {d d' : DState Lc} {o count : Nat} {l : List Nat}
    (h : takeMasksP d o count = some (l, d')) (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  takeMasksP_forth ρ h hM.1 hM.2

/-- If closeLedgerP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem closeLedgerP_met {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨closeLedgerP_keeps h hM.1, closeLedgerP_forth ρ h hM.1 hM.2⟩

/-- If spendAsMaskP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem spendAsMaskP_met {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨spendAsMaskP_keeps h hM.1, spendAsMaskP_forth ρ h hM.1 hM.2⟩

/-- If recvP returns a state and AllMet holds in front, AllMet holds behind, at the same words. -/
theorem recvP_met {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨recvP_keeps h hM.1, recvP_forth ρ h hM.1 hM.2⟩

/-- If adoptP returns a state and AllMet holds in front, AllMet holds behind, at the same words. -/
theorem adoptP_met {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨adoptP_keeps h hM.1, adoptP_forth ρ h hM.1 hM.2⟩

/-- If the function returns a state, AllMet holds in front, and the new open row holds at the
statement in front, AllMet holds behind. -/
theorem addRowP_met {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hM : AllMet ρ d.st m) (hs : Says ρ d.st row m) : AllMet ρ d'.st m :=
  ⟨(addRowP_keeps h hM.1).1, addRowP_forth ρ h hM.1 hM.2 hs⟩

/-- The like for a list of rows: each holds at the statement in front of the first adding. -/
theorem addRowsP_met {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hM : AllMet ρ d.st m) (hs : ∀ r ∈ rows, Says ρ d.st r m) :
    AllMet ρ d'.st m :=
  ⟨addRowsP_keeps h hM.1, addRowsP_forth ρ h hM.1 hM.2 hs⟩

/-- If the function returns a state, AllMet holds in front, and the sample rows that are written are
on the message and hold at the statement in front, AllMet holds behind. -/
theorem admitP_met {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hM : AllMet ρ d.st m)
    (hr : ∀ r ∈ rows.toList, RowOn d.st o r) (hs : ∀ r ∈ rows.toList, Says ρ d.st r m) :
    AllMet ρ d'.st m :=
  ⟨admitP_keeps h hM.1 hr, admitP_forth_at ρ h hM.1 hM.2 hr hs⟩

/-- If the function returns a state, AllMet holds in front, the other statement is in order, and the
copied sample rows hold at the statement behind, AllMet holds behind. -/
theorem elsewhereP_met {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hM : AllMet ρ d.st m) (hO : InOrder other)
    (hs : ∀ y, other.oracles[theirs]? = some y →
      ∀ r ∈ (y.sampleRows.map (·.renamed mine)).toList, Says ρ d'.st r m) :
    AllMet ρ d'.st m :=
  ⟨elsewhereP_keeps h hM.1 hO, elsewhereP_forth ρ h hM.1 hM.2 hs⟩

/-- If beginRunP returns a state and AllMet holds in front, AllMet holds behind. -/
theorem beginRunP_met {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hM : AllMet ρ d.st m) : AllMet ρ d'.st m :=
  ⟨beginRunP_keeps h hM.1, beginRunP_forth ρ h hM.1 hM.2⟩

/-! ## What a row's value reads of the words -/

/-- A row's value at a statement reads the words at the statement's own messages alone. -/
theorem value_of_words (S : Statement) (r : Row) {m m' : Words K}
    (h : ∀ o < S.oracles.size, ∀ part i, m o part i = m' o part i) :
    value ρ S r m = value ρ S r m' := by
  unfold value onTable
  refine Finset.sum_congr rfl fun o ho => ?_
  have e := h o (Finset.mem_range.1 ho)
  simp only [e]

/-- So does what it says. -/
theorem says_of_words (S : Statement) (r : Row) {m m' : Words K}
    (h : ∀ o < S.oracles.size, ∀ part i, m o part i = m' o part i) :
    Says ρ S r m ↔ Says ρ S r m' := by
  unfold Says
  rw [value_of_words ρ S r h]

/-- **From one family of words to another**: if AllMet holds at m, and m' agrees with m at every
message that the statement has, AllMet holds at m'. -/
theorem allMet_agree {S : Statement} {m m' : Words K} (hM : AllMet ρ S m)
    (h : ∀ o < S.oracles.size, ∀ part i, m o part i = m' o part i) : AllMet ρ S m' :=
  ⟨hM.1, ⟨fun g G hG r hr => (says_of_words ρ S r h).1 (hM.2.rows g G hG r hr),
    fun o x hx r hr => (says_of_words ρ S r h).1 (hM.2.samples o x hx r hr)⟩⟩

/-! ## What a row's value reads of a statement -/

variable {S S' : Statement}

/-- A table's size reads the codes and the message's shape alone. -/
theorem tableSize_of_shapes (hc : S'.codes = S.codes)
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) (o : Nat) (part : Part) :
    tableSize S' o part = tableSize S o part := by
  have e := hs o
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at e
    cases hx' : S'.oracles[o]? with
    | none => simp [tableSize, Statement.has, hx, hx']
    | some x' =>
      rw [hx'] at e
      cases e
  | some x =>
    rw [hx] at e
    cases hx' : S'.oracles[o]? with
    | none =>
      rw [hx'] at e
      cases e
    | some x' =>
      rw [hx'] at e
      have es : x'.shape = x.shape := Option.some.inj e
      simp [tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
        Statement.placeBits, hx, hx', es, hc]

/-- Two statements whose messages have the same shapes at every number have as many messages. -/
theorem size_of_shapes
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) : S'.oracles.size = S.oracles.size := by
  have key : ∀ (A B : Array Oracle),
      (∀ o : Nat, (A[o]?).map (fun x : Oracle => x.shape) =
        (B[o]?).map (fun x : Oracle => x.shape)) → A.size ≤ B.size := by
    intro A B h
    by_contra c
    have c' : B.size < A.size := Nat.lt_of_not_le c
    have e := h B.size
    rw [Array.getElem?_eq_getElem c', Array.getElem?_eq_none (Nat.le_refl _)] at e
    cases e
  exact Nat.le_antisymm (key _ _ hs) (key _ _ fun o => (hs o).symm)

@[inherit_doc size_of_shapes]
theorem oracles_size_of_shapes
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) : S'.oracles.size = S.oracles.size :=
  size_of_shapes hs

/-- **A row's value reads of a statement the codes and the messages' shapes alone.** -/
theorem value_of_shapes (hc : S'.codes = S.codes)
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) (r : Row) (m : Words K) :
    value ρ S' r m = value ρ S r m := by
  unfold value onTable
  rw [size_of_shapes hs]
  simp only [tableSize_of_shapes hc hs]

/-- So does what it says. -/
theorem says_of_shapes (hc : S'.codes = S.codes)
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) (r : Row) (m : Words K) :
    Says ρ S' r m ↔ Says ρ S r m := by
  unfold Says
  rw [value_of_shapes ρ hc hs]

/-- Any row says behind a joining what it says in front. -/
theorem says_joinP {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine says_of_shapes ρ (S := d.st) ?_ ?_ r m
    · rfl
    · intro o'
      exact map_modify _ _ _ _ _ fun _ => rfl
  · cases h

/-- Any row says behind the taking of a mask entry what it says in front. -/
theorem says_takeMaskP {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    refine says_of_shapes ρ (S := d.st) ?_ ?_ r m
    · rfl
    · intro o'
      exact map_modify _ _ _ _ _ fun _ => rfl
  · cases h

/-- Any row says behind the adding of an open row what it says in front. -/
theorem says_addRowP {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold addRowP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact says_of_shapes ρ rfl (fun _ => rfl) r m
  · cases h

/-- Any row says behind the opening of a group what it says in front. -/
theorem says_newGroupP {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact says_of_shapes ρ rfl (fun _ => rfl) r m
  · cases h

/-- Any row says behind the adding of open rows, one by one, what it says in front. -/
theorem says_addRowsFrom (g : Nat) (r : Row) (m : Words K) : ∀ (rows : List Row) (d d' : DState Lc),
    addRowsFrom g rows d = some d' → (Says ρ d'.st r m ↔ Says ρ d.st r m)
  | [], d, d', h => by
    obtain rfl : d = d' := Option.some.inj h
    exact Iff.rfl
  | row :: rows, d, d', h => by
    unfold addRowsFrom at h
    cases h1 : addRowP d g row with
    | none =>
      rw [h1] at h
      cases h
    | some d1 =>
      rw [h1] at h
      exact (says_addRowsFrom g r m rows d1 d' h).trans (says_addRowP ρ h1 r m)

@[inherit_doc says_addRowsFrom]
theorem says_addRowsP {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (r : Row) (m : Words K) :
    Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold addRowsP at h
  split at h
  · exact says_addRowsFrom ρ g r m rows d d' h
  · cases h

/-- Any row says behind the taking of mask entries, one by one, what it says in front. -/
theorem says_takeMasksInto (o : Nat) (r : Row) (m : Words K) : ∀ (n : Nat) (d d' : DState Lc)
    (acc : Array Nat) (l : List Nat), takeMasksInto o n d acc = some (l, d') →
    (Says ρ d'.st r m ↔ Says ρ d.st r m)
  | 0, d, d', acc, l, h => by
    unfold takeMasksInto at h
    obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj h)
    exact Iff.rfl
  | n + 1, d, d', acc, l, h => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none =>
      rw [h1] at h
      cases h
    | some y =>
      obtain ⟨i, d1⟩ := y
      rw [h1] at h
      exact (says_takeMasksInto o r m n d1 d' (acc.push i) l h).trans (says_takeMaskP ρ h1 r m)

@[inherit_doc says_takeMasksInto]
theorem says_takeMasksP {d d' : DState Lc} {o count : Nat} {l : List Nat}
    (h : takeMasksP d o count = some (l, d')) (r : Row) (m : Words K) :
    Says ρ d'.st r m ↔ Says ρ d.st r m :=
  says_takeMasksInto ρ o r m count d d' #[] l h

/-- Any row says behind the shutting of a ledger what it says in front. -/
theorem says_closeLedgerP {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    have hs : ∀ o' : Nat, ((d.st.oracles.modify o fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } })[o']?).map
          (fun x : Oracle => x.shape) = (d.st.oracles[o']?).map (fun x : Oracle => x.shape) :=
      fun o' => map_modify _ _ _ _ _ fun _ => rfl
    exact says_of_shapes ρ (S := d.st) (S' := Slice.closeLedgers d.st [o]) rfl hs r m
  · cases h

/-- Any row says behind a message's becoming a mask what it says in front. -/
theorem says_spendAsMaskP {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (r : Row) (m : Words K) : Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    refine says_of_shapes ρ (S := d.st) ?_ ?_ r m
    · rfl
    · intro o'
      exact map_modify _ _ _ _ _ fun _ => rfl
  · cases h

/-- Any row says behind the writing of a message's sample rows what it says in front. -/
theorem says_admitP {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (r : Row) (m : Words K) :
    Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    have hs : ∀ o' : Nat, ((d.st.oracles.modify o fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun q => (q.part, q.index),
        ledger := Slice.freshLedger d.st.codes x.shape })[o']?).map (fun x : Oracle => x.shape) =
          (d.st.oracles[o']?).map (fun x : Oracle => x.shape) :=
      fun o' => map_modify _ _ _ _ _ fun _ => rfl
    exact says_of_shapes ρ (S := d.st) (S' := Slice.admitted d.st o x.shape places rows) rfl hs r m
  · cases h

/-- Any row says behind the copying of another statement's sample rows what it says in front. -/
theorem says_elsewhereP {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (r : Row) (m : Words K) :
    Says ρ d'.st r m ↔ Says ρ d.st r m := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine says_of_shapes ρ (S := d.st) ?_ ?_ r m
    · rfl
    · intro o'
      exact map_modify _ _ _ _ _ fun _ => rfl
  · cases h

/-- elsewhereP_met with its premise at the statement in front, row by row of the other statement's
sample rows: each, renamed, holds at the statement in front. -/
theorem elsewhereP_met_at {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hM : AllMet ρ d.st m) (hO : InOrder other)
    (hs : ∀ y, other.oracles[theirs]? = some y →
      ∀ r0 ∈ y.sampleRows.toList, Says ρ d.st (r0.renamed mine) m) :
    AllMet ρ d'.st m := by
  refine elsewhereP_met ρ h hM hO fun y hy r hr => ?_
  simp only [Array.toList_map, List.mem_map] at hr
  obtain ⟨r0, h0, rfl⟩ := hr
  exact (says_elsewhereP ρ h _ m).2 (hs y hy r0 h0)

end OnBytes.Means

#print axioms OnBytes.Means.allMet_start
#print axioms OnBytes.Means.newGroupP_met
#print axioms OnBytes.Means.joinP_met
#print axioms OnBytes.Means.takeMaskP_met
#print axioms OnBytes.Means.takeMasksP_met
#print axioms OnBytes.Means.closeLedgerP_met
#print axioms OnBytes.Means.spendAsMaskP_met
#print axioms OnBytes.Means.recvP_met
#print axioms OnBytes.Means.adoptP_met
#print axioms OnBytes.Means.addRowP_met
#print axioms OnBytes.Means.addRowsP_met
#print axioms OnBytes.Means.admitP_met
#print axioms OnBytes.Means.elsewhereP_met
#print axioms OnBytes.Means.tableSize_of_shapes
#print axioms OnBytes.Means.size_of_shapes
#print axioms OnBytes.Means.value_of_shapes
#print axioms OnBytes.Means.says_of_shapes
#print axioms OnBytes.Means.says_joinP
#print axioms OnBytes.Means.says_takeMaskP
#print axioms OnBytes.Means.says_addRowP
#print axioms OnBytes.Means.beginRunP_met
#print axioms OnBytes.Means.value_of_words
#print axioms OnBytes.Means.says_of_words
#print axioms OnBytes.Means.allMet_agree
#print axioms OnBytes.Means.oracles_size_of_shapes
#print axioms OnBytes.Means.says_newGroupP
#print axioms OnBytes.Means.says_addRowsFrom
#print axioms OnBytes.Means.says_addRowsP
#print axioms OnBytes.Means.says_takeMasksInto
#print axioms OnBytes.Means.says_takeMasksP
#print axioms OnBytes.Means.says_closeLedgerP
#print axioms OnBytes.Means.says_spendAsMaskP
#print axioms OnBytes.Means.says_admitP
#print axioms OnBytes.Means.says_elsewhereP
#print axioms OnBytes.Means.elsewhereP_met_at
