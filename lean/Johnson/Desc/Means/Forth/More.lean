--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/More.lean: all that a statement claims goes forwards over further plain
functions that change a statement. It goes on from Johnson/Desc/Means/Forth/Holds.lean.

  onOracle_forth  the general form for a change of one oracle message that leaves its shape and its
                  sample rows
  takeMasksInto_forth, takeMasksP_forth   several mask entries are taken: these two show also that
                  the statement stays in order, which Johnson/Desc/Means/Page.lean does not
  closeLedgerP_forth   a ledger is shut
  spendAsMaskP_forth   a message that is not sampled becomes a mask
  adoptP_forth    messages whose trees another chain has sent come in: a new message has no sample
                  row yet
  elsewhereP_forth   a message is sampled in another statement: its sample rows there are copied
                  under the number here. They are a new claim here: that they hold of the words, at
                  the statement behind, is a premise
  beginRunP_forth   a proximity test begins: the group's open rows leave the statement, the members'
                  ledgers are shut, and no row comes in

That a statement stays in order over closeLedgerP, spendAsMaskP, adoptP, elsewhereP and beginRunP is
Johnson/Desc/Means/Page.lean's; for elsewhereP it asks that the other statement is in order, which
elsewhereP_forth does not ask. onOracle_forth is the converse of Holds.of_onOracle
(Johnson/Desc/Means/Back.lean).

What is not claimed. That any of the functions returns a state. Of the beginning of a proximity test
only that what the statement still claims behind it holds: nothing on the rows that the test takes
in, nor on the row into which they are batched. In elsewhereP_forth nothing ties the words at the
number here to the words at the number there. Nothing on a verifier's decision, on soundness or on
hiding.

-/
import Johnson.Desc.Means.Forth.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open VerifiableInference.Desc.Ground Desc.Plain

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) {m : Words K} {Lc : Type}

/-- If the statement is in order and all that it claims holds, all holds that it claims behind a
change of one oracle message which leaves that message's shape and its sample rows. -/
theorem onOracle_forth {S : Statement} (hI : InOrder S) (o : Nat) (f : Oracle → Oracle)
    (h1 : ∀ x, (f x).shape = x.shape) (h2 : ∀ x, (f x).sampleRows = x.sampleRows)
    (hH : Holds ρ S m) : Holds ρ { S with oracles := S.oracles.modify o f } m := by
  refine holds_forth (S' := { S with oracles := S.oracles.modify o f }) ρ hI
    (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ h1)
    (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩) (fun o' x' hx' r hr => ?_) hH
  obtain ⟨x0, hx0, c⟩ := elem_of_modify o' x' hx'
  rcases c with rfl | rfl
  · exact Or.inl ⟨_, hx0, hr⟩
  · rw [h2] at hr
    exact Or.inl ⟨x0, hx0, hr⟩

/-- If the taking of n mask entries, one by one, returns a state, the statement in front is in order
and all that it claims holds, the statement behind is in order and all that it claims holds. -/
theorem takeMasksInto_forth (o : Nat) : ∀ (n : Nat) (d d' : DState Lc) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') → InOrder d.st → Holds ρ d.st m →
    InOrder d'.st ∧ Holds ρ d'.st m
  | 0, d, d', acc, l, h, hI, hH => by
    unfold takeMasksInto at h
    obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj h)
    exact ⟨hI, hH⟩
  | n + 1, d, d', acc, l, h, hI, hH => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none =>
      rw [h1] at h
      cases h
    | some y =>
      obtain ⟨i, d1⟩ := y
      rw [h1] at h
      exact takeMasksInto_forth o n d1 d' (acc.push i) l h (takeMaskP_keeps h1 hI)
        (takeMaskP_forth ρ h1 hI hH)

@[inherit_doc takeMasksInto_forth]
theorem takeMasksP_forth {d d' : DState Lc} {o count : Nat} {l : List Nat}
    (h : takeMasksP d o count = some (l, d')) (hI : InOrder d.st) (hH : Holds ρ d.st m) :
    InOrder d'.st ∧ Holds ρ d'.st m :=
  takeMasksInto_forth ρ o count d d' #[] l h hI hH

/-- If closeLedgerP returns a state, the statement in front is in order and all that it claims
holds, all that the statement behind claims holds: it turns a ledger alone. -/
theorem closeLedgerP_forth {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hI : InOrder d.st) (hH : Holds ρ d.st m) : Holds ρ d'.st m := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact onOracle_forth ρ hI o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      (fun _ => rfl) (fun _ => rfl) hH
  · cases h

/-- The like for spendAsMaskP: it turns one mark of a message alone. -/
theorem spendAsMaskP_forth {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hI : InOrder d.st) (hH : Holds ρ d.st m) : Holds ρ d'.st m := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact onOracle_forth ρ hI o (fun x => { x with spentAsMask := true }) (fun _ => rfl)
      (fun _ => rfl) hH
  · cases h

/-- The like for adoptP: a message that comes in has no sample row yet. -/
theorem adoptP_forth {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hI : InOrder d.st) (hH : Holds ρ d.st m) :
    Holds ρ d'.st m := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    refine holds_forth ρ hI (extends_stSent d.st sent) (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩)
      (fun o x' hx' r hr => ?_) hH
    have hx'' : (Slice.stSent d.st sent).oracles[o]? = some x' := hx'
    by_cases ho : o < d.st.oracles.size
    · rw [Slice.stSent_old d.st sent o ho] at hx''
      exact Or.inl ⟨x', hx'', hr⟩
    · obtain ⟨i, rfl⟩ : ∃ i, o = d.st.oracles.size + i := ⟨o - d.st.oracles.size, by omega⟩
      rw [Slice.stSent_new] at hx''
      obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.1 hx''
      simp at hr
  · cases h

/-- **If elsewhereP returns a state, the statement in front is in order, all that it claims holds,
and the copied sample rows hold at the statement behind, all that the statement behind claims
holds.** That the copied rows hold is a premise. -/
theorem elsewhereP_forth {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hI : InOrder d.st) (hH : Holds ρ d.st m)
    (hs : ∀ y, other.oracles[theirs]? = some y →
      ∀ r ∈ (y.sampleRows.map (·.renamed mine)).toList, Says ρ d'.st r m) :
    Holds ρ d'.st m := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    refine holds_forth (S' := { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad } }) ρ hI
      (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl)
      (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩) (fun o' x' hx' r hr => ?_) hH
    obtain ⟨x0, hx0, c⟩ := elem_of_modify o' x' hx'
    rcases c with rfl | rfl
    · exact Or.inl ⟨_, hx0, hr⟩
    · exact Or.inr (hs y hy r hr)
  · cases h

/-- **If beginRunP returns a state, the statement in front is in order and all that it claims holds,
all that the statement behind claims holds**: the group under test has no open row behind, every
other row and every sample row was there in front. -/
theorem beginRunP_forth {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hI : InOrder d.st) (hH : Holds ρ d.st m) :
    Holds ρ d'.st m := by
  obtain ⟨G, _, _, e⟩ := beginRunP_inv h
  rw [e]
  refine holds_forth ρ hI (extends_begun d.st g G) (fun g' G' hG' r hr => ?_)
    (fun o x' hx' r hr => ?_) hH
  · rw [begun_groups] at hG'
    obtain ⟨G0, hG0, c⟩ := elem_of_modify g' G' hG'
    rcases c with rfl | rfl
    · exact Or.inl ⟨_, hG0, hr⟩
    · simp at hr
  · have hx'' : (Slice.closeLedgers d.st G.members.toList).oracles[o]? = some x' := hx'
    have e2 := closeLedgers_sampleRows G.members.toList d.st o
    rw [hx''] at e2
    have e3 : (d.st.oracles[o]?).map (fun x : Oracle => x.sampleRows) = some x'.sampleRows :=
      e2.symm
    obtain ⟨x, hx, hsame⟩ := Option.map_eq_some_iff.1 e3
    exact Or.inl ⟨x, hx, by rw [hsame]; exact hr⟩

end OnBytes.Means

#print axioms OnBytes.Means.onOracle_forth
#print axioms OnBytes.Means.takeMasksInto_forth
#print axioms OnBytes.Means.takeMasksP_forth
#print axioms OnBytes.Means.closeLedgerP_forth
#print axioms OnBytes.Means.spendAsMaskP_forth
#print axioms OnBytes.Means.adoptP_forth
#print axioms OnBytes.Means.elsewhereP_forth
#print axioms OnBytes.Means.beginRunP_forth
