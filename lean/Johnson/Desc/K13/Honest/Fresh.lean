--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Fresh.lean: THE NUMBERS OF THE MASK ENTRIES THAT A LEDGER HANDS OUT INCREASE
STRICTLY, AND NONE LIES BELOW THE NUMBER AT WHICH THE LEDGER STOOD (`takeMasksP`,
Johnson/Desc/First/Base/Ground.lean). Statements with their proofs; one test with code.

Why. Kind K13's batching takes 1 + 2 kCol mask entries off the ledger of the index masks' message
for the coefficients of its hiding polynomial (Johnson/Desc/K13/Text.lean: "K13.mask-entries"). A
statement in which these entries vary freely, while the rows on the pile stay as they are, needs
that the entries differ from each other and that no row on the pile names one of them. The kind's
laws on soundness ask neither (Johnson/Desc/K13/Law/Fit.lean says so).
Main names:
  `ledgerOf st o`: the ledger of the oracle message o.
  `nextRealRow_ge`: the ledger's search does not go back.
  `takeMask_next`: one take: the number handed out is at least the ledger's next, and behind the
    take the ledger's next is one more than that number.
  `takeMasks_sorted`: **n takes: the numbers increase strictly, from the ledger's next on.**
  `taken_nodup`: so the mask entries taken differ from each other.
  `pileBelowC st o pile`: a test with code: every entry of the message o that a row on the pile
    names has a number below the ledger's next.
  `taken_off_pile`: **where that test accepts, no row on the pile names an entry that is taken.**

What is not claimed. That `pileBelowC` accepts at the state of a run: it is a condition that no test
of the sub-protocol asks, shown here of no state. OWED, BY THIS KIND, AND WITHOUT AN HONEST PROVER:
that every state which the verifier's own text reaches passes it. By reading, typed nowhere: the
first chain begins with an empty pile; its text puts a row on the pile at one place alone
(`pendingKept`, Johnson/Desc/First/Walk/Quiet.lean); that row is made by `pendingRowO`
(Johnson/Desc/First/Pend/Row.lean), which takes the row's one mask entry off this same ledger and
puts the ledger back with its next one above that entry; every other writer of next raises it. That
the entries taken lie within the mask table and off the pads: under `LedgerAt`,
Johnson/Desc/K13/Law/LedgerWithin.lean and LedgerBound.lean. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerWithin
import OnBytes.Iop.Batt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open Desc.Plain (DState)
open VerifiableInference.Desc.K13.Law (nextOf taken layLedger layLedger_at)

/-- The ledger of the oracle message o. -/
def ledgerOf (st : Statement) (o : ℕ) : Option Ledger := (st.oracles[o]?).bind (·.ledger)

/-- The ledger's search does not go back. -/
theorem nextRealRow_ge (rows lr : ℕ) : ∀ fuel n : ℕ, n ≤ Blk.nextRealRow rows lr fuel n
  | 0, n => Nat.le_refl n
  | fuel + 1, n => by
    show n ≤ if n % 2 ^ lr < rows then n else Blk.nextRealRow rows lr fuel (n + 1)
    split
    · exact Nat.le_refl n
    · exact Nat.le_trans (Nat.le_succ n) (nextRealRow_ge rows lr fuel (n + 1))

variable {L : Type}

/-- **One take.** -/
theorem takeMask_next {d d' : DState L} {o i : ℕ} (h : takeMaskP d o = some (i, d')) :
    ∃ l l' : Ledger, ledgerOf d.st o = some l ∧ l.next ≤ i ∧ ledgerOf d'.st o = some l' ∧
      l'.next = i + 1 := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at h
      cases h
    | some l =>
      rw [hl] at h
      have e : (nextOf l, { d with st := layLedger d.st o (taken l) }) = (i, d') :=
        Option.some.inj h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      refine ⟨l, taken l, hl, nextRealRow_ge _ _ _ _, ?_, rfl⟩
      cases hx : d.st.oracles[o]? with
      | none =>
        rw [hx] at hl
        cases hl
      | some x =>
        show ((layLedger d.st o (taken l)).oracles[o]?).bind (·.ledger) = some (taken l)
        rw [layLedger_at hx]
        rfl
  · cases h

/-- Several takes, behind what was taken before. -/
theorem takeMasksInto_sorted (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L) (l : Ledger), ledgerOf d.st o = some l →
    takeMasksInto o n d acc = some t →
    ∃ new : List ℕ, t.1 = acc.toList ++ new ∧ new.Pairwise (· < ·) ∧ ∀ i ∈ new, l.next ≤ i
  | 0, d, acc, t, l, _, ht => by
    have e : some (acc.toList, d) = some t := ht
    rw [← Option.some.inj e]
    exact ⟨[], (List.append_nil _).symm, List.Pairwise.nil, fun _ hi => by cases hi⟩
  | n + 1, d, acc, t, l, hl, ht => by
    unfold takeMasksInto at ht
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at ht
      cases ht
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at ht
      obtain ⟨l0, l', h0, hle, hl', hn⟩ := takeMask_next hm
      obtain rfl : l0 = l := Option.some.inj (h0.symm.trans hl)
      obtain ⟨new, e, hp, hge⟩ := takeMasksInto_sorted o n d' (acc.push i) t l' hl' ht
      refine ⟨i :: new, ?_, List.pairwise_cons.2 ⟨fun j hj => ?_, hp⟩, fun j hj => ?_⟩
      · rw [e, Array.toList_push, List.append_assoc]
        rfl
      · have := hge j hj
        omega
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact hle
        · have := hge j hj
          omega

/-- **n takes: the numbers increase strictly, from the ledger's next on.** -/
theorem takeMasks_sorted {d : DState L} {o n : ℕ} {t : List ℕ × DState L} {l : Ledger}
    (hl : ledgerOf d.st o = some l) (ht : takeMasksP d o n = some t) :
    t.1.Pairwise (· < ·) ∧ ∀ i ∈ t.1, l.next ≤ i := by
  obtain ⟨new, e, hp, hge⟩ := takeMasksInto_sorted o n d #[] t l hl ht
  have e' : t.1 = new := by
    rw [e]
    rfl
  rw [e']
  exact ⟨hp, hge⟩

/-- Where a take returns, the message has a ledger. -/
theorem ledgerOf_of_take {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (ht : takeMasksP d o (n + 1) = some t) : ∃ l, ledgerOf d.st o = some l := by
  have h : takeMasksInto o (n + 1) d #[] = some t := ht
  unfold takeMasksInto at h
  cases hm : takeMaskP d o with
  | none =>
    rw [hm] at h
    cases h
  | some q =>
    obtain ⟨i, d'⟩ := q
    obtain ⟨l, _, hl, _⟩ := takeMask_next hm
    exact ⟨l, hl⟩

/-- **The mask entries taken differ from each other.** -/
theorem taken_nodup {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (ht : takeMasksP d o n = some t) : (t.1.map fun i => (⟨o, i⟩ : Slot)).Nodup := by
  have hinj : Function.Injective fun i : ℕ => (⟨o, i⟩ : Slot) :=
    fun a b h => congrArg Slot.index h
  cases n with
  | zero =>
    have e : some (([] : List ℕ), d) = some t := ht
    rw [← Option.some.inj e]
    exact List.nodup_nil
  | succ m =>
    obtain ⟨l, hl⟩ := ledgerOf_of_take ht
    exact List.Nodup.map hinj ((takeMasks_sorted hl ht).1.imp fun h => Nat.ne_of_lt h)

/-- Every entry of the message o that a row on the pile names has a number below the ledger's next:
a test with code. It rejects where the message has no ledger. -/
def pileBelowC (st : Statement) (o : ℕ) (pile : List TensorRow) : Bool :=
  match ledgerOf st o with
  | some l => pile.all fun r => r.masks.all fun m => m.1.oracle != o || decide (m.1.index < l.next)
  | none => false

/-- **Where that test accepts, no row on the pile names an entry that is taken.** -/
theorem taken_off_pile {d : DState L} {o n : ℕ} {t : List ℕ × DState L} {pile : List TensorRow}
    (hb : pileBelowC d.st o pile = true) (ht : takeMasksP d o n = some t) :
    ∀ r ∈ pile, ∀ m ∈ r.masks, m.1 ∉ t.1.map fun i => (⟨o, i⟩ : Slot) := by
  intro r hr m hm hmem
  obtain ⟨i, hi, hs⟩ := List.mem_map.1 hmem
  unfold pileBelowC at hb
  cases hl : ledgerOf d.st o with
  | none =>
    rw [hl] at hb
    cases hb
  | some l =>
    rw [hl] at hb
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hb r hr) m hm
    have h2 := (takeMasks_sorted hl ht).2 i hi
    rw [← hs] at h1
    simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h1
    omega

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.nextRealRow_ge
#print axioms VerifiableInference.Desc.K13.Honest.takeMask_next
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_sorted
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_sorted
#print axioms VerifiableInference.Desc.K13.Honest.ledgerOf_of_take
#print axioms VerifiableInference.Desc.K13.Honest.taken_nodup
#print axioms VerifiableInference.Desc.K13.Honest.taken_off_pile
