--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/TakeMany.lean: THE TAKING OF n MASK ENTRIES, ON SHAPES, AS ONE CLOSED
FORM, general in n. Definitions, statements and proofs. A routine of the verifier's ground: NOTHING
IS SHOWN OF ANY PROVER.

What for. `takeMasksS a o n` (More.lean) takes the entries one by one: n steps, each of which
searches the next real row and rewrites the list of messages. At the full size n is some 17,800, and
Lean's kernel does not carry that iteration. Here: what the n steps hand out and leave is written
without a step: the numbers as ONE FORMULA over `List.range n`, the shape behind with ONE ledger
laid in.

The order of an oracle message's free entries, and that the search walks through them in that order,
are the library's (Fmt/Places.lean: `entryNo`, `freeAt`; OnBytes/Iop/LedgerPlaces.lean:
`nextRealRow_first`,
`nextRealRow_freeAt`): CALLED. That file names no ledger; this one does.

  `freeNo m j`: the number of the j-th free entry of a mask table with m rows.
  `startAt m k`: where the search stands when k entries have been handed out. `next_free`: from
    there it finds the k-th.
  `withLedger`, `ledger_with`, `with_with`, `with_same`: a message's ledger laid in.
  `InStep l k`: the ledger is open, has a row, as many row bits as the format gives its rows, and
    stands where k entries have been handed out. A member: `inStep_fresh`.
  `take_one`: one taking. `take_into`: the loop.
  **`take_many`**: THE CLOSED FORM: where the ledger is in step at k and has n entries left.
  `take_many_step`: the ledger behind is in step at k + n: so the form can be used again.

Limits.
- k, the number of entries handed out before, is no field of a ledger: whoever calls the law names
  it. A ledger as a sending makes it is in step at 0 where its fields are as `InStep` asks: not
  shown here.
- Enough, not needed: a ledger that is not in step may hand out entries too.


-/
import Johnson.Desc.Ground.Shape.More
import OnBytes.Iop.LedgerPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes Fmt.Places

/-- The number of the j-th free entry of a mask table with m rows. -/
def freeNo (m j : Nat) : Nat := entryNo m (freeAt m j).1 (freeAt m j).2

/-- Where the search stands when k entries have been handed out. -/
def startAt (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => freeNo m k + 1

/-- From there the search finds the k-th free entry. -/
theorem next_free {m : Nat} (hm : 0 < m) : ∀ k,
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) (startAt m k) = freeNo m k
  | 0 => nextRealRow_first hm
  | k + 1 => nextRealRow_freeAt hm k

/-- The shape with a ledger laid in at message o. -/
def withLedger (a : CoreSh) (o : Nat) (l : Ledger) : CoreSh :=
  { a with st := { a.st with
      oracles := modAt a.st.oracles o fun x => { x with ledger := some l } } }

theorem ledger_with (a : CoreSh) (o : Nat) (l₀ l : Ledger)
    (h : (a.st.oracles[o]?).bind (·.ledger) = some l₀) :
    ((withLedger a o l).st.oracles[o]?).bind (·.ledger) = some l := by
  unfold withLedger
  dsimp only
  rw [modAt_get]
  cases hx : a.st.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x => rfl

theorem with_with (a : CoreSh) (o : Nat) (l l' : Ledger) :
    withLedger (withLedger a o l) o l' = withLedger a o l' := by
  unfold withLedger
  dsimp only
  rw [modAt_modAt]

theorem with_same (a : CoreSh) (o : Nat) (l : Ledger)
    (h : (a.st.oracles[o]?).bind (·.ledger) = some l) : withLedger a o l = a := by
  have e : modAt a.st.oracles o (fun x => { x with ledger := some l }) = a.st.oracles := by
    refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
    simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    by_cases c : j = o
    · subst c
      rw [if_pos rfl]
      rw [List.getElem?_eq_getElem j2] at h
      have h' : a.st.oracles[j].ledger = some l := h
      have hx : ∀ x : OrcSh, x.ledger = some l → ({ x with ledger := some l } : OrcSh) = x :=
        fun x e => by
          cases x
          cases e
          rfl
      exact hx _ h'
    · rw [if_neg c]
  unfold withLedger
  rw [e]

/-- **The ledger is in step at k.** -/
def InStep (l : Ledger) (k : Nat) : Prop :=
  l.closed = false ∧ 0 < l.rows ∧ l.logRows = logUp l.rows ∧ l.next = startAt l.rows k

/-- A member: a ledger with a row, the format's row bits, open, from which nothing is handed out. -/
theorem inStep_fresh (m left : Nat) (hm : 0 < m) : InStep ⟨0, left, m, logUp m, false⟩ 0 :=
  ⟨rfl, hm, rfl, rfl⟩

/-- The ledger behind n more takings. -/
def behind (l : Ledger) (k n : Nat) : Ledger :=
  { l with next := startAt l.rows (k + n), left := l.left - n }

/-- One taking. -/
theorem take_one (a : CoreSh) (o : Nat) (l : Ledger) (k : Nat)
    (hl : (a.st.oracles[o]?).bind (·.ledger) = some l) (hs : InStep l k) (hn : 0 < l.left) :
    takeMaskS a o = some (freeNo l.rows k, withLedger a o (behind l k 1)) := by
  obtain ⟨hc, hm, hq, hx⟩ := hs
  have hg : takeMaskG a.st o = true := by
    unfold takeMaskG
    rw [hl]
    show (!l.closed && decide (0 < l.left)) = true
    rw [hc]
    simpa using hn
  unfold takeMaskS
  rw [if_pos hg, hl]
  have e : Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next = freeNo l.rows k := by
    rw [hq, hx]
    exact next_free hm k
  show some (Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next, _) = _
  rw [e]
  rfl

theorem behind_step (l : Ledger) (k n : Nat) (hs : InStep l k) : InStep (behind l k n) (k + n) :=
  ⟨hs.1, hs.2.1, hs.2.2.1, rfl⟩

/-- The loop. -/
theorem take_into (o : Nat) : ∀ (n : Nat) (a : CoreSh) (l : Ledger) (k : Nat) (acc : Array Nat),
    (a.st.oracles[o]?).bind (·.ledger) = some l → InStep l k → n ≤ l.left →
    takeMasksIntoS o n a acc =
      some (acc.toList ++ (List.range n).map (fun i => freeNo l.rows (k + i)),
        withLedger a o (behind l k n))
  | 0, a, l, k, acc, hl, hs, _ => by
    have e : behind l k 0 = l := by
      unfold behind
      rw [Nat.add_zero, ← hs.2.2.2, Nat.sub_zero]
    rw [e, with_same a o l hl]
    show some (acc.toList, a) = _
    rw [List.range_zero, List.map_nil, List.append_nil]
  | n + 1, a, l, k, acc, hl, hs, hn => by
    rw [takeMasksIntoS, take_one a o l k hl hs (by omega)]
    show takeMasksIntoS o n (withLedger a o (behind l k 1)) (acc.push (freeNo l.rows k)) = _
    rw [take_into o n (withLedger a o (behind l k 1)) (behind l k 1) (k + 1) _
      (ledger_with a o l _ hl) (behind_step l k 1 hs) (by show n ≤ l.left - 1; omega), with_with]
    have e1 : behind (behind l k 1) (k + 1) n = behind l k (n + 1) := by
      unfold behind
      dsimp only
      rw [Nat.sub_sub, Nat.add_comm 1 n, Nat.add_assoc, Nat.add_comm 1 n]
    have e2 : (acc.push (freeNo l.rows k)).toList ++
        (List.range n).map (fun i => freeNo (behind l k 1).rows (k + 1 + i)) =
        acc.toList ++ (List.range (n + 1)).map (fun i => freeNo l.rows (k + i)) := by
      rw [Array.toList_push, List.append_assoc, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      congr 1
      show freeNo l.rows k :: _ = freeNo l.rows (k + 0) :: _
      rw [Nat.add_zero]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      show freeNo l.rows (k + 1 + i) = freeNo l.rows (k + (i + 1))
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [e1, e2]

/-- **THE CLOSED FORM.** Where the ledger of message o is in step at k and has n entries left: the
taking of n entries hands out the free entries number k, …, k + n - 1, and leaves the shape with
that ledger moved on by n. -/
theorem take_many (a : CoreSh) (o n : Nat) (l : Ledger) (k : Nat)
    (hl : (a.st.oracles[o]?).bind (·.ledger) = some l) (hs : InStep l k) (hn : n ≤ l.left) :
    takeMasksS a o n =
      some ((List.range n).map (fun i => freeNo l.rows (k + i)),
        withLedger a o (behind l k n)) := by
  unfold takeMasksS
  rw [take_into o n a l k #[] hl hs hn]
  rfl

/-- The ledger behind lies at message o and is in step at k + n. -/
theorem take_many_step (a : CoreSh) (o n : Nat) (l : Ledger) (k : Nat)
    (hl : (a.st.oracles[o]?).bind (·.ledger) = some l) (hs : InStep l k) :
    ((withLedger a o (behind l k n)).st.oracles[o]?).bind (·.ledger) = some (behind l k n) ∧
      InStep (behind l k n) (k + n) :=
  ⟨ledger_with a o l _ hl, behind_step l k n hs⟩

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.next_free
#print axioms VerifiableInference.Desc.Ground.Sh.ledger_with
#print axioms VerifiableInference.Desc.Ground.Sh.with_with
#print axioms VerifiableInference.Desc.Ground.Sh.with_same
#print axioms VerifiableInference.Desc.Ground.Sh.inStep_fresh
#print axioms VerifiableInference.Desc.Ground.Sh.take_one
#print axioms VerifiableInference.Desc.Ground.Sh.behind_step
#print axioms VerifiableInference.Desc.Ground.Sh.take_into
#print axioms VerifiableInference.Desc.Ground.Sh.take_many
#print axioms VerifiableInference.Desc.Ground.Sh.take_many_step
