--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLedgers.lean: THE LEDGERS OF MASK ENTRIES IN THE KEY FILE'S FIRST CHAIN, BY EXACT COUNTS: how
many entries the index-mask message's and the lookups' own message's ledgers have left behind the
two sendings in front of the lookups, and behind each taking. General in the chain's public values.
Statements and proofs; nothing is evaluated.

Why. Each lookup's link takes mask entries off two messages' ledgers (E2E/KeyLookupAround.lean's
`caller_decide` asks that enough are left: `Room`). Behind the lookups the sub-protocol that lays
the rows on the table asks an EQUATION: the index-mask message's ledger has handed out just the
lookups' entries (`layPile`, Johnson/Desc/Key/One.lean). A bound does not give that: so the count is
kept exactly. And the library's own word for a ledger behind k takes (`LedgerAt`,
Johnson/Desc/K13/Law/LedgerWithin.lean), from which it shows that every index given lies within the
mask table, is shown there of no sub-protocol's state: here it is carried from the step that lays a
ledger through the steps behind.

THE FORM OF THE STATEMENTS. Each says what holds BEHIND a step IF THE STEP ACCEPTS. None says that a
step accepts.

What is defined.
  `LeftIs d o n s`: message o is there, of the shape s, and its ledger is open with JUST n entries
    left.
  `Bare d o s`: message o is there, of the shape s, with no OOD sample taken in.
  **`SameAt d d' o`**: from d to d' the codes, and message o's shape, ledger, mark "sampled" and
    pad, have not turned. `LeftIs`, `Bare`, `PadAbove` and the library's `LedgerAt` travel along it
    (`LeftIs.same`, `Bare.same`, `PadAbove.same`, `ledgerAt_same`): so each step needs one lemma.
  `PadAbove d o`: message o's pad lies in its mask table, from the index `padFirst` on
    (E2E/RowsFit.lean).
  `freeOf codes s`: the entries of a message's mask rows that are free for hidden values (the
    library's `Send.freeMaskEntries` at the shape's numbers).
  `GroupIs d g o`: group g is there, with the one member o, no open row, and no test begun.
What is shown.
  `LeftIs.room`: it gives `Room` at every smaller number.   `LeftIs.lt`.
  **`takeMasks_laws`**: n + m left, n taken: m left; k takes become k + n, and every index given
    lies within the mask table (the library's `takeMasksP_within`); the other messages, all groups
    and the message's own pad stay.
  `recv_keeps`, `recv_same`, `recv_bare`: the step that receives one prover's message (`recvP`).
  **`admit_laws`**: the step that takes in a sample's answers (`admitP`) LAYS THE LEDGER: `freeOf`
    entries left, behind no take (the library's `ledgerAt_made`), and the pad (`PadAbove`).
  `newGroup_same`, `join_same`, `group_made`: a new group, and a message's joining it.
  `layRows_laws`, **`decideSend_laws`**, `seat_laws`: a sending's decision
    (Johnson/Desc/K1/Own.lean): the new messages have the next numbers; each with an OOD sample and
    mask rows has `freeOf` entries left; the older messages stay.
  `idx_laws`, `msg_laws`, **`front_laws`**: the key file's "idx.1.send" and "msg.1.send": behind
    both: the two messages differ; each ledger has all its free entries left, behind no take; the
    ranges' group has the lookups' own message as its one member.
  **`behind_takings`**: behind a link's two takings, in both words; every index that the lookups'
    own message's ledger gave lies below its pad.   **`pile_count`**: `layPile`'s
    equation from `LeftIs` and one equation of numbers.

Limits.
- NO STEP IS SHOWN TO ACCEPT. That the two sendings accept an honest run is not treated.
- The numbers are variables: `freeOf` is evaluated at no shape, and that it is what both links and
  the batching take is shown at no plan.
- The two sendings, the links and `layPile` are not chained in one theorem.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyLookupLink
import Johnson.Desc.K1.Own
import Johnson.Desc.K13.Law.LedgerWithin
import E2E.RowsFit

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc (named need bind_eq_ok)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K13.Law (LedgerAt ledgerAt_made takeMasksP_within)
open OnBytes.Means (tableSize)
open AtPublicFiles.RowsFit (padFirst pad_above takes_below ShapeIs)

/-! ## 1. What is said of a message's ledger, and what leaves it as it is -/

section Words
variable {L M N : Type}

/-- Message o is there, of the shape s, and its ledger of mask entries is open with just n left. -/
def LeftIs (d : DState L) (o n : ℕ) (s : OracleShape) : Prop :=
  ∃ x l, d.st.oracles[o]? = some x ∧ x.shape = s ∧ x.ledger = some l ∧ l.closed = false ∧
    l.left = n

/-- Message o is there, of the shape s, not sampled. -/
def Bare (d : DState L) (o : ℕ) (s : OracleShape) : Prop :=
  ∃ x, d.st.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = false

/-- **From d to d' nothing of message o's shape, ledger, mark "sampled" and pad has turned**, nor
the codes. -/
def SameAt (d : DState L) (d' : DState M) (o : ℕ) : Prop :=
  d'.st.codes = d.st.codes ∧ ∀ x, d.st.oracles[o]? = some x →
    ∃ x', d'.st.oracles[o]? = some x' ∧ x'.shape = x.shape ∧ x'.ledger = x.ledger ∧
      x'.sampled = x.sampled ∧ x'.pad = x.pad

theorem SameAt.refl (d : DState L) (o : ℕ) : SameAt d d o :=
  ⟨rfl, fun x hx => ⟨x, hx, rfl, rfl, rfl, rfl⟩⟩

theorem SameAt.trans {d : DState L} {d' : DState M} {d'' : DState N} {o : ℕ} (h : SameAt d d' o)
    (h' : SameAt d' d'' o) : SameAt d d'' o :=
  ⟨h'.1.trans h.1, fun x hx => by
    obtain ⟨x', hx', a, b, c, p⟩ := h.2 x hx
    obtain ⟨x'', hx'', a', b', c', p'⟩ := h'.2 x' hx'
    exact ⟨x'', hx'', a'.trans a, b'.trans b, c'.trans c, p'.trans p⟩⟩

theorem LeftIs.same {d : DState L} {d' : DState M} {o n : ℕ} {s : OracleShape}
    (h : LeftIs d o n s) (k : SameAt d d' o) : LeftIs d' o n s := by
  obtain ⟨x, l, hx, hs, hl, r⟩ := h
  obtain ⟨x', hx', a, b, -⟩ := k.2 x hx
  exact ⟨x', l, hx', a.trans hs, b.trans hl, r⟩

theorem Bare.same {d : DState L} {d' : DState M} {o : ℕ} {s : OracleShape} (h : Bare d o s)
    (k : SameAt d d' o) : Bare d' o s := by
  obtain ⟨x, hx, hs, hb⟩ := h
  obtain ⟨x', hx', a, -, c, -⟩ := k.2 x hx
  exact ⟨x', hx', a.trans hs, c.trans hb⟩

/-- The library's word for a ledger behind k takes travels too. -/
theorem ledgerAt_same {d : DState L} {d' : DState M} {o k : ℕ} (h : LedgerAt d.st o k)
    (s : SameAt d d' o) : LedgerAt d'.st o k := by
  obtain ⟨x, l, hx, hl, r⟩ := h
  obtain ⟨x', hx', a, b, -⟩ := s.2 x hx
  refine ⟨x', l, hx', b.trans hl, ?_⟩
  rw [a, s.1]
  exact r

/-- Message o is there, and its pad lies in its mask table, from the index `padFirst` on. -/
def PadAbove (d : DState L) (o : ℕ) : Prop :=
  ∃ x, d.st.oracles[o]? = some x ∧ ∀ q ∈ x.pad, q.1 = Part.mask ∧ padFirst d.st.codes x.shape ≤ q.2

theorem PadAbove.same {d : DState L} {d' : DState M} {o : ℕ} (h : PadAbove d o)
    (k : SameAt d d' o) : PadAbove d' o := by
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨x', hx', a, -, -, p⟩ := k.2 x hx
  refine ⟨x', hx', ?_⟩
  rw [p, a, k.1]
  exact hp

theorem LeftIs.shapeIs {d : DState L} {o n : ℕ} {s : OracleShape} (h : LeftIs d o n s) :
    ShapeIs d o d.st.codes s := by
  obtain ⟨x, _, hx, hs, -⟩ := h
  exact ⟨rfl, x, hx, hs⟩

theorem LeftIs.room {d : DState L} {o n m : ℕ} {s : OracleShape} (h : LeftIs d o n s)
    (hm : m ≤ n) : Room d o m := by
  obtain ⟨x, l, h1, -, h2, h3, h4⟩ := h
  exact ⟨x, l, h1, h2, h3, by omega⟩

theorem lt_of_some {α : Type} {a : Array α} {o : ℕ} {x : α} (h : a[o]? = some x) : o < a.size := by
  rcases Nat.lt_or_ge o a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h
    cases h

/-- A message with a ledger has a number below the number of messages. -/
theorem LeftIs.lt {d : DState L} {o n : ℕ} {s : OracleShape} (h : LeftIs d o n s) :
    o < d.st.oracles.size := by
  obtain ⟨x, _, hx, -⟩ := h
  exact lt_of_some hx

end Words

/-! ## 2. The ground's steps -/

section Steps
variable {L : Type}

/-! ### Entries are taken -/

theorem takeMask_laws {d d' : DState L} {o i : ℕ} (e : takeMaskP d o = some (i, d')) :
    (∀ n s, LeftIs d o (n + 1) s → LeftIs d' o n s) ∧ (∀ o', o' ≠ o → SameAt d d' o') ∧
      d'.st.groups = d.st.groups ∧ (PadAbove d o → PadAbove d' o) := by
  unfold takeMaskP at e
  split at e
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => rw [hl] at e; cases e
    | some l =>
      rw [hl] at e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨-, rfl⟩ := e
      refine ⟨?_, fun o' hne => ⟨rfl, fun x hx => ⟨x, by
        show (d.st.oracles.modify o _)[o']? = _
        rw [Array.getElem?_modify, if_neg (fun e => hne e.symm)]
        exact hx, rfl, rfl, rfl, rfl⟩⟩, rfl, ?_⟩
      swap
      · rintro ⟨x, hx, hp⟩
        refine ⟨{ x with ledger := some { l with
          next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1
          left := l.left - 1 } }, ?_, hp⟩
        show (d.st.oracles.modify o _)[o]? = _
        rw [Array.getElem?_modify, if_pos rfl, hx]
        rfl
      rintro n s ⟨x, l', hx, hs, hl', hc, hn⟩
      rw [hx] at hl
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
      let l₁ : Ledger :=
        { l' with
          next := Blk.nextRealRow l'.rows l'.logRows (2 ^ l'.logRows) l'.next + 1
          left := l'.left - 1 }
      refine ⟨{ x with ledger := some l₁ }, l₁, ?_, hs, rfl, hc, ?_⟩
      · show (d.st.oracles.modify o _)[o]? = _
        rw [Array.getElem?_modify, if_pos rfl, hx]
        rfl
      · show l'.left - 1 = n
        omega
  · cases e

theorem takeInto_laws {o : ℕ} : ∀ (n : ℕ) (d d' : DState L) (acc : Array ℕ) (l : List ℕ),
    takeMasksInto o n d acc = some (l, d') →
    (∀ m s, LeftIs d o (n + m) s → LeftIs d' o m s) ∧ (∀ o', o' ≠ o → SameAt d d' o') ∧
      d'.st.groups = d.st.groups ∧ (PadAbove d o → PadAbove d' o)
  | 0, d, d', acc, l, e => by
    have e' : some (acc.toList, d) = some (l, d') := e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e')
    exact ⟨fun m s h => by simpa using h, fun o' _ => SameAt.refl d o', rfl, id⟩
  | n + 1, d, d', acc, l, e => by
    unfold takeMasksInto at e
    cases ht : takeMaskP d o with
    | none => rw [ht] at e; cases e
    | some y =>
      obtain ⟨i, d₁⟩ := y
      rw [ht] at e
      obtain ⟨r1, k1, g1, p1⟩ := takeMask_laws ht
      obtain ⟨r2, k2, g2, p2⟩ := takeInto_laws n d₁ d' (acc.push i) l e
      exact ⟨fun m s h => r2 m s (r1 _ s (by rwa [Nat.add_right_comm] at h)),
        fun o' hne => (k1 o' hne).trans (k2 o' hne), g2.trans g1, p2 ∘ p1⟩

/-- **Behind the taking of n entries**: a ledger with just n + m left has just m left; the library's
count of takes has gone up by n, and every index given lies within the mask table; the other
messages stay. -/
theorem takeMasks_laws {d d' : DState L} {o n : ℕ} {l : List ℕ}
    (e : takeMasksP d o n = some (l, d')) :
    (∀ m s, LeftIs d o (n + m) s → LeftIs d' o m s) ∧
      (∀ k, LedgerAt d.st o k →
        LedgerAt d'.st o (k + n) ∧ ∀ i ∈ l, i < tableSize d.st o .mask) ∧
      (∀ o', o' ≠ o → SameAt d d' o') ∧ d'.st.groups = d.st.groups ∧
      (PadAbove d o → PadAbove d' o) := by
  obtain ⟨a, b, c, p⟩ := takeInto_laws n d d' #[] l e
  refine ⟨a, fun k h => ?_, b, c, p⟩
  obtain ⟨w1, -, w3⟩ := takeMasksP_within h e
  exact ⟨w3, w1⟩

/-! ### Messages are received -/

theorem recv_keeps {ft : ℕ} {d d' : DState L} {sent : Array OracleNotice} {ns : Array ℕ}
    (e : recvP ft d sent = some (ns, d')) :
    d'.st.codes = d.st.codes ∧ ns = (Array.range sent.size).map (· + d.st.oracles.size) ∧
      d'.st.oracles = d.st.oracles ++ sent.map fun n => { shape := n.shape } := by
  unfold recvP at e
  split at e
  · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨rfl, rfl, rfl⟩
  · cases e

theorem recv_same {ft : ℕ} {d d' : DState L} {sent : Array OracleNotice} {ns : Array ℕ}
    (e : recvP ft d sent = some (ns, d')) (o : ℕ) : SameAt d d' o :=
  ⟨(recv_keeps e).1, fun x hx => ⟨x, by
    rw [(recv_keeps e).2.2, Array.getElem?_append_left (lt_of_some hx)]
    exact hx, rfl, rfl, rfl, rfl⟩⟩

theorem recv_bare {ft : ℕ} {d d' : DState L} {sent : Array OracleNotice} {ns : Array ℕ}
    (e : recvP ft d sent = some (ns, d')) {i : ℕ} (hi : i < sent.size) :
    Bare d' (d.st.oracles.size + i) sent[i].shape := by
  refine ⟨{ shape := sent[i].shape }, ?_, rfl, rfl⟩
  have hle : d.st.oracles.size ≤ d.st.oracles.size + i := Nat.le_add_right _ _
  have hsub : d.st.oracles.size + i - d.st.oracles.size = i := Nat.add_sub_cancel_left ..
  rw [(recv_keeps e).2.2, Array.getElem?_append_right hle, hsub, Array.getElem?_map,
    Array.getElem?_eq_getElem hi]
  rfl

/-! ### A sample's answers are in: the ledger is laid -/

/-- The entries of a message's mask rows that are free for hidden values. -/
def freeOf (codes : Codes) (s : OracleShape) : ℕ :=
  Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers

theorem admit_laws {d d' : DState L} {o : ℕ} {rows : Array Row} (e : admitP d o rows = some d') :
    ∃ x, d.st.oracles[o]? = some x ∧
      (0 < x.shape.maskRows →
        LeftIs d' o (freeOf d.st.codes x.shape) x.shape ∧ LedgerAt d'.st o 0 ∧ PadAbove d' o) ∧
      ∀ o', o' ≠ o → SameAt d d' o' := by
  unfold admitP at e
  split at e
  · rename_i hok
    cases hx : d.st.oracles[o]? with
    | none => rw [hx] at e; cases e
    | some x =>
      rw [hx] at e
      cases hp : VerifiableInference.Desc.Own.padMade d.st.codes x.shape with
      | none =>
        simp only [Option.bind_eq_bind, Option.bind_some, hp, Option.bind_none] at e
        cases e
      | some places =>
        simp only [Option.bind_eq_bind, Option.bind_some, hp, Option.some.injEq] at e
        subst e
        have h1 : 1 ≤ x.shape.answers := by
          simp only [ok, admitL, hx, has, List.all_cons, List.all_nil, Bool.and_true,
            Bool.and_eq_true, Option.map_some, Option.getD_some, decide_eq_true_eq] at hok
          exact hok.2.2.2.2
        refine ⟨x, rfl, fun hm => ?_, fun o' hne => ⟨rfl, fun y hy => ⟨y, by
          show (d.st.oracles.modify o _)[o']? = _
          rw [Array.getElem?_modify, if_neg (fun e => hne e.symm)]
          exact hy, rfl, rfl, rfl, rfl⟩⟩⟩
        let l₁ : Ledger :=
          { next := 0
            left := freeOf d.st.codes x.shape
            rows := max x.shape.maskRows 1
            logRows := ceilLog2 x.shape.maskRows }
        let x₁ : Oracle :=
          { x with
            sampled := true
            sampleRows := rows
            pad := places.map fun p => (p.part, p.index)
            ledger := Slice.freshLedger d.st.codes x.shape }
        have hx₁ : (d.st.oracles.modify o fun x' => { x' with
            sampled := true
            sampleRows := rows
            pad := places.map fun p => (p.part, p.index)
            ledger := Slice.freshLedger d.st.codes x.shape })[o]? = some x₁ := by
          rw [Array.getElem?_modify, if_pos rfl, hx]
          rfl
        have hl₁ : x₁.ledger = some l₁ := by
          show Slice.freshLedger d.st.codes x.shape = _
          unfold Slice.freshLedger
          rw [if_pos hm]
          rfl
        refine ⟨⟨x₁, l₁, hx₁, rfl, hl₁, rfl, rfl⟩, ledgerAt_made (x := x₁) hx₁ hm h1 hl₁,
          x₁, hx₁, fun q hq => ?_⟩
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hq
        exact pad_above hm hp p hp'
  · cases e

/-! ### A new group; a message joins a group -/

theorem newGroup_same {d d' : DState L} {c m g : ℕ} (e : newGroupP d c m = some (g, d')) (o : ℕ) :
    SameAt d d' o := by
  unfold newGroupP at e
  split at e
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨rfl, fun x hx => ⟨x, hx, rfl, rfl, rfl, rfl⟩⟩
  · cases e

theorem join_same {d d' : DState L} {g o' : ℕ} {kept : Bool} (e : joinP d g o' kept = some d')
    (o : ℕ) : SameAt d d' o := by
  unfold joinP at e
  split at e
  · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 e
    by_cases ho : o = o'
    · subst ho
      refine ⟨rfl, fun x hx => ⟨{ x with groups := x.groups ++ [g] }, ?_, rfl, rfl, rfl, rfl⟩⟩
      show (d.st.oracles.modify o _)[o]? = _
      rw [Array.getElem?_modify, if_pos rfl, hx]
      rfl
    · refine ⟨rfl, fun x hx => ⟨x, ?_, rfl, rfl, rfl, rfl⟩⟩
      show (d.st.oracles.modify o' _)[o]? = _
      rw [Array.getElem?_modify, if_neg (fun e => ho e.symm)]
      exact hx
  · cases e

/-- Group g is there, with the one member o, no open row, and no test begun. -/
def GroupIs (d : DState L) (g o : ℕ) : Prop :=
  ∃ G, d.st.groups[g]? = some G ∧ G.members = #[o] ∧ G.rows = #[] ∧ G.inRun = false

/-- A new group that one message joins. -/
theorem group_made {d d₁ d₂ : DState L} {c m g o : ℕ} {kept : Bool}
    (e1 : newGroupP d c m = some (g, d₁)) (e2 : joinP d₁ g o kept = some d₂) : GroupIs d₂ g o := by
  unfold newGroupP at e1
  split at e1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
    unfold joinP at e2
    split at e2
    · obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 e2
      have hG' : (d.st.groups.push { code := c, maskCode := m })[d.st.groups.size]? = some G := hG
      rw [Array.getElem?_push_size] at hG'
      obtain rfl := Option.some.inj hG'
      let G₀ : OnBytes.Group := { code := c, maskCode := m }
      let G₁ : OnBytes.Group :=
        { G₀ with
          members := G₀.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o
          kept := G₀.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size kept }
      refine ⟨G₁, ?_, ?_, rfl, rfl⟩
      · show ((d.st.groups.push { code := c, maskCode := m }).modify d.st.groups.size _)[
          d.st.groups.size]? = _
        rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_push_size]
        rfl
      · show (#[] : Array ℕ).insertIdxIfInBounds ((#[] : Array ℕ).filter (· < o)).size o = #[o]
        simp [Array.insertIdxIfInBounds]
    · cases e2
  · cases e1

/-! ### A sending's messages are admitted one by one -/

theorem named_bind_ok {α β : Type} {nm : String} {x : Option α} {f : α → Except String β} {r : β}
    (h : (named nm x).bind f = .ok r) : ∃ a, x = some a ∧ f a = .ok r := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem layRows_laws {codes : Codes} {seeds : List (List E × E)} :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DState L),
      VerifiableInference.Desc.K1.layRows codes seeds l ys d = .ok d' → (l.map (·.1)).Nodup →
      (∀ y ∈ l, Bare d y.1 y.2) →
      (∀ y ∈ l, y.2.answers ≠ 0 → 0 < y.2.maskRows →
          LeftIs d' y.1 (freeOf d.st.codes y.2) y.2 ∧ LedgerAt d'.st y.1 0 ∧ PadAbove d' y.1) ∧
        ∀ o, o ∉ l.map (·.1) → SameAt d d' o
  | [], ys, d, d', e, _, _ => by
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · cases e
      exact ⟨(fun _ hy => by cases hy), fun o _ => SameAt.refl d o⟩
    · cases e
  | (o, s) :: l, ys, d, d', e, hn, hb => by
    have hn' : (l.map (·.1)).Nodup := (List.nodup_cons.1 hn).2
    have ho : o ∉ l.map (·.1) := (List.nodup_cons.1 hn).1
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · rename_i h0
      have h0' : s.answers = 0 := by simpa using h0
      obtain ⟨a, k⟩ := layRows_laws l ys d d' e hn'
        fun y hy => hb y (List.mem_cons_of_mem _ hy)
      refine ⟨fun y hy ha hm => ?_, fun o' hne => k o'
        (fun hh => hne (List.mem_cons_of_mem _ hh))⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd h0' ha
      · exact a y hy ha hm
    · split at e
      · cases e
      · split at e
        · cases e
        · dsimp only at e
          obtain ⟨d₁, ha, e'⟩ := named_bind_ok e
          obtain ⟨x, hx, a1, k1⟩ := admit_laws ha
          obtain ⟨x', hx', hs', -⟩ := hb (o, s) (List.mem_cons_self ..)
          obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
          have hne : ∀ y ∈ l, y.1 ≠ o := fun y hy hh => ho (hh ▸ List.mem_map_of_mem hy)
          obtain ⟨a, k⟩ := layRows_laws l _ d₁ d' e' hn' fun y hy =>
            (hb y (List.mem_cons_of_mem _ hy)).same (k1 y.1 (hne y hy))
          refine ⟨fun y hy hy0 hm => ?_, fun o' hno => ?_⟩
          · rcases List.mem_cons.1 hy with rfl | hy
            · obtain ⟨q1, q2, q3⟩ := a1 (hs' ▸ hm)
              rw [hs'] at q1
              exact ⟨q1.same (k o ho), ledgerAt_same q2 (k o ho), q3.same (k o ho)⟩
            · have c1 : d₁.st.codes = d.st.codes := (k1 y.1 (hne y hy)).1
              rw [← c1]
              exact a y hy hy0 hm
          · have h1 : o' ≠ o := fun hh => hno (hh ▸ List.mem_cons_self ..)
            exact (k1 o' h1).trans (k o' fun hh => hno (List.mem_cons_of_mem _ hh))

/-! ### A sending's decision -/

theorem named_ok {α : Type} {nm : String} {x : Option α} {a : α} (h : named nm x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some b => cases h; rfl

theorem mem_all {sent : Array OracleNotice} {n0 : ℕ} {y : ℕ × OracleShape}
    (hy : y ∈ ((Array.range sent.size).map (· + n0)).toList.zip (sent.toList.map (·.shape))) :
    ∃ i, ∃ hi : i < sent.size, y = (n0 + i, sent[i].shape) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
  have hk' : k < sent.size := by simpa using hk
  exact ⟨k, hk', by simp [List.getElem_zip, Nat.add_comm]⟩

theorem all_mem {sent : Array OracleNotice} {n0 i : ℕ} (hi : i < sent.size) :
    (n0 + i, sent[i].shape) ∈
      ((Array.range sent.size).map (· + n0)).toList.zip (sent.toList.map (·.shape)) := by
  refine List.mem_iff_getElem.2 ⟨i, by simpa using hi, ?_⟩
  simp [List.getElem_zip, Nat.add_comm]

theorem all_nodup (sent : Array OracleNotice) (n0 : ℕ) :
    ((((Array.range sent.size).map (· + n0)).toList.zip
      (sent.toList.map (·.shape))).map (·.1)).Nodup := by
  rw [List.map_fst_zip (by simp)]
  simp only [Array.toList_map, Array.toList_range]
  exact List.Nodup.map (fun a b h => Nat.add_right_cancel h) List.nodup_range

/-- **Behind a sending's decision**: the new messages have the next numbers; each that is sampled
and has mask rows has its ledger open with all its free entries left, behind no take; the older
messages stay. -/
theorem decideSend_laws {P : VerifiableInference.Desc.K1.Par} {owed : Option ℕ} {d d' : DState L}
    {rs : List Fmt.RoundView} {ns : Array ℕ}
    (e : VerifiableInference.Desc.K1.decideSend P owed d rs = .ok (ns, d')) :
    d'.st.codes = d.st.codes ∧ ns = (Array.range P.sent.size).map (· + d.st.oracles.size) ∧
      (∀ i, ∀ hi : i < P.sent.size, P.sent[i].shape.answers ≠ 0 → 0 < P.sent[i].shape.maskRows →
        LeftIs d' (d.st.oracles.size + i) (freeOf d.st.codes P.sent[i].shape) P.sent[i].shape ∧
          LedgerAt d'.st (d.st.oracles.size + i) 0 ∧ PadAbove d' (d.st.oracles.size + i)) ∧
      ∀ o, o < d.st.oracles.size → SameAt d d' o := by
  unfold VerifiableInference.Desc.K1.decideSend at e
  split at e
  · obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨x, hx, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨d₂, hl, e⟩ := bind_eq_ok e
    obtain ⟨ns', d₁⟩ := x
    have hr := named_ok hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    obtain ⟨c1, rfl, ho⟩ := recv_keeps hr
    obtain ⟨a, k⟩ := layRows_laws _ _ d₁ _ hl (all_nodup P.sent d.st.oracles.size) (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_all hy
      exact recv_bare hr hi)
    refine ⟨?_, rfl, fun i hi h0 hm => ?_, fun o hlt => ?_⟩
    · refine ((k (d.st.oracles.size + P.sent.size) fun hh => ?_).1).trans c1
      obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hh
      obtain ⟨i, hi, rfl⟩ := mem_all hy
      have : d.st.oracles.size + i = d.st.oracles.size + P.sent.size := hy'
      omega
    · rw [← c1]
      exact a _ (all_mem hi) h0 hm
    · refine (recv_same hr o).trans (k o fun hh => ?_)
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hh
      obtain ⟨i, hi, rfl⟩ := mem_all hy
      exact absurd hlt (Nat.not_lt.2 (Nat.le_add_right _ _))
  · cases e

end Steps

/-! ## 3. The key file's two sendings in front of the lookups, and the takings behind them -/

section Key
open VerifiableInference.Desc.Key
variable {β Cl : Type}

theorem map_ok {ε α γ : Type} {x : Except ε α} {f : α → γ} {c : γ} (h : x.map f = .ok c) :
    ∃ a, x = .ok a ∧ f a = c := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem sent_par (one : Params.OneTime) (piece : ℕ) (what : String) (msg : Array OracleNotice)
    (groups : List (List ℕ)) : (sendingPar one piece what msg groups).sent = msg := by
  simp [sendingPar, VerifiableInference.Desc.K1.Par.sent]

/-- **Behind a sending's seat**: the state's other fields stay; the statement is the sending's. -/
theorem seat_laws {name : String} {P : VerifiableInference.Desc.K1.Par} {s s' : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendingSeat (Cl := Cl) name P).decide s rs gs = .ok s') :
    s'.base = s.base ∧ s'.idx = s.idx ∧ s'.d.st.codes = s.d.st.codes ∧
      s'.sent = (Array.range P.sent.size).map (· + s.d.st.oracles.size) ∧
      (∀ i, ∀ hi : i < P.sent.size, P.sent[i].shape.answers ≠ 0 → 0 < P.sent[i].shape.maskRows →
        LeftIs s'.d (s.d.st.oracles.size + i) (freeOf s.d.st.codes P.sent[i].shape)
          P.sent[i].shape ∧ LedgerAt s'.d.st (s.d.st.oracles.size + i) 0 ∧
          PadAbove s'.d (s.d.st.oracles.size + i)) ∧
      ∀ o, o < s.d.st.oracles.size → SameAt s.d s'.d o := by
  obtain ⟨y, hy, rfl⟩ := map_ok e
  obtain ⟨x, hx, rfl⟩ := map_ok hy
  obtain ⟨ns, d'⟩ := x
  obtain ⟨c, hn, a, k⟩ := decideSend_laws hx
  exact ⟨rfl, rfl, c, hn, a, k⟩

/-- **Behind "idx.1.send"**: the index-mask message has the next number, which the state keeps; its
ledger is open with all its free entries left, behind no take. -/
theorem idx_laws {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendIndexMasks (Cl := Cl) one N groups).decide s rs gs = .ok s')
    (h0 : one.indexMasks.shape.answers ≠ 0) (hm : 0 < one.indexMasks.shape.maskRows) :
    s'.base = s.base ∧ s'.d.st.codes = s.d.st.codes ∧ s'.idx = s.d.st.oracles.size ∧
      LeftIs s'.d s'.idx (freeOf s.d.st.codes one.indexMasks.shape) one.indexMasks.shape ∧
      LedgerAt s'.d.st s'.idx 0 := by
  obtain ⟨s₁, h1, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from e)
  obtain ⟨b, -, c, hn, a, -⟩ := seat_laws h1
  rw [sent_par] at hn
  obtain ⟨i, hi, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from h2)
  have hi' := named_ok hi
  rw [hn] at hi'
  have hi0 : i = s.d.st.oracles.size := by simpa using hi'.symm
  obtain rfl := Except.ok.inj h2
  have a0 := a 0 (by rw [sent_par]; exact Nat.one_pos)
  simp only [sent_par] at a0
  obtain ⟨q1, q2, -⟩ := a0 h0 hm
  refine ⟨b, c, hi0, ?_, ?_⟩
  · show LeftIs s₁.d i _ _
    rw [hi0]
    exact q1
  · show LedgerAt s₁.d.st i 0
    rw [hi0]
    exact q2

theorem messageOf_head (x : Params.WfPublic) :
    ∃ h : 0 < (Wf.messageOf x).size, (Wf.messageOf x)[0] = x.message := by
  unfold Wf.messageOf
  split
  · split
    · exact ⟨Nat.succ_pos _, rfl⟩
    · exact ⟨Nat.succ_pos _, rfl⟩
  · exact ⟨Nat.succ_pos _, rfl⟩

/-- **Behind "msg.1.send"**: the lookups' own message has the next number, which is the one that the
parameters say; its ledger is open with all its free entries left, behind no take; it is a member
of the group that the state keeps as the ranges'; the older messages stay. -/
theorem msg_laws {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendOwnMessage (Cl := Cl) one N groups).decide s rs gs = .ok s')
    (h0 : one.ranges.message.shape.answers ≠ 0) (hm : 0 < one.ranges.message.shape.maskRows) :
    s'.base = s.base ∧ s'.idx = s.idx ∧ s'.d.st.codes = s.d.st.codes ∧
      one.ranges.messageId = s.d.st.oracles.size ∧
      LeftIs s'.d one.ranges.messageId (freeOf s.d.st.codes one.ranges.message.shape)
        one.ranges.message.shape ∧
      LedgerAt s'.d.st one.ranges.messageId 0 ∧ PadAbove s'.d one.ranges.messageId ∧
      GroupIs s'.d s'.grp one.ranges.messageId ∧
      ∀ o, o < s.d.st.oracles.size → SameAt s.d s'.d o := by
  obtain ⟨s₁, h1, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from e)
  obtain ⟨b, bi, c, hn, a, k⟩ := seat_laws h1
  obtain ⟨hz, hh⟩ := messageOf_head one.ranges
  have a0 := a 0 (by rw [sent_par]; exact hz)
  simp only [sent_par, hh] at a0 hn
  have h2' : openRangesGroup one s₁ = .ok s' := h2
  unfold openRangesGroup at h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨m, hmm, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, hid, h2'⟩ := bind_eq_ok h2'
  obtain ⟨g, hg, h2'⟩ := bind_eq_ok h2'
  obtain ⟨d₂, hj, h2'⟩ := bind_eq_ok h2'
  obtain rfl := Except.ok.inj h2'
  have hm0 := named_ok hmm
  rw [hn] at hm0
  have hm1 : m = s.d.st.oracles.size := by
    have : ((Array.range (Wf.messageOf one.ranges).size).map (· + s.d.st.oracles.size))[0]? =
        some (0 + s.d.st.oracles.size) := by
      simp [hz]
    rw [this] at hm0
    simpa using (Option.some.inj hm0).symm
  have hid' : m = one.ranges.messageId := by
    simpa using VerifiableInference.Desc.need_eq_ok hid
  have keep : ∀ o, SameAt s₁.d d₂ o := fun o =>
    (newGroup_same (g := g.1) (d' := g.2) (named_ok hg) o).trans (join_same (named_ok hj) o)
  obtain ⟨q1, q2, q3⟩ := a0 h0 hm
  refine ⟨b, bi, (keep 0).1.trans c, hid'.symm.trans hm1, ?_, ?_, ?_, ?_,
    fun o ho => (k o ho).trans (keep o)⟩
  · rw [← hid', hm1]
    exact q1.same (keep _)
  · rw [← hid', hm1]
    exact ledgerAt_same q2 (keep _)
  · rw [← hid', hm1]
    exact q3.same (keep _)
  · rw [← hid']
    exact group_made (g := g.1) (d₁ := g.2) (named_ok hg) (named_ok hj)

/-- **Behind both sendings**: the two messages differ; each ledger is open with all its free entries
left, behind no take; the ranges' group has the lookups' own message as its one member. -/
theorem front_laws {one : Params.OneTime} {N : Pieces} {g₁ g₂ : List (List ℕ)}
    {s s₁ s₂ : ChainState β} {rs₁ rs₂ : List Fmt.RoundView} {gs₁ gs₂ : List (List (ℕ × List UInt64))}
    (e₁ : (sendIndexMasks (Cl := Cl) one N g₁).decide s rs₁ gs₁ = .ok s₁)
    (e₂ : (sendOwnMessage (Cl := Cl) one N g₂).decide s₁ rs₂ gs₂ = .ok s₂)
    (i0 : one.indexMasks.shape.answers ≠ 0) (im : 0 < one.indexMasks.shape.maskRows)
    (m0 : one.ranges.message.shape.answers ≠ 0) (mm : 0 < one.ranges.message.shape.maskRows) :
    s₂.base = s.base ∧ s₂.d.st.codes = s.d.st.codes ∧ s₂.idx ≠ one.ranges.messageId ∧
      LeftIs s₂.d s₂.idx (freeOf s.d.st.codes one.indexMasks.shape) one.indexMasks.shape ∧
      LedgerAt s₂.d.st s₂.idx 0 ∧
      LeftIs s₂.d one.ranges.messageId (freeOf s.d.st.codes one.ranges.message.shape)
        one.ranges.message.shape ∧
      LedgerAt s₂.d.st one.ranges.messageId 0 ∧ PadAbove s₂.d one.ranges.messageId ∧
      GroupIs s₂.d s₂.grp one.ranges.messageId := by
  obtain ⟨b1, c1, -, l1, t1⟩ := idx_laws e₁ i0 im
  obtain ⟨b2, i2, c2, hid, l2, t2, p2, gr, k2⟩ := msg_laws e₂ m0 mm
  refine ⟨b2.trans b1, c2.trans c1, ?_, ?_, ?_, c1 ▸ l2, t2, p2, gr⟩
  · rw [i2, hid]
    exact Nat.ne_of_lt l1.lt
  · rw [i2]
    exact l1.same (k2 _ l1.lt)
  · rw [i2]
    exact ledgerAt_same t1 (k2 _ l1.lt)

/-- **Behind a link's two takings**: by exact counts, in both words; and every index given lies
within its message's mask table. -/
theorem behind_takings {L : Type} {d d₁ d₂ : DState L} {msg idx n₁ n₂ a b k₁ k₂ : ℕ}
    {o k : List ℕ} {s t : OracleShape} (hne : idx ≠ msg) (h1 : LeftIs d msg (n₁ + a) s)
    (h2 : LeftIs d idx (n₂ + b) t) (t1 : LedgerAt d.st msg k₁) (t2 : LedgerAt d.st idx k₂)
    (e1 : takeMasksP d msg n₁ = some (o, d₁)) (e2 : takeMasksP d₁ idx n₂ = some (k, d₂)) :
    LeftIs d₂ msg a s ∧ LeftIs d₂ idx b t ∧ LedgerAt d₂.st msg (k₁ + n₁) ∧
      LedgerAt d₂.st idx (k₂ + n₂) ∧ (∀ i ∈ o, i < tableSize d.st msg .mask) ∧
      (∀ i ∈ k, i < tableSize d₁.st idx .mask) ∧ d₂.st.groups = d.st.groups ∧
      (∀ i ∈ o, i < padFirst d.st.codes s) ∧ (PadAbove d msg → PadAbove d₂ msg) := by
  obtain ⟨r1, w1, k1, g1, p1⟩ := takeMasks_laws e1
  obtain ⟨r2, w2, k2, g2, -⟩ := takeMasks_laws e2
  have hne' : msg ≠ idx := fun e => hne e.symm
  obtain ⟨u1, v1⟩ := w1 k₁ t1
  obtain ⟨u2, v2⟩ := w2 k₂ (ledgerAt_same t2 (k1 idx hne))
  exact ⟨(r1 a s h1).same (k2 msg hne'), r2 b t (h2.same (k1 idx hne)),
    ledgerAt_same u1 (k2 msg hne'), u2, v1, v2, g2.trans g1, takes_below t1 h1.shapeIs e1,
    fun p => (p1 p).same (k2 msg hne')⟩

/-- **The count that the batching of the rows on the table asks**: where the index-mask message's
ledger has just n entries left and n and the lookups' entries add up to all its free entries, the
test «the ledger has handed out just the lookups' entries» of `layPile` holds. -/
theorem pile_count {one : Params.OneTime} {s : ChainState β} {n : ℕ} {t : OracleShape}
    (h : LeftIs s.d s.idx n t)
    (hn : n + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) = freeOf s.d.st.codes t) :
    ∃ o l, s.d.st.oracles[s.idx]? = some o ∧ o.ledger = some l ∧
      (l.left + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) ==
        Send.freeMaskEntries o.shape.maskRows
          (s.d.st.codes.mask.getD o.shape.maskCode default).ell o.shape.answers) = true := by
  obtain ⟨o, l, ho, hs, hl, -, hleft⟩ := h
  refine ⟨o, l, ho, hl, ?_⟩
  rw [hleft, hs, beq_iff_eq]
  exact hn

end Key

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.ledgerAt_same
#print axioms AtPublicFiles.KeyLookup.takeMasks_laws
#print axioms AtPublicFiles.KeyLookup.admit_laws
#print axioms AtPublicFiles.KeyLookup.group_made
#print axioms AtPublicFiles.KeyLookup.layRows_laws
#print axioms AtPublicFiles.KeyLookup.decideSend_laws
#print axioms AtPublicFiles.KeyLookup.seat_laws
#print axioms AtPublicFiles.KeyLookup.idx_laws
#print axioms AtPublicFiles.KeyLookup.msg_laws
#print axioms AtPublicFiles.KeyLookup.front_laws
#print axioms AtPublicFiles.KeyLookup.behind_takings
#print axioms AtPublicFiles.KeyLookup.pile_count
