-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawOrdered.lean: THE SMALLNESS TEST: BEHIND THE STEP THAT CLOSES THE LIST OF
TABLES THE GUARD OF ORDER HOLDS OF THE CARRIED RECORD ITSELF: AT ALL THREE KINDS OF LINK, AS A
READING THAT A FOLD CAN CARRY.

The step that closes the list asks the guard of order (`Order.orderOk`,
Johnson/Desc/First/K8/Order.lean) at the record that it then lays. Here that is said as one reading
of the carried record:
  `ordered s`: WITH CODE: where a link is open: whether the guard of order holds at the smallness
    test's record, the link's record and the statement that s holds.
  `layers_orders`, `head_orders`, `blockAt_orders` (Johnson/Desc/K8/ReadsQuiet.lean,
    ReadsQuietAt.lean), `attO_orders` (Johnson/Desc/First/Att/ReadsO.lean): **wherever such a step's
    decision goes on, `ordered` is yes behind it.**
  `lays_behind`: a reading that a block lays at one value, the block joined behind any other lays.
  `namedAt_of_ordered`: **`ordered s` = yes, with the invariants of
    Johnson/Desc/First/K8/LawBookNames.lean, gives `Named.namedAt p s` = yes.**
  `LinkLists a b a' b' B L`, `namedAt_of_lists`: **THE LIST OF WHAT IS OWED, IN THE FORMS IN WHICH
    THE SENDING BLOCKS' LAWS END, AND THAT IT IS ENOUGH**: the test on public values `earlyB` is
    gone: it follows from the guard of order where the link has had at most two moments.
Definitions, statements and proofs.
Limits. Those of LawBookNames.lean. The reading speaks of the record right behind the step: a block
between that step and the draw owes that it leaves `ordered`.

-/
import Johnson.Desc.First.K8.LawBookNames
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.First.K8.LawSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Named
open OnBytes OnBytes.Model

/-- Whether the guard of order holds at what the carried record holds. -/
def ordered (s : S) : Option Bool :=
  match s.tl?, s.link? with
  | some tl, some L => some (Order.orderOk tl L s.st)
  | _, _ => none

theorem ordered_spec {s : S} (h : ordered s = some true) :
    ∃ tl L, s.tl? = some tl ∧ s.link? = some L ∧ Order.orderOk tl L s.st = true := by
  unfold ordered at h
  cases ht : s.tl? with
  | none => simp [ht] at h
  | some tl =>
    cases hl : s.link? with
    | none => simp [ht, hl] at h
    | some L =>
      simp only [ht, hl, Option.some.injEq] at h
      exact ⟨tl, L, rfl, rfl, h⟩

/-- Behind the closing step at a layers' link. -/
theorem layers_orders (P : VerifiableInference.Desc.K8.ReadsQuiet.PG) :
    (VerifiableInference.Desc.K8.ReadsQuiet.layers P).Lays ordered (fun _ => some true) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', _, _, hc, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_ok h
  obtain ⟨_, _, _, hO⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  subst e
  show (some (Order.orderOk tl' a.L s.st) : Option Bool) = some true
  rw [hO]

/-- At the head's link. -/
theorem head_orders (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) :
    (VerifiableInference.Desc.K8.ReadsQuiet.head P).Lays ordered (fun _ => some true) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', _, ho, _, _, _, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨_, _, _, hO⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  subst e
  have h1 : (S.tl? { s with here := .head { a with t := some t, tl := tl' } }) = some tl' := by
    simp [S.tl?, ho]
  have h2 : (S.link? { s with here := .head { a with t := some t, tl := tl' } }) = some a.L := by
    simp [S.link?, ho]
  unfold ordered
  rw [h1, h2]
  show (some (Order.orderOk tl' a.L s.st) : Option Bool) = some true
  rw [hO]

/-- At whichever block the maker of the two gives. -/
theorem blockAt_orders (G : Array Layer.HPlan2) (hS : Head.Shape) (HLy : Head.HL)
    (H : Head.HPlanH2) (kinds : List (Nat × Nat)) (l : Nat) (q : Block S Unit)
    (hq : VerifiableInference.Desc.K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) :
    q.Lays ordered (fun _ => some true) := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.blockAt at hq
  obtain ⟨k, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  split at hq
  · obtain ⟨hp, _, rfl⟩ := Option.map_eq_some_iff.1 hq
    exact layers_orders _
  · split at hq
    · obtain rfl := Option.some.inj hq
      exact head_orders _
    · exact nomatch hq

/-- At an attention link. -/
theorem attO_orders {Cl : Type} (W : Verify.Public) (l g : Nat) (z : Block S Cl)
    (hz : Att.readsAtO (Cl := Cl) W l g = some z) : z.Lays ordered (fun _ => some true) := by
  unfold Att.readsAtO at hz
  cases hA : W.A[g]? with
  | none => simp [hA] at hz
  | some A =>
    simp only [hA, Option.map_some, Option.some.injEq] at hz
    subst hz
    intro s rs gs s' h
    have h : Att.readsAtSO A s = .ok s' := h
    unfold Att.readsAtSO at h
    cases hh : s.here with
    | att a =>
      simp only [hh] at h
      obtain ⟨h5, _, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
      obtain ⟨g', _, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
      obtain ⟨r, hr, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
      obtain rfl : { s with here := .att { a with t := some r.1, tl := r.2.1 } } = s' := by
        simpa [pure, Except.pure] using h
      unfold Att.readsStepO at hr
      obtain ⟨_, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
      obtain ⟨_, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
      obtain ⟨t, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
      obtain ⟨tl', _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
      obtain ⟨_, hf, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
      obtain rfl : (Att.tabsBack t, tl', a.F.next) = r := by simpa [pure, Except.pure] using hr
      show (some (Order.orderOk tl' a.L s.st) : Option Bool) = some true
      rw [(VerifiableInference.Desc.K8.ReadsQuiet.front_ok hf).2.2]
    | _ => simp [hh] at h

/-- A reading that a block lays at one value, the block joined behind any other lays. -/
theorem lays_behind {Cl α : Type} {f : S → α} {v : α} {q : Block S Cl}
    (h : q.Lays f (fun _ => v)) (own : Block S Cl) (name : String) :
    (Block.andThen name own q).Lays f (fun _ => v) := by
  intro s rs gs s' H
  obtain ⟨t, _, H⟩ :=
    bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) H
  exact h _ _ _ _ H

/-- **From the reading and the invariants to the test at the carried record.** -/
theorem namedAt_of_ordered {p : Par} {s : S} {a b a' b' : Nat} (hO : ordered s = some true)
    (h1 : Book.BookFits s.book) (h2 : BookHas s)
    (hS : ∀ L, s.link? = some L → SentHere a b a' b' s.book L)
    (hE : ∀ tl L, s.tl? = some tl → s.link? = some L → earlyB tl L = true)
    (hM : ∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn)
    (hR : ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn) :
    namedAt p s = true := by
  obtain ⟨tl, L, ht, hl, ho⟩ := ordered_spec hO
  exact namedAt_of_inv ht hl h1 h2 (hS L hl) (hE tl L ht hl) ho hM hR

/-- What the link's two sendings, its opening and the shape owe of the open link's record L and the
book B, at the record in front of the draw. -/
structure LinkLists (a b a' b' : Nat) (B : TreeBook) (L : LinkCtx) : Prop where
  /-- the link's own messages: those of its first sending, then those of the sending of the reads -/
  own : ∃ own0 ids : Array Nat, L.check.frame.own = own0 ++ ids ∧
    (∀ o ∈ own0.toList, ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b) ∧
    (∀ o ∈ ids.toList, ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a' ≤ jt.1 ∧ jt.1 < b') ∧
    ∀ (j : Nat) (sh : Params.ReqLink) (m : Params.ReqMessage),
      L.check.frame.shape.link[L.check.frame.link]? = some sh → sh.messages[j]? = some m →
      (m.moment = 0 → j < own0.size) ∧ (m.moment = 1 → own0.size ≤ j)
  /-- the kept copies -/
  kept : ∀ o ∈ L.check.frame.keptBefore.toList,
    ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b
  /-- the frame's number of the link is the link's -/
  link : L.check.frame.link = L.link
  /-- the link has had at most two moments -/
  moments : L.moments ≤ 2

/-- **THE LIST OF WHAT IS OWED, AND THAT IT IS ENOUGH**: the guard of order at the record; the
book's two invariants; `LinkLists` at the open link; the place names the trees of the two
sendings. -/
theorem namedAt_of_lists {p : Par} {s : S} {a b a' b' : Nat} (hO : ordered s = some true)
    (h1 : Book.BookFits s.book) (h2 : BookHas s)
    (hL : ∀ L, s.link? = some L → LinkLists a b a' b' s.book L)
    (hM : ∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn)
    (hR : ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn) :
    namedAt p s = true := by
  obtain ⟨tl, L, ht, hl, ho⟩ := ordered_spec hO
  have hh := hL L hl
  obtain ⟨own0, ids, e, x0, x1, x3⟩ := hh.own
  exact namedAt_of_inv ht hl h1 h2 (sentHere_of_lists own0 ids e hh.kept x0 x1 x3)
    (earlyB_of_order ho hh.link hh.moments) ho hM hR

end VerifiableInference.Desc.First.K8.Named

#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_of_lists
#print axioms VerifiableInference.Desc.First.K8.Named.layers_orders
#print axioms VerifiableInference.Desc.First.K8.Named.head_orders
#print axioms VerifiableInference.Desc.First.K8.Named.blockAt_orders
#print axioms VerifiableInference.Desc.First.K8.Named.attO_orders
#print axioms VerifiableInference.Desc.First.K8.Named.lays_behind
#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_of_ordered
