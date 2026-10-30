-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/Rest9.lean: WHAT AN ACCEPTING STEP OF THE BATCHING, OF THE FRAME's
SUB-PROTOCOL BEHIND IT, AND OF THE SHUTTING WRITES INTO THE VERIFIER's STATE, SAID ONCE (our files
call a sub-protocol a block): NOTHING BUT THE COUNT OF ROWS THAT IS OWED AND, IN THE OPEN SEGMENT's
PART, THE LINK's CONTEXT, THE LEDGER AND THE APPROXIMATE RANGE PROOF's STATE. Definitions and
theorems.

Why. A public item of the table is a Bool on the verifier's state; that it is kept is owed by every
sub-protocol that it rides past, for every item that is open there: sub-protocols times items. The
cut that makes it a sum: a sub-protocol's files show once what its accepting step writes; an item's
files show once that its Bool reads none of that. This is the first half for three of a link's last
sub-protocols.

What is said.
  `rest9 L₀ F₀ t₀ s`: the state with no count of rows owed and, in the open segment's part, the
    three fields blanked to L₀, F₀, t₀. `ReadsRest9 f`: f does not turn when these are blanked.
    `ReadsRest9.alike`. `rests_rest9`: the four writings of KeepsAny.lean leave `rest9`.
    `rest_putLink`, `rest_set`: so do a writing of the link's context, and the lens's writing of a
    part with the statement that it has read. `rest_batch`, `rest_behind`, `rest_shut`: **`rest9 …
    s' = rest9 … s` at an accepting step of each of the three**, the first two from the same of
    every run of the link's orders. `rest_blocks`: these two with the runs' share in
    LinkAtSort.lean's general form. `kept_of_rest`: **whatever reads the rest alone is as it was
    behind each of the three.**

Limits. The statement is NOT blanked: these three leave it (`Rb`). The one equation's sub-protocol,
which turns the statement, is not here. Which public items read the rest alone is each item's
to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkAtSort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS Where shut closed)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.JoinAtBlocks

variable (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2)

/-- The open segment's part with the link's context, the ledger and the approximate range proof's
state blanked. -/
def here9 : Here → Here
  | .lay a => .lay { a with L := L₀, F := F₀, tl := t₀ }
  | .att a => .att { a with L := L₀, F := F₀, tl := t₀ }
  | .head a => .head { a with L := L₀, F := F₀, tl := t₀ }
  | h => h

/-- **The verifier's state without all that the three sub-protocols write.** -/
def rest9 (s : S) : S := { s with rowsOwed := none, here := here9 L₀ F₀ t₀ s.here }

/-- f does not turn when these are blanked. -/
def ReadsRest9 {β : Type} (f : S → β) : Prop := ∀ s, f (rest9 L₀ F₀ t₀ s) = f s

theorem ReadsRest9.alike {β : Type} {f : S → β} (h : ReadsRest9 L₀ F₀ t₀ f) {s s' : S}
    (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) : f s' = f s := by
  rw [← h s', ← h s, e]

/-- The four writings leave it. -/
theorem rests_rest9 : FieldRests (rest9 L₀ F₀ t₀) where
  tl s tl := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [rest9, here9, S.putTl, ho]
    | _ => rfl
  fork s G := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [rest9, here9, S.putFork, ho]
    | _ => rfl
  wrote e a G e₁ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold rest9
    rw [h1]
    rfl
  head s a G h := by
    unfold rest9
    rw [h]
    rfl

/-- A writing of the link's context leaves it. -/
theorem rest_putLink (s : S) (L : LinkCtx) : rest9 L₀ F₀ t₀ (s.putLink L) = rest9 L₀ F₀ t₀ s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [rest9, here9, S.putLink, ho]
  | _ => rfl

/-- The lens's writing of a part with the statement that it has read. -/
theorem rest_set (e : S) (q q' : K9.Part) (hq : atS.get? e = some q) (hd : q'.d.st = q.d.st) :
    rest9 L₀ F₀ t₀ (atS.set e q') = rest9 L₀ F₀ t₀ e := by
  have hst : q'.d.st = e.st := hd.trans (part_reads e q hq).2
  have e1 : rest9 L₀ F₀ t₀ (atS.set e q') =
      { rest9 L₀ F₀ t₀ ((e.putLink q'.L).putFork q'.F) with st := q'.d.st } := rfl
  rw [e1, (rests_rest9 L₀ F₀ t₀).fork, rest_putLink, hst]
  rfl

/-- **At the batching.** -/
theorem rest_batch (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      rest9 L₀ F₀ t₀ e₁ = rest9 L₀ F₀ t₀ e)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, _, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  have h0 : rest9 L₀ F₀ t₀ (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) =
      rest9 L₀ F₀ t₀ s := rest_set L₀ F₀ t₀ s a _ ha rfl
  have h1 : rest9 L₀ F₀ t₀ e = rest9 L₀ F₀ t₀ s :=
    gather_holds (fun x => rest9 L₀ F₀ t₀ x = rest9 L₀ F₀ t₀ s) (fun _ => []) []
      (runsIn L.hear L.order)
      (fun r' hr' n e0 c0 e1 hr0 hx => by
        obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
        obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
        exact (hk o' ho' run hrun n e0 c0 e1 hr0).trans hx) ([], _) (c, e)
      (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  exact (rest_set L₀ F₀ t₀ e q { q with F := G } hq rfl).trans h1

/-- **At the frame's sub-protocol behind the batching.** -/
theorem rest_behind (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      rest9 L₀ F₀ t₀ e₁ = rest9 L₀ F₀ t₀ e)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact ran_holds (fun x => rest9 L₀ F₀ t₀ x = rest9 L₀ F₀ t₀ s) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq))
    (fun o ho run hl x x₁ hr hx => (hk o ho run hl x x₁ hr).trans hx) rfl

/-- **At the shutting.** -/
theorem rest_shut {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₅.step ft s rs cols = .ok (s', k)) : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  obtain ⟨L, _, rfl⟩ := shut_inv pw piece _ _ _ _ _ k (hb₅ _ _ _ _ _ h)
  exact rest_putLink L₀ F₀ t₀ s _

/-- The first two, with the runs' share in its general form. -/
theorem rest_blocks (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (H : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B) :
    (∀ ft s rs cols s' k, L.batchB.step ft s rs cols = .ok (s', k) →
      rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) ∧
    ∀ ft s rs cols s' k, L.behindB.step ft s rs cols = .ok (s', k) →
      rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  have h := H _ (relRests_of_field (rests_rest9 L₀ F₀ t₀)) (rests_rest9 L₀ F₀ t₀).fork
  exact ⟨rest_batch L₀ F₀ t₀ L pp hb₁ h.1, rest_behind L₀ F₀ t₀ L h.2⟩

/-- **Whatever reads the rest alone is as it was.** -/
theorem kept_of_rest {β : Type} (f : S → β) (hf : ReadsRest9 L₀ F₀ t₀ f) (s s' : S)
    (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) : f s' = f s := hf.alike L₀ F₀ t₀ e

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_rest9
#print axioms VerifiableInference.Desc.LinkJoin.rest_set
#print axioms VerifiableInference.Desc.LinkJoin.rest_batch
#print axioms VerifiableInference.Desc.LinkJoin.rest_behind
#print axioms VerifiableInference.Desc.LinkJoin.rest_shut
#print axioms VerifiableInference.Desc.LinkJoin.rest_blocks
