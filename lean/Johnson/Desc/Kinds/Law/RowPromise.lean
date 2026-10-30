-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowPromise.lean: what stands behind the output head's own rounds' block
(Head.blockOf W l), at every transcript on which its step goes on. Stated and proved.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  decide_record: the record behind, written out: the record in front stands in the head's link,
      opened, without a mark, and the record behind is that record with three fields of the link's
      own part laid anew: the ledger F, what was heard x, the squares' level's state squaresP.
      Nothing else of the record turns.
  marked_refused: at a marked record the block refuses; and it lays no mark.
  rides: any reading of the record that does not hang on these three fields is as it was.
  wellLaid_later, cEnd_later: a ledger later than a WellLaid one is WellLaid; numbers filled in a
      ledger are filled in every later one.
  K6After W s': on the record behind alone: no mark; the ledger WellLaid; the lookup's last claim's
      numbers filled; the two readers of the lookup's hearing agree in its points.
  K6Kept W s s': on both records: a later ledger; the same request, token and hearing of the lookup.
  K6Behind W s s': both, AND THE TWO READERS OF THE LOOKUP'S HEARING AGREE WHOLE: S.look? and
      S.lookHeard? give one value behind the block.
  RowPromiseStatement, rowPromise: K6On in front gives K6Behind, whatever is drawn.
  unmarked_both: where the block's step goes on, neither record bears a mark.

Why the whole equation stands beside K6After's last clause. K6After's clause speaks of the lookup's
points alone (zx, zk), so that it can be tested as a Bool on a record (Law/K6OnB.lean). The block
proves more (Law/RowPins.lean: look_behind), and the text that reads x.g1 behind this block
(Johnson/Desc/K8/ReadsQuiet.lean: tables) reads more: the shape and the two points zb0 and zb1, for
the weights of the planes' tables. K6After is left as it was.

What it does not say. K6Kept speaks of both records: it is not in the form of a promise on the
record behind alone. THE TABLE OF JOINTS' OWN PROMISE BEHIND A BLOCK (its book-keeping Bool; the
samples of the open pins are held; every leaf shown; no collision; the stored table decodes) IS NOT
STATED HERE: it was typed over another form of the carried record than this file. What is given is
that from which it would ride: each of its clauses reads the strings, which no step turns, and
fields of the record that decide_record leaves: THAT IT READS NO OTHER FIELD IS NOT SHOWN: it is to
be held where the two are joined. Nothing on chance. No values are shown at which K6On holds.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S HeadOwn)

/-- On the record behind alone: no mark; the ledger WellLaid; what the lookup has heard has its last
claim's numbers filled; the two readers of that hearing agree in the lookup's points. -/
def K6After (W : OnBytes.Model.Verify.Public) (s' : S) : Prop :=
  s'.failed = none ∧ WellLaid ((seatAt W.hS (readsOf W)).ledger s') ∧
    (∀ gk, s'.lookHeard? = some gk → CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s')) ∧
    pointsOf s'.look? = pointsOf s'.lookHeard?

/-- On both records (for the riding of other blocks' items past this one): a later ledger; the same
request, token and hearing of the lookup. -/
def K6Kept (W : OnBytes.Model.Verify.Public) (s s' : S) : Prop :=
  Later ((seatAt W.hS (readsOf W)).ledger s) ((seatAt W.hS (readsOf W)).ledger s') ∧
    (seatAt W.hS (readsOf W)).request s' = (seatAt W.hS (readsOf W)).request s ∧
    Reply.token (seatAt W.hS (readsOf W)).toSeat s' =
      Reply.token (seatAt W.hS (readsOf W)).toSeat s ∧
    s'.lookHeard? = s.lookHeard?

/-- Both, and the two readers of the lookup's hearing agree whole behind the block. -/
def K6Behind (W : OnBytes.Model.Verify.Public) (s s' : S) : Prop :=
  K6After W s' ∧ K6Kept W s s' ∧ s'.look? = s'.lookHeard?

/-- **What stands behind the block's step, whatever is drawn.** -/
def RowPromiseStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (firstTree : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    K6On W s → b.step firstTree s rs cols = .ok (s', n) → K6Behind W s s'

namespace Came

/-- **THE RECORD BEHIND, WRITTEN OUT.** -/
theorem decide_record (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (a : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      s.here = .head a ∧ a.opened = true ∧ s.failed = none ∧
      s' = { s with here := .head { a with F := F1, x := some X, squaresP := some Q } } := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨F, H, w, s1, s2, e1, e2, rfl⟩ := decideBy_ok hd'
  have e1' : s.putFork? F = .ok s1 := e1
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  have hun : s.putFork F = s1 ∧ s1.failed = none := by
    unfold S.putFork? at e1'
    rw [if_pos hsome] at e1'
    exact (S.unmarked_ok _ _).mp e1'
  obtain ⟨rfl, hf⟩ := hun
  cases hh : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · have hp : s.putFork F = { s with here := .head { a with F := F } } := by
        simp [S.putFork, hh, hop]
      rw [hp] at e2 hf
      unfold seatAt at e2
      dsimp only at e2
      cases hx : a.lookHeard with
      | none =>
        rw [hx] at e2
        cases e2
      | some x =>
        rw [hx] at e2
        simp only [Except.ok.injEq] at e2
        rw [← hx] at e2
        exact ⟨a, F, _, _, rfl, hop, hf, e2.symm⟩
    · simp [S.fork?, hh, hop] at hsome
  | lay a =>
    exfalso
    have hp : (s.putFork F).here = .lay { a with F := F } := by simp [S.putFork, hh]
    obtain ⟨o, _, ho, _⟩ := setHeard_ok h iU3 e2
    rw [hp] at ho
    cases ho
  | att a =>
    exfalso
    have hp : (s.putFork F).here = .att { a with F := F } := by simp [S.putFork, hh]
    obtain ⟨o, _, ho, _⟩ := setHeard_ok h iU3 e2
    rw [hp] at ho
    cases ho
  | between => simp [S.fork?, hh] at hsome
  | fin a => simp [S.fork?, hh] at hsome
  | mem a => simp [S.fork?, hh] at hsome

/-- **At a marked record the block refuses; and it lays no mark.** -/
theorem marked_refused (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    s.failed = none ∧ s'.failed = none := by
  obtain ⟨a, F1, X, Q, _, _, hf, rfl⟩ := decide_record h iU3 work l hd
  exact ⟨hf, hf⟩

/-- **Any reading of the record that does not hang on the three fields is as it was.** -/
theorem rides {α : Type} (f : S → α)
    (hfr : ∀ (s : S) (a : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard)
      (Q : OnBytes.Model.Psc), s.here = .head a →
      f { s with here := .head { a with F := F1, x := some X, squaresP := some Q } } = f s)
    (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) : Leaves f (blockAt h iU3 work l) := by
  intro s rs gs s' hd
  obtain ⟨a, F1, X, Q, ha, _, _, rfl⟩ := decide_record h iU3 work l hd
  exact hfr s a F1 X Q ha

theorem wellLaid_later {F G : Fork} (hW : WellLaid F) (hL : Later F G) : WellLaid G := by
  obtain ⟨a, b, c⟩ := hL.sized (sized_of hW)
  exact ⟨c, a, b⟩

theorem cEnd_later {gk : OnBytes.Model.Forest.Heard} {F G : Fork} (hL : Later F G)
    (h : CEndFilled gk F) : CEndFilled gk G :=
  fun x hx => (hL.keep x.1 (h x hx)).1

theorem rowPromise : RowPromiseStatement := by
  intro W l b hb firstTree s rs cols s' n hon hstep
  obtain ⟨gs, hd⟩ := step_decide firstTree b s rs cols s' n hstep
  obtain ⟨hWL, _, _, _, _, hfill⟩ := hon
  unfold blockOf at hb
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at hb
    simp at hb
  | some i =>
    rw [hU] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    have e : readsOf W = i := by
      unfold readsOf
      rw [hU]
      rfl
    unfold K6Behind K6After K6Kept
    rw [e] at hWL hfill ⊢
    have hL := blockAt_later W.hS i _ l s s' _ gs hd
    have hlk := lookHeard_leaves W.hS i _ l s _ gs s' hd
    have hlk' : s'.lookHeard? = s.lookHeard? := hlk
    obtain ⟨a, F1, X, Q, ha, _, hf, hs'⟩ := decide_record W.hS i _ l hd
    refine ⟨⟨(marked_refused W.hS i _ l hd).2, wellLaid_later hWL hL,
      fun gk hgk => cEnd_later hL (hfill gk (hlk' ▸ hgk)),
      congrArg pointsOf (look_behind W.hS i _ l hd)⟩, ⟨hL, ?_, ?_, hlk'⟩,
      look_behind W.hS i _ l hd⟩
    · rw [hs']
      rfl
    · rw [hs']
      rfl

/-- **Where the step of the block as it rides goes on, neither record bears a mark.** -/
theorem unmarked_both (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (firstTree : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (n : Nat) (hstep : b.step firstTree s rs cols = .ok (s', n)) :
    s.failed = none ∧ s'.failed = none := by
  obtain ⟨gs, hd⟩ := step_decide firstTree b s rs cols s' n hstep
  unfold blockOf at hb
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at hb
    simp at hb
  | some i =>
    rw [hU] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    exact marked_refused W.hS i _ l hd

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.unmarked_both
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.marked_refused
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowPromise
