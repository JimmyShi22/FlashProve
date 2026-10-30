-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OwedRides.lean: THE ROWS THAT ARE OWED A COUNT, OVER A LINK's FIRST TWO
PIECES: MADE BY THE BATCHING's DRAW, KEPT BY THE ADDING AND BY THE RUNS BEHIND IT. Theorems on the
blocks' steps, at the first chain's record.

Why. The one equation's piece gives the public sentence «the plan's claims and the ties' and reads'
indices are at most the batching round's rows» from its own yes, if in front of it the rows owed are
that round's (Johnson/Desc/First/Batch/Law/RowsRide.lean: `rows_hR3`). Who makes that fact, and who
keeps it? The batching kind's lens writes the field back on every adding, so the general tool for a
field that rests under the lens's writing does not fit: here is the field's own.

What is said.
  `drawn_owed`: the draw's return owes the round's rows. `owed_idem`, `owed_set`: the lens's writing
    of a part that it has read, whatever ledger is laid, leaves the reading of the rows owed.
    `owed_moves`: **along a row of moves each of which keeps that reading, it stays.** `owed_made`:
    **behind a yes of a block that is a draw with such moves behind it the rows owed are the
    round's**, if the round counts a row. `owed_kept`: a block that is a row of such moves keeps the
    reading.

Limits. The moves' duty is a premise: KeepsAny.lean pays it at each sort of link (`keeps_layers`,
`keeps_attention`, `keeps_head` at `rests_owed`), the lookup's runs' share aside. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.KeepsAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where owedOf drawn drawnClean)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)

/-- The draw's return owes the round's rows. -/
theorem drawn_owed (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ) (L : LinkCtx) (F : Fork)
    (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) : o.owed = some rows := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]

/-- What the lens's writing leaves for the reading of the rows owed. -/
theorem owed_of_set (s : S) (a : K9.Part) :
    owedOf (atS.set s a) = match a.owed with
      | some 0 => none
      | x => x := rfl

/-- The reading never gives «some 0». -/
theorem owed_idem (s : S) : (match owedOf s with
    | some 0 => none
    | x => x) = owedOf s := by
  unfold owedOf
  cases h : s.rowsOwed with
  | none => rfl
  | some r =>
    cases r with
    | zero => rfl
    | succ k => rfl

/-- The lens's writing of a part that it has read, whatever ledger is laid, leaves the reading. -/
theorem owed_set (e : S) (q : K9.Part) (hq : atS.get? e = some q) (G : Fork) :
    owedOf (atS.set e { q with F := G }) = owedOf e := by
  have ho : q.owed = owedOf e := by
    unfold atS at hq
    simp only [Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    rw [← Option.some.inj hq]
  rw [owed_of_set]
  show (match q.owed with
    | some 0 => none
    | x => x) = _
  rw [ho]
  exact owed_idem e

/-- **Along a row of moves each of which keeps the reading, it stays.** -/
theorem owed_moves : ∀ (ms : List (Move S)), (∀ m ∈ ms, MoveKeeps owedOf m) →
    ∀ (e e' : S) (c : List Claim), MovesYes atS ms e e' c → owedOf e' = owedOf e
  | [], _, e, e', c, hy => by
    obtain ⟨rfl, _⟩ := hy
    rfl
  | m :: l, hms, e, e', c, hy => by
    obtain ⟨x, c₁, c₂, h1, h2, _⟩ := hy
    have i := owed_moves l (fun q hq => hms q (List.mem_cons_of_mem _ hq)) x e' c₂ h2
    have hm := hms m List.mem_cons_self
    rw [i]
    cases m with
    | add g =>
      obtain ⟨e₁, s, G, hg, hs, _, rfl⟩ := h1
      rw [owed_set e₁ s hs G]
      exact hm e c₁ e₁ hg
    | quiet h => exact hm e x h1.1

/-- **Behind a yes of a draw with such moves behind it the rows owed are the round's.** -/
theorem owed_made {Cl : Type} (p : Where) (hp : p.rows ≠ 0) (ms : List (Move S)) (b : Block S Cl)
    (hb : DrawMoves atS p ms b) (hms : ∀ m ∈ ms, MoveKeeps owedOf m) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b.step ft s rs cols = .ok (s', k)) : owedOf s' = some p.rows := by
  obtain ⟨r, x, a, o, cls, _, _, _, hd, hy⟩ := hb ft s rs cols s' k h
  rw [owed_moves ms hms _ s' cls hy, owed_of_set]
  show (match o.owed with
    | some 0 => none
    | x => x) = _
  rw [drawn_owed _ _ _ _ _ _ _ hd]
  cases hr : p.rows with
  | zero => exact absurd hr hp
  | succ n => rfl

/-- A block that is a row of such moves keeps the reading. -/
theorem owed_kept {Cl : Type} (ms : List (Move S)) (b : Block S Cl) (hb : IsMoves atS ms b)
    (hms : ∀ m ∈ ms, MoveKeeps owedOf m) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) : owedOf s' = owedOf s := by
  obtain ⟨rs', gs, hd⟩ := step_decide b _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := hb.dec _ _ _ _ hd
  exact owed_moves ms hms _ _ cls hy

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.drawn_owed
#print axioms VerifiableInference.Desc.LinkJoin.owed_set
#print axioms VerifiableInference.Desc.LinkJoin.owed_moves
#print axioms VerifiableInference.Desc.LinkJoin.owed_made
#print axioms VerifiableInference.Desc.LinkJoin.owed_kept
