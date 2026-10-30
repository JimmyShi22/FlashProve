-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/CsHead.lean: the clauses meant for `rides` of the first chain's
`Thread`, as one written list.

The invariant has a part called `rides`: facts about the verifier's state that one sub-protocol of
the chain is meant to establish and a later sub-protocol is meant to use. Honest/Thread/Riders.lean
gives the form of such a clause (`RiderCl`) and builds `rides` from a list of clauses (`ridersOf`).
This file writes the list for the first chain at the full size.

  `csHead`   the list
  `csHead_length`   it has 55 clauses
  `csHead_mem`   membership in the list, written out
  `csHead_span`   the spans of its clauses, for arithmetic
  `staysBy_own`   the clause "the segment's own rounds have returned something" stays past a
     sub-protocol that leaves the field `own` of an open layers' segment as it was

Limits.
  * The list is a definition. Nothing here proves that any clause is established, is left as it is,
    or is enough for the sub-protocol that uses it.
  * Three parameters of the definition are left open (see its docstring).
  * The borders' numbers are written by hand: nothing here compares them with the description's flat
    list. Nothing here sets a `Thread`'s `rides` to this list.
  * This is not one of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

/-- The list of the clauses meant for `rides` of the first chain's `Thread` at the full size.

Such a clause says: from border `lo` to border `hi`, a stated fact about the verifier's state holds.
The sub-protocol just before border `lo` is meant to establish the fact after its step, the
sub-protocols between to leave it as it is, and a later sub-protocol to use it (the last at `hi`).
The list has 55 clauses:

* six facts about the output head's own part of the state;
* one fact after each segment's lookup on the digits (`st l`): 24 of span one, and the head's;
* one fact per attention segment: what the lookup on the calls returned (`R g` of the field `g`);
* one fact per layers' segment: the segment's own rounds have returned something.

Three parameters are left open. `ν` is a number: meant to be the ledger's next free slot after the
head's lookup on the digits. `st` and `R` are conditions whose definition belongs to the authors of
other kinds' lemmas. -/
def csHead {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) : List (RiderCl W S) :=
  [riderHead 342 347 (fun a => a.x.isSome = true),
    riderHead 343 348 (fun a => a.t.isSome = true),
    riderHead 347 352 (fun a => a.wo.isSome = true),
    riderHead 346 346 (fun a => a.F.next = ν),
    riderHead 344 345 (fun a => a.tl.foldDrawn = 0),
    riderHead 346 347 (fun a => a.tl.foldDrawn = 1),
    ⟨346, 347, fun _ _ s => st 24 s⟩] ++
  (List.range 24).map (fun l => ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩) ++
  (List.range 12).map (fun g =>
    riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g) ++
  (List.range 12).map (fun g => ⟨28 * g + 5, 28 * g + 10, fun _ _ s => ∃ o, s.own? = some o⟩)

/-- The list has 55 clauses. -/
theorem csHead_length {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) :
    (csHead (W := W) ν st R).length = 55 := rfl

/-- Membership in the list, written out: a clause of the list is one of the seven written clauses,
or the clause after the lookup on the digits of a segment l < 24, or the clause of the g-th
attention segment, or the clause of the g-th layers' segment, g < 12. -/
theorem csHead_mem {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (c : RiderCl W S) :
    c ∈ csHead ν st R ↔
      (((c = riderHead 342 347 (fun a => a.x.isSome = true) ∨
            c = riderHead 343 348 (fun a => a.t.isSome = true) ∨
            c = riderHead 347 352 (fun a => a.wo.isSome = true) ∨
            c = riderHead 346 346 (fun a => a.F.next = ν) ∨
            c = riderHead 344 345 (fun a => a.tl.foldDrawn = 0) ∨
            c = riderHead 346 347 (fun a => a.tl.foldDrawn = 1) ∨
            c = ⟨346, 347, fun _ _ s => st 24 s⟩) ∨
          ∃ l, l < 24 ∧ (⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩ : RiderCl W S) = c) ∨
        ∃ g, g < 12 ∧
          riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) (fun a => R g a.g) = c) ∨
      ∃ g, g < 12 ∧
        (⟨28 * g + 5, 28 * g + 10, fun _ _ s => ∃ o, s.own? = some o⟩ : RiderCl W S) = c := by
  unfold csHead
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false]

/-- The spans of the list's clauses, for arithmetic: a clause is between the borders 342 and 352, or
has the span of one of the three families. -/
theorem csHead_span {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {c : RiderCl W S}
    (h : c ∈ csHead ν st R) :
    (342 ≤ c.lo ∧ c.hi ≤ 352) ∨ (∃ l, l < 24 ∧ c.lo = 14 * l + 9 ∧ c.hi = 14 * l + 9) ∨
      (∃ g, g < 12 ∧ c.lo = 14 * (2 * g + 1) + 4 ∧ c.hi = 14 * (2 * g + 1) + 9) ∨
      ∃ g, g < 12 ∧ c.lo = 28 * g + 5 ∧ c.hi = 28 * g + 10 := by
  rcases (csHead_mem ν st R c).1 h with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · exact Or.inl ⟨(show 342 ≤ 342 by omega), (show 347 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 343 by omega), (show 348 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 347 by omega), (show 352 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 346 by omega), (show 346 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 344 by omega), (show 345 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 346 by omega), (show 347 ≤ 352 by omega)⟩
  · exact Or.inl ⟨(show 342 ≤ 346 by omega), (show 347 ≤ 352 by omega)⟩
  · exact Or.inr (Or.inl ⟨l, hl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨g, hg, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨g, hg, rfl, rfl⟩))

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- The clause "the segment's own rounds have returned something" stays past sub-protocol b, if that
sub-protocol's clause of `keeps` leaves the field `own` of an open layers' segment as it was. -/
theorem staysBy_own {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .lay a →
      ∃ a', s'.here = .lay a' ∧ a'.own = a.own) :
    StaysBy T b ⟨lo, hi, fun _ _ s => ∃ o, s.own? = some o⟩ := by
  intro w s s' hK hP
  obtain ⟨o, ho⟩ := hP
  unfold S.own? at ho
  cases hh : s.here with
  | lay a =>
    rw [hh] at ho
    obtain ⟨a', ha', e⟩ := hk s s' hK a hh
    refine ⟨o, ?_⟩
    unfold S.own?
    rw [ha']
    exact e.trans ho
  | between => rw [hh] at ho; cases ho
  | att a => rw [hh] at ho; cases ho
  | head a => rw [hh] at ho; cases ho
  | fin a => rw [hh] at ho; cases ho
  | mem a => rw [hh] at ho; cases ho

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_length
#print axioms ProofFile.Honest.csHead_mem
#print axioms ProofFile.Honest.csHead_span
#print axioms ProofFile.Honest.staysBy_own
