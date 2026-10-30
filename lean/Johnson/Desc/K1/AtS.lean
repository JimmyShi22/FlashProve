-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/AtS.lean: the kind K1 at the record that a proof file's first chain carries
(Johnson/Desc/First/State.lean: S): the kind's two blocks (Johnson/Desc/K1/Own.lean) with their
lenses, so that they can stand in a fold over blocks.

This file holds definitions only; no theorem is stated.

What a block finds and leaves: S as the program's step finds and leaves it at that border.
  A commitment (a segment's moments 1 and 2): it reads st, book, roots, rowsOwed and, of the open
    link, L, F and tl; it writes st, book, roots, rowsOwed := none, L and F. Refused where no link
    is open.
  W's sending: it reads st, book, roots, rowsOwed and the members' msg, which it holds against what
    ROUNDS announces; it writes st, book, roots, rowsOwed := none and ids. Refused where the chain
    does not stand at the members' places.
The field failed is neither read nor written: a mark made in front is handed on.

Main names: stateOf, owedOf, laid; commitAtS; sendAtS.

Not here: what the step without a round behind the reads' commitment does (the list of tables is
closed; two public tests; the guard of order: Johnson/Desc/K8/ReadsQuiet.lean at a layers' link and
at the head's) and the step behind W's sending: in a fold whose places hold these beside the sending
they are laid behind this block by Block.andThen.

What is not claimed. That a lens reads and writes just the fields named above: no theorem says so.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Own
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The statement's part of S. The opened columns are no field of S: this kind reads none. -/
def stateOf {L : Type} (s : S) (l : L) : DState L :=
  { st := s.st, book := s.book, roots := s.roots, opened := [], loc := l }

/-- The debt of rows as this kind is handed it: a debt of no rows is no debt (the carried record's
own reading: "none" and "some 0" answer alike: S.noneWaits). The kind's own test, "something is
owed: refuse", is the same. -/
def owedOf (s : S) : Option Nat := s.rowsOwed.filter (· != 0)

/-- Laid back; behind the block nothing is owed. -/
def laid {L : Type} (s : S) (d : DState L) : S :=
  { s with st := d.st, book := d.book, roots := d.roots, rowsOwed := none }

/-- **A segment's later moment, at S.** -/
def commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) : Block S Cl :=
  let b : Block (Owing (L3.St (DState Unit))) Cl := commitOwn P link moment arrays
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before, claims := [], after := []
    decide := fun s rs gs =>
      match s.link?, s.fork?, s.tl? with
      | some L, some F, some tl =>
        (b.decide { owed := owedOf s, held := { L := L, F := F, tl := tl, w := stateOf s () } } rs
          gs).map fun y => ((laid s y.held.w).putLink y.held.L).putFork y.held.F
      | _, _, _ => .error "K1: no link is open" }

/-- **W's sending, at S.** -/
def sendAtS (P : Par) : Block S Cl :=
  let b : Block (Owing (DState (Array Nat))) Cl := sendOwn P
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before, claims := [], after := []
    decide := fun s rs gs =>
      match s.here with
      | .mem a =>
        -- on the carried record alone: the record announces what ROUNDS says
        if a.msg == P.sent then
          (b.decide { owed := owedOf s, held := stateOf s #[] } rs gs).map fun y =>
            { laid s y.held with here := .mem { a with ids := y.held.loc } }
        else .error "K1: the record announces other messages than the block's rounds declare"
      | _ => .error "K1: the chain does not stand at the members' places" }

end VerifiableInference.Desc.K1
