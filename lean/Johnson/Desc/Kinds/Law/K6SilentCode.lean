-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SilentCode.lean: FOUR DEFINITIONS WITH CODE, AND NOTHING ELSE: the filling
of the table of joints' letter "silent" (the reader of a run where the run itself is silent:
Johnson/Desc/First/Batch/ReadersOfLink.lean: LinkHoles) at the head's link, and a test that it
answers. Cut out of Law/K6Silent.lean and Law/K6FormsInT.lean, to the letter, so that a harness can
import them without these files' laws. No theorem is stated.

WHY. At the border right behind the output head's own block its runs refuse: they read the places of
the reads' tables off the record's field t, which is laid one block later. But the tables are a
function of public numbers, of the request's words, of the heard reply and of what the head's own
rounds heard (Johnson/Desc/K8/ReadsQuiet.lean: tables): all of which lie in the record behind the
head's yes.

  tablesAt P s     the tables that the reads' quiet step makes at the record s: its own text's three
                   readers and its own function, in its order.
  withTables P s   the record with these tables laid in t, nothing else turned.
  k6Silent P states   THE FILLING: block b, run name, record s: the run itself (readerOf) at
                   withTables P s.
  k6SilentB        A TEST WITH CODE: the tables can be made, and the reader answers at the head's
                   four runs.

WHAT IT IS NOT. Definitions. That k6Silent answers anywhere, and what it answers: Law/K6Silent.lean
and
Law/K6FormsInT.lean, under their premises. k6SilentB has run nowhere. Nothing on soundness.

-/
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (readerOf RunOf)

/-- The tables that the reads' quiet step makes at the record. -/
def tablesAt (P : K8.ReadsQuiet.PH) (s : S) : Option OnBytes.Model.Head.Tables :=
  match s.here with
  | .head a =>
    if a.opened then
      (s.covered P.h.T P.h.V).toOption.bind fun cov =>
        a.x.bind fun x => (K8.ReadsQuiet.tables P.h P.L P.hp cov x).toOption
    else none
  | _ => none

/-- The record with these tables laid; nothing else turns. -/
def withTables (P : K8.ReadsQuiet.PH) (s : S) : Option S :=
  match s.here with
  | .head a => (tablesAt P s).map fun t => { s with here := .head { a with t := some t } }
  | _ => none

/-- **THE FILLING OF "silent"**: the run itself, at the record with the tables laid. -/
def k6Silent (P : K8.ReadsQuiet.PH) (states : Nat → List (RunOf S)) :
    Nat → String → S → Option K9.Read :=
  fun b name s => (withTables P s).bind (readerOf states b name)

/-- **A TEST WITH CODE**: the tables can be made at the record, and the reader answers at all four
runs. -/
def k6SilentB (P : K8.ReadsQuiet.PH) (states : Nat → List (RunOf S)) (b : Nat) (s : S) : Bool :=
  (withTables P s).isSome &&
    ["norm", "join", "policy", "logits"].all fun name => (k6Silent P states b name s).isSome

end VerifiableInference.Desc.Kinds.Head.Law
