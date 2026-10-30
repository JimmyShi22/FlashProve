-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Parts.lean: the five named hypotheses of OnBytes/K/TopVC.lean in two groups, and the tie
for the entry file alone.

The five hypotheses `Holes5` speak of three files. Three of them speak of the two tables' seeds and
of the entry file: `seed0`, `seed1`, `link`. Two speak of the key file's and the proof file's typed
strings: `test`, `session`. The two groups stand apart here, because they are not of one standing:
see "What is not claimed".

Main definitions. `EntryPart V R`: `seed0`, `seed1`, `link`. `KeyProofPart V R`: `test`, `session`.
Main theorems.
 `holes5_of_parts`   the two groups give `Holes5`.
 `exit_entryPart`    under `EntryPart` alone: for every run of the Lean program `verify-on-bytes`
                     (OnBytes/Main.lean) that ends in 0, at the files that this run has read and the
                     ID among its arguments, there are the program's own two tables: those at which
                     `PortYesAt` (OnBytes/K/Top.lean) holds. The first is what `Key.check` returns
                     on the key file, the further one what `Entry.check` returns against it. On a
                     served statement these two are read as records, the fixed reading gives the
                     further table and Link's typed string of the key file and the entry file, and
                     the two seeds' tests and Link say yes.

What is not claimed. Both groups are hypotheses; either may be false at a given shape, not only
unproved. `KeyProofPart` has not been weighed at three points where the typed queries meet the
strings that the prover and the verifiers that ship hash. The labels: each of a key's and of a
proof's three chains has a label of its own (the format page's R13.4, R14.3, R14.9, R14.10), while
the typed queries have one Fiat-Shamir oracle for each file's protocol. A prompt's tokens: they
enter the proof's first query byte for byte, with the request's two numbers, in the item "the
request file's words", and once more through a digest under the second hash function, in the item
"request" (R14.3). A known difference: the configuration's and the parameters' digests are answers
of the hash function. This third point touches `EntryPart` too: the seeds' first query holds the
configuration's digest. At one fixed hash function, where the served statements pin the three
public files, that digest is a constant; a soundness statement over a random function fixes it
beforehand. The two fields of `KeyProofPart` also say that the fixed reading returns a typed string
at every key file and proof file that the program accepts. The program ties two openings of one
position by their digests alone, and a typed string has one opening at a position: so at a reading
that makes typed strings of such files these two fields say that no accepted file lists one position
twice with two different openings of one digest. No proof can give that of a fixed hash function.
All that the heads of OnBytes/K/Top.lean and OnBytes/K/TopVC.lean do not claim. For proofs only; the
program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.TopVC

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open _root_.Run (bytesToDig)

/-- The hypotheses on the two seeds and on the entry file. In each, `o` are options that hold the ID
and the bits 128, the program says yes with the tables `table` and `further`, and the statement is
served. -/
structure EntryPart (V : Shape) (R : Reading5 V) : Prop where
  /-- The first table is read as a record, and the seed's test at its root says yes. -/
  seed0 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r, V.recOf (stmOf F o) table = some r ∧
      V.seed0 (stmOf F o) (bytesToDig table.root) r = true
  /-- The same for the further table. -/
  seed1 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r', V.recOf (stmOf F o) further = some r' ∧
      V.seed1 (stmOf F o) (bytesToDig further.root) r' = true
  /-- The reading gives the program's own further table and a typed string, and Link says yes. -/
  link : ∀ F o id table further r r', o.id = some id → o.bits = 128 →
    PortYesAt F id table further → V.Served (stmOf F o) → V.recOf (stmOf F o) table = some r →
    V.recOf (stmOf F o) further = some r' →
    ∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
      V.vL (stmOf F o) (bytesToDig table.root) (bytesToDig further.root) r r' πL = true

/-- The hypotheses on the key file's and the proof file's typed strings. -/
structure KeyProofPart (V : Shape) (R : Reading5 V) : Prop where
  /-- The reading gives the program's own table and a typed string, and Test says yes. -/
  test : ∀ F o id table further r, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) → V.recOf (stmOf F o) table = some r →
    ∃ πT, R.key (stmOf F o) F.key = some (table, πT) ∧
      V.vT (stmOf F o) (bytesToDig table.root) r πT = true
  /-- The request and the reply are read as an instance, the reading gives a typed string, and the
  session says yes. -/
  session : ∀ F o id table further r', o.id = some id → o.bits = 128 →
    PortYesAt F id table further → V.Served (stmOf F o) →
    V.recOf (stmOf F o) further = some r' →
    ∃ i πB, V.insOf (stmOf F o) = some i ∧ R.prf (stmOf F o) F.ent F.proof F.entry = some πB ∧
      V.vB (stmOf F o) (bytesToDig further.root) i r' πB = true

/-- The two groups give the five. -/
theorem holes5_of_parts {V : Shape} {R : Reading5 V} (A : EntryPart V R) (B : KeyProofPart V R) :
    Holes5 V R :=
  ⟨A.seed0, B.test, A.seed1, A.link, B.session⟩

/-- The tie for the entry file alone, under `EntryPart`. -/
theorem exit_entryPart (V : Shape) (R : Reading5 V) (A : EntryPart V R) {args : List String}
    {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : Params.TableName), PortYesAt F id table further ∧
        (V.Served (stmOf F a.options) →
          ∃ (r rj : V.Rec (stmOf F a.options)) (πL : V.PiL (stmOf F a.options)),
            V.recOf (stmOf F a.options) table = some r ∧
            V.recOf (stmOf F a.options) further = some rj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            V.seed0 (stmOf F a.options) (bytesToDig table.root) r = true ∧
            V.seed1 (stmOf F a.options) (bytesToDig further.root) rj = true ∧
            V.vL (stmOf F a.options) (bytesToDig table.root) (bytesToDig further.root) r rj πL =
              true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp⟩ := main_zero_port h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun hs => ?_⟩
  obtain ⟨r, hr, s0⟩ := A.seed0 F a.options id table further hi hb hp hs
  obtain ⟨rj, hrj, s1⟩ := A.seed1 F a.options id table further hi hb hp hs
  obtain ⟨πL, he, vl⟩ := A.link F a.options id table further r rj hi hb hp hs hr hrj
  exact ⟨r, rj, πL, hr, hrj, he, s0, s1, vl⟩

end OnBytes.K
