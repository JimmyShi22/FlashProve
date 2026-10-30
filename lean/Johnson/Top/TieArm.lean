-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArm.lean: the tie between the Lean program `verify-on-bytes` (OnBytes/Main.lean; "the
program" below) and the entry's arm with the lax Link, `armL`
(Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean), at an input r of Johnson/Top/InnerCompiledVerifier.lean.

An arm takes two roots, two records and Link's typed string. `armL` runs the two seeds' tests and
then Link's compiled verifier without the test of the strict format. `arm_pr_one`
(Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean) bounds, for every arm V, every coding m and every maker
over one random function g, the chance that `(runA W V (readBlocks m g) z).1 = true` while what the
arm promises fails. This file ends at that function of g, at g := Lean's BLAKE2b.

Main definitions.
 `shapeLax T`      the shape `innerInputTieShape T` (Johnson/Top/TieInnerCompiledVerifier.lean) with Link's part run
                   without the strict format.
 `ArmIn`           what the arm alone reads: the object, the wire, the seeds' data, the answers'
                   code and the coding; with which statements are served and how a table is read
                   as a record. It has no field for a commitment's code, for an instance or for a
                   cheating prover; its object still carries the three honest provers, of which
                   nothing is asked.
 `ArmIn.shape`     the shape at an `ArmIn`. Its parts for the key file and the proof file are
                   placeholders that say no; `EntryPart` does not read them.
Main theorems.
 `det_withTrace`   the first part of what an algorithm with its own log returns, at fixed oracle
                   functions, is what the algorithm returns there.
 `exit_armL`       under `EntryPart` (OnBytes/K/Parts.lean) at `shapeLax T`: if the program exits
                   with code 0, there are its own two tables (`PortYesAt`, OnBytes/K/Top.lean: what
                   `Key.check` returns on the key file, and what `Entry.check` returns against it:
                   functions of the bytes); and on a served statement the run of
                   `armL`, at what `r.oracleCoding` reads out of Lean's BLAKE2b, at their roots and records
                   and at the string that the fixed reading gives of this run's key file and entry
                   file, says yes.
 `exit_arm`        the same at an `ArmIn`.

What is not claimed. The three hypotheses of `EntryPart` are not proved here at any r, and may be
false. The bound of `arm_pr_one` is over a random function; this file speaks of one fixed function:
the step from the one to the other is taken as given, and the two theorems are composed nowhere.
That step is more than "a random function for a fixed one". In `arm_pr_one` the wires, the seeds'
data `seedQueries` (with `seedQueries.cfg`), the answers' code and the coding are fixed before the function is drawn.
At the real entry file `seedQueries.cfg` is the digest of the three public files, which is itself an answer
of the hash function; and the coding `m` that is meant there is written from that digest and from
the parameters' digest, a second such answer. At a fixed function, where `Served` pins these files,
all three are constants.
The reading R is meant to parse and not to search: the bound speaks of a maker with a budget of
queries, and an R made by choice is no algorithm. Exit code 0 covers both YES and WITHIN LIMITS.
`Served`, `recOf`, the reading R and r are parameters; while `recOf` is free, the two hypotheses on
the seeds say something only at a `recOf` whose seed is the program's own. All that the heads of
OnBytes/K/Parts.lean and Johnson/Top/TieInnerCompiledVerifier.lean do not claim. For proofs only; the program
does not import this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieInnerCompiledVerifier
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsOne

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open VerifiableInference.OnPublicFiles

/-- What an algorithm with its own log returns first, at fixed oracle functions, is what the
algorithm returns there. -/
theorem det_withTrace {S : OSpec} {α : Type} (g : Fam S) (c : OComp S α) :
    (c.withTrace.det g).1 = c.det g := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    show (((k (g o q)).withTrace.bind fun out => OComp.pure (out.1, ⟨o, q, g o q⟩ :: out.2)).det
      g).1 = (k (g o q)).det g
    rw [OComp.det_bind]
    exact ih (g o q)
  | sample n k ih => exact ih 0

variable {r : InnerCompilerInput} (T : InnerInputTieData r)

/-- The shape at r with Link's part run without the strict format. -/
def shapeLax : Shape :=
  { innerInputTieShape T with
    vL := fun _ cm cm' c c' π => (vLA' r.queryLayout r.answerCode cm cm' c c' π).det (readBlocks r.oracleCoding oBits) }

/-- The tie for the entry file at the arm with the lax Link, under `EntryPart` alone. -/
theorem exit_armL (R : Reading5 (shapeLax T)) (A : EntryPart (shapeLax T) R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (T.Served (stmOf F a.options) →
          ∃ (c cj : r.protocol.Rec) (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)),
            T.recOf (stmOf F a.options) table = some c ∧
            T.recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            (runA r.queryLayout (armL r.queryLayout r.seedQueries r.answerCode) (readBlocks r.oracleCoding oBits)
              (bytesToDig table.root, bytesToDig further.root, c, cj, πL)).1 = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp, hs⟩ := exit_entryPart (shapeLax T) R A h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun hS => ?_⟩
  obtain ⟨c, cj, πL, hc, hcj, he, s0, s1, vl⟩ := hs hS
  refine ⟨c, cj, πL, hc, hcj, he, ?_⟩
  have s0 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig table.root) c.1).det (readBlocks r.oracleCoding oBits) = true := s0
  have s1 : (outOfDomainSeedIs r.queryLayout r.seedQueries (bytesToDig further.root) cj.1).det (readBlocks r.oracleCoding oBits) = true :=
    s1
  have vl : (vLA' r.queryLayout r.answerCode (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
    (readBlocks r.oracleCoding oBits) = true := vl
  unfold runA
  rw [det_withTrace]
  show (VLA' r.queryLayout r.seedQueries r.answerCode (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
    (readBlocks r.oracleCoding oBits) = true
  unfold VLA'
  simp only [OComp.det_bind]
  rw [s0, s1, vl]
  rfl

/-- What the entry's arm alone reads. -/
structure ArmIn where
  I : Type
  X : Type
  L : HolographicProtocol I X
  Bd : Type
  aT : RoundSplits L.offline.shape
  aL : RoundSplits L.link.shape
  W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)
  Sd : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL
  /-- how a record's answers are written as digests -/
  cA : L.OutOfDomainAnswer → List (Dig 256)
  /-- the coding of typed queries as bit strings -/
  m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256
  /-- the statements that the description covers -/
  Served : UserStm → Prop
  /-- a table as a record -/
  recOf : UserStm → OnBytes.Params.TableName → Option L.Rec

/-- The shape at an `ArmIn`. The parts for the key file and the proof file are placeholders. -/
def ArmIn.shape (r : ArmIn) : Shape where
  Served := r.Served
  Rec := fun _ => r.L.Rec
  Ins := fun _ => Unit
  PiT := fun _ => Unit
  PiL := fun _ => OneProtocolProof 256 (batLC r.L r.aL)
  PiB := fun _ => Unit
  recOf := r.recOf
  insOf := fun _ => none
  seed0 := fun _ cm c => (outOfDomainSeedIs r.W r.Sd cm c.1).det (readBlocks r.m oBits)
  seed1 := fun _ cm c => (outOfDomainSeedIs r.W r.Sd cm c.1).det (readBlocks r.m oBits)
  vT := fun _ _ _ _ => false
  vL := fun _ cm cm' c c' π => (vLA' r.W r.cA cm cm' c c' π).det (readBlocks r.m oBits)
  vB := fun _ _ _ _ _ => false

/-- The tie for the entry file at the arm with the lax Link, at an `ArmIn`, under `EntryPart`
alone. -/
theorem exit_arm (r : ArmIn) (R : Reading5 r.shape) (A : EntryPart r.shape R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (r.Served (stmOf F a.options) →
          ∃ (c cj : r.L.Rec) (πL : OneProtocolProof 256 (batLC r.L r.aL)),
            r.recOf (stmOf F a.options) table = some c ∧
            r.recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            (runA r.W (armL r.W r.Sd r.cA) (readBlocks r.m oBits)
              (bytesToDig table.root, bytesToDig further.root, c, cj, πL)).1 = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp, hs⟩ := exit_entryPart r.shape R A h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun hS => ?_⟩
  obtain ⟨c, cj, πL, hc, hcj, he, s0, s1, vl⟩ := hs hS
  refine ⟨c, cj, πL, hc, hcj, he, ?_⟩
  have s0 : (outOfDomainSeedIs r.W r.Sd (bytesToDig table.root) c.1).det (readBlocks r.m oBits) = true := s0
  have s1 : (outOfDomainSeedIs r.W r.Sd (bytesToDig further.root) cj.1).det (readBlocks r.m oBits) = true :=
    s1
  have vl : (vLA' r.W r.cA (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
    (readBlocks r.m oBits) = true := vl
  unfold runA
  rw [det_withTrace]
  show (VLA' r.W r.Sd r.cA (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
    (readBlocks r.m oBits) = true
  unfold VLA'
  simp only [OComp.det_bind]
  rw [s0, s1, vl]
  rfl

end OnBytes.K
