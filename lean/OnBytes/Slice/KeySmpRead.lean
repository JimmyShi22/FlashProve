-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeySmpRead.lean: how the seed and the answer of a sent message's sample are read off
what was drawn and sent. Definitions, and statements that are not proved.


In a sending of two written rounds the verifier draws, in the first, one seed for all oracle
messages of that sending: a point and a factor other than 0. Each message reads the first
coordinates of the point, as many as its own cube has, and the factor. In the second round the
prover sends the answers.

The readers here take a written round's verifier message through its typed draws alone, and a
prover's message through the elements among its plain items alone. They name no key's data and no
format of a message. Two of them are typed, for the library's sample map; two give plain lists and
can be run. One equation for each pair is stated, under the clauses under which it is true.

Main definitions: cutPt, smpSeed, smpAns, jointC, seedList, ansList.

Statements, as definitions of type Prop: seedEq_stmt, ansEq_stmt.

Not claimed. The two statements are not proved here. Without their clauses they are false: a list
that is too short is read as 0. That jointC of a round is the number of coordinates that the program
takes there, the largest cube's among the sending's sampled messages. Which place in the answers'
message belongs to which message.
-/
import OnBytes.Slice.CorePeel

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-- **The prefix, named once**: a member reads the first bits coordinates of the joint point, and
the factor. -/
def cutPt (c bits : ℕ) (s : (Fin c → GE) × GEˣ) : (Fin bits → GE) × GEˣ :=
  (fun t => if h : t.val < c then s.1 ⟨t.val, h⟩ else 0, s.2)
/-- A member's seed, off the verifier's message of the written round d. c: the coordinates of the
joint point. bits: those of the member's cube. -/
noncomputable def smpSeed (c bits : ℕ) (d : PQ.RD) (ch : (wRound d).Chal) : (Fin bits → GE) × GEˣ :=
  cutPt c bits (gSeed c _ (valsOf d ch))
/-- A member's one answer, off the prover's message of the written round d. k: its place among the
elements of that message. 0 beyond the end. -/
def smpAns (d : PQ.RD) (a : (wRound d).Msg) (k : ℕ) : Unit → GE := fun _ => (ansOf d a).getD k 0
/-- The coordinates of a seed round's joint point: its elements less the factor. -/
def jointC (d : PQ.RD) : ℕ := nE (Fmt.dsOf d.entry d.kind) - 1
/-- The joint seed as a plain list: the point's coordinates, then the factor. -/
def seedList (c : ℕ) (d : PQ.RD) (ch : (wRound d).Chal) : List GE :=
  (elemsV _ (valsOf d ch)).take (c + 1)
/-- The answer at the place k as a plain list of one element; empty beyond the end. -/
def ansList (d : PQ.RD) (a : (wRound d).Msg) (k : ℕ) : List GE := ((ansOf d a).drop k).take 1
/-- Statement, not proved here. The typed seed against the plain list. -/
def seedEq_stmt : Prop := ∀ (c bits : ℕ) (d : PQ.RD) (ch : (wRound d).Chal), bits ≤ c →
  nE (Fmt.dsOf d.entry d.kind) = c + 1 → IsNZ (Fmt.dsOf d.entry d.kind) c →
  List.ofFn (smpSeed c bits d ch).1 = (seedList c d ch).take bits ∧
    (smpSeed c bits d ch).2.val = (seedList c d ch).getD c 0
/-- Statement, not proved here. The typed answer against the plain list. -/
def ansEq_stmt : Prop := ∀ (d : PQ.RD) (a : (wRound d).Msg) (k : ℕ), k < (ansOf d a).length →
  [smpAns d a k ()] = ansList d a k

end OnBytes.Slice
