-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1OwnFile.lean: the first toy (a product test), from end to end inside Lean, on bytes, at tiny
sizes: an honest prover writes a file along the real chain; the verifier on bytes accepts it and
refuses altered ones.

Definitions and guards (tests, #guard). No Mathlib.
The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean). The chain is the hash
chain from which the verifier's messages are drawn. So here the verifier's messages are not made up:
they come out of the hash of what the prover has sent, as in a real run.
(In this head "the programs" are the C++ implementation that comes with this Lean code, and "the
format page" is docs/format/FORMAT.md, which comes with the programs.)
The page: an edition of the format page that is not the one that ships; not held against that page.

What is joined:
  the prover without a hash (Fmt/M1Own.lean: `Own.ownStep`: the next message from the verifier's
    messages before it);
  the driver that strings a prover along a chain and writes the file (Fmt/Rules8Own.lean: `runOwn`:
    trees, roots, nonces, the chain's queries with the format's hash, draws, openings);
  the toy's description (Fmt/M1Plan.lean: `specOf`);
  the reader (Fmt/Rules8.lean), the view (Fmt/M1View.lean) and the decision (Fmt/M1All.lean: `dec`).

Main names:
  `gotsFor`: a message's elements, each named an answer or an element as the description's cut of
    the message into items says.
  `stratOf`: the prover in the form that the driver needs (`Strat`, Fmt/Rules8Own.lean); the leaves'
    salts are patterns.
  `fileOf`: the file that the honest rules make of a witness (true or false).
  `who`: what becomes of a file: the reader refuses it, the decision refuses it, or it is accepted.

Guards, at sizes of this library's own (K = 2; twenty rounds; three trees of depths 6, 7, 9; two
positions a list; 4 bits of work):
  the honest file is accepted;
  a false witness's file, made by the honest rules, is read and refused by the decision;
  a bit flipped at places all over the honest file: refused;
  a byte less, a byte more: refused by the reader.

Limits: what this file does not show. Prover and verifier share one reading of one text and the
verifier's own blocks: an error that both share is not seen (for files made by a second program,
this library's own, written independently from the same description in another language, see
Fmt/M1Tiny.lean). Nothing on the programs' own files: this file's sources include none.
The programs' own files of the first toy are held as bytes, or listed, in Fmt/M1ProgPTFiles.lean,
Fmt/M1ProgPRFiles.lean and Fmt/M1ProgPFFiles.lean; the honest proof of each set is read by the
strict reader, with the values taken from the programs' lists of the plan, the digests and the chain
read from the file or recomputed, in Fmt/M1EnginePT.lean, Fmt/M1EnginePR.lean and
Fmt/M1EnginePF.lean; and all are judged in Fmt/M1FullProg.lean, Run/PlanQSFProg.lean and files
Run/M1Engine*.lean.
No theorem.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1Own
import Fmt.M1Plan
import Fmt.M1View
import Fmt.Rules8Own

namespace Fmt.M1
namespace OwnFile

/-- A message's elements under the names of the cut (roots passed over); elements that are left over
are handed on as elements, so that the driver refuses. -/
def gotsFor : List Item → List E → List ItemValue
  | .root :: ts, es => gotsFor ts es
  | .answer :: ts, e :: es => .answer e :: gotsFor ts es
  | _ :: ts, e :: es => .e e :: gotsFor ts es
  | _, es => es.map .e

/-- The prover in the form that the driver needs. -/
def stratOf (S : Spec) (step : List (List E × List Nat) → List E × List (Nat → List UInt64)) :
    Strat := fun ds =>
  let out := step (ds.map fun d => (d.elems, d.poss))
  (gotsFor ((S.rounds.getD ds.length { entry := default, kind := .nothing }).items) out.1,
   out.2.map fun c => ⟨c, fun x => pattern 40 (x % 97 + 2) (ds.length + 1)⟩)

/-- sizes of this library's own: Fmt/M1Own.lean's, with 4 bits of work -/
def par : Par := { Own.tiny with work := 4 }

def cfg : ByteArray := configDigest [ascii "own\n"]
def spec : Spec := specOf par cfg []

/-- the file that the honest rules make of the rows a, b and a third row -/
def fileOf (c : List UInt64) (rnd : ByteArray) : Option ByteArray :=
  (runOwn spec rnd 4096 (stratOf spec (Own.ownStep blocks par Own.cn Own.wa Own.wb c))).map (·.1)

inductive Who where
  | reader
  | decision
  | accepted
  deriving DecidableEq, Repr

def who (b : ByteArray) : Who :=
  match wholeChain (m := Id) formatHash spec b with
  | none => .reader
  | some o => if dec par (viewOf 0 o) then .accepted else .decision

def honest : ByteArray := (fileOf Own.wc (pattern 32 5 1)).getD ByteArray.empty

end OwnFile

open OwnFile in
#guard spec.ok && (fileOf Own.wc (pattern 32 5 1)).isSome
-- the sizes that the head names
open OwnFile in
#guard par.K == 2 && spec.rounds.length == 20 && (List.range 4).map (fun n => (spec.shapeOf n).map (·.a)) == [some 6, some 7, some 9, none] &&
  (spec.rounds.filter fun r => r.entry.poss != 0).map (fun r => (r.entry.poss, r.entry.work)) == [(2, 4), (2, 4), (2, 4)]
-- the honest file is accepted; so is one under other random bytes (the challenges of the two runs
-- are not compared)
open OwnFile in
#guard who honest == .accepted
open OwnFile in
#guard ((fileOf Own.wc (pattern 32 9 4)).map who) == some .accepted
-- the verifier on bytes of Fmt/M1View.lean says the same
open OwnFile in
#guard verify spec (fun (_ : Unit) v => dec par v) () honest
-- a false witness (one entry of the third row one larger), by the honest rules: the file is read;
-- the decision refuses
open OwnFile in
#guard ((fileOf [39, 85, 134, 253] (pattern 32 5 1)).map who) == some .decision
-- a byte less, a byte more: the reader
open OwnFile in
#guard who (honest.extract 0 (honest.size - 1)) == .reader && who (honest ++ zeroBytes 1) == .reader
-- a bit flipped at every 97th byte of the file: never accepted
open OwnFile in
#guard (List.range (honest.size / 97)).all fun i => who (flipAt honest (97 * i)) != .accepted

end Fmt.M1
