-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyAccountKit.lean: the accounting of the plans of two small configurations,
one with and one without proof of work, compared with the lines that the C++ verifier prints. The
tests run when this file compiles.

The program does not import this file.

With work: the small example, prover/examples/target_small_f2_roomy. The plans are those that
OnBytes/Params/TestConfigure.lean derives from the first 32 lines of its policy.txt, with shapes
that are filled in by hand there. The lines of the C++ verifier were taken from an honest whole
call (-show-stages) on examples/accepted-proof, whose three public files are that example's. It
prints for each stage a record of the accounting (verifier/src/vf_accounting_record.h says what each
number is). The line "plan-rests:" holds, as its fourth and fifth numbers, the rounds with a
closeness term by the source of their count: the lemma within a third of the code's distance, the
assumed theorem. The line "plan-near:" holds, as its fifth number, the rounds that hold only because
their work is counted. The line "plan-lists:" holds the largest error without work in bits, that
round's work and, last, its name. The first line "plan-round:" is the round with the largest error
when work is counted: its bits without work, then its work, which is 0 in all three. For the stages
key and leaf the lines are about the stage's own file, for the stage request about the plans of key,
entry and proof, joined in this order:
  key      plan-rests 0 37    plan-near 14   plan-round 128.001105
           plan-lists 96.236397 32 CS (Omega, stage #)
  leaf     plan-rests 0 12    plan-near 4    plan-round 128.002475
           plan-lists 96.505873 32 CS (the two folded rows, stage #)
  request  plan-rests 0 127   plan-near 38   plan-round 128.000000
           plan-lists 96.236397 32 CS (Omega, stage #)
and, in its closing lines,
  stage key: work: 96.23 + 32 (..; key: CS (Omega, stage #))
  stage leaf: work: 96.50 + 32 (..; leaf: CS (the two folded rows, stage #))
  stage request: work: 100.11 + 28 (..; request: CS (Omega, stage #))
  proof of work: up to 32 bits counted in 38 rounds; with it the least round has 128.00 bits,
  without it 96.23 bits
The C++ verifier's planning call (-plan accounting) on the example prints 11857 rounds and, file by
file, the rounds with a closeness term by the same two sources: key 0 and 37, entry 0 and 12, proof
0 and 78.

Without work: the same 32 lines with the line "work positions 0 0 0". The plans here are made from
the same shapes. The lines of the C++ verifier were taken from its planning call on the three files
of prover/tests/configurations/pinned_no_proof_of_work_roomy, whose parameter file begins with these
32 lines and differs from the example's also in the line s. It prints 11857 rounds, the same numbers
file by file, and
  THE ROUNDS: HOLD: every round holds at the target, and none needs proof of work for it
  THE LARGEST ROUND ERROR: 2^-128.00, in the round "RNG (G0, smallness test)"
The planning call on prover/tests/configurations/pinned_no_proof_of_work prints the same lines.

What is not compared with a print: without work, the largest errors of the key's plans alone and of
the entry's alone (the planning call prints them for the three files together only); in both
configurations the mark `formed`, that a call reads the record, and that each note on work agrees
with Params.needsWork; this library's lists of places and of rounds' names, and the number 90. Of a
round's name only the word before the bracket is compared.
-/
import OnBytes.Model.VerifyAccount
import OnBytes.Params.TestConfigure

namespace OnBytes.Model.TestVerifyAccountKit

open Verify

/-- The configuration with work: the small example. -/
def madeWithWork : Option (Except String Params.Configured) := Params.TestConfigure.made

/-- The 32 lines of the configuration without work. -/
def text : List String := Params.TestFile.small.set 10 "work positions 0 0 0"

-- the line that is replaced is the example's line on work before the draws of positions
#guard Params.TestFile.small[10]? == some "work positions 20 28 32"

/-- 32 zero bytes in the place of the digest of the public files. The value is made up. It enters
only the result's field configuration and the chains' parameter bytes. No test here reads them. -/
def cfg : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- The configuration without work. -/
def madeWithout : Option (Except String Params.Configured) :=
  ((Params.readLines (Params.TestFile.fileOf text)).toOption.map (·.1)).bind fun l =>
    Params.TestConfigure.shapes.map fun x => Params.configure l x cfg 128

/-- An accounting in short: formed, holds, needs work; the two numbers of closeness terms; the
largest error in hundredths of a bit, that round's work and name. -/
def short (a : Accounting) : Bool × Bool × Bool × Nat × Nat × Nat × Nat × String :=
  (a.formed, a.holds, a.needsWork, a.closeThird, a.closeJohnson,
    a.record.centibits, a.record.work, (a.lists.map (·.name)).getD "")

/-- The accountings of the key's plans, of the entry's, and of all seven chains' plans. -/
def kit (made : Option (Except String Params.Configured)) :
    Option (List (Bool × Bool × Bool × Nat × Nat × Nat × Nat × String)) :=
  match made with
  | some (.ok c) =>
    some ([c.key, [c.entry], c.key ++ [c.entry] ++ c.proof].map fun plans =>
      short (account (merged c.sized.set plans)))
  | _ => none

#guard kit madeWithWork == some
  [(true, true, true, 0, 37, 9623, 32, "CS"),
   (true, true, true, 0, 12, 9650, 32, "CS"),
   (true, true, true, 0, 127, 9623, 32, "CS")]

-- without work, all seven chains' plans
#guard (kit madeWithout).map (·.drop 2) == some [(true, true, false, 0, 127, 12800, 0, "RNG")]

/-- For the plans of the key, of the entry, of the proof and of all seven chains: holds, needs work,
and the two numbers of closeness terms. -/
def rests (made : Option (Except String Params.Configured)) :
    Option (List (Bool × Bool × Nat × Nat)) :=
  match made with
  | some (.ok c) =>
    some ([c.key, [c.entry], c.proof, c.key ++ [c.entry] ++ c.proof].map fun plans =>
      let a := account (merged c.sized.set plans)
      (a.holds, a.needsWork, a.closeThird, a.closeJohnson))
  | _ => none

#guard rests madeWithout == some
  [(true, false, 0, 37), (true, false, 0, 12), (true, false, 0, 78), (true, false, 0, 127)]

/-- The number of rounds of all seven chains' plans; the record that the stage request returns; the
stages' notes on work; whether each note agrees with Params.needsWork on the same plans. -/
def summary (made : Option (Except String Params.Configured)) :
    Option (Nat × Option Stages.Acct × List (Option Stages.WorkNote) × Bool) :=
  match made with
  | some (.ok c) =>
    let s := c.sized.set
    let files := [("key", c.key), ("leaf", [c.entry]), ("request", c.proof)]
    let notes := files.map fun (n, plans) =>
      ((acctOfH s (some plans) 128 n).toOption.bind (·.work), Params.needsWork plans)
    some (((c.key ++ [c.entry] ++ c.proof).map (·.rounds.length)).foldl (· + ·) 0,
      acctWhole s (some (c.key ++ [c.entry] ++ c.proof)), notes.map (·.1),
      notes.all fun x => (workHeldH x.2 x.1).isOk)
  | _ => none

#guard summary madeWithWork == some
  (11857, some ⟨128, true, 9623, 32, 38, 32, 12800, 127⟩,
   [some ⟨9623, 32, "key: CS"⟩, some ⟨9650, 32, "leaf: CS"⟩, some ⟨10011, 28, "request: CS"⟩], true)

-- without work: the number of rounds; no stage has a note on work
#guard (summary madeWithout).map (fun x => (x.1, x.2.2.1)) == some (11857, [none, none, none])

/-- For the plans of the key, of the entry, of the proof and of all seven chains: the number of
rounds whose closeness term rests on a source other than the lemma within a third of the code's
distance (Acct.closeOther). -/
def otherSources (made : Option (Except String Params.Configured)) : Option (List Nat) :=
  match made with
  | some (.ok c) =>
    some ([c.key, [c.entry], c.proof, c.key ++ [c.entry] ++ c.proof].map fun plans =>
      (account (merged c.sized.set plans)).record.closeOther)
  | _ => none

#guard otherSources madeWithWork == some [37, 12, 78, 127]

-- a call reads the record
#guard (match madeWithWork with
  | some (.ok c) => (acctWhole c.sized.set (some (c.key ++ [c.entry] ++ c.proof))).map (·.taken)
  | _ => none) == some true

-- the notes' places are in the list of places, and every round of the two configurations' plans has
-- a name from the list of names
#guard (summary madeWithWork).any fun x =>
  x.2.2.1.all fun note => note.any fun n => Account.places.contains n.place
#guard [madeWithout, madeWithWork].all fun made =>
  match made with
  | some (.ok c) =>
    (c.key ++ [c.entry] ++ c.proof).all fun p =>
      p.rounds.all fun r => Account.roundNames.contains r.entry.name
  | _ => false
-- three stages times the 30 names of blocks/numbers/round_names.h
#guard Account.places.length == 90

/-- For the key's plans, for the entry's and for all seven chains' plans, the four numbers on proof
of work in a call's closing lines: the most bits of work, the rounds that hold only with their work,
and the largest error in hundredths of a bit, first with each round's work counted, then with work
left out. -/
def lineOnWork (made : Option (Except String Params.Configured)) :
    Option (List (Nat × Nat × Nat × Nat)) :=
  match made with
  | some (.ok c) =>
    some ([c.key, [c.entry], c.key ++ [c.entry] ++ c.proof].map fun plans =>
      let r := (account (merged c.sized.set plans)).record
      (r.mostWork, r.byWork, r.leastRound, r.centibits))
  | _ => none

#guard lineOnWork madeWithWork == some
  [(32, 14, 12800, 9623), (32, 4, 12800, 9650), (32, 38, 12800, 9623)]

-- Without work no bits of work are declared and no round holds only with its work; of all seven
-- chains' plans the largest error is 2^-128.00.
#guard (lineOnWork madeWithout).map (·.map fun x => (x.1, x.2.1)) == some [(0, 0), (0, 0), (0, 0)]
#guard (lineOnWork madeWithout).map (·.drop 2) == some [(0, 0, 12800, 12800)]

end OnBytes.Model.TestVerifyAccountKit
